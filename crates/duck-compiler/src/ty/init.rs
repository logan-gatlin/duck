//! Variables declared without a value: `let x: T` or `var x: T` binds a
//! name that is assigned later, as by each branch of an `if` or each arm
//! of a `match`. Nothing reads one before it is assigned, however control
//! got there, and a `let` is assigned only where it may not have been.

use std::mem;

use rustc_hash::FxHashMap;

use crate::lex::Span;
use crate::parse::{self, BinOp, Binding, ExprKind, Mutability, Pattern, PatternKind};
use crate::visit::{self, Node};

use super::{Body, Label, Place, Slots, Ty, TypeErrorKind, push_assigned};

/// What is known, where control is, of the variables declared without a
/// value.
#[derive(Clone, Default)]
pub(super) struct Flow {
    /// Whether control never gets here. Anything is so of what never runs,
    /// so nothing is reported of it.
    dead: bool,
    /// What is known of each of the variables, by its `order`.
    vars: FxHashMap<usize, Init>,
}

/// What is known of a variable declared without a value.
#[derive(Clone, Copy)]
struct Init {
    /// Whether it has a value, however control got here: only then is it
    /// read.
    set: bool,
    /// Whether it has none, however control got here: only then is a `let`
    /// assigned.
    unset: bool,
}

/// A loop while it is lowered.
pub(super) struct Round {
    /// How many variables were bound before it.
    bound: usize,
    /// What is so wherever a `break` leaves it.
    left: Flow,
    /// What is so wherever a `continue` starts it again.
    again: Flow,
    /// Each assignment in it to a `let` bound before it: the `order` and the
    /// name of the `let`, and where the assignment is.
    assigned: Vec<(usize, String, Span)>,
}

/// The operands of an expression that are evaluated in the order they are
/// written and lowered in another: one that only the type of another types
/// is lowered after it. Each is checked as what is evaluated before it
/// leaves things, whichever is lowered first.
pub(super) struct Operands<'p> {
    exprs: Vec<&'p parse::Expr>,
    /// What is known before any of them is evaluated.
    before: Flow,
    /// What is known after each that is lowered, in the order they are
    /// evaluated.
    after: Vec<Option<Flow>>,
}

impl Flow {
    /// What is known where control never gets.
    pub(super) fn never() -> Self {
        Self {
            dead: true,
            vars: FxHashMap::default(),
        }
    }

    /// Makes it what is known where control gets as it says or as `other`
    /// does: what both say.
    pub(super) fn join(&mut self, other: Self) {
        if other.dead {
            return;
        }
        if self.dead {
            *self = other;
            return;
        }
        for (order, init) in &mut self.vars {
            if let Some(other) = other.vars.get(order) {
                init.set &= other.set;
                init.unset &= other.unset;
            }
        }
    }

    /// Makes it what is known once what `other` says has been done too,
    /// where both start from what was known before either.
    fn then(&mut self, other: &Self) {
        self.dead |= other.dead;
        for (order, done) in &other.vars {
            let init = self.vars.entry(*order).or_insert(*done);
            init.set |= done.set;
            init.unset &= done.unset;
        }
    }

    /// Control never gets past here if it `ended`.
    pub(super) fn end_if(&mut self, ended: bool) {
        self.dead |= ended;
    }

    /// What is known of the variable that is the `order`th.
    fn init(&self, order: usize) -> Init {
        let anything = Init {
            set: true,
            unset: true,
        };
        match self.dead {
            true => anything,
            false => self.vars.get(&order).copied().unwrap_or(anything),
        }
    }
}

impl Body<'_> {
    /// `let pattern: Type` or `var pattern: Type`, which binds each name of
    /// the pattern to a variable that has no value yet. Nothing runs here.
    pub(super) fn declare(&mut self, binding: &Binding) {
        let pattern = &binding.pattern;
        let ty = match &binding.ty {
            Some(ty) => self.resolve_ty(ty),
            None => {
                let keyword = match binding.mutability {
                    Mutability::Let => "let",
                    Mutability::Var => "var",
                };
                let kind = TypeErrorKind::UntypedBinding {
                    pattern: written(pattern),
                    keyword,
                };
                self.error(kind, pattern.span);
                Ty::Error
            }
        };
        self.report_nameless(pattern);
        let first = self.bound;
        let mutable = binding.mutability == Mutability::Var;
        self.bind_pattern(pattern, ty, mutable, None);
        let unset = Init {
            set: false,
            unset: true,
        };
        for order in first..self.bound {
            self.late.insert(order, false);
            self.flow.vars.insert(order, unset);
        }
    }

    /// Reports each part of `pattern` that binds no name, as there is no
    /// value for it to ignore.
    fn report_nameless(&mut self, pattern: &Pattern) {
        let nothing = match &pattern.kind {
            PatternKind::Discard => "_",
            PatternKind::Tuple(elems) if elems.is_empty() => "()",
            PatternKind::Tuple(elems) => {
                for elem in elems {
                    self.report_nameless(elem);
                }
                return;
            }
            _ => return,
        };
        self.error(TypeErrorKind::BindsNothing(nothing), pattern.span);
    }

    /// The `order` of the variable `name`, if it is declared without a
    /// value, and whether it is a `let`.
    fn late_var(&self, name: &str) -> Option<(usize, bool)> {
        let var = self.lookup(name)?;
        let late = self.late.contains_key(&var.order);
        late.then_some((var.order, !var.mutable))
    }

    /// Whether `place` is a variable declared without a value, or a part of
    /// one.
    pub(super) fn late_place(&self, place: &Place) -> bool {
        let local = matches!(place.slots, Slots::Local(_)) && place.behind.is_none();
        local && self.late_var(&place.name).is_some()
    }

    /// Reports the variable `name`, read at `span`, if it is declared
    /// without a value and may have none here. It is reported once: what
    /// follows is checked as if it had one.
    pub(super) fn reads(&mut self, name: &str, span: Span) {
        let Some((order, _)) = self.late_var(name) else {
            return;
        };
        let init = self.flow.init(order);
        if init.set {
            return;
        }
        let kind = TypeErrorKind::Uninitialized {
            name: name.to_string(),
            maybe: !init.unset,
        };
        self.error(kind, span);
        self.flow.vars.insert(order, Init { set: true, ..init });
    }

    /// The variable `name`, declared without a value, is assigned at
    /// `span`, once the value is evaluated: all of it if it's `whole`, and
    /// else a part of it. A `let` is reported if it may have a value
    /// already, once, or if a `defer` gives it its first.
    pub(super) fn assigns(&mut self, name: &str, whole: bool, span: Span) {
        let Some((order, once)) = self.late_var(name) else {
            return;
        };
        // What never runs assigns nothing.
        if self.flow.dead {
            return;
        }
        let init = self.flow.init(order);
        if once {
            let name = || name.to_string();
            let outside = self.deferred_from.is_some_and(|bound| order < bound);
            let kind = match init.unset {
                false => Some(TypeErrorKind::AssignedAgain {
                    name: name(),
                    maybe: !init.set,
                }),
                // What follows the `defer` runs before this does.
                true if outside => Some(TypeErrorKind::DeferInitializes(name())),
                true => None,
            };
            self.report_once(order, kind, span);
            if let Some(round) = self.rounds.last_mut()
                && order < round.bound
            {
                round.assigned.push((order, name(), span));
            }
        }
        let init = Init {
            set: init.set || whole,
            unset: false,
        };
        self.flow.vars.insert(order, init);
    }

    /// Reports `kind` at `span`, if it's one, unless an assignment to the
    /// `let` that is the `order`th is reported already.
    fn report_once(&mut self, order: usize, kind: Option<TypeErrorKind>, span: Span) {
        let Some(kind) = kind else {
            return;
        };
        let reported = self.late.get_mut(&order).expect("declared without a value");
        if !mem::replace(reported, true) {
            self.error(kind, span);
        }
    }

    /// Starts on `exprs`, the operands of an expression in the order they
    /// are evaluated, which are lowered in another.
    pub(super) fn operands<'p>(&self, exprs: Vec<&'p parse::Expr>) -> Operands<'p> {
        Operands {
            after: exprs.iter().map(|_| None).collect(),
            exprs,
            before: self.flow.clone(),
        }
    }

    /// Lowers with `lower` the `turn`th of `operands` to be evaluated, as
    /// those before it leave things. One of them that is not lowered yet is
    /// taken to assign what it is written to: for certain what it assigns
    /// wherever it gets to its end, and maybe the rest.
    pub(super) fn operand<T>(
        &mut self,
        operands: &mut Operands,
        turn: usize,
        lower: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let mut flow = operands.before.clone();
        for (expr, after) in operands.exprs.iter().zip(&operands.after).take(turn) {
            match after {
                Some(after) => flow.then(after),
                None => self.assume_assigned(expr, &mut flow),
            }
        }
        self.flow = flow;
        let lowered = lower(self);
        let after = mem::replace(&mut self.flow, operands.before.clone());
        operands.after[turn] = Some(after);
        lowered
    }

    /// Ends `operands`, each of which is lowered: what follows them is
    /// reached once all are evaluated.
    pub(super) fn evaluated(&mut self, operands: Operands) {
        self.flow = operands.before;
        for after in operands.after.iter().flatten() {
            self.flow.then(after);
        }
    }

    /// Makes `flow` what is known once `expr` is evaluated, as far as it
    /// can be told without lowering it.
    fn assume_assigned(&self, expr: &parse::Expr, flow: &mut Flow) {
        let mut maybe = Vec::new();
        push_assigned(expr, &mut maybe);
        let certain = certainly_assigned(expr);
        for name in &maybe {
            let late = self.late_var(name);
            let Some(init) = late.and_then(|(order, _)| flow.vars.get_mut(&order)) else {
                continue;
            };
            init.unset = false;
            init.set |= certain.contains(&name.as_str());
        }
    }

    /// Lowers with `lower` the body of a `defer`, which runs later than
    /// where it is: what follows it knows nothing of what it assigns.
    pub(super) fn later<T>(&mut self, lower: impl FnOnce(&mut Self) -> T) -> T {
        let before = self.flow.clone();
        let outer = self.deferred_from.replace(self.bound);
        let lowered = lower(self);
        self.deferred_from = outer;
        self.flow = before;
        lowered
    }

    /// Starts a loop, whose head and body are lowered next.
    pub(super) fn enter_round(&mut self) {
        self.rounds.push(Round {
            bound: self.bound,
            left: Flow::never(),
            again: Flow::never(),
            assigned: Vec::new(),
        });
    }

    /// A `break` or a `continue`, as `label` is, leaves the innermost loop
    /// or starts it again from here.
    pub(super) fn leaves_round(&mut self, label: Label) {
        let flow = self.flow.clone();
        let Some(round) = self.rounds.last_mut() else {
            return;
        };
        match label {
            Label::Break => round.left.join(flow),
            Label::Continue => round.again.join(flow),
            Label::Other => {}
        }
    }

    /// Ends the innermost loop where its body does. What follows the loop
    /// is reached as `skipped` says, where the body is never run, and from
    /// the end of the body and each `break` and `continue` in it. A `let`
    /// bound before the loop that an assignment in it may reach again, the
    /// next time around, is reported at the first of them.
    pub(super) fn end_round(&mut self, skipped: Flow) {
        let round = self.rounds.pop().expect("left where it was entered");
        let mut again = round.again;
        again.join(mem::replace(&mut self.flow, skipped));
        for (order, name, span) in &round.assigned {
            if again.init(*order).unset {
                continue;
            }
            let kind = TypeErrorKind::AssignedAgain {
                name: name.clone(),
                maybe: true,
            };
            self.report_once(*order, Some(kind), *span);
        }
        self.flow.join(again);
        self.flow.join(round.left);
        // They are in each loop this one is in, too.
        if let Some(outer) = self.rounds.last_mut() {
            let before = round
                .assigned
                .into_iter()
                .filter(|(order, ..)| *order < outer.bound);
            outer.assigned.extend(before);
        }
    }
}

/// The names that `expr` assigns whole whenever it is evaluated to its end:
/// those of its assignments that are on no right side of an `and` or an
/// `or`, which may not run.
fn certainly_assigned(expr: &parse::Expr) -> Vec<&str> {
    fn assigned<'p>(node: &Node<'p>) -> Option<&'p str> {
        let Node::Expr(parse::Expr {
            kind: ExprKind::Assign {
                target, op: None, ..
            },
            ..
        }) = node
        else {
            return None;
        };
        match &target.kind {
            ExprKind::Name(name) => Some(name),
            _ => None,
        }
    }
    let (mut all, mut maybe) = (Vec::new(), Vec::new());
    visit::expr(expr, &mut |node| {
        all.extend(assigned(&node));
        if let Node::Expr(parse::Expr {
            kind: ExprKind::Binary(BinOp::And | BinOp::Or, _, right),
            ..
        }) = node
        {
            visit::expr(right, &mut |node| maybe.extend(assigned(&node)));
        }
    });
    all.retain(|name| !maybe.contains(name));
    all
}

/// `pattern` as it is written, if it's one that a `let` or a `var` takes.
pub(super) fn written(pattern: &Pattern) -> String {
    match &pattern.kind {
        PatternKind::Name(name) => name.clone(),
        PatternKind::Tuple(elems) => {
            let elems: Vec<_> = elems.iter().map(written).collect();
            match &elems[..] {
                [one] => format!("({one},)"),
                elems => format!("({})", elems.join(", ")),
            }
        }
        _ => "_".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::tests::{body, check_src, lower};

    /// Each error of `src`: what it is reported at, and what it says.
    fn said(src: &str) -> Vec<(&str, String)> {
        let errors = check_src(src).err().unwrap_or_default();
        let at = |error: &super::super::TypeError| {
            let span = error.span.expect("in the source");
            &src[span.start..span.end]
        };
        errors
            .iter()
            .map(|error| (at(error), error.kind.to_string()))
            .collect()
    }

    fn unset(name: &str) -> String {
        format!("`{name}` is used before it is initialized")
    }

    fn maybe_unset(name: &str) -> String {
        format!("`{name}` may not be initialized here")
    }

    fn set(name: &str) -> String {
        format!("can't assign to `{name}` again: it is already initialized")
    }

    fn maybe_set(name: &str) -> String {
        format!("can't assign to `{name}` again: it may already be initialized")
    }

    #[test]
    fn a_variable_declared_without_a_value_is_assigned_later() {
        let src = "\
fn f(c: bool) -> i32:
    let x: i32
    var (a, b): tuple(i32, bool)
    if c:
        x = 1
        a = 2
    else:
        x = 3
        a = 4
    b = c
    a += 1
    return x + a
";
        let module = lower(src);
        // Declaring them runs nothing.
        assert_eq!(
            body(&module, "f"),
            "(if c (then (set x 1) (set a 2)) (else (set x 3) (set a 4))) \
             (set b c) (set a (I32.Add a 1)) (return (I32.Add x a))"
        );
    }

    #[test]
    fn what_assigns_one_later_runs_as_it_is_written() {
        // A constant is folded by running what it calls.
        let src = "\
fn pick(n: i32) -> i32:
    let x: i32
    var (a, b): tuple(i32, i32)
    match n:
        0:
            x = 7
            a = 1
        else:
            x = 9
            a = 2
    b = a * 10
    while (a = a - 1) > 0:
        b += 1
    return x * 100 + b
let zero = pick(0)
let other = pick(5)
fn f() -> i32:
    return zero + other
";
        assert_eq!(body(&lower(src), "f"), "(return (I32.Add 710 921))");
    }

    #[test]
    fn nothing_reads_one_that_may_have_no_value() {
        let src = "\
struct P:
    x: i32
fn never_set() -> i32:
    let a: i32
    return a
fn set_by_one_branch(c: bool) -> i32:
    var b: i32
    if c:
        b = 1
    return b
fn changed() -> i32:
    var d: i32
    d += 1
    return d
fn of_itself() -> i32:
    var e: i32
    e = e + 1
    return e
fn in_part(v: varray(i32)) -> i32:
    var p: P
    p.x = 1
    var w: varray(i32)
    w[0] = 1
    return p.x
fn shadowed() -> i32:
    let s = 5
    let s: i32
    s = s + 1
    return s
";
        assert_eq!(
            said(src),
            vec![
                ("a", unset("a")),
                ("b", maybe_unset("b")),
                ("d", unset("d")),
                ("e", unset("e")),
                ("p", unset("p")),
                ("w", unset("w")),
                ("s", unset("s")),
            ]
        );
    }

    #[test]
    fn a_let_is_assigned_where_it_has_no_value() {
        let src = "\
struct P:
    x: i32
fn twice():
    let a: i32
    a = 1
    a = 2
fn maybe_twice(c: bool):
    let b: i32
    if c:
        b = 1
    b = 2
fn by_its_value():
    let d: i32
    d = (d = 1)
fn in_part():
    let p: P
    p = P(x: 1)
    p.x = 2
fn a_var(c: bool) -> i32:
    var v: i32
    if c:
        v = 1
    v = 2
    v = 3
    return v
";
        assert_eq!(
            said(src),
            vec![
                ("a", set("a")),
                ("b", maybe_set("b")),
                ("d", set("d")),
                ("p.x", set("p")),
            ]
        );
    }

    #[test]
    fn a_branch_that_leaves_assigns_nothing() {
        let src = "\
enum(u8) Color:
    red
    green
    blue
fn returns(c: bool) -> i32:
    let x: i32
    if c:
        x = 1
    else:
        return 0
    return x
fn traps(c: bool) -> i32:
    let x: i32
    if c:
        todo
    else:
        x = 1
    return x
fn arms(c: Color) -> i32:
    let x: i32
    match c:
        .red:
            x = 1
        .green:
            return 0
        else:
            x = 3
    return x
fn loops(n: i32) -> i32:
    var total = 0
    for i in 0..n:
        let x: i32
        if i == 1:
            continue
        else if i == 2:
            break
        else:
            x = i
        total += x
    return total
fn short(c: bool) -> i32:
    let x: i32
    c or return 0
    x = 1
    return x
";
        assert_eq!(said(src), vec![]);
        let src = "\
enum(u8) Color:
    red
    green
fn arms(c: Color) -> i32:
    let x: i32
    match c:
        .red:
            x = 1
        .green:
            pass
    return x
";
        assert_eq!(said(src), vec![("x", maybe_unset("x"))]);
    }

    #[test]
    fn what_is_never_reached_is_not_reported() {
        let src = "\
fn f(c: bool) -> i32:
    let x: i32
    return 0
    if c:
        return x
    x = 1
    x = 2
    return x
fn g() -> i32:
    let x: i32
    while true:
        pass
    return x
fn h(c: bool, d: bool) -> i32:
    let x: i32
    x = 1
    while c:
        if d:
            continue
        return x
        x = 2
    return x
";
        assert_eq!(said(src), vec![]);
    }

    #[test]
    fn a_loop_may_run_any_number_of_times() {
        let src = "\
extern:
    fn next() -> i32
fn each_time(c: bool):
    let x: i32
    while c:
        x = next()
fn once_or_never(c: bool) -> i32:
    let y: i32
    while c:
        y = next()
        break
    return y
fn not_once(c: bool) -> i32:
    var z: i32
    while c:
        z = next()
    return z
fn whatever_its_condition() -> i32:
    let w: i32
    while true:
        w = next()
        break
    return w
fn counted() -> i32:
    var s: i32
    for i in 0..3:
        s = i
    return s
";
        assert_eq!(
            said(src),
            vec![
                ("x", maybe_set("x")),
                ("y", maybe_unset("y")),
                ("z", maybe_unset("z")),
                ("w", maybe_unset("w")),
                ("s", maybe_unset("s")),
            ]
        );
    }

    #[test]
    fn what_leaves_a_loop_or_goes_around_it_is_followed() {
        let src = "\
extern:
    fn next() -> i32
enum(u8) Color:
    red
    green
fn after_a_break(c: bool, d: bool):
    let a: i32
    while c:
        if d:
            a = 1
            break
    a = 2
fn around(c: bool, d: bool):
    let b: i32
    while c:
        if d:
            b = 1
            continue
        break
fn before_the_one_that_goes_around(c: bool, d: bool):
    let e: i32
    while c:
        if d:
            e = 1
            break
        e = 2
fn in_a_loop_in_it(c: bool):
    let g: i32
    while c:
        while c:
            g = 1
            break
fn for_each_member():
    let h: i32
    for m in Color:
        h = 1
fn in_its_body(c: bool) -> i32:
    var total = 0
    while c:
        let t: i32
        t = next()
        total += t
    return total
";
        assert_eq!(
            said(src),
            vec![
                ("a", maybe_set("a")),
                ("b", maybe_set("b")),
                ("e", maybe_set("e")),
                ("g", maybe_set("g")),
                ("h", maybe_set("h")),
            ]
        );
        // The first assignment in the loop is the one reported: the next
        // time around, it may be the second.
        let at = src.find("e = 1").unwrap();
        let errors = check_src(src).unwrap_err();
        assert_eq!(errors[2].span.unwrap().start, at);
    }

    #[test]
    fn the_condition_of_a_while_runs_at_least_once() {
        let src = "\
extern:
    fn next() -> i32
fn f() -> i32:
    var line: i32
    var total = 0
    while (line = next()) != 0:
        total += line
    return total + line
";
        assert_eq!(said(src), vec![]);
        let src = "\
extern:
    fn next() -> i32
fn f():
    let line: i32
    while (line = next()) != 0:
        pass
";
        assert_eq!(said(src), vec![("line", maybe_set("line"))]);
    }

    #[test]
    fn the_right_of_and_and_or_may_not_run() {
        let src = "\
extern:
    fn next() -> i32
fn f(ready: bool) -> i32:
    var line: i32
    if ready and (line = next()) != 0:
        return line
    return 0
fn g(ready: bool) -> i32:
    var n: i32
    let all = (n = next()) != 0 and ready
    return n
";
        assert_eq!(said(src), vec![("line", maybe_unset("line"))]);
    }

    #[test]
    fn operands_are_followed_in_the_order_they_are_evaluated() {
        // What is typed by another operand is lowered after it, wherever it
        // is written: an argument that settles no type parameter, and a
        // `.name` beside what says which union it is of.
        let src = "\
union Shape:
    circle: i32
    empty
fn(T) first(n: i32, v: T) -> i32:
    return n
fn make(n: i32) -> Shape:
    return .circle(n)
fn read_first(seed: i32) -> i32:
    var a: i32
    return first(a, (a = seed))
fn assigned_first(seed: i32) -> i32:
    var b: i32
    return first((b = seed), b)
fn dot_read_first() -> bool:
    var d: i32
    return .circle(d) == make((d = 7))
fn dot_assigned_first() -> bool:
    var e: i32
    return .circle((e = 7)) == make(e)
fn assigned_by_both(seed: i32) -> i32:
    let g: i32
    return first((g = seed), (g = seed))
fn assigned_within(seed: i32) -> i32:
    var h: i32
    return first(first((h = seed), 0), h)
fn maybe_assigned(c: bool) -> bool:
    var i: i32
    return first(0, c and (i = 1) == 1) == 0 and .circle(i) == make(0)
";
        assert_eq!(
            said(src),
            vec![
                ("a", unset("a")),
                ("d", unset("d")),
                ("g", set("g")),
                ("i", maybe_unset("i")),
            ]
        );
        // Where each is reported is where it is written.
        let errors = check_src(src).unwrap_err();
        let starts: Vec<_> = errors.iter().map(|e| e.span.unwrap().start).collect();
        let at = |text: &str| src.find(text).unwrap();
        assert_eq!(
            starts,
            [
                at("a, (a = seed)"),
                at("d) == make"),
                at("g = seed))"),
                at("i) == make(0)"),
            ]
        );
    }

    #[test]
    fn a_defer_is_checked_where_it_is_written() {
        let src = "\
extern:
    fn log(n: i32)
fn reads():
    let x: i32
    defer log(x)
    x = 1
fn assigns():
    let y: i32
    defer y = 1
    log(0)
fn assigns_a_var() -> i32:
    var z: i32
    defer z = 1
    return z
fn its_own():
    defer:
        let w: i32
        w = 1
        log(w)
    log(0)
fn assigned_before():
    let v: i32
    v = 1
    defer v = 2
    log(v)
";
        let initializes = "can't initialize `y` in a `defer`: it runs as the block is left, \
                           after what follows it";
        assert_eq!(
            said(src),
            vec![
                ("x", unset("x")),
                ("y", initializes.to_string()),
                ("z", unset("z")),
                ("v", set("v")),
            ]
        );
    }

    #[test]
    fn a_function_captures_what_has_a_value() {
        let src = "\
fn f() -> i32:
    let x: i32
    let y: i32
    y = 2
    fn g() -> i32:
        return y + x
    x = 1
    return g()
";
        assert_eq!(said(src), vec![("x", unset("x"))]);
        let at = src.find("x\n    x = 1").unwrap();
        assert_eq!(check_src(src).unwrap_err()[0].span.unwrap().start, at);
    }

    #[test]
    fn one_mistake_is_reported_once() {
        let src = "\
extern:
    fn log(n: i32)
fn f(c: bool):
    let x: i32
    log(x)
    log(x)
    x = 1
    x = 2
    x = 3
    log(x)
";
        assert_eq!(said(src), vec![("x", unset("x")), ("x", set("x"))]);
    }

    #[test]
    fn what_is_declared_is_names_of_a_type() {
        let src = "\
let global: i32
var (first, second): tuple(i32, i32)
let Int: type
fn f() -> i32:
    let a
    var (b, c)
    let (d, _): tuple(i32, i32)
    let (): tuple()
    let ((e, g), (h,)): tuple(tuple(i32, bool), tuple(i32))
    let Local: type
    e = 1
    h = 2
    return e + h + global
";
        let untyped = |pattern: &str, keyword: &str| {
            format!(
                "`{pattern}` needs a type: a `{keyword}` without a value has nothing to infer \
                 one from"
            )
        };
        let no_value = |name: &str| {
            format!("`{name}` needs a value: only a variable of a function is declared without one")
        };
        let nothing = |pattern: &str| {
            format!("`{pattern}` binds nothing: a binding without a value only declares names")
        };
        assert_eq!(
            said(src),
            vec![
                ("Int", no_value("Int")),
                ("global", no_value("global")),
                ("(first, second)", no_value("(first, second)")),
                ("a", untyped("a", "let")),
                ("(b, c)", untyped("(b, c)", "var")),
                ("_", nothing("_")),
                ("()", nothing("()")),
                ("Local", no_value("Local")),
            ]
        );
    }

    #[test]
    fn a_generic_function_is_checked_as_declared() {
        let src = "\
fn(T) pick(c: bool, a: T, b: T) -> T:
    let x: T
    if c:
        x = a
    else:
        x = b
    return x
fn(T) lost(c: bool, a: T) -> T:
    let x: T
    if c:
        x = a
    return x
fn f() -> i32:
    return pick(true, 1, 2) + lost(true, 3)
";
        assert_eq!(said(src), vec![("x", maybe_unset("x"))]);
    }
}
