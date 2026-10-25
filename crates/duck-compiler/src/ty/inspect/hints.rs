//! What isn't written and would say more of what is: the type of a name
//! that is bound without one, and the parameter that an argument is for.

use std::ops::Range;

use crate::file::FileId;
use crate::parse::{self, Arg, Binding, ExprKind, ItemKind, Pattern, PatternKind, StmtKind};
use crate::visit::{self, Node};

use super::super::Ty;
use super::symbols::bound;
use super::{Analysis, Item, Target};

/// Something to show at a place as if it were written there.
#[derive(Debug, Clone, PartialEq)]
pub struct Hint {
    /// The byte of the file it is shown at.
    pub offset: usize,
    pub label: String,
    pub kind: HintKind,
    /// What is written there for the source to say what the hint shows, if
    /// something can be: the type of a name that is bound alone, as its
    /// file names that type.
    pub insert: Option<String>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HintKind {
    /// `: Type`, after a name.
    Type,
    /// `name: `, before an argument.
    Parameter,
}

impl Analysis {
    /// What to show in bytes `within` of `file`, in order: the type of each
    /// name that a `let`, a `var` or a `for` binds without one, and the
    /// parameter that each argument without a label is given to, unless
    /// the argument is named as the parameter is.
    pub fn hints(&self, file: FileId, within: Range<usize>) -> Vec<Hint> {
        let mut hints = Vec::new();
        let items = self.program.items.iter();
        let overlaps = |item: &&parse::Item| {
            let span = item.span;
            span.file == file && span.start <= within.end && within.start <= span.end
        };
        for item in items.filter(overlaps) {
            if let ItemKind::Binding(binding) = &item.kind {
                self.binding_hints(file, binding, &mut hints);
            }
            visit::each(item, &mut |node| match node {
                Node::Stmt(stmt) => match &stmt.kind {
                    StmtKind::Binding(binding) => self.binding_hints(file, binding, &mut hints),
                    // Nothing writes a type in the head of a `for`.
                    StmtKind::For { index, pattern, .. } => {
                        for pattern in index.iter().chain([pattern]) {
                            self.pattern_hints(None, pattern, &mut hints);
                        }
                    }
                    _ => {}
                },
                Node::Expr(expr) => {
                    if let ExprKind::Call(callee, args) = &expr.kind {
                        self.argument_hints(file, callee, args, &mut hints);
                    }
                }
            });
        }
        hints.retain(|hint| within.start <= hint.offset && hint.offset <= within.end);
        hints.sort_by_key(|hint| hint.offset);
        hints
    }

    /// The type of each name that `binding` binds in `file`, if it writes
    /// none. A type is written after the whole of a pattern, so only that
    /// of a name bound alone is written where it is shown.
    fn binding_hints(&self, file: FileId, binding: &Binding, hints: &mut Vec<Hint>) {
        if binding.ty.is_some() {
            return;
        }
        let alone = matches!(binding.pattern.kind, PatternKind::Name(_));
        self.pattern_hints(alone.then_some(file), &binding.pattern, hints);
    }

    /// The type of each name that `pattern` binds, with what writes it in
    /// the file `written`, if a type may be written after the name there.
    fn pattern_hints(&self, written: Option<FileId>, pattern: &Pattern, hints: &mut Vec<Hint>) {
        let mut names = Vec::new();
        bound(pattern, &mut names);
        for (_, span) in names {
            let Some(ty) = self.ty_at(span) else {
                continue;
            };
            let insert = written.and_then(|file| self.written_type(file, ty));
            hints.push(Hint {
                offset: span.end,
                label: format!(": {}", self.ck.ty_name(ty)),
                kind: HintKind::Type,
                insert: insert.map(|ty| format!(": {ty}")),
            });
        }
    }

    /// `ty` as `file` writes it, if it can: each struct, union and enum by
    /// the name that `file` has for it, or by a module that `file` names
    /// and that lets it be seen. `None` for a type that nothing writes
    /// there: that of a function itself, one that a result hides, one that
    /// no name of `file` leads to, or a type that failed to check.
    pub(super) fn written_type(&self, file: FileId, ty: Ty) -> Option<String> {
        let written = |ty: &Ty| self.written_type(file, *ty);
        let all = |tys: &[Ty]| tys.iter().map(written).collect::<Option<Vec<_>>>();
        Some(match ty {
            Ty::Prim(_) | Ty::Unit | Ty::Param(_) | Ty::AnyEnum => self.ck.ty_name(ty),
            Ty::Enum(id) => {
                let def = &self.ck.enums[id.0 as usize];
                self.named_from(file, def.module, &def.name, Item::Enum(id))?
            }
            Ty::Struct(id) => {
                let def = &self.ck.structs[id.0 as usize];
                let Some(instance) = &def.instance else {
                    return self.named_from(file, def.module, &def.name, Item::Struct(id));
                };
                let generic = &self.ck.structs[instance.generic.0 as usize];
                // One of the language's own is named as it is anywhere, but
                // for the list of a bound, which nothing names.
                let name = match self.is_builtin(id) {
                    true => (self.ck.list != Some(instance.generic)).then(|| generic.name.clone()),
                    false => {
                        let item = Item::Struct(instance.generic);
                        self.named_from(file, generic.module, &generic.name, item)
                    }
                };
                format!("{}({})", name?, all(&instance.args)?.join(", "))
            }
            Ty::Ptr(id) => {
                let pointee = written(&self.ck.pointee(id))?;
                match self.ck.writes(ty) {
                    true => format!("&var {pointee}"),
                    false => format!("&{pointee}"),
                }
            }
            Ty::Array(id) => {
                let element = written(&self.ck.element(id))?;
                match self.ck.writes(ty) {
                    true => format!("varray({element})"),
                    false => format!("array({element})"),
                }
            }
            Ty::Tuple(id) => format!("tuple({})", all(&self.ck.tuples[id.0 as usize])?.join(", ")),
            Ty::Fn(id) => {
                let (params, ret) = &self.ck.fn_tys[id.0 as usize];
                let params = all(params)?.join(", ");
                match ret {
                    Ty::Unit => format!("fn({params})"),
                    ret => format!("fn({params}) -> {}", written(ret)?),
                }
            }
            Ty::Func(_) | Ty::Opaque(_) | Ty::Type | Ty::Never | Ty::Error => return None,
        })
    }

    /// What `file` writes for `item`, which `module` declares as `name`:
    /// the name alone, if it names the item there, or else after the first
    /// name that `file` has for `module`, if the module lets it be seen.
    fn named_from(&self, file: FileId, module: FileId, name: &str, item: Item) -> Option<String> {
        if self.item(file, name) == Some(item) {
            return Some(name.to_string());
        }
        let seen = self.member(file, module, name) == Some(item);
        let scope = self.ck.scopes.get(&file).into_iter().flatten();
        let mut modules: Vec<_> = scope
            .filter(|(_, entry)| entry.item == Item::Module(module))
            .map(|(module, _)| module)
            .collect();
        modules.sort();
        let module = modules.first().filter(|_| seen)?;
        Some(format!("{module}.{name}"))
    }

    /// The parameter that each of `args` is given to by its place, in a
    /// call of `callee` in `file`, if that names a function.
    fn argument_hints(
        &self,
        file: FileId,
        callee: &parse::Expr,
        args: &[Arg],
        hints: &mut Vec<Hint>,
    ) {
        let named = match &callee.kind {
            ExprKind::Name(_) => callee.span.start,
            ExprKind::Field(_, field) => field.span.start,
            _ => return,
        };
        let site = self.locate(file, named, false);
        let Some(Target::Item(item @ (Item::Func(_) | Item::GenericFn(_)))) = self.target(&site)
        else {
            return;
        };
        let Some((_, sig)) = self.fn_decl(item) else {
            return;
        };
        // Those given by their place come first.
        let placed = args.iter().take_while(|arg| arg.label.is_none());
        for (arg, param) in placed.zip(&sig.params) {
            let name = &param.name.name;
            let says = match &arg.value.kind {
                ExprKind::Name(written) => written == name,
                ExprKind::Field(_, field) => field.name == *name,
                _ => false,
            };
            if !says {
                hints.push(Hint {
                    offset: arg.value.span.start,
                    label: format!("{name}: "),
                    kind: HintKind::Parameter,
                    insert: None,
                });
            }
        }
    }
}
