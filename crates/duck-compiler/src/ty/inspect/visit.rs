//! Every statement and expression of an item, for what looks at them all
//! rather than for the one at a place.

use crate::parse::{self, Entry, ExprKind, FnSig, ItemKind, StmtKind};

/// A statement or an expression that a visit of an item comes to.
pub(super) enum Node<'p> {
    Stmt(&'p parse::Stmt),
    Expr(&'p parse::Expr),
}

/// Calls `visit` with every statement and expression in `item`, each before
/// those within it.
pub(super) fn each<'p>(item: &'p parse::Item, visit: &mut dyn FnMut(Node<'p>)) {
    let defaults = |sig: &'p FnSig, visit: &mut dyn FnMut(Node<'p>)| {
        for default in sig.params.iter().filter_map(|param| param.default.as_ref()) {
            expr(default, visit);
        }
    };
    match &item.kind {
        ItemKind::Fn(decl) => {
            defaults(&decl.sig, visit);
            block(&decl.body, visit);
        }
        ItemKind::Extern(extern_block) => {
            for imported in &extern_block.fns {
                defaults(&imported.sig, visit);
            }
        }
        ItemKind::Struct(decl) => {
            let fields = decl.entries.iter().filter_map(Entry::own);
            for default in fields.filter_map(|field| field.default.as_ref()) {
                expr(default, visit);
            }
        }
        ItemKind::Enum(decl) => {
            let members = decl.entries.iter().filter_map(Entry::own);
            for value in members.filter_map(|member| member.value.as_ref()) {
                expr(value, visit);
            }
        }
        ItemKind::Binding(binding) => expr(&binding.value, visit),
        ItemKind::Union(_) | ItemKind::Use(_) => {}
    }
}

fn block<'p>(block: &'p [parse::Stmt], visit: &mut dyn FnMut(Node<'p>)) {
    for stmt in block {
        visit(Node::Stmt(stmt));
        match &stmt.kind {
            StmtKind::Binding(binding) => expr(&binding.value, visit),
            StmtKind::Expr(value) => expr(value, visit),
            StmtKind::If {
                cond,
                then_body,
                else_body,
            } => {
                expr(cond, visit);
                self::block(then_body, visit);
                self::block(else_body.as_deref().unwrap_or_default(), visit);
            }
            StmtKind::While { cond, body } => {
                expr(cond, visit);
                self::block(body, visit);
            }
            StmtKind::For { iter, body, .. } => {
                expr(iter, visit);
                self::block(body, visit);
            }
            StmtKind::Match { value, arms } => {
                expr(value, visit);
                for arm in arms {
                    self::block(&arm.body, visit);
                }
            }
            StmtKind::Defer(body) => self::block(body, visit),
            StmtKind::Pass => {}
        }
    }
}

fn expr<'p>(expr: &'p parse::Expr, visit: &mut dyn FnMut(Node<'p>)) {
    visit(Node::Expr(expr));
    match &expr.kind {
        ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Str(_)
        | ExprKind::Bool(_)
        | ExprKind::Unit
        | ExprKind::Name(_)
        | ExprKind::Module(_)
        | ExprKind::Placeholder
        | ExprKind::Dot(_)
        | ExprKind::FnType(_)
        | ExprKind::Break
        | ExprKind::Continue => {}
        ExprKind::Tuple(elems) | ExprKind::List(elems) => {
            for elem in elems {
                self::expr(elem, visit);
            }
        }
        ExprKind::Repeat(a, b)
        | ExprKind::Binary(_, a, b)
        | ExprKind::Index(a, b)
        | ExprKind::Pipe(a, b) => {
            self::expr(a, visit);
            self::expr(b, visit);
        }
        ExprKind::Assign { target, value, .. } => {
            self::expr(target, visit);
            self::expr(value, visit);
        }
        ExprKind::Unary(_, inner)
        | ExprKind::Deref(inner)
        | ExprKind::AddrOf(_, inner)
        | ExprKind::Field(inner, _)
        | ExprKind::Cast(inner, _, _) => self::expr(inner, visit),
        ExprKind::Call(callee, args) => {
            self::expr(callee, visit);
            for arg in args {
                self::expr(&arg.value, visit);
            }
        }
        ExprKind::Return(value) => {
            if let Some(value) = value {
                self::expr(value, visit);
            }
        }
    }
}
