//! Names of types: a global `let` of type `type` is bound to a type, written
//! where its value would be, and is that type wherever a type is written.
//! It is no global, and nothing of it is in the module.

use std::mem;

use crate::file::FileId;
use crate::lex::Span;
use crate::load::Program;
use crate::parse::{self, Binding, Mutability, PatternKind};

use super::{Checker, Item, Ty, TypeErrorKind, Visit, pattern_names};

/// A name of a type.
pub(super) struct AliasDef {
    name: String,
    /// The module that declares it, which the type is written in.
    module: FileId,
    /// The item of the program that declares it.
    pub(super) item: usize,
    is_pub: bool,
    /// The type as it is written. `None` for what is no type, which is
    /// reported where it's declared.
    written: Option<parse::Type>,
    /// The type it names, once `resolved` is done. The error type until
    /// then, and for one that failed to resolve.
    ty: Ty,
    resolved: Visit,
}

impl Checker {
    /// Declares the name that `binding` gives a type, which is item `index`
    /// of the program, `item`. Only a `let` of one name does: any other is
    /// reported and declares nothing.
    pub(super) fn declare_alias(&mut self, item: &parse::Item, index: usize, binding: &Binding) {
        let named = matches!(binding.pattern.kind, PatternKind::Name(_));
        let (Mutability::Let, true, [name]) = (
            binding.mutability,
            named,
            &pattern_names(&binding.pattern)[..],
        ) else {
            let span = binding.ty.as_ref().map_or(item.span, |ty| ty.span);
            self.error(TypeErrorKind::TypeOutsideParam, span);
            return;
        };
        let written = self.type_syntax(&binding.value);
        self.aliases.push(AliasDef {
            name: name.name.clone(),
            module: self.module,
            item: index,
            is_pub: item.is_pub,
            written,
            ty: Ty::Error,
            resolved: Visit::New,
        });
        self.declare_item(item, name, Item::Alias(self.aliases.len() - 1));
    }

    /// The type that alias `id` names, which is resolved the first time
    /// it's asked for, where the alias is declared. The error type for one
    /// written with itself, which is reported at `span`, where it is named.
    pub(super) fn alias_ty(&mut self, id: usize, span: Span) -> Ty {
        let def = &self.aliases[id];
        match def.resolved {
            Visit::Done => return def.ty,
            Visit::Active => {
                self.error(TypeErrorKind::RecursiveAlias(def.name.clone()), span);
                return Ty::Error;
            }
            Visit::New => {}
        }
        let (written, is_pub, name) = (def.written.clone(), def.is_pub, def.name.clone());
        self.aliases[id].resolved = Visit::Active;
        // What first names it may be in another module, or be generic.
        let module = mem::replace(&mut self.module, self.aliases[id].module);
        let type_params = mem::take(&mut self.type_params);
        let ty = match &written {
            Some(written) => {
                let ty = self.resolve_ty(written);
                if is_pub {
                    self.check_public(ty, written.span, &name);
                }
                ty
            }
            None => Ty::Error,
        };
        self.module = module;
        self.type_params = type_params;
        let def = &mut self.aliases[id];
        (def.ty, def.resolved) = (ty, Visit::Done);
        ty
    }

    /// The type that alias `id` names, once every alias is resolved.
    pub(super) fn aliased(&self, id: usize) -> Ty {
        self.aliases[id].ty
    }

    /// Resolves each alias that nothing has named yet, so that what it is
    /// written with is checked whether or not it is used.
    pub(super) fn define_aliases(&mut self, program: &Program) {
        for id in 0..self.aliases.len() {
            let span = program.items[self.aliases[id].item].span;
            self.alias_ty(id, span);
        }
    }
}
