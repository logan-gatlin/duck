//! What a constant is evaluated to, as it would be written: the checker
//! folds each where it is first used, and keeps the scalars of its value,
//! some of which only linking knows.

use crate::ir::Const;

use super::super::{Prim, Scalar, Slots, Ty};
use super::Analysis;

/// The longest value shown of a constant: one longer says less of it than
/// its type does.
const MAX_VALUE: usize = 60;

impl Analysis {
    /// What global `index` is evaluated to, if it is a `let`, which is its
    /// value wherever it is used, and its initializer has one.
    pub(super) fn global_value(&self, index: usize) -> Option<String> {
        let global = self.ck.globals.get(index)?.as_ref()?;
        match &global.slots {
            Slots::Const(scalars) if global.known => {
                self.value_text(global.ty, &self.consts(scalars)?)
            }
            _ => None,
        }
    }

    /// What the member `name` of the enum that item `index` of the program
    /// declares is evaluated to, if it is one whose value is known.
    pub(super) fn member_value(&self, index: usize, name: &str) -> Option<String> {
        let def = self.ck.enums.iter().find(|def| def.item == index)?;
        let member = def.members.iter().find(|member| member.name == name)?;
        match member.known {
            true => self.value_text(def.ty, &self.consts(&member.value)?),
            false => None,
        }
    }

    /// The constants that `scalars` are, if linking knows them all: one
    /// that failed or didn't run has none.
    fn consts(&self, scalars: &[Scalar]) -> Option<Vec<Const>> {
        scalars.iter().map(|s| self.ck.link.known(*s)).collect()
    }

    /// `consts`, the scalars of a constant of type `ty`, as the value would
    /// be written, unless that is too long to say much.
    fn value_text(&self, ty: Ty, consts: &[Const]) -> Option<String> {
        let text = self.written(ty, consts)?;
        (text.len() <= MAX_VALUE).then_some(text)
    }

    /// `consts`, the scalars of a value of type `ty`, as it would be
    /// written: a number, a `bool`, a member of an enum, or a tuple or a
    /// struct of those. `None` for any other: an address says nothing of
    /// what is there, and nothing writes the tag of a union.
    fn written(&self, ty: Ty, consts: &[Const]) -> Option<String> {
        let ty = self.ck.known(ty);
        match (ty, consts) {
            (Ty::Prim(prim), [scalar]) => number(self.ck.fixed(prim), *scalar),
            (Ty::Enum(id), _) => {
                let mut members = self.ck.enums[id.0 as usize].members.iter();
                let member = members.find(|member| {
                    member.known && self.consts(&member.value).as_deref() == Some(consts)
                })?;
                Some(format!(".{}", member.name))
            }
            (Ty::Struct(_) | Ty::Tuple(_), _) if self.ck.union_id(ty).is_none() => {
                let mut rest = consts;
                let mut parts = Vec::new();
                for member in self.ck.members(ty) {
                    let (own, after) = rest.split_at_checked(self.ck.val_types(member).len())?;
                    parts.push(self.written(member, own)?);
                    rest = after;
                }
                let Ty::Struct(id) = ty else {
                    return Some(format!("({})", parts.join(", ")));
                };
                let def = &self.ck.structs[id.0 as usize];
                let fields = def.fields.iter().zip(parts);
                let fields: Vec<_> = fields
                    .map(|(field, value)| format!("{}: {value}", field.name))
                    .collect();
                Some(format!("{}({})", def.name, fields.join(", ")))
            }
            _ => None,
        }
    }
}

/// `scalar`, which holds a number or a `bool` of type `prim`, as it is
/// written. `None` for a float that nothing writes.
fn number(prim: Prim, scalar: Const) -> Option<String> {
    Some(match (prim, scalar) {
        (Prim::Bool, Const::I32(bit)) => (bit != 0).to_string(),
        (Prim::I8, Const::I32(n)) => (n as i8).to_string(),
        (Prim::I16, Const::I32(n)) => (n as i16).to_string(),
        (Prim::I32, Const::I32(n)) => n.to_string(),
        (Prim::I64, Const::I64(n)) => n.to_string(),
        (Prim::U8, Const::I32(n)) => (n as u8).to_string(),
        (Prim::U16, Const::I32(n)) => (n as u16).to_string(),
        (Prim::U32, Const::I32(n)) => (n as u32).to_string(),
        (Prim::U64, Const::I64(n)) => (n as u64).to_string(),
        (Prim::F32, Const::F32(x)) if x.is_finite() => format!("{x:?}"),
        (Prim::F64, Const::F64(x)) if x.is_finite() => format!("{x:?}"),
        _ => return None,
    })
}
