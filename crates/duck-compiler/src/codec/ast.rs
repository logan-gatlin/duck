//! The syntax tree as bytes, so that the declarations of a package can be
//! kept, and read back, without its source being parsed again. Every field
//! is written as it is, in the order it is declared, so what is read is
//! exactly what was parsed: nothing is derived from the rest.

use crate::codec::{Decode, DecodeError, Encode, Reader, Writer, bad, lists};
use crate::parse::{
    Arg, Arm, BinOp, Binding, Entry, EnumDecl, Expr, ExprKind, ExternBlock, ExternFn, Field,
    FnDecl, FnSig, Ident, Item, ItemKind, Member, Module, Mutability, Param, Pattern, PatternKind,
    Stmt, StmtKind, StructDecl, Type, TypeArg, TypeKind, TypeParam, TypeUse, UnaryOp, UnionDecl,
    Use, UsePath, Variant,
};

lists!(
    Item,
    UsePath,
    Ident,
    TypeParam,
    Param,
    Type,
    ExternFn,
    Entry<Field>,
    Entry<Member>,
    Entry<Variant>,
    Pattern,
    TypeArg,
    Stmt,
    Arm,
    Expr,
    Arg,
);

impl Encode for Module {
    fn encode(&self, w: &mut Writer) {
        self.items.encode(w);
    }
}

impl Decode for Module {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Module {
            items: Decode::decode(r)?,
        })
    }
}

impl Encode for Item {
    fn encode(&self, w: &mut Writer) {
        self.is_pub.encode(w);
        self.kind.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Item {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Item {
            is_pub: Decode::decode(r)?,
            kind: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for ItemKind {
    fn encode(&self, w: &mut Writer) {
        match self {
            ItemKind::Fn(decl) => {
                w.tag(0);
                decl.encode(w);
            }
            ItemKind::Extern(block) => {
                w.tag(1);
                block.encode(w);
            }
            ItemKind::Struct(decl) => {
                w.tag(2);
                decl.encode(w);
            }
            ItemKind::Enum(decl) => {
                w.tag(3);
                decl.encode(w);
            }
            ItemKind::Union(decl) => {
                w.tag(4);
                decl.encode(w);
            }
            ItemKind::Binding(binding) => {
                w.tag(5);
                binding.encode(w);
            }
            ItemKind::Use(use_) => {
                w.tag(6);
                use_.encode(w);
            }
        }
    }
}

impl Decode for ItemKind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => ItemKind::Fn(Decode::decode(r)?),
            1 => ItemKind::Extern(Decode::decode(r)?),
            2 => ItemKind::Struct(Decode::decode(r)?),
            3 => ItemKind::Enum(Decode::decode(r)?),
            4 => ItemKind::Union(Decode::decode(r)?),
            5 => ItemKind::Binding(Decode::decode(r)?),
            6 => ItemKind::Use(Decode::decode(r)?),
            tag => return Err(bad("item", tag)),
        })
    }
}

impl Encode for Use {
    fn encode(&self, w: &mut Writer) {
        self.paths.encode(w);
    }
}

impl Decode for Use {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Use {
            paths: Decode::decode(r)?,
        })
    }
}

impl Encode for UsePath {
    fn encode(&self, w: &mut Writer) {
        self.segments.encode(w);
        self.alias.encode(w);
    }
}

impl Decode for UsePath {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(UsePath {
            segments: Decode::decode(r)?,
            alias: Decode::decode(r)?,
        })
    }
}

impl Encode for FnDecl {
    fn encode(&self, w: &mut Writer) {
        self.sig.encode(w);
        self.body.encode(w);
        self.interface.encode(w);
        self.export_name.encode(w);
    }
}

impl Decode for FnDecl {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(FnDecl {
            sig: Decode::decode(r)?,
            body: Decode::decode(r)?,
            interface: Decode::decode(r)?,
            export_name: Decode::decode(r)?,
        })
    }
}

impl Encode for FnSig {
    fn encode(&self, w: &mut Writer) {
        self.type_params.encode(w);
        self.name.encode(w);
        self.params.encode(w);
        self.ret.encode(w);
    }
}

impl Decode for FnSig {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(FnSig {
            type_params: Decode::decode(r)?,
            name: Decode::decode(r)?,
            params: Decode::decode(r)?,
            ret: Decode::decode(r)?,
        })
    }
}

impl Encode for TypeParam {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.bound.encode(w);
        self.default.encode(w);
    }
}

impl Decode for TypeParam {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(TypeParam {
            name: Decode::decode(r)?,
            bound: Decode::decode(r)?,
            default: Decode::decode(r)?,
        })
    }
}

impl Encode for ExternBlock {
    fn encode(&self, w: &mut Writer) {
        self.module.encode(w);
        self.fns.encode(w);
    }
}

impl Decode for ExternBlock {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ExternBlock {
            module: Decode::decode(r)?,
            fns: Decode::decode(r)?,
        })
    }
}

impl Encode for ExternFn {
    fn encode(&self, w: &mut Writer) {
        self.is_pub.encode(w);
        self.sig.encode(w);
        self.import_name.encode(w);
        self.span.encode(w);
    }
}

impl Decode for ExternFn {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(ExternFn {
            is_pub: Decode::decode(r)?,
            sig: Decode::decode(r)?,
            import_name: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for Param {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.ty.encode(w);
        self.default.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Param {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Param {
            name: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            default: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for StructDecl {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.params.encode(w);
        self.entries.encode(w);
    }
}

impl Decode for StructDecl {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(StructDecl {
            name: Decode::decode(r)?,
            params: Decode::decode(r)?,
            entries: Decode::decode(r)?,
        })
    }
}

impl<T: Encode> Encode for Entry<T> {
    fn encode(&self, w: &mut Writer) {
        match self {
            Entry::Own(own) => {
                w.tag(0);
                own.encode(w);
            }
            Entry::Use(used) => {
                w.tag(1);
                used.encode(w);
            }
        }
    }
}

impl Encode for TypeUse {
    fn encode(&self, w: &mut Writer) {
        self.ty.encode(w);
        self.name.encode(w);
        self.is_pub.encode(w);
        self.span.encode(w);
    }
}

impl Decode for TypeUse {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(TypeUse {
            ty: Decode::decode(r)?,
            name: Decode::decode(r)?,
            is_pub: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl<T: Decode> Decode for Entry<T> {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Entry::Own(Decode::decode(r)?),
            1 => Entry::Use(Decode::decode(r)?),
            tag => return Err(bad("entry", tag)),
        })
    }
}

impl Encode for Field {
    fn encode(&self, w: &mut Writer) {
        self.is_pub.encode(w);
        self.name.encode(w);
        self.ty.encode(w);
        self.default.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Field {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Field {
            is_pub: Decode::decode(r)?,
            name: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            default: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for EnumDecl {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.ty.encode(w);
        self.entries.encode(w);
    }
}

impl Decode for EnumDecl {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(EnumDecl {
            name: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            entries: Decode::decode(r)?,
        })
    }
}

impl Encode for Member {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.value.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Member {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Member {
            name: Decode::decode(r)?,
            value: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for UnionDecl {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.params.encode(w);
        self.entries.encode(w);
    }
}

impl Decode for UnionDecl {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(UnionDecl {
            name: Decode::decode(r)?,
            params: Decode::decode(r)?,
            entries: Decode::decode(r)?,
        })
    }
}

impl Encode for Variant {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.ty.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Variant {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Variant {
            name: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for Binding {
    fn encode(&self, w: &mut Writer) {
        self.mutability.encode(w);
        self.pattern.encode(w);
        self.ty.encode(w);
        self.value.encode(w);
    }
}

impl Decode for Binding {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Binding {
            mutability: Decode::decode(r)?,
            pattern: Decode::decode(r)?,
            ty: Decode::decode(r)?,
            value: Decode::decode(r)?,
        })
    }
}

impl Encode for Pattern {
    fn encode(&self, w: &mut Writer) {
        self.kind.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Pattern {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Pattern {
            kind: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for PatternKind {
    fn encode(&self, w: &mut Writer) {
        match self {
            PatternKind::Name(name) => {
                w.tag(0);
                name.encode(w);
            }
            PatternKind::Discard => w.tag(1),
            PatternKind::Tuple(elements) => {
                w.tag(2);
                elements.encode(w);
            }
            PatternKind::Variant(name, inner) => {
                w.tag(3);
                name.encode(w);
                inner.encode(w);
            }
            PatternKind::Literal(value) => {
                w.tag(4);
                value.encode(w);
            }
            PatternKind::Array(elements) => {
                w.tag(5);
                elements.encode(w);
            }
        }
    }
}

impl Decode for PatternKind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => PatternKind::Name(Decode::decode(r)?),
            1 => PatternKind::Discard,
            2 => PatternKind::Tuple(Decode::decode(r)?),
            3 => PatternKind::Variant(Decode::decode(r)?, Decode::decode(r)?),
            4 => PatternKind::Literal(Decode::decode(r)?),
            5 => PatternKind::Array(Decode::decode(r)?),
            tag => return Err(bad("pattern", tag)),
        })
    }
}

impl Encode for Mutability {
    fn encode(&self, w: &mut Writer) {
        match self {
            Mutability::Let => w.tag(0),
            Mutability::Var => w.tag(1),
        }
    }
}

impl Decode for Mutability {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => Mutability::Let,
            1 => Mutability::Var,
            tag => return Err(bad("mutability", tag)),
        })
    }
}

impl Encode for Ident {
    fn encode(&self, w: &mut Writer) {
        self.name.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Ident {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Ident {
            name: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for Type {
    fn encode(&self, w: &mut Writer) {
        self.kind.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Type {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Type {
            kind: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for TypeArg {
    fn encode(&self, w: &mut Writer) {
        self.label.encode(w);
        self.ty.encode(w);
    }
}

impl Decode for TypeArg {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(TypeArg {
            label: Decode::decode(r)?,
            ty: Decode::decode(r)?,
        })
    }
}

impl Encode for TypeKind {
    fn encode(&self, w: &mut Writer) {
        match self {
            TypeKind::Named(name, args) => {
                w.tag(0);
                name.encode(w);
                args.encode(w);
            }
            TypeKind::Pointer(mutability, pointee) => {
                w.tag(1);
                mutability.encode(w);
                pointee.encode(w);
            }
            TypeKind::Qualified(module, ty) => {
                w.tag(2);
                module.encode(w);
                ty.encode(w);
            }
            TypeKind::Module(name) => {
                w.tag(3);
                name.encode(w);
            }
            TypeKind::Fn(params, ret) => {
                w.tag(4);
                params.encode(w);
                ret.encode(w);
            }
            TypeKind::Todo => w.tag(5),
        }
    }
}

impl Decode for TypeKind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => TypeKind::Named(Decode::decode(r)?, Decode::decode(r)?),
            1 => TypeKind::Pointer(Decode::decode(r)?, Decode::decode(r)?),
            2 => TypeKind::Qualified(Decode::decode(r)?, Decode::decode(r)?),
            3 => TypeKind::Module(Decode::decode(r)?),
            4 => TypeKind::Fn(Decode::decode(r)?, Decode::decode(r)?),
            5 => TypeKind::Todo,
            tag => return Err(bad("type", tag)),
        })
    }
}

impl Encode for Stmt {
    fn encode(&self, w: &mut Writer) {
        self.kind.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Stmt {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Stmt {
            kind: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for StmtKind {
    fn encode(&self, w: &mut Writer) {
        match self {
            StmtKind::Binding(binding) => {
                w.tag(0);
                binding.encode(w);
            }
            StmtKind::Expr(expr) => {
                w.tag(1);
                expr.encode(w);
            }
            StmtKind::If {
                cond,
                then_body,
                else_body,
            } => {
                w.tag(2);
                cond.encode(w);
                then_body.encode(w);
                else_body.encode(w);
            }
            StmtKind::While { cond, body } => {
                w.tag(3);
                cond.encode(w);
                body.encode(w);
            }
            StmtKind::For {
                index,
                addr,
                pattern,
                iter,
                body,
            } => {
                w.tag(4);
                index.encode(w);
                addr.encode(w);
                pattern.encode(w);
                iter.encode(w);
                body.encode(w);
            }
            StmtKind::Match { value, arms } => {
                w.tag(5);
                value.encode(w);
                arms.encode(w);
            }
            StmtKind::Pass => w.tag(6),
            StmtKind::Defer(body) => {
                w.tag(7);
                body.encode(w);
            }
            StmtKind::Fn(decl) => {
                w.tag(8);
                decl.encode(w);
            }
        }
    }
}

impl Decode for StmtKind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => StmtKind::Binding(Decode::decode(r)?),
            1 => StmtKind::Expr(Decode::decode(r)?),
            2 => StmtKind::If {
                cond: Decode::decode(r)?,
                then_body: Decode::decode(r)?,
                else_body: Decode::decode(r)?,
            },
            3 => StmtKind::While {
                cond: Decode::decode(r)?,
                body: Decode::decode(r)?,
            },
            4 => StmtKind::For {
                index: Decode::decode(r)?,
                addr: Decode::decode(r)?,
                pattern: Decode::decode(r)?,
                iter: Decode::decode(r)?,
                body: Decode::decode(r)?,
            },
            5 => StmtKind::Match {
                value: Decode::decode(r)?,
                arms: Decode::decode(r)?,
            },
            6 => StmtKind::Pass,
            7 => StmtKind::Defer(Decode::decode(r)?),
            8 => StmtKind::Fn(Decode::decode(r)?),
            tag => return Err(bad("statement", tag)),
        })
    }
}

impl Encode for Arm {
    fn encode(&self, w: &mut Writer) {
        self.pattern.encode(w);
        self.body.encode(w);
    }
}

impl Decode for Arm {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Arm {
            pattern: Decode::decode(r)?,
            body: Decode::decode(r)?,
        })
    }
}

impl Encode for Expr {
    fn encode(&self, w: &mut Writer) {
        self.kind.encode(w);
        self.span.encode(w);
    }
}

impl Decode for Expr {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Expr {
            kind: Decode::decode(r)?,
            span: Decode::decode(r)?,
        })
    }
}

impl Encode for ExprKind {
    fn encode(&self, w: &mut Writer) {
        match self {
            ExprKind::Int(n) => {
                w.tag(0);
                n.encode(w);
            }
            ExprKind::Float(x) => {
                w.tag(1);
                x.encode(w);
            }
            ExprKind::Str(s) => {
                w.tag(2);
                s.encode(w);
            }
            ExprKind::Char(c) => {
                w.tag(3);
                c.encode(w);
            }
            ExprKind::Bool(b) => {
                w.tag(4);
                b.encode(w);
            }
            ExprKind::Unit => w.tag(5),
            ExprKind::Name(name) => {
                w.tag(6);
                name.encode(w);
            }
            ExprKind::Module(name) => {
                w.tag(7);
                name.encode(w);
            }
            ExprKind::Tuple(elements) => {
                w.tag(8);
                elements.encode(w);
            }
            ExprKind::List(elements) => {
                w.tag(9);
                elements.encode(w);
            }
            ExprKind::Repeat(value, len) => {
                w.tag(10);
                value.encode(w);
                len.encode(w);
            }
            ExprKind::Range(start, end) => {
                w.tag(11);
                start.encode(w);
                end.encode(w);
            }
            ExprKind::Unary(op, operand) => {
                w.tag(12);
                op.encode(w);
                operand.encode(w);
            }
            ExprKind::Binary(op, lhs, rhs) => {
                w.tag(13);
                op.encode(w);
                lhs.encode(w);
                rhs.encode(w);
            }
            ExprKind::Call(callee, args) => {
                w.tag(14);
                callee.encode(w);
                args.encode(w);
            }
            ExprKind::Index(array, index) => {
                w.tag(15);
                array.encode(w);
                index.encode(w);
            }
            ExprKind::Slice(array, start, end) => {
                w.tag(16);
                array.encode(w);
                start.encode(w);
                end.encode(w);
            }
            ExprKind::Field(value, name) => {
                w.tag(17);
                value.encode(w);
                name.encode(w);
            }
            ExprKind::Deref(pointer) => {
                w.tag(18);
                pointer.encode(w);
            }
            ExprKind::AddrOf(mutability, place) => {
                w.tag(19);
                mutability.encode(w);
                place.encode(w);
            }
            ExprKind::Cast(value, ty, unchecked) => {
                w.tag(20);
                value.encode(w);
                ty.encode(w);
                unchecked.encode(w);
            }
            ExprKind::FnType(ty) => {
                w.tag(21);
                ty.encode(w);
            }
            ExprKind::Pipe(value, body) => {
                w.tag(22);
                value.encode(w);
                body.encode(w);
            }
            ExprKind::Placeholder => w.tag(23),
            ExprKind::Dot(name) => {
                w.tag(24);
                name.encode(w);
            }
            ExprKind::Assign { target, op, value } => {
                w.tag(25);
                target.encode(w);
                op.encode(w);
                value.encode(w);
            }
            ExprKind::Return(value) => {
                w.tag(26);
                value.encode(w);
            }
            ExprKind::Break => w.tag(27),
            ExprKind::Continue => w.tag(28),
            ExprKind::Todo => w.tag(29),
        }
    }
}

impl Decode for ExprKind {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => ExprKind::Int(Decode::decode(r)?),
            1 => ExprKind::Float(Decode::decode(r)?),
            2 => ExprKind::Str(Decode::decode(r)?),
            3 => ExprKind::Char(Decode::decode(r)?),
            4 => ExprKind::Bool(Decode::decode(r)?),
            5 => ExprKind::Unit,
            6 => ExprKind::Name(Decode::decode(r)?),
            7 => ExprKind::Module(Decode::decode(r)?),
            8 => ExprKind::Tuple(Decode::decode(r)?),
            9 => ExprKind::List(Decode::decode(r)?),
            10 => ExprKind::Repeat(Decode::decode(r)?, Decode::decode(r)?),
            11 => ExprKind::Range(Decode::decode(r)?, Decode::decode(r)?),
            12 => ExprKind::Unary(Decode::decode(r)?, Decode::decode(r)?),
            13 => ExprKind::Binary(Decode::decode(r)?, Decode::decode(r)?, Decode::decode(r)?),
            14 => ExprKind::Call(Decode::decode(r)?, Decode::decode(r)?),
            15 => ExprKind::Index(Decode::decode(r)?, Decode::decode(r)?),
            16 => ExprKind::Slice(Decode::decode(r)?, Decode::decode(r)?, Decode::decode(r)?),
            17 => ExprKind::Field(Decode::decode(r)?, Decode::decode(r)?),
            18 => ExprKind::Deref(Decode::decode(r)?),
            19 => ExprKind::AddrOf(Decode::decode(r)?, Decode::decode(r)?),
            20 => ExprKind::Cast(Decode::decode(r)?, Decode::decode(r)?, Decode::decode(r)?),
            21 => ExprKind::FnType(Decode::decode(r)?),
            22 => ExprKind::Pipe(Decode::decode(r)?, Decode::decode(r)?),
            23 => ExprKind::Placeholder,
            24 => ExprKind::Dot(Decode::decode(r)?),
            25 => ExprKind::Assign {
                target: Decode::decode(r)?,
                op: Decode::decode(r)?,
                value: Decode::decode(r)?,
            },
            26 => ExprKind::Return(Decode::decode(r)?),
            27 => ExprKind::Break,
            28 => ExprKind::Continue,
            29 => ExprKind::Todo,
            tag => return Err(bad("expression", tag)),
        })
    }
}

impl Encode for Arg {
    fn encode(&self, w: &mut Writer) {
        self.label.encode(w);
        self.value.encode(w);
    }
}

impl Decode for Arg {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(Arg {
            label: Decode::decode(r)?,
            value: Decode::decode(r)?,
        })
    }
}

impl Encode for UnaryOp {
    fn encode(&self, w: &mut Writer) {
        match self {
            UnaryOp::Neg => w.tag(0),
            UnaryOp::BitNot => w.tag(1),
            UnaryOp::Not => w.tag(2),
        }
    }
}

impl Decode for UnaryOp {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => UnaryOp::Neg,
            1 => UnaryOp::BitNot,
            2 => UnaryOp::Not,
            tag => return Err(bad("unary operator", tag)),
        })
    }
}

impl Encode for BinOp {
    fn encode(&self, w: &mut Writer) {
        w.tag(match self {
            BinOp::Or => 0,
            BinOp::And => 1,
            BinOp::Eq => 2,
            BinOp::NotEq => 3,
            BinOp::Lt => 4,
            BinOp::Le => 5,
            BinOp::Gt => 6,
            BinOp::Ge => 7,
            BinOp::BitOr => 8,
            BinOp::BitXor => 9,
            BinOp::BitAnd => 10,
            BinOp::Shl => 11,
            BinOp::Shr => 12,
            BinOp::Add => 13,
            BinOp::Sub => 14,
            BinOp::Mul => 15,
            BinOp::Div => 16,
            BinOp::Rem => 17,
        });
    }
}

impl Decode for BinOp {
    fn decode(r: &mut Reader) -> Result<Self, DecodeError> {
        Ok(match r.tag()? {
            0 => BinOp::Or,
            1 => BinOp::And,
            2 => BinOp::Eq,
            3 => BinOp::NotEq,
            4 => BinOp::Lt,
            5 => BinOp::Le,
            6 => BinOp::Gt,
            7 => BinOp::Ge,
            8 => BinOp::BitOr,
            9 => BinOp::BitXor,
            10 => BinOp::BitAnd,
            11 => BinOp::Shl,
            12 => BinOp::Shr,
            13 => BinOp::Add,
            14 => BinOp::Sub,
            15 => BinOp::Mul,
            16 => BinOp::Div,
            17 => BinOp::Rem,
            tag => return Err(bad("binary operator", tag)),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::FileId;
    use crate::lex::tokenize;
    use crate::parse::parse_partial;

    fn parse(src: &str) -> Module {
        let tokens = tokenize(FileId::minted(0), src).unwrap();
        let (module, errors) = parse_partial(&tokens);
        assert_eq!(errors, vec![], "{src}");
        module
    }

    fn bytes<T: Encode>(value: &T) -> Vec<u8> {
        let mut w = Writer::default();
        value.encode(&mut w);
        w.bytes
    }

    fn roundtrip(src: &str) {
        let module = parse(src);
        let bytes = bytes(&module);
        let mut r = Reader::new(&bytes);
        let decoded = Module::decode(&mut r).unwrap();
        assert!(r.done());
        assert_eq!(decoded, module);
    }

    #[test]
    fn functions_and_externs_roundtrip() {
        roundtrip(
            "use geo.{Point, len as length}\n\
             pub use a.b.c as d\n\
             extern \"host\":\n\
             \tpub fn log(n: i32) = \"print\"\n\
             \tfn now() -> i64\n\
             extern:\n\
             \tfn exit()\n\
             fn(T, U: Bound, V: (A, B), W = i32) generic(x: T, y: U = 1, f: fn(T) -> U) -> V:\n\
             \treturn todo\n\
             fn alloc(T: type, n: uint = 1) -> &var T:\n\
             \treturn 0 as! &var T\n\
             pub \"wasi:cli/run\":\n\
             \tfn run() = \"run\":\n\
             \t\tpass\n\
             pub let LIMIT: i32 = 100\n\
             var count = 0\n\
             let Step: type = fn(i32) -> i32\n\
             let path: todo = todo\n",
        );
    }

    #[test]
    fn declarations_roundtrip() {
        roundtrip(
            "pub struct(T, U = u8) Vec:\n\
             \tuse varray(T)\n\
             \tuse geo.Box(&T)\n\
             \tpub use Meta as meta\n\
             \tuse Tag as tag\n\
             \tpub cap: uint = 0\n\
             \tname: Name(A, T: B)\n\
             \tempty: Name()\n\
             \tkind: module.Kind\n\
             union(A, B) Either:\n\
             \tuse option(i32)\n\
             \tleft: A\n\
             \tright: tuple(f32, f32)\n\
             \tnone\n\
             enum(u8) Color:\n\
             \tuse Warm\n\
             \tred\n\
             \tgreen = 5\n\
             \tblue\n",
        );
    }

    #[test]
    fn statements_roundtrip() {
        roundtrip(
            "fn demo(a: array(i32), v: varray(i32), pairs: array(tuple(i32, i32))) -> i32:\n\
             \tlet (q, _) = (1, 2)\n\
             \tvar (x, (y, z)): tuple(i32, tuple(bool, f32))\n\
             \tlet s: i32\n\
             \tif q > 10 and not x == y:\n\
             \t\tpass\n\
             \telse if q < 0:\n\
             \t\treturn -1\n\
             \telse:\n\
             \t\ts = 1\n\
             \twhile true:\n\
             \t\tbreak\n\
             \tfor e in a:\n\
             \t\tcontinue\n\
             \tfor i, (low, high) in pairs:\n\
             \t\tpass\n\
             \tfor &e in a:\n\
             \t\tpass\n\
             \tfor i, &var e in v:\n\
             \t\te.* *= 2\n\
             \tfor n in 1..a.len:\n\
             \t\tpass\n\
             \tmatch (a, true):\n\
             \t\t(\"zero\", _):\n\
             \t\t\tpass\n\
             \t\t([first, _], true):\n\
             \t\t\tpass\n\
             \t\t([], false):\n\
             \t\t\tpass\n\
             \t\telse:\n\
             \t\t\tpass\n\
             \tmatch q:\n\
             \t\t.circle(r):\n\
             \t\t\tpass\n\
             \t\t.rect((w, _)):\n\
             \t\t\tpass\n\
             \t\t.empty:\n\
             \t\t\tpass\n\
             \t\t-1:\n\
             \t\t\tpass\n\
             \t\t'c':\n\
             \t\t\tpass\n\
             \t\tother:\n\
             \t\t\tpass\n\
             \tdefer close(a)\n\
             \tdefer:\n\
             \t\tpass\n\
             \tfn inner(n: i32) -> i32:\n\
             \t\treturn n\n\
             \treturn 0\n",
        );
    }

    #[test]
    fn expressions_roundtrip() {
        roundtrip(
            "fn exprs(p: &var Point, a: array(u8)) -> i32:\n\
             \tlet ints = 1 + 18446744073709551615\n\
             \tlet floats = 1.5 * -2.25 / 0.0\n\
             \tlet s = \"hello\\n\"\n\
             \tlet c = '\u{1F986}'\n\
             \tlet flags = true or false\n\
             \tlet unit = ()\n\
             \tlet m = module.include(\"assets/logo.png\")\n\
             \tlet t = (1, 2, 3)\n\
             \tlet one = (1,)\n\
             \tlet l = [1, 2, 3]\n\
             \tlet e: array(i32) = []\n\
             \tlet rep = [0; 4]\n\
             \tlet u = -x + ~y - (not z) as i32\n\
             \tlet b = 1 | 2 ^ 3 & 4 << 5 >> 6 % 7\n\
             \tlet cmp = (1 == 2, 3 != 4, 5 < 6, 7 <= 8, 9 > 10, 11 >= 12)\n\
             \tlet called = f(0, c: 5, d: g())\n\
             \tlet idx = a[1]\n\
             \tlet slices = (a[1..a.len - 1], a[2..], a[..2], a[..])\n\
             \tlet field = p.x.y\n\
             \tlet tuple_field = t.0\n\
             \tlet deref = p.*\n\
             \tlet addr = (&p, &var count)\n\
             \tlet casts = (1 as f32, 16 as! &u8)\n\
             \tlet fn_ty = fn(i32, &T) -> i32\n\
             \tlet no_ret = fn(i32)\n\
             \tlet piped = 1 |> add(_, _) - 1 |> _ / 2\n\
             \tlet v: Shape = .empty\n\
             \tlet w: Shape = .circle(1.0)\n\
             \tp.x = 1\n\
             \tp.x += 1\n\
             \tp.x -= 1\n\
             \tp.x *= 1\n\
             \tp.x /= 1\n\
             \tp.x %= 1\n\
             \tlet sz = (Point.size, (&Point).align)\n\
             \tn >= 0 or return -1\n\
             \twhile true:\n\
             \t\tbreak\n\
             \twhile true:\n\
             \t\tcontinue\n\
             \tlet never: i32 = todo\n\
             \treturn\n",
        );
    }

    #[test]
    fn floats_are_bit_exact() {
        let module = parse("let x = 0.1\nlet y = -0.0\nlet z = 1.0e300\n");
        let bytes = bytes(&module);
        let decoded = Module::decode(&mut Reader::new(&bytes)).unwrap();
        for (a, b) in module.items.iter().zip(&decoded.items) {
            let (ItemKind::Binding(a), ItemKind::Binding(b)) = (&a.kind, &b.kind) else {
                panic!()
            };
            let (Some(a), Some(b)) = (&a.value, &b.value) else {
                panic!()
            };
            // `-0.0 == 0.0`, and `assert_eq!` would miss a sign, so the bits
            // are compared.
            assert_eq!(format!("{a:?}"), format!("{b:?}"));
        }
    }

    #[test]
    fn truncated_bytes_fail() {
        let module = parse("fn f(a: i32, b: i32 = 1) -> i32:\n\treturn a + b\n");
        let bytes = bytes(&module);
        for len in 0..bytes.len() {
            let mut r = Reader::new(&bytes[..len]);
            assert!(Module::decode(&mut r).is_err(), "{len} of {}", bytes.len());
        }
    }

    #[test]
    fn unknown_tags_fail() {
        let mut w = Writer::default();
        1usize.encode(&mut w);
        true.encode(&mut w);
        w.tag(200);
        let err = Module::decode(&mut Reader::new(&w.bytes)).unwrap_err();
        assert_eq!(err, bad("item", 200));
    }
}
