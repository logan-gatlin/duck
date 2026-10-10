//! Whether what a function is declared to take and give is what the WIT of
//! the world says it does.
//!
//! A type of Duck is one of WIT by its shape: a `record` is a struct with
//! as many fields, each the type of the field it is in order, a `variant` a
//! union so, and an `enum` an enum with as many members, counted from 0.
//! Names are of no account. A `list<T>` is an `array(T)` and a `string` an
//! `array(u8)`, `tuple`, `option` and `result` are Duck's own, `flags` are
//! the narrowest unsigned integer with a bit for each, a `char` is a `u32`,
//! and a handle of any kind is an `i32`.

use crate::ir::Const;
use crate::lex::Span;
use crate::load::Program;
use crate::parse::FnSig;
use crate::world::{ImportError, ROOT, WitFunc, WitTy, kebab};

use super::{Checker, FuncSig, OPTION, Prim, RESULT, Ty, TypeErrorKind, extern_fns};

/// The start of the name a handle of a resource is dropped by, before the
/// resource's.
const RESOURCE_DROP: &str = "[resource-drop]";

/// What starts the name of a function that a WIT declares, where a resource
/// has it. Any other name in brackets is a built-in of the component model,
/// which no WIT declares.
const DECLARED: [&str; 3] = ["[method]", "[static]", "[constructor]"];

/// Where a type of Duck isn't the type of WIT it is to be: the innermost
/// type of the two that differs.
struct Mismatch {
    /// The type of WIT there, as it is written.
    wit: String,
    /// What it is in Duck.
    expected: String,
    /// The type of Duck there.
    found: String,
}

impl Checker {
    /// Reports each `extern` function that isn't one the world imports, as
    /// the WIT declares it: one of an interface that isn't imported, one
    /// the interface doesn't have, one with no name there, and one that
    /// takes or gives what the WIT doesn't say.
    pub(super) fn check_imports(&mut self, program: &Program) {
        let mut unknown: Vec<Span> = Vec::new();
        for (index, (block, decl)) in extern_fns(program).enumerate() {
            let own = &decl.sig.name;
            let Some(field) = decl.import_name.clone().or_else(|| kebab(&own.name)) else {
                self.error(TypeErrorKind::NoWitName(own.name.clone()), own.span);
                continue;
            };
            let interface = block.module.as_ref().filter(|module| module.name != ROOT);
            let name = interface.map(|interface| interface.name.as_str());
            let found = match field.strip_prefix(RESOURCE_DROP) {
                Some(resource) => self.resource_drop(name, resource),
                // Only its interface says anything of a built-in.
                None if is_builtin(&field) => {
                    self.world
                        .import(name, "")
                        .map(|_| None)
                        .or_else(|e| match e {
                            ImportError::Function => Ok(None),
                            e => Err(e),
                        })
                }
                None => self.world.import(name, &field),
            };
            match (found, interface) {
                (Ok(None), _) => {}
                (Ok(Some(function)), _) => {
                    let sig = self.funcs[index].clone();
                    self.check_signature(&decl.sig, &sig, &function, true);
                }
                (Err(ImportError::Interface { imported }), Some(interface)) => {
                    // Each block is reported once, where it is named.
                    if !unknown.contains(&interface.span) {
                        unknown.push(interface.span);
                        let name = interface.name.clone();
                        let imported = nearest(&name, imported);
                        let kind = TypeErrorKind::UnknownImportInterface { name, imported };
                        self.error(kind, interface.span);
                    }
                }
                (Err(_), _) => {
                    let interface = name.map(str::to_string);
                    let kind = TypeErrorKind::UnknownImport {
                        interface,
                        name: field,
                    };
                    self.error(kind, own.span);
                }
            }
        }
    }

    /// The function that drops a handle of `resource` of `interface`: one
    /// that takes it.
    fn resource_drop(
        &self,
        interface: Option<&str>,
        resource: &str,
    ) -> Result<Option<WitFunc>, ImportError> {
        let Some(interface) = interface else {
            return Err(ImportError::Function);
        };
        // An interface that isn't imported is reported as that.
        self.world
            .import(Some(interface), "")
            .or_else(|e| match e {
                ImportError::Function => Ok(None),
                e => Err(e),
            })?;
        if !self.world.imports_resource(interface, resource) {
            return Err(ImportError::Function);
        }
        let handle = WitTy::Handle(format!("own<{resource}>"));
        Ok(Some(WitFunc {
            params: vec![("handle".to_string(), handle)],
            result: None,
        }))
    }

    /// Reports where `sig`, which `decl` declares, isn't `function` of the
    /// WIT. An `imported` one may take a `&var` to its result as a last
    /// parameter in place of giving it, as the Canonical ABI passes one
    /// that is more than a wasm value.
    pub(super) fn check_signature(
        &mut self,
        decl: &FnSig,
        sig: &FuncSig,
        function: &WitFunc,
        imported: bool,
    ) {
        let name = &decl.name;
        let mut params: Vec<_> = (decl.params.iter().zip(&sig.params))
            .map(|(param, (_, ty))| (param.ty.span, *ty))
            .collect();
        let mut result = (decl.ret.as_ref().map(|ty| ty.span), sig.ret);
        let lowered = imported
            && function.result.is_some()
            && sig.ret == Ty::Unit
            && params.len() == function.params.len() + 1;
        if let (true, Some((span, Ty::Ptr(id)))) = (lowered, params.last().copied())
            && self.writes(Ty::Ptr(id))
        {
            params.pop();
            result = (Some(span), self.pointee(id));
        }
        if params.len() != function.params.len() {
            let kind = TypeErrorKind::WitParams {
                name: name.name.clone(),
                wit: function.params.len(),
                found: params.len(),
            };
            self.error(kind, name.span);
        }
        for ((span, ty), (_, wit)) in params.into_iter().zip(&function.params) {
            self.check_wit(ty, wit, span);
        }
        match (&function.result, result) {
            (None, (_, Ty::Unit | Ty::Never | Ty::Error)) => {}
            (None, (span, _)) => {
                let name = name.name.clone();
                let kind = TypeErrorKind::WitResult { name, wit: None };
                self.error(kind, span.unwrap_or(decl.name.span));
            }
            (Some(wit), (None, _) | (_, Ty::Unit)) => {
                let wit = Some(wit.to_string());
                let name = name.name.clone();
                self.error(TypeErrorKind::WitResult { name, wit }, decl.name.span);
            }
            (Some(wit), (Some(span), ty)) => self.check_wit(ty, wit, span),
        }
    }

    /// Reports `ty`, written at `span`, if it isn't `wit`.
    fn check_wit(&mut self, ty: Ty, wit: &WitTy, span: Span) {
        if let Some(mismatch) = self.mismatch(ty, wit) {
            let kind = TypeErrorKind::WitMismatch {
                wit: wit.to_string(),
                within: mismatch.wit,
                expected: mismatch.expected,
                found: mismatch.found,
            };
            self.error(kind, span);
        }
    }

    /// Where `ty` isn't `wit`, if it isn't.
    fn mismatch(&self, ty: Ty, wit: &WitTy) -> Option<Mismatch> {
        let differs = || {
            Some(Mismatch {
                wit: wit.to_string(),
                expected: expected(wit),
                found: self.ty_name(ty),
            })
        };
        let prim = |prim: Prim| match ty == Ty::Prim(prim) {
            true => None,
            false => differs(),
        };
        let all = |types: &mut dyn Iterator<Item = (Ty, &WitTy)>| {
            let mut found = None;
            for (ty, wit) in types {
                found = found.or_else(|| self.mismatch(ty, wit));
            }
            found
        };
        if ty == Ty::Error {
            return None;
        }
        match wit {
            WitTy::Bool => prim(Prim::Bool),
            WitTy::S8 => prim(Prim::I8),
            WitTy::U8 => prim(Prim::U8),
            WitTy::S16 => prim(Prim::I16),
            WitTy::U16 => prim(Prim::U16),
            WitTy::S32 | WitTy::Handle(_) => prim(Prim::I32),
            WitTy::U32 | WitTy::Char => prim(Prim::U32),
            WitTy::S64 => prim(Prim::I64),
            WitTy::U64 => prim(Prim::U64),
            WitTy::F32 => prim(Prim::F32),
            WitTy::F64 => prim(Prim::F64),
            WitTy::Flags { flags, .. } => prim(flags_prim(*flags)),
            WitTy::String => match ty {
                Ty::Array(id) if !self.writes(ty) && self.element(id) == Ty::Prim(Prim::U8) => None,
                _ => differs(),
            },
            WitTy::List(elem) => match ty {
                Ty::Array(id) if !self.writes(ty) => self.mismatch(self.element(id), elem),
                _ => differs(),
            },
            WitTy::Tuple(elems) => match ty {
                Ty::Tuple(id) if self.tuples[id.0 as usize].len() == elems.len() => {
                    all(&mut self.tuples[id.0 as usize].iter().copied().zip(elems))
                }
                _ => differs(),
            },
            WitTy::Record { fields, .. } => match self.declared(ty, false) {
                Some(found) if found.len() == fields.len() => {
                    all(&mut found.iter().map(|(ty, _)| *ty).zip(fields))
                }
                _ => differs(),
            },
            WitTy::Variant { cases, .. } => match self.declared(ty, true) {
                Some(found) if found.len() == cases.len() => {
                    let mut cases = found.iter().zip(cases);
                    cases.find_map(|((ty, bare), case)| match (case, bare) {
                        (None, true) => None,
                        (Some(case), false) => self.mismatch(*ty, case),
                        _ => differs(),
                    })
                }
                _ => differs(),
            },
            WitTy::Enum { cases, .. } => match ty {
                Ty::Enum(id) if self.counts(id, *cases) => None,
                _ => differs(),
            },
            WitTy::Option(inner) => match self.builtin(ty, OPTION).as_deref() {
                Some([held]) => self.mismatch(*held, inner),
                _ => differs(),
            },
            WitTy::Result(ok, err) => match self.builtin(ty, RESULT).as_deref() {
                Some([found_ok, found_err]) => {
                    let held = |found: Ty, wit: &Option<Box<WitTy>>| match (wit, found) {
                        (Some(wit), _) => self.mismatch(found, wit),
                        (None, Ty::Unit) => None,
                        (None, _) => Some(Mismatch {
                            wit: "_".to_string(),
                            expected: "`tuple()`".to_string(),
                            found: self.ty_name(found),
                        }),
                    };
                    held(*found_ok, ok).or_else(|| held(*found_err, err))
                }
                _ => differs(),
            },
            WitTy::Unsupported(_) => differs(),
        }
    }

    /// The type of each field of the struct `ty`, or of each variant if it
    /// is to be a `union`, with whether it is a variant that holds nothing.
    /// `None` if it isn't one that the source declares.
    fn declared(&self, ty: Ty, union: bool) -> Option<Vec<(Ty, bool)>> {
        let Ty::Struct(id) = ty else {
            return None;
        };
        let def = &self.structs[id.0 as usize];
        let generic = def
            .instance
            .as_ref()
            .map_or(id, |instance| instance.generic);
        let builtin = self.builtin_unions.contains(&generic) || self.list == Some(generic);
        let fields = def.fields.iter().map(|field| (field.ty, field.bare));
        (def.union == union && !builtin).then(|| fields.collect())
    }

    /// The type arguments of `ty`, if it is the built-in union `name`.
    fn builtin(&self, ty: Ty, name: &str) -> Option<Vec<Ty>> {
        let Ty::Struct(id) = ty else {
            return None;
        };
        let instance = self.structs[id.0 as usize].instance.as_ref()?;
        (Some(instance.generic) == self.builtin_union(name)).then(|| instance.args.clone())
    }

    /// Whether enum `id` is an `enum` of WIT with `cases` cases: its values
    /// are of the narrowest unsigned integer that counts them, and its
    /// members count from 0.
    fn counts(&self, id: super::EnumId, cases: usize) -> bool {
        let def = &self.enums[id.0 as usize];
        let mut counted = def.members.iter().enumerate();
        def.ty == Ty::Prim(enum_prim(cases))
            && def.members.len() == cases
            && counted.all(|(index, member)| member.value == [Const::I32(index as i32)])
    }
}

/// Those of `interfaces` that are of the package `name` names, which are
/// what it is most likely meant to be, or all of them if none is.
fn nearest(name: &str, interfaces: Vec<String>) -> Vec<String> {
    let package = |name: &str| name.split('/').next().map(str::to_string);
    let wanted = package(name);
    let of_package = |interface: &&String| package(interface) == wanted;
    let near: Vec<_> = interfaces.iter().filter(of_package).cloned().collect();
    match near.is_empty() {
        true => interfaces,
        false => near,
    }
}

/// Whether a function the host knows as `name` is a built-in of the
/// component model, which no WIT declares.
fn is_builtin(name: &str) -> bool {
    name.starts_with('[') && !DECLARED.iter().any(|declared| name.starts_with(declared))
}

/// The integer that `flags` flags are: the narrowest with a bit for each.
fn flags_prim(flags: usize) -> Prim {
    match flags {
        0..=8 => Prim::U8,
        9..=16 => Prim::U16,
        _ => Prim::U32,
    }
}

/// The integer that the value of an `enum` of `cases` cases is: the
/// narrowest that counts them.
fn enum_prim(cases: usize) -> Prim {
    match cases {
        0..=256 => Prim::U8,
        257..=65536 => Prim::U16,
        _ => Prim::U32,
    }
}

/// What `wit` is in Duck, as an error says it.
fn expected(wit: &WitTy) -> String {
    let prim = |prim: Prim| format!("`{}`", prim.name());
    match wit {
        WitTy::Bool => prim(Prim::Bool),
        WitTy::S8 => prim(Prim::I8),
        WitTy::U8 => prim(Prim::U8),
        WitTy::S16 => prim(Prim::I16),
        WitTy::U16 => prim(Prim::U16),
        WitTy::S32 => prim(Prim::I32),
        WitTy::U32 | WitTy::Char => prim(Prim::U32),
        WitTy::S64 => prim(Prim::I64),
        WitTy::U64 => prim(Prim::U64),
        WitTy::F32 => prim(Prim::F32),
        WitTy::F64 => prim(Prim::F64),
        WitTy::Handle(_) => "an `i32`, as a handle is".to_string(),
        WitTy::Flags { flags, .. } => {
            let bits = flags_prim(*flags).name();
            format!("a `{bits}`, with a bit for each of its {flags} flags")
        }
        WitTy::String => "an `array(u8)`".to_string(),
        WitTy::List(_) => "an `array` of its elements".to_string(),
        WitTy::Tuple(elems) => format!("a `tuple` of {}", elems.len()),
        WitTy::Record { fields, .. } => format!("a struct of {} fields", fields.len()),
        WitTy::Variant { cases, .. } => format!("a union of {} variants", cases.len()),
        WitTy::Enum { cases, .. } => {
            let value = enum_prim(*cases).name();
            format!("an `enum({value})` of {cases} members, counted from 0")
        }
        WitTy::Option(_) => "an `option`".to_string(),
        WitTy::Result(..) => "a `result`".to_string(),
        WitTy::Unsupported(_) => "a type that Duck has none for yet".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use crate::file::{DummyManager, FileManager, Settings, Wit, WitFile};
    use crate::lex::tokenize;
    use crate::load::Program;
    use crate::parse;
    use crate::ty::{TypeError, check};

    const WIT: &str = "
package my:pkg@0.1.0;

interface host {
    record point { x: f32, y: f32 }
    record sized { at: point, size: u64, name: string }
    variant shape { circle(f32), rect(tuple<f32, f32>), empty }
    enum color { red, green, blue }
    flags access { read, write, exec }
    resource file {
        read: func(len: u32) -> result<list<u8>, color>;
        open: static func(path: string) -> option<file>;
    }

    area: func(s: shape) -> f32;
    paint: func(at: point, tint: color, may: access) -> bool;
    measure: func(what: sized) -> result<_, string>;
    letter: func(c: char) -> list<tuple<u32, string>>;
    wait: func();
    pipe: func(data: stream<u8>) -> future<bool>;
}

interface unused {
    idle: func();
}

world app {
    import host;
    import trace: func(code: u32);
    export sum: func(a: s32, b: s32) -> s32;
    export host;
}
";

    /// Each error of `src` as a component of `world`, one of [`WIT`] or
    /// none for a library, as it is shown, with what it is reported at.
    fn errors_in<'a>(src: &'a str, world: Option<&str>) -> Vec<(String, &'a str)> {
        let settings = Settings {
            world: world.map(str::to_string),
            wit: Wit {
                package: vec![WitFile {
                    path: "app.wit".to_string(),
                    contents: WIT.to_string(),
                }],
                deps: Vec::new(),
            },
            ..Settings::default()
        };
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let errors = check(&program, &settings).err().unwrap_or_default();
        let at = |e: &TypeError| e.span.map_or("", |span| &src[span.start..span.end]);
        errors.iter().map(|e| (e.kind.to_string(), at(e))).collect()
    }

    /// The types of [`WIT`] as Duck declares them.
    const TYPES: &str = "
struct Point:
    x: f32
    y: f32

struct Sized:
    at: Point
    size: u64
    name: string

union Shape:
    circle: f32
    rect: tuple(f32, f32)
    empty

enum(u8) Color:
    red
    green
    blue
";

    #[test]
    fn a_function_is_declared_as_the_wit_declares_it() {
        let src = format!(
            "{TYPES}
extern \"my:pkg/host@0.1.0\":
    fn area(s: Shape) -> f32
    fn paint(at: Point, with: Color, may: u8) -> bool
    fn measure(what: Sized, ret: &var result(tuple(), array(u8)))
    fn letter(c: u32, ret: &var array(tuple(u32, array(u8))))
    fn wait() -> never
    fn pipe(data: i32) -> i32
    fn read(self: i32, len: u32, ret: &var result(array(u8), Color)) = \"[method]file.read\"
    fn open(path: string, ret: &var option(i32)) = \"[static]file.open\"
    fn close(file: i32) = \"[resource-drop]file\"
    fn stream_new() -> i64 = \"[stream-new-0]pipe\"
    fn anything(a: f64) -> f64 = \"[async-lower]wait\"

extern:
    fn trace(code: u32)

extern \"$root\":
    fn set_new() -> i32 = \"[waitable-set-new]\"

pub fn sum(a: i32, b: i32) -> i32:
    return a + b
"
        );
        // Only what the world exports is left to define.
        let errors = errors_in(&src, Some("app"));
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(errors[0].0.starts_with("nothing defines "), "{errors:#?}");
    }

    #[test]
    fn a_type_is_the_one_of_the_wit_by_its_shape() {
        let src = "
struct Point:
    x: f32
    y: f64

struct Sized:
    at: Point
    size: u64
    name: string

union Shape:
    circle: f32
    rect: tuple(f32, f32)
    empty: bool

enum(u8) Color:
    red
    green = 5
    blue

enum(u16) Wide:
    red
    green
    blue

extern \"my:pkg/host@0.1.0\":
    fn area(s: Shape) -> f64
    fn paint(at: tuple(f32, f32), with: Color, may: u16) -> i32
    fn measure(what: Sized, ret: &var result(i32, varray(u8)))
    fn letter(c: i32, ret: &var array(tuple(u32, u32)))
    fn pipe(data: i64) -> i32
    fn read(self: i32, len: u32, ret: &var option(array(u8))) = \"[method]file.read\"
    fn open(path: string, ret: &var option(Wide)) = \"[static]file.open\"
";
        let shown: Vec<_> = errors_in(src, None);
        let shown: Vec<_> = shown.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown,
            [
                (
                    "the WIT has `shape` here, which is a union of 3 variants: found `Shape`",
                    "Shape"
                ),
                ("the WIT has `f32` here, which is `f32`: found `f64`", "f64"),
                (
                    "the WIT has `point` here, which is a struct of 2 fields: found \
                     `tuple(f32, f32)`",
                    "tuple(f32, f32)"
                ),
                (
                    "the WIT has `color` here, which is an `enum(u8)` of 3 members, counted \
                     from 0: found `Color`",
                    "Color"
                ),
                (
                    "the WIT has `access` here, which is a `u8`, with a bit for each of its 3 \
                     flags: found `u16`",
                    "u16"
                ),
                (
                    "the WIT has `bool` here, which is `bool`: found `i32`",
                    "i32"
                ),
                (
                    "the WIT has `sized` here, whose `f32` is `f32`: found `f64`",
                    "Sized"
                ),
                (
                    "the WIT has `result<_, string>` here, whose `_` is `tuple()`: found `i32`",
                    "&var result(i32, varray(u8))"
                ),
                (
                    "the WIT has `char` here, which is `u32`: found `i32`",
                    "i32"
                ),
                (
                    "the WIT has `list<tuple<u32, string>>` here, whose `string` is an \
                     `array(u8)`: found `u32`",
                    "&var array(tuple(u32, u32))"
                ),
                (
                    "the WIT has `stream<u8>` here, which is an `i32`, as a handle is: found \
                     `i64`",
                    "i64"
                ),
                (
                    "the WIT has `result<list<u8>, color>` here, which is a `result`: found \
                     `option(array(u8))`",
                    "&var option(array(u8))"
                ),
                (
                    "the WIT has `option<own<file>>` here, whose `own<file>` is an `i32`, as a \
                     handle is: found `Wide`",
                    "&var option(Wide)"
                ),
            ]
        );
    }

    #[test]
    fn a_function_takes_and_gives_as_much_as_the_wit_says() {
        let src = "
extern \"my:pkg/host@0.1.0\":
    fn wait(n: i32)
    fn idle() = \"wait\"
    fn area() -> f32
    fn paint(a: f32, b: f32, c: f32, d: f32)
    fn letter(c: u32)
    fn pipe(data: i32)
    fn spin() -> i32 = \"wait\"
    fn close(file: i64) = \"[resource-drop]file\"
";
        let shown: Vec<_> = errors_in(src, None);
        let shown: Vec<_> = shown.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown,
            [
                ("`wait` takes 0 parameters in the WIT, and 1 here", "wait"),
                ("`area` takes 1 parameter in the WIT, and 0 here", "area"),
                ("`paint` takes 3 parameters in the WIT, and 4 here", "paint"),
                (
                    "the WIT has `point` here, which is a struct of 2 fields: found `f32`",
                    "f32"
                ),
                (
                    "the WIT has `color` here, which is an `enum(u8)` of 3 members, counted \
                     from 0: found `f32`",
                    "f32"
                ),
                (
                    "the WIT has `access` here, which is a `u8`, with a bit for each of its 3 \
                     flags: found `f32`",
                    "f32"
                ),
                (
                    "`paint` gives a `bool` in the WIT, and nothing here",
                    "paint"
                ),
                (
                    "`letter` gives a `list<tuple<u32, string>>` in the WIT, and nothing here",
                    "letter"
                ),
                (
                    "`pipe` gives a `future<bool>` in the WIT, and nothing here",
                    "pipe"
                ),
                ("`spin` gives nothing in the WIT", "i32"),
                (
                    "the WIT has `own<file>` here, which is an `i32`, as a handle is: found \
                     `i64`",
                    "i64"
                ),
            ]
        );
    }

    #[test]
    fn only_what_is_there_is_imported() {
        let src = "
extern \"my:pkg/unused@0.1.0\":
    fn idle()
    fn other()

extern \"my:pkg/host\":
    fn wait()

extern \"my:pkg/host@0.1.0\":
    fn missing()
    fn close(file: i32) = \"[resource-drop]pipe\"
    fn method() = \"[method]file.write\"

extern:
    fn trace(code: u32)
    fn log(code: u32)

extern \"nope:pkg/x\":
    fn stream_new() -> i64 = \"[stream-new-0]pipe\"

pub fn sum(a: i32, b: i32) -> i32:
    return a + b

pub \"my:pkg/host@0.1.0\":
    pass
";
        let errors = errors_in(src, Some("app"));
        let shown: Vec<_> = errors.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown[..7],
            [
                (
                    "no interface `my:pkg/unused@0.1.0` is there to import: there is \
                     `my:pkg/host@0.1.0`",
                    "\"my:pkg/unused@0.1.0\""
                ),
                (
                    "no interface `my:pkg/host` is there to import: there is `my:pkg/host@0.1.0`",
                    "\"my:pkg/host\""
                ),
                ("`my:pkg/host@0.1.0` has no function `missing`", "missing"),
                (
                    "`my:pkg/host@0.1.0` has no function `[resource-drop]pipe`",
                    "close"
                ),
                (
                    "`my:pkg/host@0.1.0` has no function `[method]file.write`",
                    "method"
                ),
                ("the world imports no function `log`", "log"),
                (
                    "no interface `nope:pkg/x` is there to import: there is `my:pkg/host@0.1.0`",
                    "\"nope:pkg/x\""
                ),
            ]
        );

        // A library imports what any interface of its WIT has, and nothing
        // says what its world would give it.
        let library = "
extern \"my:pkg/unused@0.1.0\":
    fn idle()

extern \"wasi:cli/exit@0.3.0\":
    fn exit_with_code(status: u8)

extern:
    fn anything(a: f64) -> f64

extern \"js\":
    fn now() -> f64
";
        let errors = errors_in(library, None);
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(
            errors[0]
                .0
                .starts_with("no interface `js` is there to import: there is `wasi:")
        );
        assert_eq!(errors[0].1, "\"js\"");
    }

    #[test]
    fn what_is_exported_is_declared_as_the_wit_declares_it() {
        let src = "
pub fn sum(a: i64, b: i32):
    pass

pub \"my:pkg/host@0.1.0\":
    fn wait() -> i32:
        return 1
    fn area(s: f32) -> f32:
        return s
";
        let errors = errors_in(src, Some("app"));
        let shown: Vec<_> = errors.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown[..4],
            [
                ("the WIT has `s32` here, which is `i32`: found `i64`", "i64"),
                ("`sum` gives a `s32` in the WIT, and nothing here", "sum"),
                (
                    "the WIT has `shape` here, which is a union of 3 variants: found `f32`",
                    "f32"
                ),
                ("`wait` gives nothing in the WIT", "i32"),
            ]
        );
    }
}
