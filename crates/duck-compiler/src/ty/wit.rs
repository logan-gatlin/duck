//! Whether what a function is declared to take and give is what the WIT of
//! the world says it does.
//!
//! A type of Duck is one of WIT by its shape: a `record` is a struct with
//! as many fields, each the type of the field it is in order, a `variant` a
//! union so, and an `enum` an enum with as many members, counted from 0.
//! Names are of no account. A `list<T>` is an `array(T)`, a `string` an
//! `array(u8)` and a `map<K, V>` an `array(tuple(K, V))`, as the Canonical
//! ABI passes one. `tuple`, `option` and `result` are Duck's own, `flags` are
//! the narrowest unsigned integer with a bit for each, a `char` is a `u32`,
//! and a handle of any kind is an `i32`.
//!
//! A struct with one field is also what its field is, as it is laid out and
//! passed as that: one that holds an `i32` is a handle, which no other
//! struct that holds one is taken for by the source. So is a tuple of one
//! element, and what a `tuple` of one of the WIT holds is that tuple.

use crate::ir::{Const, FuncId};
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
            let sig = self.funcs[index].clone();
            let needs = self.import_passing(FuncId(index as u32)).size;
            self.check_fits(needs, own.span);
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
                    self.check_signature(&decl.sig, &sig, &function, true);
                }
                (
                    Err(error @ (ImportError::Interface { .. } | ImportError::Unimported { .. })),
                    Some(interface),
                ) => {
                    // Each block is reported once, where it is named.
                    if !unknown.contains(&interface.span) {
                        unknown.push(interface.span);
                        let name = interface.name.clone();
                        let kind = match error {
                            ImportError::Unimported { world } => {
                                TypeErrorKind::UnimportedInterface { name, world }
                            }
                            ImportError::Interface { imported } => {
                                let imported = nearest(&name, imported);
                                TypeErrorKind::UnknownImportInterface { name, imported }
                            }
                            ImportError::Function => unreachable!("it is of an interface"),
                        };
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

    /// Reports a function declared at `span` that passes `needs` bytes in
    /// memory, if that is more than the return area holds.
    pub(super) fn check_fits(&mut self, needs: u32, span: Span) {
        let has = self.return_area_size;
        if needs > has {
            self.error(TypeErrorKind::ReturnArea { needs, has }, span);
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
    /// WIT. Notes what the host of one that is `imported`, or of one that
    /// is exported, passes in memory that it has the component allocate.
    pub(super) fn check_signature(
        &mut self,
        decl: &FnSig,
        sig: &FuncSig,
        function: &WitFunc,
        imported: bool,
    ) {
        let name = &decl.name;
        let params: Vec<_> = (decl.params.iter().zip(&sig.params))
            .map(|(param, (_, ty))| (param.ty.span, *ty))
            .collect();
        let result = (decl.ret.as_ref().map(|ty| ty.span), sig.ret);
        let passing = self.passing(sig, imported);
        // The host allocates what it passes: a list an import returns, or
        // one an export takes, and parameters of an export that are too
        // many for wasm values.
        let given = match imported {
            true => function.result.iter().zip(result.0).collect::<Vec<_>>(),
            false => (function.params.iter().map(|(_, wit)| wit))
                .zip(params.iter().map(|(span, _)| *span))
                .collect(),
        };
        let allocated = given.into_iter().find(|(wit, _)| allocates(wit));
        let spilled = (!imported && passing.params.is_some()).then(|| {
            let wit: Vec<_> = function
                .params
                .iter()
                .map(|(_, wit)| wit.to_string())
                .collect();
            (name.span, format!("tuple<{}>", wit.join(", ")))
        });
        let allocated = allocated
            .map(|(wit, span)| (span, wit.to_string()))
            .or(spilled);
        if self.allocated.is_none() {
            self.allocated = allocated;
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

    /// Where `ty` isn't `wit`, if it isn't. What holds one thing and
    /// nothing else is laid out and passed as that thing is, so it is that
    /// too: a struct with one field, and a tuple of one element, of Duck
    /// or of the WIT.
    fn mismatch(&self, ty: Ty, wit: &WitTy) -> Option<Mismatch> {
        let own = self.mismatch_as_declared(ty, wit)?;
        if let WitTy::Tuple(elems) = wit
            && let [held] = &elems[..]
            && self.mismatch(ty, held).is_none()
        {
            return None;
        }
        let fields = self.declared(ty, false);
        let held = match (ty, fields.as_deref()) {
            (_, Some([(field, _)])) => *field,
            (Ty::Tuple(id), _) => match self.tuples[id.0 as usize][..] {
                [elem] => elem,
                _ => return Some(own),
            },
            _ => return Some(own),
        };
        let held = self.mismatch(held, wit)?;
        // A `record` is a struct and a `tuple` a tuple, so `ty` itself is
        // what isn't one.
        Some(match wit {
            WitTy::Record { .. } | WitTy::Tuple(_) => own,
            _ => held,
        })
    }

    /// Where `ty` itself isn't `wit`, if it isn't.
    fn mismatch_as_declared(&self, ty: Ty, wit: &WitTy) -> Option<Mismatch> {
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
            WitTy::Map(key, value) => match ty {
                Ty::Array(id) if !self.writes(ty) => match self.element(id) {
                    Ty::Tuple(entry) => match self.tuples[entry.0 as usize][..] {
                        [found_key, found_value] => (self.mismatch(found_key, key))
                            .or_else(|| self.mismatch(found_value, value)),
                        _ => differs(),
                    },
                    _ => differs(),
                },
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

/// Whether a value of `wit` holds what is allocated: a list or a string.
fn allocates(wit: &WitTy) -> bool {
    match wit {
        WitTy::String | WitTy::List(_) | WitTy::Map(..) => true,
        WitTy::Tuple(elems) => elems.iter().any(allocates),
        WitTy::Record { fields, .. } => fields.iter().any(allocates),
        WitTy::Variant { cases, .. } => cases.iter().flatten().any(allocates),
        WitTy::Option(inner) => allocates(inner),
        WitTy::Result(ok, err) => [ok, err].into_iter().flatten().any(|ty| allocates(ty)),
        _ => false,
    }
}

/// Whether a function the host knows as `name` is a built-in of the
/// component model, which no WIT declares.
pub(super) fn is_builtin(name: &str) -> bool {
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
        WitTy::Map(..) => "an `array` of a `tuple` of each key and its value".to_string(),
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
    use crate::ir::Stmt;
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
    count: func(words: map<string, u32>) -> map<u32, point>;
    single: func(one: tuple<u32>, pair: list<tuple<point>>) -> tuple<tuple<f32>>;
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

world hosted {
    import host;
    import trace: func(code: u32);
}

world counted {
    export count: func(text: string) -> u32;
}
";

    /// Checks `src` as a component of `world`, one of [`WIT`] or none for
    /// a library.
    fn check_in(src: &str, world: Option<&str>) -> Result<crate::ir::Module, Vec<TypeError>> {
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
        check(&program, &settings)
    }

    /// Each error of `src` as a component of `world`, as [`check_in`]
    /// checks it, as it is shown, with what it is reported at.
    fn errors_in<'a>(src: &'a str, world: Option<&str>) -> Vec<(String, &'a str)> {
        let errors = check_in(src, world).err().unwrap_or_default();
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
    fn measure(what: Sized) -> result(tuple(), string)
    fn letter(c: u32) -> array(tuple(u32, array(u8)))
    fn wait() -> never
    fn pipe(data: i32) -> i32
    fn read(self: i32, len: u32) -> result(array(u8), Color) = \"[method]file.read\"
    fn open(path: string) -> option(i32) = \"[static]file.open\"
    fn close(file: i32) = \"[resource-drop]file\"
    fn stream_new() -> i64 = \"[stream-new-0]pipe\"
    fn anything(a: f64) -> f64 = \"[async-lower]wait\"

extern:
    fn trace(code: u32)

extern \"$root\":
    fn set_new() -> i32 = \"[waitable-set-new]\"

pub fn sum(a: i32, b: i32) -> i32:
    return a + b

pub fn cabi_realloc(old: &u8, old_size: uint, align: uint, new_size: uint) -> &var u8:
    return 0
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
    fn measure(what: Sized) -> result(i32, varray(u8))
    fn letter(c: i32) -> array(tuple(u32, u32))
    fn pipe(data: i64) -> i32
    fn read(self: i32, len: u32) -> option(array(u8)) = \"[method]file.read\"
    fn open(path: string) -> option(Wide) = \"[static]file.open\"
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
                    "result(i32, varray(u8))"
                ),
                (
                    "the WIT has `char` here, which is `u32`: found `i32`",
                    "i32"
                ),
                (
                    "the WIT has `list<tuple<u32, string>>` here, whose `string` is an \
                     `array(u8)`: found `u32`",
                    "array(tuple(u32, u32))"
                ),
                (
                    "the WIT has `stream<u8>` here, which is an `i32`, as a handle is: found \
                     `i64`",
                    "i64"
                ),
                (
                    "the WIT has `result<list<u8>, color>` here, which is a `result`: found \
                     `option(array(u8))`",
                    "option(array(u8))"
                ),
                (
                    "the WIT has `option<own<file>>` here, whose `own<file>` is an `i32`, as a \
                     handle is: found `Wide`",
                    "option(Wide)"
                ),
            ]
        );
    }

    #[test]
    fn a_struct_of_one_field_is_what_its_field_is() {
        let types = "
struct File:
    handle: i32

struct Stream:
    of: File

struct Meters:
    value: f32

struct Path:
    text: string

struct Held:
    shape: Shape

struct Wrong:
    handle: i64

struct Two:
    a: i32
    b: i32
";
        let src = format!(
            "{TYPES}{types}
extern \"my:pkg/host@0.1.0\":
    fn read(self: File, len: u32) -> result(array(u8), Color) = \"[method]file.read\"
    fn open(path: Path) -> option(File) = \"[static]file.open\"
    fn close(file: File) = \"[resource-drop]file\"
    fn pipe(data: Stream) -> File
    fn area(s: Held) -> Meters
"
        );
        assert_eq!(errors_in(&src, None), []);
        // It is passed as its field is.
        let module = check_in(&src, None).unwrap();
        let pipe = module
            .imports
            .iter()
            .find(|import| import.name == "pipe")
            .unwrap();
        assert_eq!((pipe.params.len(), pipe.results.len()), (1, 1));

        let src = format!(
            "{TYPES}{types}
extern \"my:pkg/host@0.1.0\":
    fn pipe(data: Wrong) -> Two
    fn wait() -> Meters
"
        );
        let errors = errors_in(&src, None);
        let shown: Vec<_> = errors.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown,
            [
                (
                    "the WIT has `stream<u8>` here, which is an `i32`, as a handle is: found \
                     `i64`",
                    "Wrong"
                ),
                (
                    "the WIT has `future<bool>` here, which is an `i32`, as a handle is: found \
                     `Two`",
                    "Two"
                ),
                ("`wait` gives nothing in the WIT", "Meters"),
            ]
        );
    }

    #[test]
    fn a_tuple_of_one_is_what_it_holds() {
        // As the WIT has it, and with either in place of the other: the
        // two are laid out and passed alike.
        for (one, pair, gives) in [
            ("tuple(u32)", "array(tuple(Point))", "tuple(tuple(f32))"),
            ("u32", "array(Point)", "f32"),
            ("u32", "array(tuple(Point))", "tuple(f32)"),
            (
                "tuple(tuple(u32))",
                "array(Point)",
                "tuple(tuple(tuple(f32)))",
            ),
        ] {
            let src = format!(
                "{TYPES}
extern \"my:pkg/host@0.1.0\":
    fn single(one: {one}, pair: {pair}) -> {gives}
    fn area(s: tuple(Shape)) -> tuple(f32)
"
            );
            assert_eq!(errors_in(&src, None), [], "{one} {pair} {gives}");
        }
        let src = format!(
            "{TYPES}
extern \"my:pkg/host@0.1.0\":
    fn single(one: tuple(i32), pair: array(tuple(Point, Point))) -> tuple(f32, f32)
"
        );
        let errors = errors_in(&src, None);
        let shown: Vec<_> = errors.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown,
            [
                (
                    "the WIT has `tuple<u32>` here, whose `u32` is `u32`: found `i32`",
                    "tuple(i32)"
                ),
                (
                    "the WIT has `list<tuple<point>>` here, whose `tuple<point>` is a `tuple` \
                     of 1: found `tuple(Point, Point)`",
                    "array(tuple(Point, Point))"
                ),
                (
                    "the WIT has `tuple<tuple<f32>>` here, which is a `tuple` of 1: found \
                     `tuple(f32, f32)`",
                    "tuple(f32, f32)"
                ),
            ]
        );
    }

    #[test]
    fn a_map_is_an_array_of_each_key_with_its_value() {
        let src = format!(
            "{TYPES}
struct Words:
    of: array(tuple(string, u32))

extern \"my:pkg/host@0.1.0\":
    fn count(words: Words) -> array(tuple(u32, Point))
"
        );
        assert_eq!(errors_in(&src, None), []);
        // The host allocates one that it gives, as it does a list.
        let hosted = format!("{src}\nextern:\n    fn trace(code: u32)\n");
        let errors = errors_in(&hosted, Some("hosted"));
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(
            errors[0]
                .0
                .starts_with("the host passes a `map<u32, point>` in memory")
        );

        let src = format!(
            "{TYPES}
extern \"my:pkg/host@0.1.0\":
    fn count(words: array(tuple(string, i32))) -> array(u32)
"
        );
        let errors = errors_in(&src, None);
        let shown: Vec<_> = errors.iter().map(|(e, at)| (e.as_str(), *at)).collect();
        assert_eq!(
            shown,
            [
                (
                    "the WIT has `map<string, u32>` here, whose `u32` is `u32`: found `i32`",
                    "array(tuple(string, i32))"
                ),
                (
                    "the WIT has `map<u32, point>` here, which is an `array` of a `tuple` of each \
                     key and its value: found `array(u32)`",
                    "array(u32)"
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
    fn what_is_passed_in_memory_goes_through_the_return_area() {
        let src = "
struct Wide:
    a: tuple(u64, u64, u64, u64, u64, u64, u64, u64)
    b: tuple(u64, u64, u64, u64, u64, u64, u64, u64)
    c: u64

extern:
    fn one(n: i32) -> i32
    fn pair(n: i32) -> tuple(i32, i64)
    fn many(wide: Wide, last: u8) -> i64
    fn both(wide: Wide) -> Wide

let text = \"text\"

fn f(wide: Wide) -> i64:
    let (a, b) = pair(one(1))
    return many(wide, 2) + b + a as i64 + both(wide).c as i64 + text.len as i64
";
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let check_with = |return_area| {
            let settings = Settings {
                return_area,
                ..Settings::default()
            };
            check(&program, &settings)
        };
        // What `many` takes is 137 bytes, and what `both` takes and gives is
        // 272. An area that is said to hold fewer holds neither.
        let errors = check_with(Some(128)).unwrap_err();
        let shown: Vec<_> = errors.iter().map(|e| e.kind.to_string()).collect();
        let at = |e: &TypeError| e.span.map_or("", |span| &src[span.start..span.end]);
        assert_eq!(
            shown,
            [
                "this passes 137 bytes in memory, and `return` under `[memory]` in Duck.toml \
                 gives the return area 128: without it the area holds as many as are passed",
                "this passes 272 bytes in memory, and `return` under `[memory]` in Duck.toml \
                 gives the return area 128: without it the area holds as many as are passed",
            ]
        );
        assert_eq!(errors.iter().map(at).collect::<Vec<_>>(), ["many", "both"]);
        assert_eq!(check_with(Some(271)).unwrap_err().len(), 1);
        assert!(check_with(Some(272)).is_ok());

        // Without one it holds the most that any function passes, and is
        // before every literal.
        let module = check_with(None).unwrap();
        assert_eq!(module.data.len(), 1);
        assert_eq!(
            (module.data[0].offset, &module.data[0].bytes[..]),
            (272, &b"text"[..])
        );
        let larger = check_with(Some(512)).unwrap();
        assert_eq!(larger.data[0].offset, 512);
        let types = |index: usize| {
            let import = &module.imports[index];
            (import.params.len(), import.results.len())
        };
        // One wasm value is given as it is. More are written where the
        // host is told to, and more than 16 are read from where it is.
        assert_eq!(
            [types(0), types(1), types(2), types(3)],
            [(1, 1), (2, 0), (1, 1), (2, 0)]
        );
        // What is stored for a call is read by it before any other call
        // writes there: the call of `many` follows what it is passed.
        let body = &module.funcs[0].body;
        let is_store = |stmt: &Stmt| matches!(stmt, Stmt::Store { .. });
        let stored = body
            .windows(2)
            .find(|pair| is_store(&pair[0]) && !is_store(&pair[1]));
        let Some([_, Stmt::Call { func, dests, .. }]) = stored else {
            panic!("{body:#?}");
        };
        assert_eq!(module.imports[func.0 as usize].name, "many");
        assert_eq!(dests.len(), 1);
        // The area is memory of the module's, which nothing else is in.
        assert_eq!(module.memory.min_pages, 1);
        // A module that passes nothing in memory has none.
        let direct = "extern:\n    fn one(n: i32) -> i32\nlet text = \"text\"\n";
        let tokens = tokenize(entry, direct).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let module = check(&program, &Settings::default()).unwrap();
        assert_eq!(module.data[0].offset, 0);
    }

    /// The module of `src`, a library.
    fn lower(src: &str) -> crate::ir::Module {
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        check(&program, &Settings::default()).unwrap()
    }

    #[test]
    fn nothing_is_evaluated_once_arguments_are_in_the_return_area() {
        let src = "
struct Wide:
    a: tuple(u64, u64, u64, u64, u64, u64, u64, u64)
    b: tuple(u64, u64, u64, u64, u64, u64, u64)

extern:
    fn pair(n: i32) -> tuple(i32, i64)
    fn many(wide: Wide, last: i32, more: i32) -> i64

fn second() -> i32:
    return pair(1).0

fn f(wide: Wide) -> i64:
    return many(wide, second(), 3)
";
        // `second` writes to the return area, so it is called before any
        // argument of `many` is stored there.
        let module = lower(src);
        let f = module.funcs.iter().find(|f| f.name == "f").unwrap();
        let is_store = |stmt: &&Stmt| matches!(stmt, Stmt::Store { .. });
        let first = f.body.iter().position(|stmt| is_store(&stmt)).unwrap();
        let shown = format!("{:?}", &f.body[first..]);
        let second = module.imports.len()
            + module
                .funcs
                .iter()
                .position(|f| f.name == "second")
                .unwrap();
        assert!(
            !shown.contains(&format!("Call(FuncId({second})")),
            "{shown}"
        );
        assert_eq!(f.body[first..].iter().filter(is_store).count(), 17);
    }

    #[test]
    fn a_pointer_to_an_import_passes_as_a_call_of_it_does() {
        let src = "
extern:
    fn pair(n: i32) -> tuple(i32, i64)
    fn one(n: i32) -> i32

let pointers: tuple(fn(i32) -> tuple(i32, i64), fn(i32) -> i32) = (pair, one)
";
        // What is called through a pointer takes and gives wasm values, as
        // every function of the source does.
        let module = lower(src);
        let table = module.table.unwrap().funcs;
        let imports = module.imports.len() as u32;
        assert!(table[0].0 >= imports, "{table:?}");
        assert_eq!(table[1].0, 1);
    }

    #[test]
    fn a_built_in_is_passed_as_it_is_declared() {
        let src = "
extern \"wasi:cli/stdout@0.3.0\":
    fn odd(a: tuple(i64, i64, i64, i64, i64, i64, i64, i64, i64)) -> tuple(i64, i64) = \"[stream-new-0]write-via-stream\"
    fn huge() -> tuple(u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64, u64) = \"[stream-read-0]write-via-stream\"

fn f():
    let _ = huge()
";
        let module = lower(src);
        let types = |index: usize| {
            let import = &module.imports[index];
            (import.params.len(), import.results.len())
        };
        assert_eq!([types(0), types(1)], [(9, 2), (0, 17)]);
        assert_eq!(module.memory.min_pages, 0);
    }

    #[test]
    fn what_allocates_for_the_host_is_declared_as_the_host_calls_it() {
        let src = "
extern \"my:pkg/host@0.1.0\":
    fn letter(c: u32) -> array(tuple(u32, string))

pub fn cabi_realloc(old: &u8, old_size: uint, new_size: uint) -> &var u8:
    return 0
";
        assert_eq!(
            errors_in(src, Some("hosted")),
            [(
                "`cabi_realloc` is called by the host as a `fn(old: &u8, old_size: uint, align: \
                 uint, new_size: uint) -> &var u8`"
                    .to_string(),
                "cabi_realloc"
            )]
        );
    }

    #[test]
    fn what_the_host_allocates_needs_an_allocator() {
        let needs = "the host passes a `list<tuple<u32, string>>` in memory that it has the \
                     component allocate: the entry file is to have a `pub fn cabi_realloc(old: \
                     &u8, old_size: uint, align: uint, new_size: uint) -> &var u8`";
        let import = "
extern \"my:pkg/host@0.1.0\":
    fn letter(c: u32) -> array(tuple(u32, string))

extern:
    fn trace(code: u32)
";
        let errors = errors_in(import, Some("hosted"));
        assert_eq!(errors, [(needs.to_string(), "array(tuple(u32, string))")]);
        let allocator = "
pub fn cabi_realloc(old: &u8, old_size: uint, align: uint, new_size: uint) -> &var u8:
    return 0
";
        assert_eq!(
            errors_in(&format!("{import}{allocator}"), Some("hosted")),
            []
        );
        // What is only taken is the component's own to place.
        let taken = "
extern \"my:pkg/host@0.1.0\":
    fn open(path: string) -> option(i32) = \"[static]file.open\"
";
        assert_eq!(errors_in(taken, Some("hosted")), []);
        // An export is passed what it takes.
        let export = "
pub fn count(text: string) -> u32:
    return text.len as u32
";
        let errors = errors_in(export, Some("counted"));
        assert_eq!(errors.len(), 1, "{errors:#?}");
        assert!(
            errors[0]
                .0
                .starts_with("the host passes a `string` in memory")
        );
        assert_eq!(errors[0].1, "string");
        assert_eq!(
            errors_in(&format!("{export}{allocator}"), Some("counted")),
            []
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
                    "the world `app` doesn't import `my:pkg/unused@0.1.0`, which the WIT has: \
                     one that does has `import my:pkg/unused@0.1.0;`",
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
