//! `duck wit-bindgen`: the declarations in Duck of interfaces of WIT, for a
//! library to have.
//!
//! Each type that is declared in WIT is declared as the type of Duck that
//! it is: a `record` as a struct, a `variant` as a union, an `enum` as an
//! enum, and a resource as a struct of its own that holds its handle, so
//! that no handle is taken for one of another resource. `flags` are an
//! integer, with a constant for each. Each function is declared in the
//! `extern` block of its interface, with the built-ins of the component
//! model that make, read, write and drop each stream and future it takes or
//! gives. Everything is `pub`, as it is a library's to offer.
//!
//! A package is all of its interfaces that a component may import: one that
//! worlds only export, as `wasi:cli/run` is, is declared only where it is
//! named itself.
//!
//! All that is asked for is one module, so that what two interfaces share
//! is declared once. Two of a name are each named for their interface too,
//! and for their package where that still doesn't tell them apart.

use std::collections::{HashMap, HashSet};
use std::fmt;

use wit_parser::{
    Docs, Function, FunctionKind, Handle, InterfaceId, Resolve, Type, TypeDefKind, TypeId,
    TypeOwner, WorldItem,
};

use crate::file::Settings;
use crate::format;
use crate::lex;
use crate::world::{World, WorldError, kebab};

/// The names of Duck's own types, which no item is named.
const RESERVED: [&str; 8] = [
    "array", "varray", "string", "tuple", "type", "option", "result", "never",
];

/// Why nothing was generated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BindgenError {
    /// The WIT can't be read.
    World(WorldError),
    /// A name that is no interface or package of the WIT, and the packages
    /// it has.
    Unknown { name: String, packages: Vec<String> },
    /// No name, where no world says what is imported.
    Unnamed,
}

/// What an `extern` block declares.
enum Decl<'a> {
    Function(&'a Function),
    /// What drops a handle of the resource.
    Drop(TypeId),
}

/// Something to name: what it is named in WIT, with each `-` kept, and the
/// interface and the package it is of, which name it too where another has
/// its name.
struct Named {
    own: String,
    interface: String,
    package: String,
}

/// The WIT that declarations are generated from, and what was asked of it.
struct Generator<'a> {
    world: &'a World,
    resolve: &'a Resolve,
    /// The interfaces whose functions are declared.
    interfaces: Vec<InterfaceId>,
    /// The types that are declared, in the order they are met.
    types: Vec<TypeId>,
    /// What each of those is named.
    names: HashMap<TypeId, String>,
    /// What each of those is named with the words of WIT, each `-` kept,
    /// which the constants of `flags` are named after.
    words: HashMap<TypeId, String>,
}

impl fmt::Display for BindgenError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::World(e) => e.fmt(f),
            Self::Unknown { name, packages } => {
                let packages: Vec<_> = packages.iter().map(|p| format!("`{p}`")).collect();
                write!(
                    f,
                    "the WIT has no interface or package `{name}`: its packages are {}",
                    packages.join(", ")
                )
            }
            Self::Unnamed => write!(
                f,
                "nothing to generate: name an interface or a package, as a library has no \
                 world to import any"
            ),
        }
    }
}

impl std::error::Error for BindgenError {}

/// The source of a Duck module that declares what `names` have: each an
/// interface, as `wasi:cli/stdout@0.3.0` names one, or a package, as
/// `wasi:cli@0.3.0` does, of the WIT of `settings`. Without any, what the
/// world of `settings` imports.
pub fn bindgen(settings: &Settings, names: &[String]) -> Result<String, BindgenError> {
    let world = World::load(settings).map_err(BindgenError::World)?;
    let resolve = world.resolve();
    let mut interfaces = Vec::new();
    for name in names {
        let package =
            (resolve.packages.iter()).find(|(_, package)| package.name.to_string() == *name);
        let interface = resolve.interfaces.iter().map(|(id, _)| id);
        let interface = interface.filter(|id| resolve.id_of(*id).as_deref() == Some(name));
        match package {
            // An interface that worlds only export is a component's to
            // define, and so is declared only where it is named itself.
            Some((_, package)) => {
                let imported = package
                    .interfaces
                    .values()
                    .filter(|id| !only_exported(resolve, **id));
                interfaces.extend(imported.copied());
            }
            None => interfaces.extend(interface),
        }
        if interfaces.is_empty() {
            let packages = resolve
                .packages
                .iter()
                .map(|(_, package)| package.name.to_string());
            return Err(BindgenError::Unknown {
                name: name.clone(),
                packages: packages.collect(),
            });
        }
    }
    if names.is_empty() {
        let imports = world.imports().ok_or(BindgenError::Unnamed)?;
        interfaces.extend(imports.filter_map(|item| match item {
            WorldItem::Interface { id, .. } => Some(*id),
            _ => None,
        }));
    }
    let mut seen = HashSet::new();
    interfaces.retain(|id| seen.insert(*id));
    let mut generator = Generator {
        world: &world,
        resolve,
        interfaces,
        types: Vec::new(),
        names: HashMap::new(),
        words: HashMap::new(),
    };
    generator.collect();
    let asked: String = names.iter().map(|name| format!(" {name}")).collect();
    let mut source = format!("# Generated by `duck wit-bindgen{asked}`.\n\n");
    generator.types(&mut source);
    generator.interfaces(&mut source);
    // It is laid out as any source is, if it is one.
    Ok(format::format(&source).unwrap_or(source))
}

impl<'a> Generator<'a> {
    /// Finds the types to declare: those of the interfaces, and those of
    /// others that they or their functions use. Names each.
    fn collect(&mut self) {
        for interface in self.interfaces.clone() {
            let interface = &self.resolve.interfaces[interface];
            for ty in interface.types.values() {
                self.reach(&Type::Id(*ty));
            }
            for function in interface.functions.values() {
                let params = function.params.iter().map(|param| &param.ty);
                for ty in params.chain(&function.result) {
                    self.reach(ty);
                }
            }
        }
        let named: Vec<_> = self.types.iter().map(|ty| self.type_named(*ty)).collect();
        let words = distinct(&named);
        let names = words.iter().map(|name| camel(name));
        self.names = self.types.iter().copied().zip(names).collect();
        self.words = self.types.iter().copied().zip(words).collect();
    }

    /// Notes each type to declare that `ty` is or holds.
    fn reach(&mut self, ty: &Type) {
        let Type::Id(id) = ty else {
            return;
        };
        let def = &self.resolve.types[*id];
        let declared = matches!(
            def.kind,
            TypeDefKind::Record(_)
                | TypeDefKind::Variant(_)
                | TypeDefKind::Enum(_)
                | TypeDefKind::Flags(_)
                | TypeDefKind::Resource
        );
        if declared && self.types.contains(id) {
            return;
        }
        if declared {
            self.types.push(*id);
        }
        match &def.kind {
            TypeDefKind::Type(ty) | TypeDefKind::List(ty) | TypeDefKind::Option(ty) => {
                self.reach(ty)
            }
            TypeDefKind::FixedLengthList(ty, _) => self.reach(ty),
            TypeDefKind::Handle(Handle::Own(id) | Handle::Borrow(id)) => self.reach(&Type::Id(*id)),
            TypeDefKind::Record(record) => record.fields.iter().for_each(|f| self.reach(&f.ty)),
            TypeDefKind::Variant(variant) => variant
                .cases
                .iter()
                .flat_map(|case| &case.ty)
                .for_each(|ty| self.reach(ty)),
            TypeDefKind::Tuple(tuple) => tuple.types.iter().for_each(|ty| self.reach(ty)),
            TypeDefKind::Result(result) => [&result.ok, &result.err]
                .into_iter()
                .flatten()
                .for_each(|ty| self.reach(ty)),
            TypeDefKind::Stream(ty) | TypeDefKind::Future(ty) => {
                ty.iter().for_each(|ty| self.reach(ty))
            }
            TypeDefKind::Map(key, value) => [key, value].into_iter().for_each(|ty| self.reach(ty)),
            TypeDefKind::Enum(_)
            | TypeDefKind::Flags(_)
            | TypeDefKind::Resource
            | TypeDefKind::Unknown => {}
        }
    }

    /// What names the type `ty`.
    fn type_named(&self, ty: TypeId) -> Named {
        let def = &self.resolve.types[ty];
        let interface = match def.owner {
            TypeOwner::Interface(interface) => Some(interface),
            _ => None,
        };
        self.named(def.name.clone().unwrap_or_default(), interface)
    }

    /// What names something of `interface` that is `own` there.
    fn named(&self, own: String, interface: Option<InterfaceId>) -> Named {
        let interface = interface.map(|id| &self.resolve.interfaces[id]);
        let package = interface.and_then(|interface| interface.package);
        Named {
            own,
            interface: interface.and_then(|i| i.name.clone()).unwrap_or_default(),
            package: package.map_or(String::new(), |id| {
                self.resolve.packages[id].name.name.clone()
            }),
        }
    }

    /// Declares each type after `out`.
    fn types(&self, out: &mut String) {
        for id in &self.types {
            let def = &self.resolve.types[*id];
            let name = &self.names[id];
            let wit = def.name.as_deref().unwrap_or_default();
            if let Err(held) = self.declarable(*id) {
                out.push_str(&format!(
                    "# `{wit}` holds a `{held}`, which Duck has no type for yet.\n\n"
                ));
                continue;
            }
            comment(&def.docs, "", out);
            match &def.kind {
                TypeDefKind::Resource => {
                    out.push_str(&format!("pub struct {name}:\n\tpub handle: i32\n\n"));
                }
                TypeDefKind::Record(record) => {
                    out.push_str(&format!("pub struct {name}:\n"));
                    for field in &record.fields {
                        comment(&field.docs, "\t", out);
                        let ty = self.ty(&field.ty).expect("it is declarable");
                        out.push_str(&format!("\tpub {}: {ty}\n", ident(&snake(&field.name))));
                    }
                    out.push('\n');
                }
                TypeDefKind::Variant(variant) => {
                    out.push_str(&format!("pub union {name}:\n"));
                    for case in &variant.cases {
                        comment(&case.docs, "\t", out);
                        let held = case
                            .ty
                            .as_ref()
                            .map(|ty| self.ty(ty).expect("it is declarable"));
                        let held = held.map_or(String::new(), |ty| format!(": {ty}"));
                        out.push_str(&format!("\t{}{held}\n", ident(&snake(&case.name))));
                    }
                    out.push('\n');
                }
                TypeDefKind::Enum(members) => {
                    let value = integer(members.cases.len(), 256, 65536);
                    out.push_str(&format!("pub enum({value}) {name}:\n"));
                    for case in &members.cases {
                        comment(&case.docs, "\t", out);
                        out.push_str(&format!("\t{}\n", ident(&snake(&case.name))));
                    }
                    out.push('\n');
                }
                TypeDefKind::Flags(flags) => {
                    let bits = integer(flags.flags.len(), 8, 16);
                    for (bit, flag) in flags.flags.iter().enumerate() {
                        comment(&flag.docs, "", out);
                        let flag = format!("{}-{}", self.words[id], flag.name);
                        let flag = ident(&snake(&flag).to_uppercase());
                        out.push_str(&format!("pub let {flag}: {bits} = {}\n", 1u64 << bit));
                    }
                    out.push('\n');
                }
                _ => unreachable!("only these are declared"),
            }
        }
    }

    /// Whether the type `id` can be declared: the first type it holds that
    /// Duck has none for, as WIT writes it, if it holds one.
    fn declarable(&self, id: TypeId) -> Result<(), String> {
        match &self.resolve.types[id].kind {
            TypeDefKind::Record(record) => record
                .fields
                .iter()
                .try_for_each(|field| self.ty(&field.ty).map(|_| ())),
            TypeDefKind::Variant(variant) => {
                let held = variant.cases.iter().flat_map(|case| &case.ty);
                held.into_iter().try_for_each(|ty| self.ty(ty).map(|_| ()))
            }
            _ => Ok(()),
        }
    }

    /// The type of Duck that `ty` is, or `ty` as WIT writes it if Duck has
    /// no type for it yet.
    fn ty(&self, ty: &Type) -> Result<String, String> {
        let id = match ty {
            Type::Bool => return Ok("bool".to_string()),
            Type::S8 => return Ok("i8".to_string()),
            Type::U8 => return Ok("u8".to_string()),
            Type::S16 => return Ok("i16".to_string()),
            Type::U16 => return Ok("u16".to_string()),
            Type::S32 | Type::ErrorContext => return Ok("i32".to_string()),
            Type::U32 | Type::Char => return Ok("u32".to_string()),
            Type::S64 => return Ok("i64".to_string()),
            Type::U64 => return Ok("u64".to_string()),
            Type::F32 => return Ok("f32".to_string()),
            Type::F64 => return Ok("f64".to_string()),
            Type::String => return Ok("string".to_string()),
            Type::Id(id) => *id,
        };
        let none = || Err(self.world.ty(ty).to_string());
        let unit = || Ok("tuple()".to_string());
        match &self.resolve.types[id].kind {
            TypeDefKind::Type(ty) => self.ty(ty),
            TypeDefKind::Handle(Handle::Own(id) | Handle::Borrow(id)) => self.ty(&Type::Id(*id)),
            TypeDefKind::Record(_) | TypeDefKind::Variant(_) => {
                self.declarable(id)?;
                Ok(self.names[&id].clone())
            }
            TypeDefKind::Enum(_) | TypeDefKind::Resource => Ok(self.names[&id].clone()),
            TypeDefKind::Flags(flags) => Ok(integer(flags.flags.len(), 8, 16).to_string()),
            TypeDefKind::List(elem) => Ok(format!("array({})", self.ty(elem)?)),
            // It is passed as a list of each key with its value.
            TypeDefKind::Map(key, value) => Ok(format!(
                "array(tuple({}, {}))",
                self.ty(key)?,
                self.ty(value)?
            )),
            TypeDefKind::Option(held) => Ok(format!("option({})", self.ty(held)?)),
            TypeDefKind::Result(result) => {
                let ok = result.ok.as_ref().map_or_else(unit, |ty| self.ty(ty))?;
                let err = result.err.as_ref().map_or_else(unit, |ty| self.ty(ty))?;
                Ok(format!("result({ok}, {err})"))
            }
            TypeDefKind::Tuple(tuple) => {
                let elems = tuple.types.iter().map(|ty| self.ty(ty));
                let elems = elems.collect::<Result<Vec<_>, _>>()?;
                Ok(format!("tuple({})", elems.join(", ")))
            }
            TypeDefKind::Stream(_) | TypeDefKind::Future(_) => Ok("i32".to_string()),
            TypeDefKind::FixedLengthList(..) | TypeDefKind::Unknown => none(),
        }
    }

    /// Declares the functions of each interface, in an `extern` block of
    /// it, after `out`.
    fn interfaces(&self, out: &mut String) {
        let mut decls: Vec<(InterfaceId, Decl)> = Vec::new();
        for id in &self.interfaces {
            let interface = &self.resolve.interfaces[*id];
            let functions = interface.functions.values().map(Decl::Function);
            let resources = interface
                .types
                .values()
                .filter(|ty| matches!(self.resolve.types[**ty].kind, TypeDefKind::Resource));
            let drops = resources.map(|ty| Decl::Drop(*ty));
            decls.extend(functions.chain(drops).map(|decl| (*id, decl)));
        }
        let named: Vec<_> = (decls.iter())
            .map(|(interface, decl)| self.named(self.decl_named(decl), Some(*interface)))
            .collect();
        let names: Vec<_> = distinct(&named)
            .iter()
            .map(|name| ident(&snake(name)))
            .collect();
        for id in &self.interfaces {
            let of = decls
                .iter()
                .zip(&names)
                .filter(|((interface, _), _)| interface == id);
            let mut block = String::new();
            for ((_, decl), name) in of {
                match decl {
                    Decl::Function(function) => self.function(function, name, &mut block),
                    Decl::Drop(resource) => {
                        let wit = self.resolve.types[*resource]
                            .name
                            .as_deref()
                            .unwrap_or_default();
                        let handle = &self.names[resource];
                        block.push_str(&format!(
                            "\tpub fn {name}(handle: {handle}) = \"[resource-drop]{wit}\"\n"
                        ));
                    }
                }
            }
            if !block.is_empty() {
                comment(&self.resolve.interfaces[*id].docs, "", out);
                let interface = self.resolve.id_of(*id).unwrap_or_default();
                out.push_str(&format!("extern \"{interface}\":\n{block}\n"));
            }
        }
    }

    /// What `decl` is named in WIT, with the resource it is of before it,
    /// as the type of that resource is named: for its interface too where
    /// another resource has its name.
    fn decl_named(&self, decl: &Decl) -> String {
        let wit = |id: &TypeId| self.resolve.types[*id].name.clone().unwrap_or_default();
        let resource = |id: &TypeId| self.words.get(id).cloned().unwrap_or_else(|| wit(id));
        match decl {
            Decl::Drop(id) => format!("{}-drop", resource(id)),
            Decl::Function(function) => match &function.kind {
                FunctionKind::Constructor(id) => format!("{}-new", resource(id)),
                FunctionKind::Method(id)
                | FunctionKind::AsyncMethod(id)
                | FunctionKind::Static(id)
                | FunctionKind::AsyncStatic(id) => {
                    format!("{}-{}", resource(id), function.item_name())
                }
                FunctionKind::Freestanding | FunctionKind::AsyncFreestanding => {
                    function.name.clone()
                }
            },
        }
    }

    /// Declares `function` as `name` after `out`, and then the built-ins of
    /// each stream and future that it takes or gives.
    fn function(&self, function: &Function, name: &str, out: &mut String) {
        let wit = &function.name;
        let unsupported = |does: &str, ty: String| {
            format!(
                "\t# `{}` {does} a `{ty}`, which Duck has no type for yet.\n",
                function.item_name()
            )
        };
        let mut params = Vec::new();
        for param in &function.params {
            match self.ty(&param.ty) {
                Ok(ty) => params.push(format!("{}: {ty}", ident(&snake(&param.name)))),
                Err(ty) => return out.push_str(&unsupported("takes", ty)),
            }
        }
        let result = match function.result.as_ref().map(|ty| self.ty(ty)) {
            Some(Ok(ty)) => format!(" -> {ty}"),
            Some(Err(ty)) => return out.push_str(&unsupported("gives", ty)),
            None => String::new(),
        };
        comment(&function.docs, "\t", out);
        let given = match kebab(name).as_deref() == Some(wit) {
            true => String::new(),
            false => format!(" = \"{wit}\""),
        };
        out.push_str(&format!(
            "\tpub fn {name}({}){result}{given}\n",
            params.join(", ")
        ));

        for (index, id) in function
            .find_futures_and_streams(self.resolve)
            .iter()
            .enumerate()
        {
            let (kind, held, read, write) = match &self.resolve.types[*id].kind {
                TypeDefKind::Stream(held) => ("stream", held, "into: varray", "items: array"),
                TypeDefKind::Future(held) => ("future", held, "into: &var ", "value: &"),
                _ => continue,
            };
            let builtin = |does: &str, takes: &str, gives: &str, lowered: &str| {
                let does_name = does.replace('-', "_");
                format!(
                    "\tpub fn {name}_{kind}{index}_{does_name}({takes}){gives} = \
                     \"{lowered}[{kind}-{does}-{index}]{wit}\"\n"
                )
            };
            out.push_str(&builtin("new", "", " -> i64", ""));
            // What it holds is read and written in memory, if it holds
            // anything that Duck has a type for.
            if let Some(Ok(held)) = held.as_ref().map(|ty| self.ty(ty)) {
                let of = |takes: &str| match kind {
                    "stream" => format!("{kind}: i32, {takes}({held})"),
                    _ => format!("{kind}: i32, {takes}{held}"),
                };
                out.push_str(&builtin("read", &of(read), " -> i32", "[async-lower]"));
                out.push_str(&builtin("write", &of(write), " -> i32", "[async-lower]"));
            }
            let handle = format!("{kind}: i32");
            out.push_str(&builtin("drop-readable", &handle, "", ""));
            out.push_str(&builtin("drop-writable", &handle, "", ""));
        }
    }
}

/// Whether a world of `resolve` exports `interface` and none imports it.
fn only_exported(resolve: &Resolve, interface: InterfaceId) -> bool {
    let is = |item: &WorldItem| matches!(item, WorldItem::Interface { id, .. } if *id == interface);
    let worlds = || resolve.worlds.iter().map(|(_, world)| world);
    worlds().any(|world| world.exports.values().any(is))
        && !worlds().any(|world| world.imports.values().any(is))
}

/// A name for each of `named`, with each `-` kept: its own where no other
/// has it, and else with its interface's before it, and its package's
/// before that where the interface's still doesn't tell them apart.
fn distinct(named: &[Named]) -> Vec<String> {
    let at = |named: &Named, level: usize| {
        let parts = [&named.package, &named.interface, &named.own];
        let parts: Vec<_> = parts[2 - level..]
            .iter()
            .filter(|part| !part.is_empty())
            .collect();
        parts
            .iter()
            .map(|part| part.as_str())
            .collect::<Vec<_>>()
            .join("-")
    };
    let mut levels = vec![0; named.len()];
    for _ in 0..2 {
        let names: Vec<_> = named
            .iter()
            .zip(&levels)
            .map(|(n, level)| at(n, *level))
            .collect();
        for (index, name) in names.iter().enumerate() {
            if names.iter().filter(|other| *other == name).count() > 1 {
                levels[index] = (levels[index] + 1).min(2);
            }
        }
    }
    named
        .iter()
        .zip(levels)
        .map(|(named, level)| at(named, level))
        .collect()
}

/// The comment that `docs` are, each line after `indent`, after `out`.
fn comment(docs: &Docs, indent: &str, out: &mut String) {
    for line in docs.contents.iter().flat_map(|docs| docs.lines()) {
        match line.trim_end() {
            "" => out.push_str(&format!("{indent}#\n")),
            line => out.push_str(&format!("{indent}# {line}\n")),
        }
    }
}

/// The narrowest unsigned integer for `count` of something: a `u8` for up
/// to `byte` of them, and a `u16` for up to `short`.
fn integer(count: usize, byte: usize, short: usize) -> &'static str {
    match count {
        count if count <= byte => "u8",
        count if count <= short => "u16",
        _ => "u32",
    }
}

/// `name` of WIT as a function, a field or a variable of Duck is named.
fn snake(name: &str) -> String {
    name.replace('-', "_")
}

/// `name` of WIT as a type of Duck is named.
fn camel(name: &str) -> String {
    let word = |word: &str| {
        let mut chars = word.chars();
        let first = chars.next().map(|c| c.to_ascii_uppercase());
        first.into_iter().chain(chars).collect::<String>()
    };
    ident(&name.split('-').map(word).collect::<String>())
}

/// `name`, or with a `_` after it if it is a word of Duck's own.
fn ident(name: &str) -> String {
    match lex::is_identifier(name) && !RESERVED.contains(&name) {
        true => name.to_string(),
        false => format!("{name}_"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::{DummyManager, FileManager, Wit, WitFile};
    use crate::lex::tokenize;
    use crate::load::Program;
    use crate::parse;
    use crate::ty::check;
    use crate::world::COMMAND;

    const WIT: &str = "
package my:pkg@0.1.0;

interface host {
    /// A point.
    ///
    /// Of the plane.
    record point { x: f32, %type: u8 }
    variant shape { circle(f32), rect(tuple<f32, f32>), empty }
    enum color { red, green }
    flags access {
        read,
        /// Every byte.
        write-all,
    }
    type size = u64;
    resource file {
        constructor(path: string);
        /// Reads some.
        read: func(len: size) -> result<list<u8>, color>;
        open: static func(path: string, may: access) -> option<file>;
        lines: func() -> tuple<stream<string>, future<result<_, color>>>;
    }
    area: func(s: shape, at: point) -> f32;
    wait: async func();
    in: func(%type: u32) -> bool;
    grid: func(cells: list<u8, 4>);
    count: func(words: map<string, u32>) -> map<u32, point>;
    single: func(one: tuple<u32>) -> tuple<tuple<point>>;
}

interface other {
    use host.{file};
    record point { a: s32 }
    area: func(p: point) -> s32;
    close: func(f: file, lines: stream<u8>);
}

world app {
    import other;
}
";

    fn settings(world: Option<&str>) -> Settings {
        Settings {
            world: world.map(str::to_string),
            wit: Wit {
                package: vec![WitFile {
                    path: "app.wit".to_string(),
                    contents: WIT.to_string(),
                }],
                deps: Vec::new(),
            },
            ..Settings::default()
        }
    }

    /// The errors of `src` as a library with the WIT of `settings`.
    fn errors(src: &str, settings: &Settings) -> Vec<String> {
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, src).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let errors = check(&program, settings).err().unwrap_or_default();
        errors.iter().map(|e| e.kind.to_string()).collect()
    }

    #[test]
    fn an_interface_is_declared_as_duck_has_it() {
        let names = ["my:pkg@0.1.0".to_string()];
        let generated = bindgen(&settings(None), &names).unwrap();
        for expected in [
            // A resource is a struct of its own that holds its handle.
            "pub struct File:\n\tpub handle: i32\n",
            // Two of a name are each named for their interface.
            "# A point.\n#\n# Of the plane.\npub struct HostPoint:\n\tpub x: f32\n\tpub type_: u8\n",
            "pub struct OtherPoint:\n\tpub a: i32\n",
            "pub union Shape:\n\tcircle: f32\n\trect: tuple(f32, f32)\n\tempty\n",
            "pub enum(u8) Color:\n\tred\n\tgreen\n",
            "pub let ACCESS_READ: u8 = 1\n# Every byte.\npub let ACCESS_WRITE_ALL: u8 = 2\n",
            "extern \"my:pkg/host@0.1.0\":\n",
            "\tpub fn file_new(path: string) -> File = \"[constructor]file\"\n",
            "\t# Reads some.\n\tpub fn file_read(self: File, len: u64) -> result(array(u8), Color) = \
             \"[method]file.read\"\n",
            "\tpub fn file_open(path: string, may: u8) -> option(File) = \"[static]file.open\"\n",
            "\tpub fn file_lines(self: File) -> tuple(i32, i32) = \"[method]file.lines\"\n",
            "\tpub fn file_lines_stream0_new() -> i64 = \"[stream-new-0][method]file.lines\"\n",
            "\tpub fn file_lines_stream0_read(\n\t\tstream: i32,\n\t\tinto: varray(string),\n\t) -> \
             i32 = \"[async-lower][stream-read-0][method]file.lines\"\n",
            "\tpub fn file_lines_future1_read(\n\t\tfuture: i32,\n\t\tinto: &var result(tuple(), \
             Color),\n\t) -> i32 = \"[async-lower][future-read-1][method]file.lines\"\n",
            "\tpub fn file_drop(handle: File) = \"[resource-drop]file\"\n",
            "\tpub fn host_area(s: Shape, at: HostPoint) -> f32 = \"area\"\n",
            "\tpub fn count(words: array(tuple(string, u32))) -> array(tuple(u32, HostPoint))\n",
            "\tpub fn single(one: tuple(u32)) -> tuple(tuple(HostPoint))\n",
            // A name that WIT has for it needs none given.
            "\tpub fn wait()\n",
            "\tpub fn in_(type_: u32) -> bool = \"in\"\n",
            "\t# `grid` takes a `list<u8, 4>`, which Duck has no type for yet.\n",
            "extern \"my:pkg/other@0.1.0\":\n",
            "\tpub fn other_area(p: OtherPoint) -> i32 = \"area\"\n",
            "\tpub fn close(f: File, lines: i32)\n",
            "\tpub fn close_stream0_write(\n\t\tstream: i32,\n\t\titems: array(u8),\n\t) -> i32 = \
             \"[async-lower][stream-write-0]close\"\n",
        ] {
            assert!(generated.contains(expected), "{expected}\n{generated}");
        }
        assert!(generated.starts_with("# Generated by `duck wit-bindgen my:pkg@0.1.0`.\n"));
        // It is laid out as `duck format` lays it out, and is what the WIT
        // says.
        assert_eq!(crate::format::format(&generated).unwrap(), generated);
        assert_eq!(errors(&generated, &settings(None)), Vec::<String>::new());
    }

    #[cfg(feature = "gfx")]
    #[test]
    fn what_draws_is_declared_as_its_wit_says() {
        let names = [
            "wasi:webgpu@0.3.0-rc.2",
            "wasi-gfx:frame-buffer@0.2.0",
            "wasi-gfx:surface@0.2.0",
        ];
        let generated = bindgen(&Settings::default(), &names.map(str::to_string)).unwrap();
        assert_eq!(
            errors(&generated, &Settings::default()),
            Vec::<String>::new()
        );
        assert_eq!(crate::format::format(&generated).unwrap(), generated);
        for expected in [
            "extern \"wasi:webgpu/webgpu@0.3.0-rc.2\":\n",
            "extern \"wasi-gfx:surface/surface@0.2.0\":\n",
            "extern \"wasi-gfx:surface/surface-webgpu@0.2.0\":\n",
            "extern \"wasi-gfx:surface/surface-frame-buffer@0.2.0\":\n",
            "extern \"wasi-gfx:frame-buffer/frame-buffer@0.2.0\":\n",
            "pub struct Surface:\n\tpub handle: i32\n",
            "pub struct GpuDevice:\n\tpub handle: i32\n",
            // Each function of a resource is named for it as its type is,
            // where two resources have a name.
            "pub struct SurfaceWebgpuContext:\n",
            "\tpub fn surface_webgpu_context_configure(\n",
            "\tpub fn surface_frame_buffer_context_get_current_buffer(\n",
        ] {
            assert!(generated.contains(expected), "{expected}");
        }
        assert!(
            !generated.contains("which Duck has no type for yet"),
            "{generated}"
        );
    }

    #[test]
    fn what_is_named_is_what_is_generated() {
        // An interface alone, with the types of others that it uses.
        let other = bindgen(&settings(None), &["my:pkg/other@0.1.0".to_string()]).unwrap();
        assert!(other.contains("pub struct File:\n"), "{other}");
        assert!(other.contains("pub struct Point:\n"), "{other}");
        assert!(
            other.contains("\tpub fn area(p: Point) -> i32\n"),
            "{other}"
        );
        assert!(!other.contains("my:pkg/host@0.1.0"), "{other}");
        // Without a name, what the world imports, which is every
        // interface that one it names uses.
        let imported = bindgen(&settings(Some("app")), &[]).unwrap();
        assert!(imported.starts_with("# Generated by `duck wit-bindgen`.\n"));
        assert!(imported.contains("extern \"my:pkg/other@0.1.0\":\n"));
        assert!(imported.contains("extern \"my:pkg/host@0.1.0\":\n"));
        assert_eq!(bindgen(&settings(None), &[]), Err(BindgenError::Unnamed));
        let unknown = bindgen(&settings(None), &["my:nope".to_string()]).unwrap_err();
        assert!(
            unknown
                .to_string()
                .starts_with("the WIT has no interface or package `my:nope`: "),
            "{unknown}"
        );
        assert!(unknown.to_string().contains("`my:pkg@0.1.0`"), "{unknown}");
    }

    #[test]
    fn wasi_is_declared_as_its_wit_says() {
        let wasi = ["cli", "clocks", "filesystem", "random", "sockets"];
        for package in wasi {
            let names = [format!("wasi:{package}@0.3.0")];
            let generated = bindgen(&Settings::default(), &names).unwrap();
            assert_eq!(
                errors(&generated, &Settings::default()),
                Vec::<String>::new(),
                "{package}"
            );
            assert_eq!(
                crate::format::format(&generated).unwrap(),
                generated,
                "{package}"
            );
        }
        // Each word of a name is a word of what is named for it.
        let names = ["wasi:filesystem@0.3.0".to_string()];
        let filesystem = bindgen(&Settings::default(), &names).unwrap();
        for expected in [
            "pub let OPEN_FLAGS_CREATE: u8 = 1\n",
            "pub struct DescriptorStat:\n",
            "\tpub fn descriptor_drop(handle: Descriptor) = \"[resource-drop]descriptor\"\n",
        ] {
            assert!(filesystem.contains(expected), "{expected}\n{filesystem}");
        }
        // What a program is to define is no import of it, unless it is
        // asked for.
        let cli = bindgen(&Settings::default(), &["wasi:cli@0.3.0".to_string()]).unwrap();
        assert!(cli.contains("extern \"wasi:cli/stdout@0.3.0\":\n"), "{cli}");
        assert!(!cli.contains("wasi:cli/run@0.3.0"), "{cli}");
        let run = bindgen(&Settings::default(), &["wasi:cli/run@0.3.0".to_string()]).unwrap();
        assert!(run.contains("extern \"wasi:cli/run@0.3.0\":\n"), "{run}");
        assert!(
            run.contains("\tpub fn run() -> result(tuple(), tuple())\n"),
            "{run}"
        );
        // All of it at once, as a program imports it.
        let program = Settings {
            world: Some(COMMAND.to_string()),
            start: None,
            ..Settings::default()
        };
        let all = bindgen(&program, &[]).unwrap();
        assert_eq!(errors(&all, &Settings::default()), Vec::<String>::new());
        assert!(
            all.contains("pub union FilesystemTypesErrorCode:\n"),
            "{all}"
        );
    }
}
