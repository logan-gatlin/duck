//! What a component exports: each function its world lists, found among
//! those the entry module defines.
//!
//! A function of the world itself is a `pub fn` of the entry module, or one
//! a `pub use` there names, and a function of an interface is in the
//! `pub "interface":` block of that interface. Each is named as WIT names
//! it, which is its own name with a `-` for each `_` unless an `= "name"`
//! says another.

use crate::ir::{self, FuncId};
use crate::lex::Span;
use crate::load::Program;
use crate::parse::Ident;
use crate::world::{REALLOC, RUN_INTERFACE, kebab};

use super::{Checker, FuncSig, Item, MEMORY_EXPORT, Synth, TypeError, TypeErrorKind, fn_decls};

/// A function that may be what the world exports as `name`.
struct Candidate {
    name: String,
    /// The index of the function among those lowered.
    func: usize,
    /// Where it is named: its `= "name"`, or the name it is declared or
    /// used with.
    span: Span,
    /// Whether an `= "name"` names it, which is only for an export.
    explicit: bool,
    /// Whether the world exports it.
    exported: bool,
}

impl Checker {
    /// Reports an error in no source file: one in what the settings ask.
    pub(super) fn error_nowhere(&mut self, kind: TypeErrorKind) {
        self.errors.push(TypeError::nowhere(kind));
    }

    /// Names each of `funcs`, the functions the source defines in order,
    /// as the world exports it, and reports what the world exports that
    /// none is, and what is to be exported that the world doesn't. With a
    /// `start` function the `run` of [`RUN_INTERFACE`] is made to call it,
    /// so it needs no other definition.
    pub(super) fn export_funcs(&mut self, program: &Program, funcs: &mut [ir::Func], start: bool) {
        let (mut top, mut blocks) = self.candidates(program);
        if self.world.is_library() {
            // Nothing says what a library exports.
            for (interface, _) in &blocks {
                self.error(TypeErrorKind::ExportOutsideEntry, interface.span);
            }
            if start {
                let error = self.world.start_error();
                self.error_nowhere(TypeErrorKind::World(error));
            }
            return;
        }
        let exports = self.world.exports();

        let names = exports.functions.iter().map(String::as_str);
        let missing = self.export_each(program, names.chain([REALLOC]), None, &mut top, funcs);
        let allocates = !missing.iter().any(|name| name == REALLOC);
        let missing: Vec<_> = missing.into_iter().filter(|name| name != REALLOC).collect();
        if !missing.is_empty() {
            self.error_nowhere(TypeErrorKind::MissingExports {
                interface: None,
                names: missing,
            });
        }

        let mut runs = false;
        for interface in &exports.interfaces {
            let started = interface.name == RUN_INTERFACE && start;
            runs |= interface.name == RUN_INTERFACE;
            let block = blocks.iter_mut().find(|(i, _)| i.name == interface.name);
            let Some((named, candidates)) = block else {
                if !started && !interface.functions.is_empty() {
                    self.error_nowhere(TypeErrorKind::MissingExports {
                        interface: Some(interface.name.clone()),
                        names: interface.functions.clone(),
                    });
                }
                continue;
            };
            let span = named.span;
            if started {
                self.error(TypeErrorKind::StartAndRun, span);
            }
            let names = interface.functions.iter().map(String::as_str);
            let named = Some(interface.name.as_str());
            let missing = self.export_each(program, names, named, candidates, funcs);
            if !missing.is_empty() {
                let interface = Some(interface.name.clone());
                let names = missing;
                self.error(TypeErrorKind::MissingExports { interface, names }, span);
            }
        }
        let exported = |name: &str| exports.interfaces.iter().any(|i| i.name == name);
        for (interface, _) in blocks.iter().filter(|(i, _)| !exported(&i.name)) {
            let exported = exports.interfaces.iter().map(|i| i.name.clone());
            let kind = TypeErrorKind::UnknownExportInterface {
                name: interface.name.clone(),
                exported: exported.collect(),
            };
            self.error(kind, interface.span);
        }
        if start && !runs {
            let error = self.world.start_error();
            self.error_nowhere(TypeErrorKind::World(error));
        }
        if let (false, Some((span, wit))) = (allocates, self.allocated.clone()) {
            self.error(TypeErrorKind::NeedsRealloc(wit), span);
        }
    }

    /// The functions that may be exported: those of the world itself, and
    /// those of each `pub "interface":` block, with the interface as the
    /// block names it.
    fn candidates(&mut self, program: &Program) -> (Vec<Candidate>, Vec<(Ident, Vec<Candidate>)>) {
        let mut top = Vec::new();
        let mut blocks: Vec<(Ident, Vec<Candidate>)> = Vec::new();
        for (func, (item, decl)) in fn_decls(program).enumerate() {
            let in_entry = item.span.file == self.entry;
            let own = &decl.sig.name;
            let explicit = decl.export_name.is_some();
            let named = match &decl.export_name {
                Some(name) => Some((name.name.clone(), name.span)),
                None => kebab(&own.name).map(|name| (name, own.span)),
            };
            let candidate = |(name, span)| Candidate {
                name,
                func,
                span,
                explicit,
                exported: false,
            };
            if let Some(interface) = &decl.interface {
                // Each block is reported once, where it is named.
                let block = blocks.iter().position(|(i, _)| i.span == interface.span);
                let block = block.unwrap_or_else(|| {
                    if !in_entry {
                        self.error(TypeErrorKind::ExportOutsideEntry, interface.span);
                    } else if blocks.iter().any(|(i, _)| i.name == interface.name) {
                        let name = interface.name.clone();
                        self.error(TypeErrorKind::ExportBlockRepeated(name), interface.span);
                    }
                    blocks.push((interface.clone(), Vec::new()));
                    blocks.len() - 1
                });
                match named {
                    Some(named) => blocks[block].1.push(candidate(named)),
                    None => self.error(TypeErrorKind::NoWitName(own.name.clone()), own.span),
                }
            } else if in_entry && item.is_pub {
                // One with no name in WIT is `pub` and nothing more.
                let realloc = (own.name == REALLOC && !explicit).then(|| REALLOC.to_string());
                let named = realloc.map(|name| (name, own.span)).or(named);
                top.extend(named.map(candidate));
            } else if let Some(name) = &decl.export_name {
                self.error(TypeErrorKind::UnexportedName, name.span);
            }
        }
        // Only the entry module's blocks are of the world.
        blocks.retain(|(interface, _)| interface.span.file == self.entry);
        let mut seen = Vec::new();
        blocks.retain(|(interface, _)| {
            let first = !seen.contains(&interface.name);
            seen.push(interface.name.clone());
            first
        });
        for (item, name) in &self.reexports {
            let Item::Func(id) = item else {
                continue;
            };
            let named = match name.name == REALLOC {
                true => Some(REALLOC.to_string()),
                false => kebab(&name.name),
            };
            top.extend(named.map(|named| Candidate {
                name: named,
                func: (id.0 - self.import_count) as usize,
                span: name.span,
                explicit: false,
                exported: false,
            }));
        }
        (top, blocks)
    }

    /// Exports the candidate of each of `names`, the functions of
    /// `interface` or of the world itself, and reports one that isn't
    /// declared as the WIT declares it, another of the same name, and one
    /// that says a name the world doesn't have. Returns the names that no
    /// candidate has.
    fn export_each<'a>(
        &mut self,
        program: &Program,
        names: impl Iterator<Item = &'a str>,
        interface: Option<&str>,
        candidates: &mut [Candidate],
        funcs: &mut [ir::Func],
    ) -> Vec<String> {
        let mut missing = Vec::new();
        for name in names {
            let mut named = candidates.iter_mut().filter(|c| c.name == name);
            let Some(first) = named.next() else {
                missing.push(name.to_string());
                continue;
            };
            first.exported = true;
            let func = first.func;
            for again in named {
                again.exported = true;
                self.error(TypeErrorKind::DuplicateExport(name.to_string()), again.span);
            }
            let export = match interface {
                Some(interface) => format!("{interface}#{name}"),
                None => name.to_string(),
            };
            // The module exports its memory by that name.
            if export == MEMORY_EXPORT {
                let span = candidates.iter().find(|c| c.func == func).map(|c| c.span);
                let kind = TypeErrorKind::ReservedExport(export.clone());
                self.error(kind, span.expect("it is a candidate"));
            }
            // What allocates for the host is no function of the world's.
            let Some(function) = self.world.export(interface, name) else {
                funcs[func].exports.push(export);
                continue;
            };
            let (_, decl) = fn_decls(program).nth(func).expect("it is defined");
            let target = FuncId(self.import_count + func as u32);
            let sig = self.funcs[target.0 as usize].clone();
            self.check_signature(&decl.sig, &sig, &function, false);
            self.check_fits(&sig, false, decl.sig.name.span);
            // One that takes or gives more than wasm values hold is called
            // by a function that passes the rest in memory, as the host has
            // it.
            let passing = self.passing(&sig, false);
            if passing.params.is_none() && passing.result.is_none() {
                funcs[func].exports.push(export);
                continue;
            }
            self.funcs.push(FuncSig {
                name: format!("export {}", sig.name),
                defaults: Vec::new(),
                ..sig
            });
            self.synths.push(Synth::Export(target, export));
        }
        // A function of the world itself that it doesn't export is only
        // `pub`, unless it says what it is exported as.
        let unknown = candidates.iter().filter(|c| !c.exported);
        for candidate in unknown.filter(|c| c.explicit || interface.is_some()) {
            let kind = TypeErrorKind::UnknownExport {
                interface: interface.map(str::to_string),
                name: candidate.name.clone(),
            };
            self.error(kind, candidate.span);
        }
        missing
    }
}

#[cfg(test)]
mod tests {
    use crate::file::{DummyManager, FileManager, Settings, Wit, WitFile};
    use crate::ir::Module;
    use crate::lex::tokenize;
    use crate::load::Program;
    use crate::parse;
    use crate::ty::{TypeError, check};
    use crate::world::COMMAND;

    const WIT: &str = "
package my:pkg@0.1.0;

interface math {
    add: func(a: s32, b: s32) -> s32;
    negate-it: func(a: s32) -> s32;
}

interface marker {
    type id = u32;
}

world app {
    export math;
    export marker;
    export tick-now: func();
    export poll: func() -> s32;
}

world bare {
}

world hosted {
    include wasi:cli/imports@0.3.0;
    import trace-it: func(code: u32);
}
";

    /// Checks `src` as a component of `world`, one of [`WIT`] or of WASI.
    fn check_in(src: &str, world: &str, start: Option<&str>) -> Result<Module, Vec<TypeError>> {
        let settings = Settings {
            start: start.map(str::to_string),
            world: Some(world.to_string()),
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
        check(
            &Program::single(entry, parse::parse(&tokens).unwrap()),
            &settings,
        )
    }

    /// Each function of `module` that is exported, with what it is exported
    /// as.
    fn exported(module: &Module) -> Vec<(&str, Vec<&str>)> {
        let funcs = module.funcs.iter().filter(|f| !f.exports.is_empty());
        let named = funcs.map(|f| {
            let exports = f.exports.iter().map(String::as_str).collect();
            (f.name.as_str(), exports)
        });
        named.collect()
    }

    /// Each error of `src` as a component of `world`, as it is shown, with
    /// what it is reported at.
    fn errors_in<'a>(src: &'a str, world: &str, start: Option<&str>) -> Vec<(String, &'a str)> {
        let errors = check_in(src, world, start).unwrap_err();
        let at = |e: &TypeError| e.span.map_or("", |span| &src[span.start..span.end]);
        errors.iter().map(|e| (e.kind.to_string(), at(e))).collect()
    }

    const APP: &str = "
pub \"my:pkg/math@0.1.0\":
    fn add(a: i32, b: i32) -> i32:
        return a + b
    pub fn negate(a: i32) -> i32 = \"negate-it\":
        return 0 - a

pub fn tick_now():
    pass

pub fn poll() -> i32:
    return add(1, negate(1))

pub fn helper():
    pass

pub fn _unnamed():
    pass

fn private():
    pass
";

    #[test]
    fn a_component_exports_what_its_world_does() {
        let module = check_in(APP, "app", None).unwrap();
        assert_eq!(
            exported(&module),
            [
                ("add", vec!["my:pkg/math@0.1.0#add"]),
                ("negate", vec!["my:pkg/math@0.1.0#negate-it"]),
                ("tick_now", vec!["tick-now"]),
                ("poll", vec!["poll"]),
            ]
        );
        // Neither a global nor the table is exported, as no world has one.
        let globals = "pub let limit = 1\npub var count = 0\nfn f():\n    count = limit\n\
                       let pointer = f\n";
        let module = check_in(globals, "bare", None).unwrap();
        assert!(module.globals.iter().all(|g| g.exports.is_empty()));
        assert_eq!(module.table.unwrap().export, None);
    }

    #[test]
    fn what_the_world_exports_is_defined() {
        let src = "
pub \"my:pkg/math@0.1.0\":
    fn add(a: i32, b: i32) -> i32:
        return a + b
    fn extra():
        pass
    fn Odd():
        pass

pub fn poll() -> i32:
    return 1
";
        assert_eq!(
            errors_in(src, "app", None),
            [
                (
                    "`Odd` has no name in WIT, where one is words of lowercase letters or of \
                     capitals joined by `-`: give it one with `= \"name\"`"
                        .to_string(),
                    "Odd"
                ),
                (
                    "nothing defines `tick-now`, which the world exports: each is a `pub fn` of \
                     the entry file"
                        .to_string(),
                    ""
                ),
                (
                    "`my:pkg/math@0.1.0` has no function `extra`".to_string(),
                    "extra"
                ),
                (
                    "nothing defines `negate-it` of `my:pkg/math@0.1.0`, which the world \
                     exports: define each in a `pub \"my:pkg/math@0.1.0\":` block"
                        .to_string(),
                    "\"my:pkg/math@0.1.0\""
                ),
            ]
        );
        // An interface with no block is as one whose block has nothing.
        assert_eq!(
            errors_in(
                "pub fn tick_now():\n    pass\npub fn poll() -> i32:\n    return 1\n",
                "app",
                None
            ),
            [(
                "nothing defines `add`, `negate-it` of `my:pkg/math@0.1.0`, which the world \
                 exports: define each in a `pub \"my:pkg/math@0.1.0\":` block"
                    .to_string(),
                ""
            )]
        );
    }

    #[test]
    fn only_what_the_world_exports_is_named_for_it() {
        let src = "
pub \"my:pkg/other@0.1.0\":
    fn f():
        pass

pub \"my:pkg/marker@0.1.0\":
    pass

pub fn tick() = \"tick\":
    pass

pub fn again() = \"poll\":
    pass

pub fn poll():
    pass

fn private() = \"private\":
    pass
";
        assert_eq!(
            errors_in(src, "bare", None),
            [
                (
                    "only a function that is exported has a name to be exported as".to_string(),
                    "\"private\""
                ),
                (
                    "the world exports no function `tick`".to_string(),
                    "\"tick\""
                ),
                (
                    "the world exports no function `poll`".to_string(),
                    "\"poll\""
                ),
                (
                    "the world exports no interface `my:pkg/other@0.1.0`: it exports none"
                        .to_string(),
                    "\"my:pkg/other@0.1.0\""
                ),
            ]
        );
        let twice = "
pub \"my:pkg/math@0.1.0\":
    fn add(a: i32, b: i32) -> i32:
        return a
    fn negate_it(a: i32) -> i32:
        return a
    fn again(a: i32) -> i32 = \"add\":
        return a

pub \"my:pkg/math@0.1.0\":
    fn other():
        pass

pub \"wasi:cli/run@0.3.0\":
    pass

pub fn tick_now():
    pass

pub fn poll() -> i32:
    return 1

pub fn sample() -> i32 = \"poll\":
    return 2
";
        assert_eq!(
            errors_in(twice, "app", None),
            [
                (
                    "another block exports `my:pkg/math@0.1.0`: one has every function of an \
                     interface"
                        .to_string(),
                    "\"my:pkg/math@0.1.0\""
                ),
                (
                    "another function is exported as `poll`".to_string(),
                    "\"poll\""
                ),
                (
                    "another function is exported as `add`".to_string(),
                    "\"add\""
                ),
            ]
        );
        // A library has no world to export anything.
        let library = "pub \"my:pkg/math@0.1.0\":\n    fn add():\n        pass\n";
        let entry = DummyManager::new().entry_point();
        let tokens = tokenize(entry, library).unwrap();
        let program = Program::single(entry, parse::parse(&tokens).unwrap());
        let errors = check(&program, &Settings::default()).unwrap_err();
        let shown: Vec<_> = errors.iter().map(|e| e.kind.to_string()).collect();
        assert_eq!(
            shown,
            ["only the entry file of a component exports an interface"]
        );
    }

    #[test]
    fn a_program_is_its_start_function_or_its_run() {
        let src = "
pub \"wasi:cli/run@0.3.0\":
    fn run() -> result(tuple(), tuple()):
        return .err(())

fn main():
    pass
";
        let module = check_in(src, COMMAND, None).unwrap();
        assert_eq!(exported(&module), [("run", vec!["wasi:cli/run@0.3.0#run"])]);
        assert_eq!(
            errors_in(src, COMMAND, Some("main")),
            [(
                "`start` in Duck.toml names what a `run` made for it calls, so none is defined"
                    .to_string(),
                "\"wasi:cli/run@0.3.0\""
            )]
        );
        let main = "fn main():\n    pass\n";
        let module = check_in(main, COMMAND, Some("main")).unwrap();
        let run = "wasi:cli/run@0.3.0#run";
        assert_eq!(exported(&module), [(run, vec![run])]);
        assert_eq!(
            errors_in(main, COMMAND, None),
            [(
                "nothing defines `run` of `wasi:cli/run@0.3.0`, which the world exports: name \
                 a `start` in Duck.toml for it to call, or define it in a \
                 `pub \"wasi:cli/run@0.3.0\":` block"
                    .to_string(),
                ""
            )]
        );
        assert_eq!(
            errors_in(main, "bare", Some("main")),
            [(
                "`start` needs a world that exports `wasi:cli/run@0.3.0`, whose `run` calls \
                 it: `bare` doesn't"
                    .to_string(),
                ""
            )]
        );
    }

    #[test]
    fn the_host_knows_a_function_by_its_name_in_wit() {
        let src = "
extern \"wasi:cli/environment@0.3.0\":
    fn get_arguments() -> array(string)
    fn cwd() -> option(string) = \"get-initial-cwd\"

extern:
    fn trace_it(code: u32)

pub fn cabi_realloc(old: &u8, old_size: uint, align: uint, new_size: uint) -> &var u8:
    return 0
";
        let module = check_in(src, "hosted", None).unwrap();
        let imports = module.imports.iter();
        let imports: Vec<_> = imports
            .map(|i| (i.module.as_str(), i.field.as_str()))
            .collect();
        assert_eq!(
            imports,
            [
                ("wasi:cli/environment@0.3.0", "get-arguments"),
                ("wasi:cli/environment@0.3.0", "get-initial-cwd"),
                ("$root", "trace-it"),
            ]
        );
        // What allocates for the host has one name, which is no WIT's.
        assert_eq!(exported(&module), [("cabi_realloc", vec!["cabi_realloc"])]);

        let unnamed = "extern:\n    fn getArgs()\n    fn _private()\n    fn trace_it(code: u32)\n";
        let errors = errors_in(unnamed, "hosted", None);
        let at: Vec<_> = errors.iter().map(|(_, at)| *at).collect();
        assert_eq!(at, ["getArgs", "_private"]);
    }

    #[test]
    fn a_world_that_is_not_there_is_an_error_in_no_file() {
        let errors = errors_in("fn f():\n    pass\n", "missing", None);
        assert_eq!(errors.len(), 1, "{errors:?}");
        assert!(
            errors[0].0.starts_with("no world `missing`: "),
            "{errors:?}"
        );
        assert_eq!(errors[0].1, "");
    }
}
