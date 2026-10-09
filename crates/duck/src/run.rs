//! `duck run`: runs a module in Wasmtime, which gives it WASI 0.2.
//!
//! WASI 0.2 is given to components, so the module is made one: of the world
//! `program` in `wit/duck.wit`, whose imports are those of `wasi:cli/imports`.
//! An `extern` block names one of its interfaces, as in
//! `extern "wasi:cli/stdout@0.2.12"`, and declares its functions as the
//! Canonical ABI lowers them.
//!
//! The module's start function is what runs. A component's imports that read
//! or write memory can't be called while its module is instantiated, so the
//! function is exported and called once it has been.

use std::fmt;

use duck_compiler::{emit, ir};
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Engine, Store, Trap, WasmBacktrace};
use wasmtime_wasi::{FsPerms, I32Exit, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};
use wit_component::{ComponentEncoder, StringEncoding};
use wit_parser::{Resolve, WorldId};

/// The WIT of WASI 0.2 as Wasmtime implements it, each package after those
/// it uses, and then of the world a module is run as. The packages are
/// copied from `src/p2/wit/deps` of the `wasmtime-wasi` this crate depends
/// on, and change when it does.
const WIT: [(&str, &str); 7] = [
    ("io.wit", include_str!("../wit/io.wit")),
    ("clocks.wit", include_str!("../wit/clocks.wit")),
    ("random.wit", include_str!("../wit/random.wit")),
    ("filesystem.wit", include_str!("../wit/filesystem.wit")),
    ("sockets.wit", include_str!("../wit/sockets.wit")),
    ("cli.wit", include_str!("../wit/cli.wit")),
    ("duck.wit", include_str!("../wit/duck.wit")),
];

/// The world of `wit/duck.wit` that a module is made a component of.
const WORLD: &str = "program";

/// The name that world exports the start function as. No `pub` item is
/// named it, as it is no identifier.
const START: &str = "start-function";

/// The directories a program is given, each to read and write under the
/// path it has here: the working directory, which is the first, and the
/// root of the file system, which holds every other file.
const DIRS: [&str; 2] = [".", "/"];

/// Why a module didn't run, or stopped short of its end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// The module has no start function, so nothing of it runs.
    NoStart,
    /// The module addresses memory with 64 bits, as no component does.
    Memory64,
    /// The module is no component of the world: it imports what the world
    /// doesn't have, or declares it as the Canonical ABI doesn't.
    Component(String),
    /// One of [`DIRS`] that can't be opened.
    Dir { path: &'static str, error: String },
    /// Wasmtime can't compile or instantiate the component.
    Invalid(String),
    /// A trap, with the name of each function that was running, innermost
    /// first.
    Trap { message: String, stack: Vec<String> },
}

/// What the host functions of WASI keep for one program.
struct Host {
    ctx: WasiCtx,
    table: ResourceTable,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoStart => write!(
                f,
                "nothing to run: the module has no start function, which `start` under \
                 `[module]` in Duck.toml names"
            ),
            Self::Memory64 => write!(
                f,
                "cannot run a `memory64` module: WASI 0.2 addresses memory with 32 bits"
            ),
            Self::Component(e) => write!(f, "cannot give the module WASI 0.2: {e}"),
            Self::Dir { path, error } => write!(f, "cannot open `{path}`: {error}"),
            Self::Invalid(e) => write!(f, "cannot run the module: {e}"),
            Self::Trap { message, stack } => {
                write!(f, "the program trapped: {message}")?;
                for name in stack {
                    write!(f, "\n    in `{name}`")?;
                }
                Ok(())
            }
        }
    }
}

impl std::error::Error for Error {}

impl WasiView for Host {
    fn ctx(&mut self) -> WasiCtxView<'_> {
        WasiCtxView {
            ctx: &mut self.ctx,
            table: &mut self.table,
        }
    }
}

/// Runs the start function of `module` with the arguments `args`, the first
/// of which names the program. It reaches all that this process does: its
/// standard streams, its environment, its files and the network. Returns
/// the status it exits with, which is 0 unless it gives another.
pub fn run(module: ir::Module, args: &[String]) -> Result<u8, Error> {
    let component = component(module)?;
    let mut ctx = context(args)?;
    execute(&component, ctx.inherit_stdio().build())
}

/// What a program is given but for its standard streams: its arguments,
/// the environment, [`DIRS`] and every use of the network.
fn context(args: &[String]) -> Result<WasiCtxBuilder, Error> {
    let mut ctx = WasiCtxBuilder::new();
    ctx.args(args).inherit_env().inherit_network();
    ctx.allow_tcp(true)
        .allow_udp(true)
        .allow_ip_name_lookup(true);
    for path in DIRS {
        let opened = ctx.preopened_dir(path, path, FsPerms::ReadWrite);
        opened.map_err(|e| Error::Dir {
            path,
            error: format!("{e:#}"),
        })?;
    }
    Ok(ctx)
}

/// Encodes `module` as a component of [`WORLD`], which exports its start
/// function as [`START`] rather than running it when it is instantiated.
fn component(mut module: ir::Module) -> Result<Vec<u8>, Error> {
    let start = module.start.take().ok_or(Error::NoStart)?;
    if module.memory.memory64 {
        return Err(Error::Memory64);
    }
    // A function of the module's own calls it, as the start function may
    // be an imported one, which has no export of its own.
    module.funcs.push(ir::Func {
        name: START.to_string(),
        export: Some(START.to_string()),
        params: Vec::new(),
        results: Vec::new(),
        locals: Vec::new(),
        body: vec![ir::Stmt::Call {
            func: start,
            args: Vec::new(),
            dests: Vec::new(),
        }],
    });
    let mut bytes = emit::emit(&module);
    let (resolve, world) = world();
    let encoded =
        wit_component::embed_component_metadata(&mut bytes, &resolve, world, StringEncoding::UTF8)
            .and_then(|()| ComponentEncoder::default().module(&bytes)?.encode());
    encoded.map_err(|e| {
        // The causes before the last two say only that the module was read.
        let causes: Vec<_> = e.chain().map(ToString::to_string).collect();
        Error::Component(causes[causes.len().saturating_sub(2)..].join(": "))
    })
}

/// The WIT a module is run against, and the world of it that it is run as.
fn world() -> (Resolve, WorldId) {
    let mut resolve = Resolve::default();
    let mut package = None;
    for (path, wit) in WIT {
        package = Some(resolve.push_str(path, wit).expect("the WIT is valid"));
    }
    let package = package.expect("there is WIT");
    let world = resolve.select_world(&[package], Some(WORLD));
    (resolve, world.expect("the WIT has the world"))
}

/// Calls [`START`] of `component`, giving its imports `ctx`. Returns the
/// status the program exits with.
fn execute(component: &[u8], ctx: WasiCtx) -> Result<u8, Error> {
    let invalid = |e: wasmtime::Error| Error::Invalid(format!("{e:#}"));
    let engine = Engine::default();
    let component = Component::new(&engine, component).map_err(invalid)?;
    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p2::add_to_linker_sync(&mut linker).map_err(invalid)?;
    let host = Host {
        ctx,
        table: ResourceTable::new(),
    };
    let mut store = Store::new(&engine, host);
    let instance = linker.instantiate(&mut store, &component);
    let instance = instance.map_err(invalid)?;
    let start = instance.get_typed_func::<(), ()>(&mut store, START);
    match start.map_err(invalid)?.call(&mut store, ()) {
        Ok(()) => Ok(0),
        Err(e) => stopped(e),
    }
}

/// The status of a program that `error` stopped, if it asked to exit.
fn stopped(error: wasmtime::Error) -> Result<u8, Error> {
    if let Some(I32Exit(status)) = error.downcast_ref() {
        return Ok(*status as u8);
    }
    let message = match error.downcast_ref::<Trap>() {
        Some(trap) => trap.to_string(),
        None => format!("{:#}", error.root_cause()),
    };
    let message = message.strip_prefix("wasm trap: ").unwrap_or(&message);
    let backtrace = error.downcast_ref::<WasmBacktrace>();
    let frames = backtrace.map_or(&[][..], WasmBacktrace::frames);
    // The last is the function that only calls the start function.
    let frames = frames
        .iter()
        .filter(|frame| frame.func_name() != Some(START));
    Err(Error::Trap {
        message: message.to_string(),
        stack: frames
            .map(|frame| frame.func_name().unwrap_or("<unknown>").to_string())
            .collect(),
    })
}

#[cfg(test)]
mod tests {
    use duck_compiler::file::{FileId, FileManager, Settings};
    use wasmtime_wasi::p2::pipe::MemoryOutputPipe;

    use super::*;

    /// What every program that writes has: `print`, and the allocator that
    /// the host returns lists through.
    const PRELUDE: &str = r#"
union StreamError:
    last_operation_failed: i32
    closed

extern "wasi:cli/stdout@0.2.12":
    fn get_stdout() -> i32 = "get-stdout"

extern "wasi:io/streams@0.2.12":
    fn write(
        stream: i32,
        bytes: array(u8),
        ret: &var result(tuple(), StreamError),
    ) = "[method]output-stream.blocking-write-and-flush"

let newline = "\n"
let written = &var result(tuple(), StreamError).ok(())
var heap: uint = 0

fn print(line: array(u8)):
    let out = get_stdout()
    write(out, line, written)
    write(out, newline, written)

pub fn cabi_realloc(old: &u8, old_size: uint, align: uint, new_size: uint) -> &var u8:
    if heap == 0:
        heap = module.size() * module.page_size
    let at = (heap + align - 1) / align * align
    heap = at + new_size
    let pages = (heap + module.page_size - 1) / module.page_size
    if pages > module.size():
        if module.grow(pages - module.size()) < 0:
            module.unreachable()
    let new = at as! &var u8
    module.copy(new, old, old_size)
    return new
"#;

    /// One file, whose `main` is the start function unless it has none.
    struct Source {
        contents: String,
        settings: Settings,
    }

    impl FileManager for Source {
        fn entry_point(&mut self) -> FileId {
            Self::mint_file_id(0)
        }

        fn display_name(&mut self, _: FileId) -> String {
            "main.duck".to_string()
        }

        fn contents(&mut self, _: FileId) -> String {
            self.contents.clone()
        }

        fn open(&mut self, _: FileId, _: &[&str]) -> Option<FileId> {
            None
        }

        fn open_package(&mut self, _: FileId, _: &str) -> Option<FileId> {
            None
        }

        fn settings(&mut self) -> Settings {
            self.settings.clone()
        }
    }

    /// The module of `src` with the settings `settings`.
    fn lower(src: &str, settings: Settings) -> ir::Module {
        let contents = src.to_string();
        duck_compiler::lower(&mut Source { contents, settings }).unwrap()
    }

    /// The module of `src`, which starts with `main`.
    fn program(src: &str) -> ir::Module {
        let start = Some("main".to_string());
        lower(
            src,
            Settings {
                start,
                ..Settings::default()
            },
        )
    }

    /// Runs `src` after [`PRELUDE`] with `args`. Returns its status and what
    /// it wrote to its standard output.
    fn run_with(src: &str, args: &[&str]) -> (Result<u8, Error>, String) {
        let args: Vec<_> = args.iter().map(|arg| arg.to_string()).collect();
        let stdout = MemoryOutputPipe::new(1 << 16);
        let status = component(program(&format!("{PRELUDE}{src}"))).and_then(|component| {
            let mut ctx = context(&args)?;
            execute(&component, ctx.stdout(stdout.clone()).build())
        });
        (status, String::from_utf8(stdout.contents().into()).unwrap())
    }

    #[test]
    fn the_start_function_runs_with_the_arguments() {
        let src = r#"
extern "wasi:cli/environment@0.2.12":
    fn get_arguments(ret: &var array(array(u8))) = "get-arguments"

let arguments: &var array(array(u8)) = &var []

fn main():
    get_arguments(arguments)
    for argument in arguments.*:
        print(argument)
"#;
        let (status, stdout) = run_with(src, &["out.wasm", "-a", "b c"]);
        assert_eq!(status, Ok(0));
        assert_eq!(stdout, "out.wasm\n-a\nb c\n");
    }

    #[test]
    fn the_overview_runs_as_it_says() {
        let (_, wasi) = crate::agents::OVERVIEW.split_once("\n## WASI\n").unwrap();
        let (_, example) = wasi.split_once("\n```duck\n").unwrap();
        let (example, _) = example.split_once("\n```").unwrap();
        let args = ["out.wasm", " duck!"].map(str::to_string);
        let stdout = MemoryOutputPipe::new(1 << 16);
        let component = component(program(example)).unwrap();
        let ctx = context(&args).unwrap().stdout(stdout.clone()).build();
        assert_eq!(execute(&component, ctx), Ok(0));
        assert_eq!(stdout.contents(), "Hello,out.wasm duck!\n");
    }

    #[test]
    fn a_program_exits_with_its_status() {
        let coded = r#"
extern "wasi:cli/exit@0.2.12":
    fn exit(status: u8) = "exit-with-code"

let before = "before"
let after = "after"

fn main():
    print(before)
    exit(42)
    print(after)
"#;
        assert_eq!(run_with(coded, &[]), (Ok(42), "before\n".to_string()));

        // An interface is imported at any version that this one stands for.
        let failed = r#"
extern "wasi:cli/exit@0.2.0":
    fn exit(status: result(tuple(), tuple()))

fn main():
    exit(.err(()))
"#;
        assert_eq!(run_with(failed, &[]).0, Ok(1));
    }

    #[test]
    fn a_trap_names_the_functions_that_were_running() {
        let src = r#"
var zero = 0

fn divide(by: i32) -> i32:
    return 1 / by

fn main():
    let _ = divide(zero)
"#;
        let trap = Error::Trap {
            message: "integer divide by zero".to_string(),
            stack: vec!["divide".to_string(), "main".to_string()],
        };
        assert_eq!(run_with(src, &[]).0, Err(trap.clone()));
        assert_eq!(
            trap.to_string(),
            "the program trapped: integer divide by zero\n    in `divide`\n    in `main`"
        );
    }

    #[test]
    fn only_a_32_bit_module_with_a_start_function_runs() {
        let src = "fn main():\n    pass\n";
        let unstarted = lower(src, Settings::default());
        assert_eq!(component(unstarted), Err(Error::NoStart));
        let wide = Settings {
            start: Some("main".to_string()),
            memory64: true,
            ..Settings::default()
        };
        assert_eq!(component(lower(src, wide)), Err(Error::Memory64));
    }

    #[test]
    fn imports_are_those_of_the_world() {
        let foreign = "extern:\n    fn log(n: i32)\n\nfn main():\n    log(1)\n";
        let Err(Error::Component(e)) = component(program(foreign)) else {
            panic!("`env` is no interface of WASI");
        };
        assert!(e.contains("`env::log`"), "{e}");

        // As the Canonical ABI lowers it, the function returns an `i32`.
        let mistyped = r#"
extern "wasi:cli/stdout@0.2.12":
    fn get_stdout() -> i64 = "get-stdout"

fn main():
    let _ = get_stdout()
"#;
        let Err(Error::Component(e)) = component(program(mistyped)) else {
            panic!("a handle is no `i64`");
        };
        assert!(e.contains("type mismatch for function `get-stdout`"), "{e}");

        // A list is returned in memory that the module allocates.
        let unallocated = r#"
extern "wasi:cli/environment@0.2.12":
    fn get_arguments(ret: &var array(array(u8))) = "get-arguments"

let arguments: &var array(array(u8)) = &var []

fn main():
    get_arguments(arguments)
"#;
        let Err(Error::Component(e)) = component(program(unallocated)) else {
            panic!("nothing allocates the arguments");
        };
        assert!(e.contains("`cabi_realloc`"), "{e}");
    }

    #[test]
    fn the_working_directory_and_the_root_are_open() {
        let src = r#"
extern "wasi:filesystem/preopens@0.2.12":
    fn get_directories(ret: &var array(tuple(i32, array(u8)))) = "get-directories"

extern "wasi:filesystem/types@0.2.12":
    fn open_at(
        dir: i32,
        path_flags: u8,
        path: array(u8),
        open_flags: u8,
        flags: u8,
        ret: &var result(i32, u8),
    ) = "[method]descriptor.open-at"

let directories: &var array(tuple(i32, array(u8))) = &var []
let opened = &var result(i32, u8).ok(0)
let manifest = "Cargo.toml"
let found = "found"

fn main():
    get_directories(directories)
    for directory in directories.*:
        print(directory.1)
    # To read, which is the first of the `descriptor-flags`.
    open_at(directories.*[0].0, 0, manifest, 0, 1, opened)
    match opened.*:
        .ok(_):
            print(found)
        .err(_):
            pass
"#;
        // A test runs in the directory of its crate.
        assert_eq!(run_with(src, &[]), (Ok(0), ".\n/\nfound\n".to_string()));
    }

    #[test]
    fn the_network_is_reached() {
        let src = r#"
struct Ipv4:
    port: u16
    address: tuple(u8, u8, u8, u8)

struct Ipv6:
    port: u16
    flow_info: u32
    address: tuple(u16, u16, u16, u16, u16, u16, u16, u16)
    scope_id: u32

union Address:
    ipv4: Ipv4
    ipv6: Ipv6

extern "wasi:sockets/instance-network@0.2.12":
    fn instance_network() -> i32 = "instance-network"

extern "wasi:sockets/ip-name-lookup@0.2.12":
    fn resolve(network: i32, name: array(u8), ret: &var result(i32, u8)) = "resolve-addresses"

extern "wasi:sockets/tcp-create-socket@0.2.12":
    fn create(family: u8, ret: &var result(i32, u8)) = "create-tcp-socket"

extern "wasi:sockets/tcp@0.2.12":
    fn start_bind(
        socket: i32,
        network: i32,
        address: Address,
        ret: &var result(tuple(), u8),
    ) = "[method]tcp-socket.start-bind"

let handle = &var result(i32, u8).ok(0)
let bound = &var result(tuple(), u8).ok(())
let name = "127.0.0.1"
let resolving = "resolving"
let binding = "binding"

fn main():
    let network = instance_network()
    # An address is its own name, which nothing is asked for.
    resolve(network, name, handle)
    match handle.*:
        .ok(_):
            print(resolving)
        .err(_):
            pass
    create(0, handle)
    match handle.*:
        .ok(socket):
            # Any port of this machine, which is there without a network.
            let local = Address.ipv4(Ipv4(port: 0, address: (127, 0, 0, 1)))
            start_bind(socket, network, local, bound)
        .err(_):
            return
    match bound.*:
        .ok(_):
            print(binding)
        .err(_):
            pass
"#;
        assert_eq!(
            run_with(src, &[]),
            (Ok(0), "resolving\nbinding\n".to_string())
        );
    }
}
