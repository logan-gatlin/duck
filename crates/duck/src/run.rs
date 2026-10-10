//! `duck run`: runs a component in Wasmtime, which gives it WASI 0.3.
//!
//! The component is one of a world that exports `wasi:cli/run`, as
//! `wasi:cli/command` does, and its `run` is what runs: it calls the start
//! function. That `run` is an `async func`, so what it calls may block: an
//! import that is one too is called as any other is, and returns when it is
//! done.

use std::fmt;

use duck_compiler::world::RUN_EXPORT;
use wasmtime::component::{Component, Linker, ResourceTable};
use wasmtime::{Engine, Store, Trap, WasmBacktrace};
use wasmtime_wasi::p3::bindings::Command;
use wasmtime_wasi::{FsPerms, I32Exit, WasiCtx, WasiCtxBuilder, WasiCtxView, WasiView};

/// The directories a program is given, each to read and write under the
/// path it has here: the working directory, which is the first, and the
/// root of the file system, which holds every other file.
const DIRS: [&str; 2] = [".", "/"];

/// Why a component didn't run, or stopped short of its end.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    /// One of [`DIRS`] that can't be opened.
    Dir { path: &'static str, error: String },
    /// Wasmtime can't compile or instantiate the component, as it can't
    /// one that imports what WASI doesn't have.
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
            Self::Dir { path, error } => write!(f, "cannot open `{path}`: {error}"),
            Self::Invalid(e) => write!(
                f,
                "cannot run the component, which `duck build` still builds: {e}"
            ),
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

/// Runs `component`, one of a world that exports `wasi:cli/run`, with the
/// arguments `args`, the first of which names the program. It reaches all
/// that this process does: its standard streams, its environment, its files
/// and the network. Returns the status it exits with, which is 0 unless it
/// gives another.
pub fn run(component: &[u8], args: &[String]) -> Result<u8, Error> {
    let mut ctx = context(args)?;
    execute(component, ctx.inherit_stdio().build())
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

/// Calls the `run` of `component`, giving its imports `ctx`. Returns the
/// status the program exits with.
fn execute(component: &[u8], ctx: WasiCtx) -> Result<u8, Error> {
    let invalid = |e: wasmtime::Error| Error::Invalid(format!("{e:#}"));
    let engine = Engine::default();
    let component = Component::new(&engine, component).map_err(invalid)?;
    let mut linker = Linker::new(&engine);
    wasmtime_wasi::p3::add_to_linker(&mut linker).map_err(invalid)?;
    let host = Host {
        ctx,
        table: ResourceTable::new(),
    };
    let mut store = Store::new(&engine, host);
    // The calls are async so that the program may block, and are polled by
    // the Tokio runtime that `wasmtime-wasi` keeps, which its imports need.
    let returned = wasmtime_wasi::runtime::in_tokio(async {
        let command = Command::instantiate_async(&mut store, &component, &linker);
        let command = command.await.map_err(invalid)?;
        let run = async |store: &_| command.wasi_cli_run().call_run(store).await;
        Ok(store.run_concurrent(run).await)
    })?;
    match returned {
        Ok(Ok(Ok(()))) => Ok(0),
        Ok(Ok(Err(()))) => Ok(1),
        Ok(Err(e)) | Err(e) => stopped(e),
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
        .filter(|frame| frame.func_name() != Some(RUN_EXPORT));
    Err(Error::Trap {
        message: message.to_string(),
        stack: frames
            .map(|frame| frame.func_name().unwrap_or("<unknown>").to_string())
            .collect(),
    })
}

#[cfg(test)]
mod tests {
    use duck_compiler::file::{FileId, FileManager, Settings, Wit, WitFile};
    use duck_compiler::world::COMMAND;
    use wasmtime_wasi::p2::pipe::MemoryOutputPipe;

    use super::*;

    /// What every program that writes has: `print`, which waits for what
    /// it writes to be written, and the allocator that the host returns
    /// lists through.
    const PRELUDE: &str = r#"
extern "$root":
    fn set_new() -> i32 = "[waitable-set-new]"
    fn join(waitable: i32, set: i32) = "[waitable-join]"
    fn wait(set: i32, event: &var tuple(i32, i32)) -> i32 = "[waitable-set-wait]"
    fn set_drop(set: i32) = "[waitable-set-drop]"

extern "wasi:cli/stdout@0.3.0":
    fn write_via_stream(data: i32) -> i32 = "write-via-stream"
    fn stream_new() -> i64 = "[stream-new-0]write-via-stream"
    fn stream_write(stream: i32, bytes: array(u8)) -> i32 = "[async-lower][stream-write-0]write-via-stream"
    fn stream_drop(stream: i32) = "[stream-drop-writable-0]write-via-stream"
    fn future_read(future: i32, ret: &var result(tuple(), u8)) -> i32 = "[async-lower][future-read-1]write-via-stream"
    fn future_drop(future: i32) = "[future-drop-readable-1]write-via-stream"

# An `error-code` of `wasi:filesystem` or `wasi:sockets` as it is laid out: a
# variant, the last of which holds an `option<string>`.
struct Failure:
    code: u8
    message: option(array(u8))

let newline = "\n"
let event = &var (0, 0)
let written = &var result(tuple(), u8).ok(())
var heap: uint = 0

fn settle(waitable: i32, code: i32) -> i32:
    if code != -1:
        return code
    let set = set_new()
    join(waitable, set)
    let _ = wait(set, event)
    join(waitable, 0)
    set_drop(set)
    return event.*.1

fn send(stream: i32, bytes: array(u8)):
    var rest = bytes
    while rest.len > 0:
        let code = settle(stream, stream_write(stream, rest))
        let count = (code as u32 >> 4) as uint
        rest = array(u8)(ptr: (rest.ptr as uint + count) as! &u8, len: rest.len - count)
        if code & 15 != 0:
            return

fn print(line: array(u8)):
    let ends = stream_new()
    let stream = (ends >> 32) as i32
    let future = write_via_stream(ends as i32)
    send(stream, line)
    send(stream, newline)
    stream_drop(stream)
    let _ = settle(future, future_read(future, written))
    future_drop(future)

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

    /// The component of `src` with the settings `settings`, or why it is
    /// none.
    fn compile(src: &str, settings: Settings) -> Result<Vec<u8>, String> {
        let contents = src.to_string();
        let compiled = duck_compiler::compile(&mut Source { contents, settings });
        compiled.map_err(|errors| errors[0].to_string())
    }

    /// How a program is compiled: as one that `duck run` runs, which starts
    /// with `main`.
    fn program() -> Settings {
        Settings {
            start: Some("main".to_string()),
            world: Some(COMMAND.to_string()),
            ..Settings::default()
        }
    }

    /// Runs `src` after [`PRELUDE`] with `args`. Returns its status and what
    /// it wrote to its standard output.
    fn run_with(src: &str, args: &[&str]) -> (Result<u8, Error>, String) {
        let args: Vec<_> = args.iter().map(|arg| arg.to_string()).collect();
        let stdout = MemoryOutputPipe::new(1 << 16);
        let component = compile(&format!("{PRELUDE}{src}"), program()).unwrap();
        let ctx = context(&args).unwrap().stdout(stdout.clone()).build();
        let status = execute(&component, ctx);
        (status, String::from_utf8(stdout.contents().into()).unwrap())
    }

    #[test]
    fn the_start_function_runs_with_the_arguments() {
        let src = r#"
extern "wasi:cli/environment@0.3.0":
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
        let component = compile(example, program()).unwrap();
        let ctx = context(&args).unwrap().stdout(stdout.clone()).build();
        assert_eq!(execute(&component, ctx), Ok(0));
        assert_eq!(stdout.contents(), "Hello,out.wasm duck!\n");
    }

    #[test]
    fn a_program_exits_with_its_status() {
        let coded = r#"
extern "wasi:cli/exit@0.3.0":
    fn exit(status: u8) = "exit-with-code"

let before = "before"
let after = "after"

fn main():
    print(before)
    exit(42)
    print(after)
"#;
        assert_eq!(run_with(coded, &[]), (Ok(42), "before\n".to_string()));

        let failed = r#"
extern "wasi:cli/exit@0.3.0":
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
    fn only_a_32_bit_module_with_a_start_function_is_a_program() {
        let src = "fn main():\n    pass\n";
        let unstarted = Settings {
            start: None,
            ..program()
        };
        let e = compile(src, unstarted).unwrap_err();
        assert!(e.contains("`wasi:cli/run@0.3.0`"), "{e}");
        let wide = Settings {
            memory64: true,
            ..program()
        };
        assert_eq!(
            compile(src, wide).unwrap_err(),
            "`memory64` builds no component: one addresses memory with 32 bits"
        );
        // A library is built into the components that use it.
        assert_eq!(
            compile(src, Settings::default()).unwrap_err(),
            "a library is no component: it has no world"
        );
    }

    #[test]
    fn imports_are_those_of_the_world() {
        let foreign = "extern:\n    fn log(n: i32)\n\nfn main():\n    log(1)\n";
        let e = compile(foreign, program()).unwrap_err();
        assert!(e.contains("`env::log`"), "{e}");

        // As the Canonical ABI lowers it, the function returns an `i32`.
        let mistyped = r#"
extern "wasi:cli/stdout@0.3.0":
    fn write_via_stream(data: i32) -> i64 = "write-via-stream"

fn main():
    let _ = write_via_stream(0)
"#;
        let e = compile(mistyped, program()).unwrap_err();
        let mismatch = "type mismatch for function `write-via-stream`";
        assert!(e.contains(mismatch), "{e}");

        // A list is returned in memory that the module allocates.
        let unallocated = r#"
extern "wasi:cli/environment@0.3.0":
    fn get_arguments(ret: &var array(array(u8))) = "get-arguments"

let arguments: &var array(array(u8)) = &var []

fn main():
    get_arguments(arguments)
"#;
        let e = compile(unallocated, program()).unwrap_err();
        assert!(e.contains("`cabi_realloc`"), "{e}");
    }

    #[test]
    fn a_component_is_one_of_the_world_its_package_has() {
        let wit = r#"
package my:pkg@0.1.0;

interface math {
    add: func(a: s32, b: s32) -> s32;
}

world app {
    import math;
    export double: func(n: s32) -> s32;
}
"#;
        let src = r#"
extern "my:pkg/math@0.1.0":
    fn add(a: i32, b: i32) -> i32

pub fn double(n: i32) -> i32:
    return add(n, n)

fn idle():
    pass
"#;
        let file = WitFile {
            path: "wit/app.wit".to_string(),
            contents: wit.to_string(),
        };
        let settings = |world: &str| Settings {
            world: Some(world.to_string()),
            wit: Wit {
                package: vec![file.clone()],
                deps: Vec::new(),
            },
            ..Settings::default()
        };
        let component = compile(src, settings("app")).unwrap();

        // Its import is the host's to give, and its export the host's to
        // call.
        let engine = Engine::default();
        let component = Component::new(&engine, component).unwrap();
        let mut linker = Linker::<()>::new(&engine);
        let mut math = linker.instance("my:pkg/math@0.1.0").unwrap();
        let add = |_: wasmtime::StoreContextMut<()>, (a, b): (i32, i32)| Ok((a + b,));
        math.func_wrap("add", add).unwrap();
        let mut store = Store::new(&engine, ());
        let instance = linker.instantiate(&mut store, &component).unwrap();
        let double = instance.get_typed_func::<(i32,), (i32,)>(&mut store, "double");
        assert_eq!(double.unwrap().call(&mut store, (21,)).unwrap(), (42,));

        // A world is named in full where it is another package's.
        assert!(compile(src, settings("my:pkg/app@0.1.0")).is_ok());
        let e = compile(src, settings("missing")).unwrap_err();
        assert!(e.starts_with("no world `missing`: "), "{e}");
        // A start function is what the `run` of `wasi:cli/run` calls.
        let started = Settings {
            start: Some("idle".to_string()),
            ..settings("app")
        };
        assert_eq!(
            compile(src, started).unwrap_err(),
            "`start` needs a world that exports `wasi:cli/run@0.3.0`, whose `run` calls it: \
             `app` doesn't"
        );
        // The WIT of the package is read as it is written.
        let broken = Settings {
            wit: Wit {
                package: vec![WitFile {
                    path: "wit/app.wit".to_string(),
                    contents: "package my:pkg;\nworld app { import missing; }\n".to_string(),
                }],
                deps: Vec::new(),
            },
            ..settings("app")
        };
        let e = compile(src, broken).unwrap_err();
        assert!(e.starts_with("cannot read the WIT of the package: "), "{e}");
        assert!(e.contains("wit/app.wit:2"), "{e}");
    }

    #[test]
    fn the_working_directory_and_the_root_are_open() {
        let src = r#"
extern "wasi:filesystem/preopens@0.3.0":
    fn get_directories(ret: &var array(tuple(i32, array(u8)))) = "get-directories"

extern "wasi:filesystem/types@0.3.0":
    fn open_at(
        dir: i32,
        path_flags: u8,
        path: array(u8),
        open_flags: u8,
        flags: u8,
        ret: &var result(i32, Failure),
    ) = "[method]descriptor.open-at"

let directories: &var array(tuple(i32, array(u8))) = &var []
let opened = &var result(i32, Failure).ok(0)
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

union Ip:
    ipv4: tuple(u8, u8, u8, u8)
    ipv6: tuple(u16, u16, u16, u16, u16, u16, u16, u16)

extern "wasi:sockets/ip-name-lookup@0.3.0":
    fn resolve(name: array(u8), ret: &var result(array(Ip), Failure)) = "resolve-addresses"

extern "wasi:sockets/types@0.3.0":
    fn create(family: u8, ret: &var result(i32, Failure)) = "[static]tcp-socket.create"
    fn bind(
        socket: i32,
        address: Address,
        ret: &var result(tuple(), Failure),
    ) = "[method]tcp-socket.bind"

let resolved = &var result(array(Ip), Failure).ok([])
let handle = &var result(i32, Failure).ok(0)
let bound = &var result(tuple(), Failure).ok(())
let name = "127.0.0.1"
let resolving = "resolving"
let binding = "binding"

fn main():
    # An address is its own name, which nothing is asked for.
    resolve(name, resolved)
    match resolved.*:
        .ok([.ipv4((127, 0, 0, 1))]):
            print(resolving)
        else:
            pass
    create(0, handle)
    match handle.*:
        .ok(socket):
            # Any port of this machine, which is there without a network.
            let local = Address.ipv4(Ipv4(port: 0, address: (127, 0, 0, 1)))
            bind(socket, local, bound)
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
