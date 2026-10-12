//! `duck test`: runs the tests of a package, each in an instance of its
//! own.
//!
//! The component of the tests is compiled once, and exports one function,
//! which calls the test at an index. Each test is that call in a new store
//! and a new instance, so it starts with the memory, the globals and the
//! table that the constants of the package left: nothing a test does to
//! them is there for the next. What is outside the instance is not put
//! back: a file that a test writes stays written.
//!
//! A test is given what `duck run` gives a program: WASI 0.3, with the same
//! directories, environment and network, and its standard streams.
//!
//! Each test is reported as it runs, on a [`Console`]: its name as it
//! starts, and on the same line how it ended and how long it took, as in
//! `test lexer.empty_source ... ok (3 ms)`. What a test writes goes where
//! it writes it, as it writes it, between two lines that name the test:
//! the first is ended before what it writes, and the second says how it
//! ended.
//!
//! ```text
//! test lexer.traces ...
//! 2 tokens
//! test lexer.traces ... ok (3 ms)
//! ```

use std::fmt;
use std::io::{self, Write};
use std::mem;
use std::pin::Pin;
use std::sync::{Arc, Mutex, MutexGuard};
use std::task::{Context, Poll};
use std::time::{Duration, Instant};

use duck_compiler::Tests;
use duck_compiler::ty::Test;
use duck_compiler::world::TEST_EXPORT;
use tokio::io::AsyncWrite;
use wasmtime::component::{Component, InstancePre};
use wasmtime::{Engine, Store};
use wasmtime_wasi::WasiCtx;
use wasmtime_wasi::cli::{IsTerminal, StdoutStream};

use super::{Error, Host, context, invalid, linker, stopped};

/// The tests of a package, ready to run: their component, compiled, with
/// what it imports found.
pub struct Runner {
    engine: Engine,
    component: InstancePre<Host>,
    /// The arguments each test is given: the name of the program alone.
    args: Vec<String>,
}

/// Where the tests of a package are reported, and where what they write
/// goes: a standard output, which has the lines that say how each test
/// ended and what tests write to theirs, and a standard error, which has
/// what they write to theirs. Each is written to in the order things
/// happen, and nothing is kept back from either: a line is there as soon as
/// it is written, whether or not it has its end.
///
/// What is cloned of it writes to the same two, as one.
#[derive(Clone)]
pub struct Console(Arc<Mutex<Written>>);

/// What a [`Console`] writes to, and where it is in what it writes.
struct Written {
    /// The standard output and then the standard error, each with whether
    /// it is a terminal, which a test is told of its own.
    streams: [(Box<dyn Write + Send>, bool); 2],
    /// Whether the line that names the test that is running is still the
    /// last thing written: the test has written nothing.
    named: bool,
    /// Whether what a test last wrote to each stream left a line without
    /// its end.
    unended: [bool; 2],
}

/// One of the two standard streams that a test writes to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Stream {
    Out,
    Err,
}

/// A standard stream of a test, which writes to that of a [`Console`].
#[derive(Clone)]
struct TestStream {
    console: Console,
    stream: Stream,
}

/// Why a test failed, as it passes by returning.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Failure {
    /// It trapped: what the trap said, and the name of each function that
    /// was running, innermost first.
    Trap { message: String, stack: Vec<String> },
    /// It exited with this status.
    Exit(u8),
}

/// How many of the tests of a package did what.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct Summary {
    pub passed: usize,
    pub failed: usize,
    /// Those that a filter asked for and that weren't run, as one of those
    /// to skip named them.
    pub skipped: usize,
    /// Those that weren't run, as there were filters and none named them,
    /// whether or not they were to be skipped too.
    pub filtered: usize,
    /// How long the tests that ran took between them.
    pub time: Duration,
}

/// What ends each line that tests are reported by.
const NEWLINE: &[u8] = b"\n";

impl fmt::Display for Failure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Trap { message, stack } => {
                write!(f, "the test trapped: {message}")?;
                for name in stack {
                    write!(f, "\n    in `{name}`")?;
                }
                Ok(())
            }
            Self::Exit(status) => write!(
                f,
                "the test exited with status {status}: one passes by returning"
            ),
        }
    }
}

impl fmt::Display for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} passed, {} failed", self.passed, self.failed)?;
        if self.skipped > 0 {
            write!(f, ", {} skipped", self.skipped)?;
        }
        if self.filtered > 0 {
            write!(f, ", {} filtered out", self.filtered)?;
        }
        write!(f, " ({})", elapsed(self.time))
    }
}

impl Stream {
    /// Its place among the streams of a [`Console`].
    fn index(self) -> usize {
        match self {
            Self::Out => 0,
            Self::Err => 1,
        }
    }
}

impl Console {
    /// The standard streams of this process.
    pub fn stdio() -> Self {
        let (out, err) = (io::stdout(), io::stderr());
        let terminals = [
            io::IsTerminal::is_terminal(&out),
            io::IsTerminal::is_terminal(&err),
        ];
        Self::new(out, err, terminals)
    }

    /// One that writes to `out` as its standard output and to `err` as its
    /// standard error, each of which is a terminal if `terminals` says so
    /// of it.
    pub fn new(
        out: impl Write + Send + 'static,
        err: impl Write + Send + 'static,
        terminals: [bool; 2],
    ) -> Self {
        let [out_terminal, err_terminal] = terminals;
        let written = Written {
            streams: [(Box::new(out), out_terminal), (Box::new(err), err_terminal)],
            named: false,
            unended: [false; 2],
        };
        Self(Arc::new(Mutex::new(written)))
    }

    /// What is written, which a thread that panicked while it wrote left
    /// as it is.
    fn written(&self) -> MutexGuard<'_, Written> {
        self.0
            .lock()
            .unwrap_or_else(|poisoned| poisoned.into_inner())
    }

    /// Says that the test `name` runs: what is said of it next is on the
    /// same line, unless the test writes first.
    fn start(&self, name: &str) {
        let mut written = self.written();
        written.put(Stream::Out, format!("test {name} ...").as_bytes());
        written.named = true;
    }

    /// Says that the test `name`, which was said to run, ended as `verdict`
    /// says: on the line that names it, or else on one that names it again,
    /// after what the test wrote. A line that the test left without its end
    /// is given one, on the stream that it is on.
    fn end(&self, name: &str, verdict: &str) {
        let mut written = self.written();
        written.end_lines();
        let line = match written.named {
            true => format!(" {verdict}\n"),
            false => format!("test {name} ... {verdict}\n"),
        };
        written.put(Stream::Out, line.as_bytes());
        written.named = false;
    }

    /// Ends the line that names a test that was said to run and that
    /// nothing will be said of, as it couldn't be run.
    fn abandon(&self) {
        let mut written = self.written();
        written.unended[Stream::Out.index()] |= written.named;
        written.named = false;
        written.end_lines();
    }

    /// Writes `line` on a line of its own.
    fn line(&self, line: &str) {
        self.written()
            .put(Stream::Out, format!("{line}\n").as_bytes());
    }

    /// Writes `bytes`, which a test writes to its `stream`: after the end
    /// of the line that names the test, if nothing was written since.
    fn write(&self, stream: Stream, bytes: &[u8]) -> io::Result<usize> {
        if bytes.is_empty() {
            return Ok(0);
        }
        let mut written = self.written();
        if written.named {
            written.put(Stream::Out, NEWLINE);
            written.named = false;
        }
        let (to, _) = &mut written.streams[stream.index()];
        to.write_all(bytes).and_then(|()| to.flush())?;
        written.unended[stream.index()] = !bytes.ends_with(NEWLINE);
        Ok(bytes.len())
    }

    /// The `stream` of a test, which writes here.
    fn stream(&self, stream: Stream) -> TestStream {
        TestStream {
            console: self.clone(),
            stream,
        }
    }
}

impl Written {
    /// Writes `bytes` to `stream`, and has them there at once. What can't
    /// be written is not: how many tests failed still says what they did.
    fn put(&mut self, stream: Stream, bytes: &[u8]) {
        let (to, _) = &mut self.streams[stream.index()];
        let _ = to.write_all(bytes).and_then(|()| to.flush());
    }

    /// Ends each line that was left without its end, on its own stream.
    fn end_lines(&mut self) {
        for stream in [Stream::Out, Stream::Err] {
            if mem::take(&mut self.unended[stream.index()]) {
                self.put(stream, NEWLINE);
            }
        }
    }
}

impl IsTerminal for TestStream {
    fn is_terminal(&self) -> bool {
        self.console.written().streams[self.stream.index()].1
    }
}

impl StdoutStream for TestStream {
    fn async_stream(&self) -> Box<dyn AsyncWrite + Send + Sync> {
        Box::new(self.clone())
    }
}

/// Writes at once, as the standard streams of a process are written to: a
/// test waits for what it writes to be written.
impl AsyncWrite for TestStream {
    fn poll_write(
        self: Pin<&mut Self>,
        _: &mut Context<'_>,
        bytes: &[u8],
    ) -> Poll<io::Result<usize>> {
        Poll::Ready(self.console.write(self.stream, bytes))
    }

    fn poll_flush(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }

    fn poll_shutdown(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<io::Result<()>> {
        Poll::Ready(Ok(()))
    }
}

impl Runner {
    /// Compiles `component`, that of the tests of a package, for a program
    /// named `name` to run each of them as.
    pub fn new(component: &[u8], name: &str) -> Result<Self, Error> {
        let engine = Engine::default();
        let component = Component::new(&engine, component).map_err(invalid)?;
        // A window is opened by the thread that a process starts on, which
        // runs the tests.
        #[cfg(feature = "gfx")]
        if super::gfx::opens_windows(&component, &engine) {
            return Err(Error::Windowed);
        }
        let component = linker(&engine)?.instantiate_pre(&component);
        Ok(Self {
            component: component.map_err(invalid)?,
            engine,
            args: vec![name.to_string()],
        })
    }

    /// Runs the test at `index` of the tests the component was compiled
    /// with, in an instance of its own. It reaches all that this process
    /// does, as a program that `duck run` runs, but that what it writes to
    /// its standard streams is written to `console`. Returns why it failed,
    /// if it did.
    pub fn run(&self, index: usize, console: &Console) -> Result<Option<Failure>, Error> {
        let mut ctx = context(&self.args)?;
        ctx.inherit_stdin()
            .stdout(console.stream(Stream::Out))
            .stderr(console.stream(Stream::Err));
        self.run_with(index, ctx.build())
    }

    /// Runs the test at `index`, giving its imports `ctx`.
    fn run_with(&self, index: usize, ctx: WasiCtx) -> Result<Option<Failure>, Error> {
        let host = Host::new(
            ctx,
            #[cfg(feature = "gfx")]
            super::gfx::Gfx::default(),
        );
        let mut store = Store::new(&self.engine, host);
        // The calls are async so that the test may block, as a program may.
        let returned = wasmtime_wasi::runtime::in_tokio(async {
            let instance = self.component.instantiate_async(&mut store).await;
            let instance = instance.map_err(invalid)?;
            let call = instance.get_typed_func::<(u32,), ()>(&mut store, TEST_EXPORT);
            let call = call.map_err(invalid)?;
            Ok(call.call_async(&mut store, (index as u32,)).await)
        })?;
        let failure = match returned.map_err(|e| stopped(e, TEST_EXPORT)) {
            Ok(()) => None,
            Err(Ok(status)) => Some(Failure::Exit(status)),
            Err(Err(Error::Trap { message, stack })) => Some(Failure::Trap { message, stack }),
            Err(Err(error)) => return Err(error),
        };
        Ok(failure)
    }
}

/// Whether one of `filters` names `test`: its name has that one in it.
fn named(test: &Test, filters: &[String]) -> bool {
    let mut filters = filters.iter();
    filters.any(|filter| test.name.contains(filter.as_str()))
}

/// Whether `test` is one that `filters` ask for: one of them names it, or
/// there are none.
fn asked(test: &Test, filters: &[String]) -> bool {
    filters.is_empty() || named(test, filters)
}

/// How long `time` is, as it is said of a test: in whole milliseconds, or
/// in seconds and tenths of one from a second up.
fn elapsed(time: Duration) -> String {
    match time.as_millis() {
        millis if millis < 1000 => format!("{millis} ms"),
        _ => format!("{:.1} s", time.as_secs_f64()),
    }
}

/// How a test that took `time` ended, where `ended` says whether it passed:
/// with how long it took, unless that is less than a millisecond, which is
/// no time worth the saying of every test.
fn verdict(ended: &str, time: Duration) -> String {
    match time.as_millis() {
        0 => ended.to_string(),
        _ => format!("{ended} ({})", elapsed(time)),
    }
}

/// Writes to `out` the name of each of `tests` that `filters` ask for and
/// that none of `skip` names, a line each, in the order they would run in.
pub fn list(
    tests: &[Test],
    filters: &[String],
    skip: &[String],
    out: &mut impl Write,
) -> io::Result<()> {
    let listed = |test: &&Test| asked(test, filters) && !named(test, skip);
    for test in tests.iter().filter(listed) {
        writeln!(out, "{}", test.name)?;
    }
    Ok(())
}

/// Runs each of `tests` that `filters` ask for and that none of `skip`
/// names, in order, as a program named `name`. Reports each on `console`
/// as it runs: its name as it starts, then how it ended and how long it
/// took, with why it failed if it did, after what it wrote, if anything.
/// Then how many did what, and how long they took between them.
pub fn run(
    tests: &Tests,
    filters: &[String],
    skip: &[String],
    name: &str,
    console: &Console,
) -> Result<Summary, Error> {
    let runner = Runner::new(&tests.component, name)?;
    report(&tests.tests, filters, skip, console, |index| {
        let started = Instant::now();
        let failure = runner.run(index, console)?;
        Ok((failure, started.elapsed()))
    })
}

/// Runs each of `tests` that `filters` ask for and that none of `skip`
/// names by `run`, which is given its index among them all and gives how
/// long it took, and reports on `console` what [`run`] does.
fn report(
    tests: &[Test],
    filters: &[String],
    skip: &[String],
    console: &Console,
    run: impl Fn(usize) -> Result<(Option<Failure>, Duration), Error>,
) -> Result<Summary, Error> {
    let mut summary = Summary::default();
    for (index, test) in tests.iter().enumerate() {
        if !asked(test, filters) {
            summary.filtered += 1;
            continue;
        }
        if named(test, skip) {
            summary.skipped += 1;
            continue;
        }
        console.start(&test.name);
        // A test that couldn't be run is no test that failed: nothing more
        // is said of it here.
        let (failure, time) = run(index).inspect_err(|_| console.abandon())?;
        summary.time += time;
        match failure {
            None => {
                summary.passed += 1;
                console.end(&test.name, &verdict("ok", time));
            }
            Some(failure) => {
                summary.failed += 1;
                let failure = failure.to_string().replace('\n', "\n    ");
                let failed = verdict("FAILED", time);
                console.end(&test.name, &format!("{failed}\n    {failure}"));
            }
        }
    }
    console.line(&format!("\n{summary}"));
    Ok(summary)
}

#[cfg(test)]
mod tests {
    use duck_compiler::file::{FileId, FileManager, Settings, TestModule, Wit, WitFile};
    use duck_compiler::world::COMMAND;
    use wasmtime_wasi::p2::pipe::MemoryOutputPipe;

    use super::super::tests::PRELUDE;
    use super::*;

    /// The entry file of a program after [`PRELUDE`], which its tests are
    /// modules of: what a test changes, and what one checks by.
    const ENTRY: &str = r#"
var count = 0
let cells: varray(i32) = [0; 4]
let pages = module.size()

fn check(ok: bool):
    ok or module.unreachable()

fn main():
    count = 9
"#;

    /// An entry file and one test module, `checks`, of the package it is
    /// in.
    struct Package {
        entry: String,
        checks: String,
        settings: Settings,
    }

    impl FileManager for Package {
        fn entry_point(&mut self) -> FileId {
            Self::mint_file_id(0)
        }

        fn display_name(&mut self, id: FileId) -> String {
            match id == self.entry_point() {
                true => "main.duck".to_string(),
                false => "checks.duck".to_string(),
            }
        }

        fn contents(&mut self, id: FileId) -> String {
            match id == self.entry_point() {
                true => self.entry.clone(),
                false => self.checks.clone(),
            }
        }

        fn open(&mut self, _: FileId, path: &[&str]) -> Option<FileId> {
            (path == ["main"]).then(|| Self::mint_file_id(0))
        }

        fn open_package(&mut self, _: FileId, _: &str) -> Option<FileId> {
            None
        }

        fn tests(&mut self) -> Vec<TestModule> {
            vec![TestModule {
                file: Self::mint_file_id(1),
                path: vec!["checks".to_string()],
            }]
        }

        fn settings(&mut self) -> Settings {
            self.settings.clone()
        }
    }

    /// The tests of the program whose entry file is [`PRELUDE`] and then
    /// [`ENTRY`], and whose test module is `checks`.
    fn tests(checks: &str) -> Tests {
        let settings = Settings {
            start: Some("main".to_string()),
            world: Some(COMMAND.to_string()),
            ..Settings::default()
        };
        let mut files = Package {
            entry: format!("{PRELUDE}{ENTRY}"),
            checks: format!("use main\nuse main.check\n{checks}"),
            settings,
        };
        match duck_compiler::compile_tests(&mut files) {
            Ok(tests) => tests,
            Err(errors) => panic!("{errors:#?}"),
        }
    }

    /// What is written to one stream of a console, apart from what is
    /// there to read: only what is flushed is.
    #[derive(Clone, Default)]
    struct Shown(Arc<Mutex<(Vec<u8>, Vec<u8>)>>);

    impl Shown {
        /// What is there to read, which is text.
        fn text(&self) -> String {
            String::from_utf8(self.0.lock().unwrap().0.clone()).unwrap()
        }
    }

    impl Write for Shown {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.0.lock().unwrap().1.extend(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            let mut written = self.0.lock().unwrap();
            let kept = mem::take(&mut written.1);
            written.0.extend(kept);
            Ok(())
        }
    }

    /// A console that is no terminal, with what is there to read of its
    /// standard output and of its standard error.
    fn shown() -> (Console, Shown, Shown) {
        let (out, err) = (Shown::default(), Shown::default());
        let console = Console::new(out.clone(), err.clone(), [false; 2]);
        (console, out, err)
    }

    /// A console that nothing is read of.
    fn unread() -> Console {
        Console::new(io::sink(), io::sink(), [false; 2])
    }

    fn strings(strs: &[&str]) -> Vec<String> {
        strs.iter().map(|str| str.to_string()).collect()
    }

    /// Runs each test of `tests` that `filters` ask for and none of `skip`
    /// names, as [`run`] does, but that the test at an index takes as long
    /// as `times` has there, or no time. Returns how many did what, and
    /// what was written to the standard output and to the standard error.
    fn ran(
        tests: &Tests,
        filters: &[&str],
        skip: &[&str],
        times: &[Duration],
    ) -> (Summary, String, String) {
        let runner = Runner::new(&tests.component, "out.wasm").unwrap();
        let (console, out, err) = shown();
        let run = |index: usize| {
            let time = times.get(index).copied().unwrap_or_default();
            Ok((runner.run(index, &console)?, time))
        };
        let (filters, skip) = (strings(filters), strings(skip));
        let summary = report(&tests.tests, &filters, &skip, &console, run).unwrap();
        (summary, out.text(), err.text())
    }

    /// Why each test of `checks` fails, or `None`, by its name without its
    /// module's, running them in order.
    fn failures(checks: &str) -> Vec<(String, Option<Failure>)> {
        let tests = tests(checks);
        let runner = Runner::new(&tests.component, "out.wasm").unwrap();
        let run = |(index, test): (usize, &Test)| {
            let name = test.name.strip_prefix("checks.").unwrap().to_string();
            (name, runner.run(index, &unread()).unwrap())
        };
        tests.tests.iter().enumerate().map(run).collect()
    }

    /// A trap that said `message` in the functions `stack`, innermost first.
    fn trap(message: &str, stack: &[&str]) -> Option<Failure> {
        Some(Failure::Trap {
            message: message.to_string(),
            stack: stack.iter().map(|name| name.to_string()).collect(),
        })
    }

    #[test]
    fn a_test_passes_if_it_returns_and_fails_if_it_traps() {
        let checks = r#"
var zero = 0
let few: array(i32) = [1, 2]
var nothing = 0 as uint as! fn()

fn divide(by: i32) -> i32:
    return 1 / by

fn at(i: uint) -> i32:
    return few[i]

pub fn returns():
    check(divide(1) == 1)

pub fn is_unreachable():
    check(divide(1) == 2)

pub fn divides_by_zero():
    check(divide(zero) == 0)

pub fn reads_past_the_end():
    check(at(2) == 0)

pub fn reads_past_memory():
    let far: &i32 = 0xfffffff0
    check(far.* == 0)

pub fn calls_nothing():
    nothing()

pub fn is_yet_to_be_written():
    todo
"#;
        let unreachable = "wasm `unreachable` instruction executed";
        let expected = [
            ("returns", None),
            (
                "is_unreachable",
                trap(unreachable, &["check", "is_unreachable"]),
            ),
            (
                "divides_by_zero",
                trap("integer divide by zero", &["divide", "divides_by_zero"]),
            ),
            (
                "reads_past_the_end",
                trap(unreachable, &["at", "reads_past_the_end"]),
            ),
            (
                "reads_past_memory",
                trap("out of bounds memory access", &["reads_past_memory"]),
            ),
            (
                "calls_nothing",
                trap("uninitialized element", &["calls_nothing"]),
            ),
            (
                "is_yet_to_be_written",
                trap(unreachable, &["is_yet_to_be_written"]),
            ),
        ];
        let expected = expected.map(|(name, failure)| (name.to_string(), failure));
        assert_eq!(failures(checks), expected);
        // What failed is said as `duck run` says what stopped a program.
        assert_eq!(
            expected[2].1.as_ref().unwrap().to_string(),
            "the test trapped: integer divide by zero\n    in `divide`\n    in `divides_by_zero`"
        );
    }

    #[test]
    fn a_test_that_exits_fails() {
        // Whatever its status, as it didn't return.
        let checks = r#"
extern "wasi:cli/exit@0.3.0":
    fn exit_with_code(status: u8) -> never

pub fn exits():
    exit_with_code(0)

pub fn exits_with_a_status():
    exit_with_code(3)

pub fn returns():
    pass
"#;
        let expected = [
            ("exits", Some(Failure::Exit(0))),
            ("exits_with_a_status", Some(Failure::Exit(3))),
            ("returns", None),
        ];
        assert_eq!(
            failures(checks),
            expected.map(|(name, failure)| (name.to_string(), failure))
        );
        assert_eq!(
            Failure::Exit(3).to_string(),
            "the test exited with status 3: one passes by returning"
        );
    }

    #[test]
    fn each_test_starts_as_the_constants_left_the_program() {
        // Each checks that nothing is as another left it, and then leaves
        // all of it changed: a `var`, memory, and how much of it there is.
        let checks = r#"
var own = 1
let filled = main.cells[0] = 6

fn untouched():
    check(main.count == 0 and own == 1)
    check(main.cells[0] == 6 and main.cells[3] == 0)
    check(module.size() == main.pages)

fn touch():
    main.count += 5
    own += 1
    main.cells[0] = 1
    main.cells[3] = 7
    check(module.grow(2) == main.pages as int)
    let grown = (main.pages * module.page_size) as! &var i32
    grown.* = 3
    let held = main.cabi_realloc(0, 0, 4, 64)
    check(main.heap != 0 and held as uint != 0)

pub fn first():
    untouched()
    touch()

pub fn second():
    untouched()
    check(main.heap == 0)
    touch()

pub fn third():
    untouched()
"#;
        let tests = tests(checks);
        let runner = Runner::new(&tests.component, "out.wasm").unwrap();
        // In whichever order, and however many times.
        for index in [0, 1, 2, 1, 0, 0, 2] {
            let failure = runner.run(index, &unread()).unwrap();
            assert_eq!(failure, None, "{}", tests.tests[index].name);
        }
    }

    #[test]
    fn a_test_is_given_what_a_program_is() {
        let checks = r#"
extern "wasi:cli/environment@0.3.0":
    fn get_arguments() -> array(string)

let starting = "starting"

pub fn prints_its_name():
    main.print(starting)
    for argument in get_arguments():
        main.print(argument)

pub fn has_only_its_name():
    check(get_arguments().len == 1)
"#;
        let tests = tests(checks);
        let runner = Runner::new(&tests.component, "out.wasm").unwrap();
        let stdout = MemoryOutputPipe::new(1 << 16);
        for (index, test) in tests.tests.iter().enumerate() {
            let ctx = context(&runner.args)
                .unwrap()
                .stdout(stdout.clone())
                .build();
            assert_eq!(runner.run_with(index, ctx), Ok(None), "{}", test.name);
        }
        assert_eq!(stdout.contents(), "starting\nout.wasm\n");
    }

    #[test]
    fn the_tests_that_are_asked_for_run_in_order() {
        let checks = r#"
var zero = 0

pub fn adds():
    check(1 + 1 == 2)

pub fn divides():
    check(1 / zero == 0)

pub fn adds_again():
    check(main.count + 2 == 2)
"#;
        let tests = tests(checks);
        let times = [
            Duration::from_micros(999),
            Duration::from_millis(12),
            Duration::from_millis(2500),
        ];
        let (summary, out, err) = ran(&tests, &[], &[], &times);
        let all = Summary {
            passed: 2,
            failed: 1,
            skipped: 0,
            filtered: 0,
            time: times.iter().sum(),
        };
        assert_eq!(summary, all);
        // Each with how long it took, but for one that took no time worth
        // the saying, and then how long they all took.
        assert_eq!(
            out,
            "test checks.adds ... ok\n\
             test checks.divides ... FAILED (12 ms)\n    \
             the test trapped: integer divide by zero\n        \
             in `divides`\n\
             test checks.adds_again ... ok (2.5 s)\n\
             \n2 passed, 1 failed (2.5 s)\n"
        );
        assert_eq!(err, "");
        // A test whose name has any of them in it.
        let (summary, out, _) = ran(&tests, &["again", "s.adds"], &[], &times);
        assert_eq!((summary.passed, summary.filtered), (2, 1));
        assert_eq!(
            out,
            "test checks.adds ... ok\ntest checks.adds_again ... ok (2.5 s)\n\n\
             2 passed, 0 failed, 1 filtered out (2.5 s)\n"
        );
        let (summary, out, _) = ran(&tests, &["nothing"], &[], &times);
        assert_eq!(
            (summary.passed, summary.failed, summary.filtered),
            (0, 0, 3)
        );
        assert_eq!(out, "\n0 passed, 0 failed, 3 filtered out (0 ms)\n");

        // Their names alone, of which nothing is run.
        let listed = |filters: &[&str], skip: &[&str]| {
            let mut out = Vec::new();
            list(&tests.tests, &strings(filters), &strings(skip), &mut out).unwrap();
            String::from_utf8(out).unwrap()
        };
        assert_eq!(
            listed(&[], &[]),
            "checks.adds\nchecks.divides\nchecks.adds_again\n"
        );
        assert_eq!(listed(&["divide", "missing"], &[]), "checks.divides\n");
        assert_eq!(
            listed(&[], &["divide", "missing"]),
            "checks.adds\nchecks.adds_again\n"
        );
        assert_eq!(listed(&["adds"], &["again"]), "checks.adds\n");
        assert_eq!(listed(&["divides"], &["checks."]), "");
    }

    #[test]
    fn the_tests_that_are_to_be_skipped_are_left_out() {
        let checks = r#"
var zero = 0

pub fn adds():
    check(1 + 1 == 2)

pub fn divides():
    check(1 / zero == 0)

pub fn adds_again():
    check(main.count + 2 == 2)
"#;
        let tests = tests(checks);
        // A test whose name has any of them in it, which is not run.
        let (summary, out, _) = ran(&tests, &[], &["divide", "missing"], &[]);
        assert_eq!((summary.passed, summary.failed), (2, 0));
        assert_eq!((summary.skipped, summary.filtered), (1, 0));
        assert_eq!(
            out,
            "test checks.adds ... ok\ntest checks.adds_again ... ok\n\n\
             2 passed, 0 failed, 1 skipped (0 ms)\n"
        );
        // Whatever asks for it. One that nothing asks for is not counted
        // as skipped, whether or not it would be.
        let (summary, out, _) = ran(&tests, &["adds", "again"], &["again", "divides"], &[]);
        assert_eq!((summary.passed, summary.failed), (1, 0));
        assert_eq!((summary.skipped, summary.filtered), (1, 1));
        assert_eq!(
            out,
            "test checks.adds ... ok\n\n1 passed, 0 failed, 1 skipped, 1 filtered out (0 ms)\n"
        );
        let (summary, out, _) = ran(&tests, &[], &["checks."], &[]);
        assert_eq!((summary.passed, summary.skipped), (0, 3));
        assert_eq!(out, "\n0 passed, 0 failed, 3 skipped (0 ms)\n");
    }

    #[test]
    fn a_time_is_said_in_milliseconds_or_in_seconds() {
        let said = |micros: u64| elapsed(Duration::from_micros(micros));
        assert_eq!(said(0), "0 ms");
        assert_eq!(said(999), "0 ms");
        assert_eq!(said(1_000), "1 ms");
        assert_eq!(said(999_999), "999 ms");
        assert_eq!(said(1_000_000), "1.0 s");
        assert_eq!(said(61_260_000), "61.3 s");
        // A test that takes less than a millisecond is said to take none.
        let ended = |micros: u64| verdict("ok", Duration::from_micros(micros));
        assert_eq!(ended(999), "ok");
        assert_eq!(ended(1_000), "ok (1 ms)");
        assert_eq!(ended(3_400_000), "ok (3.4 s)");
    }

    /// A test that is only named.
    fn named_test(name: &str) -> Test {
        let span = duck_compiler::lex::Span {
            file: FileId::default(),
            start: 0,
            end: 0,
        };
        Test {
            name: name.to_string(),
            span,
        }
    }

    #[test]
    fn a_test_is_named_before_it_runs() {
        let tests = ["a.first", "a.second", "a.third"].map(named_test);
        let (console, out, _) = shown();
        // What is there to read as each test runs: every line before it,
        // whole, and its own name.
        let seen = Mutex::new(Vec::new());
        let run = |index: usize| {
            seen.lock().unwrap().push(out.text());
            let failure = (index == 1).then_some(Failure::Exit(2));
            Ok((failure, Duration::from_millis(index as u64)))
        };
        report(&tests, &[], &[], &console, run).unwrap();
        let first = "test a.first ... ok\n";
        let second = "test a.second ... FAILED (1 ms)\n    \
                      the test exited with status 2: one passes by returning\n";
        assert_eq!(
            seen.into_inner().unwrap(),
            [
                "test a.first ...".to_string(),
                format!("{first}test a.second ..."),
                format!("{first}{second}test a.third ..."),
            ]
        );
        let all =
            format!("{first}{second}test a.third ... ok (2 ms)\n\n2 passed, 1 failed (3 ms)\n");
        assert_eq!(out.text(), all);

        // A test that can't be run stops them, and leaves its line whole.
        let (console, out, _) = shown();
        let run = |index: usize| match index {
            0 => Ok((None, Duration::ZERO)),
            _ => Err(Error::Invalid("no such test".to_string())),
        };
        let stopped = report(&tests, &[], &[], &console, run);
        assert_eq!(stopped, Err(Error::Invalid("no such test".to_string())));
        assert_eq!(out.text(), "test a.first ... ok\ntest a.second ...\n");
    }

    /// What writes to the standard streams with no end of a line but the
    /// one it is given: `put` to the standard output, as `print` of the
    /// entry file does, and `eprint` to the standard error.
    const WRITERS: &str = r#"
extern "wasi:cli/exit@0.3.0":
    fn exit_with_code(status: u8) -> never

extern "wasi:cli/stderr@0.3.0":
    fn write_via_stream(data: i32) -> i32
    fn stream_new() -> i64 = "[stream-new-0]write-via-stream"
    fn stream_write(stream: i32, bytes: array(u8)) -> i32 = "[async-lower][stream-write-0]write-via-stream"
    fn stream_drop(stream: i32) = "[stream-drop-writable-0]write-via-stream"
    fn future_read(future: i32, ret: &var result(tuple(), u8)) -> i32 = "[async-lower][future-read-1]write-via-stream"
    fn future_drop(future: i32) = "[future-drop-readable-1]write-via-stream"

fn put(text: array(u8)):
    let ends = main.stream_new()
    let stream = (ends >> 32) as i32
    let future = main.write_via_stream(ends as i32)
    main.send(stream, text)
    main.stream_drop(stream)
    let _ = main.settle(future, main.future_read(future, main.written))
    main.future_drop(future)

fn eprint(text: array(u8)):
    let ends = stream_new()
    let stream = (ends >> 32) as i32
    let future = write_via_stream(ends as i32)
    var rest = text
    while rest.len > 0:
        let code = main.settle(stream, stream_write(stream, rest))
        let count = (code as u32 >> 4) as uint
        rest = array(u8)(ptr: (rest.ptr as uint + count) as! &u8, len: rest.len - count)
        if code & 15 != 0:
            break
    stream_drop(stream)
    let _ = main.settle(future, future_read(future, main.written))
    future_drop(future)
"#;

    #[test]
    fn what_a_test_writes_is_between_the_lines_that_name_it() {
        let checks = r#"
pub fn writes_nothing():
    pass

pub fn writes_a_line():
    put("a line\n")

pub fn leaves_a_line_unended():
    put("two\nlines")

pub fn writes_to_its_error():
    eprint("an error\n")
    eprint("unended")

pub fn writes_to_both():
    put("out 1\n")
    eprint("err 1\n")
    put("out 2")
    eprint("err 2")

pub fn writes_and_traps():
    put("before the trap")
    module.unreachable()

pub fn writes_and_exits():
    eprint("before the exit\n")
    exit_with_code(3)
"#;
        let tests = tests(&format!("{WRITERS}{checks}"));
        let times = [Duration::ZERO, Duration::from_millis(4)];
        let (summary, out, err) = ran(&tests, &[], &[], &times);
        assert_eq!((summary.passed, summary.failed), (5, 2));
        // Its first byte ends the line that names it, on whichever stream
        // it is, and how it ended is on a line that names it again: after
        // the end of a line that it left without one.
        assert_eq!(
            out,
            "test checks.writes_nothing ... ok\n\
             test checks.writes_a_line ...\n\
             a line\n\
             test checks.writes_a_line ... ok (4 ms)\n\
             test checks.leaves_a_line_unended ...\n\
             two\nlines\n\
             test checks.leaves_a_line_unended ... ok\n\
             test checks.writes_to_its_error ...\n\
             test checks.writes_to_its_error ... ok\n\
             test checks.writes_to_both ...\n\
             out 1\nout 2\n\
             test checks.writes_to_both ... ok\n\
             test checks.writes_and_traps ...\n\
             before the trap\n\
             test checks.writes_and_traps ... FAILED\n    \
             the test trapped: wasm `unreachable` instruction executed\n        \
             in `writes_and_traps`\n\
             test checks.writes_and_exits ...\n\
             test checks.writes_and_exits ... FAILED\n    \
             the test exited with status 3: one passes by returning\n\
             \n5 passed, 2 failed (4 ms)\n"
        );
        // Every line of the standard error is a whole one too.
        assert_eq!(err, "an error\nunended\nerr 1\nerr 2\nbefore the exit\n");

        // Where the two are one, as on a terminal, each thing is where it
        // was written among the others. Each stream's line is given its
        // end, so one that both left without has two.
        let runner = Runner::new(&tests.component, "out.wasm").unwrap();
        let both = Shown::default();
        let console = Console::new(both.clone(), both.clone(), [false; 2]);
        let run = |index: usize| Ok((runner.run(index, &console)?, Duration::ZERO));
        let asked = strings(&["both", "error"]);
        report(&tests.tests, &asked, &[], &console, run).unwrap();
        assert_eq!(
            both.text(),
            "test checks.writes_to_its_error ...\n\
             an error\nunended\n\
             test checks.writes_to_its_error ... ok\n\
             test checks.writes_to_both ...\n\
             out 1\nerr 1\nout 2err 2\n\n\
             test checks.writes_to_both ... ok\n\
             \n2 passed, 0 failed, 5 filtered out (0 ms)\n"
        );
    }

    #[test]
    fn a_test_is_told_whether_its_streams_are_terminals() {
        let terminal = |terminals: [bool; 2], stream: Stream| {
            let console = Console::new(io::sink(), io::sink(), terminals);
            console.stream(stream).is_terminal()
        };
        assert!(terminal([true, false], Stream::Out));
        assert!(!terminal([true, false], Stream::Err));
        assert!(terminal([false, true], Stream::Err));
    }

    #[test]
    fn the_overview_tests_as_it_says() {
        let (_, section) = crate::agents::OVERVIEW.split_once("\n## Tests\n").unwrap();
        let (_, example) = section.split_once("\n```duck\n").unwrap();
        let (example, _) = example.split_once("\n```").unwrap();
        // A library that has nothing but its tests.
        let mut files = Package {
            entry: String::new(),
            checks: example.to_string(),
            settings: Settings::default(),
        };
        let tests = duck_compiler::compile_tests(&mut files).unwrap();
        let (summary, out, _) = ran(&tests, &[], &[], &[]);
        assert_eq!(
            out,
            "test checks.counts_from_one ... ok\n\
             test checks.starts_again ... ok\n\
             test checks.holds_what_it_stores ... ok\n\
             \n3 passed, 0 failed (0 ms)\n"
        );
        assert_eq!(summary.failed, 0);
    }

    #[test]
    fn tests_run_with_what_wasi_has_only() {
        let wit = "package my:pkg;\ninterface host {\n  log: func(n: s32);\n}\n\
                   world app {\n  import host;\n}\n";
        let settings = Settings {
            world: Some("app".to_string()),
            wit: Wit {
                package: vec![WitFile {
                    path: "wit/app.wit".to_string(),
                    contents: wit.to_string(),
                }],
                deps: Vec::new(),
            },
            ..Settings::default()
        };
        let mut files = Package {
            entry: "extern \"my:pkg/host\":\n    pub fn log(n: i32)\n".to_string(),
            checks: "use main\npub fn logs():\n    main.log(1)\n".to_string(),
            settings,
        };
        let tests = duck_compiler::compile_tests(&mut files).unwrap();
        let error = Runner::new(&tests.component, "out.wasm").err().unwrap();
        let error = error.to_string();
        assert!(error.starts_with("cannot run the component"), "{error}");
        assert!(error.contains("my:pkg/host"), "{error}");
    }
}
