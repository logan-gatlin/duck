//! What draws, which `duck run` gives a program beside WASI 0.3:
//! `wasi:webgpu`, and the surface and the frame buffer of `wasi-gfx`, as
//! `wasi-gfx-runtime` implements them over wgpu, winit and softbuffer: the
//! copy of it that this repository has, in `wasi-gfx-runtime`.
//!
//! A surface is a window, and the event loop of windows takes the thread it
//! runs on, which is to be the first of the process, until the process
//! ends. A program takes its thread until it ends too. So a program that
//! has a surface runs on a thread of its own, and the event loop on the
//! one `duck run` starts on: what happens to a window reaches the program
//! through the streams of its surface. One without a surface runs where it
//! starts, as any does, whether or not it computes on a GPU.

use std::panic::{self, AssertUnwindSafe};
use std::sync::{Arc, OnceLock};
use std::thread;

use frame_buffer_wasmtime::{FrameBufferCtx, FrameBufferCtxView};
use surface_wasmtime::winit::{WasiWinitEventLoopProxy, create_wasi_winit_event_loop};
use surface_wasmtime::{
    MainThreadSpawner, SurfaceCtx, SurfaceCtxView, SurfaceFrameBufferCtx,
    SurfaceFrameBufferCtxView, SurfaceWebgpuCtx, SurfaceWebgpuCtxView,
};
use wasi_webgpu_wasmtime::{WasiWebGpuCtx, WasiWebGpuCtxView, WasiWebGpuOptions};
use wasmtime::component::{Component, Linker};
use wasmtime::{Engine, Store};
use wasmtime_wasi::WasiCtx;
use wgpu_core::global::Global;

use super::{Error, Host};

/// What starts the name of each interface of a surface, which is what
/// opens a window.
const SURFACE: &str = "wasi-gfx:surface/";

/// The status of a program that the host stopped by a fault of its own,
/// as Rust gives one that panics.
const FAULT: u8 = 101;

/// Why a function of a surface has the event loop to ask.
const WINDOWED: &str = "a program that imports a surface is run with an event loop";

/// What the host functions that draw keep for one program.
#[derive(Default)]
pub(super) struct Gfx {
    /// Every adapter and device of the program, made when it first asks
    /// for one: finding the GPUs of the machine is no work of a program
    /// that draws nothing.
    gpu: OnceLock<Arc<Global>>,
    options: WasiWebGpuOptions,
    /// The event loop of the windows, which the thread that `duck run`
    /// starts on runs. `None` for a program without a surface.
    main_thread: Option<Arc<WasiWinitEventLoopProxy>>,
}

impl Gfx {
    /// Every adapter and device of the program.
    fn gpu(&self) -> &Arc<Global> {
        self.gpu.get_or_init(|| {
            let descriptor = wgpu_types::InstanceDescriptor {
                backends: wgpu_types::Backends::all(),
                flags: wgpu_types::InstanceFlags::from_build_config(),
                backend_options: Default::default(),
                memory_budget_thresholds: Default::default(),
                display: None,
            };
            Arc::new(Global::new("webgpu", descriptor, None))
        })
    }

    /// The event loop of the windows.
    fn main_thread(&self) -> &WasiWinitEventLoopProxy {
        self.main_thread.as_deref().expect(WINDOWED)
    }
}

impl WasiWebGpuCtxView for Host {
    fn webgpu_ctx(&mut self) -> WasiWebGpuCtx<'_> {
        WasiWebGpuCtx {
            instance: self.gfx.gpu(),
            table: &mut self.table,
            options: &self.gfx.options,
        }
    }
}

impl FrameBufferCtxView for Host {
    fn frame_buffer_ctx(&mut self) -> FrameBufferCtx<'_> {
        FrameBufferCtx {
            table: &mut self.table,
        }
    }
}

impl SurfaceCtxView for Host {
    type Spawner = WasiWinitEventLoopProxy;

    fn surface_ctx(&mut self) -> SurfaceCtx<'_, WasiWinitEventLoopProxy> {
        SurfaceCtx {
            table: &mut self.table,
            main_thread_spawner: self.gfx.main_thread(),
        }
    }
}

impl SurfaceWebgpuCtxView for Host {
    type Spawner = WasiWinitEventLoopProxy;

    fn surface_webgpu_ctx(&mut self) -> SurfaceWebgpuCtx<'_, WasiWinitEventLoopProxy> {
        SurfaceWebgpuCtx {
            table: &mut self.table,
            instance: self.gfx.gpu(),
            main_thread_spawner: self.gfx.main_thread(),
        }
    }
}

impl SurfaceFrameBufferCtxView for Host {
    type Spawner = WasiWinitEventLoopProxy;

    fn surface_frame_buffer_ctx(&mut self) -> SurfaceFrameBufferCtx<'_, WasiWinitEventLoopProxy> {
        SurfaceFrameBufferCtx {
            table: &mut self.table,
            instance: self.gfx.gpu(),
            main_thread_spawner: self.gfx.main_thread(),
        }
    }
}

/// Gives `linker` what draws.
pub(super) fn add_to_linker(linker: &mut Linker<Host>) -> wasmtime::Result<()> {
    wasi_webgpu_wasmtime::add_to_linker(linker)?;
    frame_buffer_wasmtime::add_to_linker(linker)?;
    surface_wasmtime::add_all_to_linker(linker)
}

/// Whether `component` imports a surface, and so may open a window.
pub(super) fn opens_windows(component: &Component, engine: &Engine) -> bool {
    let ty = component.component_type();
    ty.imports(engine)
        .any(|(name, _)| name.starts_with(SURFACE))
}

/// Runs `component`, which may open a window, on a thread of its own, and
/// the event loop of windows on this one, which is to be the first of the
/// process. Nothing stops that loop but the end of the process, so this
/// returns only where there is no loop to run: the process exits with the
/// status of the program when it ends, saying why if it stopped short. A
/// window that is asked to close ends the streams of its surface, for the
/// program to end by, and the loop exits with 1 where it is asked again.
///
/// What the program still holds as it ends is left to the system, which
/// takes it all back: the window of a texture that is still to be shown is
/// no window to close first.
pub(super) fn run_windowed(
    engine: Engine,
    component: Component,
    linker: Linker<Host>,
    ctx: WasiCtx,
) -> Result<u8, Error> {
    if !has_display() {
        return Err(Error::NoDisplay);
    }
    let (event_loop, main_thread) = create_wasi_winit_event_loop();
    let main_thread = Arc::new(main_thread);
    let gfx = Gfx {
        main_thread: Some(Arc::clone(&main_thread)),
        ..Gfx::default()
    };
    let host = Host::new(ctx, gfx);
    thread::spawn(move || {
        let mut store = Store::new(&engine, host);
        // Whatever stops the program ends the process, as nothing else
        // ends the loop: a panic of the host has said what it is.
        let run = AssertUnwindSafe(|| super::start(&mut store, &component, &linker));
        let status = match panic::catch_unwind(run) {
            Ok(Ok(status)) => status,
            Ok(Err(e)) => {
                eprintln!("error: {e}");
                1
            }
            Err(_) => FAULT,
        };
        exit_from(&main_thread, status)
    });
    event_loop.run();
    Ok(0)
}

/// Ends the process with `status`, from the thread of the event loop that
/// `main_thread` reaches. Ending it takes down what the loop has of the
/// display, which the loop would be reading on its own thread if another
/// ended it: that thread is to be the one that does.
fn exit_from(main_thread: &WasiWinitEventLoopProxy, status: u8) -> ! {
    let exit = main_thread.spawn(move || std::process::exit(status.into()));
    // The loop never answers, as the process ends where it would.
    wasmtime_wasi::runtime::in_tokio(exit)
}

/// Whether there is a display to open a window on, as far as the
/// environment says: winit stops the process where there is none.
fn has_display() -> bool {
    let named = |name: &str| std::env::var_os(name).is_some_and(|display| !display.is_empty());
    let asks = cfg!(all(
        unix,
        not(any(
            target_os = "macos",
            target_os = "ios",
            target_os = "android"
        ))
    ));
    !asks || named("WAYLAND_DISPLAY") || named("DISPLAY")
}
