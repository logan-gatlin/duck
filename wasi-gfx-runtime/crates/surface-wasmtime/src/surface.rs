use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
use shared::channel_to_stream;
use std::{fmt::Debug, future::Future, marker::PhantomData, pin::Pin, sync::Arc};
use wasi_gfx::surface::surface;
pub use wasi_gfx::surface::surface::{
    FrameEvent, Key, KeyEvent, PointerEvent, {CreateDesc as SurfaceDesc, ResizeEvent},
};
use wasmtime::component::{Access, HasData, Resource, StreamReader};

wasmtime::component::bindgen!({
    world: "wasi-gfx:surface/imports",
    require_store_data_send: true,
    imports: {
        "wasi-gfx:surface/surface.[method]surface.on-pointer-down": store | trappable,
        "wasi-gfx:surface/surface.[method]surface.on-pointer-move": store | trappable,
        "wasi-gfx:surface/surface.[method]surface.on-key-up": store | trappable,
        "wasi-gfx:surface/surface.[method]surface.on-pointer-up": store | trappable,
        "wasi-gfx:surface/surface.[method]surface.on-key-down": store | trappable,
        "wasi-gfx:surface/surface.[method]surface.on-resize": store | trappable,
        "wasi-gfx:surface/surface.[method]surface.on-frame": store | trappable,
        default: trappable,
    },
    with: {
        "wasi-gfx:surface/surface.surface": Surface,
    },
});

// types

/// Any type implementing GfxWindow can be used to back a wasi-gfx:surface
pub trait GfxWindow: HasDisplayHandle + HasWindowHandle {
    fn height(&self) -> u32;
    fn width(&self) -> u32;
    fn request_set_size(&self, width: Option<u32>, height: Option<u32>);
}

#[derive(Clone, Debug)]
pub struct Surface(Arc<SurfaceInner>);

impl Surface {
    pub fn new(window: Box<dyn GfxWindow + Send + Sync + 'static>) -> Self {
        let (mut pointer_up_sender, pointer_up_receiver) = async_broadcast::broadcast(5);
        let pointer_up_receiver = pointer_up_receiver.deactivate();
        pointer_up_sender.set_overflow(true);
        let (mut pointer_down_sender, pointer_down_receiver) = async_broadcast::broadcast(5);
        let pointer_down_receiver = pointer_down_receiver.deactivate();
        pointer_down_sender.set_overflow(true);
        let (mut pointer_move_sender, pointer_move_receiver) = async_broadcast::broadcast(1);
        let pointer_move_receiver = pointer_move_receiver.deactivate();
        pointer_move_sender.set_overflow(true);
        let (mut key_up_sender, key_up_receiver) = async_broadcast::broadcast(5);
        let key_up_receiver = key_up_receiver.deactivate();
        key_up_sender.set_overflow(true);
        let (mut key_down_sender, key_down_receiver) = async_broadcast::broadcast(5);
        let key_down_receiver = key_down_receiver.deactivate();
        key_down_sender.set_overflow(true);
        let (mut resize_sender, resize_receiver) = async_broadcast::broadcast(5);
        let resize_receiver = resize_receiver.deactivate();
        resize_sender.set_overflow(true);
        let (mut frame_sender, frame_receiver) = async_broadcast::broadcast(1);
        let frame_receiver = frame_receiver.deactivate();
        frame_sender.set_overflow(true);
        Surface(Arc::new(SurfaceInner {
            window,
            pointer_up_sender,
            _pointer_up_receiver: pointer_up_receiver,
            pointer_down_sender,
            _pointer_down_receiver: pointer_down_receiver,
            pointer_move_sender,
            _pointer_move_receiver: pointer_move_receiver,
            key_up_sender,
            _key_up_receiver: key_up_receiver,
            key_down_sender,
            _key_down_receiver: key_down_receiver,
            resize_sender,
            _resize_receiver: resize_receiver,
            frame_sender,
            _frame_receiver: frame_receiver,
        }))
    }

    pub fn height(&self) -> u32 {
        self.0.window.height()
    }

    pub fn width(&self) -> u32 {
        self.0.window.width()
    }

    /// Asks the window to be `width` by `height`. A window that takes the
    /// size at once says nothing of it, as it asked for none: the resize is
    /// said here, so that every change of size is an event.
    pub fn request_set_size(&self, width: Option<u32>, height: Option<u32>) {
        let before = (self.width(), self.height());
        self.0.window.request_set_size(width, height);
        let (width, height) = (self.width(), self.height());
        if (width, height) != before {
            self.canvas_resize(ResizeEvent { height, width });
        }
    }

    /// Ends every stream of the surface, as its window is asked to close:
    /// what was sent is still read, and then each stream is done. Returns
    /// whether this is what ended them, which they are only once.
    pub fn close(&self) -> bool {
        let inner = &self.0;
        // Each is closed, whichever is first.
        let closed = [
            inner.pointer_up_sender.close(),
            inner.pointer_down_sender.close(),
            inner.pointer_move_sender.close(),
            inner.key_up_sender.close(),
            inner.key_down_sender.close(),
            inner.resize_sender.close(),
            inner.frame_sender.close(),
        ];
        closed.contains(&true)
    }

    /// clone the Arc reference. i.e shallow clone
    pub fn arc_clone(&self) -> Self {
        Surface(Arc::clone(&self.0))
    }

    pub fn pointer_up(&self, event: PointerEvent) {
        shared::unwrap_unless_inactive(self.0.pointer_up_sender.try_broadcast(event));
    }
    pub fn pointer_down(&self, event: PointerEvent) {
        shared::unwrap_unless_inactive(self.0.pointer_down_sender.try_broadcast(event));
    }
    pub fn pointer_move(&self, event: PointerEvent) {
        shared::unwrap_unless_inactive_or_full(self.0.pointer_move_sender.try_broadcast(event));
    }
    pub fn key_up(&self, event: KeyEvent) {
        shared::unwrap_unless_inactive(self.0.key_up_sender.try_broadcast(event));
    }
    pub fn key_down(&self, event: KeyEvent) {
        shared::unwrap_unless_inactive(self.0.key_down_sender.try_broadcast(event));
    }
    pub fn canvas_resize(&self, event: ResizeEvent) {
        shared::unwrap_unless_inactive(self.0.resize_sender.try_broadcast(event));
    }
    pub fn animation_frame(&self) {
        shared::unwrap_unless_inactive_or_full(
            self.0
                .frame_sender
                .try_broadcast(FrameEvent { nothing: true }),
        );
    }
}

impl HasDisplayHandle for Surface {
    fn display_handle(
        &self,
    ) -> Result<raw_window_handle::DisplayHandle<'_>, raw_window_handle::HandleError> {
        self.0.window.display_handle()
    }
}
impl HasWindowHandle for Surface {
    fn window_handle(
        &self,
    ) -> Result<raw_window_handle::WindowHandle<'_>, raw_window_handle::HandleError> {
        self.0.window.window_handle()
    }
}

struct SurfaceInner {
    pub window: Box<dyn GfxWindow + Send + Sync + 'static>,

    // Keeping inactive receivers to keep channels open.
    // See https://docs.rs/async-broadcast/0.7.1/async_broadcast/struct.InactiveReceiver.html
    pointer_up_sender: async_broadcast::Sender<PointerEvent>,
    _pointer_up_receiver: async_broadcast::InactiveReceiver<PointerEvent>,
    pointer_down_sender: async_broadcast::Sender<PointerEvent>,
    _pointer_down_receiver: async_broadcast::InactiveReceiver<PointerEvent>,
    pointer_move_sender: async_broadcast::Sender<PointerEvent>,
    _pointer_move_receiver: async_broadcast::InactiveReceiver<PointerEvent>,
    key_up_sender: async_broadcast::Sender<KeyEvent>,
    _key_up_receiver: async_broadcast::InactiveReceiver<KeyEvent>,
    key_down_sender: async_broadcast::Sender<KeyEvent>,
    _key_down_receiver: async_broadcast::InactiveReceiver<KeyEvent>,
    resize_sender: async_broadcast::Sender<ResizeEvent>,
    _resize_receiver: async_broadcast::InactiveReceiver<ResizeEvent>,
    frame_sender: async_broadcast::Sender<FrameEvent>,
    _frame_receiver: async_broadcast::InactiveReceiver<FrameEvent>,
}

impl Debug for SurfaceInner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Surface")
            .field("window", &"<Boxed window>")
            .field("pointer_up_sender", &self.pointer_up_sender)
            .field("_pointer_up_receiver", &self._pointer_up_receiver)
            .field("pointer_down_sender", &self.pointer_down_sender)
            .field("_pointer_down_receiver", &self._pointer_down_receiver)
            .field("pointer_move_sender", &self.pointer_move_sender)
            .field("_pointer_move_receiver", &self._pointer_move_receiver)
            .field("key_up_sender", &self.key_up_sender)
            .field("_key_up_receiver", &self._key_up_receiver)
            .field("key_down_sender", &self.key_down_sender)
            .field("_key_down_receiver", &self._key_down_receiver)
            .field("resize_sender", &self.resize_sender)
            .field("_resize_receiver", &self._resize_receiver)
            .field("frame_sender", &self.frame_sender)
            .field("_frame_receiver", &self._frame_receiver)
            .finish()
    }
}

// linker connection
pub fn add_to_linker<T>(l: &mut wasmtime::component::Linker<T>) -> wasmtime::Result<()>
where
    T: SurfaceCtxView,
{
    wasi_gfx::surface::surface::add_to_linker::<_, HasSurfaceCtx<T::Spawner>>(l, T::surface_ctx)?;
    Ok(())
}

pub trait SurfaceCtxView: Send {
    /// Spawner used to run main-thread-only windowing operations.
    type Spawner: MainThreadSpawner;
    /// returns a struct of references.
    /// Returning all references in a struct allows us to use multiple mutable references at the same time.
    fn surface_ctx(&mut self) -> SurfaceCtx<'_, Self::Spawner>;
}

pub struct SurfaceCtx<'a, S: MainThreadSpawner> {
    pub table: &'a mut wasmtime_wasi::ResourceTable,
    pub main_thread_spawner: &'a S,
}

struct HasSurfaceCtx<S>(PhantomData<S>);

impl<S: MainThreadSpawner> HasData for HasSurfaceCtx<S> {
    type Data<'a> = SurfaceCtx<'a, S>;
}

/// Runs main-thread-only operations, as required by some operating systems
/// (e.g. macOS). On platforms without that requirement the implementation may run them in place.
pub trait MainThreadSpawner: Send + Sync + 'static {
    /// Run an arbitrary closure on the main thread and resolve to its result.
    fn spawn<F, T>(&self, f: F) -> impl Future<Output = T>
    where
        F: FnOnce() -> T + Send + 'static,
        T: Send + 'static;

    /// Create a surface (window) on the main thread.
    fn create_surface(&self, desc: SurfaceDesc) -> Pin<Box<dyn Future<Output = Surface> + Send>>;
}

// wasmtime trait impls
impl<'a, S: MainThreadSpawner> surface::Host for SurfaceCtx<'a, S> {}

impl<'a, S: MainThreadSpawner> surface::HostSurface for SurfaceCtx<'a, S> {
    fn new(&mut self, desc: SurfaceDesc) -> wasmtime::Result<Resource<Surface>> {
        let surface = futures::executor::block_on(self.main_thread_spawner.create_surface(desc));
        Ok(self.table.push(surface)?)
    }

    fn height(&mut self, surface: Resource<Surface>) -> wasmtime::Result<u32> {
        let surface = self.table.get(&surface)?;
        Ok(surface.height())
    }

    fn width(&mut self, surface: Resource<Surface>) -> wasmtime::Result<u32> {
        let surface = self.table.get(&surface)?;
        Ok(surface.width())
    }

    // The WIT has the height first.
    fn request_set_size(
        &mut self,
        surface: Resource<Surface>,
        height: Option<u32>,
        width: Option<u32>,
    ) -> wasmtime::Result<()> {
        let surface = self.table.get(&surface)?;
        surface.request_set_size(width, height);
        Ok(())
    }

    fn drop(&mut self, surface: Resource<Surface>) -> wasmtime::Result<()> {
        self.table.delete(surface)?;
        Ok(())
    }
}

impl<T, S: MainThreadSpawner> surface::HostSurfaceWithStore<T> for HasSurfaceCtx<S> {
    fn on_pointer_down(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<PointerEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.pointer_down_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }

    fn on_pointer_move(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<PointerEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.pointer_move_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }

    fn on_pointer_up(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<PointerEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.pointer_up_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }

    fn on_key_up(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<KeyEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.key_up_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }

    fn on_key_down(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<KeyEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.key_down_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }

    fn on_resize(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<ResizeEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.resize_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }

    fn on_frame(
        mut access: Access<T, Self>,
        surface: Resource<surface::Surface>,
    ) -> wasmtime::Result<StreamReader<FrameEvent>> {
        let ctx = access.get();
        let surface = ctx.table.get(&surface)?;
        let receiver = surface.0.frame_sender.new_receiver();
        Ok(channel_to_stream(access, receiver))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::{executor::block_on, StreamExt};
    use raw_window_handle::{DisplayHandle, HandleError, WindowHandle};
    use std::sync::Mutex;

    /// A window that is only a size, which it takes at once when asked.
    struct Sized(Mutex<(u32, u32)>);

    impl HasDisplayHandle for Sized {
        fn display_handle(&self) -> Result<DisplayHandle<'_>, HandleError> {
            Err(HandleError::Unavailable)
        }
    }

    impl HasWindowHandle for Sized {
        fn window_handle(&self) -> Result<WindowHandle<'_>, HandleError> {
            Err(HandleError::Unavailable)
        }
    }

    impl GfxWindow for Sized {
        fn height(&self) -> u32 {
            self.0.lock().unwrap().1
        }

        fn width(&self) -> u32 {
            self.0.lock().unwrap().0
        }

        fn request_set_size(&self, width: Option<u32>, height: Option<u32>) {
            let mut size = self.0.lock().unwrap();
            *size = (width.unwrap_or(size.0), height.unwrap_or(size.1));
        }
    }

    fn surface(width: u32, height: u32) -> Surface {
        Surface::new(Box::new(Sized(Mutex::new((width, height)))))
    }

    #[test]
    fn a_size_that_is_taken_at_once_is_a_resize() {
        let surface = surface(10, 20);
        let mut resizes = surface.0.resize_sender.new_receiver();

        surface.request_set_size(Some(30), None);
        let event = block_on(resizes.next()).unwrap();
        assert_eq!((event.width, event.height), (30, 20));

        // A size that the window already has changes nothing.
        surface.request_set_size(Some(30), Some(20));
        assert!(resizes.try_recv().is_err());
    }

    #[test]
    fn closing_ends_every_stream_once() {
        let surface = surface(10, 20);
        let mut frames = surface.0.frame_sender.new_receiver();
        let mut moves = surface.0.pointer_move_sender.new_receiver();
        surface.animation_frame();

        assert!(surface.close());
        assert!(!surface.close());

        // Nothing more is sent, and sending is no fault.
        surface.animation_frame();
        surface.pointer_up(PointerEvent { x: 0.0, y: 0.0 });
        surface.canvas_resize(ResizeEvent {
            height: 1,
            width: 1,
        });

        // What was sent before is still read, and then the stream is done.
        assert!(block_on(frames.next()).is_some());
        assert!(block_on(frames.next()).is_none());
        assert!(block_on(moves.next()).is_none());

        // A stream that is asked for afterwards is done from the start.
        let mut late = surface.0.key_down_sender.new_receiver();
        assert!(block_on(late.next()).is_none());
    }
}
