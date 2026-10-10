// Wrappers around `wgpu_*` types
// Every type here should have an explanation as to why we can't use the type directly.

use std::{
    collections::HashMap,
    fmt,
    sync::{Arc, Mutex, Weak},
    task::{Context, Poll, Waker},
};

use crate::wasi::webgpu::webgpu;

pub struct WgslLanguageFeatures;
impl WgslLanguageFeatures {
    pub fn new() -> Self {
        Self
    }
    pub fn has(&self, feature: &str) -> bool {
        use wgpu_core::naga::front::wgsl::LanguageExtension;
        matches!(
            LanguageExtension::from_ident(feature),
            Some(LanguageExtension::Implemented(_))
        )
    }
}

// can't pass generics to `wasmtime::component::bindgen`
// TODO: these should be unit-structs instead of `types` so that the internals are private to the crate
pub type RecordGpuPipelineConstantValue = HashMap<String, webgpu::GpuPipelineConstantValue>;
pub type RecordOptionGpuSize64 = HashMap<String, Option<webgpu::GpuSize64>>;

// label needed in `label` and `set-label`: wgpu takes a label as it makes a resource, and gives none back.
// can't pass generics to `wasmtime::component::bindgen`
pub type BindGroup = Labeled<wgpu_core::id::BindGroupId>;
pub type BindGroupLayout = Labeled<wgpu_core::id::BindGroupLayoutId>;
pub type CommandBuffer = Labeled<wgpu_core::id::CommandBufferId>;
pub type PipelineLayout = Labeled<wgpu_core::id::PipelineLayoutId>;
pub type RenderBundle = Labeled<wgpu_core::id::RenderBundleId>;
pub type Sampler = Labeled<wgpu_core::id::SamplerId>;
pub type TextureView = Labeled<wgpu_core::id::TextureViewId>;

pub struct Labeled<T> {
    pub(crate) id: T,
    pub(crate) label: String,
}

// error_handler needed for the errors that wgpu gives of a pass as it is encoded, which are those of a pass that has ended.
// label needed in `label` and `set-label`.
// A pass is kept until its resource is dropped: wgpu takes what it holds of the command encoder as the pass ends, and says of every later call that it has.
pub struct RenderPassEncoder {
    pub(crate) pass: wgpu_core::command::RenderPass,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}
pub struct ComputePassEncoder {
    pub(crate) pass: wgpu_core::command::ComputePass,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}

// encoder is None once `finish` has taken it: a render bundle is made of the encoder itself.
// device needed while there is an encoder: wgpu finishes it through the device, which it is to know by then.
pub struct RenderBundleEncoder {
    pub(crate) encoder: Option<wgpu_core::command::RenderBundleEncoder>,
    pub(crate) device: Arc<RegisteredDevice>,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}
impl RenderBundleEncoder {
    /// The encoder, or none once it is finished, which is an error of validation.
    /// https://www.w3.org/TR/webgpu/#abstract-opdef-validate-the-encoder-state
    pub(crate) fn encoder(&mut self) -> Option<&mut wgpu_core::command::RenderBundleEncoder> {
        if self.encoder.is_none() {
            self.error_handler
                .handle_possible_error(Some(ValidationError(
                    "The render bundle encoder is finished".to_string(),
                )));
        }
        self.encoder.as_mut()
    }
}

// size needed in `GpuBuffer.size`, `RenderPass.set_index_buffer`, `RenderPass.set_vertex_buffer`.
// usage needed in `GpuBuffer.usage`
// map_mode needed in `GpuBuffer.get_mapped_range_set_with_copy`: what is mapped to be read is not written.
// device needed in `GpuBuffer.map_async`, which polls it, and queue for what was written to the buffer to be in it by then. The queue is not kept from being dropped.
// label needed in `label` and `set-label`.
pub struct Buffer {
    pub(crate) buffer_id: wgpu_core::id::BufferId,
    pub(crate) size: u64,
    pub(crate) usage: wgpu_types::BufferUsages,
    pub(crate) map_state: webgpu::GpuBufferMapState,
    pub(crate) map_mode: wgpu_core::device::HostMap,
    pub(crate) device: Arc<RegisteredDevice>,
    pub(crate) queue: Weak<wgpu_core::id::QueueId>,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}

// references to queue and adapter are also saved in device.
// TODO: these should be unit-structs instead of `types` so that the internals are private to the crate
pub type Adapter = Arc<wgpu_core::id::AdapterId>;

// device needed in `GpuQueue.on_submitted_work_done`, which polls it.
// error_handler needed for the errors of `GpuQueue.submit` and of what the queue writes.
// label is that of every resource of the one queue.
pub struct Queue {
    pub(crate) queue_id: Arc<wgpu_core::id::QueueId>,
    pub(crate) device: Arc<RegisteredDevice>,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: Arc<Mutex<String>>,
}

// Keeps a device known to wgpu, which panics on the id of one that it has forgotten, until everything that reaches wgpu through the id is dropped:
// the device, its queue and its buffers poll it, and a render bundle encoder is finished through it.
pub(crate) struct RegisteredDevice {
    pub(crate) id: wgpu_core::id::DeviceId,
    pub(crate) instance: Arc<wgpu_core::global::Global>,
}
impl Drop for RegisteredDevice {
    fn drop(&mut self) {
        self.instance.device_drop(self.id);
    }
}
impl RegisteredDevice {
    /// Blocks until wgpu has done what was submitted up to `submission_index`, or all that was where none is given.
    /// wgpu calls back what waits for that from here, and from nowhere else: nothing polls a device but this.
    pub(crate) fn wait(&self, submission_index: Option<wgpu_core::SubmissionIndex>) {
        let poll_type = wgpu_types::PollType::Wait {
            submission_index,
            timeout: None,
        };
        if let Err(err) = self.instance.device_poll(self.id, poll_type) {
            log::warn!("Failed to poll device: {err}");
        }
    }
}

// queue needed for Device.queue
// adapter needed for surface_get_capabilities in connect_graphics_context
// keeping queue and adapter as Arc for reference counting while dropping.
// registered needed for all that polls the device, which is dropped with the last of it.
// lost needed in `GpuDevice.lost`.
// label and queue_label needed in `label` and `set-label`.
#[derive(Clone)]
pub struct Device {
    pub(crate) device: wgpu_core::id::DeviceId,
    pub(crate) queue: Arc<wgpu_core::id::QueueId>,
    pub(crate) adapter: Arc<wgpu_core::id::AdapterId>,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) registered: Arc<RegisteredDevice>,
    pub(crate) lost: Arc<DeviceLost>,
    pub(crate) label: String,
    pub(crate) queue_label: Arc<Mutex<String>>,
}
impl Device {
    pub fn device_id(&self) -> &wgpu_core::id::DeviceId {
        &self.device
    }

    /// Create a `Texture` from a `TextureId` that is connected to this device.
    /// Useful in cases where an external crate get a texture through get_current_texture
    /// and needs to connect it to a device.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the TextureId is actually connected to this device
    #[doc(hidden)]
    pub unsafe fn connect_texture(&self, texture_id: wgpu_core::id::TextureId) -> Texture {
        Texture {
            texture_id,
            error_handler: Arc::clone(&self.error_handler),
            descriptor: None,
            texture_binding_view_dimension: None,
            label: String::new(),
        }
    }

    /// Create a `Texture` as [`Device::connect_texture`] does, of a texture that `descriptor` describes.
    /// wgpu says nothing of a texture that it gave, so the getters of `gpu-texture` answer with `descriptor`,
    /// and have nothing to answer with for a texture that was connected without one.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the TextureId is actually connected to this device
    #[doc(hidden)]
    pub unsafe fn connect_texture_with_descriptor<L, V: Clone>(
        &self,
        texture_id: wgpu_core::id::TextureId,
        descriptor: &wgpu_types::TextureDescriptor<L, V>,
    ) -> Texture {
        Texture {
            descriptor: Some(descriptor.map_label_and_view_formats(|_| (), |_| ())),
            ..self.connect_texture(texture_id)
        }
    }
}

// What `GpuDevice.lost` resolves to, once wgpu says that the device is lost, and what waits for it until then.
#[derive(Default)]
pub(crate) struct DeviceLost(Mutex<DeviceLostInner>);

#[derive(Default)]
struct DeviceLostInner {
    info: Option<DeviceLostInfo>,
    wakers: Vec<Waker>,
}

#[derive(Clone, Debug)]
pub struct DeviceLostInfo {
    pub(crate) reason: webgpu::GpuDeviceLostReason,
    pub(crate) message: String,
}

impl DeviceLost {
    pub(crate) fn set(&self, info: DeviceLostInfo) {
        let mut inner = self.0.lock().unwrap();
        // A device is lost once.
        inner.info.get_or_insert(info);
        for waker in inner.wakers.drain(..) {
            waker.wake();
        }
    }

    pub(crate) fn poll(&self, cx: &mut Context<'_>) -> Poll<DeviceLostInfo> {
        let mut inner = self.0.lock().unwrap();
        match &inner.info {
            Some(info) => Poll::Ready(info.clone()),
            None => {
                inner.wakers.push(cx.waker().clone());
                Poll::Pending
            }
        }
    }
}

#[derive(Clone)]
pub struct CommandEncoder {
    pub(crate) command_encoder_id: wgpu_core::id::CommandEncoderId,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}

// descriptor and texture_binding_view_dimension needed in the getters of `GpuTexture`: wgpu gives nothing of a texture back.
// descriptor is None for a texture that `Device::connect_texture` was given none of.
pub struct Texture {
    pub(crate) texture_id: wgpu_core::id::TextureId,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) descriptor: Option<wgpu_types::TextureDescriptor<(), ()>>,
    pub(crate) texture_binding_view_dimension: Option<webgpu::GpuTextureViewDimension>,
    pub(crate) label: String,
}
impl Texture {
    /// What the texture was made with, for the getter `name` of `gpu-texture` to answer with.
    pub(crate) fn descriptor(
        &self,
        name: &str,
    ) -> wasmtime::Result<&wgpu_types::TextureDescriptor<(), ()>> {
        self.descriptor.as_ref().ok_or_else(|| {
            wasmtime::format_err!(
                "gpu-texture.{name}: the texture was connected to its device with no descriptor to answer with"
            )
        })
    }
}
pub struct RenderPipeline {
    pub(crate) render_pipeline_id: wgpu_core::id::RenderPipelineId,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}
pub struct ComputePipeline {
    pub(crate) compute_pipeline_id: wgpu_core::id::ComputePipelineId,
    pub(crate) error_handler: Arc<ErrorHandler>,
    pub(crate) label: String,
}

// messages needed in `GpuShaderModule.get_compilation_info`: wgpu gives what compiling a shader says as the error of making it, once.
pub struct ShaderModule {
    pub(crate) id: wgpu_core::id::ShaderModuleId,
    pub(crate) messages: Vec<CompilationMessage>,
    pub(crate) label: String,
}

pub struct CompilationInfo {
    pub(crate) messages: Vec<CompilationMessage>,
}

#[derive(Clone, Debug)]
pub struct CompilationMessage {
    pub(crate) message: String,
    pub(crate) type_: webgpu::GpuCompilationMessageType,
    pub(crate) line_num: u64,
    pub(crate) line_pos: u64,
    pub(crate) offset: u64,
    pub(crate) length: u64,
}

// type_ and count needed in `GpuQuerySet.type` and `GpuQuerySet.count`.
pub struct QuerySet {
    pub(crate) id: wgpu_core::id::QuerySetId,
    pub(crate) type_: webgpu::GpuQueryType,
    pub(crate) count: u32,
    pub(crate) label: String,
}

#[derive(Debug, Clone)]
pub struct GpuError {
    pub(crate) message: String,
    pub(crate) kind: webgpu::GpuErrorKind,
}

// An error of validation that this crate finds itself, in what wgpu is never given to find it in.
#[derive(Debug)]
pub(crate) struct ValidationError(pub(crate) String);

impl fmt::Display for ValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for ValidationError {}

impl wgpu_types::error::WebGpuError for ValidationError {
    fn webgpu_error_type(&self) -> wgpu_types::error::ErrorType {
        wgpu_types::error::ErrorType::Validation
    }
}

// Device level error handler
#[derive(Debug)]
pub(crate) struct ErrorHandler(Mutex<ErrorHandlerInner>);

#[derive(Debug)]
pub(crate) struct ErrorHandlerInner {
    scopes: Vec<ErrorScope>,
    uncaptured_error_sender: async_broadcast::Sender<webgpu::GpuError>,
    // Keeping inactive receiver to keep channel open.
    // See https://docs.rs/async-broadcast/0.7.1/async_broadcast/struct.InactiveReceiver.html
    _uncaptured_error_receiver: async_broadcast::InactiveReceiver<webgpu::GpuError>,
}

impl Default for ErrorHandler {
    fn default() -> Self {
        let (sender, receiver) = async_broadcast::broadcast(5);
        let receiver = receiver.deactivate();
        let inner = ErrorHandlerInner {
            scopes: Default::default(),
            uncaptured_error_sender: sender,
            _uncaptured_error_receiver: receiver,
        };
        Self(Mutex::new(inner))
    }
}

#[derive(Debug)]
struct ErrorScope {
    error: Option<webgpu::GpuError>,
    filter: webgpu::GpuErrorFilter,
}

impl ErrorHandler {
    pub fn push_scope(&self, filter: webgpu::GpuErrorFilter) {
        self.0.lock().unwrap().scopes.push(ErrorScope {
            filter,
            error: None,
        });
    }

    pub fn pop_scope(&self) -> Result<Option<webgpu::GpuError>, webgpu::PopErrorScopeError> {
        let scopes = self.0.lock().unwrap().scopes.pop();
        match scopes {
            Some(scope) => Ok(scope.error),
            None => {
                // From the spec:
                // > If any of the following requirements are unmet:
                // >  - this.[[errorScopeStack]].size must be > 0.
                // > Then issue the following steps on contentTimeline and return:
                // >  1. Reject promise with an OperationError.
                // https://www.w3.org/TR/webgpu/#dom-gpudevice-poperrorscope
                Err(webgpu::PopErrorScopeError {
                    kind: webgpu::PopErrorScopeErrorKind::OperationError,
                    message: "pop-error-scope on empty stack".to_string(),
                })
            }
        }
    }

    pub fn handle_possible_error<E: wgpu_types::error::WebGpuError + fmt::Display>(
        &self,
        error: Option<E>,
    ) {
        if let Some(error) = error {
            // A device that is lost has no errors: what is asked of it is done to no effect.
            // https://www.w3.org/TR/webgpu/#lose-the-device
            let Ok(error_kind) = webgpu::GpuErrorKind::try_from(error.webgpu_error_type()) else {
                return;
            };
            let error = GpuError {
                message: message(&error),
                kind: error_kind,
            };

            let error_filter = error_kind.into();
            let mut inner = self.0.lock().unwrap();
            match &mut inner
                .scopes
                .iter_mut()
                .rev()
                .find(|scope| scope.filter == error_filter)
            {
                Some(scope) => {
                    // Only return one error per scope.
                    // From the spec:
                    // > 4. Let error be any one of the items in scope.[[errors]], or null if there are none.
                    // >   For any two errors E1 and E2 in the list, if E2 was caused by E1, E2 should not be the one selected.
                    // https://www.w3.org/TR/webgpu/#dom-gpudevice-poperrorscope
                    // Here we're assuming that the first error is the one that caused the others, so only set the first error.
                    if scope.error.is_none() {
                        scope.error = Some(error);
                    }
                }
                None => {
                    shared::unwrap_unless_inactive_or_full(
                        inner.uncaptured_error_sender.try_broadcast(error),
                    );
                }
            }
        }
    }

    pub(crate) fn new_error_receiver(&self) -> async_broadcast::Receiver<webgpu::GpuError> {
        self.0
            .lock()
            .unwrap()
            .uncaptured_error_sender
            .new_receiver()
    }
}

/// What `error` says, and then what each error that caused it says and `error` leaves out:
/// wgpu has the reason of an error be its source as often as its text.
pub(crate) fn message(error: &dyn std::error::Error) -> String {
    let mut message = error.to_string();
    let mut source = error.source();
    while let Some(error) = source {
        let cause = error.to_string();
        if !message.contains(&cause) {
            message.push_str(": ");
            message.push_str(&cause);
        }
        source = error.source();
    }
    message
}

// For now, GpuErrorFilter and GpuErrorKind are effectively the same, just with different names.
impl From<webgpu::GpuErrorFilter> for webgpu::GpuErrorKind {
    fn from(filter: webgpu::GpuErrorFilter) -> Self {
        match filter {
            webgpu::GpuErrorFilter::Validation => webgpu::GpuErrorKind::ValidationError,
            webgpu::GpuErrorFilter::OutOfMemory => webgpu::GpuErrorKind::OutOfMemoryError,
            webgpu::GpuErrorFilter::Internal => webgpu::GpuErrorKind::InternalError,
        }
    }
}
impl From<webgpu::GpuErrorKind> for webgpu::GpuErrorFilter {
    fn from(kind: webgpu::GpuErrorKind) -> Self {
        match kind {
            webgpu::GpuErrorKind::ValidationError => webgpu::GpuErrorFilter::Validation,
            webgpu::GpuErrorKind::OutOfMemoryError => webgpu::GpuErrorFilter::OutOfMemory,
            webgpu::GpuErrorKind::InternalError => webgpu::GpuErrorFilter::Internal,
        }
    }
}
