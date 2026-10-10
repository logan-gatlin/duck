use callback_future::CallbackFuture;
use core::slice;
use shared::StreamPipeMap;
use std::{
    borrow::Cow,
    collections::HashMap,
    num::NonZeroU64,
    pin::Pin,
    sync::{Arc, Mutex},
    task::{Context, Poll},
};
use wasmtime::{
    bail,
    component::{Access, Accessor, FutureProducer, FutureReader, Resource, StreamReader},
    StoreContextMut,
};

use crate::{
    to_core_conversions::ToCore,
    types::{
        message, Buffer, CommandEncoder, CompilationInfo, CompilationMessage, ComputePassEncoder,
        ComputePipeline, Device, DeviceLost, DeviceLostInfo, ErrorHandler, Labeled, QuerySet,
        Queue, RegisteredDevice, RenderBundleEncoder, RenderPassEncoder, RenderPipeline,
        ShaderModule, Texture, ValidationError, WgslLanguageFeatures,
    },
    wasi::webgpu::webgpu,
    WasiWebGpuCtx, WasiWebGpuCtxView, PREFERRED_CANVAS_FORMAT,
};

// What `GpuDevice.lost` gives: how its device was lost, once it is.
struct Lost(Arc<DeviceLost>);

impl<T: WasiWebGpuCtxView + 'static> FutureProducer<T> for Lost {
    type Item = Resource<webgpu::GpuDeviceLostInfo>;

    fn poll_produce(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        mut store: StoreContextMut<T>,
        finish: bool,
    ) -> Poll<wasmtime::Result<Option<Self::Item>>> {
        match self.0.poll(cx) {
            Poll::Ready(info) => {
                let info = store.data_mut().webgpu_ctx().table.push(info)?;
                Poll::Ready(Ok(Some(info)))
            }
            Poll::Pending if finish => Poll::Ready(Ok(None)),
            Poll::Pending => Poll::Pending,
        }
    }
}

/// The `size` elements of `data` from `offset`, or none where `data` has no such part.
/// The part is from the start where no `offset` is given, and up to the end where no `size` is.
fn part<T>(data: &[T], offset: Option<u64>, size: Option<u64>) -> Option<&[T]> {
    let data = data.get(usize::try_from(offset.unwrap_or(0)).ok()?..)?;
    match size {
        Some(size) => data.get(..usize::try_from(size).ok()?),
        None => Some(data),
    }
}

/// The dynamic offsets that a `set-bind-group` is given.
///
/// From the spec:
/// > 1. If dynamicOffsetsDataStart + dynamicOffsetsDataLength > dynamicOffsetsData.length, throw a RangeError and return.
///
/// https://www.w3.org/TR/webgpu/#programmable-passes
fn dynamic_offsets(
    data: &Option<Vec<webgpu::GpuBufferDynamicOffset>>,
    start: Option<webgpu::GpuSize64>,
    length: Option<webgpu::GpuSize32>,
) -> Result<&[webgpu::GpuBufferDynamicOffset], webgpu::SetBindGroupError> {
    let data = data.as_deref().unwrap_or(&[]);
    part(data, start, length.map(u64::from)).ok_or_else(|| webgpu::SetBindGroupError {
        kind: webgpu::SetBindGroupErrorKind::RangeError,
        message: format!(
            "the dynamic offsets asked for are not among the {} that were given",
            data.len()
        ),
    })
}

/// The bytes that a `set-immediates` is given: those of `data` from `offset`, as many as `size`.
/// WebGPU has an `OperationError` be thrown where `data` has no such part, which the WIT has no result for.
fn immediates<'a>(
    function: &str,
    data: &'a [u8],
    offset: Option<u64>,
    size: Option<u64>,
) -> wasmtime::Result<&'a [u8]> {
    part(data, offset, size).ok_or_else(|| {
        wasmtime::format_err!(
            "{function}: the bytes asked for are not among the {} that were given",
            data.len()
        )
    })
}

/// What compiling a shader said, which wgpu gives as the `error` of making its module.
/// It says where in the code as WebGPU does, in UTF-16 code units, and naga in bytes of UTF-8.
/// https://www.w3.org/TR/webgpu/#gpucompilationmessage
fn compilation_message(error: &wgpu_core::pipeline::CreateShaderModuleError) -> CompilationMessage {
    use wgpu_core::pipeline::CreateShaderModuleError;
    let (text, located) = match error {
        CreateShaderModuleError::Parsing(e) => (
            e.inner.message().to_string(),
            e.inner.location(&e.source).map(|l| (l, e.source.as_str())),
        ),
        CreateShaderModuleError::Validation(e) => (
            message(e.inner.as_inner()),
            e.inner.location(&e.source).map(|l| (l, e.source.as_str())),
        ),
        error => (message(error), None),
    };
    let units = |code: Option<&str>| code.map_or(0, |code| code.encode_utf16().count() as u64);
    let (line_num, line_pos, offset, length) = match located {
        Some((location, code)) => {
            let start = location.offset as usize;
            let end = start + location.length as usize;
            let line = (start + 1).saturating_sub(location.line_position as usize);
            (
                location.line_number as u64,
                units(code.get(line..start)) + 1,
                units(code.get(..start)),
                units(code.get(start..end)),
            )
        }
        // From the spec:
        // > If the message corresponds to a substring this points to the first UTF-16 code unit of the substring. Otherwise, it must be 0.
        None => (0, 0, 0, 0),
    };
    CompilationMessage {
        message: text,
        // wgpu gives nothing of a shader that it compiles but why it won't.
        type_: webgpu::GpuCompilationMessageType::Error,
        line_num,
        line_pos,
        offset,
        length,
    }
}

/// The bytes of `buffer` that `get-mapped-range-get-with-copy` reads and `get-mapped-range-set-with-copy` writes, as wgpu has mapped them.
///
/// From the spec:
/// > 4. If any of the following conditions are unsatisfied, throw an OperationError and return.
///
/// https://www.w3.org/TR/webgpu/#dom-gpubuffer-getmappedrange
fn mapped_range(
    instance: &wgpu_core::global::Global,
    buffer: &Buffer,
    offset: Option<webgpu::GpuSize64>,
    size: Option<webgpu::GpuSize64>,
) -> Result<(std::ptr::NonNull<u8>, usize), webgpu::GetMappedRangeError> {
    let operation_error = |message| webgpu::GetMappedRangeError {
        kind: webgpu::GetMappedRangeErrorKind::OperationError,
        message,
    };
    if buffer.map_state != webgpu::GpuBufferMapState::Mapped {
        return Err(operation_error("the buffer is not mapped".to_string()));
    }
    let (ptr, len) = instance
        // https://www.w3.org/TR/webgpu/#gpubuffer
        .buffer_get_mapped_range(buffer.buffer_id, offset.unwrap_or(0), size)
        .map_err(|err| operation_error(message(&err)))?;
    Ok((ptr, len as usize))
}

/// Why a pipeline was not made, as `create-compute-pipeline-async` and `create-render-pipeline-async` give it.
/// https://www.w3.org/TR/webgpu/#gpupipelineerror
fn pipeline_error<E: wgpu_types::error::WebGpuError>(error: E) -> webgpu::CreatePipelineError {
    let reason = match error.webgpu_error_type() {
        wgpu_types::error::ErrorType::Validation => webgpu::GpuPipelineErrorReason::Validation,
        _ => webgpu::GpuPipelineErrorReason::Internal,
    };
    webgpu::CreatePipelineError {
        kind: webgpu::CreatePipelineErrorKind::GpuPipelineError(reason),
        message: message(&error),
    }
}

/// The name of who makes the GPUs of the PCI vendor `id`, as WebGPU has an adapter give it, or none where it is not one that wgpu knows.
/// https://www.w3.org/TR/webgpu/#dom-gpuadapterinfo-vendor
fn vendor_name(id: u32) -> Option<&'static str> {
    // https://github.com/gfx-rs/wgpu/blob/v29/wgpu-hal/src/auxil/mod.rs
    Some(match id {
        0x1002 | 0x1022 => "amd",
        0x106B => "apple",
        0x13B5 => "arm",
        0x14E4 => "broadcom",
        0x1010 => "img-tec",
        0x8086 => "intel",
        0x10005 => "mesa",
        0x1414 => "microsoft",
        0x10DE => "nvidia",
        0x5143 => "qualcomm",
        _ => return None,
    })
}

impl<'a> webgpu::Host for WasiWebGpuCtx<'a> {
    fn get_gpu(&mut self) -> wasmtime::Result<Resource<webgpu::Gpu>> {
        Ok(Resource::new_own(0))
    }
}

impl<'a> webgpu::HostRecordGpuPipelineConstantValue for WasiWebGpuCtx<'a> {
    fn new(&mut self) -> wasmtime::Result<Resource<webgpu::RecordGpuPipelineConstantValue>> {
        Ok(self.table.push(HashMap::new())?)
    }

    fn add(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
        key: String,
        value: webgpu::GpuPipelineConstantValue,
    ) -> wasmtime::Result<()> {
        let record = self.table.get_mut(&record)?;
        record.insert(key, value);
        Ok(())
    }

    fn get(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
        key: String,
    ) -> wasmtime::Result<Option<webgpu::GpuPipelineConstantValue>> {
        let record = self.table.get(&record)?;
        let value = record.get(&key).copied();
        Ok(value)
    }

    fn has(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
        key: String,
    ) -> wasmtime::Result<bool> {
        let record = self.table.get(&record)?;
        Ok(record.contains_key(&key))
    }

    fn remove(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
        key: String,
    ) -> wasmtime::Result<()> {
        let record = self.table.get_mut(&record)?;
        record.remove(&key);
        Ok(())
    }

    fn keys(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
    ) -> wasmtime::Result<Vec<String>> {
        let record = self.table.get(&record)?;
        let keys = record.keys().cloned().collect();
        Ok(keys)
    }

    fn values(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
    ) -> wasmtime::Result<Vec<webgpu::GpuPipelineConstantValue>> {
        let record = self.table.get(&record)?;
        let values = record.values().copied().collect();
        Ok(values)
    }

    fn entries(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
    ) -> wasmtime::Result<Vec<(String, webgpu::GpuPipelineConstantValue)>> {
        let record = self.table.get(&record)?;
        let entries = record.iter().map(|(k, v)| (k.clone(), *v)).collect();
        Ok(entries)
    }

    fn drop(
        &mut self,
        record: Resource<webgpu::RecordGpuPipelineConstantValue>,
    ) -> wasmtime::Result<()> {
        self.table.delete(record)?;
        Ok(())
    }
}

impl<'a> webgpu::HostRecordOptionGpuSize64 for WasiWebGpuCtx<'a> {
    fn new(&mut self) -> wasmtime::Result<Resource<webgpu::RecordOptionGpuSize64>> {
        let record = std::collections::HashMap::new();
        Ok(self.table.push(record)?)
    }
    fn add(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
        key: String,
        value: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        let record = self.table.get_mut(&record)?;
        record.insert(key, value);
        Ok(())
    }
    fn get(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
        key: String,
    ) -> wasmtime::Result<Option<Option<webgpu::GpuSize64>>> {
        let record = self.table.get(&record)?;
        Ok(record.get(&key).copied())
    }
    fn has(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
        key: String,
    ) -> wasmtime::Result<bool> {
        let record = self.table.get(&record)?;
        Ok(record.contains_key(&key))
    }
    fn remove(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
        key: String,
    ) -> wasmtime::Result<()> {
        let record = self.table.get_mut(&record)?;
        record.remove(&key);
        Ok(())
    }
    fn keys(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
    ) -> wasmtime::Result<Vec<String>> {
        let record = self.table.get(&record)?;
        Ok(record.keys().cloned().collect())
    }
    fn values(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
    ) -> wasmtime::Result<Vec<Option<webgpu::GpuSize64>>> {
        let record = self.table.get(&record)?;
        Ok(record.values().cloned().collect())
    }
    fn entries(
        &mut self,
        record: Resource<webgpu::RecordOptionGpuSize64>,
    ) -> wasmtime::Result<Vec<(String, Option<webgpu::GpuSize64>)>> {
        let record = self.table.get(&record)?;
        Ok(record.iter().map(|(k, v)| (k.clone(), *v)).collect())
    }
    fn drop(&mut self, record: Resource<webgpu::RecordOptionGpuSize64>) -> wasmtime::Result<()> {
        self.table.delete(record)?;
        Ok(())
    }
}

impl<'a> webgpu::HostGpuDevice for WasiWebGpuCtx<'a> {
    fn adapter_info(
        &mut self,
        device: Resource<Device>,
    ) -> wasmtime::Result<Resource<webgpu::GpuAdapterInfo>> {
        let adapter_id = *self.table.get(&device)?.adapter;
        let info = self.instance.adapter_get_info(adapter_id);
        let info = self.table.push(info)?;
        Ok(info)
    }

    fn create_command_encoder(
        &mut self,
        device: Resource<Device>,
        descriptor: Option<webgpu::GpuCommandEncoderDescriptor>,
    ) -> wasmtime::Result<Resource<CommandEncoder>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor
            .as_ref()
            .and_then(|d| d.label.clone())
            .unwrap_or_default();

        let (command_encoder_id, err) = self.instance.device_create_command_encoder(
            device_id,
            &descriptor
                .map(|d| d.to_core(self.table))
                .unwrap_or(wgpu_types::CommandEncoderDescriptor::default()),
            None,
        );

        error_handler.handle_possible_error(err);

        let command_encoder = self.table.push(CommandEncoder {
            command_encoder_id,
            error_handler,
            label,
        })?;
        Ok(command_encoder)
    }

    fn create_shader_module(
        &mut self,
        device: Resource<Device>,
        descriptor: webgpu::GpuShaderModuleDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuShaderModule>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();

        let code =
            wgpu_core::pipeline::ShaderModuleSource::Wgsl(Cow::Owned(descriptor.code.to_owned()));
        let (id, err) = self.instance.device_create_shader_module(
            device_id,
            &descriptor.to_core(self.table),
            code,
            None,
        );

        let messages = err.iter().map(compilation_message).collect();
        error_handler.handle_possible_error(err);

        Ok(self.table.push(ShaderModule {
            id,
            messages,
            label,
        })?)
    }

    fn create_render_pipeline(
        &mut self,
        device: Resource<Device>,
        descriptor: webgpu::GpuRenderPipelineDescriptor,
    ) -> wasmtime::Result<Resource<RenderPipeline>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();

        let (render_pipeline_id, err) = self.instance.device_create_render_pipeline(
            device_id,
            &descriptor.to_core(self.table),
            None,
        );

        error_handler.handle_possible_error(err);

        let render_pipeline = self.table.push(RenderPipeline {
            render_pipeline_id,
            error_handler,
            label,
        })?;
        Ok(render_pipeline)
    }

    fn queue(&mut self, device: Resource<Device>) -> wasmtime::Result<Resource<webgpu::GpuQueue>> {
        let device = self.table.get(&device)?;
        let queue = Queue {
            queue_id: Arc::clone(&device.queue),
            device: Arc::clone(&device.registered),
            error_handler: Arc::clone(&device.error_handler),
            label: Arc::clone(&device.queue_label),
        };
        Ok(self.table.push(queue)?)
    }

    fn features(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
    ) -> wasmtime::Result<Resource<webgpu::GpuSupportedFeatures>> {
        let device = self.table.get(&device)?.device;
        let features = self.instance.device_features(device);
        Ok(self.table.push(features)?)
    }

    fn limits(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
    ) -> wasmtime::Result<Resource<webgpu::GpuSupportedLimits>> {
        let device = self.table.get(&device)?.device;
        let limits = self.instance.device_limits(device);
        Ok(self.table.push(limits)?)
    }

    fn destroy(&mut self, device: Resource<webgpu::GpuDevice>) -> wasmtime::Result<()> {
        let device = self.table.get(&device)?;
        self.instance.device_destroy(device.device);
        // wgpu says that the device is lost as it is next polled with nothing left to do: `GpuDevice.lost` resolves by then.
        device.registered.wait(None);
        Ok(())
    }

    fn create_buffer(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuBufferDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuBuffer>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let registered = Arc::clone(&device.registered);
        let queue = Arc::downgrade(&device.queue);
        let label = descriptor.label.clone().unwrap_or_default();
        let descriptor = descriptor.to_core(self.table);

        let size = descriptor.size;
        let usage = descriptor.usage;
        let (buffer_id, err) = self
            .instance
            .device_create_buffer(device_id, &descriptor, None);

        // A buffer that was not made is mapped by nothing.
        let map_state = match descriptor.mapped_at_creation && err.is_none() {
            true => webgpu::GpuBufferMapState::Mapped,
            false => webgpu::GpuBufferMapState::Unmapped,
        };

        error_handler.handle_possible_error(err);

        let buffer = Buffer {
            buffer_id,
            size,
            usage,
            map_state,
            // https://www.w3.org/TR/webgpu/#dom-gpubufferdescriptor-mappedatcreation
            map_mode: wgpu_core::device::HostMap::Write,
            device: registered,
            queue,
            error_handler,
            label,
        };

        Ok(self.table.push(buffer)?)
    }

    fn create_texture(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuTextureDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuTexture>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();
        let texture_binding_view_dimension = descriptor.texture_binding_view_dimension;
        let descriptor = descriptor.to_core(self.table);

        let (texture_id, err) = self
            .instance
            .device_create_texture(device_id, &descriptor, None);

        error_handler.handle_possible_error(err);

        Ok(self.table.push(Texture {
            texture_id,
            error_handler,
            descriptor: Some(descriptor.map_label_and_view_formats(|_| (), |_| ())),
            texture_binding_view_dimension,
            label,
        })?)
    }

    fn create_sampler(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: Option<webgpu::GpuSamplerDescriptor>,
    ) -> wasmtime::Result<Resource<webgpu::GpuSampler>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor
            .as_ref()
            .and_then(|d| d.label.clone())
            .unwrap_or_default();

        let descriptor = descriptor
            .map(|d| d.to_core(self.table))
            // https://www.w3.org/TR/webgpu/#dictdef-gpusamplerdescriptor
            .unwrap_or_else(|| wgpu_core::resource::SamplerDescriptor {
                label: None,
                address_modes: [wgpu_types::AddressMode::ClampToEdge; 3],
                mag_filter: wgpu_types::FilterMode::Nearest,
                min_filter: wgpu_types::FilterMode::Nearest,
                mipmap_filter: wgpu_types::MipmapFilterMode::Nearest,
                lod_min_clamp: 0.0,
                lod_max_clamp: 32.0,
                compare: None,
                // TODO: make sure that anisotropy_clamp actually corresponds to maxAnisotropy
                anisotropy_clamp: 1,
                // border_color is not present in WebGPU
                border_color: None,
            });

        let (id, err) = self
            .instance
            .device_create_sampler(device_id, &descriptor, None);

        error_handler.handle_possible_error(err);

        Ok(self.table.push(Labeled { id, label })?)
    }

    fn create_bind_group_layout(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuBindGroupLayoutDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuBindGroupLayout>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();

        let id = match descriptor.to_core(self.table) {
            Ok(descriptor) => {
                let (id, err) =
                    self.instance
                        .device_create_bind_group_layout(device_id, &descriptor, None);
                error_handler.handle_possible_error(err);
                id
            }
            Err(err) => {
                error_handler.handle_possible_error(Some(err));
                // The layout is then one that is not valid, which wgpu makes only of a descriptor that it refuses itself:
                // one of two entries for a binding is, for whatever device.
                let entry = wgpu_types::BindGroupLayoutEntry {
                    binding: 0,
                    visibility: wgpu_types::ShaderStages::NONE,
                    ty: wgpu_types::BindingType::Sampler(wgpu_types::SamplerBindingType::Filtering),
                    count: None,
                };
                let descriptor = wgpu_core::binding_model::BindGroupLayoutDescriptor {
                    label: Some(label.as_str().into()),
                    entries: vec![entry, entry].into(),
                };
                let (id, _) =
                    self.instance
                        .device_create_bind_group_layout(device_id, &descriptor, None);
                id
            }
        };

        Ok(self.table.push(Labeled { id, label })?)
    }

    fn create_pipeline_layout(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuPipelineLayoutDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuPipelineLayout>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();

        let (id, err) = self.instance.device_create_pipeline_layout(
            device_id,
            &descriptor.to_core(self.table),
            None,
        );

        error_handler.handle_possible_error(err);

        Ok(self.table.push(Labeled { id, label })?)
    }

    fn create_bind_group(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuBindGroupDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuBindGroup>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();
        // The views that are made here of the textures that are bound, which the bind group keeps for itself.
        let mut views = Vec::new();

        // not using to_core for conversion since we need instance or self for `GpuBindingResource::GpuTexture`
        let descriptor = wgpu_core::binding_model::BindGroupDescriptor {
            label: descriptor.label.map(|l| l.into()),
            layout: descriptor.layout.to_core(self.table),
            entries: descriptor
                .entries
                .into_iter()
                .map(|entry| -> wasmtime::Result<_> {
                    let resource = match entry.resource {
                        webgpu::GpuBindingResource::GpuBuffer(buffer) => {
                            let binding = webgpu::GpuBufferBinding {
                                buffer,
                                offset: None,
                                size: None,
                            };
                            wgpu_core::binding_model::BindingResource::Buffer(
                                binding.to_core(self.table),
                            )
                        }
                        webgpu::GpuBindingResource::GpuBufferBinding(buffer) => {
                            wgpu_core::binding_model::BindingResource::Buffer(
                                buffer.to_core(self.table),
                            )
                        }
                        webgpu::GpuBindingResource::GpuSampler(sampler) => {
                            wgpu_core::binding_model::BindingResource::Sampler(
                                sampler.to_core(self.table),
                            )
                        }
                        webgpu::GpuBindingResource::GpuTexture(texture) => {
                            // https://www.w3.org/TR/webgpu/#typedefdef-gpubindingresource
                            let texture_id = self.table.get(&texture)?.texture_id;
                            let (view, err) = self.instance.texture_create_view(
                                texture_id,
                                &wgpu_core::resource::TextureViewDescriptor::default(),
                                None,
                            );
                            error_handler.handle_possible_error(err);
                            views.push(view);
                            wgpu_core::binding_model::BindingResource::TextureView(view)
                        }
                        webgpu::GpuBindingResource::GpuTextureView(texture_view) => {
                            wgpu_core::binding_model::BindingResource::TextureView(
                                texture_view.to_core(self.table),
                            )
                        }
                    };
                    Ok(wgpu_core::binding_model::BindGroupEntry {
                        binding: entry.binding,
                        resource,
                    })
                })
                .collect::<wasmtime::Result<_>>()?,
        };

        let (id, err) = self
            .instance
            .device_create_bind_group(device_id, &descriptor, None);

        error_handler.handle_possible_error(err);
        for view in views {
            self.instance.texture_view_drop(view);
        }

        Ok(self.table.push(Labeled { id, label })?)
    }

    fn create_compute_pipeline(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuComputePipelineDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuComputePipeline>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();

        let (compute_pipeline_id, err) = self.instance.device_create_compute_pipeline(
            device_id,
            &descriptor.to_core(self.table),
            None,
        );

        error_handler.handle_possible_error(err);

        Ok(self.table.push(ComputePipeline {
            compute_pipeline_id,
            error_handler,
            label,
        })?)
    }

    fn create_render_bundle_encoder(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuRenderBundleEncoderDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuRenderBundleEncoder>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let registered = Arc::clone(&device.registered);
        let label = descriptor.label.clone().unwrap_or_default();
        let encoder = wgpu_core::command::RenderBundleEncoder::new(
            &descriptor.to_core(self.table),
            device_id,
        )
        // An encoder that wgpu won't make is one that finishes to no bundle, as it has it itself.
        .unwrap_or_else(|err| {
            error_handler.handle_possible_error(Some(err));
            wgpu_core::command::RenderBundleEncoder::dummy(device_id)
        });
        let render_bundle_encoder = self.table.push(RenderBundleEncoder {
            encoder: Some(encoder),
            device: registered,
            error_handler,
            label,
        })?;
        Ok(render_bundle_encoder)
    }

    fn create_query_set(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuQuerySetDescriptor,
    ) -> wasmtime::Result<Result<Resource<webgpu::GpuQuerySet>, webgpu::CreateQuerySetError>> {
        let device = self.table.get(&device)?;
        let device_id = device.device;
        let error_handler = Arc::clone(&device.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();
        let type_ = descriptor.type_;
        let count = descriptor.count;

        let (id, err) =
            self.instance
                .device_create_query_set(device_id, &descriptor.to_core(self.table), None);

        // From the spec:
        // > 1. If descriptor.type is "timestamp", but "timestamp-query" is not enabled for this:
        // >  1. Throw a TypeError.
        // https://www.w3.org/TR/webgpu/#dom-gpudevice-createqueryset
        if let Some(wgpu_core::resource::CreateQuerySetError::MissingFeatures(_)) = err {
            self.instance.query_set_drop(id);
            return Ok(Err(webgpu::CreateQuerySetError {
                kind: webgpu::CreateQuerySetErrorKind::TypeError,
                message: err.iter().map(|err| message(err)).collect(),
            }));
        }

        error_handler.handle_possible_error(err);

        Ok(Ok(self.table.push(QuerySet {
            id,
            type_,
            count,
            label,
        })?))
    }

    fn label(&mut self, device: Resource<webgpu::GpuDevice>) -> wasmtime::Result<String> {
        Ok(self.table.get(&device)?.label.clone())
    }

    fn set_label(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&device)?.label = label;
        Ok(())
    }

    fn push_error_scope(
        &mut self,
        device: Resource<webgpu::GpuDevice>,
        filter: webgpu::GpuErrorFilter,
    ) -> wasmtime::Result<()> {
        let device = self.table.get(&device)?;
        device.error_handler.push_scope(filter);
        Ok(())
    }

    fn drop(&mut self, device: Resource<webgpu::GpuDevice>) -> wasmtime::Result<()> {
        let device = self.table.delete(device)?;
        // wgpu drops the device itself with `device.registered`, once nothing polls it.
        if let Some(adapter_id) = Arc::into_inner(device.adapter) {
            self.instance.adapter_drop(adapter_id);
        }
        if let Some(queue_id) = Arc::into_inner(device.queue) {
            self.instance.queue_drop(queue_id);
        }
        Ok(())
    }
}

impl<T: Send + WasiWebGpuCtxView> webgpu::HostGpuDeviceWithStore<T> for crate::HasWasiWebGpuCtx {
    async fn create_compute_pipeline_async(
        accessor: &Accessor<T, Self>,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuComputePipelineDescriptor,
    ) -> wasmtime::Result<Result<Resource<webgpu::GpuComputePipeline>, webgpu::CreatePipelineError>>
    {
        accessor.with(|mut access| {
            let ctx = access.get();
            let device = ctx.table.get(&device)?;
            let device_id = device.device;
            let error_handler = Arc::clone(&device.error_handler);
            let label = descriptor.label.clone().unwrap_or_default();

            let (compute_pipeline_id, err) = ctx.instance.device_create_compute_pipeline(
                device_id,
                &descriptor.to_core(ctx.table),
                None,
            );

            // From the spec:
            // > Note: No error is generated from pipeline creation in this case; the returned promise is rejected instead.
            // https://www.w3.org/TR/webgpu/#dom-gpudevice-createcomputepipelineasync
            if let Some(err) = err {
                ctx.instance.compute_pipeline_drop(compute_pipeline_id);
                return Ok(Err(pipeline_error(err)));
            }

            Ok(Ok(ctx.table.push(ComputePipeline {
                compute_pipeline_id,
                error_handler,
                label,
            })?))
        })
    }

    async fn create_render_pipeline_async(
        accessor: &Accessor<T, Self>,
        device: Resource<webgpu::GpuDevice>,
        descriptor: webgpu::GpuRenderPipelineDescriptor,
    ) -> wasmtime::Result<Result<Resource<webgpu::GpuRenderPipeline>, webgpu::CreatePipelineError>>
    {
        accessor.with(|mut access| {
            let ctx = access.get();
            let device = ctx.table.get(&device)?;
            let device_id = device.device;
            let error_handler = Arc::clone(&device.error_handler);
            let label = descriptor.label.clone().unwrap_or_default();

            let (render_pipeline_id, err) = ctx.instance.device_create_render_pipeline(
                device_id,
                &descriptor.to_core(ctx.table),
                None,
            );

            // https://www.w3.org/TR/webgpu/#dom-gpudevice-createrenderpipelineasync
            if let Some(err) = err {
                ctx.instance.render_pipeline_drop(render_pipeline_id);
                return Ok(Err(pipeline_error(err)));
            }

            let render_pipeline = ctx.table.push(RenderPipeline {
                render_pipeline_id,
                error_handler,
                label,
            })?;
            Ok(Ok(render_pipeline))
        })
    }

    async fn pop_error_scope(
        accessor: &Accessor<T, Self>,
        device: Resource<webgpu::GpuDevice>,
    ) -> wasmtime::Result<Result<Option<Resource<webgpu::GpuError>>, webgpu::PopErrorScopeError>>
    {
        accessor.with(|mut access| {
            let ctx = access.get();
            let device = ctx.table.get(&device)?;
            Ok(match device.error_handler.pop_scope() {
                Ok(Some(error)) => Ok(Some(ctx.table.push(error)?)),
                Ok(None) => Ok(None),
                Err(error) => Err(error),
            })
        })
    }

    fn on_uncaptured_error(
        mut access: Access<T, Self>,
        device: Resource<webgpu::GpuDevice>,
    ) -> wasmtime::Result<StreamReader<Resource<webgpu::GpuError>>> {
        let ctx = access.get();
        let receiver = ctx.table.get(&device)?.error_handler.new_error_receiver();
        StreamReader::new(
            access,
            StreamPipeMap(receiver, |data: &mut T, err| {
                Ok(data.webgpu_ctx().table.push(err)?)
            }),
        )
    }

    fn lost(
        mut access: Access<T, Self>,
        device: Resource<webgpu::GpuDevice>,
    ) -> wasmtime::Result<FutureReader<Resource<webgpu::GpuDeviceLostInfo>>> {
        let ctx = access.get();
        let lost = Arc::clone(&ctx.table.get(&device)?.lost);
        FutureReader::new(access, Lost(lost))
    }
}

impl<'a> webgpu::HostGpuTexture for WasiWebGpuCtx<'a> {
    fn create_view(
        &mut self,
        texture: Resource<Texture>,
        descriptor: Option<webgpu::GpuTextureViewDescriptor>,
    ) -> wasmtime::Result<Resource<webgpu::GpuTextureView>> {
        let texture = self.table.get(&texture)?;
        let texture_id = texture.texture_id;
        let error_handler = Arc::clone(&texture.error_handler);
        let label = descriptor
            .as_ref()
            .and_then(|d| d.label.clone())
            .unwrap_or_default();
        let (id, err) = self.instance.texture_create_view(
            texture_id,
            &descriptor
                .map(|d| d.to_core(self.table))
                .unwrap_or(wgpu_core::resource::TextureViewDescriptor::default()),
            None,
        );
        error_handler.handle_possible_error(err);
        Ok(self.table.push(Labeled { id, label })?)
    }

    fn destroy(&mut self, texture: Resource<webgpu::GpuTexture>) -> wasmtime::Result<()> {
        let texture = self.table.get(&texture)?.texture_id;
        self.instance.texture_destroy(texture);
        Ok(())
    }

    fn width(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuIntegerCoordinateOut> {
        let texture = self.table.get(&texture)?;
        Ok(texture.descriptor("width")?.size.width)
    }

    fn height(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuIntegerCoordinateOut> {
        let texture = self.table.get(&texture)?;
        Ok(texture.descriptor("height")?.size.height)
    }

    fn depth_or_array_layers(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuIntegerCoordinateOut> {
        let texture = self.table.get(&texture)?;
        let descriptor = texture.descriptor("depth-or-array-layers")?;
        Ok(descriptor.size.depth_or_array_layers)
    }

    fn mip_level_count(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuIntegerCoordinateOut> {
        let texture = self.table.get(&texture)?;
        Ok(texture.descriptor("mip-level-count")?.mip_level_count)
    }

    fn sample_count(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuSize32Out> {
        let texture = self.table.get(&texture)?;
        Ok(texture.descriptor("sample-count")?.sample_count)
    }

    fn dimension(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuTextureDimension> {
        let texture = self.table.get(&texture)?;
        Ok(texture.descriptor("dimension")?.dimension.into())
    }

    fn format(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuTextureFormat> {
        let texture = self.table.get(&texture)?;
        let format = texture.descriptor("format")?.format;
        // A texture of a surface may have a format that only wgpu has.
        format.try_into().map_err(|_: wasmtime::Error| {
            wasmtime::format_err!("gpu-texture.format: WebGPU has no format that is {format:?}")
        })
    }

    fn usage(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<webgpu::GpuTextureUsage> {
        let texture = self.table.get(&texture)?;
        texture.descriptor("usage")?.usage.try_into()
    }

    fn texture_binding_view_dimension(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
    ) -> wasmtime::Result<Option<webgpu::GpuTextureViewDimension>> {
        let texture = self.table.get(&texture)?;
        Ok(texture.texture_binding_view_dimension)
    }

    fn label(&mut self, texture: Resource<webgpu::GpuTexture>) -> wasmtime::Result<String> {
        Ok(self.table.get(&texture)?.label.clone())
    }

    fn set_label(
        &mut self,
        texture: Resource<webgpu::GpuTexture>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&texture)?.label = label;
        Ok(())
    }

    fn drop(&mut self, texture: Resource<webgpu::GpuTexture>) -> wasmtime::Result<()> {
        let texture = self.table.delete(texture)?;
        self.instance.texture_drop(texture.texture_id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuTextureView for WasiWebGpuCtx<'a> {
    fn label(&mut self, view: Resource<webgpu::GpuTextureView>) -> wasmtime::Result<String> {
        Ok(self.table.get(&view)?.label.clone())
    }

    fn set_label(
        &mut self,
        view: Resource<webgpu::GpuTextureView>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&view)?.label = label;
        Ok(())
    }

    fn drop(&mut self, view: Resource<webgpu::GpuTextureView>) -> wasmtime::Result<()> {
        let view = self.table.delete(view)?;
        self.instance.texture_view_drop(view.id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuCommandBuffer for WasiWebGpuCtx<'a> {
    fn label(
        &mut self,
        command_buffer: Resource<webgpu::GpuCommandBuffer>,
    ) -> wasmtime::Result<String> {
        Ok(self.table.get(&command_buffer)?.label.clone())
    }

    fn set_label(
        &mut self,
        command_buffer: Resource<webgpu::GpuCommandBuffer>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&command_buffer)?.label = label;
        Ok(())
    }

    fn drop(&mut self, command_buffer: Resource<webgpu::GpuCommandBuffer>) -> wasmtime::Result<()> {
        let command_buffer = self.table.delete(command_buffer)?;
        self.instance.command_buffer_drop(command_buffer.id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuShaderModule for WasiWebGpuCtx<'a> {
    fn label(&mut self, shader: Resource<webgpu::GpuShaderModule>) -> wasmtime::Result<String> {
        Ok(self.table.get(&shader)?.label.clone())
    }

    fn set_label(
        &mut self,
        shader: Resource<webgpu::GpuShaderModule>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&shader)?.label = label;
        Ok(())
    }

    fn drop(&mut self, shader: Resource<webgpu::GpuShaderModule>) -> wasmtime::Result<()> {
        let shader = self.table.delete(shader)?;
        self.instance.shader_module_drop(shader.id);
        Ok(())
    }
}

impl<T: Send> webgpu::HostGpuShaderModuleWithStore<T> for crate::HasWasiWebGpuCtx {
    async fn get_compilation_info(
        accessor: &Accessor<T, Self>,
        shader: Resource<webgpu::GpuShaderModule>,
    ) -> wasmtime::Result<Resource<webgpu::GpuCompilationInfo>> {
        accessor.with(|mut access| {
            let ctx = access.get();
            // wgpu compiles a shader as it makes its module, so there is nothing to wait for.
            let messages = ctx.table.get(&shader)?.messages.clone();
            Ok(ctx.table.push(CompilationInfo { messages })?)
        })
    }
}

impl<'a> webgpu::HostGpuRenderPipeline for WasiWebGpuCtx<'a> {
    fn label(&mut self, pipeline: Resource<RenderPipeline>) -> wasmtime::Result<String> {
        Ok(self.table.get(&pipeline)?.label.clone())
    }

    fn set_label(
        &mut self,
        pipeline: Resource<RenderPipeline>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&pipeline)?.label = label;
        Ok(())
    }

    fn get_bind_group_layout(
        &mut self,
        pipeline: Resource<RenderPipeline>,
        index: u32,
    ) -> wasmtime::Result<Resource<webgpu::GpuBindGroupLayout>> {
        let pipeline = self.table.get(&pipeline)?;
        let pipeline_id = pipeline.render_pipeline_id;
        let error_handler = Arc::clone(&pipeline.error_handler);
        let (id, err) =
            self.instance
                .render_pipeline_get_bind_group_layout(pipeline_id, index, None);
        error_handler.handle_possible_error(err);
        // https://www.w3.org/TR/webgpu/#dom-gpupipelinebase-getbindgrouplayout
        let label = String::new();
        Ok(self.table.push(Labeled { id, label })?)
    }

    fn drop(&mut self, pipeline: Resource<webgpu::GpuRenderPipeline>) -> wasmtime::Result<()> {
        let pipeline = self.table.delete(pipeline)?;
        self.instance
            .render_pipeline_drop(pipeline.render_pipeline_id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuAdapter for WasiWebGpuCtx<'a> {
    fn features(
        &mut self,
        adapter: Resource<webgpu::GpuAdapter>,
    ) -> wasmtime::Result<Resource<webgpu::GpuSupportedFeatures>> {
        let adapter = *(*self.table.get(&adapter)?);
        let features = self.instance.adapter_features(adapter);
        Ok(self.table.push(features)?)
    }

    fn limits(
        &mut self,
        adapter: Resource<webgpu::GpuAdapter>,
    ) -> wasmtime::Result<Resource<webgpu::GpuSupportedLimits>> {
        let adapter = *(*self.table.get(&adapter)?);
        let limits = self.instance.adapter_limits(adapter);
        Ok(self.table.push(limits)?)
    }

    fn info(
        &mut self,
        adapter: Resource<webgpu::GpuAdapter>,
    ) -> wasmtime::Result<Resource<webgpu::GpuAdapterInfo>> {
        let adapter_id = *(*self.table.get(&adapter)?);
        let info = self.instance.adapter_get_info(adapter_id);
        Ok(self.table.push(info)?)
    }

    fn drop(&mut self, adapter: Resource<webgpu::GpuAdapter>) -> wasmtime::Result<()> {
        let adapter_id = self.table.delete(adapter)?;
        if let Some(adapter_id) = Arc::into_inner(adapter_id) {
            self.instance.adapter_drop(adapter_id);
        }
        Ok(())
    }
}

impl<T: Send> webgpu::HostGpuAdapterWithStore<T> for crate::HasWasiWebGpuCtx {
    async fn request_device(
        accessor: &Accessor<T, Self>,
        adapter: Resource<webgpu::GpuAdapter>,
        descriptor: Option<webgpu::GpuDeviceDescriptor>,
    ) -> wasmtime::Result<Result<Resource<webgpu::GpuDevice>, webgpu::RequestDeviceError>> {
        accessor.with(|mut access| {
            let ctx = access.get();
            let table = ctx.table;
            let adapter = Arc::clone(table.get(&adapter)?);
            let label = descriptor
                .as_ref()
                .and_then(|d| d.label.clone())
                .unwrap_or_default();
            // https://www.w3.org/TR/webgpu/#dom-gpuobjectdescriptorbase-label
            let queue_label = descriptor
                .as_ref()
                .and_then(|d| d.default_queue.as_ref())
                .and_then(|q| q.label.clone())
                .unwrap_or_default();

            let mut descriptor = match descriptor {
                Some(desc) => {
                    // The limits are the device's to keep: the guest gave them up as it passed them.
                    let required_limits = match desc.required_limits {
                        Some(limits) => Some(table.delete(limits)?),
                        None => None,
                    };
                    // From the spec:
                    // > 1. If any of the following requirements are unmet:
                    // >  - The set of values in descriptor.requiredFeatures must be a subset of those in adapter.[[features]].
                    // > Then issue the following steps on contentTimeline and return:
                    // >  1. Reject promise with a TypeError.
                    // https://www.w3.org/TR/webgpu/#dom-gpuadapter-requestdevice
                    let required_features = match desc.required_features.map(|f| f.to_core(table)) {
                        Some(Ok(features)) => features,
                        Some(Err(feature)) => {
                            return Ok(Err(webgpu::RequestDeviceError {
                                kind: webgpu::RequestDeviceErrorKind::TypeError,
                                message: format!("{feature:?} is no feature of the adapter"),
                            }))
                        }
                        None => wgpu_types::Features::default(),
                    };
                    // From the spec:
                    // > 2. All of the requirements in the following steps must be met.
                    // >  2. For each [key, value] in descriptor.requiredLimits for which value is not undefined:
                    // >   1. key must be the name of a member of supported limits.
                    // > 3. If any are unmet, issue the following steps on contentTimeline and return:
                    // >  1. Reject promise with an OperationError.
                    let required_limits = match required_limits.as_ref().map(|l| l.to_core(table)) {
                        Some(Ok(limits)) => limits,
                        Some(Err(key)) => {
                            return Ok(Err(webgpu::RequestDeviceError {
                                kind: webgpu::RequestDeviceErrorKind::OperationError,
                                message: format!("{key} is the name of no limit"),
                            }))
                        }
                        None => wgpu_types::Limits::defaults(),
                    };
                    wgpu_types::DeviceDescriptor {
                        label: desc.label.map(|l| l.into()),
                        required_features,
                        required_limits,
                        // trace is not present in WebGPU
                        trace: wgpu_types::Trace::default(),
                        // Don't enable any experimental features
                        experimental_features: wgpu_types::ExperimentalFeatures::disabled(),
                        // memory_hints is not present in WebGPU, comes from options
                        memory_hints: ctx.options.device_memory_hints.clone(),
                    }
                }
                None => wgpu_types::DeviceDescriptor::default(),
            };

            // Immediates are no feature of WebGPU's for a device to be asked for, though they are one of wgpu's:
            // a device has them wherever its adapter does, with the size of them that WebGPU has every device have.
            // https://www.w3.org/TR/webgpu/#dom-supported-limits-maximmediatesize
            if ctx
                .instance
                .adapter_features(*adapter)
                .contains(wgpu_types::Features::IMMEDIATES)
            {
                descriptor.required_features |= wgpu_types::Features::IMMEDIATES;
                let limits = &mut descriptor.required_limits;
                let supported = ctx.instance.adapter_limits(*adapter).max_immediate_size;
                limits.max_immediate_size = limits.max_immediate_size.max(supported.min(64));
            }

            let device_queue_result =
                ctx.instance
                    .adapter_request_device(*adapter, &descriptor, None, None);

            Ok(match device_queue_result {
                Ok((device_id, queue_id)) => {
                    let lost = Arc::new(DeviceLost::default());
                    ctx.instance.device_set_device_lost_closure(
                        device_id,
                        Box::new({
                            let lost = Arc::clone(&lost);
                            move |reason, message| {
                                let reason = reason.into();
                                lost.set(DeviceLostInfo { reason, message })
                            }
                        }),
                    );
                    let device = table.push(Device {
                        device: device_id,
                        queue: Arc::new(queue_id),
                        adapter,
                        error_handler: Arc::new(ErrorHandler::default()),
                        registered: Arc::new(RegisteredDevice {
                            id: device_id,
                            instance: Arc::clone(ctx.instance),
                        }),
                        lost,
                        label,
                        queue_label: Arc::new(Mutex::new(queue_label)),
                    })?;
                    Ok(device)
                }

                Err(err) => {
                    let message = message(&err);
                    // https://www.w3.org/TR/webgpu/#dom-gpuadapter-requestdevice
                    match err {
                        wgpu_core::instance::RequestDeviceError::UnsupportedFeature(_) => {
                            // From the spec:
                            // > 1. If any of the following requirements are unmet:
                            // >  - The set of values in descriptor.requiredFeatures must be a subset of those in adapter.[[features]].
                            // > Then issue the following steps on contentTimeline and return:
                            // >  1. Reject promise with a TypeError.
                            Err(webgpu::RequestDeviceError {
                                kind: webgpu::RequestDeviceErrorKind::TypeError,
                                message,
                            })
                        }
                        // From the spec:
                        // > 2. All of the requirements in the following steps must be met.
                        // >  2. For each [key, value] in descriptor.requiredLimits for which value is not undefined:
                        // >   1. key must be the name of a member of supported limits.
                        // >   2. value must be no better than adapter.[[limits]][key].
                        // >   3. If key’s class is alignment, value must be a power of 2 less than 232.
                        // > 3. If any are unmet, issue the following steps on contentTimeline and return:
                        // >  1. Reject promise with an OperationError.
                        //
                        // WebGPU has every other failure lose the device that it gives, which wgpu has none of to give:
                        // an adapter that makes no device is one that the operation failed on.
                        _ => Err(webgpu::RequestDeviceError {
                            kind: webgpu::RequestDeviceErrorKind::OperationError,
                            message,
                        }),
                    }
                }
            })
        })
    }
}

impl<'a> webgpu::HostGpuQueue for WasiWebGpuCtx<'a> {
    fn submit(
        &mut self,
        queue: Resource<webgpu::GpuQueue>,
        val: Vec<Resource<webgpu::GpuCommandBuffer>>,
    ) -> wasmtime::Result<()> {
        let command_buffers = val
            .into_iter()
            .map(|buffer| Ok(self.table.get(&buffer)?.id))
            .collect::<wasmtime::Result<Vec<_>>>()?;
        let queue = self.table.get(&queue)?;
        // https://www.w3.org/TR/webgpu/#dom-gpuqueue-submit
        let result = self
            .instance
            .queue_submit(*queue.queue_id, &command_buffers);
        queue
            .error_handler
            .handle_possible_error(result.err().map(|(_index, err)| err));
        Ok(())
    }

    fn write_buffer_with_copy(
        &mut self,
        queue: Resource<webgpu::GpuQueue>,
        buffer: Resource<webgpu::GpuBuffer>,
        buffer_offset: webgpu::GpuSize64,
        data: Vec<u8>,
        data_offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<Result<(), webgpu::WriteBufferError>> {
        let queue = self.table.get(&queue)?;
        let buffer_id = self.table.get(&buffer)?.buffer_id;
        // From the spec:
        // > 5. If any of the following conditions are unsatisfied, throw an OperationError and return.
        // >  - dataOffset ≤ dataSize.
        // >  - dataOffset + contentsSize ≤ dataSize.
        // https://www.w3.org/TR/webgpu/#dom-gpuqueue-writebuffer
        let Some(data) = part(&data, data_offset, size) else {
            return Ok(Err(webgpu::WriteBufferError {
                kind: webgpu::WriteBufferErrorKind::OperationError,
                message: format!(
                    "the bytes asked for are not among the {} that were given",
                    data.len()
                ),
            }));
        };
        let result =
            self.instance
                .queue_write_buffer(*queue.queue_id, buffer_id, buffer_offset, data);
        queue.error_handler.handle_possible_error(result.err());
        Ok(Ok(()))
    }

    fn write_texture_with_copy(
        &mut self,
        queue: Resource<webgpu::GpuQueue>,
        destination: webgpu::GpuTexelCopyTextureInfo,
        data: Vec<u8>,
        data_layout: webgpu::GpuTexelCopyBufferLayout,
        size: webgpu::GpuExtent3D,
    ) -> wasmtime::Result<()> {
        let queue = self.table.get(&queue)?;
        let result = self.instance.queue_write_texture(
            *queue.queue_id,
            &destination.to_core(self.table),
            &data,
            &data_layout.to_core(self.table),
            &size.to_core(self.table),
        );
        queue.error_handler.handle_possible_error(result.err());
        Ok(())
    }

    fn label(&mut self, queue: Resource<webgpu::GpuQueue>) -> wasmtime::Result<String> {
        Ok(self.table.get(&queue)?.label.lock().unwrap().clone())
    }

    fn set_label(
        &mut self,
        queue: Resource<webgpu::GpuQueue>,
        label: String,
    ) -> wasmtime::Result<()> {
        *self.table.get(&queue)?.label.lock().unwrap() = label;
        Ok(())
    }

    fn drop(&mut self, queue: Resource<webgpu::GpuQueue>) -> wasmtime::Result<()> {
        let queue = self.table.delete(queue)?;
        if let Some(queue_id) = Arc::into_inner(queue.queue_id) {
            self.instance.queue_drop(queue_id);
        }
        Ok(())
    }
}

impl<T: Send> webgpu::HostGpuQueueWithStore<T> for crate::HasWasiWebGpuCtx {
    async fn on_submitted_work_done(
        accessor: &Accessor<T, Self>,
        queue: Resource<webgpu::GpuQueue>,
    ) -> wasmtime::Result<()> {
        accessor
            .with(|mut access| -> wasmtime::Result<_> {
                let ctx = access.get();
                let instance = Arc::clone(ctx.instance);
                let queue = ctx.table.get(&queue)?;
                let queue_id = *queue.queue_id;
                let device = Arc::clone(&queue.device);
                let error_handler = Arc::clone(&queue.error_handler);

                Ok(CallbackFuture::new(Box::new(
                    move |resolve: Box<dyn FnOnce(()) + Send>| {
                        // What the queue was given to write is work too, which wgpu does only as something is next submitted.
                        let flushed = instance.queue_submit(queue_id, &[]);
                        error_handler.handle_possible_error(flushed.err().map(|(_index, err)| err));

                        let resolve = Arc::new(Mutex::new(Some(resolve)));
                        let done = Arc::clone(&resolve);
                        let submission_index = instance.queue_on_submitted_work_done(
                            queue_id,
                            Box::new(move || {
                                if let Some(resolve) = done.lock().unwrap().take() {
                                    resolve(())
                                }
                            }),
                        );
                        // wgpu calls back as the device is polled, which nothing else does.
                        device.wait(Some(submission_index));
                        // It hasn't where the device was lost first: the work is then as done as it will be.
                        // https://www.w3.org/TR/webgpu/#lose-the-device
                        let resolve = resolve.lock().unwrap().take();
                        if let Some(resolve) = resolve {
                            resolve(())
                        }
                    },
                )))
            })?
            .await;

        Ok(())
    }
}

impl<'a> webgpu::HostGpuCommandEncoder for WasiWebGpuCtx<'a> {
    fn begin_render_pass(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        descriptor: webgpu::GpuRenderPassDescriptor,
    ) -> wasmtime::Result<Resource<webgpu::GpuRenderPassEncoder>> {
        let command_encoder = self.table.get(&command_encoder)?;
        let command_encoder_id = command_encoder.command_encoder_id;
        let error_handler = Arc::clone(&command_encoder.error_handler);
        let label = descriptor.label.clone().unwrap_or_default();
        let timestamp_writes = descriptor.timestamp_writes.map(|tw| tw.to_core(self.table));
        // can't use to_core because depth_stencil_attachment is Option<&x>.
        let depth_stencil_attachment = descriptor
            .depth_stencil_attachment
            .map(|d| d.to_core(self.table));
        let descriptor = wgpu_core::command::RenderPassDescriptor {
            label: descriptor.label.map(|l| l.into()),
            color_attachments: descriptor
                .color_attachments
                .into_iter()
                .map(|c| c.map(|c| c.to_core(self.table)))
                .collect::<Vec<_>>()
                .into(),
            depth_stencil_attachment: depth_stencil_attachment.as_ref(),
            timestamp_writes: timestamp_writes.as_ref(),
            occlusion_query_set: descriptor
                .occlusion_query_set
                .map(|oqs| oqs.to_core(self.table)),
            // multiview_mask is not present in WebGPU
            multiview_mask: None,
            // TODO: self.max_draw_count not used
        };
        let (pass, err) = self
            .instance
            .command_encoder_begin_render_pass(command_encoder_id, &descriptor);

        error_handler.handle_possible_error(err);

        Ok(self.table.push(RenderPassEncoder {
            pass,
            error_handler,
            label,
        })?)
    }

    fn finish(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        descriptor: Option<webgpu::GpuCommandBufferDescriptor>,
    ) -> wasmtime::Result<Resource<webgpu::GpuCommandBuffer>> {
        let command_encoder = self.table.get(&command_encoder)?;
        let command_encoder_id = command_encoder.command_encoder_id;
        let error_handler = Arc::clone(&command_encoder.error_handler);
        let label = descriptor
            .as_ref()
            .and_then(|d| d.label.clone())
            .unwrap_or_default();
        let (id, err) = self.instance.command_encoder_finish(
            command_encoder_id,
            &descriptor
                .map(|d| d.to_core(self.table))
                .unwrap_or(wgpu_types::CommandBufferDescriptor::default()),
            None,
        );
        // dropping the label, which is that of the encoder: the error says of which it is.
        let err = err.map(|(_label, err)| err);
        error_handler.handle_possible_error(err);
        Ok(self.table.push(Labeled { id, label })?)
    }

    fn begin_compute_pass(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        descriptor: Option<webgpu::GpuComputePassDescriptor>,
    ) -> wasmtime::Result<Resource<webgpu::GpuComputePassEncoder>> {
        let command_encoder = self.table.get(&command_encoder)?;
        let command_encoder_id = command_encoder.command_encoder_id;
        let error_handler = Arc::clone(&command_encoder.error_handler);
        let label = descriptor
            .as_ref()
            .and_then(|d| d.label.clone())
            .unwrap_or_default();
        let (pass, err) = self.instance.command_encoder_begin_compute_pass(
            command_encoder_id,
            // can't use to_core because timestamp_writes is Option<&x>.
            &wgpu_core::command::ComputePassDescriptor {
                // TODO: can we get rid of the clone here?
                label: descriptor
                    .as_ref()
                    .and_then(|d| d.label.clone().map(|l| l.into())),
                timestamp_writes: descriptor
                    .and_then(|d| d.timestamp_writes.map(|tw| tw.to_core(self.table))),
            },
        );
        error_handler.handle_possible_error(err);
        Ok(self.table.push(ComputePassEncoder {
            pass,
            error_handler,
            label,
        })?)
    }

    fn copy_buffer_to_buffer(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        source: Resource<webgpu::GpuBuffer>,
        source_offset: Option<webgpu::GpuSize64>,
        destination: Resource<webgpu::GpuBuffer>,
        destination_offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let source = self.table.get(&source)?.buffer_id;
        let destination = self.table.get(&destination)?.buffer_id;
        // https://www.w3.org/TR/webgpu/#dom-gpucommandencoder-copybuffertobuffer
        // Note: wasi:webgpu uses `option` for offsets in lieu of the shorthand overload
        let result = self.instance.command_encoder_copy_buffer_to_buffer(
            command_encoder.command_encoder_id,
            source,
            source_offset.unwrap_or(0),
            destination,
            destination_offset.unwrap_or(0),
            size,
        );
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn copy_buffer_to_texture(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        source: webgpu::GpuTexelCopyBufferInfo,
        destination: webgpu::GpuTexelCopyTextureInfo,
        copy_size: webgpu::GpuExtent3D,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self.instance.command_encoder_copy_buffer_to_texture(
            command_encoder.command_encoder_id,
            &source.to_core(self.table),
            &destination.to_core(self.table),
            &copy_size.to_core(self.table),
        );
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn copy_texture_to_buffer(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        source: webgpu::GpuTexelCopyTextureInfo,
        destination: webgpu::GpuTexelCopyBufferInfo,
        copy_size: webgpu::GpuExtent3D,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self.instance.command_encoder_copy_texture_to_buffer(
            command_encoder.command_encoder_id,
            &source.to_core(self.table),
            &destination.to_core(self.table),
            &copy_size.to_core(self.table),
        );
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn copy_texture_to_texture(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        source: webgpu::GpuTexelCopyTextureInfo,
        destination: webgpu::GpuTexelCopyTextureInfo,
        copy_size: webgpu::GpuExtent3D,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self.instance.command_encoder_copy_texture_to_texture(
            command_encoder.command_encoder_id,
            &source.to_core(self.table),
            &destination.to_core(self.table),
            &copy_size.to_core(self.table),
        );
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn clear_buffer(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        buffer: Resource<webgpu::GpuBuffer>,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        let buffer_id = self.table.get(&buffer)?.buffer_id;
        let command_encoder = self.table.get(&command_encoder)?;
        // https://www.w3.org/TR/webgpu/#gpucommandencoder
        let result = self.instance.command_encoder_clear_buffer(
            command_encoder.command_encoder_id,
            buffer_id,
            offset.unwrap_or(0),
            size,
        );
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn resolve_query_set(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        query_set: Resource<webgpu::GpuQuerySet>,
        first_query: webgpu::GpuSize32,
        query_count: webgpu::GpuSize32,
        destination: Resource<webgpu::GpuBuffer>,
        destination_offset: webgpu::GpuSize64,
    ) -> wasmtime::Result<()> {
        let query_set_id = self.table.get(&query_set)?.id;
        let destination = self.table.get(&destination)?.buffer_id;
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self.instance.command_encoder_resolve_query_set(
            command_encoder.command_encoder_id,
            query_set_id,
            first_query,
            query_count,
            destination,
            destination_offset,
        );
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn label(&mut self, command_encoder: Resource<CommandEncoder>) -> wasmtime::Result<String> {
        Ok(self.table.get(&command_encoder)?.label.clone())
    }

    fn set_label(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&command_encoder)?.label = label;
        Ok(())
    }

    fn push_debug_group(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        group_label: String,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self
            .instance
            .command_encoder_push_debug_group(command_encoder.command_encoder_id, &group_label);
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn pop_debug_group(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self
            .instance
            .command_encoder_pop_debug_group(command_encoder.command_encoder_id);
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn insert_debug_marker(
        &mut self,
        command_encoder: Resource<CommandEncoder>,
        marker_label: String,
    ) -> wasmtime::Result<()> {
        let command_encoder = self.table.get(&command_encoder)?;
        let result = self
            .instance
            .command_encoder_insert_debug_marker(command_encoder.command_encoder_id, &marker_label);
        command_encoder
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn drop(&mut self, command_encoder: Resource<CommandEncoder>) -> wasmtime::Result<()> {
        let command_encoder = self.table.delete(command_encoder)?;
        self.instance
            .command_encoder_drop(command_encoder.command_encoder_id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuRenderPassEncoder for WasiWebGpuCtx<'a> {
    fn set_pipeline(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        pipeline: Resource<webgpu::GpuRenderPipeline>,
    ) -> wasmtime::Result<()> {
        let pipeline_id = self.table.get(&pipeline)?.render_pipeline_id;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_set_pipeline(&mut render_pass.pass, pipeline_id);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn draw(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        vertex_count: webgpu::GpuSize32,
        instance_count: Option<webgpu::GpuSize32>,
        first_vertex: Option<webgpu::GpuSize32>,
        first_instance: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
        let result = self.instance.render_pass_draw(
            &mut render_pass.pass,
            vertex_count,
            instance_count.unwrap_or(1),
            first_vertex.unwrap_or(0),
            first_instance.unwrap_or(0),
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn end(&mut self, render_pass: Resource<RenderPassEncoder>) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_end(&mut render_pass.pass);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_viewport(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        x: f32,
        y: f32,
        width: f32,
        height: f32,
        min_depth: f32,
        max_depth: f32,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_set_viewport(
            &mut render_pass.pass,
            x,
            y,
            width,
            height,
            min_depth,
            max_depth,
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_scissor_rect(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        x: webgpu::GpuIntegerCoordinate,
        y: webgpu::GpuIntegerCoordinate,
        width: webgpu::GpuIntegerCoordinate,
        height: webgpu::GpuIntegerCoordinate,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result =
            self.instance
                .render_pass_set_scissor_rect(&mut render_pass.pass, x, y, width, height);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_blend_constant(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        color: webgpu::GpuColor,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_set_blend_constant(&mut render_pass.pass, color.into());
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_stencil_reference(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        reference: webgpu::GpuStencilValue,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_set_stencil_reference(&mut render_pass.pass, reference);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn begin_occlusion_query(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        query_index: webgpu::GpuSize32,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_begin_occlusion_query(&mut render_pass.pass, query_index);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn end_occlusion_query(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_end_occlusion_query(&mut render_pass.pass);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn execute_bundles(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        bundles: Vec<Resource<webgpu::GpuRenderBundle>>,
    ) -> wasmtime::Result<()> {
        let render_bundle_ids = bundles
            .iter()
            .map(|bundle| Ok(self.table.get(bundle)?.id))
            .collect::<wasmtime::Result<Vec<_>>>()?;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_execute_bundles(&mut render_pass.pass, &render_bundle_ids);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn label(&mut self, render_pass: Resource<RenderPassEncoder>) -> wasmtime::Result<String> {
        Ok(self.table.get(&render_pass)?.label.clone())
    }

    fn set_label(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&render_pass)?.label = label;
        Ok(())
    }

    fn push_debug_group(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        group_label: String,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result =
            self.instance
                .render_pass_push_debug_group(&mut render_pass.pass, &group_label, 0);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn pop_debug_group(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self
            .instance
            .render_pass_pop_debug_group(&mut render_pass.pass);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn insert_debug_marker(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        marker_label: String,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result =
            self.instance
                .render_pass_insert_debug_marker(&mut render_pass.pass, &marker_label, 0);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_bind_group(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        index: webgpu::GpuIndex32,
        bind_group: Option<Resource<webgpu::GpuBindGroup>>,
        dynamic_offsets_data: Option<Vec<webgpu::GpuBufferDynamicOffset>>,
        dynamic_offsets_data_start: Option<webgpu::GpuSize64>,
        dynamic_offsets_data_length: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<Result<(), webgpu::SetBindGroupError>> {
        let bind_group = match bind_group {
            Some(bind_group) => Some(self.table.get(&bind_group)?.id),
            None => None,
        };
        let dynamic_offsets = match dynamic_offsets(
            &dynamic_offsets_data,
            dynamic_offsets_data_start,
            dynamic_offsets_data_length,
        ) {
            Ok(dynamic_offsets) => dynamic_offsets,
            Err(err) => return Ok(Err(err)),
        };
        let render_pass = self.table.get_mut(&render_pass)?;

        let result = self.instance.render_pass_set_bind_group(
            &mut render_pass.pass,
            index,
            bind_group,
            dynamic_offsets,
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(Ok(()))
    }

    fn set_index_buffer(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        buffer: Resource<webgpu::GpuBuffer>,
        index_format: webgpu::GpuIndexFormat,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        let buffer_id = self.table.get(&buffer)?.buffer_id;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_set_index_buffer(
            &mut render_pass.pass,
            buffer_id,
            index_format.into(),
            // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
            offset.unwrap_or(0),
            // wgpu has no size for a range of no bytes: it takes a size of 0 for all that follows `offset`.
            size.and_then(NonZeroU64::new),
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_vertex_buffer(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        slot: webgpu::GpuIndex32,
        buffer: Option<Resource<webgpu::GpuBuffer>>,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        // wgpu sets the buffer of a slot, and has nothing that unsets it.
        let Some(buffer) = buffer else {
            bail!("gpu-render-pass-encoder.set-vertex-buffer: wgpu can't unset the vertex buffer of slot {slot}");
        };
        let buffer_id = self.table.get(&buffer)?.buffer_id;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_set_vertex_buffer(
            &mut render_pass.pass,
            slot,
            buffer_id,
            // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
            offset.unwrap_or(0),
            // wgpu has no size for a range of no bytes: it takes a size of 0 for all that follows `offset`.
            size.and_then(NonZeroU64::new),
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn draw_indexed(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        index_count: webgpu::GpuSize32,
        instance_count: Option<webgpu::GpuSize32>,
        first_index: Option<webgpu::GpuSize32>,
        base_vertex: Option<webgpu::GpuSignedOffset32>,
        first_instance: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<()> {
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_draw_indexed(
            &mut render_pass.pass,
            index_count,
            // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
            instance_count.unwrap_or(1),
            first_index.unwrap_or(0),
            base_vertex.unwrap_or(0),
            first_instance.unwrap_or(0),
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn draw_indirect(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        indirect_buffer: Resource<webgpu::GpuBuffer>,
        indirect_offset: webgpu::GpuSize64,
    ) -> wasmtime::Result<()> {
        let indirect_buffer = self.table.get(&indirect_buffer)?.buffer_id;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_draw_indirect(
            &mut render_pass.pass,
            indirect_buffer,
            indirect_offset,
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn draw_indexed_indirect(
        &mut self,
        render_pass: Resource<RenderPassEncoder>,
        indirect_buffer: Resource<webgpu::GpuBuffer>,
        indirect_offset: webgpu::GpuSize64,
    ) -> wasmtime::Result<()> {
        let indirect_buffer = self.table.get(&indirect_buffer)?.buffer_id;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result = self.instance.render_pass_draw_indexed_indirect(
            &mut render_pass.pass,
            indirect_buffer,
            indirect_offset,
        );
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_immediates(
        &mut self,
        render_pass: Resource<webgpu::GpuRenderPassEncoder>,
        range_offset: u32,
        data: Vec<u8>,
        data_offset: Option<u64>,
        data_size: Option<u64>,
    ) -> wasmtime::Result<()> {
        let data = immediates(
            "gpu-render-pass-encoder.set-immediates",
            &data,
            data_offset,
            data_size,
        )?;
        let render_pass = self.table.get_mut(&render_pass)?;
        let result =
            self.instance
                .render_pass_set_immediates(&mut render_pass.pass, range_offset, data);
        render_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn drop(&mut self, render_pass: Resource<RenderPassEncoder>) -> wasmtime::Result<()> {
        self.table.delete(render_pass)?;
        Ok(())
    }
}

// Nothing of wasi:webgpu gives a `gpu-uncaptured-error-event`: `GpuDevice.on-uncaptured-error` is a stream of the errors themselves. So no guest has one to call these with.
impl<'a> webgpu::HostGpuUncapturedErrorEvent for WasiWebGpuCtx<'a> {
    // fn new(
    //     &mut self,
    //     _type_: String,
    //     _gpu_uncaptured_error_event_init_dict: webgpu::GpuUncapturedErrorEventInit,
    // ) -> Resource<webgpu::GpuUncapturedErrorEvent> {
    //     todo!()
    // }

    fn error(
        &mut self,
        _self_: Resource<webgpu::GpuUncapturedErrorEvent>,
    ) -> wasmtime::Result<Resource<webgpu::GpuError>> {
        bail!("gpu-uncaptured-error-event.error: there is no such event")
    }

    fn drop(&mut self, _error: Resource<webgpu::GpuUncapturedErrorEvent>) -> wasmtime::Result<()> {
        bail!("gpu-uncaptured-error-event.drop: there is no such event")
    }
}
// impl<'a> webgpu::HostGpuInternalError for WasiWebGpu<'a> {
//     fn new(&mut self, _message: String) -> Resource<webgpu::GpuInternalError> {
//         todo!()
//     }

//     fn message(&mut self, _self_: Resource<webgpu::GpuInternalError>) -> String {
//         todo!()
//     }

//     fn drop(&mut self, error: Resource<webgpu::GpuInternalError>) -> wasmtime::Result<()> {
//         self.table.delete(error)?;
//         Ok(())
//     }
// }
// impl<'a> webgpu::HostGpuOutOfMemoryError for WasiWebGpu<'a> {
//     fn new(&mut self, _message: String) -> Resource<webgpu::GpuOutOfMemoryError> {
//         todo!()
//     }

//     fn message(&mut self, _self_: Resource<webgpu::GpuOutOfMemoryError>) -> String {
//         todo!()
//     }

//     fn drop(&mut self, error: Resource<webgpu::GpuOutOfMemoryError>) -> wasmtime::Result<()> {
//         self.table.delete(error)?;
//         Ok(())
//     }
// }
// impl<'a> webgpu::HostGpuValidationError for WasiWebGpu<'a> {
//     fn new(&mut self, _message: String) -> Resource<webgpu::GpuValidationError> {
//         todo!()
//     }

//     fn message(&mut self, _self_: Resource<webgpu::GpuValidationError>) -> String {
//         todo!()
//     }

//     fn drop(&mut self, error: Resource<webgpu::GpuValidationError>) -> wasmtime::Result<()> {
//         self.table.delete(error)?;
//         Ok(())
//     }
// }
impl<'a> webgpu::HostGpuError for WasiWebGpuCtx<'a> {
    fn message(&mut self, error: Resource<webgpu::GpuError>) -> wasmtime::Result<String> {
        let error = self.table.get(&error)?;
        Ok(error.message.clone())
    }

    fn kind(
        &mut self,
        error: Resource<webgpu::GpuError>,
    ) -> wasmtime::Result<webgpu::GpuErrorKind> {
        let error = self.table.get(&error)?;
        Ok(error.kind)
    }

    fn drop(&mut self, _error: Resource<webgpu::GpuError>) -> wasmtime::Result<()> {
        self.table.delete(_error)?;
        Ok(())
    }
}
impl<'a> webgpu::HostGpuDeviceLostInfo for WasiWebGpuCtx<'a> {
    fn reason(
        &mut self,
        info: Resource<webgpu::GpuDeviceLostInfo>,
    ) -> wasmtime::Result<webgpu::GpuDeviceLostReason> {
        let info = self.table.get(&info)?;
        Ok(info.reason)
    }

    fn message(&mut self, info: Resource<webgpu::GpuDeviceLostInfo>) -> wasmtime::Result<String> {
        let info = self.table.get(&info)?;
        Ok(info.message.clone())
    }

    fn drop(&mut self, info: Resource<webgpu::GpuDeviceLostInfo>) -> wasmtime::Result<()> {
        self.table.delete(info)?;
        Ok(())
    }
}
// Nothing of wasi:webgpu gives a `gpu-canvas-context`: a surface of wasi-gfx has a context of its own. So no guest has one to call these with.
impl<'a> webgpu::HostGpuCanvasContext for WasiWebGpuCtx<'a> {
    fn configure(
        &mut self,
        _self_: Resource<webgpu::GpuCanvasContext>,
        _configuration: webgpu::GpuCanvasConfiguration,
    ) -> wasmtime::Result<()> {
        bail!("gpu-canvas-context.configure: there is no such context")
    }

    fn get_configuration(
        &mut self,
        _self_: Resource<webgpu::GpuCanvasContext>,
    ) -> wasmtime::Result<Option<webgpu::GpuCanvasConfigurationOwned>> {
        bail!("gpu-canvas-context.get-configuration: there is no such context")
    }

    fn unconfigure(&mut self, _self_: Resource<webgpu::GpuCanvasContext>) -> wasmtime::Result<()> {
        bail!("gpu-canvas-context.unconfigure: there is no such context")
    }

    fn get_current_texture(
        &mut self,
        _self_: Resource<webgpu::GpuCanvasContext>,
    ) -> wasmtime::Result<Resource<webgpu::GpuTexture>> {
        bail!("gpu-canvas-context.get-current-texture: there is no such context")
    }

    fn drop(&mut self, _rep: Resource<webgpu::GpuCanvasContext>) -> wasmtime::Result<()> {
        bail!("gpu-canvas-context.drop: there is no such context")
    }
}
impl<'a> webgpu::HostGpuRenderBundle for WasiWebGpuCtx<'a> {
    fn label(&mut self, bundle: Resource<webgpu::GpuRenderBundle>) -> wasmtime::Result<String> {
        Ok(self.table.get(&bundle)?.label.clone())
    }

    fn set_label(
        &mut self,
        bundle: Resource<webgpu::GpuRenderBundle>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&bundle)?.label = label;
        Ok(())
    }

    fn drop(&mut self, bundle: Resource<webgpu::GpuRenderBundle>) -> wasmtime::Result<()> {
        let bundle = self.table.delete(bundle)?;
        self.instance.render_bundle_drop(bundle.id);
        Ok(())
    }
}
impl<'a> webgpu::HostGpuComputePassEncoder for WasiWebGpuCtx<'a> {
    fn set_pipeline(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        pipeline: Resource<webgpu::GpuComputePipeline>,
    ) -> wasmtime::Result<()> {
        let pipeline = self.table.get(&pipeline)?.compute_pipeline_id;
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result = self
            .instance
            .compute_pass_set_pipeline(&mut compute_pass.pass, pipeline);
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn dispatch_workgroups(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        workgroup_count_x: webgpu::GpuSize32,
        workgroup_count_y: Option<webgpu::GpuSize32>,
        workgroup_count_z: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<()> {
        let compute_pass = self.table.get_mut(&compute_pass)?;
        // https://www.w3.org/TR/webgpu/#gpucomputepassencoder
        let result = self.instance.compute_pass_dispatch_workgroups(
            &mut compute_pass.pass,
            workgroup_count_x,
            workgroup_count_y.unwrap_or(1),
            workgroup_count_z.unwrap_or(1),
        );
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn dispatch_workgroups_indirect(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        indirect_buffer: Resource<webgpu::GpuBuffer>,
        indirect_offset: webgpu::GpuSize64,
    ) -> wasmtime::Result<()> {
        let indirect_buffer = self.table.get(&indirect_buffer)?.buffer_id;
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result = self.instance.compute_pass_dispatch_workgroups_indirect(
            &mut compute_pass.pass,
            indirect_buffer,
            indirect_offset,
        );
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn end(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
    ) -> wasmtime::Result<()> {
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result = self.instance.compute_pass_end(&mut compute_pass.pass);
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn label(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
    ) -> wasmtime::Result<String> {
        Ok(self.table.get(&compute_pass)?.label.clone())
    }

    fn set_label(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&compute_pass)?.label = label;
        Ok(())
    }

    fn push_debug_group(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        group_label: String,
    ) -> wasmtime::Result<()> {
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result =
            self.instance
                .compute_pass_push_debug_group(&mut compute_pass.pass, &group_label, 0);
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn pop_debug_group(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
    ) -> wasmtime::Result<()> {
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result = self
            .instance
            .compute_pass_pop_debug_group(&mut compute_pass.pass);
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn insert_debug_marker(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        label: String,
    ) -> wasmtime::Result<()> {
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result =
            self.instance
                .compute_pass_insert_debug_marker(&mut compute_pass.pass, &label, 0);
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn set_bind_group(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        index: webgpu::GpuIndex32,
        bind_group: Option<Resource<webgpu::GpuBindGroup>>,
        dynamic_offsets_data: Option<Vec<webgpu::GpuBufferDynamicOffset>>,
        dynamic_offsets_data_start: Option<webgpu::GpuSize64>,
        dynamic_offsets_data_length: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<Result<(), webgpu::SetBindGroupError>> {
        let bind_group = match bind_group {
            Some(bind_group) => Some(self.table.get(&bind_group)?.id),
            None => None,
        };
        let dynamic_offsets = match dynamic_offsets(
            &dynamic_offsets_data,
            dynamic_offsets_data_start,
            dynamic_offsets_data_length,
        ) {
            Ok(dynamic_offsets) => dynamic_offsets,
            Err(err) => return Ok(Err(err)),
        };
        let compute_pass = self.table.get_mut(&compute_pass)?;

        let result = self.instance.compute_pass_set_bind_group(
            &mut compute_pass.pass,
            index,
            bind_group,
            dynamic_offsets,
        );
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(Ok(()))
    }

    fn set_immediates(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
        range_offset: u32,
        data: Vec<u8>,
        data_offset: Option<u64>,
        data_size: Option<u64>,
    ) -> wasmtime::Result<()> {
        let data = immediates(
            "gpu-compute-pass-encoder.set-immediates",
            &data,
            data_offset,
            data_size,
        )?;
        let compute_pass = self.table.get_mut(&compute_pass)?;
        let result =
            self.instance
                .compute_pass_set_immediates(&mut compute_pass.pass, range_offset, data);
        compute_pass
            .error_handler
            .handle_possible_error(result.err());
        Ok(())
    }

    fn drop(
        &mut self,
        compute_pass: Resource<webgpu::GpuComputePassEncoder>,
    ) -> wasmtime::Result<()> {
        self.table.delete(compute_pass)?;
        Ok(())
    }
}
// impl<'a> webgpu::HostGpuPipelineError for WasiWebGpu<'a> {
//     fn new(
//         &mut self,
//         _message: Option<String>,
//         _options: webgpu::GpuPipelineErrorInit,
//     ) -> Resource<webgpu::GpuPipelineError> {
//         todo!()
//     }

//     fn reason(
//         &mut self,
//         _self_: Resource<webgpu::GpuPipelineError>,
//     ) -> webgpu::GpuPipelineErrorReason {
//         todo!()
//     }

//     fn drop(&mut self, error: Resource<webgpu::GpuPipelineError>) -> wasmtime::Result<()> {
//         self.table.delete(error)?;
//         Ok(())
//     }
// }
impl<'a> webgpu::HostGpuCompilationMessage for WasiWebGpuCtx<'a> {
    fn message(
        &mut self,
        message: Resource<webgpu::GpuCompilationMessage>,
    ) -> wasmtime::Result<String> {
        let message = self.table.get(&message)?;
        Ok(message.message.clone())
    }

    fn type_(
        &mut self,
        message: Resource<webgpu::GpuCompilationMessage>,
    ) -> wasmtime::Result<webgpu::GpuCompilationMessageType> {
        let message = self.table.get(&message)?;
        Ok(message.type_)
    }

    fn line_num(
        &mut self,
        message: Resource<webgpu::GpuCompilationMessage>,
    ) -> wasmtime::Result<u64> {
        let message = self.table.get(&message)?;
        Ok(message.line_num)
    }

    fn line_pos(
        &mut self,
        message: Resource<webgpu::GpuCompilationMessage>,
    ) -> wasmtime::Result<u64> {
        let message = self.table.get(&message)?;
        Ok(message.line_pos)
    }

    fn offset(
        &mut self,
        message: Resource<webgpu::GpuCompilationMessage>,
    ) -> wasmtime::Result<u64> {
        let message = self.table.get(&message)?;
        Ok(message.offset)
    }

    fn length(
        &mut self,
        message: Resource<webgpu::GpuCompilationMessage>,
    ) -> wasmtime::Result<u64> {
        let message = self.table.get(&message)?;
        Ok(message.length)
    }

    fn drop(&mut self, message: Resource<webgpu::GpuCompilationMessage>) -> wasmtime::Result<()> {
        self.table.delete(message)?;
        Ok(())
    }
}
impl<'a> webgpu::HostGpuCompilationInfo for WasiWebGpuCtx<'a> {
    fn messages(
        &mut self,
        info: Resource<webgpu::GpuCompilationInfo>,
    ) -> wasmtime::Result<Vec<Resource<webgpu::GpuCompilationMessage>>> {
        let messages = self.table.get(&info)?.messages.clone();
        messages
            .into_iter()
            .map(|message| Ok(self.table.push(message)?))
            .collect()
    }

    fn drop(&mut self, info: Resource<webgpu::GpuCompilationInfo>) -> wasmtime::Result<()> {
        self.table.delete(info)?;
        Ok(())
    }
}
impl<'a> webgpu::HostGpuQuerySet for WasiWebGpuCtx<'a> {
    fn destroy(&mut self, query_set: Resource<webgpu::GpuQuerySet>) -> wasmtime::Result<()> {
        // wgpu has nothing that destroys a query set: it frees one as it is dropped, and keeps one that is used after this valid.
        // https://github.com/gfx-rs/wgpu/issues/6495
        self.table.get(&query_set)?;
        Ok(())
    }

    fn type_(
        &mut self,
        query_set: Resource<webgpu::GpuQuerySet>,
    ) -> wasmtime::Result<webgpu::GpuQueryType> {
        Ok(self.table.get(&query_set)?.type_)
    }

    fn count(
        &mut self,
        query_set: Resource<webgpu::GpuQuerySet>,
    ) -> wasmtime::Result<webgpu::GpuSize32Out> {
        Ok(self.table.get(&query_set)?.count)
    }

    fn label(&mut self, query_set: Resource<webgpu::GpuQuerySet>) -> wasmtime::Result<String> {
        Ok(self.table.get(&query_set)?.label.clone())
    }

    fn set_label(
        &mut self,
        query_set: Resource<webgpu::GpuQuerySet>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&query_set)?.label = label;
        Ok(())
    }

    fn drop(&mut self, query_set: Resource<webgpu::GpuQuerySet>) -> wasmtime::Result<()> {
        let query_set = self.table.delete(query_set)?;
        self.instance.query_set_drop(query_set.id);
        Ok(())
    }
}
impl<'a> webgpu::HostGpuRenderBundleEncoder for WasiWebGpuCtx<'a> {
    fn finish(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        descriptor: Option<webgpu::GpuRenderBundleDescriptor>,
    ) -> wasmtime::Result<Resource<webgpu::GpuRenderBundle>> {
        let label = descriptor
            .as_ref()
            .and_then(|d| d.label.clone())
            .unwrap_or_default();
        let descriptor = descriptor
            .map(|d| d.to_core(self.table))
            .unwrap_or(wgpu_types::RenderBundleDescriptor::default());
        let bundle_encoder = self.table.get_mut(&bundle_encoder)?;
        // An encoder that is finished finishes again as one that wgpu makes no bundle of does.
        let device_id = bundle_encoder.device.id;
        let encoder = match bundle_encoder.encoder() {
            Some(_) => bundle_encoder.encoder.take(),
            None => None,
        }
        .unwrap_or_else(|| wgpu_core::command::RenderBundleEncoder::dummy(device_id));
        let (id, err) = self
            .instance
            .render_bundle_encoder_finish(encoder, &descriptor, None);
        bundle_encoder.error_handler.handle_possible_error(err);
        Ok(self.table.push(Labeled { id, label })?)
    }

    fn label(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
    ) -> wasmtime::Result<String> {
        Ok(self.table.get(&bundle_encoder)?.label.clone())
    }

    fn set_label(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&bundle_encoder)?.label = label;
        Ok(())
    }

    // wgpu keeps no debug groups or markers in a render bundle, which draws the same without them:
    // these do nothing, and nothing says that a group that is pushed is not popped.
    fn push_debug_group(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        _group_label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&bundle_encoder)?.encoder();
        Ok(())
    }

    fn pop_debug_group(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&bundle_encoder)?.encoder();
        Ok(())
    }

    fn insert_debug_marker(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        _marker_label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&bundle_encoder)?.encoder();
        Ok(())
    }

    fn set_bind_group(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        index: webgpu::GpuIndex32,
        bind_group: Option<Resource<webgpu::GpuBindGroup>>,
        dynamic_offsets_data: Option<Vec<webgpu::GpuBufferDynamicOffset>>,
        dynamic_offsets_data_start: Option<webgpu::GpuSize64>,
        dynamic_offsets_data_length: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<Result<(), webgpu::SetBindGroupError>> {
        let bind_group_id = match bind_group {
            Some(bind_group) => Some(self.table.get(&bind_group)?.id),
            None => None,
        };
        let dynamic_offsets = match dynamic_offsets(
            &dynamic_offsets_data,
            dynamic_offsets_data_start,
            dynamic_offsets_data_length,
        ) {
            Ok(dynamic_offsets) => dynamic_offsets,
            Err(err) => return Ok(Err(err)),
        };
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(Ok(()));
        };

        unsafe {
            wgpu_core::command::bundle_ffi::wgpu_render_bundle_set_bind_group(
                bundle_encoder,
                index,
                bind_group_id,
                dynamic_offsets.as_ptr(),
                dynamic_offsets.len(),
            )
        };
        Ok(Ok(()))
    }

    fn set_pipeline(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        pipeline: Resource<RenderPipeline>,
    ) -> wasmtime::Result<()> {
        let pipeline = self.table.get(&pipeline)?;
        let pipeline_id = pipeline.render_pipeline_id;
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_set_pipeline(
            bundle_encoder,
            pipeline_id,
        );
        Ok(())
    }

    fn set_index_buffer(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        buffer: Resource<webgpu::GpuBuffer>,
        index_format: webgpu::GpuIndexFormat,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        let buffer_id = self.table.get(&buffer)?.buffer_id;
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_set_index_buffer(
            bundle_encoder,
            buffer_id,
            index_format.into(),
            offset.unwrap_or(0),
            // wgpu has no size for a range of no bytes: it takes a size of 0 for all that follows `offset`.
            size.and_then(NonZeroU64::new),
        );
        Ok(())
    }

    fn set_vertex_buffer(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        slot: webgpu::GpuIndex32,
        buffer: Option<Resource<webgpu::GpuBuffer>>,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<()> {
        // wgpu sets the buffer of a slot, and has nothing that unsets it.
        let Some(buffer) = buffer else {
            bail!("gpu-render-bundle-encoder.set-vertex-buffer: wgpu can't unset the vertex buffer of slot {slot}");
        };
        let buffer_id = self.table.get(&buffer)?.buffer_id;
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_set_vertex_buffer(
            bundle_encoder,
            slot,
            buffer_id,
            offset.unwrap_or(0),
            // wgpu has no size for a range of no bytes: it takes a size of 0 for all that follows `offset`.
            size.and_then(NonZeroU64::new),
        );
        Ok(())
    }

    fn draw(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        vertex_count: webgpu::GpuSize32,
        instance_count: Option<webgpu::GpuSize32>,
        first_vertex: Option<webgpu::GpuSize32>,
        first_instance: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<()> {
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_draw(
            bundle_encoder,
            vertex_count,
            instance_count.unwrap_or(1),
            first_vertex.unwrap_or(0),
            first_instance.unwrap_or(0),
        );
        Ok(())
    }

    fn draw_indexed(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        index_count: webgpu::GpuSize32,
        instance_count: Option<webgpu::GpuSize32>,
        first_index: Option<webgpu::GpuSize32>,
        base_vertex: Option<webgpu::GpuSignedOffset32>,
        first_instance: Option<webgpu::GpuSize32>,
    ) -> wasmtime::Result<()> {
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        // https://www.w3.org/TR/webgpu/#gpurendercommandsmixin
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_draw_indexed(
            bundle_encoder,
            index_count,
            instance_count.unwrap_or(1),
            first_index.unwrap_or(0),
            base_vertex.unwrap_or(0),
            first_instance.unwrap_or(0),
        );
        Ok(())
    }

    fn draw_indirect(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        indirect_buffer: Resource<webgpu::GpuBuffer>,
        indirect_offset: webgpu::GpuSize64,
    ) -> wasmtime::Result<()> {
        let indirect_buffer = self.table.get(&indirect_buffer)?.buffer_id;
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_draw_indirect(
            bundle_encoder,
            indirect_buffer,
            indirect_offset,
        );
        Ok(())
    }

    fn draw_indexed_indirect(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        indirect_buffer: Resource<webgpu::GpuBuffer>,
        indirect_offset: webgpu::GpuSize64,
    ) -> wasmtime::Result<()> {
        let indirect_buffer = self.table.get(&indirect_buffer)?.buffer_id;
        let Some(bundle_encoder) = self.table.get_mut(&bundle_encoder)?.encoder() else {
            return Ok(());
        };
        wgpu_core::command::bundle_ffi::wgpu_render_bundle_draw_indexed_indirect(
            bundle_encoder,
            indirect_buffer,
            indirect_offset,
        );
        Ok(())
    }

    fn set_immediates(
        &mut self,
        bundle_encoder: Resource<webgpu::GpuRenderBundleEncoder>,
        range_offset: u32,
        data: Vec<u8>,
        data_offset: Option<u64>,
        data_size: Option<u64>,
    ) -> wasmtime::Result<()> {
        let data = immediates(
            "gpu-render-bundle-encoder.set-immediates",
            &data,
            data_offset,
            data_size,
        )?;
        let bundle_encoder = self.table.get_mut(&bundle_encoder)?;
        // wgpu panics on what a pass has be an error of validation: an offset or a size that is no multiple of 4 bytes, or a size that is no `u32`.
        let aligned = |n: usize| n.is_multiple_of(wgpu_types::IMMEDIATE_DATA_ALIGNMENT as usize);
        let size = u32::try_from(data.len()).ok();
        let (true, true, Some(size)) = (aligned(range_offset as usize), aligned(data.len()), size)
        else {
            bundle_encoder
                .error_handler
                .handle_possible_error(Some(ValidationError(format!(
                "Immediate data of {} bytes at offset {range_offset} is not aligned to {} bytes",
                data.len(),
                wgpu_types::IMMEDIATE_DATA_ALIGNMENT
            ))));
            return Ok(());
        };
        let Some(bundle_encoder) = bundle_encoder.encoder() else {
            return Ok(());
        };
        // SAFETY: `data` is `size` bytes.
        unsafe {
            wgpu_core::command::bundle_ffi::wgpu_render_bundle_set_immediates(
                bundle_encoder,
                range_offset,
                size,
                data.as_ptr(),
            )
        };
        Ok(())
    }

    fn drop(&mut self, encoder: Resource<webgpu::GpuRenderBundleEncoder>) -> wasmtime::Result<()> {
        self.table.delete(encoder)?;
        Ok(())
    }
}
impl<'a> webgpu::HostGpuComputePipeline for WasiWebGpuCtx<'a> {
    fn label(
        &mut self,
        pipeline: Resource<webgpu::GpuComputePipeline>,
    ) -> wasmtime::Result<String> {
        Ok(self.table.get(&pipeline)?.label.clone())
    }

    fn set_label(
        &mut self,
        pipeline: Resource<webgpu::GpuComputePipeline>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&pipeline)?.label = label;
        Ok(())
    }

    fn get_bind_group_layout(
        &mut self,
        compute_pipeline: Resource<webgpu::GpuComputePipeline>,
        index: u32,
    ) -> wasmtime::Result<Resource<webgpu::GpuBindGroupLayout>> {
        let pipeline = self.table.get(&compute_pipeline)?;
        let pipeline_id = pipeline.compute_pipeline_id;
        let error_handler = Arc::clone(&pipeline.error_handler);
        let (id, err) =
            self.instance
                .compute_pipeline_get_bind_group_layout(pipeline_id, index, None);
        error_handler.handle_possible_error(err);
        // https://www.w3.org/TR/webgpu/#dom-gpupipelinebase-getbindgrouplayout
        let label = String::new();
        Ok(self.table.push(Labeled { id, label })?)
    }

    fn drop(&mut self, pipeline: Resource<webgpu::GpuComputePipeline>) -> wasmtime::Result<()> {
        let pipeline = self.table.delete(pipeline)?;
        self.instance
            .compute_pipeline_drop(pipeline.compute_pipeline_id);
        Ok(())
    }
}
impl<'a> webgpu::HostGpuBindGroup for WasiWebGpuCtx<'a> {
    fn label(&mut self, bind_group: Resource<webgpu::GpuBindGroup>) -> wasmtime::Result<String> {
        Ok(self.table.get(&bind_group)?.label.clone())
    }

    fn set_label(
        &mut self,
        bind_group: Resource<webgpu::GpuBindGroup>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&bind_group)?.label = label;
        Ok(())
    }

    fn drop(&mut self, bind_group: Resource<webgpu::GpuBindGroup>) -> wasmtime::Result<()> {
        let bind_group = self.table.delete(bind_group)?;
        self.instance.bind_group_drop(bind_group.id);
        Ok(())
    }
}
impl<'a> webgpu::HostGpuPipelineLayout for WasiWebGpuCtx<'a> {
    fn label(&mut self, layout: Resource<webgpu::GpuPipelineLayout>) -> wasmtime::Result<String> {
        Ok(self.table.get(&layout)?.label.clone())
    }

    fn set_label(
        &mut self,
        layout: Resource<webgpu::GpuPipelineLayout>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&layout)?.label = label;
        Ok(())
    }

    fn drop(&mut self, layout: Resource<webgpu::GpuPipelineLayout>) -> wasmtime::Result<()> {
        let layout = self.table.delete(layout)?;
        self.instance.pipeline_layout_drop(layout.id);
        Ok(())
    }
}
impl<'a> webgpu::HostGpuBindGroupLayout for WasiWebGpuCtx<'a> {
    fn label(&mut self, layout: Resource<webgpu::GpuBindGroupLayout>) -> wasmtime::Result<String> {
        Ok(self.table.get(&layout)?.label.clone())
    }

    fn set_label(
        &mut self,
        layout: Resource<webgpu::GpuBindGroupLayout>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&layout)?.label = label;
        Ok(())
    }

    fn drop(&mut self, layout: Resource<webgpu::GpuBindGroupLayout>) -> wasmtime::Result<()> {
        let layout = self.table.delete(layout)?;
        self.instance.bind_group_layout_drop(layout.id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuSampler for WasiWebGpuCtx<'a> {
    fn label(&mut self, sampler: Resource<webgpu::GpuSampler>) -> wasmtime::Result<String> {
        Ok(self.table.get(&sampler)?.label.clone())
    }

    fn set_label(
        &mut self,
        sampler: Resource<webgpu::GpuSampler>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&sampler)?.label = label;
        Ok(())
    }

    fn drop(&mut self, sampler: Resource<webgpu::GpuSampler>) -> wasmtime::Result<()> {
        let sampler = self.table.delete(sampler)?;
        self.instance.sampler_drop(sampler.id);
        Ok(())
    }
}

impl<'a> webgpu::HostGpuBuffer for WasiWebGpuCtx<'a> {
    fn size(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
    ) -> wasmtime::Result<webgpu::GpuSize64Out> {
        let buffer = self.table.get(&buffer)?;
        Ok(buffer.size)
    }

    fn usage(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
    ) -> wasmtime::Result<webgpu::GpuBufferUsage> {
        let buffer = self.table.get(&buffer)?;
        buffer.usage.try_into()
    }

    fn map_state(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
    ) -> wasmtime::Result<webgpu::GpuBufferMapState> {
        let buffer = self.table.get(&buffer)?;
        Ok(buffer.map_state)
    }

    fn get_mapped_range_get_with_copy(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<Result<Vec<u8>, webgpu::GetMappedRangeError>> {
        let buffer = self.table.get(&buffer)?;
        let (ptr, len) = match mapped_range(self.instance, buffer, offset, size) {
            Ok(range) => range,
            Err(err) => return Ok(Err(err)),
        };
        // SAFETY: wgpu gave `len` bytes of a buffer that is mapped, which stay mapped while they are copied.
        let data = unsafe { slice::from_raw_parts(ptr.as_ptr(), len) };
        Ok(Ok(data.to_vec()))
    }

    fn get_mapped_range_set_with_copy(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
        data: Vec<u8>,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<Result<(), webgpu::GetMappedRangeError>> {
        let buffer = self.table.get(&buffer)?;
        let (ptr, len) = match mapped_range(self.instance, buffer, offset, size) {
            Ok(range) => range,
            Err(err) => return Ok(Err(err)),
        };
        // The bytes are written from the start of the range, which may be longer than they are, as an `ArrayBuffer` of it would be.
        if data.len() > len {
            return Ok(Err(webgpu::GetMappedRangeError {
                kind: webgpu::GetMappedRangeErrorKind::OperationError,
                message: format!(
                    "{} bytes are more than the {len} of the range that is written",
                    data.len()
                ),
            }));
        }
        // What is written to a range that is mapped to be read is never in the buffer, so nothing is: wgpu may have mapped such memory to be read only.
        // https://www.w3.org/TR/webgpu/#dom-gpubuffer-unmap
        if buffer.map_mode == wgpu_core::device::HostMap::Write {
            // SAFETY: wgpu gave `len` bytes of a buffer that is mapped to be written, which stay mapped while they are.
            let range = unsafe { slice::from_raw_parts_mut(ptr.as_ptr(), len) };
            range[..data.len()].copy_from_slice(&data);
        }
        Ok(Ok(()))
    }

    fn unmap(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
    ) -> wasmtime::Result<Result<(), webgpu::UnmapError>> {
        let buffer = self.table.get_mut(&buffer)?;
        // https://www.w3.org/TR/webgpu/#dom-gpubuffer-unmap
        match self.instance.buffer_unmap(buffer.buffer_id) {
            // A buffer that is not mapped is unmapped to no effect.
            Ok(()) | Err(wgpu_core::resource::BufferAccessError::NotMapped) => {}
            Err(err) => buffer.error_handler.handle_possible_error(Some(err)),
        }
        buffer.map_state = webgpu::GpuBufferMapState::Unmapped;
        Ok(Ok(()))
    }

    fn destroy(&mut self, buffer: Resource<webgpu::GpuBuffer>) -> wasmtime::Result<()> {
        let buffer = self.table.get_mut(&buffer)?;
        self.instance.buffer_destroy(buffer.buffer_id);
        // https://www.w3.org/TR/webgpu/#dom-gpubuffer-destroy
        buffer.map_state = webgpu::GpuBufferMapState::Unmapped;
        Ok(())
    }

    fn label(&mut self, buffer: Resource<webgpu::GpuBuffer>) -> wasmtime::Result<String> {
        Ok(self.table.get(&buffer)?.label.clone())
    }

    fn set_label(
        &mut self,
        buffer: Resource<webgpu::GpuBuffer>,
        label: String,
    ) -> wasmtime::Result<()> {
        self.table.get_mut(&buffer)?.label = label;
        Ok(())
    }

    fn drop(&mut self, buffer: Resource<webgpu::GpuBuffer>) -> wasmtime::Result<()> {
        let buffer = self.table.delete(buffer)?;
        self.instance.buffer_drop(buffer.buffer_id);
        Ok(())
    }
}

impl<T: Send> webgpu::HostGpuBufferWithStore<T> for crate::HasWasiWebGpuCtx {
    async fn map_async(
        accessor: &Accessor<T, Self>,
        buffer: Resource<webgpu::GpuBuffer>,
        mode: webgpu::GpuMapMode,
        offset: Option<webgpu::GpuSize64>,
        size: Option<webgpu::GpuSize64>,
    ) -> wasmtime::Result<Result<(), webgpu::MapAsyncError>> {
        // https://www.w3.org/TR/webgpu/#gpubuffer
        let offset = offset.unwrap_or(0);

        accessor.with(|mut access| -> wasmtime::Result<_> {
            let ctx = access.get();
            let buffer = ctx.table.get_mut(&buffer)?;

            // source: https://www.w3.org/TR/webgpu/#typedefdef-gpumapmodeflags
            // from the spec
            // > 3. If any of the following conditions are unsatisfied:
            // >     - mode contains exactly one of READ or WRITE.
            // >   Then:
            // >     3. Generate a validation error.
            let map_mode = if mode == webgpu::GpuMapMode::READ {
                wgpu_core::device::HostMap::Read
            } else if mode == webgpu::GpuMapMode::WRITE {
                wgpu_core::device::HostMap::Write
            } else {
                let err = ValidationError(
                    "A buffer is mapped to be read or to be written, and not to be both or neither"
                        .to_string(),
                );
                let message = err.to_string();
                buffer.error_handler.handle_possible_error(Some(err));
                return Ok(Err(webgpu::MapAsyncError {
                    kind: webgpu::MapAsyncErrorKind::OperationError,
                    message,
                }));
            };

            // What the queue was given to write to the buffer is to be read from it, which wgpu writes only as something is next submitted.
            if map_mode == wgpu_core::device::HostMap::Read {
                if let Some(queue) = buffer.queue.upgrade() {
                    let flushed = ctx.instance.queue_submit(*queue, &[]);
                    buffer
                        .error_handler
                        .handle_possible_error(flushed.err().map(|(_index, err)| err));
                }
            }

            let mapped = Arc::new(Mutex::new(None));
            let op = wgpu_core::resource::BufferMapOperation {
                host: map_mode,
                callback: Some(Box::new({
                    let mapped = Arc::clone(&mapped);
                    move |result| *mapped.lock().unwrap() = Some(result)
                })),
            };
            let result = ctx
                .instance
                .buffer_map_async(buffer.buffer_id, offset, size, op)
                .and_then(|submission_index| {
                    // wgpu calls back as the device is polled, which nothing else does: it has by the time what the buffer waits for is done.
                    buffer.device.wait(Some(submission_index));
                    let result = mapped.lock().unwrap().take();
                    // It hasn't where the device was lost first.
                    result.unwrap_or(Err(wgpu_core::resource::BufferAccessError::MapAborted))
                });

            Ok(match result {
                Ok(()) => {
                    buffer.map_state = webgpu::GpuBufferMapState::Mapped;
                    buffer.map_mode = map_mode;
                    Ok(())
                }
                Err(err) => {
                    let message = message(&err);
                    // From the spec:
                    // > 1. If this.[[pending_map]] is not null:
                    // >  1. Issue the early-reject steps and return.
                    // > 7. If any of the following conditions are unsatisfied: [...]
                    // >  3. Generate a validation error.
                    // Either way the promise is rejected with an OperationError, or with an AbortError where the buffer was unmapped before it was mapped.
                    // https://www.w3.org/TR/webgpu/#dom-gpubuffer-mapasync
                    let kind = match err {
                        wgpu_core::resource::BufferAccessError::MapAborted => {
                            webgpu::MapAsyncErrorKind::AbortError
                        }
                        wgpu_core::resource::BufferAccessError::MapAlreadyPending => {
                            webgpu::MapAsyncErrorKind::OperationError
                        }
                        err => {
                            buffer.error_handler.handle_possible_error(Some(err));
                            webgpu::MapAsyncErrorKind::OperationError
                        }
                    };
                    Err(webgpu::MapAsyncError { kind, message })
                }
            })
        })
    }
}

impl<'a> webgpu::HostGpu for WasiWebGpuCtx<'a> {
    fn get_preferred_canvas_format(
        &mut self,
        _gpu: Resource<webgpu::Gpu>,
    ) -> wasmtime::Result<webgpu::GpuTextureFormat> {
        Ok(PREFERRED_CANVAS_FORMAT)
    }

    fn wgsl_language_features(
        &mut self,
        _self_: Resource<webgpu::Gpu>,
    ) -> wasmtime::Result<Resource<webgpu::WgslLanguageFeatures>> {
        Ok(self.table.push(WgslLanguageFeatures::new())?)
    }

    fn drop(&mut self, _gpu: Resource<webgpu::Gpu>) -> wasmtime::Result<()> {
        // not actually a resource in the table
        Ok(())
    }
}

impl<T: Send> webgpu::HostGpuWithStore<T> for crate::HasWasiWebGpuCtx {
    async fn request_adapter(
        accessor: &Accessor<T, Self>,
        _gpu: Resource<webgpu::Gpu>,
        options: Option<webgpu::GpuRequestAdapterOptions>,
    ) -> wasmtime::Result<Option<Resource<webgpu::GpuAdapter>>> {
        accessor.with(|mut access: Access<'_, T, crate::HasWasiWebGpuCtx>| {
            let ctx = access.get();
            let adapter = ctx.instance.request_adapter(
                &options
                    .map(|o| o.to_core(ctx.table))
                    .unwrap_or(wgpu_types::RequestAdapterOptions::default()),
                wgpu_types::Backends::all(),
                None,
            );
            Ok(match adapter {
                Ok(adapter) => {
                    let adapter = Arc::new(adapter);
                    let adapter = ctx.table.push(adapter)?;
                    Some(adapter)
                }
                Err(wgpu_types::RequestAdapterError::NotFound { .. }) => {
                    log::warn!("GPU adapter not found");
                    None
                }
                // WebGPU has every failure to find an adapter give none.
                // https://www.w3.org/TR/webgpu/#dom-gpu-requestadapter
                Err(e) => {
                    log::warn!("Failed to get gpu adapter: {e:?}");
                    None
                }
            })
        })
    }
}

impl<'a> webgpu::HostGpuAdapterInfo for WasiWebGpuCtx<'a> {
    // Each is what wgpu knows of the adapter that WebGPU has a place for, and empty where it knows nothing.
    // https://www.w3.org/TR/webgpu/#gpuadapterinfo
    // take ideas from https://bugzilla.mozilla.org/show_bug.cgi?id=1831994
    // keep an eye on https://github.com/gfx-rs/wgpu/issues/8649
    fn vendor(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<String> {
        let adapter_info = self.table.get(&adapter_info)?;
        // The name of the vendor, or its PCI id where wgpu has no name for it.
        Ok(
            match (vendor_name(adapter_info.vendor), adapter_info.vendor) {
                (Some(name), _) => name.to_string(),
                (None, 0) => String::new(),
                (None, id) => format!("{id:#06x}"),
            },
        )
    }

    fn architecture(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<String> {
        // wgpu knows nothing of the family of GPUs that an adapter is of.
        self.table.get(&adapter_info)?;
        Ok(String::new())
    }

    fn device(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<String> {
        let adapter_info = self.table.get(&adapter_info)?;
        // The PCI id of the device, which is what its vendor knows it by.
        Ok(match adapter_info.device {
            0 => String::new(),
            id => format!("{id:#06x}"),
        })
    }

    fn description(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<String> {
        let adapter_info = self.table.get(&adapter_info)?;
        // The name that the driver gives the adapter, and then the driver and the backend that reach it.
        let driver = [&adapter_info.driver, &adapter_info.driver_info]
            .into_iter()
            .filter(|part| !part.is_empty())
            .fold(String::new(), |driver, part| driver + part + " ");
        Ok(format!(
            "{} ({driver}on {})",
            adapter_info.name, adapter_info.backend
        ))
    }

    fn subgroup_min_size(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<u32> {
        let adapter_info = self.table.get(&adapter_info)?;
        Ok(adapter_info.subgroup_min_size)
    }

    fn subgroup_max_size(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<u32> {
        let adapter_info = self.table.get(&adapter_info)?;
        Ok(adapter_info.subgroup_max_size)
    }

    fn is_fallback_adapter(
        &mut self,
        adapter_info: Resource<webgpu::GpuAdapterInfo>,
    ) -> wasmtime::Result<bool> {
        let adapter_info = self.table.get(&adapter_info)?;
        // wgpu in browser treats only cpu as fallback
        // https://github.com/gfx-rs/wgpu/blob/0d32f7e75604feeff976445576c234da377fa3df/wgpu/src/backend/webgpu.rs#L889-L893
        let is_fallback = match adapter_info.device_type {
            wgpu_types::DeviceType::IntegratedGpu
            | wgpu_types::DeviceType::DiscreteGpu
            | wgpu_types::DeviceType::VirtualGpu
            | wgpu_types::DeviceType::Other => false,
            wgpu_types::DeviceType::Cpu => true,
        };
        Ok(is_fallback)
    }

    fn drop(&mut self, info: Resource<webgpu::GpuAdapterInfo>) -> wasmtime::Result<()> {
        self.table.delete(info)?;
        Ok(())
    }
}
impl<'a> webgpu::HostWgslLanguageFeatures for WasiWebGpuCtx<'a> {
    fn has(
        &mut self,
        features: Resource<webgpu::WgslLanguageFeatures>,
        key: String,
    ) -> wasmtime::Result<bool> {
        let features = self.table.get(&features)?;
        Ok(features.has(&key))
    }

    fn drop(&mut self, features: Resource<webgpu::WgslLanguageFeatures>) -> wasmtime::Result<()> {
        self.table.delete(features)?;
        Ok(())
    }
}
impl<'a> webgpu::HostGpuSupportedFeatures for WasiWebGpuCtx<'a> {
    fn has(
        &mut self,
        features: Resource<webgpu::GpuSupportedFeatures>,
        query: String,
    ) -> wasmtime::Result<bool> {
        let features = self.table.get(&features)?;
        // TODO: disable the ones not present in the wgpu yet.
        Ok(match query.as_str() {
            "core-features-and-limits" => {
                // TODO: enable once wgpu does
                // features.contains(wgpu_types::Features::CORE_FEATURES_AND_LIMITS)
                false
            }
            "depth-clip-control" => features.contains(wgpu_types::Features::DEPTH_CLIP_CONTROL),
            "depth32float-stencil8" => {
                features.contains(wgpu_types::Features::DEPTH32FLOAT_STENCIL8)
            }
            "texture-compression-bc" => {
                features.contains(wgpu_types::Features::TEXTURE_COMPRESSION_BC)
            }
            "texture-compression-bc-sliced-3d" => {
                features.contains(wgpu_types::Features::TEXTURE_COMPRESSION_BC_SLICED_3D)
            }
            "texture-compression-etc2" => {
                features.contains(wgpu_types::Features::TEXTURE_COMPRESSION_ETC2)
            }
            "texture-compression-astc" => {
                features.contains(wgpu_types::Features::TEXTURE_COMPRESSION_ASTC)
            }
            "texture-compression-astc-sliced-3d" => {
                features.contains(wgpu_types::Features::TEXTURE_COMPRESSION_ASTC_SLICED_3D)
            }
            "timestamp-query" => features.contains(wgpu_types::Features::TIMESTAMP_QUERY),
            "indirect-first-instance" => {
                features.contains(wgpu_types::Features::INDIRECT_FIRST_INSTANCE)
            }
            "shader-f16" => features.contains(wgpu_types::Features::SHADER_F16),
            "rg11b10ufloat-renderable" => {
                features.contains(wgpu_types::Features::RG11B10UFLOAT_RENDERABLE)
            }
            "bgra8unorm-storage" => features.contains(wgpu_types::Features::BGRA8UNORM_STORAGE),
            "float32-filterable" => features.contains(wgpu_types::Features::FLOAT32_FILTERABLE),
            "float32-blendable" => features.contains(wgpu_types::Features::FLOAT32_BLENDABLE),
            "clip-distances" => features.contains(wgpu_types::Features::CLIP_DISTANCES),
            "dual-source-blending" => features.contains(wgpu_types::Features::DUAL_SOURCE_BLENDING),
            "subgroups" => {
                // TODO: enable once wgpu does
                // features.contains(wgpu_types::Features::SUBGROUPS)
                false
            }
            "texture-formats-tier1" => {
                // TODO: enable once wgpu does
                // features.contains(wgpu_types::Features::TEXTURE_FORMATS_TIER1)
                false
            }
            "texture-formats-tier2" => {
                // TODO: enable once wgpu does
                // features.contains(wgpu_types::Features::TEXTURE_FORMATS_TIER2)
                false
            }
            "primitive-index" => features.contains(wgpu_types::Features::PRIMITIVE_INDEX),
            "texture-component-swizzle" => {
                // TODO: enable once wgpu does
                // features.contains(wgpu_types::Features::TEXTURE_COMPONENT_SWIZZLE)
                false
            }
            name => {
                log::warn!("unknown feature name: {}", name);
                false
            }
        })
    }

    fn drop(&mut self, features: Resource<webgpu::GpuSupportedFeatures>) -> wasmtime::Result<()> {
        self.table.delete(features)?;
        Ok(())
    }
}
impl<'a> webgpu::HostGpuSupportedLimits for WasiWebGpuCtx<'a> {
    fn max_texture_dimension1_d(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_texture_dimension_1d)
    }

    fn max_texture_dimension2_d(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_texture_dimension_2d)
    }

    fn max_texture_dimension3_d(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_texture_dimension_3d)
    }

    fn max_texture_array_layers(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_texture_array_layers)
    }

    fn max_bind_groups(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_bind_groups)
    }

    fn max_bind_groups_plus_vertex_buffers(
        &mut self,
        _limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        // Not present in wgpu yet so rely on spec default
        // https://www.w3.org/TR/webgpu/#dom-supported-limits-maxbindgroupsplusvertexbuffers
        // TODO: take value from wgpu once implemented there
        Ok(24)
    }

    fn max_bindings_per_bind_group(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_bindings_per_bind_group)
    }

    fn max_dynamic_uniform_buffers_per_pipeline_layout(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_dynamic_uniform_buffers_per_pipeline_layout)
    }

    fn max_dynamic_storage_buffers_per_pipeline_layout(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_dynamic_storage_buffers_per_pipeline_layout)
    }

    fn max_sampled_textures_per_shader_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_sampled_textures_per_shader_stage)
    }

    fn max_samplers_per_shader_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_samplers_per_shader_stage)
    }

    fn max_storage_buffers_per_shader_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_buffers_per_shader_stage)
    }

    fn max_storage_textures_per_shader_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_textures_per_shader_stage)
    }

    fn max_uniform_buffers_per_shader_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_uniform_buffers_per_shader_stage)
    }

    fn max_uniform_buffer_binding_size(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u64> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_uniform_buffer_binding_size)
    }

    fn max_storage_buffer_binding_size(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u64> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_buffer_binding_size)
    }

    fn min_uniform_buffer_offset_alignment(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.min_uniform_buffer_offset_alignment)
    }

    fn min_storage_buffer_offset_alignment(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.min_storage_buffer_offset_alignment)
    }

    fn max_vertex_buffers(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_vertex_buffers)
    }

    fn max_buffer_size(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u64> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_buffer_size)
    }

    fn max_vertex_attributes(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_vertex_attributes)
    }

    fn max_vertex_buffer_array_stride(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_vertex_buffer_array_stride)
    }

    fn max_inter_stage_shader_variables(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_inter_stage_shader_variables)
    }

    fn max_color_attachments(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_color_attachments)
    }

    fn max_color_attachment_bytes_per_sample(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_color_attachment_bytes_per_sample)
    }

    fn max_compute_workgroup_storage_size(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_compute_workgroup_storage_size)
    }

    fn max_compute_invocations_per_workgroup(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_compute_invocations_per_workgroup)
    }

    fn max_compute_workgroup_size_x(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_compute_workgroup_size_x)
    }

    fn max_compute_workgroup_size_y(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_compute_workgroup_size_y)
    }

    fn max_compute_workgroup_size_z(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_compute_workgroup_size_z)
    }

    fn max_compute_workgroups_per_dimension(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_compute_workgroups_per_dimension)
    }

    fn max_immediate_size(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        let limits = self.table.get(&limits)?;
        Ok(limits.max_immediate_size)
    }

    fn max_storage_buffers_in_vertex_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        // Not present in wgpu, which has one limit for every stage: that is the limit of each.
        // https://www.w3.org/TR/webgpu/#dom-supported-limits-maxstoragebuffersinvertexstage
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_buffers_per_shader_stage)
    }

    fn max_storage_buffers_in_fragment_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        // Not present in wgpu, which has one limit for every stage: that is the limit of each.
        // https://www.w3.org/TR/webgpu/#dom-supported-limits-maxstoragebuffersinfragmentstage
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_buffers_per_shader_stage)
    }

    fn max_storage_textures_in_vertex_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        // Not present in wgpu, which has one limit for every stage: that is the limit of each.
        // https://www.w3.org/TR/webgpu/#dom-supported-limits-maxstoragetexturesinvertexstage
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_textures_per_shader_stage)
    }

    fn max_storage_textures_in_fragment_stage(
        &mut self,
        limits: Resource<webgpu::GpuSupportedLimits>,
    ) -> wasmtime::Result<u32> {
        // Not present in wgpu, which has one limit for every stage: that is the limit of each.
        // https://www.w3.org/TR/webgpu/#dom-supported-limits-maxstoragetexturesinfragmentstage
        let limits = self.table.get(&limits)?;
        Ok(limits.max_storage_textures_per_shader_stage)
    }

    fn drop(&mut self, limits: Resource<webgpu::GpuSupportedLimits>) -> wasmtime::Result<()> {
        self.table.delete(limits)?;
        Ok(())
    }
}
