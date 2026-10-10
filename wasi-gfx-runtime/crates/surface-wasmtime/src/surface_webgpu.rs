use crate::surface::MainThreadSpawner;
use raw_window_handle::{HasDisplayHandle, HasWindowHandle};
use std::marker::PhantomData;
use std::sync::Arc;
use wasi_gfx::surface::surface_webgpu;
use wasi_webgpu_wasmtime::reexports::{wgpu_core, wgpu_types};
use wasmtime::{
    bail,
    component::{HasData, Resource},
};

wasmtime::component::bindgen!({
    world: "wasi-gfx:surface/webgpu-imports",
    require_store_data_send: true,
    imports: {
        default: trappable,
    },
    with: {
        "wasi-gfx:surface/surface": crate::surface::wasi_gfx::surface::surface,
        "wasi:webgpu/webgpu": wasi_webgpu_wasmtime::wasi::webgpu::webgpu,
        "wasi-gfx:surface/surface-webgpu.context": Context,
    },
});

// types
pub struct Context {
    pub(crate) surface: surface_webgpu::Surface,
    pub(crate) surface_id: wgpu_core::id::SurfaceId,
    pub(crate) configuration: Option<ContextConfiguration>,
}

pub(crate) struct ContextConfiguration {
    device: Resource<wasi_webgpu_wasmtime::Device>,
    /// What wgpu was last given, for the size the window then had.
    core: wgpu_types::SurfaceConfiguration<Vec<wgpu_types::TextureFormat>>,
}

impl Context {
    /// Configures the wgpu surface as `configuration` has it, for the size
    /// the window is now, which wgpu takes no surface without.
    fn apply(
        &self,
        instance: &wgpu_core::global::Global,
        device_id: wgpu_core::id::DeviceId,
        configuration: &mut wgpu_types::SurfaceConfiguration<Vec<wgpu_types::TextureFormat>>,
    ) -> wasmtime::Result<()> {
        configuration.width = self.surface.width().max(1);
        configuration.height = self.surface.height().max(1);
        match instance.surface_configure(self.surface_id, device_id, configuration) {
            Some(err) => bail!("{err:#?}"),
            None => Ok(()),
        }
    }
}

// linker connection
pub fn add_to_linker<T>(l: &mut wasmtime::component::Linker<T>) -> wasmtime::Result<()>
where
    T: SurfaceWebgpuCtxView,
{
    wasi_gfx::surface::surface_webgpu::add_to_linker::<_, HasSurfaceWebgpu<T::Spawner>>(
        l,
        T::surface_webgpu_ctx,
    )?;
    Ok(())
}

pub trait SurfaceWebgpuCtxView: Send {
    /// Spawner used to run main-thread-only wgpu calls (e.g. surface creation).
    type Spawner: MainThreadSpawner;
    fn surface_webgpu_ctx(&mut self) -> SurfaceWebgpuCtx<'_, Self::Spawner>;
}

pub struct SurfaceWebgpuCtx<'a, S: MainThreadSpawner> {
    pub table: &'a mut wasmtime_wasi::ResourceTable,
    pub instance: &'a Arc<wasi_webgpu_wasmtime::reexports::wgpu_core::global::Global>,
    pub main_thread_spawner: &'a S,
}

struct HasSurfaceWebgpu<S>(PhantomData<S>);

impl<S: MainThreadSpawner> HasData for HasSurfaceWebgpu<S> {
    type Data<'a> = SurfaceWebgpuCtx<'a, S>;
}

// wasmtime trait impls
impl<'a, S: MainThreadSpawner> surface_webgpu::Host for SurfaceWebgpuCtx<'a, S> {}

impl<'a, S: MainThreadSpawner> surface_webgpu::HostContext for SurfaceWebgpuCtx<'a, S> {
    fn new(
        &mut self,
        surface: Resource<surface_webgpu::Surface>,
    ) -> wasmtime::Result<Resource<surface_webgpu::Context>> {
        let surface = self.table.get(&surface)?;
        let instance = Arc::clone(self.instance);

        let surface_id = futures::executor::block_on({
            let surface = surface.arc_clone();
            self.main_thread_spawner.spawn(move || {
                // SAFETY: The raw handles remain valid for the lifetime of the wgpu surface because
                // `Context` holds an `arc_clone()` of the surface alongside the `surface_id`.
                unsafe {
                    instance.instance_create_surface(
                        Some(surface.display_handle().unwrap().as_raw()),
                        surface.window_handle().unwrap().as_raw(),
                        None,
                    )
                }
            })
        })?;

        Ok(self.table.push(Context {
            surface: surface.arc_clone(),
            surface_id,
            configuration: None,
        })?)
    }

    fn configure(
        &mut self,
        context: Resource<surface_webgpu::Context>,
        configuration: surface_webgpu::ContextConfiguration,
    ) -> wasmtime::Result<()> {
        let device_id = *self.table.get(&configuration.device)?.device_id();

        let context = self.table.get_mut(&context)?;

        let mut core = wgpu_types::SurfaceConfiguration {
            // present in WebGPU, same defaults https://www.w3.org/TR/webgpu/#dictdef-gpucanvasconfiguration
            format: configuration.format.into(),
            usage: configuration
                .usage
                .unwrap_or(
                    wasi_webgpu_wasmtime::wasi::webgpu::webgpu::GpuTextureUsage::RENDER_ATTACHMENT,
                )
                .try_into()
                .unwrap(),
            view_formats: configuration
                .view_formats
                .into_iter()
                .flatten()
                .map(|f| f.into())
                .collect(),
            alpha_mode: configuration
                .alpha_mode
                .unwrap_or(wasi_webgpu_wasmtime::wasi::webgpu::webgpu::GpuCanvasAlphaMode::Opaque)
                .into(),
            // not present in WebGPU: the size is the window's, as a canvas's
            // is its own
            width: 0,
            height: 0,
            present_mode: wgpu_types::PresentMode::default(),
            desired_maximum_frame_latency: 2,
        };
        context.apply(self.instance, device_id, &mut core)?;

        context.configuration = Some(ContextConfiguration {
            device: configuration.device,
            core,
        });
        Ok(())
    }

    fn unconfigure(&mut self, context: Resource<surface_webgpu::Context>) -> wasmtime::Result<()> {
        let context = self.table.get_mut(&context)?;
        context.configuration = None;
        Ok(())
    }

    fn get_current_texture(
        &mut self,
        context: Resource<surface_webgpu::Context>,
    ) -> wasmtime::Result<Resource<surface_webgpu::GpuTexture>> {
        let Some(mut configuration) = self.table.get_mut(&context)?.configuration.take() else {
            bail!("Not configured")
        };
        let device_id = *self.table.get(&configuration.device)?.device_id();
        let context = self.table.get_mut(&context)?;

        // The texture is as large as the window is now, as that of a canvas
        // is as large as the canvas: a window that has changed size since it
        // was configured is configured again for it.
        let sized = (configuration.core.width, configuration.core.height);
        let size = (context.surface.width().max(1), context.surface.height().max(1));
        let mut outcome = Ok(());
        if size != sized {
            outcome = context.apply(self.instance, device_id, &mut configuration.core);
        }
        // What wgpu says is out of date or lost is configured again too, once.
        let mut texture_id = None;
        let mut tries = 0;
        while outcome.is_ok() && texture_id.is_none() {
            let output = self
                .instance
                .surface_get_current_texture(context.surface_id, None);
            match output {
                Ok(output) if output.texture.is_some() => texture_id = output.texture,
                Ok(_) if tries == 0 => {
                    outcome = context.apply(self.instance, device_id, &mut configuration.core);
                }
                Ok(output) => {
                    outcome = Err(wasmtime::format_err!(
                        "the surface gives no texture: {:?}",
                        output.status
                    ))
                }
                Err(err) => outcome = Err(wasmtime::format_err!("{err:#?}")),
            }
            tries += 1;
        }
        let device = Resource::new_borrow(configuration.device.rep());
        // What the texture is, for its getters to say: wgpu says nothing of
        // one that it gave.
        let descriptor = wgpu_types::TextureDescriptor {
            label: (),
            size: wgpu_types::Extent3d {
                width: configuration.core.width,
                height: configuration.core.height,
                depth_or_array_layers: 1,
            },
            mip_level_count: 1,
            sample_count: 1,
            dimension: wgpu_types::TextureDimension::D2,
            format: configuration.core.format,
            usage: configuration.core.usage,
            view_formats: configuration.core.view_formats.clone(),
        };
        context.configuration = Some(configuration);
        outcome?;
        let texture_id = texture_id.expect("there is one where nothing failed");

        let device: Resource<wasi_webgpu_wasmtime::Device> = device;
        let device = self.table.get(&device)?;

        // SAFETY: surface_get_current_texture will only give back a texture connected to the configured device.
        let texture = unsafe { device.connect_texture_with_descriptor(texture_id, &descriptor) };

        Ok(self.table.push(texture)?)
    }

    fn present(&mut self, context: Resource<surface_webgpu::Context>) -> wasmtime::Result<()> {
        let surface_id = self.table.get(&context)?.surface_id;

        self.instance.surface_present(surface_id)?;
        Ok(())
    }

    fn drop(&mut self, surface: Resource<surface_webgpu::Context>) -> wasmtime::Result<()> {
        self.table.delete(surface)?;
        Ok(())
    }
}
