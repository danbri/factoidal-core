use serde::Deserialize;
use wgpu::util::DeviceExt;

use crate::engine::{DeviceLimits, Engine};
use crate::window::Window;

type Result<T> = std::result::Result<T, Box<dyn std::error::Error>>;

#[derive(Deserialize)]
pub struct Scene {
    pub abi: String,
    pub width: u32,
    pub height: u32,
    pub data: Vec<f32>,
    pub tiles: Vec<u32>,
    pub wgsl: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Plan {
    abi: String,
    mode: String,
    format: String,
    width: u32,
    height: u32,
    uniform: Params,
    pipeline: Pipeline,
    bind_group: Binding,
    pass: Pass,
    draw: Draw,
    surface: Target,
    commands: Vec<Command>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Params {
    float_count: u32,
    bytes: u64,
    offset: u64,
    binding_type: String,
    usage: Vec<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Pipeline {
    layout: String,
    vertex_entry: String,
    fragment_entry: String,
    topology: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Binding {
    index: u32,
    layout_index: u32,
    binding: u32,
}

#[derive(Deserialize)]
struct Pass {
    clear: [f64; 4],
    load: String,
    store: String,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Draw {
    vertex_count: u32,
    instance_count: u32,
    first_vertex: u32,
    first_instance: u32,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct Target {
    alpha_mode: String,
    usage: Vec<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
enum Command {
    BeginPass,
    SetPipeline,
    SetBindGroup,
    Draw,
    EndPass,
    Submit,
    Present,
}

pub struct Gpu<'window> {
    surface: wgpu::Surface<'window>,
    device: wgpu::Device,
    queue: wgpu::Queue,
    format: wgpu::TextureFormat,
    config: Option<wgpu::SurfaceConfiguration>,
}

impl<'window> Gpu<'window> {
    pub fn open(window: &'window Window) -> Result<Self> {
        let instance = wgpu::Instance::new(&wgpu::InstanceDescriptor::default());
        let surface = window.surface(&instance)?;
        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            compatible_surface: Some(&surface),
            ..Default::default()
        }))?;
        let caps = surface.get_capabilities(&adapter);
        let format = [
            wgpu::TextureFormat::Bgra8Unorm,
            wgpu::TextureFormat::Rgba8Unorm,
        ]
        .into_iter()
        .find(|format| caps.formats.contains(format))
        .ok_or("native surface has no compatible RGBA8 format")?;
        if !caps.alpha_modes.contains(&wgpu::CompositeAlphaMode::Opaque) {
            return Err("native surface cannot present opaque frames".into());
        }
        let (device, queue) =
            pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
                required_limits: wgpu::Limits::default().using_resolution(adapter.limits()),
                ..Default::default()
            }))?;
        window.show();
        Ok(Self {
            surface,
            device,
            queue,
            format,
            config: None,
        })
    }

    pub fn present(&mut self, engine: &Engine, scene: Scene) -> Result<()> {
        if scene.abi != "lean-svg-v1" || scene.data.iter().any(|x| !x.is_finite()) {
            return Err("invalid native scene payload".into());
        }
        let size = [scene.width, scene.height];
        let format = if self.format == wgpu::TextureFormat::Bgra8Unorm {
            c"bgra8unorm"
        } else {
            c"rgba8unorm"
        };
        let limits = self.device.limits();
        let floats = u32::try_from(scene.data.len())?;
        let plan: Plan = serde_json::from_value(engine.render_plan(
            c"svg-window",
            format,
            size,
            floats,
            &DeviceLimits {
                uniform_bytes: limits.max_uniform_buffer_binding_size,
                texture_dimension: limits.max_texture_dimension_2d,
                storage_bytes: limits.max_storage_buffer_binding_size,
                buffer_bytes: u32::try_from(limits.max_buffer_size).unwrap_or(u32::MAX),
            },
        )?)?;

        let tile_bytes = u64::try_from(scene.tiles.len())?
            .checked_mul(4)
            .ok_or("tile data overflow")?;
        if plan.abi != "lean-render-plan-v1"
            || plan.mode != "svg-window"
            || [plan.width, plan.height] != size
            || plan.format.as_bytes() != format.to_bytes()
            || plan.uniform.float_count != floats
            || plan.uniform.bytes != u64::from(floats) * 4
            || plan.uniform.offset != 0
            || plan.uniform.binding_type != "read-only-storage"
            || plan.uniform.usage != ["storage", "copy-dst"]
            || plan.surface.usage != ["render-attachment"]
            || plan.surface.alpha_mode != "opaque"
            || plan.pipeline.layout != "auto"
            || plan.pipeline.topology != "triangle-list"
            || plan.pass.load != "clear"
            || plan.pass.store != "store"
            || tile_bytes == 0
            || tile_bytes > limits.max_buffer_size
            || tile_bytes > u64::from(limits.max_storage_buffer_binding_size)
        {
            return Err("unsupported or inconsistent native render plan".into());
        }
        let error_scope = self.device.push_error_scope(wgpu::ErrorFilter::Validation);
        let result = self.draw(scene, plan);
        if let Some(error) = pollster::block_on(error_scope.pop()) {
            return Err(error.into());
        }
        result
    }

    fn draw(&mut self, scene: Scene, plan: Plan) -> Result<()> {
        if self
            .config
            .as_ref()
            .is_none_or(|c| c.width != plan.width || c.height != plan.height)
        {
            let config = wgpu::SurfaceConfiguration {
                usage: wgpu::TextureUsages::RENDER_ATTACHMENT,
                format: self.format,
                width: plan.width,
                height: plan.height,
                present_mode: wgpu::PresentMode::Fifo,
                desired_maximum_frame_latency: 1,
                alpha_mode: wgpu::CompositeAlphaMode::Opaque,
                view_formats: vec![],
            };
            self.surface.configure(&self.device, &config);
            self.config = Some(config);
        }

        let shader = self
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: None,
                source: wgpu::ShaderSource::Wgsl(scene.wgsl.into()),
            });
        let pipeline = self
            .device
            .create_render_pipeline(&wgpu::RenderPipelineDescriptor {
                label: None,
                layout: None,
                vertex: wgpu::VertexState {
                    module: &shader,
                    entry_point: Some(&plan.pipeline.vertex_entry),
                    buffers: &[],
                    compilation_options: Default::default(),
                },
                fragment: Some(wgpu::FragmentState {
                    module: &shader,
                    entry_point: Some(&plan.pipeline.fragment_entry),
                    targets: &[Some(self.format.into())],
                    compilation_options: Default::default(),
                }),
                primitive: wgpu::PrimitiveState::default(),
                depth_stencil: None,
                multisample: wgpu::MultisampleState::default(),
                multiview_mask: None,
                cache: None,
            });
        let data = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: None,
                contents: &scene
                    .data
                    .into_iter()
                    .flat_map(f32::to_le_bytes)
                    .collect::<Vec<_>>(),
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            });
        let tiles = self
            .device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: None,
                contents: &scene
                    .tiles
                    .into_iter()
                    .flat_map(u32::to_le_bytes)
                    .collect::<Vec<_>>(),
                usage: wgpu::BufferUsages::STORAGE | wgpu::BufferUsages::COPY_DST,
            });
        // The lean-svg-v1 shader ABI puts the tile words immediately after the
        // parameter binding. The existing host binds the same two byte streams.
        let tile_binding = plan
            .bind_group
            .binding
            .checked_add(1)
            .ok_or("tile binding overflow")?;
        let group = self.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: None,
            layout: &pipeline.get_bind_group_layout(plan.bind_group.layout_index),
            entries: &[
                wgpu::BindGroupEntry {
                    binding: plan.bind_group.binding,
                    resource: data.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: tile_binding,
                    resource: tiles.as_entire_binding(),
                },
            ],
        });
        let mut texture = Some(self.surface.get_current_texture()?);
        let view = texture
            .as_ref()
            .unwrap()
            .texture
            .create_view(&wgpu::TextureViewDescriptor::default());
        let mut encoder = Some(
            self.device
                .create_command_encoder(&wgpu::CommandEncoderDescriptor::default()),
        );
        let mut pass: Option<wgpu::RenderPass<'static>> = None;
        for command in plan.commands {
            match command {
                Command::BeginPass if pass.is_none() => {
                    let [r, g, b, a] = plan.pass.clear;
                    let attachment = Some(wgpu::RenderPassColorAttachment {
                        view: &view,
                        depth_slice: None,
                        resolve_target: None,
                        ops: wgpu::Operations {
                            load: wgpu::LoadOp::Clear(wgpu::Color { r, g, b, a }),
                            store: wgpu::StoreOp::Store,
                        },
                    });
                    pass = Some(
                        encoder
                            .as_mut()
                            .ok_or("beginPass after submit")?
                            .begin_render_pass(&wgpu::RenderPassDescriptor {
                                color_attachments: &[attachment],
                                ..Default::default()
                            })
                            .forget_lifetime(),
                    );
                }
                Command::SetPipeline => pass
                    .as_mut()
                    .ok_or("setPipeline outside pass")?
                    .set_pipeline(&pipeline),
                Command::SetBindGroup => pass
                    .as_mut()
                    .ok_or("setBindGroup outside pass")?
                    .set_bind_group(plan.bind_group.index, &group, &[]),
                Command::Draw => {
                    let draw = &plan.draw;
                    let end_vertex = draw
                        .first_vertex
                        .checked_add(draw.vertex_count)
                        .ok_or("vertex range overflow")?;
                    let end_instance = draw
                        .first_instance
                        .checked_add(draw.instance_count)
                        .ok_or("instance range overflow")?;
                    pass.as_mut().ok_or("draw outside pass")?.draw(
                        draw.first_vertex..end_vertex,
                        draw.first_instance..end_instance,
                    );
                }
                Command::EndPass => drop(pass.take().ok_or("endPass outside pass")?),
                Command::Submit if pass.is_none() => {
                    self.queue
                        .submit([encoder.take().ok_or("duplicate submit")?.finish()]);
                }
                Command::Present if encoder.is_none() => {
                    texture.take().ok_or("duplicate present")?.present();
                }
                _ => return Err("out-of-order native GPU command".into()),
            }
        }
        if texture.is_some() {
            return Err("native plan did not present its frame".into());
        }
        Ok(())
    }
}
