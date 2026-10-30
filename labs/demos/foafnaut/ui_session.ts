export type SceneFrame = { width:number; height:number; data:number[]; wgsl?:string };
import { SurfaceLifecycle } from "./surface_lifecycle.ts";

export type FrameBackend = {
  configure: (width: number, height: number) => void;
  upload: (data: Float32Array<ArrayBuffer>) => void;
  draw: () => boolean;
  dispose: () => void;
};
export type SessionStats = {
  builds: number; frames: number; uploads: number; configurations: number;
};

// No resource construction appears in the frame loop. GPU allocation is a
// one-time backend factory; a resize only reconfigures the presentation surface.
export class PersistentSession {
  readonly stats: SessionStats = { builds: 1, frames: 0, uploads: 0, configurations: 0 };
  private width = 0;
  private height = 0;
  private disposed = false;
  private constructor(private backend: FrameBackend, private floatCount: number) {}
  static async create(initial: SceneFrame, build: (initial: SceneFrame) => Promise<FrameBackend>) {
    return new PersistentSession(await build(initial), initial.data.length);
  }
  render(frame: SceneFrame) {
    if (this.disposed) throw new Error("Render after session disposal");
    if (frame.data.length !== this.floatCount) throw new Error("Scene ABI changed; a new session is required");
    if (frame.width !== this.width || frame.height !== this.height) {
      this.backend.configure(frame.width, frame.height);
      this.width=frame.width; this.height=frame.height; this.stats.configurations++;
    }
    this.backend.upload(new Float32Array(frame.data)); this.stats.uploads++;
    if(!this.backend.draw())return false;
    this.stats.frames++;
    return true;
  }
  dispose() {
    if (!this.disposed) { this.disposed=true; this.backend.dispose(); }
  }
}

export async function createWindowSession(device: GPUDevice, surface: Deno.UnsafeWindowSurface, initial: SceneFrame,
  native:{prepare?:()=>void;state?:()=>unknown;ready?:()=>boolean}={}) {
  if (!initial.wgsl) throw new Error("Initial Lean UI response has no shader");
  return await PersistentSession.create(initial, async () => {
    const format = navigator.gpu.getPreferredCanvasFormat();
    const context = surface.getContext("webgpu") as GPUCanvasContext;
    if (!context) throw new Error("Native surface has no WebGPU context");
    const shader = device.createShaderModule({ code: initial.wgsl! });
    const diagnostics = await shader.getCompilationInfo();
    for (const message of diagnostics.messages) console.log(`${message.type} ${message.lineNum}:${message.linePos}: ${message.message}`);
    if (diagnostics.messages.some(m => m.type === "error")) throw new Error("Lean UI WGSL compilation failed");
    const pipeline = await device.createRenderPipelineAsync({
      layout:"auto", vertex:{module:shader,entryPoint:"vertex"},
      fragment:{module:shader,entryPoint:"fragment",targets:[{format}]},
      primitive:{topology:"triangle-list"},
    });
    const uniform = device.createBuffer({size:initial.data.length*4,usage:GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST});
    const bindGroup = device.createBindGroup({layout:pipeline.getBindGroupLayout(0),entries:[{binding:0,resource:{buffer:uniform}}]});
    const presentation=new SurfaceLifecycle({
      configure(width,height) {
        surface.width=width;surface.height=height;
        context.configure({device,format,alphaMode:"opaque"});
      },
      prepare:()=>native.prepare?.(),
      acquire:()=>context.getCurrentTexture(),
      present:()=>surface.present(),
      state:native.state,
      ready:native.ready,
    },format);
    return {
      configure:(width,height)=>presentation.configure(width,height),
      upload(data) { device.queue.writeBuffer(uniform,0,data); },
      draw() {
        const texture=presentation.acquire();
        if(!texture)return false;
        const encoder=device.createCommandEncoder();
        const pass=encoder.beginRenderPass({colorAttachments:[{
          view:texture.createView(),clearValue:[0,0,0,1],loadOp:"clear",storeOp:"store",
        }]});
        pass.setPipeline(pipeline); pass.setBindGroup(0,bindGroup); pass.draw(3); pass.end();
        device.queue.submit([encoder.finish()]); presentation.present();
        return true;
      },
      dispose() { context.unconfigure(); uniform.destroy(); },
    };
  });
}
