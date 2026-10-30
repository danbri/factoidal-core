export type SceneFrame = { width:number; height:number; data:number[]; wgsl?:string };
import { SurfaceLifecycle } from "./surface_lifecycle.ts";
import { requestRenderPlan, createPlanResources, textureUsage, commandInterpreter } from "./render_plan.ts";

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
    const plan=await requestRenderPlan("window",navigator.gpu.getPreferredCanvasFormat(),initial,device.limits);
    const context = surface.getContext("webgpu") as GPUCanvasContext;
    if (!context) throw new Error("Native surface has no WebGPU context");
    const resources=await createPlanResources(device,plan,initial.wgsl!);
    const {uniform}=resources;
    const presentation=new SurfaceLifecycle({
      configure(width,height) {
        surface.width=width;surface.height=height;
        context.configure({device,format:plan.format,alphaMode:plan.surface!.alphaMode,usage:textureUsage(plan.surface!.usage)});
      },
      prepare:()=>native.prepare?.(),
      acquire:()=>context.getCurrentTexture(),
      present:()=>surface.present(),
      state:native.state,
      ready:native.ready,
    },plan.format);
    return {
      configure:(width,height)=>presentation.configure(width,height),
      upload(data) { device.queue.writeBuffer(uniform,plan.uniform.offset,data); },
      draw() {
        const texture=presentation.acquire();
        if(!texture)return false;
        const interpreter=commandInterpreter(device,plan,resources,texture.createView(),{present:()=>presentation.present()});
        for(const command of plan.commands) {
          if(interpreter.step(command) instanceof Promise)throw new Error("Async command in a window render plan");
        }
        return true;
      },
      dispose() { context.unconfigure(); uniform.destroy(); },
    };
  });
}
