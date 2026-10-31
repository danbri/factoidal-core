// WebGPU/byte transport. Rendering descriptors and command order come from Lean.
import type { Artifact } from "./lean_generator.ts";
import { requestRenderPlan, createPlanResources, textureUsage, bufferUsage, commandInterpreter } from "./render_plan.ts";
type Renderable=Pick<Artifact,"width"|"height"|"data"|"wgsl"|"checks">;

export function unpad(padded: Uint8Array, width: number, height: number, stride: number) {
  const rgba = new Uint8Array(width * height * 4);
  for (let y = 0; y < height; y++) rgba.set(padded.subarray(y * stride, y * stride + width * 4), y * width * 4);
  return rgba;
}

export function encodePPM(rgba: Uint8Array, width: number, height: number) {
  const header = new TextEncoder().encode(`P6\n${width} ${height}\n255\n`);
  const image = new Uint8Array(header.length + width * height * 3);
  image.set(header);
  for (let i = 0; i < width * height; i++) image.set(rgba.subarray(i * 4, i * 4 + 3), header.length + i * 3);
  return image;
}

export function checkPixels(a: Renderable, rgba: Uint8Array) {
  if (rgba.length !== a.width * a.height * 4) throw new Error("Unexpected GPU readback size");
  for (const { x, y, rgb } of a.checks) {
    const offset = (y * a.width + x) * 4;
    if (rgb.some((v, i) => Math.abs(rgba[offset + i] - v) > 1) || rgba[offset + 3] !== 255) {
      throw new Error(`GPU readback mismatch at ${x},${y}: ${[...rgba.slice(offset, offset + 4)]}; Lean expected ${rgb}`);
    }
  }
}

// Resource lifetime is a host concern; descriptors and every draw/copy/map
// command remain supplied by Lean. Repeated frames keep device/pipeline/buffers.
export async function createOffscreenSession(a:Renderable,mode:"offscreen"|"svg-offscreen"="offscreen") {
  if(!navigator.gpu)throw new Error("WebGPU API absent; add --unstable-webgpu");
  const verification={...a,checks:a.checks.map(p=>({...p,rgb:[...p.rgb]}))};
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter)return null;
  console.log("GPU adapter:",adapter.info);
  const device=await adapter.requestDevice();
  let resources:Awaited<ReturnType<typeof createPlanResources>>|undefined;
  let texture:GPUTexture|undefined,readback:GPUBuffer|undefined;
  let closed=false,busy=false,failed=false,scope=false;
  const counters={devices:1,shaderModules:0,pipelines:0,buffers:0,textures:0,uploads:0,submissions:0,frames:0};
  const close=()=>{
    if(closed)return;
    if(busy)throw new Error("Cannot close GPU session during a frame");
    closed=true;
    const errors:unknown[]=[];
    for(const resource of [readback,texture,resources?.uniform,device])try{resource?.destroy();}catch(error){errors.push(error);}
    if(errors.length)console.warn("GPU session cleanup:",errors.map(String).join("; "));
  };
  try {
    device.pushErrorScope("validation");scope=true;
    const plan=await requestRenderPlan(mode,"rgba8unorm",a,device.limits);
    resources=await createPlanResources(device,plan,a.wgsl);
    counters.shaderModules=1;counters.pipelines=1;counters.buffers=1;
    device.queue.writeBuffer(resources.uniform,plan.uniform.offset,new Float32Array(a.data));counters.uploads++;
    texture=device.createTexture({size:[plan.width,plan.height,plan.texture!.depth],format:plan.format,usage:textureUsage(plan.texture!.usage)});counters.textures++;
    readback=device.createBuffer({size:plan.readback!.bytes,usage:bufferUsage(plan.readback!.usage)});counters.buffers++;
    const initialError=await device.popErrorScope();scope=false;
    if(initialError)throw new Error(initialError.message);
    return {
      adapterInfo:adapter.info,
      get stats(){return {...counters,closed,failed};},
      async draw():Promise<Uint8Array> {
        if(closed||failed)throw new Error("GPU session is closed or failed");
        if(busy)throw new Error("Concurrent GPU readbacks are unsupported");
        busy=true;
        try {
          device.pushErrorScope("validation");scope=true;
          const interpreter=commandInterpreter(device,plan,resources!,texture!.createView(),{texture,readback});
          for(const command of plan.commands){await interpreter.step(command);if(command==="submit")counters.submissions++;}
          const padded=interpreter.mapped();
          if(!padded)throw new Error("Lean offscreen plan did not return pixels");
          const rgba=unpad(padded,plan.width,plan.height,plan.readback!.bytesPerRow);
          const error=await device.popErrorScope();scope=false;
          if(error)throw new Error(error.message);
          checkPixels(verification,rgba);counters.frames++;
          return rgba;
        }catch(error){failed=true;throw error;}
        finally {
          if(scope){try{await device.popErrorScope();}catch{/* preserve frame error */}scope=false;}
          busy=false;
        }
      },
      close,
    };
  }catch(error){
    if(scope){try{await device.popErrorScope();}catch{/* preserve setup error */}scope=false;}
    close();throw error;
  }
}

export async function render(a:Renderable,mode:"offscreen"|"svg-offscreen"="offscreen"):Promise<Uint8Array|null> {
  const session=await createOffscreenSession(a,mode);
  if(!session)return null;
  try{return await session.draw();}finally{session.close();}
}
