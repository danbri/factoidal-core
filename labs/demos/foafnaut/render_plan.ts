// Checked transport for a plan computed by Lean. No layout or drawing policy.
// @deno-types="./foafnaut-engine.d.ts"
import createModule from "./.build/engines/render-plan.mjs";

export type RenderPlan = {
  abi:"lean-render-plan-v1"; mode:"window"|"offscreen";
  width:number; height:number; format:GPUTextureFormat;
  uniform:{floatCount:number;rowCount:number;bytes:number;offset:number;usage:string[]};
  pipeline:{layout:"auto";vertexEntry:string;fragmentEntry:string;topology:GPUPrimitiveTopology};
  bindGroup:{index:number;layoutIndex:number;binding:number};
  pass:{clear:[number,number,number,number];load:GPULoadOp;store:GPUStoreOp};
  draw:{vertexCount:number;instanceCount:number;firstVertex:number;firstInstance:number};
  surface?:{alphaMode:GPUCanvasAlphaMode;usage:string[]};
  texture?:{usage:string[];depth:number};
  readback?:{offset:number;bytesPerRow:number;rowsPerImage:number;bytes:number;usage:string[];mapMode:"read";copyExtent:[number,number,number]};
  commands:string[];
};
export type DeviceFacts=Pick<GPUSupportedLimits,"maxUniformBufferBindingSize"|"maxTextureDimension2D"|"maxBufferSize">;
let modulePromise:ReturnType<typeof createModule>|undefined;
export async function requestRenderPlan(mode:"window"|"offscreen",format:string,
  frame:{width:number;height:number;data:number[]},limits:DeviceFacts):Promise<RenderPlan> {
  const args=[frame.width,frame.height,frame.data.length,limits.maxUniformBufferBindingSize,limits.maxTextureDimension2D];
  if(!args.every(n=>Number.isInteger(n)&&n>=0&&n<=0xffffffff) || !frame.data.every(n=>Number.isFinite(n)&&Number.isFinite(Math.fround(n))))
    throw new Error("Invalid render-plan ABI inputs");
  const module=await (modulePromise??=createModule());
  const pointer=module.ccall("render_plan","number",["string","string",...args.map(()=>"number")],[mode,format,...args]);
  if(!pointer)throw new Error("Lean render-plan allocation failed");
  let p:RenderPlan;
  try {
    const wire=JSON.parse(module.UTF8ToString(pointer));
    if(wire.error)throw new Error(`Lean render plan: ${wire.error}`);
    p=wire;
  } finally { module.ccall("render_plan_free",null,["number"],[pointer]); }
  // Validate ABI/capability correspondence at the trusted host boundary.
  if(p.abi!=="lean-render-plan-v1" || p.mode!==mode || p.width!==frame.width || p.height!==frame.height ||
    p.uniform.floatCount!==frame.data.length || p.uniform.bytes!==frame.data.length*Float32Array.BYTES_PER_ELEMENT ||
    !Number.isSafeInteger(p.uniform.bytes) || p.uniform.bytes>limits.maxBufferSize ||
    !["rgba8unorm","bgra8unorm"].includes(p.format) ||
    (p.readback && (!Number.isSafeInteger(p.readback.bytes)||p.readback.bytes>limits.maxBufferSize)))
    throw new Error("Render plan does not match payload or device buffer capacity");
  return p;
}
export function bufferUsage(names:string[]):number {
  const flags:Record<string,number>={uniform:GPUBufferUsage.UNIFORM,"copy-dst":GPUBufferUsage.COPY_DST,"map-read":GPUBufferUsage.MAP_READ};
  return names.reduce((n,k)=>{if(!(k in flags))throw new Error(`Unknown buffer usage ${k}`);return n|flags[k];},0);
}
export function textureUsage(names:string[]):number {
  const flags:Record<string,number>={"render-attachment":GPUTextureUsage.RENDER_ATTACHMENT,"copy-src":GPUTextureUsage.COPY_SRC};
  return names.reduce((n,k)=>{if(!(k in flags))throw new Error(`Unknown texture usage ${k}`);return n|flags[k];},0);
}
export async function createPlanResources(device:GPUDevice,p:RenderPlan,code:string) {
  const shader=device.createShaderModule({code});
  const diagnostics=await shader.getCompilationInfo();
  for(const m of diagnostics.messages)console.log(`${m.type} ${m.lineNum}:${m.linePos}: ${m.message}`);
  if(diagnostics.messages.some(m=>m.type==="error"))throw new Error("Lean WGSL compilation failed");
  const pipeline=await device.createRenderPipelineAsync({layout:p.pipeline.layout,
    vertex:{module:shader,entryPoint:p.pipeline.vertexEntry},
    fragment:{module:shader,entryPoint:p.pipeline.fragmentEntry,targets:[{format:p.format}]},
    primitive:{topology:p.pipeline.topology}});
  const uniform=device.createBuffer({size:p.uniform.bytes,usage:bufferUsage(p.uniform.usage)});
  const bindGroup=device.createBindGroup({layout:pipeline.getBindGroupLayout(p.bindGroup.layoutIndex),
    entries:[{binding:p.bindGroup.binding,resource:{buffer:uniform}}]});
  return {pipeline,uniform,bindGroup};
}

// This interpreter is a trusted FFI boundary. The order and arguments come
// from Lean; handle validity and actual WebGPU behavior are not proved here.
export function commandInterpreter(device:GPUDevice,p:RenderPlan,
  resources:{pipeline:GPURenderPipeline;bindGroup:GPUBindGroup},view:GPUTextureView,
  io:{present?:()=>void;texture?:GPUTexture;readback?:GPUBuffer}={}) {
  const encoder=device.createCommandEncoder();
  let pass:GPURenderPassEncoder|undefined;
  let mapped:Uint8Array|undefined;
  const handlers:Record<string,()=>void|Promise<void>>={
    beginPass:()=>{pass=encoder.beginRenderPass({colorAttachments:[{view,clearValue:p.pass.clear,loadOp:p.pass.load,storeOp:p.pass.store}]});},
    setPipeline:()=>pass!.setPipeline(resources.pipeline),
    setBindGroup:()=>pass!.setBindGroup(p.bindGroup.index,resources.bindGroup),
    draw:()=>pass!.draw(p.draw.vertexCount,p.draw.instanceCount,p.draw.firstVertex,p.draw.firstInstance),
    endPass:()=>pass!.end(),
    copyTextureToBuffer:()=>encoder.copyTextureToBuffer({texture:io.texture!},
      {buffer:io.readback!,offset:p.readback!.offset,bytesPerRow:p.readback!.bytesPerRow,rowsPerImage:p.readback!.rowsPerImage},p.readback!.copyExtent),
    submit:()=>device.queue.submit([encoder.finish()]),
    present:()=>{if(!io.present)throw new Error("Present requires native surface");io.present();},
    mapRead:()=>io.readback!.mapAsync(GPUMapMode.READ),
    readMapped:()=>{mapped=new Uint8Array(io.readback!.getMappedRange()).slice();},
    unmap:()=>io.readback!.unmap(),
  };
  return {
    step(command:string) {
      if(!(command in handlers))throw new Error(`Unknown Lean GPU command ${command}`);
      return handlers[command]();
    },
    mapped:()=>mapped,
  };
}
