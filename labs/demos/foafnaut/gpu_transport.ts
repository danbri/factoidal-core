// WebGPU/byte transport. Rendering descriptors and command order come from Lean.
import type { ShaderSubmission, RenderPlan } from "./render_plan.ts";
import type { Artifact } from "./lean_generator.ts";
import { requestRenderPlan, createPlanResources, textureUsage, bufferUsage, commandInterpreter } from "./render_plan.ts";
type Renderable=Pick<Artifact,"width"|"height"|"data"|"wgsl"|"checks">&{tiles?:number[]};

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
export async function createOffscreenSession(a:Renderable,mode:"offscreen"|"svg-offscreen"="offscreen",observeShader?:(event:ShaderSubmission)=>void) {
  if(!navigator.gpu)throw new Error("WebGPU API absent; add --unstable-webgpu");
  let verification={...a,checks:a.checks.map(p=>({...p,rgb:[...p.rgb]}))};
  const shape={width:a.width,height:a.height,wgsl:a.wgsl,floatCount:a.data.length,tiles:a.tiles?.join()};
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
    for(const resource of [readback,texture,resources?.uniform,resources?.tiles,device])try{resource?.destroy();}catch(error){errors.push(error);}
    if(errors.length)console.warn("GPU session cleanup:",errors.map(String).join("; "));
  };
  try {
    device.pushErrorScope("validation");scope=true;
    const plan=await requestRenderPlan(mode,"rgba8unorm",a,device.limits);
    resources=await createPlanResources(device,plan,a.wgsl,observeShader,a.tiles);
    counters.shaderModules=1;counters.pipelines=1;counters.buffers=1;
    device.queue.writeBuffer(resources.uniform,plan.uniform.offset,new Float32Array(a.data));counters.uploads++;
    texture=device.createTexture({size:[plan.width,plan.height,plan.texture!.depth],format:plan.format,usage:textureUsage(plan.texture!.usage)});counters.textures++;
    readback=device.createBuffer({size:plan.readback!.bytes,usage:bufferUsage(plan.readback!.usage)});counters.buffers++;
    const initialError=await device.popErrorScope();scope=false;
    if(initialError)throw new Error(initialError.message);
    return {
      adapterInfo:adapter.info,
      get stats(){return {...counters,closed,failed};},
      async update(next:Renderable):Promise<boolean> {
        if(closed||failed)throw new Error("GPU session is closed or failed");
        if(busy)throw new Error("Concurrent GPU updates/readbacks are unsupported");
        if(next.width!==shape.width||next.height!==shape.height||next.wgsl!==shape.wgsl||next.data.length!==shape.floatCount||next.tiles?.join()!==shape.tiles)return false;
        busy=true;
        try {
          // Lean revalidates the new payload and supplies the complete plan.
          // Reuse is allowed only when all descriptors and commands agree.
          const nextPlan=await requestRenderPlan(mode,"rgba8unorm",next,device.limits);
          if(JSON.stringify(nextPlan)!==JSON.stringify(plan))return false;
          const checks=next.checks.map(p=>({...p,rgb:[...p.rgb]}));
          device.pushErrorScope("validation");scope=true;
          device.queue.writeBuffer(resources!.uniform,plan.uniform.offset,new Float32Array(next.data));
          const error=await device.popErrorScope();scope=false;
          if(error)throw new Error(error.message);
          verification={...next,checks};counters.uploads++;
          return true;
        }catch(error){failed=true;throw error;}
        finally {
          if(scope){try{await device.popErrorScope();}catch{/* preserve update error */}scope=false;}
          busy=false;
        }
      },
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

// The plan commands that read a frame back to the CPU. Lean's plan always lists
// them. A frame that is not checked leaves them out; Lean still decides every
// other command and its order. (Issue 1268.)
export const READBACK_COMMANDS:ReadonlySet<string>=new Set(["copyTextureToBuffer","mapRead","readMapped","unmap"]);

export type SurfaceFrameResult={checked:boolean;pixelHash:string;drawMs:number;gpuMs:number};

// A session that draws straight into the current texture of a canvas context
// (an OffscreenCanvas in a worker, or an HTMLCanvasElement). The frame is not
// read back unless check is true: then Lean's probe pixels are compared and the
// frame is hashed (FNV-1a over the RGBA bytes, the same hash on every path).
// The device, the pipeline and the buffers live as long as the session. The
// pipeline is built again only when the WGSL text or the plan's pipeline
// description changes; a buffer is made again only when it must grow. A change of
// frame size resizes the canvas and asks Lean for a new plan, once per size.
export async function createSurfaceSession(canvas:{width:number;height:number;getContext(kind:string):unknown},options:{check?:boolean;waitForGpu?:boolean}={}) {
  if(!navigator.gpu)return null;
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter)return null;
  const context=canvas.getContext("webgpu") as GPUCanvasContext|null;
  if(!context)return null;
  const device=await adapter.requestDevice();
  const format=navigator.gpu.getPreferredCanvasFormat();
  const check=options.check===true,waitForGpu=options.waitForGpu===true||check;
  const counters={devices:1,planRequests:0,pipelineBuilds:0,uniformBuffers:0,tileBuffers:0,bindGroups:0,configures:0,frames:0,checkedFrames:0,submissions:0};
  type Growing={buffer:GPUBuffer;capacity:number};
  const plans=new Map<string,RenderPlan>();
  let pipelineKey="",pipeline:GPURenderPipeline|undefined,uniform:Growing|undefined,tiles:Growing|undefined,readback:Growing|undefined;
  let bindKey="",bindGroup:GPUBindGroup|undefined,configuredKey="";
  let closed=false,busy=false,failed=false,lost="",lastError="";
  device.lost.then(info=>{lost=info.message||info.reason;failed=true;});
  device.addEventListener("uncapturederror",(event:Event)=>{lastError=(event as GPUUncapturedErrorEvent).error.message;console.error("GPU error:",lastError);});
  const grow=(slot:Growing|undefined,bytes:number,usage:number,count:()=>void):Growing=>{
    if(slot&&slot.capacity>=bytes)return slot;
    slot?.buffer.destroy();count();
    return {buffer:device.createBuffer({size:bytes,usage}),capacity:bytes};
  };
  async function buildPipeline(plan:RenderPlan,code:string) {
    const key=JSON.stringify([code,plan.pipeline,plan.bindGroup,plan.format,plan.uniform.bindingType,plan.uniform.usage]);
    if(key===pipelineKey&&pipeline)return;
    const shader=device.createShaderModule({code});
    const diagnostics=await shader.getCompilationInfo();
    for(const m of diagnostics.messages)console.log(`${m.type} ${m.lineNum}:${m.linePos}: ${m.message}`);
    if(diagnostics.messages.some(m=>m.type==="error"))throw new Error("WGSL compilation failed: "+diagnostics.messages.filter(m=>m.type==="error").map(m=>`${m.lineNum}:${m.linePos} ${m.message}`).join("; "));
    pipeline=await device.createRenderPipelineAsync({layout:plan.pipeline.layout,
      vertex:{module:shader,entryPoint:plan.pipeline.vertexEntry},
      fragment:{module:shader,entryPoint:plan.pipeline.fragmentEntry,targets:[{format:plan.format}]},
      primitive:{topology:plan.pipeline.topology}});
    pipelineKey=key;bindKey="";counters.pipelineBuilds++;
  }
  return {
    adapterInfo:adapter.info,format,
    get stats(){return {...counters,closed,failed,lost,lastError};},
    async draw(frame:Renderable):Promise<SurfaceFrameResult> {
      if(closed||failed)throw new Error("GPU surface session is closed or failed"+(lost?": "+lost:""));
      if(busy)throw new Error("Concurrent GPU surface frames are unsupported");
      busy=true;
      const start=performance.now();
      let scoped=false;
      try {
        const planKey=`${frame.width}x${frame.height}x${frame.data.length}`;
        let plan=plans.get(planKey);
        if(!plan){
          counters.planRequests++;
          plan={...await requestRenderPlan("svg-offscreen",format,frame as unknown as {width:number;height:number;data:number[]},device.limits),format};
          plans.set(planKey,plan);if(plans.size>32)plans.delete(plans.keys().next().value!);
        }
        await buildPipeline(plan,frame.wgsl);
        if(configuredKey!==planKey){
          canvas.width=frame.width;canvas.height=frame.height;
          context.configure({device,format,alphaMode:"opaque",usage:GPUTextureUsage.RENDER_ATTACHMENT|(check?GPUTextureUsage.COPY_SRC:0)});
          configuredKey=planKey;counters.configures++;
        }
        const uniformBytes=plan.uniform.bytes,tileWords=frame.tiles,tileBytes=tileWords?Math.max(16,tileWords.length*4):0;
        const uniformBefore=uniform?.buffer,tilesBefore=tiles?.buffer;
        uniform=grow(uniform,uniformBytes,bufferUsage(plan.uniform.usage),()=>{counters.uniformBuffers++;});
        if(tileWords)tiles=grow(tiles,tileBytes,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST,()=>{counters.tileBuffers++;});
        const wantBind=`${uniformBytes}|${tileBytes}`;
        if(!bindGroup||bindKey!==wantBind||uniform.buffer!==uniformBefore||tiles?.buffer!==tilesBefore){
          const entries:GPUBindGroupEntry[]=[{binding:plan.bindGroup.binding,resource:{buffer:uniform.buffer,offset:0,size:uniformBytes}}];
          if(tileWords)entries.push({binding:plan.bindGroup.binding+1,resource:{buffer:tiles!.buffer,offset:0,size:tileBytes}});
          bindGroup=device.createBindGroup({layout:pipeline!.getBindGroupLayout(plan.bindGroup.layoutIndex),entries});
          bindKey=wantBind;counters.bindGroups++;
        }
        if(check)readback=grow(readback,plan.readback!.bytes,bufferUsage(plan.readback!.usage),()=>{});
        if(check){device.pushErrorScope("validation");scoped=true;}
        device.queue.writeBuffer(uniform.buffer,plan.uniform.offset,frame.data instanceof Float32Array?frame.data:new Float32Array(frame.data));
        if(tileWords)device.queue.writeBuffer(tiles!.buffer,0,new Uint32Array(tileWords));
        const texture=context.getCurrentTexture();
        const interpreter=commandInterpreter(device,plan,{pipeline:pipeline!,bindGroup:bindGroup!},texture.createView(),{texture,readback:readback?.buffer});
        for(const command of plan.commands){
          if(!check&&READBACK_COMMANDS.has(command))continue;
          await interpreter.step(command);
          if(command==="submit")counters.submissions++;
        }
        const built=performance.now();
        let pixelHash="";
        if(check){
          const bytes=interpreter.mapped();if(!bytes)throw new Error("Lean surface plan produced no pixels");
          const pixels=unpad(bytes,plan.width,plan.height,plan.readback!.bytesPerRow);
          if(plan.format==="bgra8unorm")for(let i=0;i<pixels.length;i+=4){const b=pixels[i];pixels[i]=pixels[i+2];pixels[i+2]=b;}
          checkPixels(frame,pixels);
          pixelHash=hashPixels(pixels);counters.checkedFrames++;
          const error=await device.popErrorScope();scoped=false;
          if(error)throw new Error(error.message);
        }else if(waitForGpu)await device.queue.onSubmittedWorkDone();
        counters.frames++;
        return {checked:check,pixelHash,drawMs:built-start,gpuMs:performance.now()-start};
      }catch(error){
        if(scoped)try{await device.popErrorScope();}catch{/* preserve frame error */}
        failed=true;throw error;
      }finally{busy=false;}
    },
    close() {
      if(closed)return;
      if(busy)throw new Error("Cannot close GPU surface session during a frame");
      closed=true;
      try{context.unconfigure();}catch{/* the context may already be gone */}
      for(const r of [readback?.buffer,uniform?.buffer,tiles?.buffer,device])try{r?.destroy();}catch{/* cleanup */}
    },
  };
}

// FNV-1a over the RGBA bytes read as 32-bit words. Two renderers agree only if every byte agrees.
export function hashPixels(rgba:Uint8Array):string {
  let h=0x811c9dc5;const words=new Uint32Array(rgba.buffer,rgba.byteOffset,rgba.byteLength>>>2);
  for(let i=0;i<words.length;i++)h=Math.imul(h^words[i],0x01000193);
  return (h>>>0).toString(16).padStart(8,"0");
}
