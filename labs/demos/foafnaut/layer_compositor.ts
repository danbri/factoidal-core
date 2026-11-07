// GPU side of the two-layer render (WebDocument.layersJSON, issue 1268). Lean gives
// the chrome layer, the page layer of a band, the scene WGSL, the composite WGSL and
// every plan command. The host keeps a texture for each layer and runs the plans; it
// decides no colour and no position: the composite offset is scroll-bandTop, kept in
// the band that Lean gives (keepFrom..keepTo; clampOffset below).
//
// A scroll inside the band only runs the composite plan again with a new offset.
import {requestRenderPlan,bufferUsage,commandInterpreter,type RenderPlan,type DeviceFacts} from "./render_plan.ts";
import {unpad,checkPixels} from "./gpu_transport.ts";
import type {HTMLArtifact,HTMLLayers} from "./native_html_engine.ts";

// The plan commands that read the frame back to the CPU. Lean's plan always
// lists them. The host leaves them out for a frame that is not checked.
export const READBACK_COMMANDS:ReadonlySet<string>=new Set(["copyTextureToBuffer","mapRead","readMapped","unmap"]);

/** FNV-1a over the pixels: two renderers agree only if every byte agrees. */
export function pixelHash(pixels:Uint8Array):string {
  let h=0x811c9dc5;const words=new Uint32Array(pixels.buffer,pixels.byteOffset,pixels.byteLength>>>2);
  for(let i=0;i<words.length;i++){h=Math.imul(h^words[i],0x01000193);}
  return (h>>>0).toString(16).padStart(8,"0");
}

/** The composite offset for a scroll: the page row of the band shown at the top of the view,
 * kept inside the band. `exact` is false when the scroll is past the band and the view waits for a new one. */
export function clampOffset(place:HTMLLayers["layers"],scroll:number):{offset:number;exact:boolean} {
  const last=Math.max(0,place.bandHeight-place.view);
  const offset=Math.max(0,Math.min(last,scroll-place.bandTop));
  return {offset,exact:offset===scroll-place.bandTop};
}
/** True when Lean says this band shows the scroll with no new render. */
export function keeps(place:HTMLLayers["layers"],scroll:number):boolean {return scroll>=place.keepFrom&&scroll<=place.keepTo;}

type Growing={buffer:GPUBuffer;capacity:number};
type Slot={uniform?:Growing;tiles?:Growing;bind?:GPUBindGroup;bindKey:string;texture?:GPUTexture;size:string};
export type PassResult={steps:Record<string,number>;pixels?:Uint8Array;hash:string};

const LAYER_USAGE=()=>GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.TEXTURE_BINDING|GPUTextureUsage.COPY_SRC;

export function createLayerRenderer(device:GPUDevice,format:GPUTextureFormat,limits:DeviceFacts=device.limits) {
  const plans=new Map<string,RenderPlan>();
  const pipelines=new Map<string,GPURenderPipeline>();
  const stats={planRequests:0,pipelineBuilds:0,layerTextures:0,bindGroups:0};
  const grow=(slot:Growing|undefined,bytes:number,usage:number):Growing=>{
    if(slot&&slot.capacity>=bytes)return slot;
    slot?.buffer.destroy();
    return {buffer:device.createBuffer({size:bytes,usage}),capacity:bytes};
  };
  async function plan(width:number,height:number,data:ArrayLike<number>):Promise<RenderPlan> {
    const key=`${width}x${height}x${data.length}`;
    let p=plans.get(key);
    if(!p){
      stats.planRequests++;
      p={...await requestRenderPlan("svg-offscreen",format,{width,height,data:data as number[]},limits),format};
      plans.set(key,p);if(plans.size>32)plans.delete(plans.keys().next().value!);
    }
    return p;
  }
  async function pipelineFor(p:RenderPlan,code:string):Promise<GPURenderPipeline> {
    const key=JSON.stringify([code,p.pipeline,p.format]);
    const kept=pipelines.get(key);if(kept)return kept;
    const shader=device.createShaderModule({code});
    const info=await shader.getCompilationInfo();
    if(info.messages.some(m=>m.type==="error"))throw new Error("WGSL compilation failed: "+info.messages.filter(m=>m.type==="error").map(m=>`${m.lineNum}:${m.linePos} ${m.message}`).join("; "));
    const pipeline=await device.createRenderPipelineAsync({layout:p.pipeline.layout,
      vertex:{module:shader,entryPoint:p.pipeline.vertexEntry},
      fragment:{module:shader,entryPoint:p.pipeline.fragmentEntry,targets:[{format:p.format}]},
      primitive:{topology:p.pipeline.topology}});
    stats.pipelineBuilds++;pipelines.set(key,pipeline);if(pipelines.size>8)pipelines.delete(pipelines.keys().next().value!);
    return pipeline;
  }
  let readback:Growing|undefined;
  // Run a Lean plan on one target texture; with check, read it back and hash it.
  async function run(p:RenderPlan,resources:{pipeline:GPURenderPipeline;bindGroup:GPUBindGroup},target:GPUTexture,check:boolean,
    write:()=>void):Promise<PassResult> {
    if(check)readback=grow(readback,p.readback!.bytes,bufferUsage(p.readback!.usage));
    device.pushErrorScope("validation");let scoped=true;
    try{
      write();
      const interpreter=commandInterpreter(device,p,resources,target.createView(),{texture:target,readback:readback?.buffer});
      const steps:Record<string,number>={};
      for(const command of p.commands){
        if(!check&&READBACK_COMMANDS.has(command))continue;
        const s=performance.now();await interpreter.step(command);steps[command]=Math.round((performance.now()-s)*10)/10;
      }
      let pixels:Uint8Array|undefined,hash="";
      if(check){
        const bytes=interpreter.mapped();if(!bytes)throw new Error("Lean plan produced no readback");
        pixels=unpad(bytes,p.width,p.height,p.readback!.bytesPerRow);
        if(p.format==="bgra8unorm")for(let i=0;i<pixels.length;i+=4){const b=pixels[i];pixels[i]=pixels[i+2];pixels[i+2]=b;}
        hash=pixelHash(pixels);
      }
      const error=await device.popErrorScope();scoped=false;if(error)throw new Error(error.message);
      return {steps,pixels,hash};
    }catch(error){
      if(scoped)try{await device.popErrorScope();}catch{/* original failure */}
      throw error;
    }
  }
  /** Draw one Lean scene into the slot's texture (made at the scene's size), or into `target`. */
  async function drawScene(slot:Slot,frame:HTMLArtifact,check:boolean,target?:GPUTexture):Promise<PassResult> {
    const p=await plan(frame.width,frame.height,frame.data);
    const pipeline=await pipelineFor(p,frame.wgsl);
    if(!target){
      const size=`${frame.width}x${frame.height}`;
      if(!slot.texture||slot.size!==size){
        slot.texture?.destroy();stats.layerTextures++;
        slot.texture=device.createTexture({size:[frame.width,frame.height],format:p.format,usage:LAYER_USAGE()});slot.size=size;
      }
    }
    const tileWords=frame.tiles;
    const uniformBytes=p.uniform.bytes,tileBytes=tileWords?Math.max(16,tileWords.length*4):0;
    const before=[slot.uniform?.buffer,slot.tiles?.buffer];
    slot.uniform=grow(slot.uniform,uniformBytes,bufferUsage(p.uniform.usage));
    if(tileWords)slot.tiles=grow(slot.tiles,tileBytes,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST);
    const want=`${uniformBytes}|${tileBytes}|${JSON.stringify(p.pipeline)}`;
    if(!slot.bind||slot.bindKey!==want||slot.uniform.buffer!==before[0]||slot.tiles?.buffer!==before[1]){
      const entries:GPUBindGroupEntry[]=[{binding:p.bindGroup.binding,resource:{buffer:slot.uniform.buffer,offset:0,size:uniformBytes}}];
      if(tileWords)entries.push({binding:p.bindGroup.binding+1,resource:{buffer:slot.tiles!.buffer,offset:0,size:tileBytes}});
      slot.bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(p.bindGroup.layoutIndex),entries});slot.bindKey=want;stats.bindGroups++;
    }
    const result=await run(p,{pipeline,bindGroup:slot.bind},target??slot.texture!,check,()=>{
      device.queue.writeBuffer(slot.uniform!.buffer,p.uniform.offset,(frame.data instanceof Float32Array?frame.data:new Float32Array(frame.data)) as Float32Array<ArrayBuffer>);
      if(tileWords)device.queue.writeBuffer(slot.tiles!.buffer,0,new Uint32Array(tileWords));
    });
    if(check&&result.pixels)checkPixels(frame as unknown as Parameters<typeof checkPixels>[0],result.pixels);
    return result;
  }
  const chrome:Slot={bindKey:"",size:""},page:Slot={bindKey:"",size:""},single:Slot={bindKey:"",size:""};
  let shown:HTMLLayers|undefined,place:GPUBuffer|undefined,compositeBind:GPUBindGroup|undefined,compositeKey="";
  let textureIds=new WeakMap<GPUTexture,number>(),nextId=0;
  const idOf=(t:GPUTexture)=>{let id=textureIds.get(t);if(id===undefined){id=++nextId;textureIds.set(t,id);}return id;};
  return {
    stats,
    plan,
    /** Draw both layers of one Lean render into their textures. */
    async drawLayers(layers:HTMLLayers,check:boolean):Promise<{chrome:PassResult;page:PassResult}> {
      const c=await drawScene(chrome,layers.chrome,check);
      const g=await drawScene(page,layers.page,check);
      shown=layers;
      return {chrome:c,page:g};
    },
    /** Draw one single-frame Lean scene into `target`: the reference that the composite must equal. */
    drawSingle:(frame:HTMLArtifact,target:GPUTexture,check:boolean)=>drawScene(single,frame,check,target),
    get layers(){return shown;},
    /** Copy the layers into `target` (width x height): Lean's composite WGSL at this offset. */
    async composite(target:GPUTexture,width:number,height:number,offset:number,check:boolean):Promise<PassResult> {
      if(!shown)throw new Error("composite before any layers were drawn");
      const p=await plan(width,height,[0,0,0,0]);
      const pipeline=await pipelineFor(p,shown.layers.composite);
      place??=device.createBuffer({size:16,usage:GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST});
      const key=`${idOf(chrome.texture!)}|${idOf(page.texture!)}|${JSON.stringify(p.pipeline)}`;
      if(!compositeBind||compositeKey!==key){
        compositeBind=device.createBindGroup({layout:pipeline.getBindGroupLayout(p.bindGroup.layoutIndex),entries:[
          {binding:0,resource:chrome.texture!.createView()},{binding:1,resource:page.texture!.createView()},{binding:2,resource:{buffer:place}}]});
        compositeKey=key;stats.bindGroups++;
      }
      const words=new Uint32Array([shown.layers.top,offset,shown.layers.bandHeight,0]);
      return run(p,{pipeline,bindGroup:compositeBind},target,check,()=>device.queue.writeBuffer(place!,0,words));
    },
    dispose(){
      for(const slot of [chrome,page,single]){slot.texture?.destroy();slot.uniform?.buffer.destroy();slot.tiles?.buffer.destroy();}
      place?.destroy();readback?.buffer.destroy();textureIds=new WeakMap();
    },
  };
}
export type LayerRenderer=ReturnType<typeof createLayerRenderer>;
