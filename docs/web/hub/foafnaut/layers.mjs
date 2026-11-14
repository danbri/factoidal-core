// The two-layer view of the Hub (issue 1268), as labs/demos/foafnaut/layer_compositor.ts
// is for the native window. Lean gives the chrome layer, the page layer of a band, the
// scene WGSL, the composite WGSL and every plan command. This keeps a texture for each
// layer and runs Lean's plans; it decides no colour and no position. The composite offset
// is scroll-bandTop, kept in the band Lean gives (keepFrom..keepTo).
//
// A scroll inside the band only runs the composite plan again with a new offset: no Lean
// layout and no scene draw.
import {requestRenderPlan,bufferUsage,commandInterpreter} from '../html-webgpu/runtime/render-plan-host.mjs';
import {createPageGpu} from './page-gpu.mjs';

const READBACK=new Set(['copyTextureToBuffer','mapRead','readMapped','unmap']);
// The composite uniform: the place and the press-rectangle count, then the rectangles
// (WebDocument.compositeShader: array<vec4u,maxPressRects+2>). The Hub draws no press.
const PLACE_WORDS=4*(8+2);

/** The answer of a render with layers:true, checked; undefined for any other answer. */
export function layersOf(answer){
  const place=answer?.layers;
  if(!place||!['top','view','bandTop','bandHeight','keepFrom','keepTo'].every(k=>Number.isSafeInteger(place[k]))||typeof place.composite!=='string')return;
  if(!answer.page?.data||!answer.chrome?.data||typeof answer.page.wgsl!=='string'||typeof answer.chrome.wgsl!=='string')return;
  return answer;
}
/** The composite offset for a scroll, kept inside the band; exact is false past the band. */
export function clampOffset(place,scroll){
  const last=Math.max(0,place.bandHeight-place.view);
  const offset=Math.max(0,Math.min(last,scroll-place.bandTop));
  return {offset,exact:offset===scroll-place.bandTop};
}
/** True when Lean says this band shows the scroll with no new render. */
export const keeps=(place,scroll)=>scroll>=place.keepFrom&&scroll<=place.keepTo;
/** Rows a band keeps on each side of the scroll it was made at (scroll_prefetch.ts keepReach). */
export function keepReach(place){
  const margin=Math.floor((place.bandHeight-place.view)/2);
  return Math.max(0,margin-(place.bandTop+place.bandHeight-place.view-place.keepTo));
}

export function hashPixels(rgba){
  let h=0x811c9dc5;const words=new Uint32Array(rgba.buffer,rgba.byteOffset,rgba.byteLength>>>2);
  for(let i=0;i<words.length;i++)h=Math.imul(h^words[i],0x01000193);
  return (h>>>0).toString(16).padStart(8,'0');
}
function unpad(padded,width,height,stride){
  const rgba=new Uint8Array(width*height*4);
  for(let y=0;y<height;y++)rgba.set(padded.subarray(y*stride,y*stride+width*4),y*width*4);
  return rgba;
}
function checkPixels(frame,rgba){
  for(const {x,y,rgb} of frame.checks??[]){
    const o=(y*frame.width+x)*4;
    if(rgb.some((v,i)=>Math.abs(rgba[o+i]-v)>1)||rgba[o+3]!==255)
      throw Error(`GPU readback mismatch at ${x},${y}: ${[...rgba.slice(o,o+4)]}; Lean expected ${rgb}`);
  }
}

/** A canvas (OffscreenCanvas or HTMLCanvasElement) drawn with Lean's layers; null with no WebGPU.
 * With no canvas, frames go to a texture and are read back (the page paints them). */
export async function createLayerSurface(canvas,{check=false,waitForGpu=false}={}){
  if(!navigator.gpu)return null;
  const adapter=await navigator.gpu.requestAdapter();if(!adapter)return null;
  const context=canvas?canvas.getContext('webgpu'):undefined;if(canvas&&!context)return null;
  if(!canvas)check=true;
  let window;
  const device=await adapter.requestDevice();
  const format=navigator.gpu.getPreferredCanvasFormat();
  const plans=new Map(),pipelines=new Map();
  const stats={planRequests:0,pipelineBuilds:0,layerTextures:0,composites:0,scenes:0};
  let failed=false,lost='',cause='',closed=false,configured='';
  device.lost.then(info=>{lost=info.message||info.reason;failed=true;});
  const grow=(slot,bytes,usage)=>{
    if(slot&&slot.capacity>=bytes)return slot;
    slot?.buffer.destroy();
    return {buffer:device.createBuffer({size:bytes,usage}),capacity:bytes};
  };
  async function plan(width,height,data){
    const key=`${width}x${height}x${data.length}`;
    let p=plans.get(key);
    if(!p){
      stats.planRequests++;
      p={...await requestRenderPlan('svg-offscreen',format,{width,height,data},device.limits),format};
      plans.set(key,p);if(plans.size>32)plans.delete(plans.keys().next().value);
    }
    return p;
  }
  async function pipelineFor(p,code){
    const key=JSON.stringify([code,p.pipeline,p.format]);
    const kept=pipelines.get(key);if(kept)return kept;
    const shader=device.createShaderModule({code});
    const info=await shader.getCompilationInfo();
    if(info.messages.some(m=>m.type==='error'))throw Error('WGSL compilation failed: '+info.messages.filter(m=>m.type==='error').map(m=>`${m.lineNum}:${m.linePos} ${m.message}`).join('; '));
    const pipeline=await device.createRenderPipelineAsync({layout:p.pipeline.layout,
      vertex:{module:shader,entryPoint:p.pipeline.vertexEntry},
      fragment:{module:shader,entryPoint:p.pipeline.fragmentEntry,targets:[{format:p.format}]},
      primitive:{topology:p.pipeline.topology}});
    stats.pipelineBuilds++;pipelines.set(key,pipeline);if(pipelines.size>8)pipelines.delete(pipelines.keys().next().value);
    return pipeline;
  }
  let readback;
  // Run a Lean plan on one target texture; with check, read it back.
  async function run(p,resources,target,checking,write){
    if(checking)readback=grow(readback,p.readback.bytes,bufferUsage(p.readback.usage));
    device.pushErrorScope('validation');let scoped=true;
    try{
      write();
      const interpreter=commandInterpreter(device,p,resources,target.createView(),{texture:target,readback:readback?.buffer});
      for(const command of p.commands){if(!checking&&READBACK.has(command))continue;await interpreter.step(command);}
      let pixels;
      if(checking){
        const bytes=interpreter.mapped();if(!bytes)throw Error('Lean plan produced no readback');
        pixels=unpad(bytes,p.width,p.height,p.readback.bytesPerRow);
        if(p.format==='bgra8unorm')for(let i=0;i<pixels.length;i+=4){const b=pixels[i];pixels[i]=pixels[i+2];pixels[i+2]=b;}
      }
      const error=await device.popErrorScope();scoped=false;if(error)throw Error(error.message);
      return pixels;
    }catch(error){
      if(scoped)try{await device.popErrorScope();}catch{/* the first failure */}
      // keep the first error: every later draw reports it (a validation error is thrown once)
      if(!cause)cause=String(error?.message??error);
      failed=true;throw error;
    }
  }
  // Draw one Lean scene into the slot's texture (made at the scene's size), or into the texture
  // that targetOf gives. That is asked for only after every await: a canvas texture lasts
  // until the browser presents it.
  async function drawScene(slot,frame,checking,targetOf){
    const p=await plan(frame.width,frame.height,frame.data);
    const pipeline=await pipelineFor(p,frame.wgsl);
    const target=targetOf?.();
    if(!target){
      const size=`${frame.width}x${frame.height}`;
      if(!slot.texture||slot.size!==size){
        slot.texture?.destroy();stats.layerTextures++;
        slot.texture=device.createTexture({size:[frame.width,frame.height],format:p.format,
          usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.TEXTURE_BINDING|GPUTextureUsage.COPY_SRC});
        slot.size=size;slot.drawn=undefined;
      }
    }
    // Lean's damage (WebPaint.retainedAnswer): the texture holds the answer it names.
    const damage=frame.damage;
    if(!target&&!checking&&damage&&slot.drawn===damage.id){stats.scenesKept=(stats.scenesKept??0)+1;return undefined;}
    const tileWords=frame.tiles,uniformBytes=p.uniform.bytes,tileBytes=tileWords?Math.max(16,tileWords.length*4):0;
    const before=[slot.uniform?.buffer,slot.tiles?.buffer];
    slot.uniform=grow(slot.uniform,uniformBytes,bufferUsage(p.uniform.usage));
    if(tileWords)slot.tiles=grow(slot.tiles,tileBytes,GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST);
    const want=`${uniformBytes}|${tileBytes}|${JSON.stringify(p.pipeline)}|${stats.pipelineBuilds}`;
    if(!slot.bind||slot.bindKey!==want||slot.uniform.buffer!==before[0]||slot.tiles?.buffer!==before[1]||slot.pipeline!==pipeline){
      const entries=[{binding:p.bindGroup.binding,resource:{buffer:slot.uniform.buffer,offset:0,size:uniformBytes}}];
      if(tileWords)entries.push({binding:p.bindGroup.binding+1,resource:{buffer:slot.tiles.buffer,offset:0,size:tileBytes}});
      slot.bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(p.bindGroup.layoutIndex),entries});slot.bindKey=want;slot.pipeline=pipeline;
    }
    stats.scenes++;
    const write=()=>{
      device.queue.writeBuffer(slot.uniform.buffer,p.uniform.offset,frame.data instanceof Float32Array?frame.data:new Float32Array(frame.data));
      if(tileWords)device.queue.writeBuffer(slot.tiles.buffer,0,tileWords instanceof Uint32Array?tileWords:new Uint32Array(tileWords));
    };
    // A frame whose damage Lean knows and whose base is in the texture: only those rectangles.
    const rects=!target&&!checking&&damage?.rects&&damage.base!==null&&slot.drawn===damage.base&&slot.texture?damage.rects:undefined;
    let pixels;
    if(rects){
      stats.scenesPartial=(stats.scenesPartial??0)+1;
      if(rects.length){
        device.pushErrorScope('validation');let scoped=true;
        try{
          write();
          const encoder=device.createCommandEncoder();
          const pass=encoder.beginRenderPass({colorAttachments:[{view:slot.texture.createView(),loadOp:'load',storeOp:'store'}]});
          pass.setPipeline(pipeline);pass.setBindGroup(p.bindGroup.index,slot.bind);
          for(const [x,y,w,h] of rects){pass.setScissorRect(x,y,w,h);pass.draw(p.draw.vertexCount,p.draw.instanceCount,p.draw.firstVertex,p.draw.firstInstance);}
          pass.end();device.queue.submit([encoder.finish()]);
          const error=await device.popErrorScope();scoped=false;if(error)throw Error(error.message);
        }catch(error){if(scoped)try{await device.popErrorScope();}catch{/* the first failure */}failed=true;throw error;}
      }else write();
    }else{
      stats.scenesFull=(stats.scenesFull??0)+1;
      pixels=await run(p,{pipeline,bindGroup:slot.bind},target??slot.texture,checking,write);
      if(checking&&pixels)checkPixels(frame,pixels);
    }
    if(!target)slot.drawn=damage?.id;
    return pixels;
  }
  const chrome={},page={},single={};
  // Page canvases drawn by page scripts (page-gpu.mjs): Lean-validated commands, blitted into
  // the page layer at Lean's rectangles.
  let pageGpu;
  const gpuOf=()=>pageGpu??=createPageGpu(device);
  const blitCanvases=answer=>!!(answer?.layers?.canvases&&page.texture&&pageGpu?.blit(page.texture,answer.layers.canvases,answer.layers.canvasBlit));
  let shown,place,compositeBind,compositeKey='',ids=new WeakMap(),nextId=0;
  const idOf=t=>{let id=ids.get(t);if(id===undefined){id=++nextId;ids.set(t,id);}return id;};
  // The canvas, at the window's size; with check it can be read back.
  function canvasTexture(width,height){
    const want=`${width}x${height}`;
    if(!context){
      if(configured!==want){window?.destroy();window=device.createTexture({size:[width,height],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});configured=want;}
      return window;
    }
    if(configured!==want){
      canvas.width=width;canvas.height=height;
      context.configure({device,format,alphaMode:'opaque',usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});
      configured=want;
    }
    return context.getCurrentTexture();
  }
  const ensure=()=>{if(closed||failed)throw Error('GPU layer surface is '+(failed?'failed':'closed')+(lost?': device lost: '+lost:'')+(cause?': first error: '+cause:''));};
  // At most one frame of GPU work in flight (the native host's gate, gpu_pacing.ts): a frame
  // takes the done-promise of its work when it is submitted and the next GPU work waits for it.
  // When the GPU keeps up, the promise has resolved by then and nothing waits. A page whose
  // frames cost the GPU more than a turn can not queue frames on the GPU, nor hold it after
  // the tab goes. In a browser this promise does not block the thread.
  let inFlight;
  const gate=async()=>{if(inFlight){const p=inFlight;await p;if(inFlight===p)inFlight=undefined;}};
  const finish=async()=>{if(waitForGpu)await device.queue.onSubmittedWorkDone();else inFlight=device.queue.onSubmittedWorkDone().catch(()=>{});};
  return {
    format,
    get stats(){return {...stats,failed,lost,cause};},
    get layers(){return shown;},
    /** Draw both layers of one Lean render into their textures. */
    async drawLayers(answer){
      ensure();await gate();
      await drawScene(chrome,answer.chrome,check);
      await drawScene(page,answer.page,check);
      blitCanvases(answer);
      shown=answer;
    },
    /** Replay page GPU commands (Lean's host commands of page session `p`). */
    async replayGpu(p,commands){ensure();await gate();return gpuOf().replay(p,commands);},
    /** The page canvases again, into the page layer on screen; true when one was drawn
     * (the caller then composites). */
    refreshCanvases(){ensure();return blitCanvases(shown);},
    get pageGpuStats(){return pageGpu?.stats;},
    /** A new chrome layer alone (Lean's chromeLayer answer: a fold of the chrome), `top`
     * rows high: the page layer stays, and the next composite shows it under this chrome. */
    async setChrome(scene,top){
      ensure();await gate();
      if(!shown)throw Error('setChrome before any layers were drawn');
      await drawScene(chrome,scene,check);
      shown={...shown,chrome:scene,layers:{...shown.layers,top}};
    },
    /** The layers on screen at this offset (Lean's composite WGSL), into the canvas or into
     * target. With readback, the pixels come back (RGBA). */
    async composite(width,height,offset,{target,readBack=check}={}){
      ensure();await gate();
      if(!shown)throw Error('composite before any layers were drawn');
      const p=await plan(width,height,[0,0,0,0]);
      const pipeline=await pipelineFor(p,shown.layers.composite);
      place??=device.createBuffer({size:PLACE_WORDS*4,usage:GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST});
      const key=`${idOf(chrome.texture)}|${idOf(page.texture)}|${idOf(pipeline)}`;
      if(!compositeBind||compositeKey!==key){
        compositeBind=device.createBindGroup({layout:pipeline.getBindGroupLayout(p.bindGroup.layoutIndex),entries:[
          {binding:0,resource:chrome.texture.createView()},{binding:1,resource:page.texture.createView()},{binding:2,resource:{buffer:place}}]});
        compositeKey=key;
      }
      const words=new Uint32Array(PLACE_WORDS);
      words.set([shown.layers.top,offset,shown.layers.bandHeight,0]);
      stats.composites++;
      const pixels=await run(p,{pipeline,bindGroup:compositeBind},target??canvasTexture(width,height),readBack,()=>device.queue.writeBuffer(place,0,words));
      await finish();
      return pixels;
    },
    /** One single-frame Lean scene (the path with no layers), into the canvas or target. */
    async drawSingle(frame,{target,readBack=check}={}){
      ensure();await gate();
      const pixels=await drawScene(single,frame,readBack,()=>target??canvasTexture(frame.width,frame.height));
      await finish();
      return pixels;
    },
    /** A texture the size of the window that can be read back: for tests. */
    target:(width,height)=>device.createTexture({size:[width,height],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC}),
    close(){
      if(closed)return;closed=true;
      try{context?.unconfigure();window?.destroy();}catch{/* gone */}
      for(const slot of [chrome,page,single]){slot.texture?.destroy();slot.uniform?.buffer.destroy();slot.tiles?.buffer.destroy();}
      place?.destroy();readback?.buffer.destroy();ids=new WeakMap();pageGpu?.close();
      try{device.destroy();}catch{/* gone */}
    },
  };
}

// The layer surface with no GPU (docs/designissues/2026-11-08-cpu-render-backend.md). Lean
// drew each layer on the CPU (SVGRaster: a render with cpu:true gives each scene its RGBA
// rows, `pixels`); this keeps those bytes and copies them. It decides no colour and no
// position: the composite is WebDocument.compositeShader's copy, window row y<top from
// chrome row y and row y>=top from page row y-top+offset, white past the page layer. The
// Hub draws no press rectangle, as with the GPU. A scroll inside the band is a copy, with
// no Lean call, as with the GPU.
const pixelsOf=scene=>scene?.pixels instanceof Uint8Array&&scene.pixels.length===scene.width*scene.height*4?scene.pixels:undefined;
/** The answer of a render with layers:true and cpu:true, checked; undefined for any other. */
export function cpuLayersOf(answer){
  const layers=layersOf(answer);
  return layers&&pixelsOf(layers.page)&&pixelsOf(layers.chrome)?layers:undefined;
}
/** The window at this offset from the two layers' bytes: WebDocument.compositeShader. */
export function compositeBytes(chrome,page,place,width,height,offset){
  const out=new Uint8Array(width*height*4).fill(255),row=width*4;
  const top=Math.min(place.top,height,chrome.height);
  if(chrome.width===width)out.set(chrome.pixels.subarray(0,top*row),0);
  if(page.width===width){
    const rows=Math.max(0,Math.min(height-place.top,page.height-offset));
    if(rows>0)out.set(page.pixels.subarray(offset*row,(offset+rows)*row),place.top*row);
  }
  return out;
}
/** A canvas (OffscreenCanvas or HTMLCanvasElement, 2D) shown with Lean's CPU layers, or
 * with no canvas, frames read back (the page paints them). Same calls as createLayerSurface. */
export function createCpuLayerSurface(canvas){
  const context=canvas?canvas.getContext('2d'):undefined;
  if(canvas&&!context)return null;
  const stats={planRequests:0,pipelineBuilds:0,layerTextures:0,composites:0,scenes:0,cpu:true};
  let shown,closed=false;
  const ensure=()=>{if(closed)throw Error('CPU layer surface is closed');};
  const need=scene=>{const pixels=pixelsOf(scene);if(!pixels)throw Error('Lean answered no CPU pixels for a layer');stats.scenes++;return {width:scene.width,height:scene.height,pixels};};
  let chrome,page;
  function show(width,height,rgba){
    if(!context)return rgba;
    if(canvas.width!==width||canvas.height!==height){canvas.width=width;canvas.height=height;}
    context.putImageData(new ImageData(new Uint8ClampedArray(rgba.buffer,rgba.byteOffset,rgba.byteLength),width,height),0,0);
  }
  return {
    format:'rgba8unorm',cpu:true,
    get stats(){return {...stats,failed:false,lost:''};},
    get layers(){return shown;},
    async drawLayers(answer){ensure();chrome=need(answer.chrome);page=need(answer.page);shown=answer;},
    // Page canvases need a GPU: with none they stay as Lean drew them (blank).
    async replayGpu(){},
    refreshCanvases(){return false;},
    get pageGpuStats(){return undefined;},
    async setChrome(scene,top){
      ensure();if(!shown)throw Error('setChrome before any layers were drawn');
      chrome=need(scene);shown={...shown,chrome:scene,layers:{...shown.layers,top}};
    },
    async composite(width,height,offset){
      ensure();if(!shown)throw Error('composite before any layers were drawn');
      stats.composites++;
      return show(width,height,compositeBytes(chrome,page,shown.layers,width,height,offset));
    },
    async drawSingle(frame){ensure();const f=need(frame);return show(f.width,f.height,f.pixels.slice());},
    target:()=>undefined,
    close(){closed=true;chrome=page=shown=undefined;},
  };
}
