// Page GPU commands on the Hub (docs/designissues/2026-11-08-page-gpu.md). A page script's
// WebGPU calls reach Lean as typed commands; Lean (L4Factoidal.PageGpu) validates each one,
// prints the WGSL it allows, and emits host commands. This replays those host commands on
// the layer surface's device and draws each page canvas into the page layer at the
// rectangle and clip Lean gives (render answer `layers.canvases`), with Lean's blit WGSL.
// Every id, size, offset, usage, shader text and rectangle is Lean's; this decides nothing.
// The page's objects are kept apart from the engine's (a table per page session).
// Compute (docs/designissues/2026-11-14-gpu-compute-and-webnn.md): compute pipelines with
// the layout Lean gives, bind groups, compute passes, copies, and readbacks, whose bytes go
// back to Lean (the host's `gpuRead` action) with the ticket Lean gave.

const FORMAT='rgba8unorm';
// The watchdog (docs/designissues/2026-11-14-gpu-compute-and-webnn.md, wall time): a replay's
// GPU work that has not finished this long after it was submitted loses the page's GPU
// device. Lean then refuses every later command of the page; the replay drops its objects;
// the engine's own drawing and other pages go on. Work already on the GPU is not cancelled
// (WebGPU has no way to); Lean bounds each frame's work in operations.
export const WATCHDOG_MS=3000;
const b64=bytes=>{let s='';for(let i=0;i<bytes.length;i+=32768)s+=String.fromCharCode.apply(null,bytes.subarray(i,i+32768));return btoa(s);};
const BINDING={uniform:{type:'uniform'},'read-only-storage':{type:'read-only-storage'},storage:{type:'storage'}};
// Lean's run-length form of a 2D canvas's pixels (PageCanvas.rle): a word n, then with the
// high bit n pixels as they are, else one pixel n times. Only copies bytes.
export function unrle(b,w,h){
  const out=new Uint8Array(w*h*4),o32=new Uint32Array(out.buffer),dv=new DataView(b.buffer,b.byteOffset,b.byteLength);
  let i=0,p=0;
  while(i+4<=b.length&&p<w*h){
    const head=dv.getUint32(i,true),n=Math.min(head&0x7fffffff,w*h-p);i+=4;
    if(head&0x80000000){out.set(b.subarray(i,i+4*n),4*p);i+=4*n;}
    else{o32.fill(new Uint32Array(b.slice(i,i+4).buffer)[0],p,p+n);i+=4;}
    p+=n;
  }
  return out;
}

export function createPageGpu(device,{watchdogMs=WATCHDOG_MS}={}){
  let page=-1,blitCode='',blitPipeline,rect,lostPage=-1,lostTold=false;
  const objs=new Map(),canvases=new Map(),stats={commands:0,passes:0,pixels:0,errors:0,blits:0,computePasses:0,dispatches:0,reads:0,lost:0};
  // Readbacks of this replay: [ticket, the buffer], mapped after the replay's commands.
  let reads=[];
  const of=g=>objs.get(g[1]);
  function reset(p){
    for(const o of objs.values())try{o.destroy?.();}catch{/* gone */}
    objs.clear();canvases.clear();page=p;
  }
  const warn=(what,error)=>{stats.errors++;console.warn(`foafnaut: page GPU ${what}:`,String(error?.message??error));};
  function one(c){
    switch(c.k){
      case 'canvas':{
        const texture=device.createTexture({size:[c.w,c.h],format:FORMAT,usage:c.usage});
        objs.set(c.g[1],texture);canvases.set(c.node,texture);break;
      }
      case 'buffer':objs.set(c.g[1],device.createBuffer({size:c.size,usage:c.usage}));break;
      case 'clear':{
        // Its own submit, before any later queue write to the buffer.
        const encoder=device.createCommandEncoder();encoder.clearBuffer(of(c.g),0,c.size);device.queue.submit([encoder.finish()]);break;
      }
      case 'write':{
        const bytes=Uint8Array.from(atob(c.data),ch=>ch.charCodeAt(0));
        device.queue.writeBuffer(of(c.g),c.offset,bytes);break;
      }
      case 'shader':objs.set(c.g[1],device.createShaderModule({code:c.code}));break;
      // Canvas 2D (docs/designissues/2026-11-08-canvas-2d.md): the pixels Lean drew, the whole canvas.
      case 'pixels':{
        const raw=Uint8Array.from(atob(c.data),ch=>ch.charCodeAt(0)),bytes=c.rle?unrle(raw,c.w,c.h):raw;
        device.queue.writeTexture({texture:of(c.g)},bytes,{bytesPerRow:c.w*4},[c.w,c.h]);stats.pixels++;break;
      }
      case 'pipeline':{
        const module=of(c.shader);
        objs.set(c.g[1],device.createRenderPipeline({layout:'auto',
          vertex:{module,entryPoint:c.vs,buffers:c.buffers},
          fragment:{module,entryPoint:c.fs,targets:[{format:FORMAT}]},
          primitive:{topology:c.topology}}));
        break;
      }
      case 'bind':{
        const pipeline=of(c.pipeline);
        objs.set(c.g[1],device.createBindGroup({layout:pipeline.getBindGroupLayout(0),
          entries:[{binding:0,resource:{buffer:of(c.buffer),offset:0,size:c.size}}]}));
        break;
      }
      case 'pass':{
        const target=of(c.canvas),encoder=device.createCommandEncoder();
        const pass=encoder.beginRenderPass({colorAttachments:[{view:target.createView(),loadOp:'clear',storeOp:'store',
          clearValue:{r:c.clear[0]/255,g:c.clear[1]/255,b:c.clear[2]/255,a:c.clear[3]/255}}]});
        for(const d of c.draws){
          pass.setPipeline(of(d.pipeline));
          if(d.bind)pass.setBindGroup(0,of(d.bind));
          d.vbufs.forEach((g,i)=>pass.setVertexBuffer(i,of(g)));
          pass.draw(d.count,d.instances,d.first,d.firstInstance);
        }
        pass.end();device.queue.submit([encoder.finish()]);stats.passes++;break;
      }
      case 'cpipeline':{
        const layout=device.createBindGroupLayout({entries:c.layout.map(([binding,type])=>({binding,visibility:GPUShaderStage.COMPUTE,buffer:BINDING[type]}))});
        const pipeline=device.createComputePipeline({layout:device.createPipelineLayout({bindGroupLayouts:[layout]}),
          compute:{module:of(c.shader),entryPoint:c.entry}});
        pipeline.foafnautLayout=layout;objs.set(c.g[1],pipeline);break;
      }
      case 'cbind':{
        const pipeline=of(c.pipeline);
        objs.set(c.g[1],device.createBindGroup({layout:pipeline.foafnautLayout,
          entries:c.entries.map(([binding,g,size])=>({binding,resource:{buffer:of(g),offset:0,size}}))}));
        break;
      }
      case 'cpass':{
        const encoder=device.createCommandEncoder(),pass=encoder.beginComputePass();
        for(const d of c.dispatches){
          pass.setPipeline(of(d.pipeline));
          if(d.bind)pass.setBindGroup(0,of(d.bind));
          pass.dispatchWorkgroups(d.x,d.y,d.z);stats.dispatches++;
        }
        pass.end();device.queue.submit([encoder.finish()]);stats.computePasses++;break;
      }
      case 'copy':{
        const encoder=device.createCommandEncoder();
        encoder.copyBufferToBuffer(of(c.src),c.srcOffset,of(c.dst),c.dstOffset,c.size);device.queue.submit([encoder.finish()]);break;
      }
      case 'read':reads.push([c.ticket,of(c.g),c.size]);break;
      case 'destroy':{
        const o=of(c.g);objs.delete(c.g[1]);
        for(const [node,t] of canvases)if(t===o)canvases.delete(node);
        try{o?.destroy?.();}catch{/* gone */}break;
      }
      default:throw Error('unknown page GPU command '+c.k);
    }
  }
  return {
    get stats(){return {...stats,objects:objs.size,canvases:canvases.size,page};},
    /** Replay Lean's host commands of page session `p`, in order. The answer is the
     * readbacks the commands asked for, for Lean (`gpuRead` action `results`): each
     * {ticket, dataBase64}, or {ticket, error:true} when the map failed. */
    async replay(p,commands){
      if(p!==page)reset(p);
      // a lost page: nothing more of its work reaches the GPU; Lean is told once
      if(p===lostPage){if(lostTold)return [];lostTold=true;return [{lost:true}];}
      reads=[];
      device.pushErrorScope('validation');
      for(const c of commands){
        if(c.g&&c.g[0]!==p||c.canvas&&c.canvas[0]!==p||c.src&&c.src[0]!==p||c.dst&&c.dst[0]!==p){warn('command','not of this page');continue;}
        try{one(c);stats.commands++;}catch(error){warn(c.k,error);}
      }
      const error=await device.popErrorScope();
      if(error)warn('validation',error);
      // the watchdog: the timer is cleared when the GPU has done this replay's work
      if(commands.some(c=>c.k==='pass'||c.k==='cpass'||c.k==='copy')){
        let done=false;
        const timer=setTimeout(()=>{if(done||page!==p)return;
          console.warn(`foafnaut: page GPU work of page ${p} did not finish in ${watchdogMs} ms: its GPU device is lost`);
          stats.lost++;lostPage=p;lostTold=false;reset(p);},watchdogMs);
        device.queue.onSubmittedWorkDone().then(()=>{done=true;clearTimeout(timer);},()=>{});
      }
      const now=reads;reads=[];
      return Promise.all(now.map(async([ticket,buffer,size])=>{
        try{
          await buffer.mapAsync(GPUMapMode.READ,0,size);
          const bytes=new Uint8Array(buffer.getMappedRange(0,size)).slice();buffer.unmap();stats.reads++;
          return {ticket,dataBase64:b64(bytes)};
        }catch(e){warn('read',e);return {ticket,error:true};}
      }));
    },
    /** Draw each page canvas into `target` (the page layer) at Lean's rectangles. */
    blit(target,rects,code){
      if(!rects?.length||!code)return false;
      let drawn=false;
      for(const {node,rect:r,clip} of rects){
        const texture=canvases.get(node);if(!texture)continue;
        if(code!==blitCode){
          const module=device.createShaderModule({code});
          blitPipeline=device.createRenderPipeline({layout:'auto',vertex:{module,entryPoint:'vertex'},
            fragment:{module,entryPoint:'fragment',targets:[{format:target.format}]},primitive:{topology:'triangle-list'}});
          blitCode=code;
        }
        rect??=device.createBuffer({size:16,usage:GPUBufferUsage.UNIFORM|GPUBufferUsage.COPY_DST});
        device.queue.writeBuffer(rect,0,new Float32Array(r));
        const bind=device.createBindGroup({layout:blitPipeline.getBindGroupLayout(0),entries:[
          {binding:0,resource:texture.createView()},{binding:1,resource:{buffer:rect}}]});
        const encoder=device.createCommandEncoder();
        const pass=encoder.beginRenderPass({colorAttachments:[{view:target.createView(),loadOp:'load',storeOp:'store'}]});
        pass.setPipeline(blitPipeline);pass.setBindGroup(0,bind);
        pass.setScissorRect(clip[0],clip[1],clip[2],clip[3]);
        pass.draw(3);pass.end();device.queue.submit([encoder.finish()]);
        stats.blits++;drawn=true;
      }
      return drawn;
    },
    close(){reset(-1);rect?.destroy();},
  };
}
