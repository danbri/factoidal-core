// Page GPU commands on the Hub (docs/designissues/2026-11-08-page-gpu.md). A page script's
// WebGPU calls reach Lean as typed commands; Lean (L4Factoidal.PageGpu) validates each one,
// prints the WGSL it allows, and emits host commands. This replays those host commands on
// the layer surface's device and draws each page canvas into the page layer at the
// rectangle and clip Lean gives (render answer `layers.canvases`), with Lean's blit WGSL.
// Every id, size, offset, usage, shader text and rectangle is Lean's; this decides nothing.
// The page's objects are kept apart from the engine's (a table per page session).

const FORMAT='rgba8unorm';
// The full image of each 2D canvas, for the replay log (a new device needs the whole canvas,
// a turn sends only the rectangle that changed). Only copies bytes.
export function canvasImages(){
  const images=new Map();
  return {
    /** The command to log for `c`: a texture's, or the canvas's whole image after `c`'s rectangle. */
    take(c){
      if(c.k==='canvas'&&c.twoD){images.set(c.g[1],{w:c.w,h:c.h,bytes:new Uint8Array(c.w*c.h*4)});return c;}
      if(c.k!=='pixels'||!c.bytes)return c;
      const im=images.get(c.g[1]);if(!im)return c;
      for(let y=0;y<c.h;y++)im.bytes.set(c.bytes.subarray(y*c.w*4,(y+1)*c.w*4),((c.y+y)*im.w+c.x)*4);
      return {k:'pixels',g:c.g,x:0,y:0,w:im.w,h:im.h,bytes:im.bytes};
    },
  };
}

export function createPageGpu(device){
  let page=-1,blitCode='',blitPipeline,rect;
  const objs=new Map(),canvases=new Map(),stats={commands:0,passes:0,pixels:0,errors:0,blits:0};
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
        // A rectangle of Lean's pixels (straight RGBA, raw bytes from the host's bytes call).
        if(!c.bytes){warn('pixels','no bytes');break;}
        if(c.w>0&&c.h>0)device.queue.writeTexture({texture:of(c.g),origin:[c.x??0,c.y??0]},c.bytes,{bytesPerRow:c.w*4},[c.w,c.h]);
        stats.pixels++;break;
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
    /** Replay Lean's host commands of page session `p`, in order. */
    async replay(p,commands){
      if(p!==page)reset(p);
      device.pushErrorScope('validation');
      for(const c of commands){
        if(c.g&&c.g[0]!==p||c.canvas&&c.canvas[0]!==p){warn('command','not of this page');continue;}
        try{one(c);stats.commands++;}catch(error){warn(c.k,error);}
      }
      const error=await device.popErrorScope();
      if(error)warn('validation',error);
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
