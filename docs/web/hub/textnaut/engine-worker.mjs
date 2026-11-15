// The shared engine's worker: one built-in engine (engine-core.mjs) for every view of the page
// (the Textnaut page, or every cell of a notebook). It starts when the page first asks for a
// view (engine.mjs creates this worker then), so a page that never asks loads nothing.
// Requests are answered one at a time, in order: the engine and the GPU session are one each.
import {createEngineCore} from './engine-core.mjs';

const runtimeBase=new URL('../html-webgpu/runtime/',import.meta.url);
// The engine module compiles while it downloads (as the Foafnaut Hub page's worker does).
const compiled=(async()=>{
  const url=new URL('web-render.wasm',runtimeBase);
  try{if(typeof WebAssembly.compileStreaming==='function')return await WebAssembly.compileStreaming(fetch(url,{credentials:'same-origin'}));}catch{/* compile the bytes */}
  const response=await fetch(url,{credentials:'same-origin'});
  if(!response.ok)throw Error(`the engine did not load: HTTP ${response.status}`);
  return WebAssembly.compile(await response.arrayBuffer());
})();
compiled.catch(()=>{});
const loader=import('../html-webgpu/runtime/web-render.mjs');loader.catch(()=>{});

async function gpu(){
  if(!self.navigator?.gpu)return undefined;
  let adapter;try{adapter=await navigator.gpu.requestAdapter();}catch{return undefined;}
  if(!adapter)return undefined;
  const transport=await import('../html-webgpu/runtime/gpu-transport.mjs');
  let session;
  return {async draw(artifact){
    if(session&&(typeof session.update!=='function'||!(await session.update(artifact)))){session.close();session=undefined;}
    session??=await transport.createOffscreenSession(artifact,'svg-offscreen');
    if(!session)throw Error('no WebGPU device');
    const t0=performance.now(),rgba=await session.draw();
    return {rgba,gpuMs:performance.now()-t0};
  }};
}

const core=createEngineCore({
  createModule:async options=>(await loader).default(options),
  compiled,
  origin:self.location.origin,
  fontURL:new URL('../foafnaut/fonts/noto-sans/NotoSans-Regular.ttf',import.meta.url).href,
  async fetchBytes(url){
    const response=await fetch(url,{credentials:'same-origin'});
    if(!response.ok)throw Error(`HTTP ${response.status} for ${url}`);
    return {url:response.url||url,bytes:new Uint8Array(await response.arrayBuffer()),contentType:response.headers.get('content-type')??''};
  },
  gpu,
  grid:()=>import('./grid.mjs'),
});

const ops={
  ready:()=>core.ready(),
  open:(id,input,options)=>core.open(id,input,options),
  textGrid:(id,input,options)=>core.textGrid(id,input,options),
  click:(id,x,y)=>core.click(id,x,y),
  linkAt:(id,x,y)=>core.linkAt(id,x,y),
  close:id=>core.close(id),
};
let queue=Promise.resolve();
self.onmessage=({data})=>{
  const {id,op,args}=data??{};
  queue=queue.then(async()=>{
    try{
      if(!Object.hasOwn(ops,op))throw Error(`unknown request ${op}`);
      const result=await ops[op](...(args??[]));
      const pixels=result?.rgba??result?.frame?.rgba;
      self.postMessage({id,result},pixels?.buffer?[pixels.buffer]:[]);
    }catch(error){self.postMessage({id,error:String(error?.message??error)});}
  });
};
