import {createOffscreenSession,render} from "./gpu_transport.ts";
const frame={width:1,height:1,data:Array(16).fill(0),wgsl:"shader fixture, not GPU validation",checks:[{x:0,y:0,rgb:[18,24,39]}]};
const assert=(b:boolean,m:string)=>{if(!b)throw new Error(m);};
async function rejects(f:()=>Promise<unknown>,s:string){try{await f();}catch(e){assert(String(e).includes(s),String(e));return;}throw new Error("Expected rejection");}
function mock(failSetup=false,corrupt=false){
 const calls:string[]=[];
 const bytes=new Uint8Array(256);bytes.set([18,24,corrupt?0:39,255]);
 const buffer=(readback:boolean)=>({destroy(){calls.push(readback?"destroy-readback":"destroy-storage");},async mapAsync(){calls.push("map");},getMappedRange(){return bytes.buffer;},unmap(){calls.push("unmap");}});
 const pass={setPipeline(){},setBindGroup(){},draw(){calls.push("draw");},end(){}};
 const device={limits:{maxUniformBufferBindingSize:65536,maxStorageBufferBindingSize:1048576,maxBufferSize:268435456,maxTextureDimension2D:4096},
  pushErrorScope(){},async popErrorScope(){return null;},destroy(){calls.push("destroy-device");},
  createShaderModule(){calls.push("shader");return {async getCompilationInfo(){return {messages:[]};}};},
  async createRenderPipelineAsync(){calls.push("pipeline");return {getBindGroupLayout:()=>({})};},
  createBindGroup(){return {};},
  createBuffer(d:GPUBufferDescriptor){calls.push("buffer");return buffer((d.usage&GPUBufferUsage.MAP_READ)!==0);},
  createTexture(){if(failSetup)throw new Error("texture setup failed");calls.push("texture");return {createView:()=>({}),destroy(){calls.push("destroy-texture");}};},
  createCommandEncoder(){return {beginRenderPass:()=>pass,copyTextureToBuffer(){},finish:()=>({})};},
  queue:{writeBuffer(){calls.push("upload");},submit(){calls.push("submit");}}};
 return {calls,gpu:{async requestAdapter(){return {info:{description:"transport mock"},async requestDevice(){return device;}};}}};
}
async function withGPU<T>(gpu:unknown,run:()=>Promise<T>){
 const own=Object.getOwnPropertyDescriptor(navigator,"gpu");Object.defineProperty(navigator,"gpu",{value:gpu,configurable:true});
 try{return await run();}finally{if(own)Object.defineProperty(navigator,"gpu",own);else delete (navigator as unknown as {gpu?:unknown}).gpu;}
}
Deno.test("offscreen sessions keep one pipeline and resident buffers across validated readbacks",async()=>{
 const m=mock();await withGPU(m.gpu,async()=>{
  const session=await createOffscreenSession(frame,"svg-offscreen");assert(!!session,"missing mock session");
  for(let i=0;i<3;i++){const pixels=await session!.draw();assert(pixels[2]===39,"readback changed");}
  const first=session!.draw();await rejects(()=>session!.draw(),"Concurrent");await first;
  const stats=session!.stats;
  assert(stats.shaderModules===1&&stats.pipelines===1&&stats.buffers===2&&stats.textures===1&&stats.uploads===1&&stats.frames===4&&stats.submissions===4,JSON.stringify(stats));
  assert(m.calls.filter(x=>x==="shader").length===1&&m.calls.filter(x=>x==="upload").length===1,"resources rebuilt");
  session!.close();session!.close();assert(m.calls.filter(x=>x==="destroy-device").length===1,"dispose not idempotent");
  await rejects(()=>session!.draw(),"closed");
 });
});
Deno.test("offscreen session setup/readback failure closes owned resources and cannot continue",async()=>{
 const setup=mock(true);await withGPU(setup.gpu,async()=>{await rejects(()=>createOffscreenSession(frame,"svg-offscreen"),"texture setup failed");assert(setup.calls.includes("destroy-device")&&setup.calls.includes("destroy-storage"),"partial setup leaked");});
 const bad=mock(false,true);await withGPU(bad.gpu,async()=>{const s=await createOffscreenSession(frame,"svg-offscreen");await rejects(()=>s!.draw(),"readback mismatch");assert(s!.stats.frames===0&&s!.stats.failed,"failed frame counted");await rejects(()=>s!.draw(),"failed");s!.close();assert(bad.calls.includes("destroy-readback")&&bad.calls.includes("destroy-device"),"readback failure leaked");});
 await withGPU({requestAdapter:async()=>null},async()=>{assert(await render(frame,"svg-offscreen")===null,"null adapter is a render success");});
});

Deno.test("compatible scene updates retain resources and use new pixel expectations",async()=>{
 const m=mock();await withGPU(m.gpu,async()=>{
  const s=(await createOffscreenSession(frame,"svg-offscreen"))!;
  const next={...frame,data:frame.data.map((v,i)=>i===0?1:v)};
  assert(await s.update(next),"compatible payload refused");await s.draw();
  for(const different of [{...next,width:2},{...next,height:2},{...next,wgsl:"different shader"},{...next,data:[...next.data,0,0,0,0]}]){
   assert(!(await s.update(different)),"incompatible payload reused");
  }
  assert(s.stats.uploads===2&&s.stats.pipelines===1&&s.stats.buffers===2&&s.stats.frames===1,JSON.stringify(s.stats));
  const drawing=s.draw();await rejects(()=>s.update(next),"Concurrent");await drawing;
  const changed={...next,checks:[{x:0,y:0,rgb:[255,255,255]}]};
  assert(await s.update(changed),"new expectations refused");
  changed.checks[0].rgb[0]=18;changed.checks[0].rgb[1]=24;changed.checks[0].rgb[2]=39;
  await rejects(()=>s.draw(),"readback mismatch");assert(s.stats.failed,"stale expectations used");
  s.close();await rejects(()=>s.update(next),"closed");
 });
});

Deno.test("scene updates retain Lean payload validation",async()=>{
 const m=mock();await withGPU(m.gpu,async()=>{
  const s=(await createOffscreenSession(frame,"svg-offscreen"))!;
  await rejects(()=>s.update({...frame,data:frame.data.map((v,i)=>i===0?NaN:v)}),"Invalid render-plan ABI inputs");
  assert(s.stats.uploads===1&&s.stats.failed,"invalid payload uploaded or session remained usable");s.close();
 });
});
