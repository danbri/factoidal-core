// Can two Deno workers share one WebGPU device? (issue 1031; docs/designissues/
// 2026-11-26-foafnaut-engine-sessions.md section 7.) A repeatable check, no person needed:
//
//   VK_ICD_FILENAMES=/usr/share/vulkan/icd.d/lvp_icd.json \
//     deno run --unstable-webgpu -A tools/webgpu_share_check.ts
//
// It asks, and prints one JSON line per answer:
//  1. structuredClone of a GPUDevice, a GPUBuffer and a GPUTexture (the algorithm postMessage uses);
//  2. postMessage of a GPUDevice to a worker;
//  3. a device in each of two workers on the same adapter: each writes a buffer, a compute pass
//     doubles it, and the worker reads it back (each device works alone);
//  4. the resident memory of the process before and after each worker's device.
// It checks what Deno does, not what the WebGPU specification says.
const say=(record:Record<string,unknown>)=>console.log(JSON.stringify(record));
const rssMB=()=>Math.round(Deno.memoryUsage().rss/1048576*10)/10;

const workerSource=`
const rssMB=()=>Math.round(Deno.memoryUsage().rss/1048576*10)/10;
self.onmessage=async(event)=>{
  if(event.data?.kind==="device-message"){const d=event.data.device;
    let usable=false,error="";try{d.createBuffer({size:16,usage:GPUBufferUsage.COPY_DST});usable=true;}catch(e){error=String(e);}
    self.postMessage({kind:"device-message",type:typeof d,isGPUDevice:d instanceof GPUDevice,keys:Object.keys(d??{}),createBuffer:typeof d?.createBuffer,usable,error});return;}
  const before=rssMB(),t0=performance.now();
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter){self.postMessage({kind:"compute",ok:false,error:"no adapter"});return;}
  const device=await adapter.requestDevice();
  const made=performance.now()-t0,after=rssMB();
  const n=1024,data=new Float32Array(n).map((_,i)=>i+event.data.offset);
  const buffer=device.createBuffer({size:n*4,usage:GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_SRC|GPUBufferUsage.COPY_DST});
  device.queue.writeBuffer(buffer,0,data);
  const module=device.createShaderModule({code:"@group(0) @binding(0) var<storage,read_write> v:array<f32>; @compute @workgroup_size(64) fn main(@builtin(global_invocation_id) id:vec3<u32>){ if(id.x<arrayLength(&v)){v[id.x]=v[id.x]*2.0;} }"});
  const pipeline=device.createComputePipeline({layout:"auto",compute:{module,entryPoint:"main"}});
  const bind=device.createBindGroup({layout:pipeline.getBindGroupLayout(0),entries:[{binding:0,resource:{buffer}}]});
  const read=device.createBuffer({size:n*4,usage:GPUBufferUsage.MAP_READ|GPUBufferUsage.COPY_DST});
  const encoder=device.createCommandEncoder(),pass=encoder.beginComputePass();
  pass.setPipeline(pipeline);pass.setBindGroup(0,bind);pass.dispatchWorkgroups(n/64);pass.end();
  encoder.copyBufferToBuffer(buffer,0,read,0,n*4);device.queue.submit([encoder.finish()]);
  await read.mapAsync(GPUMapMode.READ);
  const out=new Float32Array(read.getMappedRange().slice(0));read.unmap();
  const ok=out.every((v,i)=>v===2*(i+event.data.offset));
  self.postMessage({kind:"compute",ok,adapter:adapter.info?.description??"",deviceMs:Math.round(made*10)/10,rssBeforeMB:before,rssAfterMB:after,first:out[0],last:out[n-1]});
  device.destroy();
};`;
const workerURL=URL.createObjectURL(new Blob([workerSource],{type:"text/javascript"}));
const ask=(worker:Worker,message:unknown)=>new Promise<Record<string,unknown>>((resolve,reject)=>{
  worker.onmessage=event=>resolve(event.data);worker.onerror=event=>{event.preventDefault();reject(new Error(event.message));};
  worker.postMessage(message);
});

const adapter=await navigator.gpu.requestAdapter();
if(!adapter){say({check:"adapter",ok:false,error:"no WebGPU adapter (set VK_ICD_FILENAMES for a software one)"});Deno.exit(2);}
say({check:"adapter",ok:true,description:adapter.info?.description??"",vendor:adapter.info?.vendor??""});
const rss0=rssMB();
const device=await adapter.requestDevice();
say({check:"main device",ok:true,rssBeforeMB:rss0,rssAfterMB:rssMB()});
const buffer=device.createBuffer({size:16,usage:GPUBufferUsage.COPY_DST});
const texture=device.createTexture({size:[4,4],format:"rgba8unorm",usage:GPUTextureUsage.TEXTURE_BINDING});
for(const [name,value] of [["GPUDevice",device],["GPUBuffer",buffer],["GPUTexture",texture]] as const){
  // A clone that is not the object's kind (a plain object with no methods) is not a share.
  try{const copy=structuredClone(value) as Record<string,unknown>;
    say({check:`structuredClone ${name}`,cloned:true,sameKind:Object.getPrototypeOf(copy)===Object.getPrototypeOf(value),keys:Object.keys(copy),methods:typeof copy.destroy});}
  catch(error){say({check:`structuredClone ${name}`,cloned:false,error:`${(error as Error).name}: ${(error as Error).message}`});}
}
const w1=new Worker(workerURL,{type:"module"}),w2=new Worker(workerURL,{type:"module"});
try{const answer=await ask(w1,{kind:"device-message",device});say({check:"postMessage GPUDevice",sent:true,answer});}
catch(error){say({check:"postMessage GPUDevice",sent:false,error:`${(error as Error).name}: ${(error as Error).message}`});}
// One worker after the other, then both at once.
for(const [name,worker,offset] of [["worker 1",w1,0],["worker 2",w2,1000]] as const)
  say({check:`device in ${name}`,...await ask(worker,{kind:"compute",offset})});
const both=await Promise.all([ask(w1,{kind:"compute",offset:5}),ask(w2,{kind:"compute",offset:7})]);
say({check:"devices in both workers at once",ok:both.every(b=>b.ok===true),answers:both});
w1.terminate();w2.terminate();device.destroy();
say({check:"done",rssMB:rssMB()});
