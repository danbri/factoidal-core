// Experimental actual WebGPU lowering of the two-pattern integer BGP.
// This is GPU predicate/join computation, not post-query packing.
// It fuses both typed pattern projections into count/probe and emit passes.
// No untrusted host join: JS handles buffers and validates declared bounds.
// Fixed UInt32 term IDs, one triple = (s,p,o), n <= 4096, <= 512 results.
export const MAX_TRIPLES = 4096;
export const MAX_SOLUTIONS = 512;
export const COUNT = `
struct Params { n:u32, kp:u32, wp:u32, atlas:u32, };
@group(0) @binding(0) var<storage,read> triples:array<u32>;
@group(0) @binding(1) var<storage,read_write> counts:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>) {
 let i=gid.x;
 if (i>=cfg.n) {return;}
 let a=3u*i;
 if (triples[a+1u]!=cfg.kp) {counts[i]=0u;return;}
 let key=triples[a+2u];
 var count=0u;
 for(var j=0u;j<cfg.n;j=j+1u){
   let b=3u*j;
   if(triples[b+1u]==cfg.wp && triples[b+2u]==cfg.atlas && triples[b]==key){
     count=count+1u;
   }
 }
 counts[i]=count;
}
`;
export const SCAN = `
struct Params { n:u32, kp:u32, wp:u32, atlas:u32, };
@group(0) @binding(1) var<storage,read> counts:array<u32>;
@group(0) @binding(2) var<storage,read_write> offsets:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(1,1,1)
fn main(){
 var sum=0u;
 for(var i=0u;i<cfg.n;i=i+1u){
   offsets[i]=sum;
   sum=sum+counts[i];
 }
 offsets[cfg.n]=sum;
}
`;
export const EMIT = `
struct Params { n:u32, kp:u32, wp:u32, atlas:u32, };
@group(0) @binding(0) var<storage,read> triples:array<u32>;
@group(0) @binding(2) var<storage,read> offsets:array<u32>;
@group(0) @binding(3) var<storage,read_write> result:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>){
 let i=gid.x;
 if(i>=cfg.n){return;}
 let a=3u*i;
 if(triples[a+1u]!=cfg.kp){return;}
 let person=triples[a];
 let key=triples[a+2u];
 var local=0u;
 for(var j=0u;j<cfg.n;j=j+1u){
   let b=3u*j;
   if(triples[b+1u]==cfg.wp && triples[b+2u]==cfg.atlas && triples[b]==key){
     let dst=2u*(offsets[i]+local);
     result[dst]=person;
     result[dst+1u]=key;
     local=local+1u;
   }
 }
}
`;

const validWord = x => Number.isInteger(x) && x >= 0 && x <= 0xffffffff;
export function validateTriples(rows, kp, wp, atlas) {
  if(!Array.isArray(rows)||rows.length>MAX_TRIPLES||![kp,wp,atlas].every(validWord))
    throw new RangeError("BGP admission: input length/terms");
  const unique=new Set();
  for(const t of rows){
    if(!Array.isArray(t)||t.length!==3||!t.every(validWord))
      throw new TypeError("Each triple must be exactly three unsigned 32-bit integers.");
    const key=t.join(",");
    if(unique.has(key))throw new Error("Duplicate RDF triple: source graph is a set.");
    unique.add(key);
  }
  return rows.length;
}
const uintWords = mapped => Array.from(new Uint32Array(mapped.slice(0)));
const size4 = n => Math.max(4, n*4);
async function compiled(device,label,source){
  const module=device.createShaderModule({label,code:source});
  const diagnostics=await module.getCompilationInfo();
  const errors=diagnostics.messages.filter(x=>x.type==="error");
  if(errors.length)throw new Error(label+": "+errors.map(x=>x.message).join("; "));
  return device.createComputePipeline({label,layout:"auto",compute:{module,entryPoint:"main"}});
}
export async function runIntegerBgpGpu(rows, options={}) {
  const kp=options.knows??7, wp=options.works??11, atlas=options.atlas??12;
  const n=validateTriples(rows,kp,wp,atlas);
  const limit=options.maxSolutions??MAX_SOLUTIONS;
  if(!Number.isInteger(limit)||limit<0||limit>MAX_SOLUTIONS)throw new RangeError("Solution capacity");
  if(!navigator.gpu)throw new Error("No WebGPU available; no GPU query executed.");
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter)throw new Error("No WebGPU adapter; no GPU query executed.");
  const device=await adapter.requestDevice();
  const owned=[];
  const make=(bytes,usage,label)=>{
    const b=device.createBuffer({size:Math.max(4,bytes),usage,label});owned.push(b);return b;
  };
  const G=GPUBufferUsage, M=GPUMapMode;
  let lost=false;
  void device.lost.then(()=>{lost=true;});
  try {
    const [countPipeline,scanPipeline,emitPipeline]=await Promise.all([
      compiled(device,"count BGP matches",COUNT),
      compiled(device,"exclusive scan BGP matches",SCAN),
      compiled(device,"emit BGP solutions",EMIT),
    ]);
    const tripdata=new Uint32Array(rows.flat());
    const cfgdata=new Uint32Array([n,kp,wp,atlas]);
    const graph=make(tripdata.byteLength,G.STORAGE|G.COPY_DST,"triple graph");
    const cfg=make(16,G.UNIFORM|G.COPY_DST,"query constants");
    const count=make(size4(n),G.STORAGE|G.COPY_SRC,"counts");
    const offsets=make(size4(n+1),G.STORAGE|G.COPY_SRC,"offsets");
    const countRead=make(size4(n),G.COPY_DST|G.MAP_READ,"count readback");
    const offsetRead=make(size4(n+1),G.COPY_DST|G.MAP_READ,"offset readback");
    if(tripdata.byteLength)device.queue.writeBuffer(graph,0,tripdata);
    device.queue.writeBuffer(cfg,0,cfgdata);
    const group=(pipeline,entries)=>device.createBindGroup({
      layout:pipeline.getBindGroupLayout(0),
      entries:entries.map(([binding,buffer])=>({binding,resource:{buffer}})),
    });
    const encoder=device.createCommandEncoder();
    if(n){
      const p=encoder.beginComputePass();
      p.setPipeline(countPipeline);p.setBindGroup(0,group(countPipeline,[[0,graph],[1,count],[4,cfg]]));
      p.dispatchWorkgroups(Math.ceil(n/64));p.end();
    }
    const p=encoder.beginComputePass();
    p.setPipeline(scanPipeline);p.setBindGroup(0,group(scanPipeline,[[1,count],[2,offsets],[4,cfg]]));
    p.dispatchWorkgroups(1);p.end();
    if(n)encoder.copyBufferToBuffer(count,0,countRead,0,n*4);
    encoder.copyBufferToBuffer(offsets,0,offsetRead,0,(n+1)*4);
    device.queue.submit([encoder.finish()]);
    await Promise.all([offsetRead.mapAsync(M.READ),...(n?[countRead.mapAsync(M.READ)]:[])]);
    const counts=n?uintWords(countRead.getMappedRange()):[];
    const starts=uintWords(offsetRead.getMappedRange());
    offsetRead.unmap();if(n)countRead.unmap();
    if(lost||starts[0]!==0||starts.length!==n+1)throw new Error("GPU offsets unavailable.");
    for(let i=0;i<n;i++){
      if(starts[i+1]!==starts[i]+counts[i])throw new Error("GPU prefix is inconsistent.");
    }
    const total=starts[n];
    if(total>limit)throw new RangeError("GPU query exceeded admitted output capacity.");
    const allocated=new Uint32Array(2*total+2);
    allocated.fill(0x7ea7cafe,0,2*total);
    allocated.set([0xc0decafe,0xd00dcafe],2*total);
    const out=make(allocated.byteLength,G.STORAGE|G.COPY_DST|G.COPY_SRC,"BGP output pairs");
    const outRead=make(allocated.byteLength,G.COPY_DST|G.MAP_READ,"BGP output readback");
    device.queue.writeBuffer(out,0,allocated);
    const end=device.createCommandEncoder();
    if(n){
      const write=end.beginComputePass();
      write.setPipeline(emitPipeline);
      write.setBindGroup(0,group(emitPipeline,[[0,graph],[2,offsets],[3,out],[4,cfg]]));
      write.dispatchWorkgroups(Math.ceil(n/64));
      write.end();
    }
    end.copyBufferToBuffer(out,0,outRead,0,allocated.byteLength);
    device.queue.submit([end.finish()]);
    await outRead.mapAsync(M.READ);
    const result=uintWords(outRead.getMappedRange());outRead.unmap();
    if(lost||result.at(-2)!==0xc0decafe||result.at(-1)!==0xd00dcafe)
      throw new Error("GPU output canary failed or device was lost.");
    const pairs=Array.from({length:total},(_,i)=>[result[2*i],result[2*i+1]]);
    return {
      triples:n,pairs,counts,offsets:starts,solutionCount:total,
      engine:"Actual WebGPU count→scan→emit BGP, not host-computed results",
      adapter:adapter.info?.device||adapter.info?.description||"not reported",
      isFallbackAdapter:adapter.info?.isFallbackAdapter??null,
    };
  } finally {
    for(const buf of owned)buf.destroy();
    device.destroy();
  }
}
