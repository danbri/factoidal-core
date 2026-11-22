// Second, genuinely relational WebGPU lowering for the same bounded u32 BGP.
// Unlike the first fused O(T^2) probe, this explicitly MATERIALISES the
// two typed pattern relations on GPU using mark->scan->stable scatter,
// then joins only the compacted relations, including every match.
// All predicate tests, compaction writes, join comparisons and output
// mapping are WGSL executions; host only allocates/reads/checks buffers.
import {validateTriples,MAX_TRIPLES,MAX_SOLUTIONS} from "./integer-bgp-gpu.mjs";

export const PROJECT_MARK=`
struct Params { n:u32, knows:u32, works:u32, atlas:u32, };
@group(0) @binding(0) var<storage,read> triples:array<u32>;
@group(0) @binding(1) var<storage,read_write> leftFlags:array<u32>;
@group(0) @binding(2) var<storage,read_write> rightFlags:array<u32>;
@group(0) @binding(3) var<uniform> cfg:Params;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>){
 let i=gid.x;
 if(i>=cfg.n){return;}
 let j=3u*i;
 leftFlags[i]=select(0u,1u,triples[j+1u]==cfg.knows);
 rightFlags[i]=select(0u,1u,
   triples[j+1u]==cfg.works && triples[j+2u]==cfg.atlas);
}
`;
export const PROJECT_SCAN=`
struct Params { n:u32, knows:u32, works:u32, atlas:u32, };
@group(0) @binding(0) var<storage,read> leftFlags:array<u32>;
@group(0) @binding(1) var<storage,read> rightFlags:array<u32>;
@group(0) @binding(2) var<storage,read_write> leftOffsets:array<u32>;
@group(0) @binding(3) var<storage,read_write> rightOffsets:array<u32>;
@group(0) @binding(4) var<uniform> cfg:Params;
@compute @workgroup_size(1,1,1)
fn main(){
 var l=0u;
 var r=0u;
 for(var i=0u;i<cfg.n;i=i+1u){
   leftOffsets[i]=l;rightOffsets[i]=r;
   l=l+leftFlags[i];r=r+rightFlags[i];
 }
 leftOffsets[cfg.n]=l;
 rightOffsets[cfg.n]=r;
}
`;
export const PROJECT_SCATTER=`
struct Params { n:u32, knows:u32, works:u32, atlas:u32, };
@group(0) @binding(0) var<storage,read> triples:array<u32>;
@group(0) @binding(1) var<storage,read> leftFlags:array<u32>;
@group(0) @binding(2) var<storage,read> rightFlags:array<u32>;
@group(0) @binding(3) var<storage,read> leftOffsets:array<u32>;
@group(0) @binding(4) var<storage,read> rightOffsets:array<u32>;
@group(0) @binding(5) var<storage,read_write> leftRows:array<u32>;
@group(0) @binding(6) var<storage,read_write> rightRows:array<u32>;
@group(0) @binding(7) var<uniform> cfg:Params;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>){
 let i=gid.x;if(i>=cfg.n){return;}
 let j=3u*i;
 if(leftFlags[i]!=0u){
   let dest=2u*leftOffsets[i];
   leftRows[dest]=triples[j];
   leftRows[dest+1u]=triples[j+2u];
 }
 if(rightFlags[i]!=0u){rightRows[rightOffsets[i]]=triples[j];}
}
`;
export const JOIN_COUNT=`
struct Bounds { leftCount:u32,rightCount:u32,unusedA:u32,unusedB:u32, };
@group(0) @binding(0) var<storage,read> leftRows:array<u32>;
@group(0) @binding(1) var<storage,read> rightRows:array<u32>;
@group(0) @binding(2) var<storage,read_write> counts:array<u32>;
@group(0) @binding(3) var<uniform> bounds:Bounds;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>){
 let i=gid.x;if(i>=bounds.leftCount){return;}
 let key=leftRows[2u*i+1u];
 var c=0u;
 for(var j=0u;j<bounds.rightCount;j=j+1u){
   if(rightRows[j]==key){c=c+1u;}
 }
 counts[i]=c;
}
`;
export const JOIN_SCAN=`
struct Bounds { leftCount:u32,rightCount:u32,unusedA:u32,unusedB:u32, };
@group(0) @binding(0) var<storage,read> counts:array<u32>;
@group(0) @binding(1) var<storage,read_write> offsets:array<u32>;
@group(0) @binding(2) var<uniform> bounds:Bounds;
@compute @workgroup_size(1,1,1)
fn main(){
 var n=0u;
 for(var i=0u;i<bounds.leftCount;i=i+1u){
   offsets[i]=n;n=n+counts[i];
 }
 offsets[bounds.leftCount]=n;
}
`;
export const JOIN_EMIT=`
struct Bounds { leftCount:u32,rightCount:u32,unusedA:u32,unusedB:u32, };
@group(0) @binding(0) var<storage,read> leftRows:array<u32>;
@group(0) @binding(1) var<storage,read> rightRows:array<u32>;
@group(0) @binding(2) var<storage,read> offsets:array<u32>;
@group(0) @binding(3) var<storage,read_write> output:array<u32>;
@group(0) @binding(4) var<uniform> bounds:Bounds;
@compute @workgroup_size(64,1,1)
fn main(@builtin(global_invocation_id) gid:vec3<u32>){
 let i=gid.x;if(i>=bounds.leftCount){return;}
 let person=leftRows[2u*i];
 let key=leftRows[2u*i+1u];
 var local=0u;
 for(var j=0u;j<bounds.rightCount;j=j+1u){
   if(rightRows[j]==key){
     let dst=2u*(offsets[i]+local);
     output[dst]=person;output[dst+1u]=key;
     local=local+1u;
   }
 }
}
`;
export const SHADERS=[PROJECT_MARK,PROJECT_SCAN,PROJECT_SCATTER,JOIN_COUNT,JOIN_SCAN,JOIN_EMIT];
const words=buffer=>Array.from(new Uint32Array(buffer.slice(0)));
const size4=n=>Math.max(4,n*4);
async function compile(device,code,label){
  const module=device.createShaderModule({label,code});
  const result=await module.getCompilationInfo();
  const errors=result.messages.filter(m=>m.type==="error");
  if(errors.length)throw new Error(label+" WGSL: "+errors.map(m=>m.message).join("; "));
  return device.createComputePipeline({layout:"auto",compute:{module,entryPoint:"main"},label});
}
export async function runCompactedBgpGpu(triples,options={}){
  const kp=options.knows??7,wp=options.works??11,atlas=options.atlas??12;
  const n=validateTriples(triples,kp,wp,atlas);
  const maxSolutions=options.maxSolutions??MAX_SOLUTIONS;
  if(!Number.isInteger(maxSolutions)||maxSolutions<0||maxSolutions>MAX_SOLUTIONS)
    throw new RangeError("Bad maximum BGP result capacity");
  if(!navigator.gpu)throw new Error("WebGPU unavailable: no GPU BGP executed.");
  const adapter=await navigator.gpu.requestAdapter();
  if(!adapter)throw new Error("No WebGPU adapter: no GPU BGP executed.");
  const device=await adapter.requestDevice();
  const G=GPUBufferUsage,M=GPUMapMode,owned=[];
  const make=(bytes,usage,label)=>{
    const b=device.createBuffer({size:Math.max(bytes,4),usage,label});owned.push(b);return b;
  };
  const bind=(pipeline,pairs)=>device.createBindGroup({
    layout:pipeline.getBindGroupLayout(0),
    entries:pairs.map(([binding,buffer])=>({binding,resource:{buffer}})),
  });
  const read=async(buffer,n)=>{
    if(!n)return [];
    await buffer.mapAsync(M.READ);
    const data=words(buffer.getMappedRange()).slice(0,n);
    buffer.unmap();return data;
  };
  let lost=false;
  void device.lost.then(()=>{lost=true;});
  try{
    const pipelines=await Promise.all(SHADERS.map((code,i)=>compile(device,code,
      ["project/mark","project/scan","project/stable-scatter",
       "join/count","join/scan","join/emit"][i])));
    const t=new Uint32Array(triples.flat());
    const graph=make(t.byteLength,G.STORAGE|G.COPY_DST,"encoded source RDF triples");
    const cfg=make(16,G.UNIFORM|G.COPY_DST,"query pattern IDs");
    if(t.length)device.queue.writeBuffer(graph,0,t);
    device.queue.writeBuffer(cfg,0,new Uint32Array([n,kp,wp,atlas]));
    const lflags=make(size4(n),G.STORAGE,"left selection flags");
    const rflags=make(size4(n),G.STORAGE,"right selection flags");
    const loff=make(size4(n+1),G.STORAGE|G.COPY_SRC,"left selection offsets");
    const roff=make(size4(n+1),G.STORAGE|G.COPY_SRC,"right selection offsets");
    const lscanRead=make(size4(n+1),G.COPY_DST|G.MAP_READ,"left scan readback");
    const rscanRead=make(size4(n+1),G.COPY_DST|G.MAP_READ,"right scan readback");
    const enc=device.createCommandEncoder();
    if(n){
      const p=enc.beginComputePass();
      p.setPipeline(pipelines[0]);
      p.setBindGroup(0,bind(pipelines[0],[[0,graph],[1,lflags],[2,rflags],[3,cfg]]));
      p.dispatchWorkgroups(Math.ceil(n/64));p.end();
    }
    {
      const p=enc.beginComputePass();
      p.setPipeline(pipelines[1]);p.setBindGroup(0,bind(pipelines[1],
        [[0,lflags],[1,rflags],[2,loff],[3,roff],[4,cfg]]));
      p.dispatchWorkgroups(1);p.end();
    }
    enc.copyBufferToBuffer(loff,0,lscanRead,0,4*(n+1));
    enc.copyBufferToBuffer(roff,0,rscanRead,0,4*(n+1));
    device.queue.submit([enc.finish()]);
    const [Loff,Roff]=await Promise.all([read(lscanRead,n+1),read(rscanRead,n+1)]);
    const L=Loff[n],R=Roff[n];
    if(lost||L>n||R>n)throw new Error("Invalid GPU projection lengths.");
    const left=make(size4(2*L),G.STORAGE|G.COPY_SRC,"projected knows pairs");
    const right=make(size4(R),G.STORAGE|G.COPY_SRC,"projected Atlas subjects");
    const lread=make(size4(2*L),G.COPY_DST|G.MAP_READ,"knows projection readback");
    const rread=make(size4(R),G.COPY_DST|G.MAP_READ,"Atlas projection readback");
    const bound=make(16,G.UNIFORM|G.COPY_DST,"join row counts");
    device.queue.writeBuffer(bound,0,new Uint32Array([L,R,0,0]));
    const counts=make(size4(L),G.STORAGE|G.COPY_SRC,"compact join counts");
    const offsets=make(size4(L+1),G.STORAGE|G.COPY_SRC,"compact join offsets");
    const countRead=make(size4(L),G.COPY_DST|G.MAP_READ,"compact count readback");
    const offsetRead=make(size4(L+1),G.COPY_DST|G.MAP_READ,"compact offsets readback");
    const second=device.createCommandEncoder();
    if(n){
      const p=second.beginComputePass();
      p.setPipeline(pipelines[2]);p.setBindGroup(0,bind(pipelines[2],
        [[0,graph],[1,lflags],[2,rflags],[3,loff],[4,roff],
         [5,left],[6,right],[7,cfg]]));
      p.dispatchWorkgroups(Math.ceil(n/64));p.end();
    }
    if(L){
      const p=second.beginComputePass();
      p.setPipeline(pipelines[3]);p.setBindGroup(0,bind(pipelines[3],
        [[0,left],[1,right],[2,counts],[3,bound]]));
      p.dispatchWorkgroups(Math.ceil(L/64));p.end();
    }
    {
      const p=second.beginComputePass();
      p.setPipeline(pipelines[4]);p.setBindGroup(0,bind(pipelines[4],
        [[0,counts],[1,offsets],[2,bound]]));
      p.dispatchWorkgroups(1);p.end();
    }
    if(L)second.copyBufferToBuffer(left,0,lread,0,8*L);
    if(R)second.copyBufferToBuffer(right,0,rread,0,4*R);
    if(L)second.copyBufferToBuffer(counts,0,countRead,0,4*L);
    second.copyBufferToBuffer(offsets,0,offsetRead,0,4*(L+1));
    device.queue.submit([second.finish()]);
    const [Lraw,Rraw,Craw,Oraw]=await Promise.all([
      read(lread,2*L),read(rread,R),read(countRead,L),read(offsetRead,L+1)]);
    if(lost||Oraw[0]!==0||Oraw.length!==L+1)throw new Error("Invalid compact join prefix.");
    for(let i=0;i<L;i++)
      if(Oraw[i+1]!==Oraw[i]+Craw[i])throw new Error("Inconsistent compact join scan.");
    const total=Oraw[L];
    if(total>maxSolutions)throw new RangeError("GPU compact BGP result limit exceeded.");
    const initial=new Uint32Array(2*total+2);
    initial.fill(0x7ea7cafe,0,2*total);
    initial.set([0xc0decafe,0xd00dcafe],2*total);
    const output=make(initial.byteLength,G.STORAGE|G.COPY_DST|G.COPY_SRC,"joined pairs");
    const outputRead=make(initial.byteLength,G.COPY_DST|G.MAP_READ,"joined readback");
    device.queue.writeBuffer(output,0,initial);
    const third=device.createCommandEncoder();
    if(L){
      const p=third.beginComputePass();p.setPipeline(pipelines[5]);
      p.setBindGroup(0,bind(pipelines[5],
        [[0,left],[1,right],[2,offsets],[3,output],[4,bound]]));
      p.dispatchWorkgroups(Math.ceil(L/64));p.end();
    }
    third.copyBufferToBuffer(output,0,outputRead,0,initial.byteLength);
    device.queue.submit([third.finish()]);
    const returned=await read(outputRead,2*total+2);
    if(lost||returned.at(-2)!==0xc0decafe||returned.at(-1)!==0xd00dcafe)
      throw new Error("Compacted GPU BGP output canary/device failure.");
    const leftRows=Array.from({length:L},(_,i)=>[Lraw[2*i],Lraw[2*i+1]]);
    const pairs=Array.from({length:total},(_,i)=>[returned[2*i],returned[2*i+1]]);
    return {triples:n,solutionCount:total,pairs,counts:Craw,offsets:Oraw,
      leftRows,rightRows:Rraw,leftCount:L,rightCount:R,
      projectionOffsets:{knows:Loff,atlas:Roff},
      backend:"actual WebGPU select/scan/scatter x2 → equijoin count/scan/emit",
      algorithm:"compacted",adapter:adapter.info?.device||adapter.info?.description||"not reported",
      isFallbackAdapter:adapter.info?.isFallbackAdapter??null};
  }finally{
    for(const b of owned)b.destroy();
    device.destroy();
  }
}
