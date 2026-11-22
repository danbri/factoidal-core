// Exact-source execution against real Deno WebGPU / Mesa Vulkan adapter.
// GPU computes the joins; a separate BigInt CPU reference is test-only.
import {
  runSbm11BgpGpu,referenceBgp64,compareExactRows,compareBags64,
  COUNT,SCAN,EMIT,
} from "./gssl-sbm11-webgpu.mjs";
import {denseRemap64,decodeDensePairs} from "./gssl-sbm11-dense-u32.mjs";
import {runIntegerBgpGpu} from "../docs/web/hub/paralliverse/integer-bgp-gpu.mjs";
const SHA=Deno.args[0];
if(!/^[a-f0-9]{40}$/.test(SHA??""))
  throw new Error("Usage: gssl-sbm11-webgpu-smoke.mjs EXACT_HEAD_SHA");
const IRI=0x2000000000000000n;
const B=0x1000000000000000n;
const T=0x9000000000000000n;
const L=0x3000000000000000n;
const kp=IRI+0x1000n,wp=IRI+0x1001n,atlas=IRI+0x1002n;
const orion=IRI+0x1003n,label=IRI+0x1004n;
const query={knows:kp,works:wp,atlas};
const make = n=>{
  const g=[];
  for(let i=0;i<n;i++){
    const person=IRI+BigInt(i+1);
    const colleague=IRI+BigInt((i+1)%n+1);
    g.push([person,kp,colleague]);
    g.push([person,kp,IRI+BigInt((i+7)%n+1)]);
    g.push([person,wp,i%4===0?atlas:orion]);
    g.push([person,label,L+BigInt(i+1)]);
  }
  return g;
};
const tests=[
  ["empty",[]],
  ["64 people / 256 triples",make(64)],
  ["256 people / 1024 triples",make(256)],
  ["same-low-different-high",[
    [IRI+10n,kp,B+42n],
    [IRI+11n,kp,T+42n],
    [B+42n,wp,atlas],
    [T+42n,wp,orion],
  ]],
  ["no joins",[[IRI+1n,kp,T+1n],[IRI+2n,wp,atlas]]],
];
const shaders=[COUNT,SCAN,EMIT];
const digests=[];
for(const shader of shaders){
  const d=await crypto.subtle.digest("SHA-256",new TextEncoder().encode(shader));
  digests.push(Array.from(new Uint8Array(d),x=>x.toString(16).padStart(2,"0")).join(""));
}
const report={schema:"gssl-sbm11-u64-gpu-v1",status:"fail",
  sourceCommit:SHA,backend:"Deno WebGPU",denoVersion:Deno.version.deno,
  hashOfCountScanEmitWGSL:digests,cases:[],trustBoundary:
  "Host reads actual device buffers; no proof of shader compiler, driver or GPU execution semantics."};
try{
  for(const [name,graph] of tests){
    const cpu=referenceBgp64(graph,query);
    const got=await runSbm11BgpGpu(graph,query);
    if(!compareExactRows(cpu,got.pairs)||!compareBags64(cpu,got.pairs))
      throw new Error(name+": GPU readback does not match independent UInt64 oracle.");
    if(got.solutionCount!==cpu.length)
      throw new Error(name+": output count mismatch.");
    const denseStart=performance.now();
    const dense=denseRemap64(graph,query);
    const denseResult=await runIntegerBgpGpu(dense.triples,dense.queryConstants);
    const decodedDense=decodeDensePairs(denseResult.pairs,dense);
    if(!compareExactRows(cpu,decodedDense)||!compareBags64(cpu,decodedDense))
      throw new Error(name+": dense-u32 WebGPU result disagrees with the full-width CPU oracle.");
    const denseEndToEndMs=performance.now()-denseStart;
    report.cases.push({name,triples:graph.length,pairs:cpu.length,adapter:got.adapter,
      isFallbackAdapter:got.isFallbackAdapter,
      elapsedMs:Math.round(got.elapsedMs*100)/100,
      exactOrdered:true,exactBag:true,
      returnedCounts:got.counts.length,returnedOffsets:got.offsets.length,
      denseU32:{dictionarySize:dense.dictionarySize,
        actualWebGPU:true,orderedEqual:true,
        elapsedMs:Math.round(denseEndToEndMs*100)/100}});
  }
  let refused=false;
  try{await runSbm11BgpGpu(tests[1][1],query,{maxSolutions:0});}
  catch(e){if(String(e).includes("capacity"))refused=true; else throw e;}
  if(!refused)throw new Error("Result-capacity admission unexpectedly accepted.");
  report.capacityRefusalTest=true;
  report.status="pass";
}catch(e){
  report.error=e?.stack||String(e);
  Deno.exitCode=1;
}
console.log(JSON.stringify(report,null,2));
