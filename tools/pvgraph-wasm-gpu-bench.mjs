// End-to-end benchmark of the *same current Lean/Wasm* reference evaluator
// and its Lean-planned WebGPU path. No JS PVGraph interpreter.
import {createPVGraphWasm,runPVGraph} from "../npm/factoidal/gdsl.mjs";
import {loadEngine} from "../npm/factoidal/index.mjs";
import {createGsslResidentSession} from "../npm/factoidal/lib/gpu-resident.mjs";

const sizes=[16,1024,8192,65536,262144];
const samples=5;
const now=()=>performance.now();
const median=x=>x.slice().sort((a,b)=>a-b)[Math.floor(x.length/2)];
const same=(a,b)=>JSON.stringify(a)===JSON.stringify(b);
const engine=await loadEngine();
const supported=new Set(engine.call("ops",[])?.ops||[]);
for(const name of ["pvgraphBuild","pvgraphEvaluate","pvgraphGpuPlan"])
  if(!supported.has(name))throw Error("Rebuild Lean/Wasm before benchmarking: "+name);
if(!navigator.gpu)throw Error("GPU benchmark requires real WebGPU");
const adapter=await navigator.gpu.requestAdapter();
if(!adapter)throw Error("No real WebGPU adapter");
const session=await createGsslResidentSession({adapter,
  byteBudget:128*1024*1024,inspectMaxWords:16384});
const g=await createPVGraphWasm(loadEngine);
const x=g.input("words");
const scaled=g.op("u32.map.mul",{x},{value:257},
  {id:"scaled",resultType:"buffer<u32>"});
const mixed=g.op("u32.map.xor",{x:scaled},{value:2147483648},
  {id:"mixed",resultType:"buffer<u32>"});
g.output("answer",mixed);
const pvgraph=await g.build();
const report={schema:"pvgraph-end-to-end-benchmark-v1",status:"fail",
  adapter:adapter.info?.device||adapter.info?.description||"not reported",
  engine:"current Lean/Wasm",sizes,measurements:[],
  interpretation:"Warm end-to-end wall time including host marshalling, GPU plan, uploads, dispatch and full readback. No universal speedup claim."};
try{
  for(const n of sizes){
    const words=Uint32Array.from({length:n},(_,i)=>Math.imul(i,11939)>>>0);
    const runReference=()=>{
      const result=engine.call("pvgraphEvaluate",[
        JSON.stringify(pvgraph),JSON.stringify({words:Array.from(words)})]);
      if(!result?.ok)throw Error("Lean evaluator refused: "+String(result?.error));
      return result.outputs;
    };
    // Warm both routes. The GPU path must run and return full words.
    const base=runReference();
    const warm=await runPVGraph({pvgraph,bindings:{words},loadEngine,
      session,requireGPU:true,minWords:0,verifyWithLean:false});
    if(warm.status!=="gpu-observed"||!same(warm.outputs,base))
      throw Error("GPU disagrees with Lean at n="+n);
    const cpuMs=[],gpuMs=[];
    for(let k=0;k<samples;k++){
      let t=now();
      const expected=runReference();
      cpuMs.push(now()-t);
      t=now();
      const observed=await runPVGraph({pvgraph,bindings:{words},
        loadEngine,session,requireGPU:true,minWords:0,verifyWithLean:false});
      gpuMs.push(now()-t);
      if(observed.status!=="gpu-observed"||!same(observed.outputs,expected))
        throw Error("GPU/Lean disagreement at n="+n+" sample "+k);
    }
    const cpu=median(cpuMs),gpu=median(gpuMs);
    report.measurements.push({words:n,medianLeanWasmMs:cpu,
      medianWebGpuMs:gpu,observedSpeedup:cpu/gpu,gpuFaster:gpu<cpu,
      cpuSamples:cpuMs,gpuSamples:gpuMs});
  }
  report.status="pass";
}catch(e){report.error=e?.stack||String(e);
  if(typeof Deno!=="undefined")Deno.exitCode=1;
  else process.exitCode=1;
}
finally{session.close();console.log(JSON.stringify(report,null,2));}
