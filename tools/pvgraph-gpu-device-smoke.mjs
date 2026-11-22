// Actual WebGPU execution of *Lean-emitted* PVGraph plans.
// Read source-authoritative JSONL fixtures from a native Lean executable.
// No JavaScript PVGraph model, parser, operator registry or CPU evaluator.
import {readFileSync} from "node:fs";
import {createGsslResidentSession}
  from "../npm/factoidal/lib/gpu-resident.mjs";

const args=typeof Deno!=="undefined"?Deno.args:process.argv.slice(2);
const inputPath=args[0],sha=args[1];
if(!inputPath||!/^[a-f0-9]{40}$/.test(sha??""))
  throw Error("Usage: pvgraph-gpu-device-smoke.mjs LEAN_FIXTURES HEAD_SHA");
const fixtures=readFileSync(inputPath,"utf8").trim().split(/\r?\n/)
  .filter(Boolean).map(JSON.parse);
if(fixtures.length!==8)throw Error("expected eight Lean-authored cases");
const u64=fixtures.find(r=>r.case==="u64-two-lane-equality");
if(!u64||u64.expected.differenceLow[0]!==0||
   u64.expected.differenceHigh[0]===0||
   u64.expected.differenceLow[1]!==0||
   u64.expected.differenceHigh[1]!==0)
  throw Error("UInt64 fixture must distinguish high-bit collisions while preserving equal IDs");
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter)throw Error("PVGraph GPU gate requires an actual WebGPU adapter.");
const session=await createGsslResidentSession({
  adapter,byteBudget:64*1024*1024,inspectMaxWords:16384
});
const data={commit:sha,status:"fail",backend:"Deno WebGPU",
  adapter:adapter.info?.device||adapter.info?.description||"not reported",
  trust:"observed GPU results, not a proof about the shader compiler or device",
  cases:[],benchmarks:[]};
let seq=0;
const same=(a,b)=>{
  // JSON object members are unordered, including those produced by Lean.
  // Array order is significant: it encodes SPARQL solution occurrences.
  const ka=Object.keys(a).sort(),kb=Object.keys(b).sort();
  return JSON.stringify(ka)===JSON.stringify(kb) &&
    ka.every(k=>JSON.stringify(a[k])===JSON.stringify(b[k]));
};
const now=()=>performance.now();
try{
  for(const record of fixtures){
    if(!record.eligible){
      if(record.plan!==null)throw Error("unsupported case returned a plan");
      data.cases.push({name:record.case,correctlyRefused:true});
      continue;
    }
    const plan=record.plan;
    if(plan.version!=="pvgraph-gpu/0.1"||typeof plan.shader!=="string")
      throw Error("invalid Lean GPU fixture plan");
    await session.compile("pvgraph_u32",plan.shader);
    const key="pv"+(++seq)+"_";
    const refs=new Map(),allocated=[];
    const buf=id=>key+id;
    const upload=async(id,words)=>{
      const target=buf(id);
      await session.upload(target,new Uint32Array(words.length?words:[0]));
      refs.set(id,target);allocated.push(target);
    };
    const started=now();
    try{
      for(const step of plan.steps){
        if(step.kind==="input"){
          const source=record.input[step.name];
          if(step.words!== (Array.isArray(source)?source.length:1))
            throw Error(record.case+": incorrect input length from Lean plan");
          await upload(step.node,Array.isArray(source)?source:[source]);
        }else if(step.kind==="const"){
          await upload(step.node,[step.value]);
        }else if(step.kind==="kernel"){
          const dest=buf(step.node);
          session.allocate(dest,Math.max(1,step.words)*4);
          allocated.push(dest);
          const config=buf(step.node+"_config");
          await upload(step.node+"_config",[step.code,step.words,step.constant,0]);
          await session.dispatch({kernel:"pvgraph_u32",bindings:[
            {binding:0,id:refs.get(step.a)},
            {binding:1,id:refs.get(step.b)},
            {binding:2,id:dest},
            {binding:3,id:config}
          ],writes:[dest],workgroups:[step.workgroups,1,1]});
          refs.set(step.node,dest);
        }else throw Error("unknown Lean plan step "+step.kind);
      }
      const observed={};
      for(const output of plan.outputs){
        const words=await session.readWords(refs.get(output.source),
          {countWords:output.words});
        observed[output.name]=output.kind==="scalar"?words[0]:words;
      }
      if(!same(observed,record.expected))
        throw Error(record.case+": actual GPU output differs from Lean: "+
          JSON.stringify({observed,expected:record.expected}).slice(0,1000));
      const elapsed=now()-started;
      data.cases.push({name:record.case,correct:true,
        inputWords:plan.steps.filter(s=>s.kind==="input").reduce((n,s)=>n+s.words,0),
        dispatches:plan.steps.filter(s=>s.kind==="kernel").length,
        ms:elapsed,readbacks:plan.outputs.length});
      if(record.case.startsWith("large-"))
        data.benchmarks.push({name:record.case,observedGpuWallMs:elapsed,
          excludes:"Lean CPU execution and Wasm artifact generation",
          includes:"GPU buffer uploads, dispatch and full output readback"});
    }finally{
      for(const id of allocated.reverse())session.release(id);
    }
  }
  if(data.cases.length!==8||data.cases.some(c=>!c.correct&&!c.correctlyRefused))
    throw Error("missing PVGraph GPU evidence");
  data.status="pass";
}catch(error){
  data.error=error?.stack||String(error);
  if(typeof Deno!=="undefined")Deno.exitCode=1;
  else process.exitCode=1;
}finally{
  data.resources=session.status();
  try{session.close();}catch(e){
    data.cleanupError=String(e);
    if(typeof Deno!=="undefined")Deno.exitCode=1;
    else process.exitCode=1;
  }
  console.log(JSON.stringify(data,null,2));
}
