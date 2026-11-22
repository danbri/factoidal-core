// Actual WebGPU execution of *Lean-emitted* PVGraph plans.
// Read source-authoritative JSONL fixtures from a native Lean executable.
// No JavaScript PVGraph model, parser, operator registry or CPU evaluator.
import {readFileSync} from "node:fs";
import {executePVGraphGpuPlan} from "../npm/factoidal/lib/gdsl-gpu.mjs";
import {createGsslResidentSession}
  from "../npm/factoidal/lib/gpu-resident.mjs";
import {sourceProvenance} from "./pvgraph-evidence-provenance.mjs";

const args=typeof Deno!=="undefined"?Deno.args:process.argv.slice(2);
const inputPath=args[0],sha=args[1];
if(!inputPath||!/^[a-f0-9]{40}$/.test(sha??""))
  throw Error("Usage: pvgraph-gpu-device-smoke.mjs LEAN_FIXTURES HEAD_SHA");
const fixtures=readFileSync(inputPath,"utf8").trim().split(/\r?\n/)
  .filter(Boolean).map(JSON.parse);
const required=["map-highbits","fanout-zip","broadcast","scalar","empty",
  "large-8192","u64-two-lane-equality","u64-two-column-bounds","scan-parallel",
  ...[0,63,64,65,4095,4096,4097,16385,262145].map(n=>"scan-boundary-"+n),
  ...["duplicates","high-half","empty-left","empty-right","empty-both",
    "no-match","skew","large-16385"].flatMap(name=>
      ["join-"+name+"-probe","join-"+name+"-expand"])];
if(new Set(fixtures.map(r=>r.case)).size!==fixtures.length||
   required.some(name=>!fixtures.some(r=>r.case===name)))
  throw Error("missing or duplicate Lean-authored device case");
const u64=fixtures.find(r=>r.case==="u64-two-lane-equality");
if(!u64||u64.expected.differenceLow[0]!==0||
   u64.expected.differenceHigh[0]===0||
   u64.expected.differenceLow[1]!==0||
   u64.expected.differenceHigh[1]!==0)
  throw Error("UInt64 fixture must distinguish high-bit collisions while preserving equal IDs");
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter)throw Error("PVGraph GPU gate requires an actual WebGPU adapter.");
const session=await createGsslResidentSession({
  adapter,byteBudget:256*1024*1024,inspectMaxWords:16384
});
const data={commit:sha,provenance:sourceProvenance(sha),status:"fail",backend:"Deno WebGPU",
  adapter:adapter.info?.description||adapter.info?.device||"not reported",
  isSoftwareAdapter:adapter.info?.isFallbackAdapter===true||
    /swiftshader|llvmpipe|lavapipe|software/i.test([
      adapter.info?.vendor,adapter.info?.device,adapter.info?.description].join(" ")),
  trust:"observed GPU results, not a proof about the shader compiler or device",
  cases:[],benchmarks:[]};
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
    const bindings=Object.fromEntries(Object.entries(record.input).map(([name,value])=>
      [name,Array.isArray(value)?value:[value]]));
    const started=now();
    const result=await executePVGraphGpuPlan({plan,bindings,session});
    const observed=result.outputs;
    if(!same(observed,record.expected))
      throw Error(record.case+": actual GPU output differs from Lean: "+
        JSON.stringify({observed,expected:record.expected}).slice(0,1000));
    const elapsed=now()-started;
    data.cases.push({name:record.case,correct:true,
      inputWords:plan.steps.filter(s=>s.kind==="input").reduce((n,s)=>n+s.words,0),
      residentBytes:result.residentBytes,
      dispatches:result.dispatches,timing:result.timing,
      ms:elapsed,readbacks:plan.outputs.length});
    if(record.case.includes("large-"))
      data.benchmarks.push({name:record.case,observedGpuWallMs:elapsed,
        residentBytes:result.residentBytes,
        excludes:"Lean CPU execution and Wasm artifact generation",
        includes:"Shader compilation, GPU buffer uploads, dispatch and full output readback"});
  }
  if(data.cases.length!==fixtures.length||data.cases.some(c=>!c.correct&&!c.correctlyRefused))
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
