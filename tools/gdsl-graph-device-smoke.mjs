// Exact common GDSL graph runtime on actual Mesa/Deno WebGPU.
// Same graph is constructed via JS and round-tripped through S-expressions.
// The independent JS reference is checked against the device output, but
// this is NOT an unrestricted WGSL compiler nor a Lean proof of hardware.
import {checkPVGraph,runPVGraphCPU,toPVSexpr,fromPVSexpr}
  from "../npm/factoidal/lib/gdsl-graph.mjs";
import {example,listExamples} from "../npm/factoidal/lib/gdsl-examples.mjs";
import {runPVGraphGPU} from "../npm/factoidal/lib/gdsl-webgpu.mjs";
import {createGsslResidentSession}
  from "../npm/factoidal/lib/gpu-resident.mjs";

const commit=Deno.args[0]??"";
if(!/^[0-9a-f]{40}$/.test(commit))
  throw Error("Usage: gdsl-graph-device-smoke.mjs HEAD_SHA");
const s=await createGsslResidentSession({
  byteBudget:8*1024*1024,inspectMaxWords:256});
const report={schema:"gdsl-pvgraph-device-v0.2",commit,
  status:"fail",backend:"actual Deno WebGPU Mesa Vulkan software adapter",
  cases:[],trust:"device observation, not verified shader compiler/refinement"};
const same=(a,b)=>JSON.stringify(Object.entries(a).sort())===
  JSON.stringify(Object.entries(b).sort());
try{
  for(const meta of listExamples()){
    const e=example(meta.id);
    const sexpr=toPVSexpr(e.pvgraph);
    const reparsed=fromPVSexpr(sexpr);
    if(JSON.stringify(checkPVGraph(reparsed))!==JSON.stringify(e.pvgraph))
      throw Error(meta.id+": canonical S-expression round-trip mismatch.");
    const expected=runPVGraphCPU(reparsed,e.input).outputs;
    const gpu=await runPVGraphGPU(reparsed,e.input,{session:s});
    if(!same(expected,gpu.outputs))
      throw Error(meta.id+": actual GPU readback differs from CPU dataflow result.");
    report.cases.push({
      name:meta.id,nodes:reparsed.nodes.length,links:reparsed.links.length,
      gpuDispatches:gpu.gpuDispatches,allOutputsEqual:true,
      residentUploads:gpu.resident.uploads,
      pipelineCompilations:gpu.resident.createdPipelines,
      readbacks:gpu.resident.readbacks,
      submissionCount:gpu.resident.submissions,
    });
  }
  // Running the identical graph with unchanged inputs should reuse all
  // content versions and the exact same trusted kernel compilation.
  const e=example("signal");
  const uploadsBefore=s.status().uploads;
  const pipelinesBefore=s.status().createdPipelines;
  const again=await runPVGraphGPU(e.pvgraph,e.input,{session:s});
  if(again.resident.uploads!==uploadsBefore ||
     again.resident.createdPipelines!==pipelinesBefore)
    throw Error("Repeated graph reuploaded unchanged source or compiled a new pipeline.");
  report.unmodifiedGraphReuse=true;
  // Exercise zero and high-bit cases on the *same* canonical graph API.
  const before=runPVGraphCPU(example("font").pvgraph,{advances:[]}).outputs;
  const gpuEmpty=await runPVGraphGPU(example("font").pvgraph,{advances:[]},{session:s});
  if(!same(before,gpuEmpty.outputs))throw Error("Empty input differs on GPU.");
  const extreme=[0,1,0x80000000,0xffffffff];
  const high=example("image");
  const expectedHigh=runPVGraphCPU(high.pvgraph,{pixels:extreme}).outputs;
  const observedHigh=await runPVGraphGPU(high.pvgraph,{pixels:extreme},{session:s});
  if(!same(expectedHigh,observedHigh.outputs))throw Error("u32 overflow differs on GPU.");
  report.emptyAndHighBits=true;
  report.status="pass";
}catch(e){
  report.error=e?.stack||String(e);
  Deno.exitCode=1;
}finally{
  try{s.close();}catch(e){
    report.status="fail";report.closeError=String(e);Deno.exitCode=1;
  }
}
console.log(JSON.stringify(report,null,2));
