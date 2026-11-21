// Real Mesa/Deno WebGPU smoke for a generic resident compute session.
// This uses no RDF/SPARQL objects; the same buffers are fed directly to two
// successive compute dispatches without host staging between them.
import {createGsslResidentSession} from "./gssl-gpu-resident.mjs";

const sourceCommit=Deno.args[0]??"";
if(!/^[0-9a-f]{40}$/.test(sourceCommit))
  throw new Error("Usage: gssl-gpu-resident-device-smoke.mjs HEAD_SHA");
const WGSL = `
@group(0) @binding(0) var<storage, read> source: array<u32>;
@group(0) @binding(1) var<storage, read_write> destination: array<u32>;
@compute @workgroup_size(4)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
  if(gid.x >= 4u) { return; }
  destination[gid.x] = source[gid.x] * 3u + 1u;
}
`;
const report={
  schema:"gssl-generic-resident-v1",sourceCommit,status:"fail",
  deviceKind:"actual Deno WebGPU command submissions; Mesa Vulkan software adapter",
  note:"This proves no shader/compiler correctness beyond observed cases.",
};
let session;
try{
  session=await createGsslResidentSession({byteBudget:64*1024,inspectMaxWords:16});
  await session.upload("input",new Uint32Array([2,3,5,7]));
  session.allocate("intermediate",16);
  session.allocate("output",16);
  await session.compile("affine",WGSL);
  // The second compile is an exact-content cache hit.
  const already=await session.compile("affine",WGSL);
  if(already.compiled)throw Error("Identical WGSL compiled twice.");
  await session.dispatch({kernel:"affine",bindings:[
    {binding:0,id:"input"},{binding:1,id:"intermediate"},
  ],writes:["intermediate"],workgroups:[1,1,1]});
  await session.dispatch({kernel:"affine",bindings:[
    {binding:0,id:"intermediate"},{binding:1,id:"output"},
  ],writes:["output"],workgroups:[1,1,1]});
  const before=session.status();
  if(before.readbacks!==0||before.uploads!==1||
    before.submissions!==2||before.createdPipelines!==1)
    throw Error("Two compute passes did not retain GPU buffers/pipeline.");
  const observed=await session.inspect("output",{countWords:4});
  const expected=[22,31,49,67]; // ((x*3+1)*3+1)
  if(JSON.stringify(observed.words)!==JSON.stringify(expected))
    throw Error("Actual GPU result is not the two-pass affine computation.");
  // Small partial debug sample, not a full 64 KiB dump.
  const partial=await session.inspect("intermediate",{offsetWords:1,countWords:2});
  if(JSON.stringify(partial.words)!==JSON.stringify([10,16]))
    throw Error("Intermediate GPU buffer did not survive between dispatches.");
  const reused=await session.upload("input",new Uint32Array([2,3,5,7]));
  if(reused.uploaded||session.status().uploads!==1)
    throw Error("Unchanged inputs were redundantly uploaded.");
  const stats=session.status();
  report.status="pass";
  report.expected=expected;
  report.observed=observed.words;
  report.intermediateSample=partial.words;
  report.graphUploads=null; // no graph or RDF model exists in this API
  report.stats=stats;
}catch(error){
  report.error=error?.stack??String(error);
  Deno.exitCode=1;
}finally{
  try{session?.close();}catch(error){
    report.closeError=String(error);report.status="fail";Deno.exitCode=1;
  }
}
console.log(JSON.stringify(report,null,2));
