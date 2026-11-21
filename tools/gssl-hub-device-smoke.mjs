// The exact GSSL Hub WGSL kernel, executed with the same generic runtime.
// This is a real device differential test against the independent JS CPU
// arithmetic reference; it does NOT prove arbitrary GSSL→WGSL lowering.
import {WGSL,runReference,equalWords}
  from "../docs/web/hub/gssl/lab-core.mjs";
import {createGsslResidentSession}
  from "../npm/factoidal/lib/gpu-resident.mjs";

const sourceCommit=Deno.args[0];
if(!/^[a-f0-9]{40}$/.test(sourceCommit??""))
  throw Error("Usage: gssl-hub-device-smoke.mjs COMMIT_SHA");

const inputs=[
  [2,3,5,7,11,13,17,19],
  [0,1,0xffffffff,0x80000000,0x7fffffff,0xaaaa5555,0x12345678,42],
];
const paramsA=[3,1],paramsB=[5,7];
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter)throw Error("No WebGPU adapter (test must not report a fake GPU pass).");
const session=await createGsslResidentSession({
  adapter,byteBudget:1024*1024,inspectMaxWords:64,
});
const report={
  format:"gssl-hub-device-v1",sourceCommit,status:"fail",
  adapter:adapter.info?.device||adapter.info?.description||"not reported",
  isFallbackAdapter:adapter.info?.isFallbackAdapter??null,
  deno:Deno.version.deno,
  trust:"observed device execution, not WGSL compiler/driver correctness proof",
  cases:[],
};
try{
  await session.compile("affine-u32",WGSL);
  session.allocate("middle",32);
  session.allocate("result",32);
  const execute=async(source)=>{
    const expected=runReference(source,paramsA,paramsB);
    await session.upload("source",new Uint32Array(source));
    await session.upload("paramsA",new Uint32Array(paramsA));
    await session.upload("paramsB",new Uint32Array(paramsB));
    await session.dispatch({
      kernel:"affine-u32",
      bindings:[{binding:0,id:"source"},{binding:1,id:"middle"},
        {binding:2,id:"paramsA"}],
      writes:["middle"],workgroups:[1,1,1],
    });
    await session.dispatch({
      kernel:"affine-u32",
      bindings:[{binding:0,id:"middle"},{binding:1,id:"result"},
        {binding:2,id:"paramsB"}],
      writes:["result"],workgroups:[1,1,1],
    });
    const middle=(await session.inspect("middle",{countWords:source.length})).words;
    const out=(await session.inspect("result",{countWords:source.length})).words;
    if(!equalWords(expected.intermediate,middle)||!equalWords(expected.output,out))
      throw Error("CPU reference disagreed with the actual GPU output.");
    return {length:source.length,expected:expected.output,observed:out,stats:session.status()};
  };
  const first=await execute(inputs[0]);
  if(first.stats.uploads!==3||first.stats.submissions!==2||
    first.stats.readbacks!==2||first.stats.createdPipelines!==1)
    throw Error("Initial GSSL Hub pass didn't retain the documented resources.");
  const same=await execute(inputs[0]);
  if(same.stats.uploads!==3||same.stats.reuses!==3||
    same.stats.submissions!==4||same.stats.readbacks!==4||
    same.stats.createdPipelines!==1)
    throw Error("Repeated run did not reuse identical host uploads and pipeline.");
  const wrap=await execute(inputs[1]);
  if(wrap.stats.uploads!==4||wrap.stats.submissions!==6)
    throw Error("Changed input wasn't uploaded exactly once.");
  report.cases=[
    {name:"first",matches:true,stats:first.stats},
    {name:"unchanged second",matches:true,stats:same.stats},
    {name:"wrap and high bit",matches:true,stats:wrap.stats},
  ];
  report.status="pass";
}catch(error){
  report.error=error?.stack||String(error);
  Deno.exitCode=1;
}finally{
  try{session.close();}catch(e){
    report.status="fail";report.cleanupError=String(e);Deno.exitCode=1;
  }
}
console.log(JSON.stringify(report,null,2));
