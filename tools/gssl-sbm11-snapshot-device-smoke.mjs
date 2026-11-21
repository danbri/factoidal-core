// Live WebGPU validation of the lease gate around BOTH SBM11 GPU layouts.
// Exact-host-code demonstration, not an end-to-end SPARQL/GPU proof.
import {createSnapshotRequest} from "./gssl-sbm11-snapshot.mjs";
import {observeSnapshotBgp} from "./gssl-sbm11-snapshot-gpu.mjs";
import {compareExactRows,compareBags64,referenceBgp64}
  from "./gssl-sbm11-webgpu.mjs";

const SHA=Deno.args[0];
if(!/^[0-9a-f]{40}$/.test(SHA||""))
  throw new Error("Usage: gssl-sbm11-snapshot-device-smoke.mjs SHA");
const IRI=0x2000000000000000n;
const BNODE=0x1000000000000000n;
const TT=0x9000000000000000n;
const P=IRI+0x100n,Q=IRI+0x101n,ATLAS=IRI+0x102n;
const graph=[
  [IRI+1n,P,BNODE+0x55n],
  [IRI+2n,P,TT+0x55n],
  [BNODE+0x55n,Q,ATLAS],
  [TT+0x55n,Q,IRI+0x103n],
  [IRI+3n,P,BNODE+0x55n],
];
const query={knows:P,works:Q,atlas:ATLAS};
const queryText="SELECT ?person ?colleague WHERE { ?person <p> ?colleague . ?colleague <q> <atlas> . }";
const codebookDigest="e1".repeat(32); // test-only synthetic digest, not a verified SBM11 manifest
const refs=referenceBgp64(graph,query);
if(refs.length!==2)throw Error("Expected two independent CPU oracle bindings.");
const request=layout=>createSnapshotRequest({
  sourceId:"test-only-sbm11-source",generation:"test-only-generation",
  graphId:0n,codebookDigest,requestNumber:5,
  layout,triples:graph,queryConstants:query,queryText,
});
const report={
  schema:"gssl-sbm11-snapshot-device-v1",
  sourceCommit:SHA,status:"fail",
  backend:"Deno WebGPU Mesa Vulkan",
  realGpuRequested:true,
  codebookIsAuthenticated:false,
  trustBoundary:"Host-side lease and actual GPU output, NOT an authenticated SBM11 snapshot or Lean GPU certificate.",
  cases:[],
};
try{
  for(const layout of ["direct64Lanes","dense32Snapshot"]){
    const snapshot=await request(layout);
    const result=await observeSnapshotBgp(snapshot,{current:()=>snapshot.lease});
    if(result.status!=="observed-not-certified")
      throw Error(layout+": no completed GPU result: "+result.reason);
    const got=result.result;
    if(!compareExactRows(refs,got.pairs)||!compareBags64(refs,got.pairs))
      throw Error(layout+": device bindings mismatch independently computed UInt64 BGP.");
    report.cases.push({
      layout,status:result.status,expectedBindings:refs.length,
      observedBindings:got.pairs.length,orderedMatch:true,bagMatch:true,
      adapter:got.adapter,isFallbackAdapter:got.isFallbackAdapter,
      dictionarySize:got.dictionarySize??null,
    });
  }
  // This test deliberately revokes the lease AFTER real device execution.
  const stale=await request("direct64Lanes");
  let checks=0;
  const bad=await observeSnapshotBgp(stale,{
    current:()=>{
      checks++;
      return checks===1?stale.lease:
        {...stale.lease,generation:"test-only-generation-updated"};
    },
  });
  if(bad.status!=="fallback"||bad.reason!=="stale-after-readback"||checks!==2)
    throw Error("Completed real GPU result was not refused after generation invalidation.");
  report.staleAfterDeviceReadbackRefused=true;

  const cancel=await request("dense32Snapshot");
  const signal=new AbortController();signal.abort();
  const aborted=await observeSnapshotBgp(cancel,{
    signal:signal.signal,current:()=>cancel.lease,
  });
  if(aborted.reason!=="cancelled")
    throw Error("Cancelled request was not rejected before GPU dispatch.");
  report.cancelBeforeDeviceDispatchRefused=true;

  const absent=await request("direct64Lanes");
  const failed=await observeSnapshotBgp(absent,{
    current:()=>absent.lease,maxSolutions:0,
  });
  if(failed.status!=="fallback"||!failed.reason.includes("capacity"))
    throw Error("Capacity refusal did not trigger fallback.");
  report.capacityRefusal=true;
  report.status="pass";
}catch(e){
  report.error=e?.stack||String(e);
  Deno.exitCode=1;
}
console.log(JSON.stringify(report,null,2));
