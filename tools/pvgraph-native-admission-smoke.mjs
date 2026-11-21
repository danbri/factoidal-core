// Native Lean admission smoke for the actual PVGraph public API.
// Works with a Lean 4.33.1 toolchain and the checked-out Lean source;
// no GPU device is needed here. Fails unless the native Lean evaluator
// accepts the same exact serialized PVGraph and input values as JS.
import {strict as assert} from "node:assert";
import {example,listExamples} from "../npm/factoidal/lib/gdsl-examples.mjs";
import {PVGraph,checkPVGraph,runPVGraphCPU}
  from "../npm/factoidal/lib/gdsl-graph.mjs";
import {admitPVGraphWithLean,requirePVGraphLeanAdmission}
  from "../npm/factoidal/lib/pvgraph-lean-admission.mjs";
import {runPVGraphGPU} from "../npm/factoidal/lib/gdsl-webgpu.mjs";

let passed=0,refused=0;
for(const info of listExamples()){
  const e=example(info.id);
  const admitted=await admitPVGraphWithLean(e.pvgraph,e.input);
  assert.equal(Object.isFrozen(admitted),true);
  assert.equal(Reflect.ownKeys(admitted).length,0,
    "Lean capability must not contain caller-editable grants");
  const state=await requirePVGraphLeanAdmission(admitted,e.pvgraph,e.input);
  assert.equal(typeof state.digest,"string");
  assert.equal(state.digest.length,64);
  assert.deepEqual(Object.keys(state.expected).sort(),
    Object.keys(runPVGraphCPU(e.pvgraph,e.input).outputs).sort());
  passed++;
  // The primitive WGSL runner cannot skip a native admission:
  await assert.rejects(
    runPVGraphGPU(e.pvgraph,e.input,{admission:{approved:true}}),
    /missing native Lean admission/
  );
  refused++;
  // Editing even one admitted input after the proof has been issued
  // must invalidate the permit before reaching any GPU entrypoint.
  const different=Object.fromEntries(Object.entries(e.input).map(([k,v])=>
    [k,v.slice()]));
  const name=Object.keys(different)[0];
  different[name]=different[name].concat([7]);
  await assert.rejects(runPVGraphGPU(e.pvgraph,different,{admission:admitted}),
    /does not match current PVGraph/);
  refused++;
  // Likewise an altered operator constant is not the same admitted PVGraph.
  const changed=JSON.parse(JSON.stringify(e.pvgraph));
  const n=changed.nodes.find(x=>x.op==="u32.map.mul"||x.op==="u32.map.add"||
    x.op==="u32.map.xor"||x.op==="u32.scalar.const");
  if(n){
    n.params.value=(n.params.value+1)>>>0;
    await assert.rejects(
      runPVGraphGPU(changed,e.input,{admission:admitted}),
      /does not match current PVGraph/
    );
    refused++;
  }
}
{
  const g=PVGraph();
  const words=g.input("words");
  const mul=g.op("u32.map.mul",{x:words},{value:5});
  g.output("out",mul);
  const pvgraph=g.build();
  assert.deepEqual(checkPVGraph(pvgraph),pvgraph);
  await assert.rejects(
    runPVGraphGPU(pvgraph,{words:[1,2,3]}),/missing native Lean admission/
  );
  refused++;
}
console.log(JSON.stringify({
  schema:"pvgraph-native-lean-gate-v0.2",
  status:"pass",realLeanApprovals:passed,refusedMissingOrStale:refused,
  guarantees:"PVGraph GPU entrypoint requires native Lean admission bound to actual inputs",
  caveat:"WGSL, WebGPU and JavaScript runtime are not formally proved correct"
},null,2));
