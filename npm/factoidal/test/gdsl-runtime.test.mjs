import test from "node:test";
import assert from "node:assert/strict";
import {loadEngine} from "@factoidal/core";
import {createPVGraphWasm,runPVGraph} from "@factoidal/core/gdsl";

async function reduction(){
  const g=await createPVGraphWasm(loadEngine);
  const values=g.input("values");
  const total=g.op("u32.reduce.sum",{x:values},{},
    {resultType:"scalar<u32>",id:"sum"});
  g.output("total",total);
  return g.build();
}

function observedEngine(engine,changePlan){
  const calls=[];
  return {
    calls,
    loadEngine:async()=>({call(op,args){
      calls.push(op);
      if(op==="pvgraphGpuPlan"&&changePlan)return changePlan(args);
      return engine.call(op,args);
    }})
  };
}

test("automatic PVGraph reduction uses Lean after the shipping loader throws its refusal",async()=>{
  const pvgraph=await reduction(),engine=await loadEngine();
  const observed=observedEngine(engine);
  const result=await runPVGraph({pvgraph,bindings:{values:[2,3,5]},
    loadEngine:observed.loadEngine,
    session:{status(){assert.fail("CPU fallback must not allocate a GPU session");}}});
  assert.equal(result.status,"lean-reference");
  assert.equal(result.reason,"outside Lean GPU fragment");
  assert.deepEqual(result.outputs,{total:10});
  assert.equal(result.dispatches,0);
  assert.deepEqual(observed.calls,["ops","pvgraphGpuPlan","pvgraphEvaluate"]);
});

test("a host returning the same Lean refusal envelope also selects the reference",async()=>{
  const pvgraph=await reduction(),engine=await loadEngine();
  const observed=observedEngine(engine,args=>{
    try{return engine.call("pvgraphGpuPlan",args);}
    catch(error){assert.equal(error.envelope?.ok,false);return error.envelope;}
  });
  const result=await runPVGraph({pvgraph,bindings:{values:[0xffffffff,2]},
    loadEngine:observed.loadEngine});
  assert.equal(result.status,"lean-reference");
  assert.deepEqual(result.outputs,{total:1});
  assert.deepEqual(observed.calls,["ops","pvgraphGpuPlan","pvgraphEvaluate"]);
});

test("required GPU preserves the shipping loader refusal and never evaluates on CPU",async()=>{
  const pvgraph=await reduction(),observed=observedEngine(await loadEngine());
  await assert.rejects(runPVGraph({pvgraph,bindings:{values:[2,3,5]},
    loadEngine:observed.loadEngine,requireGPU:true}),error=>{
    assert.equal(error.envelope?.ok,false);
    assert.match(error.envelope.error,/operator requires Lean CPU fallback/);
    return true;
  });
  assert.deepEqual(observed.calls,["ops","pvgraphGpuPlan"]);
});

test("malformed PVGraphs and invalid bindings are refused without CPU fallback",async()=>{
  const pvgraph=await reduction(),engine=await loadEngine();
  const badGraph=structuredClone(pvgraph);
  badGraph.nodes.find(n=>n.id==="sum").op="app.unregistered";
  const badLink=structuredClone(pvgraph);
  badLink.links[0].to.port="absent";
  for(const [doc,bindings] of [
    [badGraph,{values:[2,3,5]}],
    [badLink,{values:[2,3,5]}],
    [pvgraph,{values:[-1]}],
    [pvgraph,{values:[1],extra:[2]}],
    [pvgraph,{}]
  ]){
    const observed=observedEngine(engine);
    await assert.rejects(runPVGraph({pvgraph:doc,bindings,loadEngine:observed.loadEngine}));
    assert.equal(observed.calls.includes("pvgraphEvaluate"),false);
  }
});

test("unrelated planning exceptions retain their identity and do not fall back",async()=>{
  const pvgraph=await reduction(),engine=await loadEngine();
  for(const failure of [
    new Error("operator requires Lean CPU fallback without a Lean refusal envelope"),
    new Error("Wasm execution interrupted"),
    Object.assign(new Error("resource bound exceeded"),
      {envelope:{ok:false,error:"PVGraph GPU: input exceeds GPU bound",code:"op.failed"}})
  ]){
    const observed=observedEngine(engine,()=>{throw failure;});
    await assert.rejects(runPVGraph({pvgraph,bindings:{values:[1]},
      loadEngine:observed.loadEngine}),error=>error===failure);
    assert.deepEqual(observed.calls,["ops","pvgraphGpuPlan"]);
  }
});

test("the Lean reference still refuses invalid shapes after an ineligible GPU operator",async()=>{
  const g=await createPVGraphWasm(loadEngine);
  const a=g.input("a"),b=g.input("b");
  const total=g.op("u32.reduce.sum",{x:a},{},{resultType:"scalar<u32>"});
  const zipped=g.op("u32.zip.add",{a,b},{},{resultType:"buffer<u32>"});
  g.output("total",total);
  g.output("zipped",zipped);
  const observed=observedEngine(await loadEngine());
  await assert.rejects(runPVGraph({pvgraph:await g.build(),bindings:{a:[1],b:[2,3]},
    loadEngine:observed.loadEngine}),/zip lengths differ/);
  assert.deepEqual(observed.calls,["ops","pvgraphGpuPlan","pvgraphEvaluate"]);
});
