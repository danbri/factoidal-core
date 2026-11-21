import test from "node:test";
import assert from "node:assert/strict";
import {createPVGraphWasm} from "../npm/factoidal/gdsl.mjs";

function stub(){
  const calls=[];
  const graph={version:"gdsl/0.2",nodes:[],links:[]};
  const engine={call(op,args){
    calls.push({op,args});
    if(op==="ops")return {ok:true,ops:["pvgraphBuild","pvgraphAdmit","pvgraphEvaluate"]};
    if(op==="pvgraphBuild")return {ok:true,pvgraph:graph};
    if(op==="pvgraphAdmit")return {ok:true,pvgraph:graph};
    if(op==="pvgraphEvaluate")return {ok:true,outputs:{answer:[6,9]}};
    throw Error("host MUST NOT implement op "+op);
  }};
  return {engine,calls,graph};
}

test("JS is only a command marshaler; Lean/Wasm owns PVGraph build and evaluation",async()=>{
  const {engine,calls,graph}=stub();
  const g=await createPVGraphWasm(async()=>engine);
  const xs=g.input("samples");
  const ys=g.op("u32.map.mul",{x:xs},{value:3},{resultType:"buffer<u32>"});
  g.output("answer",ys);
  assert.strictEqual(await g.build(),graph);
  assert.strictEqual(await g.admit(graph),graph);
  assert.deepEqual(await g.evaluate(graph,{samples:[2,3]}),{answer:[6,9]});
  const build=calls.find(x=>x.op==="pvgraphBuild");
  const commands=JSON.parse(build.args[0]).steps;
  assert.deepEqual(commands,[
    {cmd:"input",name:"samples",type:"buffer<u32>",id:null,ref:"r1"},
    {cmd:"op",op:"u32.map.mul",resultType:"buffer<u32>",
      args:[{port:"x",source:"r1"}],params:{value:3},id:null,ref:"r2"},
    {cmd:"output",name:"answer",source:"r2",id:null}
  ]);
  assert.deepEqual(calls.map(x=>x.op),
    ["ops","pvgraphBuild","pvgraphAdmit","pvgraphEvaluate"]);
  await assert.rejects(g.build(),/already finalized/);
});

test("No alternate local semantic evaluator or cross-builder references",async()=>{
  const {engine}=stub();
  const a=await createPVGraphWasm(async()=>engine);
  const b=await createPVGraphWasm(async()=>engine);
  const ref=a.input("x");
  assert.throws(()=>b.output("answer",ref),/this builder/);
  assert.throws(()=>a.op("u32.reduce.sum",{x:ref}),/resultType/);
});

test("Requires the actual exported Lean/Wasm operations, with no JS fallback",async()=>{
  await assert.rejects(createPVGraphWasm(async()=>({call(op){
    if(op==="ops")return {ok:true,ops:[]};
    throw Error("unexpected");
  }})),/requires a rebuilt Lean engine/);
});

test("Wasm rejection surfaces as failure and never yields an admitted graph",async()=>{
  const {engine}=stub();
  const oldCall=engine.call;
  engine.call=(op,args)=>op==="pvgraphBuild"
    ? {ok:false,error:"Lean admission refused"}
    : oldCall(op,args);
  const g=await createPVGraphWasm(async()=>engine);
  const xs=g.input("x");
  g.output("answer",xs);
  await assert.rejects(g.build(),/Lean admission refused/);
});
