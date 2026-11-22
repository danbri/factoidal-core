import test from "node:test";
import assert from "node:assert/strict";
import {runPVGraph} from "../npm/factoidal/gdsl.mjs";

const pvgraph={version:"gdsl/0.2",nodes:[
  {id:"words",op:"core.input",params:{name:"words",type:"buffer<u32>"}},
  {id:"map",op:"u32.map.mul",params:{value:7}},
  {id:"result",op:"core.output",params:{name:"out",type:"buffer<u32>"}}
],links:[
  {from:{node:"words",port:"out"},to:{node:"map",port:"x"},kind:"buffer",type:"u32"},
  {from:{node:"map",port:"out"},to:{node:"result",port:"in"},kind:"buffer",type:"u32"}
]};

test("unsupported GPU fragment goes through actual Lean/Wasm CPU evaluator",async()=>{
  const ops=[];
  const engine={call(op,args){
    ops.push({op,args});
    if(op==="ops")return {ok:true,ops:["pvgraphEvaluate","pvgraphGpuPlan"]};
    if(op==="pvgraphGpuPlan")return {ok:false,error:"operator requires Lean CPU fallback"};
    if(op==="pvgraphEvaluate")return {ok:true,outputs:{out:[7,14,21]}};
    throw Error("unexpected operation "+op);
  }};
  const r=await runPVGraph({pvgraph,bindings:{words:new Uint32Array([1,2,3])},
    loadEngine:async()=>engine,minWords:0});
  assert.equal(r.status,"lean-reference");
  assert.deepEqual(r.outputs,{out:[7,14,21]});
  assert.deepEqual(ops.map(x=>x.op),["ops","pvgraphGpuPlan","pvgraphEvaluate"]);
  assert.deepEqual(JSON.parse(ops[1].args[1]),{words:3});
  assert.deepEqual(JSON.parse(ops[2].args[1]),{words:[1,2,3]});
});

test("GPU failure does not forge success or change semantic authority",async()=>{
  let cpu=0;
  const engine={call(op){
    if(op==="ops")return {ok:true,ops:["pvgraphEvaluate","pvgraphGpuPlan"]};
    if(op==="pvgraphGpuPlan")return {ok:true,plan:{
      version:"pvgraph-gpu/0.1",shader:"not a valid shader",
      steps:[{kind:"input",node:"words",name:"words",words:3},
        {kind:"kernel",node:"map",code:2,a:"words",b:"words",
          constant:7,words:3,workgroups:1}],
      outputs:[{name:"out",source:"map",kind:"buffer",words:3}]
    }};
    if(op==="pvgraphEvaluate"){cpu++;return {ok:true,outputs:{out:[7,14,21]}};}
  }};
  // No WebGPU adapter on a plain Node runner; the only fallback is Lean.
  const oldNavigator=globalThis.navigator;
  try{
    Object.defineProperty(globalThis,"navigator",{value:{},configurable:true});
    const r=await runPVGraph({pvgraph,bindings:{words:[1,2,3]},
      loadEngine:async()=>engine,minWords:0});
    assert.equal(r.status,"lean-reference");
    assert.equal(cpu,1);
    assert.match(r.reason,/GPU unavailable/);
    await assert.rejects(runPVGraph({pvgraph,bindings:{words:[1,2,3]},
      loadEngine:async()=>engine,requireGPU:true}),/No WebGPU adapter/);
    assert.equal(cpu,1);
  }finally{
    Object.defineProperty(globalThis,"navigator",
      {value:oldNavigator,configurable:true});
  }
});

test("GPU call refuses missing Lean op instead of using JS semantics",async()=>{
  await assert.rejects(runPVGraph({pvgraph,bindings:{words:[1]},
    loadEngine:async()=>({call:()=>({ok:true,ops:["pvgraphEvaluate"]})})}),
    /needs Lean\/Wasm/);
});
