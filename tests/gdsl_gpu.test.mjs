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


test("Lean GPU plan instructions wire WebGPU buffers without JS graph interpretation",async()=>{
  const allocations=new Map();
  const released=[];
  const fakeSession={
    async compile(){},
    async upload(id,typed){
      allocations.set(id,Array.from(typed));
    },
    allocate(id,bytes){allocations.set(id,Array(bytes/4).fill(0));},
    async dispatch({bindings}){
      const slots=new Map(bindings.map(e=>[e.binding,e.id]));
      const a=allocations.get(slots.get(0)),config=allocations.get(slots.get(3));
      const out=allocations.get(slots.get(2));
      // Test-only device model: a real device lane separately executes WGSL.
      for(let i=0;i<config[1];i++)out[i]=Math.imul(a[i],config[2])>>>0;
    },
    async readWords(id,{countWords}){return allocations.get(id).slice(0,countWords);},
    status(){return {fakeDevice:true};},
    release(id){released.push(id);allocations.delete(id);}
  };
  const plan={version:"pvgraph-gpu/0.1",shader:"test-only-device-shader",
    steps:[{kind:"input",node:"words",name:"words",words:3},
      {kind:"kernel",node:"map",a:"words",b:"words",
        code:2,constant:7,words:3,workgroups:1}],
    outputs:[{name:"out",source:"map",kind:"buffer",words:3}]};
  const engine={call(op){
    if(op==="ops")return {ops:["pvgraphGpuPlan","pvgraphEvaluate"]};
    if(op==="pvgraphGpuPlan")return {ok:true,plan};
    throw Error("GPU execution must not compute a JS reference");
  }};
  const result=await runPVGraph({pvgraph,bindings:{words:[1,2,3]},
    loadEngine:async()=>engine,session:fakeSession,requireGPU:true,minWords:0,
    verifyWithLean:false});
  assert.equal(result.status,"gpu-observed");
  assert.equal(result.dispatches,1);
  assert.deepEqual({...result.outputs},{out:[7,14,21]});
  assert.ok(released.length>=3);
  assert.equal(allocations.size,0);
});
