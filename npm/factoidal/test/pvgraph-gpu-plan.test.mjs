import test from "node:test";
import assert from "node:assert/strict";
import {executePVGraphGpuPlan} from "../lib/gdsl-gpu.mjs";

function plan(){
  return {version:"pvgraph-gpu/0.2",shaders:{word:"word source",scan:"scan source"},
    steps:[{kind:"input",node:"input/a",name:"x",words:3},
      {kind:"kernel",node:"local",a:"input/a",b:"input/a",words:3,
        workgroups:1,shader:"scan",config:[30,3,0,3,3]},
      {kind:"kernel",node:"final",a:"local",b:"input/a",words:3,
        workgroups:1,shader:"word",config:[31,3,64,3,3]}],
    outputs:[{name:"answer",source:"final",kind:"buffer",words:3}]};
}
function recordingSession({readback=[1,3,6],fail=null}={}){
  const allocated=new Map(),events=[];
  return {allocated,events,
    status:()=>({byteBudget:1024,usedBytes:0}),
    async compile(id,source){events.push(["compile",id,source]);},
    async upload(id,data){allocated.set(id,data.byteLength);events.push(["upload",id,[...data]]);},
    allocate(id,bytes){allocated.set(id,bytes);events.push(["allocate",id,bytes]);},
    async dispatchBatch(commands){events.push(["batch",commands]);if(fail)throw Error(fail);},
    async readWords(id,shape){events.push(["read",id,shape]);return readback;},
    release(id){allocated.delete(id);events.push(["release",id]);}
  };
}

test("multi-pass transport submits one batch and preserves Lean configurations",async()=>{
  const session=recordingSession();
  const result=await executePVGraphGpuPlan({plan:plan(),bindings:{x:[1,2,3]},session});
  assert.deepEqual({...result.outputs},{answer:[1,3,6]});
  assert.equal(result.dispatches,2);
  const batches=session.events.filter(e=>e[0]==="batch");
  assert.equal(batches.length,1);
  const commands=batches[0][1];
  assert.equal(commands[1].bindings[0].id,commands[0].writes[0]);
  assert.deepEqual(session.events.filter(e=>e[0]==="upload").map(e=>e[2]),
    [[1,2,3],[30,3,0,3,3],[31,3,64,3,3]]);
  assert.equal(session.allocated.size,0);
  assert.equal(session.events.findIndex(e=>e[0]==="read")>
    session.events.findIndex(e=>e[0]==="batch"),true);
});

test("invalid transport plans fail before GPU allocation or compilation",async()=>{
  for(const mutate of [
    p=>{p.steps[0].words=4194241;},
    p=>{p.steps[1].config[0]=NaN;},
    p=>{p.steps[1].a="future";},
    p=>{p.steps[1].workgroups=65536;},
    p=>{p.steps[1].node=p.steps[0].node;},
    p=>{p.outputs[0].words=4;},
    p=>{p.outputs.push(p.outputs[0]);},
    p=>{p.shaders.scan="";}
  ]){
    const value=plan(),session=recordingSession();mutate(value);
    await assert.rejects(executePVGraphGpuPlan({plan:value,bindings:{x:[1,2,3]},session}));
    assert.deepEqual(session.events,[]);
  }
});

test("device failure releases all invocation resources",async()=>{
  const session=recordingSession({fail:"device lost"});
  await assert.rejects(executePVGraphGpuPlan({plan:plan(),bindings:{x:[1,2,3]},session}),
    /device lost/);
  assert.equal(session.allocated.size,0);
  assert.equal(session.events.some(e=>e[0]==="read"),false);
});

test("truncated device readback fails rather than supplying a partial result",async()=>{
  const session=recordingSession({readback:[1,3]});
  await assert.rejects(executePVGraphGpuPlan({plan:plan(),bindings:{x:[1,2,3]},session}),
    /incomplete GPU output/);
  assert.equal(session.allocated.size,0);
});

test("resource names cannot alias through punctuation in Lean node IDs",async()=>{
  const value=plan();
  value.steps[1].node="input_a";
  value.steps[2].a="input_a";
  const session=recordingSession();
  await executePVGraphGpuPlan({plan:value,bindings:{x:[1,2,3]},session});
  const ids=session.events.filter(e=>["upload","allocate"].includes(e[0])).map(e=>e[1]);
  assert.equal(new Set(ids).size,ids.length);
});
