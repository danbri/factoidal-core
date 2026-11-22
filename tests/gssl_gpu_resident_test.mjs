import test from "node:test";
import assert from "node:assert/strict";
import {webcrypto} from "node:crypto";
import {createGsslResidentSession} from "../tools/gssl-gpu-resident.mjs";

globalThis.crypto ??= webcrypto;
globalThis.GPUBufferUsage = Object.freeze({
  STORAGE:1,COPY_SRC:2,COPY_DST:4,MAP_READ:8,
});
globalThis.GPUMapMode = Object.freeze({READ:1});

class MockGPUBuffer {
  constructor(size,usage) {
    this.size=size;this.usage=usage;this.data=new Uint8Array(size);
    this.mapState="unmapped";this.destroyed=false;
  }
  destroy(){this.destroyed=true;}
  async mapAsync(){assert.equal(this.destroyed,false);this.mapState="mapped";}
  unmap(){this.mapState="unmapped";}
  getMappedRange(){
    if(this.mapState!=="mapped")throw new Error("not mapped");
    return this.data.buffer;
  }
}
function mockDevice({slowFence=false,compileFailure=false}={}) {
  const stats={created:0,shaderCompiles:0,writes:0,submissions:0,destroyed:0,dispatches:0};
  let resume=()=>{}, signalLost=()=>{};
  const lost=new Promise(resolve=>{signalLost=resolve;});
  const fence=()=>slowFence?new Promise(resolve=>{resume=resolve;}):Promise.resolve();
  const device={
    lost,
    createBuffer({size,usage}){
      stats.created++;
      return new MockGPUBuffer(size,usage);
    },
    createShaderModule({code}){
      stats.shaderCompiles++;
      return {code,async getCompilationInfo(){
        return {messages:compileFailure?[{type:"error",message:"deliberate error"}]:[]};
      }};
    },
    createComputePipeline({compute}){
      return {code:compute.module.code,getBindGroupLayout:()=>({})};
    },
    createBindGroup({entries}){
      return {bindings:new Map(entries.map(x=>[x.binding,x.resource.buffer]))};
    },
    createCommandEncoder(){
      const commands=[];
      return {
        beginComputePass(){
          let pipeline,group;
          return {
            setPipeline(p){pipeline=p;},
            setBindGroup(_slot,g){group=g;},
            dispatchWorkgroups(){commands.push(()=>{
              stats.dispatches++;
              if(pipeline.code.includes("mock-add-one")){
                const input=new Uint32Array(group.bindings.get(0).data.buffer);
                const output=new Uint32Array(group.bindings.get(1).data.buffer);
                for(let i=0;i<input.length;i++)output[i]=input[i]+1;
              }else if(pipeline.code.includes("mock-overwrite")){
                const output=new Uint32Array(group.bindings.get(0).data.buffer);
                output[0]=88;
              }
            });},
            end(){},
          };
        },
        copyBufferToBuffer(from,fo,to,at,size){
          commands.push(()=>to.data.set(from.data.subarray(fo,fo+size),at));
        },
        finish(){return commands;},
      };
    },
    queue:{
      writeBuffer(buffer,offset,data){
        stats.writes++;
        if(buffer.destroyed)throw Error("write destroyed");
        const bytes=new Uint8Array(data.buffer,data.byteOffset,data.byteLength);
        buffer.data.set(bytes,offset);
      },
      submit(commandBuffers){
        stats.submissions++;
        for(const commands of commandBuffers)for(const cmd of commands)cmd();
      },
      onSubmittedWorkDone:fence,
    },
    destroy(){stats.destroyed++;},
  };
  return {device,stats,resume:()=>resume(),lose:()=>signalLost({reason:'destroyed'})};
}
const source="// mock-add-one\n@compute @workgroup_size(1) fn main() {}";

test("resident data remains GPU-backed across dispatches; unchanged bytes upload once",async()=>{
  const {device,stats}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:128});
  assert.deepEqual(await s.upload("input",new Uint32Array([2,5,9,12])),
    {id:"input",sha256:(await s.upload("input",new Uint32Array([2,5,9,12]))).sha256,
     uploaded:true,revision:1});
  // The assertion above intentionally calls upload twice; the second is a reuse.
  assert.equal(s.status().uploads,1);
  assert.equal(s.status().reuses,1);
  s.allocate("scratch",16);
  s.allocate("result",16);
  await s.compile("add-one",source);
  await s.compile("add-one",source);
  assert.equal(s.status().createdPipelines,1);
  await s.dispatch({kernel:"add-one",bindings:[
    {binding:0,id:"input"},{binding:1,id:"scratch"}],
    writes:["scratch"],workgroups:[1,1,1]});
  await s.dispatch({kernel:"add-one",bindings:[
    {binding:0,id:"scratch"},{binding:1,id:"result"}],
    writes:["result"],workgroups:[1,1,1]});
  const result=await s.inspect("result",{countWords:4});
  assert.deepEqual(result.words,[4,7,11,14]);
  assert.equal(s.status().submissions,2);
  assert.equal(s.status().readbacks,1);
  assert.equal(s.status().uploads,1);
  assert.equal(stats.writes,1);
  assert.equal(s.status().resources.find(r=>r.id==="result").dirty,true);
  s.close();s.close();
  assert.equal(stats.destroyed,0); // injected device is borrowed
});

test("GPU mutation invalidates upload reuse, even when re-uploading original bytes",async()=>{
  const {device}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:64});
  await s.upload("buffer",new Uint32Array([3,4]));
  await s.compile("overwrite","// mock-overwrite\n@compute fn main() {}");
  await s.dispatch({kernel:"overwrite",bindings:[{binding:0,id:"buffer"}],
    writes:["buffer"],workgroups:[1,1,1]});
  assert.deepEqual((await s.inspect("buffer",{countWords:2})).words,[88,4]);
  const again=await s.upload("buffer",new Uint32Array([3,4]));
  assert.equal(again.uploaded,true);
  assert.deepEqual((await s.inspect("buffer",{countWords:2})).words,[3,4]);
  assert.equal(s.status().uploads,2);
  s.close();
});

test("resource cap, inspections, initialization and close are enforced",async()=>{
  const {device,stats}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:32,inspectMaxWords:2,ownsDevice:true});
  s.allocate("a",16);
  s.allocate("b",16);
  assert.throws(()=>s.allocate("c",4),/budget/);
  await assert.rejects(s.inspect("a",{countWords:1}),/Uninitialized/);
  assert.throws(()=>s.allocate("a",4),/already allocated/);
  assert.throws(()=>s.allocate("not valid?",4),/identifier/);
  assert.throws(()=>s.allocate("c",3),/multiple of four/);
  assert.equal(s.release("a"),true);
  assert.equal(s.release("a"),false);
  await s.upload("c",new Uint32Array([1,2]));
  await assert.rejects(s.inspect("c",{countWords:3}),/bounds/);
  await assert.rejects(s.inspect("c",{offsetWords:2,countWords:1}),/bounds/);
  assert.deepEqual((await s.inspect("c",{offsetWords:1,countWords:1})).words,[2]);
  s.close();s.close();
  assert.equal(stats.destroyed,1);
  assert.throws(()=>s.allocate("z",4),/closed/);
});

test("reject uninitialized reads and incorrect write ownership",async()=>{
  const {device}=mockDevice();
  const s=await createGsslResidentSession({device});
  s.allocate("out",4);
  await s.compile("noop","@compute fn main() {}");
  await assert.rejects(s.dispatch({kernel:"noop",bindings:[{binding:0,id:"out"}],
    workgroups:[1,1,1]}),/Uninitialized/);
  await assert.rejects(s.dispatch({kernel:"noop",bindings:[{binding:0,id:"out"}],
    writes:["unbound"],workgroups:[1,1,1]}),/bound resources/);
  await assert.rejects(s.dispatch({kernel:"noop",bindings:[{binding:0,id:"out"}],
    writes:["out"],workgroups:[65536,1,1]}),/workgroups/);
  s.close();
});

test("busy session rejects overlapping buffer mutation, readback, and close",async()=>{
  const {device,resume}=mockDevice({slowFence:true});
  const s=await createGsslResidentSession({device});
  await s.upload("x",new Uint32Array([10]));
  await s.compile("noop","@compute fn main() {}");
  const pending=s.dispatch({kernel:"noop",bindings:[{binding:0,id:"x"}],
    writes:["x"],workgroups:[1,1,1]});
  assert.throws(()=>s.release("x"),/busy/);
  await assert.rejects(s.inspect("x"),/busy/);
  assert.throws(()=>s.close(),/busy/);
  resume();
  await pending;
  s.close();
});

test("compilation diagnostics do not register a failed kernel",async()=>{
  const {device}=mockDevice({compileFailure:true});
  const s=await createGsslResidentSession({device});
  await assert.rejects(s.compile("bad","@compute fn main() {}"),/deliberate error/);
  assert.equal(s.status().kernelCount,0);
  s.close();
});

test("changed buffer usage replaces the resource and re-upload is not confused with a cache hit",async()=>{
  const {device}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:32});
  const small=GPUBufferUsage.STORAGE|GPUBufferUsage.COPY_DST;
  await s.upload("x",new Uint32Array([99]),{usage:small});
  assert.equal(s.status().usedBytes,4);
  await assert.rejects(s.inspect("x",{countWords:1}),/COPY_SRC/);
  const replacement=await s.upload("x",new Uint32Array([99]),
    {usage:small|GPUBufferUsage.COPY_SRC});
  assert.equal(replacement.uploaded,true);
  assert.equal(s.status().usedBytes,4);
  assert.deepEqual((await s.inspect("x",{countWords:1})).words,[99]);
  s.close();
});

test("host write failure poisons cached version; close is possible after device loss",async()=>{
  const {device,lose}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:32});
  await s.upload("x",new Uint32Array([1]));
  const originalWrite=device.queue.writeBuffer;
  device.queue.writeBuffer=()=>{throw Error("driver rejected host write");};
  await assert.rejects(s.upload("x",new Uint32Array([2])),/driver rejected/);
  const resource=s.status().resources.find(r=>r.id==="x");
  assert.equal(resource.dirty,true);
  assert.equal(resource.initialized,false);
  assert.equal(resource.sha256,null);
  device.queue.writeBuffer=originalWrite;
  await s.upload("x",new Uint32Array([1]));
  assert.deepEqual((await s.inspect("x",{countWords:1})).words,[1]);
  lose();await Promise.resolve();await Promise.resolve();
  assert.equal(s.status().lost,true);
  s.close();s.close();
  assert.equal(s.status().closed,true);
});

test("dependent compute passes run in one submission with ordered writes",async()=>{
  const {device,stats}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:64});
  await s.upload("input",new Uint32Array([2,5,9,12]));
  s.allocate("scratch",16);s.allocate("result",16);
  await s.compile("add-one",source);
  await s.dispatchBatch([
    {kernel:"add-one",bindings:[{binding:0,id:"input"},{binding:1,id:"scratch"}],
      writes:["scratch"],workgroups:[1,1,1]},
    {kernel:"add-one",bindings:[{binding:0,id:"scratch"},{binding:1,id:"result"}],
      writes:["result"],workgroups:[1,1,1]}
  ]);
  assert.equal(stats.submissions,1);
  assert.equal(stats.dispatches,2);
  assert.deepEqual(await s.readWords("result",{countWords:4}),[4,7,11,14]);
  s.close();
});

test("invalid later batch command prevents all earlier dispatches",async()=>{
  const {device,stats}=mockDevice();
  const s=await createGsslResidentSession({device,byteBudget:64});
  await s.upload("input",new Uint32Array([2]));s.allocate("result",4);
  await s.compile("add-one",source);
  await assert.rejects(s.dispatchBatch([
    {kernel:"add-one",bindings:[{binding:0,id:"input"},{binding:1,id:"result"}],
      writes:["result"],workgroups:[1,1,1]},
    {kernel:"absent",bindings:[{binding:0,id:"result"}],workgroups:[1,1,1]}
  ]),/Unknown compute kernel/);
  assert.equal(stats.submissions,0);
  assert.equal(stats.dispatches,0);
  await assert.rejects(s.readWords("result",{countWords:1}),/Uninitialized/);
  s.close();
});

test("device storage limits are checked before buffer creation",async()=>{
  const {device,stats}=mockDevice();
  device.limits={maxBufferSize:64,maxStorageBufferBindingSize:16};
  const s=await createGsslResidentSession({device,byteBudget:128});
  assert.throws(()=>s.allocate("large",20),/device storage/);
  await assert.rejects(s.upload("large",new Uint32Array(5)),/device storage/);
  assert.equal(stats.created,0);
  assert.equal(s.status().resourceCount,0);
  s.close();
});

test("asynchronous batch validation failure poisons all destinations",async()=>{
  const {device}=mockDevice();
  const scopes=[];
  device.pushErrorScope=kind=>scopes.push(kind);
  device.popErrorScope=async()=>({message:"injected binding validation error"});
  const s=await createGsslResidentSession({device,byteBudget:128});
  await s.upload("input",new Uint32Array([1,2]));
  s.allocate("output",8);
  await s.compile("add-one",source);
  await assert.rejects(s.dispatchBatch([{kernel:"add-one",bindings:[
    {binding:0,id:"input"},{binding:1,id:"output"}],writes:["output"]}]),
    /injected binding validation error/);
  assert.deepEqual(scopes,["validation"]);
  await assert.rejects(s.readWords("output",{countWords:2}),/Uninitialized/);
  await s.upload("output",new Uint32Array([7,8]));
  assert.deepEqual(await s.readWords("output",{countWords:2}),[7,8]);
  s.close();
});
