// The host's GPU pacing (gpu_pacing.ts): the gate keeps one submission in flight, the guard
// slows animation on a page whose frames hold the GPU and lets go when they are fast again.
import {strict as assert} from "node:assert";
import {createGpuGate,createGpuGuard,GUARD_DEFAULTS} from "./gpu_pacing.ts";

/** A queue whose submissions finish when the test says. */
function fakeQueue(){
  const pending:(()=>void)[]=[];
  return {onSubmittedWorkDone:()=>new Promise<void>(resolve=>pending.push(resolve)),finishAll(){while(pending.length)pending.shift()!();},get asked(){return pending.length;}};
}
const tick=()=>new Promise(resolve=>setTimeout(resolve,0));

Deno.test("gate: the next GPU work waits until the work before is done", async()=>{
  const queue=fakeQueue(),gate=createGpuGate(queue,1);
  await gate.before();gate.after();
  assert.equal(gate.inFlight,1);
  let started=false;
  const next=gate.before().then(()=>{started=true;});
  await tick();
  assert.equal(started,false);
  queue.finishAll();await next;
  assert.equal(started,true);
  assert.equal(gate.inFlight,0);
  assert.equal(gate.stats.maxInFlight,1);
  assert.equal(gate.stats.waits,1);
});

Deno.test("gate: no wait when the GPU has finished", async()=>{
  const queue=fakeQueue(),gate=createGpuGate(queue,1);
  gate.after();await tick();queue.finishAll();await gate.idle();
  const start=performance.now();await gate.before();
  assert(performance.now()-start<5);
  assert.equal(gate.stats.waits,0);
});

Deno.test("gate: 0 is no bound and asks the GPU nothing until idle", async()=>{
  const queue=fakeQueue(),gate=createGpuGate(queue,0);
  for(let i=0;i<5;i++){await gate.before();gate.after();}
  assert.equal(queue.asked,0);
  assert.equal(gate.stats.submits,5);
  const idle=gate.idle();await tick();queue.finishAll();await idle;
});

Deno.test("gate: GPU times reach onDone, submit to done", async()=>{
  const queue=fakeQueue(),times:number[]=[];
  const gate=createGpuGate(queue,1,ms=>times.push(ms));
  gate.after();await tick();queue.finishAll();await gate.idle();
  assert.equal(times.length,1);
  assert(times[0]>=0);
});

Deno.test("guard: three heavy frames slow animation; three fast frames end it", ()=>{
  const guard=createGpuGuard();
  assert.equal(guard.gapMs(),0);
  assert.equal(guard.record(400),false);assert.equal(guard.record(400),false);
  assert.equal(guard.record(400),true);
  assert(guard.slowed);
  // The GPU is busy at most a quarter of the time: three times the frame between frames.
  assert.equal(guard.gapMs(),1200);
  // A fast frame or two do not end it; three in a row do.
  guard.record(20);guard.record(20);assert(guard.slowed);
  assert.equal(guard.record(20),true);
  assert(!guard.slowed);
  assert.equal(guard.gapMs(),0);
  assert.equal(guard.changes,2);
});

Deno.test("guard: frames between the two thresholds keep the state", ()=>{
  const guard=createGpuGuard();
  for(let i=0;i<10;i++)guard.record(200);
  assert(!guard.slowed);
  for(let i=0;i<3;i++)guard.record(300);
  assert(guard.slowed);
  for(let i=0;i<10;i++)guard.record(200);
  assert(guard.slowed);
  assert.equal(guard.gapMs(),Math.max(GUARD_DEFAULTS.minGapMs,600));
});

Deno.test("guard: the gap is bounded", ()=>{
  const guard=createGpuGuard();
  for(let i=0;i<3;i++)guard.record(4000);
  assert.equal(guard.gapMs(),GUARD_DEFAULTS.maxGapMs);
  const light=createGpuGuard();
  for(let i=0;i<3;i++)light.record(260);
  assert.equal(light.gapMs(),780);
});
