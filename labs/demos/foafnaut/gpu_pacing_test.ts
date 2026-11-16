// The host's GPU pacing (gpu_pacing.ts): the gate keeps one submission in flight, the guard
// slows animation on a page whose frames hold the GPU and lets go when they are fast again.
import {strict as assert} from "node:assert";
import {createGpuGate,createGpuGuard,GUARD_DEFAULTS,sceneCost,sceneCostIn} from "./gpu_pacing.ts";

/** A queue whose submissions finish when the test says. */
function fakeQueue(){
  const pending:(()=>void)[]=[];
  return {onSubmittedWorkDone:()=>new Promise<void>(resolve=>pending.push(resolve)),finishAll(){while(pending.length)pending.shift()!();},get asked(){return pending.length;}};
}
const tick=()=>new Promise(resolve=>setTimeout(resolve,0));

Deno.test("gate: light work has three submissions unanswered, the fourth waits", async()=>{
  const queue=fakeQueue(),gate=createGpuGate(queue,1);
  for(let i=0;i<3;i++){await gate.before();gate.after();}
  let started=false;
  const next=gate.before().then(()=>{started=true;});
  await tick();
  assert.equal(started,false);
  // One ask at a time: the first answers for submission 1, the next ask covers 2 and 3.
  for(let i=0;i<4&&!started;i++){queue.finishAll();await tick();}
  await next;
  assert.equal(started,true);
  assert.equal(gate.stats.maxInFlight,3);
  assert.equal(gate.stats.waits,1);
});

Deno.test("gate: after heavy work, one submission in flight", async()=>{
  // A GPU that takes 60 ms per submission.
  const queue={onSubmittedWorkDone:()=>new Promise<void>(resolve=>setTimeout(resolve,60))};
  const gate=createGpuGate(queue,1);
  gate.after();await gate.idle();
  await gate.before();gate.after();
  let started=false;
  const next=gate.before().then(()=>{started=true;});
  await new Promise(resolve=>setTimeout(resolve,5));
  assert.equal(started,false);
  await next;
  assert.equal(gate.inFlight,0);
  assert.equal(gate.stats.maxInFlight,1);
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

Deno.test("gate driven by the loop: asks start only at a turn, one a turn, and are traced", async()=>{
  const events:string[]=[];
  // A queue that answers at once (the GPU is done when asked).
  const queue={onSubmittedWorkDone:()=>Promise.resolve()};
  const gate=createGpuGate(queue,1,undefined,0,event=>events.push(event));
  gate.turn();
  for(let i=0;i<3;i++){await gate.before();gate.after();}
  await tick();
  assert.equal(events.filter(e=>e==="ask").length,0);
  gate.turn();events.push("pump");gate.turn();
  assert.equal(events.filter(e=>e==="ask").length,1);
  await tick();await tick();
  assert.equal(gate.inFlight,0);
  assert.deepEqual(events,["submit","submit","submit","ask","answer","pump"]);
});

Deno.test("gate driven by the loop: the fallback asks when the loop stops turning", async()=>{
  const queue={onSubmittedWorkDone:()=>Promise.resolve()};
  const gate=createGpuGate(queue,1);
  gate.turn();gate.after();
  await new Promise(resolve=>setTimeout(resolve,80));
  assert.equal(gate.inFlight,0);
  assert.equal(gate.stats.fallbackAsks,1);
});

Deno.test("gate: a settled submission (a readback) is answered at once", async()=>{
  const queue=fakeQueue(),gate=createGpuGate(queue,1);
  gate.turn();gate.after(0,true);
  assert.equal(gate.inFlight,0);
  await gate.quiet();
  assert.equal(queue.asked,0);
});

/** A queue like Deno's: the ask blocks the thread until the GPU is done (`doneAt`), and its
 * promise answers `lagMs` later. */
function blockingQueue(lagMs=11){
  const q={doneAt:0,asks:0,onSubmittedWorkDone():Promise<void> {
    q.asks++;
    while(performance.now()<q.doneAt){/* the blocking poll */}
    return new Promise<void>(resolve=>setTimeout(resolve,lagMs));
  }};
  return q;
}
const sleep=(ms:number)=>new Promise(resolve=>setTimeout(resolve,ms));

Deno.test("gate, answers at return: the next frame does not wait for the ask's promise", async()=>{
  const queue=blockingQueue(40),events:string[]=[];
  const gate=createGpuGate(queue,1,undefined,0,event=>events.push(event),{answersAtReturn:true});
  gate.turn();
  // Three submissions in flight (light work): the fourth waits for the answer.
  for(let i=0;i<3;i++){await gate.before();gate.after();}
  let resumedAt=0;
  const next=gate.before().then(()=>{resumedAt=performance.now();});
  const asked=performance.now();
  gate.turn();
  // Answered inside the turn (the call returned), though the promise is 40 ms away.
  assert.equal(gate.inFlight,0);
  assert.equal(gate.stats.returnAnswers,1);
  await next;
  assert(resumedAt-asked<20,`the frame resumed ${resumedAt-asked} ms after the ask`);
  assert.deepEqual(events,["submit","submit","submit","ask","answer"]);
  // One ask at a time still: the next ask waits for the first promise.
  gate.after();gate.turn();
  assert.equal(queue.asks,1);
  await sleep(60);gate.turn();
  assert.equal(queue.asks,2);
  assert.equal(gate.inFlight,0);
  assert.equal(gate.stats.answersAtReturn,true);
});

Deno.test("gate, answers at return: a queue that does not block is found out and answers by promise", async()=>{
  // The call returns at once and the promise answers 70 ms later, while the loop turns.
  const queue={onSubmittedWorkDone:()=>new Promise<void>(resolve=>setTimeout(resolve,70))};
  const gate=createGpuGate(queue,1,undefined,0,undefined,{answersAtReturn:true});
  gate.turn();
  for(let i=0;i<3;i++){
    assert.equal(gate.stats.answersAtReturn,true);
    gate.after();gate.turn();
    for(let k=0;k<10;k++){await sleep(10);gate.turn();}
  }
  assert.equal(gate.stats.answersAtReturn,false);
  // From now on the submission is in flight until the promise answers.
  gate.after();gate.turn();
  assert.equal(gate.inFlight,1);
  await gate.idle();
  assert.equal(gate.inFlight,0);
});

Deno.test("gate: a band is predicted by its own cost, not by the whole frame's time", async()=>{
  const queue=blockingQueue(1);
  const gate=createGpuGate(queue,1,undefined,0,undefined,{answersAtReturn:true});
  gate.turn();
  // A whole frame of 100 units that takes the GPU 80 ms: the ask blocks and measures the rate.
  queue.doneAt=performance.now()+80;
  gate.after(100);gate.turn();
  assert.equal(gate.inFlight,0);
  const rate=gate.stats.msPerUnit;
  assert(rate>0.7&&rate<1.0,`rate ${rate}`);
  assert(Math.abs(gate.msFor(100)-100*rate)<1);
  await sleep(5);
  // One band of the same scene (a sixteenth of its cost): due in about 5.5 ms, not 88.
  gate.after(100/16);
  const due=gate.dueIn();
  assert(due!==null&&due<12,`a band's ask is due in ${due} ms`);
  await gate.idle();
});

Deno.test("gate: predictions several times too long fall fast", async()=>{
  const queue=blockingQueue(1);
  const gate=createGpuGate(queue,1,undefined,0,undefined,{answersAtReturn:true});
  gate.turn();
  queue.doneAt=performance.now()+60;
  gate.after(10);gate.turn();
  const first=gate.stats.msPerUnit;
  // The GPU is now done at once: every ask finds it done (no measurement), the rate falls.
  const rates:number[]=[];
  for(let i=0;i<5;i++){
    await sleep(3);
    gate.after(10);
    for(let k=0;k<200&&gate.inFlight;k++){await sleep(2);gate.turn();}
    rates.push(gate.stats.msPerUnit);
  }
  // 0.9, 0.9, 0.75, 0.5, 0.5 of the one before: under a tenth of the first after five.
  assert(rates[4]<first*0.16,`rates ${first} -> ${rates.join(", ")}`);
  assert(rates[0]>first*0.85);
});

Deno.test("sceneCostIn: the whole frame is sceneCost; bands add up to it; an empty rectangle is 0", ()=>{
  // 2 x 2 tiles of 16 px on a 30 x 20 frame; tile lists: tile 0 has records 2 and 5, tile 3 has record 2.
  // Layout (gpu_pacing.ts): [size, across, down, offsets(4+1)..., entries...], listBase = 4+across*down.
  const tiles=[16,2,2, 0,2,2,2,3, 2,5,2];
  // Records: row base+1 holds [tag, count]: record 2 a path (tag 6) of 10 edges, record 5 a rect (tag 1).
  const data=new Float32Array(4*8);
  data[4*3]=6;data[4*3+1]=10;data[4*6]=1;data[4*6+1]=0;
  const frame={width:30,height:20,data,tiles};
  const whole=sceneCost(frame);
  assert(whole>0);
  assert(Math.abs(sceneCostIn(frame,[[0,0,30,20]])-whole)<1e-12);
  const top=sceneCostIn(frame,[[0,0,30,7]]),bottom=sceneCostIn(frame,[[0,7,30,13]]);
  assert(Math.abs(top+bottom-whole)<1e-12);
  assert.equal(sceneCostIn(frame,[[0,0,0,5]]),0);
  assert.equal(sceneCostIn(frame,[[100,100,5,5]]),0);
  // A rectangle inside tile 0 alone: its pixels times (1 + the edges of tile 0's records).
  assert(Math.abs(sceneCostIn(frame,[[2,2,4,4]])-16*(11+1)/1e6)<1e-12);
});
