import {strict as assert} from "node:assert";
import {POINTER_CANCEL,beginPress,movePress,pointerNode,pressPointers,beforeFirstFrame} from "./native_press.ts";

Deno.test("release uses its own endpoint without a final move",()=>{
  const page={},press=beginPress(page,10,20);
  movePress(press,30,40);
  assert.deepEqual(movePress(press,50,60),[10,20,50,60]);
  assert.equal(press.page,page);
  assert.deepEqual(movePress(beginPress(page,10,20),80,90),[10,20,80,90]);
});

Deno.test("release and cancel fall back to the down node; move and empty down do not",()=>{
  for(const kind of ["up","cancel"] as const){
    const press=beginPress({},10,20);
    assert.equal(pointerNode(press,"down",7),7);
    assert.equal(pointerNode(press,"move",9),9);
    assert.equal(pointerNode(press,"move",null),undefined);
    assert.equal(pointerNode(press,kind,null),7);
    assert.equal(pointerNode(press,kind,11),11);
    const empty=beginPress({},10,20);
    assert.equal(pointerNode(empty,"down",null),undefined);
    assert.equal(pointerNode(empty,kind,null),undefined);
  }
});

Deno.test("input before the first frame retains press, release, cancel and command order",()=>{
  const ready=beforeFirstFrame<{event:{kind:number};at:number}>();
  const events=[1,2,3,4,10,2,POINTER_CANCEL].map((kind,at)=>({event:{kind},at}));
  assert.deepEqual(ready(events.slice(0,3),false),events.slice(0,1));
  assert.deepEqual(ready(events.slice(3),false),[]);
  assert.deepEqual(ready([],false),[]);
  assert.deepEqual(ready([],true),events.slice(1));
  assert.deepEqual(ready([],true),[]);
});

Deno.test("first-frame input is drained before newly arrived input",()=>{
  const ready=beforeFirstFrame<{event:{kind:number}}>();
  const down={event:{kind:2}},up={event:{kind:4}};
  assert.deepEqual(ready([down],false),[]);
  assert.deepEqual(ready([up],true),[down,up]);
  assert.deepEqual(ready([down,up],true),[down,up]);
});

Deno.test("fast release waits for the down hit and keeps its page after a tab change",async()=>{
  const queue=pressPointers(),owner={},other={};
  let page=owner;
  const press=beginPress(page,10,20),seen:unknown[]=[];
  let finish!:()=>void;
  const hit=new Promise<void>(resolve=>{finish=resolve;});
  const down=queue("down",async()=>{await hit;seen.push(["down",press.page,pointerNode(press,"down",7)]);});
  page=other;
  const up=queue("up",async()=>{seen.push(["up",press.page,pointerNode(press,"up",null)]);});
  await Promise.resolve();assert.deepEqual(seen,[]);
  finish();await Promise.all([down,up]);
  assert.notEqual(page,press.page);
  assert.deepEqual(seen,[["down",owner,7],["up",owner,7]]);
});

Deno.test("cancel and the next click retain separate nodes while down is pending",async()=>{
  const queue=pressPointers(),one=beginPress({},0,0),two=beginPress({},1,1),seen:unknown[]=[];
  let finish!:()=>void;
  const hit=new Promise<void>(resolve=>{finish=resolve;});
  const jobs=[queue("down",async()=>{await hit;pointerNode(one,"down",5);}),
    queue("cancel",async()=>{seen.push(["cancel",pointerNode(one,"cancel",null)]);}),
    queue("down",async()=>{pointerNode(two,"down",8);}),
    queue("up",async()=>{seen.push(["up",pointerNode(two,"up",null)]);})];
  finish();await Promise.all(jobs);
  assert.deepEqual(seen,[["cancel",5],["up",8]]);
});

Deno.test("busy moves are skipped but release and later input survive a failed call",async()=>{
  const queue=pressPointers(),seen:string[]=[];
  const failed=queue("down",async()=>{throw new Error("hit failed");});
  const failure=assert.rejects(failed,/hit failed/);
  const move=queue("move",async()=>{seen.push("busy move");});
  const up=queue("up",async()=>{seen.push("up");});
  await Promise.all([failure,move,up]);
  await queue("move",async()=>{seen.push("idle move");});
  assert.deepEqual(seen,["up","idle move"]);
});

Deno.test("close, resize and occlusion do not wait behind a held press", () => {
  const ready = beforeFirstFrame<{ event: { kind: number } }>();
  const e = (kind: number) => ({ event: { kind } });
  assert(ready([e(2), e(6)], false).map((i) => i.event.kind).join() === "6");
  assert(ready([e(4), e(1), e(8)], false).map((i) => i.event.kind).join() === "1,8");
  assert(ready([], true).map((i) => i.event.kind).join() === "2,4");
});
