import {strict as assert} from "node:assert";
import {createBandWake} from "./presenter_wake.ts";

Deno.test("presenter wake: final publication before old reply triggers another read",async()=>{
  let latest=0,seen=0,sends=0;
  const replies:(()=>void)[]=[];
  const wake=createBandWake(()=>{
    sends++;
    seen=latest; // worker read precedes its reply
    return new Promise<void>(resolve=>replies.push(resolve));
  },()=>true);
  latest=10;wake(1n);
  assert.equal(seen,10);
  latest=20;wake(2n);
  latest=30;wake(3n);
  assert.equal(sends,1,"writes share the outstanding wake");
  replies.shift()!();
  await Promise.resolve();
  assert.equal(sends,2,"the newer final value gets a read after the old reply");
  assert.equal(seen,30);
  replies.shift()!();
  await Promise.resolve();
  assert.equal(sends,2,"no new value means no extra wake");
});

Deno.test("presenter wake: termination prevents queued wake dispatch",async()=>{
  let alive=true,sends=0,reply:()=>void=()=>{};
  const wake=createBandWake(()=>{sends++;return new Promise<void>(resolve=>{reply=resolve;});},()=>alive);
  wake(1n);wake(2n);alive=false;reply();
  await Promise.resolve();
  assert.equal(sends,1);
});
