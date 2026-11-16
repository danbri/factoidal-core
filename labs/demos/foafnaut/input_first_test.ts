// Input first (page-load.mjs inputFirst, the rule of every host): a due timer turn waits while
// a scroll, key or press waits for its frame or came in the last INPUT_FIRST_MS, and never
// longer than TIMER_HOLD_MAX_MS. Until 2026-11-15 a scroll on a Wikipedia article waited about
// 2 s behind a 1.2 s timer turn and the layout after it.
import {strict as assert} from "node:assert";
import {inputFirst,INPUT_FIRST_MS,TIMER_HOLD_MAX_MS,turnSliceSteps} from "../../../docs/web/hub/foafnaut/page-load.mjs";

Deno.test("no input: a due timer turn runs", ()=>{
  assert.equal(inputFirst({now:1000,inputAt:-Infinity,waiting:false,heldSince:undefined}),false);
  assert.equal(inputFirst({now:1000,inputAt:1000-INPUT_FIRST_MS,waiting:false,heldSince:undefined}),false);
});

Deno.test("recent input, or input waiting for its frame: the timer turn waits", ()=>{
  assert.equal(inputFirst({now:1000,inputAt:990,waiting:false,heldSince:undefined}),true);
  assert.equal(inputFirst({now:1000,inputAt:-Infinity,waiting:true,heldSince:undefined}),true);
  assert.equal(inputFirst({now:1000,inputAt:990,waiting:true,heldSince:1000-TIMER_HOLD_MAX_MS+1}),true);
});

Deno.test("a timer turn is never held past TIMER_HOLD_MAX_MS: timers are not starved by a long scroll", ()=>{
  // a scroll every 16 ms for two seconds: the turn runs at least every TIMER_HOLD_MAX_MS
  let heldSince:number|undefined,ran=0,longest=0,last=0;
  for(let now=0;now<2000;now++){
    const inputAt=Math.floor(now/16)*16;
    if(inputFirst({now,inputAt,waiting:false,heldSince})){heldSince??=now;continue;}
    ran++;longest=Math.max(longest,now-last);last=now;heldSince=undefined;
  }
  assert.ok(ran>=2000/TIMER_HOLD_MAX_MS-1,`ran ${ran}`);
  assert.ok(longest<=TIMER_HOLD_MAX_MS+1,`longest wait ${longest}`);
});

Deno.test("the slice is a whole number of steps, about 50 ms of BubblePopJS", ()=>{
  assert.ok(Number.isInteger(turnSliceSteps)&&turnSliceSteps>=1000&&turnSliceSteps<=100000);
});

import {scrollFirst,SCROLL_QUIET_MS,SCROLL_HOLD_MAX_MS} from "../../../docs/web/hub/foafnaut/page-load.mjs";

Deno.test("scroll first: a page change waits while the user scrolls, at most SCROLL_HOLD_MAX_MS", ()=>{
  assert.equal(scrollFirst({now:1000,scrollAt:-Infinity,changedAt:undefined}),false);
  assert.equal(scrollFirst({now:1000,scrollAt:1000-SCROLL_QUIET_MS+1,changedAt:undefined}),true);
  assert.equal(scrollFirst({now:1000,scrollAt:1000-SCROLL_QUIET_MS,changedAt:undefined}),false);
  assert.equal(scrollFirst({now:5000,scrollAt:4999,changedAt:5000-SCROLL_HOLD_MAX_MS}),false);
  assert.equal(scrollFirst({now:5000,scrollAt:4999,changedAt:5000-SCROLL_HOLD_MAX_MS+1}),true);
});

Deno.test("scroll first: just after a page is first shown, a change waits SCROLL_QUIET_MS", ()=>{
  assert.equal(scrollFirst({now:1000,scrollAt:-Infinity,changedAt:undefined,shownAt:1000-SCROLL_QUIET_MS+1}),true);
  assert.equal(scrollFirst({now:1000,scrollAt:-Infinity,changedAt:undefined,shownAt:1000-SCROLL_QUIET_MS}),false);
});
