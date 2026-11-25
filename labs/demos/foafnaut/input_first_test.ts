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

import {scriptsFirst,startSliceSteps,SCRIPTS_HOLD_MIN_MS,SCRIPTS_HOLD_MAX_MS,SCRIPTS_HOLD_LAYOUTS} from "../../../docs/web/hub/foafnaut/page-load.mjs";

Deno.test("scripts first: a page change waits while the page's start has not finished, a few layout times at most", ()=>{
  // a start that finished holds nothing
  assert.equal(scriptsFirst({now:1000,more:false,changedAt:undefined,layoutMs:1500}),false);
  assert.equal(scriptsFirst({now:1000,more:false,changedAt:990,layoutMs:1500}),false);
  // a start that has not: the change waits, from when it was made
  assert.equal(scriptsFirst({now:1000,more:true,changedAt:undefined,layoutMs:1500}),true);
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_LAYOUTS*1500-1,more:true,changedAt:1000,layoutMs:1500}),true);
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_LAYOUTS*1500,more:true,changedAt:1000,layoutMs:1500}),false);
  // a page whose layout is quick is drawn often; a very slow one within the most
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_MIN_MS-1,more:true,changedAt:1000,layoutMs:2}),true);
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_MIN_MS,more:true,changedAt:1000,layoutMs:2}),false);
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_MAX_MS,more:true,changedAt:1000,layoutMs:60000}),false);
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_MAX_MS-1,more:true,changedAt:1000,layoutMs:60000}),true);
  // with no layout timed yet, the least
  assert.equal(scriptsFirst({now:1000+SCRIPTS_HOLD_MIN_MS,more:true,changedAt:1000}),false);
});

Deno.test("scripts first: a host that draws when the rule lets it spends at most a quarter of a long start in layouts", ()=>{
  // a start of 20 s of script slices that each change the page; a layout takes 1.5 s
  const layoutMs=1500;let now=0,changedAt:number|undefined,layouts=0,scriptMs=0;
  while(scriptMs<20000){
    now+=50;scriptMs+=50;changedAt??=now;                       // a slice, and its change
    if(!scriptsFirst({now,more:true,changedAt,layoutMs})){now+=layoutMs;layouts++;changedAt=undefined;}
  }
  assert.ok(layouts>=3&&layouts*layoutMs<=scriptMs/SCRIPTS_HOLD_LAYOUTS+layoutMs,`${layouts} layouts in ${scriptMs} ms of scripts`);
});

Deno.test("the start's slice is a whole number of steps", ()=>{
  assert.ok(Number.isInteger(startSliceSteps)&&startSliceSteps>=1000&&startSliceSteps<=100000);
});
