// Sliced timer turns (WebScripts action `advance` with `sliceSteps`; PageEvents.Engine.advanceUntil;
// EventLoop.Driver.advanceGoStop with its theorems advanceGo_eq_stop, advanceGoStop_resume,
// advanceGoStop_never). A host that takes input between turns asks for at most `sliceSteps` steps
// of the page's scripts: the engine stops between two tasks, and what is still due is due at once
// (`nextWake` is the clock). Slicing changes no result: an original page with many timers,
// promises and a frame callback gives the same logs, DOM and clock sliced as in one advance, and
// each slice stops within one task of its budget. Also the script clock's own rate
// (LeanJS.stepsPerMs): a loop that waits for the clock to move 50 ms ends far before the step budget.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env turn_slice_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Turn=ScriptTurn&{logs:string[];errors:string[];instructions:number;clock:number;nextWake:number|null;commands?:unknown[];changes:number};

const page=`<!doctype html><html><body><ol id="out"></ol><script>
const out=document.getElementById('out');
const note=t=>{const li=document.createElement('li');li.textContent=t;out.appendChild(li);console.log(t);};
function work(n){let x=0;for(let i=0;i<n;i++)x=(x*31+i)%1000003;return x;}
for(let k=0;k<24;k++)setTimeout(()=>{note('task '+k+' '+work(400+k*10));Promise.resolve().then(()=>note('micro '+k));},k%3);
requestAnimationFrame(t=>note('frame'));
setTimeout(()=>note('late'),40);
</script></body></html>`;

const start={action:"start",url:"http://example.test/slices.html",resources:[],engine:"bubblepop",width:800,height:600,instructionsPerMs:1e12};

Deno.test({name:"sliced advances give the logs, DOM and clock of one advance",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const one=engine.scriptSession(page,start) as Turn;
  const whole=engine.scriptSession("",{action:"advance",session:one.session,ms:60}) as Turn;
  engine.scriptSession("",{action:"close"});

  const first=engine.scriptSession(page,start) as Turn;
  const logs:string[]=[];let turn:Turn=first,slices=0,maxSteps=0,target=60;
  // the host's loop: ask for the time still to go; a stopped slice leaves work due at once
  for(let i=0;i<10000;i++){
    turn=engine.scriptSession("",{action:"advance",session:first.session,ms:Math.max(0,target-turn.clock),sliceSteps:300}) as Turn;
    logs.push(...turn.logs);slices++;maxSteps=Math.max(maxSteps,turn.instructions);
    // the host goes on while the clock is short of its target or something is due now
    if(!(turn.clock<target||(turn.nextWake!==null&&turn.nextWake<=turn.clock)))break;
  }
  const full=engine.scriptSession("",{action:"turn",session:first.session,full:true}) as Turn;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(logs,whole.logs,"the same logs, in the same order");
  assert.equal(turn.clock,whole.clock,"the same clock");
  assert.ok(slices>3,`the advance was cut into slices (${slices})`);
  // one task of this page is at most about 1,000 steps: a slice stops within one task of 300
  assert.ok(maxSteps<300+2000,`a slice ran ${maxSteps} steps`);
  const wholeFull=engine.scriptSession(page,start) as Turn;
  const again=engine.scriptSession("",{action:"advance",session:wholeFull.session,ms:60,full:true}) as Turn;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(full.commands,again.commands,"the same DOM");
}});

Deno.test({name:"a loop that waits 50 ms of the script clock ends within the budget (BubblePopJS rate)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const waiting=`<!doctype html><script>setTimeout(()=>{const end=performance.now()+50;let n=0;while(performance.now()<end)n++;console.log('spun '+(n>0));},0);</script>`;
  // the host names no rate: the engine's own (LeanJS.stepsPerMs)
  const first=engine.scriptSession(waiting,{action:"start",url:"http://example.test/w.html",resources:[],engine:"bubblepop",width:800,height:600}) as Turn;
  const turn=engine.scriptSession("",{action:"advance",session:first.session,ms:10}) as Turn;
  engine.scriptSession("",{action:"close"});
  // the timer is due at time 0: the start turn runs it
  assert.deepEqual([...first.errors,...turn.errors],[],"no step-budget halt");
  assert.ok([...first.logs,...turn.logs].some(l=>l.includes("spun true")),JSON.stringify([first.logs,turn.logs]));
  // 50 ms at 500 steps a ms, with the loop's own steps: far below the 5 M budget
  assert.ok(first.instructions+turn.instructions<200000,`the loop ran ${first.instructions+turn.instructions} steps`);
}});
