// A start in slices (WebScripts action `start` with `sliceSteps`; LeanJS.startSome with its
// theorems startSome_never, startSome_resume, startFinish_eq_startSome; WebScripts.startGoOn_never).
// A host that shows the page between slices gives the start a step budget: the classic scripts
// run whole, then the module scripts, DOMContentLoaded, the load event and the tasks due at once
// stop between two of them past the budget; the turn says `startMore`, what is left is due at
// once (`nextWake` is the clock), and each `advance` with `sliceSteps` goes on. Until 2026-11-16
// the start was one turn: a news article's first frame waited 15 s for 9.6 M steps of module
// scripts and two hydration tasks. Slicing changes no result: an original page with classic
// scripts, module scripts, DOMContentLoaded and load listeners, timers and promises gives the
// same logs in the same order, the same DOM and the same errors sliced as whole; each slice
// stops within one script or task of its budget; an action that takes no budget (`turn`,
// `settle`, an `advance` without `sliceSteps`) finishes the start first.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env start_slice_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Turn=ScriptTurn&{logs:string[];errors:string[];instructions:number;clock:number;nextWake:number|null;commands?:unknown[];startMore?:boolean};

const modules=Array.from({length:8},(_,k)=>`<script type="module">note('module ${k} '+work(${600+k*50}));Promise.resolve().then(()=>note('module micro ${k}'));
if(${k}===3)setTimeout(()=>note('timer of module 3'),0);</script>`).join("\n");
const page=`<!doctype html><html><body><ol id="out"></ol><script>
const out=document.getElementById('out');
function note(t){const li=document.createElement('li');li.textContent=t;out.appendChild(li);console.log(t);}
function work(n){let x=0;for(let i=0;i<n;i++)x=(x*31+i)%1000003;return x;}
note('classic 1 '+work(900)+' '+document.readyState);
document.addEventListener('DOMContentLoaded',()=>{note('DOMContentLoaded '+work(500)+' '+document.querySelectorAll('li').length);
  for(let k=0;k<12;k++)setTimeout(()=>{note('task '+k+' '+work(400+k*10));Promise.resolve().then(()=>note('micro '+k));},0);});
window.addEventListener('load',()=>note('load '+document.readyState));
setTimeout(()=>note('early timer'),0);
</script>
<script>note('classic 2 '+work(700));</script>
${modules}
<script>note('classic 3 after the modules in the document');</script></body></html>`;

const start={action:"start",url:"http://example.test/start-slices.html",resources:[],engine:"bubblepop",width:800,height:600,instructionsPerMs:1e12};

Deno.test({name:"a start in slices gives the logs, DOM and errors of a whole start",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  if(!(engine.scriptInfo().engines??[]).includes("bubblepop")){console.log("NOT RUN: this engine has no BubblePopJS");return;}
  const whole=engine.scriptSession(page,{...start,full:true}) as Turn;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(whole.errors,[],"page errors of the whole start");
  assert.equal(whole.startMore,undefined,"a start without a budget is whole");
  assert.ok(whole.logs.some(l=>l.startsWith("load ")),"the whole start ran the load event");

  const budget=400;
  const first=engine.scriptSession(page,{...start,sliceSteps:budget}) as Turn;
  const logs=[...first.logs],errors=[...first.errors];let turn=first,slices=1,maxSteps=0;
  // the classic scripts run whole, in document order, before the first answer
  assert.deepEqual(first.logs.filter(l=>l.startsWith("classic")).map(l=>l.slice(0,9)),["classic 1","classic 2","classic 3"],"the classic scripts are in the first slice");
  assert.equal(first.startMore,true,"the first slice says the start is not finished");
  assert.equal(first.nextWake,first.clock,"what is left is due at once");
  assert.ok(!first.logs.some(l=>l.startsWith("DOMContentLoaded")),"DOMContentLoaded waits for the module scripts");
  for(let i=0;i<10000&&turn.startMore;i++){
    turn=engine.scriptSession("",{action:"advance",session:first.session,ms:0,sliceSteps:budget}) as Turn;
    logs.push(...turn.logs);errors.push(...turn.errors);slices++;maxSteps=Math.max(maxSteps,turn.instructions);
  }
  // the tasks still queued when the start's own steps ended
  for(let i=0;i<10000&&turn.nextWake!==null&&turn.nextWake<=turn.clock;i++){
    turn=engine.scriptSession("",{action:"advance",session:first.session,ms:0,sliceSteps:budget}) as Turn;
    logs.push(...turn.logs);errors.push(...turn.errors);slices++;maxSteps=Math.max(maxSteps,turn.instructions);
  }
  const full=engine.scriptSession("",{action:"turn",session:first.session,full:true}) as Turn;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(errors,[],"page errors of the sliced start");
  assert.deepEqual(logs,whole.logs,"the same logs, in the same order");
  assert.deepEqual(full.commands,whole.commands,"the same DOM");
  assert.ok(slices>8,`the start was cut into slices (${slices})`);
  // one script or task of this page is at most about 2,500 steps: a slice stops within one of its budget
  assert.ok(maxSteps<budget+4000,`a slice ran ${maxSteps} steps`);
  console.log(`start in ${slices} slices of at most ${maxSteps} steps; ${whole.logs.length} log lines`);
}});

Deno.test({name:"an action without a budget finishes a start that stopped",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  if(!(engine.scriptInfo().engines??[]).includes("bubblepop"))return;
  const whole=engine.scriptSession(page,start) as Turn;
  engine.scriptSession("",{action:"close"});
  for(const action of ["turn","settle","advance"]){
    const first=engine.scriptSession(page,{...start,sliceSteps:400}) as Turn;
    assert.equal(first.startMore,true);
    const rest=engine.scriptSession("",{action,session:first.session,...(action==="advance"?{ms:0}:{})}) as Turn;
    engine.scriptSession("",{action:"close"});
    assert.equal(rest.startMore,undefined,`${action}: the start is finished`);
    assert.deepEqual([...first.logs,...rest.logs],whole.logs,`${action}: the same logs as a whole start`);
  }
}});

Deno.test({name:"a click between the slices of a start reaches the page as it is then",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  if(!(engine.scriptInfo().engines??[]).includes("bubblepop"))return;
  const clicky=`<!doctype html><html><body><button id="b">b</button><script>
function work(n){let x=0;for(let i=0;i<n;i++)x=(x*31+i)%1000003;return x;}
document.getElementById('b').addEventListener('click',()=>console.log('click, modules run: '+(window.ran||0)));
</script>${Array.from({length:6},(_,k)=>`<script type="module">work(900);window.ran=(window.ran||0)+1;console.log('module ${k}');</script>`).join("")}</body></html>`;
  const first=engine.scriptSession(clicky,{...start,sliceSteps:300}) as Turn;
  assert.equal(first.startMore,true);
  // the button's node number is not known here: the first node whose click the listener hears
  let clicked:Turn|undefined;
  for(let node=1;node<12&&!clicked?.logs.some(l=>l.startsWith("click"));node++)
    clicked=engine.scriptSession("",{action:"click",session:first.session,node}) as Turn;
  assert.ok(clicked?.logs.some(l=>l.startsWith("click, modules run: ")),"the click's listener ran");
  assert.equal(clicked!.startMore,true,"the click did not finish the start");
  const rest=engine.scriptSession("",{action:"settle",session:first.session}) as Turn;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(rest.logs.filter(l=>l.startsWith("module")).length+first.logs.filter(l=>l.startsWith("module")).length+clicked!.logs.filter(l=>l.startsWith("module")).length,6,"every module script ran once");
}});
