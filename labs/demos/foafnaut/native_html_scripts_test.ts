// Page scripts run by Lean (WebScripts.lean; record docs/designissues/2026-11-08-page-scripts.md):
// QuickJS-NG in WasmVM inside the engine, on the page's Lean DOM, with the Lean event loop
// deciding each callback. A scripted page: its scripts at start, a click found with nodeAt,
// a timer on the virtual clock, and a turn with no DOM change. The DOM text is read from the
// engine's own layout (selectedText with the session's commands), so the commands replay.
// Run on the Wasm engine and, when it is built, the native library; both give the same turns.
// Needs the guest module: QUICKJS_WASM, else ~/working/qjs-wasm/qjs-wasmvm.wasm, else the one
// fetch-builds installs (docs/web/hub/wasm-guests/). Run with --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";
// The turns run on BubblePopJS (the JavaScript engine written in Lean, WasmVM/Hosts/LeanJS.lean), with
// no guest module. QUICKJS-EXCEPTION: SCRIPT_ENGINE=quickjs runs the same turns on QuickJS-NG in WasmVM
// (needs the guest module), a differential test against BubblePopJS.
const lean=Deno.env.get("SCRIPT_ENGINE")!=="quickjs";
const withEngine=(request:Record<string,unknown>)=>({...request,engine:lean?"bubblepop":"quickjs"});

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=[Deno.env.get("QUICKJS_WASM")??"",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`,
  decodeURIComponent(new URL("../../../docs/web/hub/wasm-guests/qjs-wasmvm.wasm",import.meta.url).pathname)].find(exists);

const page=`<!doctype html><html><head><title>Scripted</title>
<style>body{margin:0}#go{display:block;width:400px;height:120px;margin:0;font-size:40px}</style></head><body>
<button id=go>Go</button><p id=out>before</p><ul id=list></ul>
<script>
const out = document.getElementById('out'), list = document.getElementById('list');
let clicks = 0;
out.textContent = 'scripts ran';
document.getElementById('go').addEventListener('click', e => {
  clicks++;
  out.textContent = 'clicked ' + clicks + ' ' + e.type + ' ' + e.target.id;
  const li = document.createElement('li'); li.textContent = 'item ' + clicks; list.appendChild(li);
  Promise.resolve().then(() => console.log('microtask after click ' + clicks));
});
setTimeout(() => { out.textContent += ' and the timer fired at ' + Date.now(); }, 50);
console.log('loaded at ' + Date.now());
</script></body></html>`;

/** The page text as the engine lays it out with the session's commands. */
const text=(engine:HTMLEngine,commands:unknown[])=>engine.selectedText(page,800,600,{url:"file:///scripted.html",selection:"all",commands});

async function runs(engine:HTMLEngine){
  const info=engine.scriptInfo();
  assert(info.ops.includes("start")&&info.ops.includes("click"));
  if(!lean)engine.scriptLoad(await Deno.readFile(guest!));
  const turns:ScriptTurn[]=[];
  // Start: the script runs in document order; the timer is armed, not fired.
  // The script clock runs at a rate so high that script time stays 0 here: this test is of
  // the event loop's clock (native_html_pointer_test.ts tests script time).
  let turn=engine.scriptSession(page,withEngine({action:"start",url:"file:///scripted.html",resources:[],instructionsPerMs:1e12}));turns.push(turn);
  assert.equal(turn.changed,true);
  assert.deepEqual(turn.logs,["loaded at 0"]);
  assert.equal(turn.timers,1);
  assert.equal(turn.nextWake,50);
  let commands=turn.commands!;
  assert.match(text(engine,commands),/scripts ran/);
  // A click: Lean finds the button under the point, then dispatches the click.
  const node=engine.nodeAt(page,800,600,{url:"file:///scripted.html",commands,x:30,y:30});
  assert.equal(typeof node,"number");
  turn=engine.scriptSession("",{action:"click",session:turn.session,node});turns.push(turn);
  assert.equal(turn.changed,true);
  assert.deepEqual(turn.logs,["microtask after click 1"]);
  commands=turn.commands!;
  assert.match(text(engine,commands),/clicked 1 click go/);
  assert.match(text(engine,commands),/item 1/);
  // Time: 49 ms is before the timer, so nothing runs and the DOM does not change. No change
  // means no commands in the answer, and a host lays nothing out.
  turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:49});turns.push(turn);
  assert.equal(turn.changed,false);
  assert.equal(turn.commands,undefined);
  assert.equal(turn.clock,49);
  turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:10});turns.push(turn);
  assert.equal(turn.changed,true);
  assert.equal(turn.timers,0);
  commands=turn.commands!;
  assert.match(text(engine,commands),/and the timer fired at 50/);
  // A second click on the same session.
  turn=engine.scriptSession("",{action:"click",session:turn.session,node});turns.push(turn);
  assert.match(text(engine,turn.commands!),/clicked 2 click go.*item 1.*item 2/s);
  // Settle: nothing waits.
  turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:1000});turns.push(turn);
  assert.equal(turn.quiet,true);
  assert.equal(turn.changed,false);
  engine.scriptSession("",{action:"close"});
  // The script clock (Page.ScriptClock) at its default rate, 100 000 instructions a ms: a
  // busy loop moves performance.now(); readings never go back; a timer set after the
  // loop is due its delay after the script time it was set at.
  const busy=`<!doctype html><title>Busy</title><script>
const t0 = performance.now(), d0 = Date.now(); let x = 0; for (let i = 0; i < 300000; i++) x += i;
const t1 = performance.now();
console.log('ran ' + (t1 - t0 >= 1) + ' ' + (Date.now() >= d0));
setTimeout(() => console.log('timer after ' + (performance.now() - t1 >= 10)), 10);
</script>`;
  let clock=engine.scriptSession(busy,withEngine({action:"start",url:"file:///busy.html",resources:[]}));turns.push(clock);
  assert.deepEqual(clock.logs,["ran true true"]);
  assert.ok(clock.clock>=1,"the loop's clock moved up to script time");
  clock=engine.scriptSession("",{action:"settle",session:clock.session,budgetMs:1000});turns.push(clock);
  assert.deepEqual(clock.logs,["timer after true"]);
  engine.scriptSession("",{action:"close"});
  return turns.map(({ns:_,instructions:__,...t})=>t);
}

Deno.test({name:"Lean runs a scripted page: clicks and timers change the DOM (Wasm)",ignore:!lean&&!guest,fn:async()=>{
  const engine=await loadHTML();
  try{engine.scriptInfo();}catch{console.log("NOT RUN: this Wasm engine has no scriptSession");return;}
  await runs(engine);
}});
Deno.test({name:"Lean runs a scripted page (native library), with the turns of the Wasm engine",ignore:(!lean&&!guest)||!exists(library),fn:async()=>{
  const native=await runs(await loadHTML(library));
  const wasm=await loadHTML();
  try{wasm.scriptInfo();}catch{console.log("native only: this Wasm engine has no scriptSession");return;}
  assert.equal(JSON.stringify(native),JSON.stringify(await runs(wasm)));
}});
