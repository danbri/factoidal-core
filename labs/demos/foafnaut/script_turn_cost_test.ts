// The cost of a script turn that writes and reads styles, on a page with animation rules
// (WebDocument.measure op 28, the elements that declare an animation; WasmVM/Hosts/Page.lean
// Host.measureNow). Until 2026-11-15 each element of op 28 read the keys of every element of
// the document again (a closure kept in a thunk was compiled with the key table made at each
// call), so the read after a write cost n² in the size of the page: one timer turn of a
// Wikipedia article (about 70,000 instructions) took 64 s. This page is an original construct
// with the same pattern: many elements with classes, a few animation and transition rules,
// and a timer that writes a class and reads a computed style and a size, again and again.
// The turn at four times the elements must take less than eight times as long (linear is
// four, the old cost sixteen), and the turn reports its reads at the boundary (reads, readOps,
// layouts) so a host can see which reads a slow turn made.
// Needs the native library (build-web-render.sh --native); the Wasm engine too when it is built.
// Run: deno test --allow-read --allow-ffi --allow-env script_turn_cost_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

/** The page: `n` elements in sections, animation and transition rules, and a timer that makes
 * `rounds` writes, each followed by a computed-style read and a size read. */
export function page(n:number,rounds:number){
  const items=Array.from({length:n},(_,i)=>`<li class="item k${i%7}${i%11===0?" pulse":""}"><span class="label">Item ${i}</span></li>`).join("");
  return `<!doctype html><html><head><style>
@keyframes pulse{from{opacity:1}to{opacity:.5}}
.pulse{animation:pulse 2s infinite alternate}
.item{color:#222;transition:color .2s}
.item.on{color:#a00}
.k3 .label{font-weight:bold}
</style></head><body><ul id="list">${items}</ul><p id="out"></p><script>
setTimeout(()=>{
  const list=document.getElementById('list');
  let total=0;
  for(let r=0;r<${rounds};r++){
    const el=list.children[(r*37)%list.children.length];
    el.classList.toggle('on');
    total+=getComputedStyle(el).color.length+el.offsetWidth;
  }
  document.getElementById('out').textContent='done '+total;
},10);
</script></body></html>`;
}

type Turn=ScriptTurn&{reads?:number;readOps?:string;layouts?:number;logs:string[];errors:string[]};
/** The timer turn of the page on `engine`: its time in ms, and the turn. */
function timerTurn(engine:HTMLEngine,n:number,rounds:number){
  const url="http://example.test/turns.html";
  const start={action:"start",url,resources:[],instructionsPerMs:1e12,engine:"bubblepop",layout:{url},width:800,height:600};
  const first=engine.scriptSession(page(n,rounds),start) as Turn;
  assert.deepEqual(first.errors,[],"page errors at start");
  const t0=performance.now();
  const turn=engine.scriptSession("",{action:"advance",session:first.session,ms:50}) as Turn;
  const ms=performance.now()-t0;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(turn.errors,[],"page errors in the timer turn");
  return {ms,turn};
}

async function check(engine:HTMLEngine,label:string){
  const info=engine.scriptInfo();
  if(!(info.engines??[]).includes("bubblepop")){console.log(`NOT RUN (${label}): this engine has no BubblePopJS`);return;}
  timerTurn(engine,50,4); // warm the engine
  const small=timerTurn(engine,300,30),large=timerTurn(engine,1200,30);
  assert.equal(typeof large.turn.reads,"number",`${label}: the turn reports no reads`);
  assert.ok(large.turn.reads!>=60,`${label}: ${large.turn.reads} reads for 30 rounds of two reads`);
  assert.match(large.turn.readOps??"",/\d+:\d+/,`${label}: no reads by op`);
  assert.ok(large.turn.layouts!>=1&&large.turn.layouts!<=31,`${label}: ${large.turn.layouts} layouts for 30 writes`);
  const ratio=large.ms/Math.max(1,small.ms);
  console.log(`${label}: 300 elements ${small.ms.toFixed(0)} ms, 1200 elements ${large.ms.toFixed(0)} ms (x${ratio.toFixed(1)}); reads ${large.turn.reads} (${large.turn.readOps}), layouts ${large.turn.layouts}`);
  assert.ok(ratio<8,`${label}: the turn grows faster than the page (x${ratio.toFixed(1)} for 4 times the elements)`);
}

Deno.test({name:"A script turn that writes and reads styles costs in proportion to the page (native library)",ignore:!exists(library),fn:async()=>{
  await check(await loadHTML(library),"native");
}});
