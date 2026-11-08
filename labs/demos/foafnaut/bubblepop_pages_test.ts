// The demo pages' scripts on BubblePopJS, the JavaScript engine written in Lean
// (WasmVM/Hosts/LeanJS.lean; record docs/designissues/2026-11-08-lean-js-engine.md,
// section 11): each page starts, runs its
// timers and frames for six seconds of virtual time, and takes a click on its first button
// with no page error. With the QuickJS guest module (QUICKJS_WASM, else
// ~/working/qjs-wasm/qjs-wasmvm.wasm) the same turns run on QuickJS-NG in WasmVM, and the two
// engines must make the same DOM commands, logs and page GPU commands: the same prelude, the
// same imports on the same arena, the same event loop. The script clock is as good as off
// (a trillion instructions a ms), so the two engines' instruction counts do not move time.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env bubblepop_pages_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=[Deno.env.get("QUICKJS_WASM")??"",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`,
  decodeURIComponent(new URL("../../../docs/web/hub/wasm-guests/qjs-wasmvm.wasm",import.meta.url).pathname)].find(exists);
const pages=["timers-and-clicks","foaf-explorer","showcase-dataviz-script","webgpu-triangle","webgl-triangle","js-status"];

type Turn=ScriptTurn&{gpu?:unknown[];engine?:string;changes:number};
/** A page's turns on one engine: start, six seconds of virtual time, a click, settle. */
function run(engine:HTMLEngine,name:string,source:string,lean:boolean){
  const url=`file:///${name}.html`;
  const extra=lean?{engine:"bubblepop"}:{};
  const turns:Turn[]=[];
  let turn=engine.scriptSession(source,{action:"start",url,resources:[],instructionsPerMs:1e12,full:true,...extra}) as Turn;turns.push(turn);
  const session=turn.session;
  turn=engine.scriptSession("",{action:"advance",session,ms:6000,full:true}) as Turn;turns.push(turn);
  // The first button of the page, found by Lean's layout as a host finds a click target.
  const at=engine.nodeAt(source,800,600,{url,commands:turn.commands??[],x:0,y:0});
  const buttons=[...source.matchAll(/<button/g)].length;
  if(buttons&&typeof at==="number"){
    turn=engine.scriptSession("",{action:"click",session,node:at,full:true}) as Turn;turns.push(turn);
  }
  turn=engine.scriptSession("",{action:"settle",session,budgetMs:500,full:true}) as Turn;turns.push(turn);
  engine.scriptSession("",{action:"close"});
  return turns;
}
// GPU object ids carry the session's page number (L4Factoidal.PageGpu.Gid.page): compared without it.
const essence=(turns:Turn[])=>turns.map(t=>({commands:t.commands,logs:t.logs,errors:t.errors,
  gpu:JSON.stringify(t.gpu??[]).replaceAll(`[${t.gpuPage},`,"[page,"),clock:t.clock,timers:t.timers,frames:t.frames}));

Deno.test({name:"The demo pages run on BubblePopJS (the JavaScript engine written in Lean), as on QuickJS-NG (native library)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const info=engine.scriptInfo();
  if(!(info.engines??[]).includes("bubblepop")){console.log("NOT RUN: this engine has no BubblePopJS");return;}
  const quickjs=guest?(engine.scriptLoad(await Deno.readFile(guest)),true):false;
  for(const name of pages){
    const source=await Deno.readTextFile(new URL(`./pages/${name}.html`,import.meta.url));
    const lean=run(engine,name,source,true);
    for(const t of lean)assert.deepEqual(t.errors,[],`${name}: page errors on BubblePopJS`);
    assert.ok(lean.at(-1)!.changes>0||name==="js-status",`${name}: the scripts changed nothing`);
    if(quickjs)assert.deepEqual(essence(lean),essence(run(engine,name,source,false)),`${name}: the engines differ`);
    console.log(`${name}: ${lean.length} turns, ${lean.at(-1)!.changes} changes${quickjs?", the same on QuickJS-NG":""}`);
  }
}});
