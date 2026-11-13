// Page script speed: BubblePopJS (the JavaScript engine written in Lean) (WasmVM/Hosts/LeanJS.lean) against QuickJS-NG
// in WasmVM, on the scripts of hub_scripts_speed.mjs, in the native engine library and, when it
// is built, the Wasm engine (the interpreter path; the Hub's translated QuickJS needs a browser,
// hub_scripts_speed.mjs measures it). Times are the engine's own (`ns` of each turn).
// - start-up: the first start turn of a page with one empty script (the realm with the page
//   objects is made then), and a later one (made once, copied);
// - fib(24): the start turn of a page whose script computes fib(24);
// - a WPT page start: dom/nodes/Node-appendChild.html with testharness.js;
// - a frame of timers-and-clicks.html: an advance turn of 16 ms, mean and largest over 3 s.
//   deno run --allow-read --allow-ffi --allow-env bubblepop_bench.ts [--wasm] [--runs N]
// QUICKJS-EXCEPTION: QuickJS-NG timed beside BubblePopJS for comparison.
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=[Deno.env.get("QUICKJS_WASM")??"",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`,
  decodeURIComponent(new URL("../../../docs/web/hub/wasm-guests/qjs-wasmvm.wasm",import.meta.url).pathname)].find(exists);
const wpt=new URL("../../../third_party/testing/wpt-scripting/",import.meta.url);
const runs=Number(Deno.args[Deno.args.indexOf("--runs")+1]||3);
const ms=(ns:number)=>Math.round(ns/1e4)/100;
type Turn={session:number;ns:number;instructions:number;errors:string[];logs:string[]};

const empty="<!doctype html><title>start</title><script>1</script>";
const fib='<!doctype html><html><head><meta charset="utf-8"><title>fib(24)</title></head><body><p id="out">...</p>'+
  '<script>function fib(n){return n<2?n:fib(n-1)+fib(n-2);}document.getElementById("out").textContent="fib(24) = "+fib(24);</script></body></html>';
const timers=await Deno.readTextFile(new URL("./pages/timers-and-clicks.html",import.meta.url));
const wptPage=await Deno.readTextFile(new URL("dom/nodes/Node-appendChild.html",wpt));
const harness=[await Deno.readTextFile(new URL("resources/testharness.js",wpt)),
  await Deno.readTextFile(new URL("../../../tests/browser-wpt/testharnessreport.js",import.meta.url))];

function bench(engine:HTMLEngine,lean:boolean){
  const extra={engine:lean?"bubblepop":"quickjs"};
  const start=(source:string,url:string,resources:unknown[]=[])=>
    engine.scriptSession(source,{action:"start",url,resources,instructionsPerMs:1e12,...extra}) as unknown as Turn;
  const first=start(empty,"file:///start.html");
  const later=Math.min(...Array.from({length:runs},()=>start(empty,"file:///start.html").ns));
  const fibs=Array.from({length:runs},()=>{const t=start(fib,"file:///fib.html");if(t.errors.length)throw new Error(t.errors[0]);return t.ns;});
  const facts=engine.inspect(wptPage,{url:"http://web-platform.test/dom/nodes/Node-appendChild.html"}) as unknown as {scripts:{nodeId:number;src:string}[]};
  const resources=facts.scripts.filter(s=>s.src).slice(0,2).map((s,i)=>({nodeId:s.nodeId,source:harness[i]}));
  const wpts=Array.from({length:runs},()=>start(wptPage,"http://web-platform.test/dom/nodes/Node-appendChild.html",resources).ns);
  const t=start(timers,"file:///timers-and-clicks.html");
  const frames:number[]=[];
  for(let i=0;i<Math.round(3000/16);i++){
    const turn=engine.scriptSession("",{action:"advance",session:t.session,ms:16}) as unknown as Turn;
    if(turn.errors.length)throw new Error(turn.errors[0]);
    frames.push(turn.ns);
  }
  engine.scriptSession("",{action:"close"});
  return {startFirstMs:ms(first.ns),startMs:ms(later),fib24Ms:ms(Math.min(...fibs)),wptStartMs:ms(Math.min(...wpts)),
    frameMeanMs:ms(frames.reduce((a,b)=>a+b,0)/frames.length),frameMaxMs:ms(Math.max(...frames)),frames:frames.length};
}

const out:Record<string,unknown>={};
const kinds=Deno.args.includes("--wasm")?[["wasm",undefined],["native",library]]:[["native",library]];
for(const [kind,lib] of kinds){
  if(kind==="native"&&!exists(library)){console.log("NOT RUN: no native library");continue;}
  const engine=await loadHTML(lib);
  const info=engine.scriptInfo();
  if((info.engines??[]).includes("bubblepop"))out[`${kind} BubblePopJS`]=bench(engine,true);
  if(guest){
    const bytes=await Deno.readFile(guest),t0=performance.now();
    engine.scriptLoad(bytes);
    // QuickJS makes its realm (the prelude) when the module loads, before any page.
    out[`${kind} QuickJS-NG in WasmVM`]={loadMs:Math.round((performance.now()-t0)*100)/100,...bench(engine,false)};
  }
}
console.log(JSON.stringify(out,null,1));
