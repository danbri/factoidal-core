// Page input and layout reads of scripts run by Lean (WebScripts.lean, WebHit.lean,
// WasmVM/Hosts/Page.lean; record docs/designissues/2026-11-08-page-scripts.md):
// - a tap on a shape inside an inline SVG targets the shape (nodeAt hit-tests the SVG scene),
//   and the event path goes through the SVG elements;
// - pointer and mouse events carry client, page and offset coordinates, buttons and the
//   pointer type; a release clicks; at most one pointermove in a frame;
// - innerWidth/innerHeight are the viewport; clientWidth, getBoundingClientRect and getBBox
//   come from Lean's layout of the current DOM, laid out once until the DOM changes;
//   resize fires `resize`;
// - performance.now() moves with the instructions a script runs, at the stated rate.
// Run on the native engine library and the Wasm engine when built, with the guest module
// (QUICKJS_WASM, else ~/working/qjs-wasm/qjs-wasmvm.wasm). Run with --allow-read --allow-ffi --allow-env.
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

const url="file:///pointer.html";
const page=`<!doctype html><html><head><title>Pointer</title><style>body{margin:0}</style></head><body>
<div id=box style="width:301px;height:50px;border:2px solid black"></div>
<svg id=s width="200" height="100" style="display:block"><g id=g><circle id=c cx="50" cy="50" r="40"/></g>
<rect id=r x="120" y="10" width="60" height="30" transform="translate(10 0)"/></svg>
<script>
for (const t of ['pointerdown','mousedown','pointerup','mouseup','click','pointermove','mousemove','pointercancel'])
  document.addEventListener(t, e => console.log(t + ' ' + e.target.id + ' ' + e.composedPath().map(n => n.id).filter(x => x).sort().join('<') +
    ' client ' + e.clientX + ',' + e.clientY + ' offset ' + e.offsetX + ',' + e.offsetY + ' page ' + e.pageX + ',' + e.pageY +
    ' ' + e.button + '/' + e.buttons + (e instanceof PointerEvent ? ' ' + e.pointerType : '')));
const b = document.getElementById('box');
console.log('viewport ' + innerWidth + 'x' + innerHeight);
const r = b.getBoundingClientRect();
console.log('box ' + b.clientWidth + 'x' + b.clientHeight + ' offset ' + b.offsetWidth + 'x' + b.offsetHeight + ' rect ' + [r.x, r.y, r.width, r.height].join(','));
const bb = document.getElementById('r').getBBox();
console.log('bbox ' + [bb.x, bb.y, bb.width, bb.height].join(','));
const cr = document.getElementById('c').getBoundingClientRect();
console.log('circle ' + [cr.x, cr.y, cr.width, cr.height].join(','));
const t0 = performance.now(); let x = 0; for (let i = 0; i < 300000; i++) x += i;
console.log('busy ' + (performance.now() - t0 >= 1));
addEventListener('resize', () => console.log('resize ' + innerWidth + 'x' + innerHeight));
</script></body></html>`;

async function runs(engine:HTMLEngine){
  const info=engine.scriptInfo();
  assert.ok(info.ops.includes("pointer")&&info.ops.includes("resize"));
  if(!lean)engine.scriptLoad(await Deno.readFile(guest!));
  const lines:string[]=[];
  let turn=engine.scriptSession(page,withEngine({action:"start",url,resources:[],width:400,height:300,layout:{url}}));
  lines.push(...turn.logs);
  assert.deepEqual(turn.errors,[]);
  assert.ok(turn.logs.includes("viewport 400x300"),turn.logs.join("\n"));
  // The border box is 305 by 54; the client box is inside the 2px borders.
  assert.ok(turn.logs.includes("box 301x50 offset 305x54 rect 0,0,305,54"),turn.logs.join("\n"));
  // getBBox is in the element's user space: its own transform is not applied.
  assert.ok(turn.logs.includes("bbox 120,10,60,30"),turn.logs.join("\n"));
  assert.ok(turn.logs.includes("circle 10,64,80,80"),turn.logs.join("\n"));
  assert.ok(turn.logs.includes("busy true"),turn.logs.join("\n"));
  // Reads after no write share one layout.
  assert.equal((turn as ScriptTurn&{layouts:number}).layouts,1);
  const commands=turn.commands!;
  const at=(x:number,y:number)=>engine.pointerAt(page,400,300,{url,commands,x,y});
  // The circle is at (50,104) in the page: the tap targets the circle, through g and svg.
  const hit=at(50,104);
  const pointer=(kind:string,where:Record<string,unknown>,buttons:number)=>{
    turn=engine.scriptSession("",{action:"pointer",session:turn.session,kind,...where,button:0,buttons,pointerType:"touch"});
    lines.push(...turn.logs);
    return turn.logs;
  };
  assert.deepEqual(pointer("down",hit,1),[
    "pointerdown c c<g<s client 50,104 offset 50,50 page 50,104 0/1 touch",
    "mousedown c c<g<s client 50,104 offset 50,50 page 50,104 0/1"]);
  // Two moves in one frame: one pointermove now, the second waits for the next frame.
  assert.equal(pointer("move",at(60,104),1).filter(l=>l.startsWith("pointermove")).length,1);
  assert.equal(pointer("move",at(70,104),1).length,0);
  assert.equal(typeof turn.nextWake,"number");
  turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:16});lines.push(...turn.logs);
  assert.ok(turn.logs.some(l=>l.startsWith("pointermove c c<g<s client 70,104")),turn.logs.join("\n"));
  // Release on the svg outside the circle: up there, and the click at the common ancestor.
  const logs=pointer("up",at(150,104),0);
  assert.equal(logs[0],"pointerup s s client 150,104 offset 150,50 page 150,104 0/0 touch");
  assert.ok(logs.some(l=>l.startsWith("click s ")),logs.join("\n"));
  // The empty part of the svg targets the svg; the rect, with its transform, the rect.
  const svg=at(110,150).node;
  assert.equal(typeof svg,"number");
  assert.equal(at(5,60).node,svg);
  assert.notEqual(at(140,74).node,svg);
  assert.notEqual(at(140,74).node,hit.node);
  // Resize: the viewport and the event.
  turn=engine.scriptSession("",{action:"resize",session:turn.session,width:500,height:300});
  assert.deepEqual(turn.logs,["resize 500x300"]);
  engine.scriptSession("",{action:"close"});
  return lines;
}

Deno.test({name:"Lean page input: SVG targets, pointer events, layout reads, script clock (native library)",
  ignore:(!lean&&!guest)||!exists(library),fn:async()=>{
  const native=await runs(await loadHTML(library));
  const wasm=await loadHTML();
  let ops:string[]=[];
  try{ops=wasm.scriptInfo().ops;}catch{/* no scriptSession */}
  if(!ops.includes("pointer")){console.log("native only: this Wasm engine has no pointer action");return;}
  assert.deepEqual(native,await runs(wasm));
}});
