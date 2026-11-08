// Page GPU commands (docs/designissues/2026-11-08-page-gpu.md): the demo page
// pages/webgpu-triangle.html runs in QuickJS in WasmVM inside the engine; each WebGPU call is
// a gpu_command import that Lean (L4Factoidal.PageGpu) validates. A turn carries the host
// commands Lean emitted ("gpu"); a render with layers gives the canvas rectangle and Lean's
// blit WGSL. Checks: the setup commands, a refused write past a buffer, a frame per about
// 41 ms of virtual time, the hardened shader text, and the canvas rectangle.
// Needs the native library (build-web-render.sh --native) and a guest built from this
// prelude: QUICKJS_WASM, else ~/working/qjs-wasm/qjs-wasmvm.wasm.
// Run: deno run --allow-read --allow-ffi --allow-env page_gpu_test.ts
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const guest=Deno.env.get("QUICKJS_WASM")??`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`;
const page=await Deno.readTextFile(new URL("./pages/webgpu-triangle.html",import.meta.url));
const url="file:///webgpu-triangle.html";

type Gpu={k:string;g?:[number,number];[k:string]:unknown};
type Turn={session:number;gpuPage?:number;gpu?:Gpu[];logs:string[];errors:string[];commands?:unknown[];nextWake:number|null};

const engine=await loadHTML(library);
engine.scriptLoad(await Deno.readFile(guest));
let turn=engine.scriptSession(page,{action:"start",url,resources:[]}) as unknown as Turn;
const all:Gpu[]=[...(turn.gpu??[])];
const pages=new Set<number>();if(turn.gpuPage!==undefined)pages.add(turn.gpuPage);
let commands=turn.commands;
// The script awaits promises (adapter, device, error scopes); its frames come with time.
for(let i=0;i<12;i++){
  turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:20}) as unknown as Turn;
  all.push(...(turn.gpu??[]));
  if(turn.gpuPage!==undefined)pages.add(turn.gpuPage);
  if(turn.commands)commands=turn.commands;
  for(const e of turn.errors)console.log("page error:",e);
  for(const l of turn.logs)assert(!l.startsWith("WebGPU:"),l);
}
const kinds=all.map(c=>c.k);
console.log("gpu kinds:",kinds.slice(0,12).join(" "),"...",kinds.length,"commands");
for(const k of ["canvas","buffer","clear","write","shader","pipeline","bind","pass"])assert(kinds.includes(k),`no ${k} command`);
// Every command is of this page session, numbered by its session.
assert.deepEqual([...pages],[turn.session]);
for(const c of all)if(c.g)assert.equal(c.g[0],turn.session);
// No refusal reached the console: the page's own refused write is caught by its error scope.

// A buffer is cleared right after it is made.
kinds.forEach((k,i)=>{if(k==="buffer")assert.equal(kinds[i+1],"clear");});
// The shader the host gets is Lean's printing of the hardened module.
const shader=all.find(c=>c.k==="shader")!.code as string;
assert.match(shader,/@vertex fn vs\(/);
// About 24 frames a second: 240 ms of virtual time gives a handful of passes, not 15.
const passes=kinds.filter(k=>k==="pass").length;
console.log("passes in 240 ms:",passes);
assert(passes>=3&&passes<=8,`passes ${passes}`);
// The refused write (past the uniform buffer) reached the page as an error; nothing was emitted for it.
assert(!all.some(c=>c.k==="write"&&c.offset===8));
const text=engine.selectedText(page,800,900,{url,selection:"all",commands});
assert.match(text,/Lean refused a write past a buffer: gpu: writeBuffer: out of range/);
// The render with layers: the canvas box and the blit shader.
const shell={tabs:[{title:""}],active:0,address:"",cursor:0,anchor:0,focused:false,canBack:false,canForward:false,
  loading:false,scale:1,theme:"next",pages:1,scroll:0,collapsible:false,collapse:0};
const layers=engine.compileLayers(page,800,900,{url,commands,shell,checks:false});
const place=layers.layers as unknown as {canvases?:{node:number;rect:number[];clip:number[]}[];canvasBlit?:string};
assert(place.canvases?.length===1,"one canvas rectangle");
const canvasNode=all.find(c=>c.k==="canvas")!.node;
assert.equal(place.canvases![0].node,canvasNode);
console.log("canvas rect:",place.canvases![0].rect,"clip:",place.canvases![0].clip);
assert.equal(place.canvases![0].rect[2],362); // 360 plus the 1px border box each side
assert.match(place.canvasBlit!,/textureLoad/);
console.log("page_gpu_test: ok");
