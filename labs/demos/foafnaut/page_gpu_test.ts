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
// SCRIPT_ENGINE=bubblepop runs the same turns on BubblePopJS (the JavaScript engine written in Lean) (WasmVM/Hosts/LeanJS.lean):
// the start requests carry engine:"bubblepop", and no guest module is needed.
const lean=Deno.env.get("SCRIPT_ENGINE")==="bubblepop";
const withEngine=(request:Record<string,unknown>)=>lean?{...request,engine:"bubblepop"}:request;

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const guest=Deno.env.get("QUICKJS_WASM")??`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`;
const page=await Deno.readTextFile(new URL("./pages/webgpu-triangle.html",import.meta.url));
const url="file:///webgpu-triangle.html";

type Gpu={k:string;g?:[number,number];[k:string]:unknown};
type Turn={session:number;gpuPage?:number;gpu?:Gpu[];logs:string[];errors:string[];commands?:unknown[];nextWake:number|null};

const engine=await loadHTML(library);
if(!lean)engine.scriptLoad(await Deno.readFile(guest));
let turn=engine.scriptSession(page,withEngine({action:"start",url,resources:[]})) as unknown as Turn;
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

// WebGL 1 and 2 (PageGpu.Glsl): both programs link (Lean answers attribute locations), each
// canvas gets its own frames, and the shaders the host gets are Lean's WGSL.
{
  const gl=await Deno.readTextFile(new URL("./pages/webgl-triangle.html",import.meta.url));
  const glURL="file:///webgl-triangle.html";
  let t=engine.scriptSession(gl,withEngine({action:"start",url:glURL,resources:[]})) as unknown as Turn;
  const got:Gpu[]=[...(t.gpu??[])];let glCommands=t.commands;
  for(let i=0;i<12;i++){
    t=engine.scriptSession("",{action:"advance",session:t.session,ms:20}) as unknown as Turn;
    got.push(...(t.gpu??[]));if(t.commands)glCommands=t.commands;
    for(const l of t.logs)assert(!l.startsWith("WebGL:"),l);
    for(const e of t.errors)assert.fail("page error: "+e);
  }
  const canvases=got.filter(c=>c.k==="canvas").map(c=>c.g![1]);
  assert.equal(canvases.length,2);
  const shaders=got.filter(c=>c.k==="shader").map(c=>c.code as string);
  assert.equal(shaders.length,2);
  for(const code of shaders)assert.match(code,/@vertex fn vs\(/);
  const passCanvases=new Set(got.filter(c=>c.k==="pass").map(c=>(c.canvas as number[])[1]));
  assert.deepEqual([...passCanvases].sort(),canvases.sort());
  const glText=engine.selectedText(gl,800,1200,{url:glURL,selection:"all",commands:glCommands});
  assert.match(glText,/Drawing with WebGL 2\.0/);assert.match(glText,/Drawing with WebGL 1\.0/);
  console.log("webgl: 2 canvases,",got.filter(c=>c.k==="pass").length,"passes; programs linked");
}
console.log("page_gpu_test (webgl): ok");

// Compute (docs/designissues/2026-11-14-gpu-compute-and-webnn.md): the force-graph page makes
// compute pipelines and bind groups through Lean, dispatches every frame, has its dispatch of
// 70,000 workgroups refused, and reads the nodes back: the test plays the host, answering the
// readback (action gpuRead) with bytes of the size Lean asked for, and the page's promise
// resolves with them in a later task.
{
  const fg=await Deno.readTextFile(new URL("./pages/webgpu-force-graph.html",import.meta.url));
  const fgURL="file:///webgpu-force-graph.html";
  let t=engine.scriptSession(fg,withEngine({action:"start",url:fgURL,resources:[]})) as unknown as Turn;
  const got:Gpu[]=[...(t.gpu??[])];let fgCommands=t.commands;
  let read:Gpu|undefined;
  for(let i=0;i<200&&!read;i++){
    t=engine.scriptSession("",{action:"advance",session:t.session,ms:20}) as unknown as Turn;
    got.push(...(t.gpu??[]));if(t.commands)fgCommands=t.commands;
    for(const e of t.errors)assert.fail("page error: "+e);
    read=(t.gpu??[]).find(c=>c.k==="read");
  }
  const kinds=got.map(c=>c.k);
  for(const k of ["cpipeline","cbind","cpass","copy","read","pipeline","pass"])assert(kinds.includes(k),`no ${k} command`);
  const cp=got.find(c=>c.k==="cpipeline")!;
  assert.deepEqual(cp.layout,[[0,"uniform"],[1,"read-only-storage"],[2,"storage"],[3,"read-only-storage"]]);
  const shaders=got.filter(c=>c.k==="shader").map(c=>c.code as string);
  assert(shaders.some(s=>s.includes("src[min(u32(i), (arrayLength(&src) - 1u))]")),"runtime-sized index clamped");
  for(const c of got.filter(c=>c.k==="cpass"))for(const d of c.dispatches as {x:number}[])assert(d.x<=65535);
  assert(read&&read.size===16000,"a readback of the 1,000 nodes");
  const bytes=new Float32Array(4000);for(let i=0;i<1000;i++){bytes[4*i]=0.5;bytes[4*i+2]=0.01;}
  const b64=btoa(String.fromCharCode(...new Uint8Array(bytes.buffer)));
  t=engine.scriptSession("",{action:"gpuRead",session:t.session,results:[{ticket:read!.ticket,dataBase64:b64}]}) as unknown as Turn;
  if(t.commands)fgCommands=t.commands;
  for(let i=0;i<3;i++){t=engine.scriptSession("",{action:"advance",session:t.session,ms:20}) as unknown as Turn;if(t.commands)fgCommands=t.commands;}
  const fgText=engine.selectedText(fg,800,1400,{url:fgURL,selection:"all",commands:fgCommands});
  assert.match(fgText,/Refused a dispatch of 70,000 workgroups: gpu:/);
  assert.match(fgText,/Read back at frame 60: extent 0\.50, mean speed 0\.0100/);
  console.log("compute:",kinds.filter(k=>k==="cpass").length,"compute passes; readback answered");
}
console.log("page_gpu_test (compute): ok");
