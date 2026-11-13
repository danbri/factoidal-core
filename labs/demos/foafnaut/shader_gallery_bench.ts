// Frame cost of pages/shader-gallery.html in the native engine (docs/designissues/2026-11-08-page-gpu.md):
// each shader, on WebGPU (WGSL) and WebGL 2 (GLSL ES 3.00), at the sizes asked for. A frame is one
// script turn (the page's requestAnimationFrame callback) on the virtual clock, 16 ms apart, then the
// host's replay of the GPU commands Lean emitted, on this machine's GPU (Deno's WebGPU), into the page
// canvas texture. Per frame it reports: the turn's wall time (the engine call), Lean's own ns for the
// turn (turn.ns), the replay's CPU time, the GPU time of the pass (to onSubmittedWorkDone), and
// whether the turn changed the DOM (a layout). Totals: the engine's share (turn + replay) and the
// frame time and fps these allow.
// Run: deno run --allow-read --allow-write --allow-ffi --allow-env shader_gallery_bench.ts
//   [--engine DYLIB] [--guest WASM] [--frames N] [--sizes 800x600,1600x1000] [--shaders a,b] [--apis webgpu,webgl2]
//   [--json FILE] [--png DIR]   (BubblePopJS; QUICKJS-EXCEPTION: SCRIPT_ENGINE=quickjs for QuickJS-NG in WasmVM, to compare)
// --png DIR writes the last frame of each run (the page canvas, read back here, not by the page).
import {loadHTML} from "./native_html_engine.ts";
import {pngOf,texturePixels} from "./png_write.ts";
// @ts-ignore plain module
import {createPageGpu} from "../../../docs/web/hub/foafnaut/page-gpu.mjs";
const arg=(name:string,fallback:string)=>{const i=Deno.args.indexOf(name);return i>=0?Deno.args[i+1]:fallback;};
const lean=Deno.env.get("SCRIPT_ENGINE")!=="quickjs";
const library=arg("--engine",new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname);
const guest=arg("--guest",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`);
const frames=Number(arg("--frames","60"));
const sizes=arg("--sizes","800x600,1600x1000").split(",");
const shaders=arg("--shaders","plasma,marble,spheres,seahorse,eleven").split(",");
const apis=arg("--apis","webgpu,webgl2").split(",");
const pngDir=arg("--png","");
const page=await Deno.readTextFile(new URL("./pages/shader-gallery.html",import.meta.url));
type Turn={session:number;clock:number;changed:boolean;gpu?:{k:string;[k:string]:unknown}[];gpuPage?:number;logs:string[];errors:string[];
  instructions:number;ns:number;nextWake:number|null;commandCount:number};
const engine=await loadHTML(library);
if(!lean)engine.scriptLoad(await Deno.readFile(guest));
const adapter=await navigator.gpu.requestAdapter();
const realDevice=await adapter!.requestDevice();
// For --png only: the page canvas textures the replay makes, with COPY_SRC added here (the
// bench reads them back; Lean never gives a page canvas COPY_SRC).
const made:GPUTexture[]=[];
const device=new Proxy(realDevice,{get(target,key){
  if(key==="createTexture")return (d:GPUTextureDescriptor)=>{const t=target.createTexture(pngDir?{...d,usage:d.usage|GPUTextureUsage.COPY_SRC}:d);made.push(t);return t;};
  const v=Reflect.get(target,key,target);return typeof v==="function"?v.bind(target):v;}}) as GPUDevice;

const median=(xs:number[])=>{const s=[...xs].sort((a,b)=>a-b);return s.length?s[s.length>>1]:0;};
const p95=(xs:number[])=>{const s=[...xs].sort((a,b)=>a-b);return s.length?s[Math.min(s.length-1,Math.floor(s.length*0.95))]:0;};
const r2=(x:number)=>Math.round(x*100)/100;
const rows:Record<string,unknown>[]=[];
for(const size of sizes)for(const api of apis)for(const shader of shaders){
  const url=`file:///shader-gallery.html?shader=${shader}&api=${api}&size=${size}&readout=0`;
  const t0=performance.now();
  let turn=engine.scriptSession(page,{action:"start",url,resources:[],engine:lean?"bubblepop":"quickjs"}) as unknown as Turn;
  const startMs=performance.now()-t0;
  const gpu=createPageGpu(device);
  const replay=async(t:Turn)=>{if(t.gpu?.length){await gpu.replay(t.gpuPage,t.gpu);}};
  await replay(turn);
  const errors:string[]=[...turn.errors];
  // Settle: the start's promises (adapter, device, error scopes) and the first frame.
  let setup=0;
  for(let i=0;i<20&&!(turn.gpu??[]).some(c=>c.k==="pass");i++){
    const s=performance.now();
    turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:16}) as unknown as Turn;
    setup+=performance.now()-s;errors.push(...turn.errors);
    await replay(turn);
  }
  await device.queue.onSubmittedWorkDone();
  const turnMs:number[]=[],leanMs:number[]=[],replayMs:number[]=[],instr:number[]=[],kinds=new Map<string,number>();
  let changed=0,passes=0,jsonBytes=0,lastPass:unknown;
  for(let f=0;f<frames;f++){
    const s=performance.now();
    turn=engine.scriptSession("",{action:"advance",session:turn.session,ms:16}) as unknown as Turn;
    const e=performance.now();
    errors.push(...turn.errors);
    turnMs.push(e-s);leanMs.push(turn.ns/1e6);instr.push(turn.instructions);
    if(turn.changed)changed++;
    for(const c of turn.gpu??[]){kinds.set(c.k,(kinds.get(c.k)??0)+1);if(c.k==="pass"){passes++;lastPass=c;}}
    jsonBytes+=JSON.stringify(turn.gpu??[]).length;
    const r0=performance.now();
    await replay(turn);
    replayMs.push(performance.now()-r0);
    await device.queue.onSubmittedWorkDone();
  }
  // GPU time of one pass: the frame's pass replayed 1 and 33 times, each to onSubmittedWorkDone
  // (whose own latency, about 13 ms in Deno, cancels in the difference).
  const gpuMs:number[]=[];
  if(lastPass)for(let k=0;k<3;k++){
    const t0=performance.now();await gpu.replay(turn.gpuPage,[lastPass]);await device.queue.onSubmittedWorkDone();
    const t1=performance.now();await gpu.replay(turn.gpuPage,Array(33).fill(lastPass));await device.queue.onSubmittedWorkDone();
    const t2=performance.now();gpuMs.push(Math.max(0,((t2-t1)-(t1-t0))/32));
  }
  const engineMs=median(turnMs)+median(replayMs);
  const frameMs=Math.max(1000/60,engineMs+median(gpuMs));
  const row={size,api,shader,engine:lean?"BubblePopJS":"QuickJS-NG",startMs:r2(startMs),setupMs:r2(setup),frames,passes,
    turnMs:r2(median(turnMs)),turnP95:r2(p95(turnMs)),leanMs:r2(median(leanMs)),instructions:median(instr),
    replayMs:r2(median(replayMs)),gpuMs:r2(median(gpuMs)),engineMs:r2(engineMs),fps:r2(1000/frameMs),
    domChanges:changed,gpuJsonBytesPerFrame:Math.round(jsonBytes/frames),kinds:Object.fromEntries(kinds),stats:gpu.stats,errors:errors.slice(0,3)};
  rows.push(row);
  console.log(JSON.stringify(row));
  if(pngDir){
    // The page canvas texture (the shader's canvas: the one of the page's size), read back here.
    const [w,h]=size.split("x").map(Number);
    const tex=made.find(t=>t.width===w&&t.height===h);
    if(tex)await Deno.writeFile(`${pngDir}/native-${api}-${shader}-${size}.png`,await pngOf(w,h,await texturePixels(realDevice,tex)));
  }
  made.length=0;
  gpu.close();
}
const out=arg("--json","");
if(out)await Deno.writeTextFile(out,JSON.stringify(rows,null,1));
