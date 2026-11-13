// The shader gallery (pages/shader-gallery.html) in the native engine, on the script engine of
// SCRIPT_ENGINE (bubblepop: BubblePopJS; else QuickJS-NG in WasmVM): every shader on WebGPU and on
// WebGL 2 draws a pass each frame with no page error and no DOM change; the WebGL programs reach
// the host as Lean's WGSL with GL's gl_FragCoord (gl_FragHeight), mod and atan2; a shader outside
// the subset is refused with Lean's reason; and the cost of a frame's turn stays under its ratchet
// (instructions of QuickJS-NG in WasmVM, a count that does not depend on the machine).
// Run: deno run --allow-read --allow-ffi --allow-env shader_gallery_test.ts [--engine DYLIB] [--guest WASM]
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";
const arg=(name:string,fallback:string)=>{const i=Deno.args.indexOf(name);return i>=0?Deno.args[i+1]:fallback;};
const lean=Deno.env.get("SCRIPT_ENGINE")==="bubblepop";
const library=arg("--engine",new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname);
const guest=arg("--guest",Deno.env.get("QUICKJS_WASM")??`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`);
type Gpu={k:string;[k:string]:unknown};
type Turn={session:number;changed:boolean;gpu?:Gpu[];logs:string[];errors:string[];instructions:number;ns:number};
const engine=await loadHTML(library);
if(!lean)engine.scriptLoad(await Deno.readFile(guest));
const start=(html:string,url:string)=>engine.scriptSession(html,{action:"start",url,resources:[],engine:lean?"bubblepop":"quickjs"}) as unknown as Turn;
const advance=(t:Turn,ms=16)=>engine.scriptSession("",{action:"advance",session:t.session,ms}) as unknown as Turn;
const page=await Deno.readTextFile(new URL("./pages/shader-gallery.html",import.meta.url));
// The ratchet: QuickJS-NG instructions of one frame's turn (a uniform write and a pass, or a
// WebGL draw). 2026-11-09: 286k (WebGPU) and 325k (WebGL) before the prelude's frame path,
// 118k and 112k after.
const RATCHET={webgpu:125000,webgl2:120000};
for(const api of ["webgpu","webgl2"] as const)for(const shader of ["plasma","marble","spheres","seahorse","eleven"]){
  let t=start(page,`file:///shader-gallery.html?shader=${shader}&api=${api}&size=640x400&readout=0`);
  const all:Gpu[]=[...(t.gpu??[])],errors=[...t.errors],logs=[...t.logs];
  for(let i=0;i<6;i++){t=advance(t);all.push(...(t.gpu??[]));errors.push(...t.errors);logs.push(...t.logs);}
  const frames:Turn[]=[];
  for(let i=0;i<8;i++){t=advance(t);frames.push(t);errors.push(...t.errors);logs.push(...t.logs);}
  assert.deepEqual(errors,[],`${api} ${shader}: page errors`);
  for(const l of logs)assert(!/WebGPU:|WebGL:|refused/.test(l),`${api} ${shader}: ${l}`);
  for(const f of frames){
    const kinds=(f.gpu??[]).map(c=>c.k);
    assert(kinds.includes("pass"),`${api} ${shader}: a frame with no pass (${kinds})`);
    assert(!f.changed,`${api} ${shader}: a frame changed the DOM (a layout)`);
  }
  const shaderText=all.find(c=>c.k==="shader")?.code as string;
  assert(shaderText,`${api} ${shader}: no shader reached the host`);
  if(api==="webgl2"){
    assert.match(shaderText,/let gl_FragCoord = vec4<f32>\(gl_FragPos\.x, \(gl_FragHeight - gl_FragPos\.y\)/,`${shader}: gl_FragCoord from the bottom`);
    if(shader==="eleven")assert.match(shaderText,/atan2\(d\.x, d\.y\)/);
    if(shader==="spheres")assert.match(shaderText,/floor\(\(\(floor\(p\.x\) \+ floor\(p\.z\)\) \/ 2\.0\)\)/);
  }
  const instr=frames.map(f=>f.instructions).sort((a,b)=>a-b)[frames.length>>1];
  const ms=frames.map(f=>f.ns/1e6).sort((a,b)=>a-b)[frames.length>>1];
  console.log(`${api} ${shader}: ${frames.length} frames drawn, turn ${ms.toFixed(2)} ms, ${instr} instructions`);
  if(!lean)assert(instr<=RATCHET[api],`${api} ${shader}: ${instr} instructions a frame, over the ratchet ${RATCHET[api]}`);
}
// Outside the subset: Lean's reason reaches the page (a GPUValidationError, a program's log).
const refusals=`<!doctype html><script>
// Promise chains, no await in a loop (BubblePopJS: 'yield in this position is not supported').
const head = 'struct U { t: f32 }\\n@group(0) @binding(0) var<uniform> u: U;\\n';
const bodies = ['@fragment fn fs() -> @location(0) vec4f { var i = 0; while (i < 4) { i += 1; } return vec4f(0.0); }',
  'fn wave(x: f32) -> f32 { return x; }',
  '@fragment fn fs() -> @location(0) vec4f { var x = 0.0; for (var b = 0; b < 10000; b++) { x += 1.0; } return vec4f(x); }'];
const glsl = () => {
  const gl = document.querySelector('canvas').getContext('webgl2');
  const sh = (type, src) => { const s = gl.createShader(type); gl.shaderSource(s, src); gl.compileShader(s); return s; };
  const p = gl.createProgram();
  gl.attachShader(p, sh(gl.VERTEX_SHADER, '#version 300 es\\nin vec2 pos;\\nvoid main() { gl_Position = vec4(pos, 0.0, 1.0); }'));
  gl.attachShader(p, sh(gl.FRAGMENT_SHADER, '#version 300 es\\nprecision highp float;\\nout vec4 c;\\nfloat wave(float x) { return x; }\\nvoid main() { c = vec4(1.0); }'));
  gl.linkProgram(p);
  console.log('glsl: ' + gl.getProgramInfoLog(p));
};
let device;
const next = i => {
  if (i >= bodies.length) { glsl(); return; }
  device.pushErrorScope('validation');
  device.createShaderModule({ code: head + bodies[i] });
  return device.popErrorScope().then(e => { console.log('wgsl: ' + (e ? e.message : 'accepted')); return next(i + 1); });
};
navigator.gpu.requestAdapter().then(a => a.requestDevice()).then(d => { device = d; return next(0); }).catch(e => console.log('error: ' + e));
</script><canvas width="8" height="8"></canvas>`;
let r=start(refusals,"file:///refusals.html");const said=[...r.logs];
for(let i=0;i<4;i++){r=advance(r);said.push(...r.logs);}
const lines=said.filter(l=>/^(wgsl|glsl): /.test(l));
assert.deepEqual(lines,[
  "wgsl: shader: 'while' is not in the subset: loops are for loops with integer literal bounds, at most 256 steps",
  "wgsl: shader: only @vertex and @fragment functions: functions of your own are not in the subset (write their bodies inline)",
  "wgsl: shader: the for loop over b runs 10000 times; the bound is 256",
  "glsl: shader: the function wave is not in the subset: only main (write its body inline)"]);
console.log("refusals: Lean's reasons reach the page");
console.log(`shader_gallery_test (${lean?"BubblePopJS":"QuickJS-NG"}): ok`);
