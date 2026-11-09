// Canvas 2D drawn by Lean (L4Factoidal.PageCanvas; record docs/designissues/2026-11-08-canvas-2d.md).
// On BubblePopJS and, with a guest built from this prelude (QUICKJS_WASM), on QuickJS-NG in WasmVM:
// 1. pixels: the scenes of canvas2d-scenes.js drawn by the engine against Chrome's pixels
//    (canvas2d-reference.json, from canvas2d_reference.mjs);
// 2. the host commands of a drawn canvas: one texture, then the canvas's pixels each frame;
// 3. the API answers: getImageData, isPointInPath, measureText (with no font held: zeros),
//    getTransform, fillStyle serialisation, errors;
// 4. cost: a frame of 1,000 commands, and a frame of the chart demo (pages/canvas-chart.html).
// Needs the native library (build-web-render.sh --native).
// Run: deno run --allow-read --allow-ffi --allow-env canvas2d_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";
import {scenePage} from "./canvas2d_reference.mjs";
import {unrle} from "../../../docs/web/hub/foafnaut/page-gpu.mjs";

const library=Deno.env.get("WEB_RENDER_LIBRARY")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const guest=Deno.env.get("QUICKJS_WASM");
type Turn=ScriptTurn&{gpu?:{k:string;g?:number[];node?:number;w?:number;h?:number;data?:string;rle?:number}[];gpuPage?:number};

const engine:HTMLEngine=await loadHTML(library);
if(guest)engine.scriptLoad(await Deno.readFile(guest));
const engines=guest?["bubblepop","quickjs"]:["bubblepop"];
const reference=JSON.parse(await Deno.readTextFile(new URL("./canvas2d-reference.json",import.meta.url))) as {browser:string;scenes:Record<string,string>};
const scenes=await Deno.readTextFile(new URL("./canvas2d-scenes.js",import.meta.url));

function start(kind:string,html:string,url:string):Turn{
  return engine.scriptSession(html,{action:"start",url,resources:[],instructionsPerMs:1e12,full:true,...(kind==="bubblepop"?{engine:"bubblepop"}:{})}) as Turn;
}
const advance=(t:Turn,ms:number)=>engine.scriptSession("",{action:"advance",session:t.session,ms}) as Turn;
const hexBytes=(h:string)=>Uint8Array.from(h.match(/../g)!.map(x=>parseInt(x,16)));
/** A reference scene: RGBA, raw DEFLATE, Base64. */
async function inflate(b64:string):Promise<Uint8Array>{
  const stream=new Blob([Uint8Array.from(atob(b64),c=>c.charCodeAt(0))]).stream().pipeThrough(new DecompressionStream("deflate-raw"));
  return new Uint8Array(await new Response(stream).arrayBuffer());
}

const summary:string[]=[];
for(const kind of engines){
  // 1. Pixels against Chrome.
  let t0=performance.now();
  let turn=start(kind,scenePage(scenes,true),"file:///canvas2d-scenes.html");
  const sceneLogs=[...turn.logs];
  turn=advance(turn,10);sceneLogs.push(...turn.logs);
  console.log(`${kind}: the 27 scenes drawn and read back in ${(performance.now()-t0).toFixed(0)} ms`);
  for(const e of turn.errors)console.log(`${kind} page error:`,e);
  const got=new Map<string,Uint8Array>();
  for(const line of sceneLogs){const m=/^scene (\S+) ([0-9a-f]+)$/.exec(line);if(m)got.set(m[1],hexBytes(m[2]));}
  let pass=0;const rows:string[]=[];
  for(const [name,packed] of Object.entries(reference.scenes)){
    const want=await inflate(packed),have=got.get(name);
    if(!have){rows.push(`${name}: no pixels`);continue;}
    let off=0,worst=0;
    for(let i=0;i<want.length;i+=4){
      let d=0;for(let k=0;k<4;k++)d=Math.max(d,Math.abs(want[i+k]-have[i+k]));
      if(d>24)off++;worst=Math.max(worst,d);
    }
    // Edges differ by anti-aliasing; a scene passes with at most 3% of its pixels off by more than 24.
    const ok=off<=want.length/4*0.03;if(ok)pass++;
    rows.push(`${name}: ${off} of ${want.length/4} pixels off by more than 24 (largest ${worst})${ok?"":" FAIL"}`);
  }
  console.log(`${kind}: ${pass} of ${Object.keys(reference.scenes).length} scenes match ${reference.browser}`);for(const r of rows)console.log("  "+r);
  summary.push(`${kind}: scenes ${pass}/${Object.keys(reference.scenes).length}`);
  engine.scriptSession("",{action:"close"});

  // 2 and 3. Host commands and answers.
  const page=`<!doctype html><canvas id=c width=40 height=20></canvas><script>
const c=document.getElementById('c').getContext('2d');
c.fillStyle='rgb(0 128 255 / 50%)';console.log('fillStyle '+c.fillStyle);
c.fillRect(0,0,20,20);
const d=c.getImageData(5,5,1,1).data;console.log('pixel '+d[0]+' '+d[1]+' '+d[2]+' '+d[3]);
c.rect(10,0,10,10);console.log('inPath '+c.isPointInPath(15,5)+' '+c.isPointInPath(35,5));
c.translate(3,4);const m=c.getTransform();console.log('transform '+m.a+' '+m.e+' '+m.f);
try{c.arc(0,0,-1,0,1);}catch(e){console.log('arc '+e.name);}
const g=c.createLinearGradient(0,0,10,0);try{g.addColorStop(2,'red');}catch(e){console.log('stop '+e.name);}
try{g.addColorStop(0,'nonsense');}catch(e){console.log('color '+e.name);}
c.fillStyle=g;console.log('gradient '+(c.fillStyle===g));
c.font='bold 2em serif';console.log('font '+c.font);
console.log('url '+document.getElementById('c').toDataURL().slice(0,22));
let frames=0;function f(){c.clearRect(0,0,40,20);c.fillStyle='#0a0';c.fillRect(frames%30,0,10,20);if(++frames<5)requestAnimationFrame(f);}requestAnimationFrame(f);
</script>`;
  turn=start(kind,page,"file:///c.html");
  const gpu=[...(turn.gpu??[])],logs=[...turn.logs];
  for(let i=0;i<6;i++){turn=advance(turn,20);gpu.push(...(turn.gpu??[]));logs.push(...turn.logs);}
  for(const e of turn.errors)console.log(`${kind} page error:`,e);
  const want=["fillStyle rgba(0, 128, 255, 0.5)","pixel 0 128 255 128","inPath true false","transform 1 3 4","arc IndexSizeError",
    "stop IndexSizeError","color SyntaxError","gradient true","font bold 20px serif","url data:image/png;base64,"];
  for(const w of want)assert.ok(logs.includes(w),`${kind}: expected log "${w}", got ${JSON.stringify(logs)}`);
  const kinds=gpu.map(c=>c.k);
  assert.equal(kinds.filter(k=>k==="canvas").length,1,`${kind}: one texture for the canvas`);
  const pixels=gpu.filter(c=>c.k==="pixels");
  assert.ok(pixels.length>=5,`${kind}: pixels each frame (${pixels.length})`);
  for(const p of pixels){
    assert.equal(p.w,40);assert.equal(p.h,20);
    const raw=Uint8Array.from(atob(p.data!),ch=>ch.charCodeAt(0)),px=unrle(raw,40,20);
    assert.equal(px.length,40*20*4);
    // The last frame: the green bar at x 4..13 on transparent (straight RGBA).
    if(p===pixels.at(-1)){assert.deepEqual([...px.slice(4*(10*40+8),4*(10*40+8)+4)],[0,170,0,255]);assert.equal(px[4*(10*40+30)+3],0);}
  }
  assert.equal(gpu.find(c=>c.k==="canvas")!.node,pixels[0].g![1]-1073741824);
  engine.scriptSession("",{action:"close"});

  // 4. Cost: 1,000 commands in one frame (500 fillRect and 500 fillStyle), and the chart demo.
  const heavy=`<!doctype html><canvas id=c width=300 height=150></canvas><script>
const c=document.getElementById('c').getContext('2d');let n=0;
function f(){for(let i=0;i<500;i++){c.fillStyle=i%2?'#123':'#abc';c.fillRect((i*7)%290,(i*3)%140,10,10);}if(++n<20)requestAnimationFrame(f);}
requestAnimationFrame(f);</script>`;
  turn=start(kind,heavy,"file:///heavy.html");
  t0=performance.now();turn=advance(turn,17);const first=performance.now()-t0;
  t0=performance.now();let frames=0;for(let i=0;i<10;i++){turn=advance(turn,17);frames++;}
  const heavyMs=(performance.now()-t0)/frames;
  engine.scriptSession("",{action:"close"});
  const chart=await Deno.readTextFile(new URL("./pages/canvas-chart.html",import.meta.url));
  turn=start(kind,chart,"file:///canvas-chart.html");turn=advance(turn,17);
  for(const e of turn.errors)console.log(`${kind} chart error:`,e);
  t0=performance.now();let px=0;for(let i=0;i<20;i++){turn=advance(turn,17);px+=(turn.gpu??[]).filter(c=>c.k==="pixels").length;}
  const chartMs=(performance.now()-t0)/20;
  assert.ok(px>=15,`${kind}: the chart draws a frame each step (${px})`);
  engine.scriptSession("",{action:"close"});
  console.log(`${kind}: 1,000 commands a frame: ${heavyMs.toFixed(1)} ms a frame (first ${first.toFixed(1)} ms); chart demo: ${chartMs.toFixed(1)} ms a frame (480 x 300)`);
  summary.push(`${kind}: 1,000-command frame ${heavyMs.toFixed(1)} ms; chart frame ${chartMs.toFixed(1)} ms`);
}
console.log("canvas2d_test: ok;",summary.join("; "));
