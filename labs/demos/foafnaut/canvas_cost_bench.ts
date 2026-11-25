// Canvas 2D cost bench (issue https://github.com/danbri/factoidal-core/issues/1098, items 3 and 4).
// One JSON line per case: the engine's time for one script turn of N canvas calls (µs per
// call), the bytes of the turn answer, and the bytes and host decode time of its pixels
// commands (the transfer of the canvas bitmap to the GPU texture).
// Run (Linux rig engine or a local build):
//   FOAFNAUT_NATIVE_ENGINE=PATH deno run --no-check -A canvas_cost_bench.ts [REPEAT]
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";
import {decodePixels,unrle} from "../../../docs/web/hub/foafnaut/page-gpu.mjs";

const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const library=[Deno.env.get("FOAFNAUT_NATIVE_ENGINE")??"",
  new URL("./.build/web-render/engines/libweb-render.so",import.meta.url).pathname,
  new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname].find(p=>p&&exists(p));
if(!library)throw new Error("no native engine: set FOAFNAUT_NATIVE_ENGINE");
const repeat=Number(Deno.args[0]??5);
const engine=await loadHTML(library);
const url="file:///canvas-cost-bench.html";

type Case={name:string;w:number;h:number;calls:number;body:string};
const cases:Case[]=[
  // Issue 1098 item 4: 1,500 fillRect and globalAlpha pairs (3,000 calls).
  {name:"fillRect+globalAlpha int",w:800,h:500,calls:3000,body:"for(let i=0;i<1500;i++){x.globalAlpha=(i%7+1)/8;x.fillRect((i*7)%700,(i*3)%480,5,5);}"},
  {name:"fillRect+globalAlpha frac",w:800,h:500,calls:3000,body:"let s=0.1;for(let i=0;i<1500;i++){s=s*1.0001+0.37;x.globalAlpha=(i%7+1)/8.3;x.fillRect(s%700+0.123,(i*3)%480+0.5,5,5);}"},
  {name:"fillStyle+fillRect",w:800,h:500,calls:3000,body:"for(let i=0;i<1500;i++){x.fillStyle=i%2?'#f00':'#00f';x.fillRect((i*7)%700,(i*3)%480,5,5);}"},
  {name:"empty loop (no canvas call)",w:800,h:500,calls:3000,body:"let q=0;for(let i=0;i<1500;i++){q+=(i%7+1)/8;q+=(i*7)%700;}"},
  // Item 3: one small rect on a full-window canvas; the host gets the canvas's pixels.
  {name:"one small rect 1600x1000",w:1600,h:1000,calls:1,body:"x.fillRect(10,10,20,20);"},
  {name:"full clear+fill 1600x1000",w:1600,h:1000,calls:2,body:"x.clearRect(0,0,1600,1000);x.fillRect(0,0,1600,1000);"},
];

for(const c of cases){
  const html=`<!doctype html><html><body style="margin:0"><canvas id=c width=${c.w} height=${c.h}></canvas><script>const x=document.getElementById('c').getContext('2d');${c.body}</script></body></html>`;
  const runs:{ns:number;wall:number;answer:number;pixels:number;pixelBytes:number;decodeMs:number;oldDecodeMs:number}[]=[];
  for(let r=0;r<repeat;r++){
    const t0=performance.now();
    const t=engine.scriptSession(html,{action:"start",url,resources:[],width:c.w,height:c.h,layout:{url},engine:"bubblepop",instructionsPerMs:1e12}) as ScriptTurn;
    const wall=performance.now()-t0;
    if(t.errors.length)throw new Error(c.name+": "+t.errors.join("; "));
    const gpu=(t.gpu??[]) as {k:string;data?:string;w:number;h:number;rle?:number}[];
    const pix=gpu.filter(g=>g.k==="pixels");
    const d0=performance.now();let pixelBytes=0;
    for(const p of pix)pixelBytes+=decodePixels(p).byteLength;
    const decodeMs=performance.now()-d0;
    // The decode of release 0.35 (Uint8Array.from with a function per character), for comparison.
    const o0=performance.now();
    for(const p of pix){const raw=Uint8Array.from(atob(p.data!),ch=>ch.charCodeAt(0));if(p.rle)unrle(raw,p.w,p.h);}
    const oldDecodeMs=performance.now()-o0;
    runs.push({ns:t.ns,wall,answer:JSON.stringify(t).length,pixels:pix.reduce((n,p)=>n+(p.data?.length??0),0),pixelBytes,decodeMs,oldDecodeMs});
    engine.scriptSession("",{action:"close",session:t.session});
  }
  const best=runs.reduce((a,b)=>a.ns<=b.ns?a:b);
  console.log(JSON.stringify({type:"canvas-cost-bench",case:c.name,canvas:`${c.w}x${c.h}`,calls:c.calls,
    turnMs:+(best.ns/1e6).toFixed(2),usPerCall:+(best.ns/1e3/c.calls).toFixed(2),wallMs:+best.wall.toFixed(2),
    answerChars:best.answer,pixelsChars:best.pixels,pixelBytes:best.pixelBytes,decodeMs:+best.decodeMs.toFixed(2),oldDecodeMs:+best.oldDecodeMs.toFixed(2)}));
}
