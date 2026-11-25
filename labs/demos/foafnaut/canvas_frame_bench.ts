// Canvas 2D frame cost (issue https://github.com/danbri/factoidal-core/issues/1098): the
// layers a Particle Rex frame paints, on a 1600 x 1000 canvas, one animation frame per turn.
// Run: deno run --allow-read --allow-ffi --allow-env canvas_frame_bench.ts [FRAMES] [SCENE]
// FOAFNAUT_NATIVE_ENGINE names the engine library (default .build/web-render/engines/).
// SCENE: all (default), solid, gradient, clip, alpha, rects. Prints median and p95 turn time.
import {loadHTML,type ScriptTurn} from "./native_html_engine.ts";
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const library=[Deno.env.get("FOAFNAUT_NATIVE_ENGINE")??"",
  new URL("./.build/web-render/engines/libweb-render.so",import.meta.url).pathname].find(p=>p&&exists(p))??"";
if(!library){console.error("no engine library");Deno.exit(2);}
const frames=Number(Deno.args[0]??"20");
const scene=Deno.args[1]??"all";
const W=1600,H=1000;
const body=`const c=document.getElementById('c'),x=c.getContext('2d');const scene=${JSON.stringify(scene)};let n=0;
function frame(){requestAnimationFrame(frame);n++;
  x.setTransform(1.25,0,0,1.25,0,0);x.globalAlpha=1;
  if(scene=='all'||scene=='solid'){x.fillStyle='#10131f';x.fillRect(0,0,${W/1.25},${H/1.25});}
  x.save();
  if(scene=='all'||scene=='clip'||scene=='gradient'){x.beginPath();x.rect(4,6,${W/1.25-8},${H/1.25-12});x.clip();}
  if(scene=='all'||scene=='gradient'){const g=x.createLinearGradient(0,6,0,${H/1.25-6});g.addColorStop(0,'#203060');g.addColorStop(1,'#c08050');
    x.fillStyle=g;x.fillRect(-20,-20,${W/1.25+40},${H/1.25+40});}
  if(scene=='all'||scene=='rects'){for(let i=0;i<400;i++){x.globalAlpha=(i%7+1)/8.3;x.fillStyle=i%2?'#fff':'#f80';x.fillRect((i*37+n)%1200+0.5,(i*53)%760+0.25,5,5);}}
  x.restore();
  if(scene=='all'||scene=='alpha'){x.globalAlpha=0.3;x.fillStyle='#e00000';x.fillRect(0,0,${W/1.25},${H/1.25});}
}
requestAnimationFrame(frame);`;
const engine=await loadHTML(library);
const url="file:///canvas-frame-bench.html";
let t=engine.scriptSession(`<!doctype html><html><body style="margin:0"><canvas id=c width=${W} height=${H}></canvas><script>${body}</script></body></html>`,
  {action:"start",url,resources:[],width:W,height:H,layout:{url},engine:"bubblepop",instructionsPerMs:1e12}) as ScriptTurn&{ns:number};
if((t as {errors:string[]}).errors?.length) console.error(t.errors);
const ns:number[]=[],wall:number[]=[];
for(let i=0;i<frames+2;i++){
  const t0=performance.now();
  const r=engine.scriptSession("",{action:"advance",session:t.session,ms:16}) as ScriptTurn&{ns:number};
  const t1=performance.now();
  if(i>=2){ns.push(r.ns/1e6);wall.push(t1-t0);}
}
const q=(a:number[],p:number)=>{const s=[...a].sort((u,v)=>u-v);return s[Math.min(s.length-1,Math.floor(p*s.length))];};
console.log(`${scene}: ${frames} frames, turn ms p50 ${q(ns,0.5).toFixed(2)} p95 ${q(ns,0.95).toFixed(2)}; call ms p50 ${q(wall,0.5).toFixed(2)} p95 ${q(wall,0.95).toFixed(2)}`);
engine.scriptSession("",{action:"close"});
