// Frame time of the FOAF explorer's layout work: the page's JavaScript force step, the
// verified WebAssembly overlap check (foaf-check.wat, the bytes in
// pages/foaf-explorer-verified.html), and the same check written in JavaScript for
// comparison (here only, never in a page), for the demo graph's cast (25 people) and a
// synthetic 500-node graph. In Foafnaut (the native engine library) on both script
// engines, BubblePopJS and QuickJS-NG in WasmVM; each phase runs in its own timer turn,
// and the time is the engine's own for that turn (`ns`). `--html FILE` writes the bench
// page instead, to open in a browser (it logs `performance.now()` times to the console).
// Record: docs/designissues/2026-11-09-verified-foaf-layout.md, "Performance".
//   deno run --allow-read --allow-write --allow-ffi --allow-env check_bench.ts [--library DYLIB] [--reps N] [--html FILE]
import {loadHTML,type HTMLEngine} from "../native_html_engine.ts";

const arg=(k:string)=>{const i=Deno.args.indexOf(k);return i>=0?Deno.args[i+1]:undefined;};
const library=arg("--library")??new URL("../.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const reps=Number(arg("--reps")??20);
const sizes=arg("--sizes")??"25,500";
const only=arg("--engine");
const phaseRe=arg("--phases")??"";
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
const guest=[Deno.env.get("QUICKJS_WASM")??"",`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`].find(exists);
const verified=await Deno.readTextFile(new URL("../pages/foaf-explorer-verified.html",import.meta.url));
const hex=verified.slice(verified.indexOf("var FOAF_CHECK_WASM_HEX"),verified.indexOf("/* foaf-check.wasm: END */"));

const page=`<!doctype html><html><head><meta charset="utf-8"><title>foaf-check bench</title></head><body><p id="out">bench</p><script>
${hex}
var REPS=${reps}, sizes=[${sizes}], phases=[], results={};
// Deterministic positions on a stage that holds them (people 60 px apart in a grid, jittered).
function setup(n){ var side=Math.ceil(Math.sqrt(n)), W=side*70+80, X=[],Y=[],VX=[],VY=[],FX=[],FY=[],HW=[],s=7;
  function rnd(){ s=(s*1103515245+12345)%2147483648; return s/2147483648; }
  for(var i=0;i<n;i++){X.push(40+(i%side)*70+rnd()*30);Y.push(40+Math.floor(i/side)*70+rnd()*30);VX.push(0);VY.push(0);FX.push(0);FY.push(0);HW.push(22+Math.floor(rnd()*12));}
  return {n:n,W:W,H:W,X:X,Y:Y,VX:VX,VY:VY,FX:FX,FY:FY,HW:HW,boxes:new Int32Array(4*n),EA:[],EB:[]}; }
// The explorer's force step (foaf-explorer.html), unchanged in its arithmetic.
function step(g){ var n=g.n,X=g.X,Y=g.Y,FX=g.FX,FY=g.FY,CX=g.W/2,CY=g.H/2,SPRING=100,REPEL=0.045*SPRING*SPRING,FAR=9*SPRING*SPRING,i,j,dx,dy,d2,f,ax,ay,fx,fy;
  for(i=0;i<n;i++){FX[i]=(CX-X[i])*0.012;FY[i]=(CY-Y[i])*0.012;}
  for(i=0;i<n;i++){ax=X[i];ay=Y[i];fx=0;fy=0;for(j=i+1;j<n;j++){dx=ax-X[j];dy=ay-Y[j];d2=dx*dx+dy*dy;if(d2>FAR)continue;if(d2<1){dx=(i-j)*0.7+0.3;dy=(j%3)-1+0.2;d2=dx*dx+dy*dy;}
    f=REPEL/d2*(1-d2/FAR);dx*=f;dy*=f;fx+=dx;fy+=dy;FX[j]-=dx;FY[j]-=dy;}FX[i]+=fx;FY[i]+=fy;}
  for(i=0;i<n;i++){var vx=(g.VX[i]+FX[i])*0.76,vy=(g.VY[i]+FY[i])*0.76;g.VX[i]=vx*0.001;g.VY[i]=vy*0.001;} }
function footprints(g){ var b=g.boxes; for(var i=0;i<g.n;i++){var x=Math.round(g.X[i]),y=Math.round(g.Y[i]);
  b[4*i]=Math.max(0,x-g.HW[i]);b[4*i+1]=Math.max(0,y-22);b[4*i+2]=Math.min(g.W,x+g.HW[i]);b[4*i+3]=Math.min(g.H,y+31);} return b; }
var kernel=null;
function wasmCheck(g){ var b=footprints(g),n=g.n,m=new Int32Array(kernel.memory.buffer); m.set(b,0); return kernel.check(n,500,0,16*n); }
// The same check in JavaScript (bench only).
function jsCheck(g){ var b=footprints(g),n=g.n,all=1; for(var i=0;i<n;i++){var l=b[4*i],t=b[4*i+1],r=b[4*i+2],bo=b[4*i+3],area=Math.max(r-l,0)*Math.max(bo-t,0),sum=0;
  for(var j=0;j<n;j++){if(j===i)continue;sum+=Math.max(Math.min(r,b[4*j+2])-Math.max(l,b[4*j]),0)*Math.max(Math.min(bo,b[4*j+3])-Math.max(t,b[4*j+1]),0);}
  if(!(area>0&&10000*sum<=500*area))all=0;} return all; }
function time(name,f){ var t0=performance.now(); for(var k=0;k<REPS;k++)f(); var ms=(performance.now()-t0)/REPS; results[name]=Math.round(ms*1000)/1000; console.log('phase '+name+' '+results[name]); }
var graphs={}; sizes.forEach(function(n){graphs[n]=setup(n);});
sizes.forEach(function(n){ var g=graphs[n];
  phases.push(['step-js-'+n,function(){step(g);}]);
  phases.push(['check-wasm-'+n,function(){wasmCheck(g);}]);
  phases.push(['check-js-'+n,function(){jsCheck(g);}]); });
phases = phases.filter(function(p){ return new RegExp(${JSON.stringify(phaseRe)}).test(p[0]); });
WebAssembly.instantiate((function(){var b=new Uint8Array(FOAF_CHECK_WASM_HEX.length/2);for(var i=0;i<b.length;i++)b[i]=parseInt(FOAF_CHECK_WASM_HEX.slice(2*i,2*i+2),16);return b;})(),{}).then(function(r){
  kernel=r.instance.exports;
  if (${JSON.stringify(phaseRe)} === '') sizes.forEach(function(n){ if(wasmCheck(graphs[n])!==jsCheck(graphs[n])) console.log('MISMATCH '+n); });
  phases.forEach(function(p,k){ setTimeout(function(){ time(p[0],p[1]); if(k===phases.length-1){document.getElementById('out').textContent=JSON.stringify(results);console.log('bench '+JSON.stringify(results));} }, 100*(k+1)); });
});
</script></body></html>`;

const html=arg("--html");
if(html){await Deno.writeTextFile(html,page);console.log("wrote "+html);Deno.exit(0);}
if(!exists(library)){console.log("NOT RUN: no native library at "+library);Deno.exit(0);}
type Turn={session:number;ns:number;errors:string[];logs:string[]};
function run(engine:HTMLEngine,lean:boolean){
  const extra=lean?{engine:"bubblepop"}:{};
  const t=engine.scriptSession(page,{action:"start",url:"file:///foaf-check-bench.html",resources:[],instructionsPerMs:1e12,...extra}) as unknown as Turn;
  if(t.errors.length)throw new Error(t.errors.join("; "));
  const out:Record<string,number>={};const logs:string[]=[...t.logs];
  // Promise jobs (instantiate) run in the start turn's checkpoint or the next advance.
  for(let k=0;k<=8;k++){
    const turn=engine.scriptSession("",{action:"advance",session:t.session,ms:100}) as unknown as Turn;
    if(turn.errors.length)throw new Error(turn.errors.join("; "));
    logs.push(...turn.logs);
    for(const line of turn.logs){const m=/^phase (\S+)/.exec(line);if(m){out[m[1]]=Math.round(turn.ns/reps/1e3)/1e3;console.error(lean?"bubblepop":"quickjs",m[1],out[m[1]]);}}
  }
  engine.scriptSession("",{action:"close"});
  if(logs.some(l=>l.startsWith("MISMATCH")))throw new Error("wasm and js checks disagree");
  return out;
}
const engine=await loadHTML(library);
const res:Record<string,unknown>={};
const info=engine.scriptInfo();
if(only!=="quickjs"&&(info.engines??[]).includes("bubblepop"))res["BubblePopJS (ms per call)"]=run(engine,true);
if(guest&&only!=="bubblepop"){engine.scriptLoad(await Deno.readFile(guest));res["QuickJS-NG in WasmVM (ms per call)"]=run(engine,false);}
console.log(JSON.stringify(res,null,1));
