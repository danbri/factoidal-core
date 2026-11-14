// BubblePopJS speed on page-like code (docs/designissues/2026-11-14-js-perf.md).
// Runs the workloads of bubblepop_perf/page/ as page scripts in the engine library, each in
// the start turn of its own page, and reports the engine's own time of that turn (`ns`), the
// script steps of the turn (`instructions`: calls and loop iterations, not every node), and
// steps per second; then the time of one DOM call (the loop with the call, less the same loop
// with a plain property read, per call). Best of --runs; an empty page's turn is subtracted.
//   deno run -A --unstable-ffi js_perf_bench.ts --engine libweb-render.dylib [--runs 3]
//     [--scale 1] [--only props,dom] [--json out.json] [--no-domcall] [--host DIR]
// --host: the directory of native_html_engine.ts and native_net.ts of the engine's own commit
// (the perf gate runs an older engine with its own host; the workloads stay these).
type Turn={session:number;ns:number;instructions:number;errors:string[];logs:string[];netSync?:unknown};
const arg=(k:string,d:string)=>{const i=Deno.args.indexOf(k);return i>=0?Deno.args[i+1]:d;};
const lib=arg("--engine","");
const hostDir=arg("--host","");
const hostURL=(f:string)=>hostDir?new URL(f,"file://"+(hostDir.endsWith("/")?hostDir:hostDir+"/")).href:new URL("./"+f,import.meta.url).href;
const {loadHTML}=await import(hostURL("native_html_engine.ts"));
const {netAnswer}=await import(hostURL("native_net.ts"));
if(!lib){console.error("--engine PATH required");Deno.exit(2);}
const runs=Number(arg("--runs","3")),scale=Number(arg("--scale","1"));
const only=arg("--only","").split(",").filter(Boolean);
const dir=new URL("./bubblepop_perf/page/",import.meta.url);
const WORK=["props","closures","strings","json","dom","reconcile","modules"];
const OPS=["base","getAttribute","setAttribute","createElement","appendChild","querySelector","styleRead","textContent","classList","parentNode"];
// module sources are served from a loopback port, as a page's are from its origin
const server=Deno.serve({port:0,hostname:"127.0.0.1",onListen(){}},async req=>{
  const p=new URL(req.url).pathname;
  try{return new Response(await Deno.readTextFile(new URL("."+p,dir)),{headers:{"content-type":"text/javascript"}});}
  catch{return new Response("not found",{status:404});}
});
const origin=`http://127.0.0.1:${server.addr.port}/`;
const engine=await loadHTML(lib);
const call=(src:string,req:Record<string,unknown>)=>engine.scriptSession(src,req) as unknown as Turn;
async function start(html:string,url:string):Promise<Turn>{
  let t=call(html,{action:"start",url,resources:[],instructionsPerMs:1e12,engine:"bubblepop",network:true,width:800,height:600});
  for(let i=0;t.netSync&&i<64;i++)t=call("",{action:"syncAnswer",session:t.session,answer:await netAnswer(t.netSync as never)});
  return t;
}
const page=(pre:string,body:string,module=false)=>`<!doctype html><html><head><meta charset="utf-8"><title>bench</title></head><body><div id="root"></div>`+
  `<script>var SCALE=${scale};var RESULT;${pre}</script>`+(module?`<script type="module" src="${body}"></script>`:`<script>${body}</script>`)+
  `<script>${module?"setTimeout(()=>console.log('RESULT '+RESULT),0)":"console.log('RESULT '+RESULT)"}</script></body></html>`;
async function measure(html:string,url:string){
  let best:Turn|null=null;
  for(let r=0;r<runs;r++){
    const t=await start(html,url);
    if(t.errors.length)return {error:t.errors[0].slice(0,200)};
    if(!best||t.ns<best.ns)best=t;
  }
  const t=best!;
  return {ns:t.ns,steps:t.instructions,result:(t.logs.find(l=>l.startsWith("RESULT "))??"").slice(7)};
}
const out:Record<string,unknown>={engine:lib,scale,runs};
// --loop W SECONDS: start workload W (or domcall:OP) again and again, for a profiler (`sample`)
const loopW=arg("--loop","");
if(loopW){
  const secs=Number(Deno.args[Deno.args.indexOf("--loop")+2]||"10");
  await start(page("",""),origin+"empty.html");
  console.log("LOOP START");
  const [w,op]=loopW.split(":");
  const src=w==="modules"?"modules.js":await Deno.readTextFile(new URL(w+".js",dir));
  const html=page(op?`var OP=${JSON.stringify(op)};`:"",src,w==="modules");
  const t0=performance.now();let n=0;
  while(performance.now()-t0<secs*1000){const t=await start(html,origin+w+".html");if(t.errors.length){console.log(t.errors[0]);break;}n++;}
  console.log("LOOP DONE",n);await server.shutdown();Deno.exit(0);
}
// the first start makes the realm with the page objects (kept for later starts): not timed
await start(page("",""),origin+"empty.html");
const empty=await measure(page("",""),origin+"empty.html");
out.empty=empty;
const e0=(empty as {ns:number}).ns;
const rows:Record<string,unknown>={};
for(const w of WORK){
  if(only.length&&!only.includes(w))continue;
  const src=w==="modules"?"modules.js":await Deno.readTextFile(new URL(w+".js",dir));
  const m=await measure(page("",src,w==="modules"),origin+w+".html") as {ns?:number;steps?:number;result?:string;error?:string};
  if(m.error){rows[w]=m;console.log(w,"ERROR",m.error);continue;}
  const ms=(m.ns!-e0)/1e6,sps=Math.round(m.steps!/(ms/1000));
  rows[w]={ms:Math.round(ms*10)/10,steps:m.steps,stepsPerSec:sps,result:m.result};
  console.log(`${w.padEnd(10)} ${ms.toFixed(1).padStart(9)} ms ${String(m.steps).padStart(9)} steps ${String(sps).padStart(9)} steps/s  result ${m.result}`);
}
out.workloads=rows;
if(!Deno.args.includes("--no-domcall")){
  const src=await Deno.readTextFile(new URL("domcall.js",dir));
  const per:Record<string,unknown>={};let base=0;const N=scale*2000;
  for(const op of OPS){
    const m=await measure(page(`var OP=${JSON.stringify(op)};`,src),origin+"domcall.html") as {ns?:number;error?:string;steps?:number};
    if(m.error){per[op]={error:m.error};console.log(op,"ERROR",m.error);continue;}
    if(op==="base")base=m.ns!;
    const us=(m.ns!-base)/N/1000;
    per[op]={usPerCall:Math.round(us*100)/100,ms:Math.round((m.ns!-e0)/1e4)/100};
    console.log(`dom ${op.padEnd(14)} ${op==="base"?"(loop) "+((m.ns!-e0)/N/1000).toFixed(2)+" us/iter":us.toFixed(2)+" us/call"}`);
  }
  out.domcall=per;
}
const j=arg("--json","");
if(j)await Deno.writeTextFile(j,JSON.stringify(out,null,1));
await server.shutdown();
Deno.exit(0);
