// One sample of one performance fixture (labs/demos/foafnaut/fixtures/perf, skills/perf-gate).
//
// The page is loaded as the browser host loads it: prepareHTML of the host directory given
// (the host of the engine's own commit), its sheets, images and scripts fetched over HTTP
// from a server in this process, the page's scripts on BubblePopJS. Every engine call is
// timed here; the host's own work (fetching, JSON) is not part of the engine times.
//
//   deno run -A --unstable-ffi tests/browser-wpt/perf-run.ts --engine LIB --fixture NAME \
//     [--host labs/demos/foafnaut] [--fixtures labs/demos/foafnaut/fixtures/perf] [--font NotoSans-Regular.ttf]
//
// Prints one JSON line: times in ms (parse, first layout, settled layout, a relayout at
// another width, the scripts' start and settle turns), the engine's exact counters
// (script instructions, jobs, tasks, DOM commands, frameWork, primitives) and `valid`
// (the page loaded and, for a scripted fixture, its scripts reported that they finished).
// Peak memory and CPU time are the driver's (release-tests/perf.py, from the process's
// rusage). One process is one sample: nothing is warm from an earlier sample.
import {resolve,join,dirname} from "node:path";
import {fileURLToPath} from "node:url";

const args=Deno.args;
const opt=(name:string,fallback?:string)=>{const i=args.indexOf(name);return i>=0?args[i+1]:fallback;};
const here=dirname(fileURLToPath(import.meta.url));
const root=resolve(here,"../..");
const hostDir=resolve(opt("--host",join(root,"labs/demos/foafnaut"))!);
const fixtures=resolve(opt("--fixtures",join(root,"labs/demos/foafnaut/fixtures/perf"))!);
const enginePath=opt("--engine");
const name=opt("--fixture");
const font=opt("--font");
const width=1280,height=800;
if(!enginePath||!name){console.error("usage: perf-run.ts --engine LIB --fixture NAME [--host DIR] [--fixtures DIR] [--font TTF]");Deno.exit(2);}
const manifest=JSON.parse(Deno.readTextFileSync(join(fixtures,"manifest.json")));
const fixture=manifest.fixtures[name];
if(!fixture){console.error(`no fixture ${name} in ${fixtures}/manifest.json`);Deno.exit(2);}

const out:Record<string,unknown>={fixture:name,set:manifest.set_sha256,valid:false};
const t0=performance.now();
const {loadHTML}=await import(join(hostDir,"native_html_engine.ts"));
const doc=await import(join(hostDir,"native_html_document.ts"));
const engine=loadHTML(enginePath) as unknown;
const eng=await engine as Record<string,(...a:unknown[])=>unknown>;
out.engine_load_ms=performance.now()-t0;
if(font){const f=performance.now();await doc.loadFontFile(eng,font,"Noto Sans");out.font_ms=performance.now()-f;}

// Every engine call, timed: count and ms by call name, and each call in order.
const calls:Record<string,{n:number;ms:number}>={};
const order:{call:string;ms:number}[]=[];
const timed=new Proxy(eng,{get(target,key:string){
  const v=(target as Record<string,unknown>)[key];
  if(typeof v!=="function")return v;
  return (...a:unknown[])=>{
    const s=performance.now();
    const done=()=>{const ms=performance.now()-s;const c=calls[key]??={n:0,ms:0};c.n++;c.ms+=ms;order.push({call:key,ms});};
    try{const r=(v as (...x:unknown[])=>unknown).apply(target,a);done();return r;}catch(e){done();throw e;}
  };
}});

// The fixtures over HTTP, as a site serves them.
const types:Record<string,string>={html:"text/html; charset=utf-8",css:"text/css; charset=utf-8",js:"text/javascript; charset=utf-8",
  png:"image/png",svg:"image/svg+xml",json:"application/json"};
const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},async req=>{
  const path=decodeURIComponent(new URL(req.url).pathname).replace(/^\/+/,"");
  if(path.includes(".."))return new Response("no",{status:403});
  try{const body=await Deno.readFile(join(fixtures,path));
    return new Response(body,{headers:{"content-type":types[path.split(".").pop()!]??"application/octet-stream"}});}
  catch{return new Response("not found",{status:404});}
});
const origin=`http://127.0.0.1:${server.addr.port}`;
const pageURL=`${origin}/${fixture.page}`;

type Turn={session:number;changed:boolean;commandCount:number;commands?:unknown[];logs:string[];errors:string[];
  instructions:number;jobs:number;tasks:number;ns:number;fetches?:{id:number;url:string;kind:string}[]};
const logs:string[]=[],errors:string[]=[];
const script={instructions:0,jobs:0,tasks:0,turns:0,start_ms:0,settle_ms:0,commands:0};
const note=(t:Turn)=>{logs.push(...t.logs);errors.push(...t.errors);script.instructions+=t.instructions;script.jobs+=t.jobs;script.tasks+=t.tasks;
  script.turns++;script.commands=t.commandCount;};
const call=(source:string,request:Record<string,unknown>)=>{const s=performance.now();const t=timed.scriptSession(source,request) as Turn;return {t,ms:performance.now()-s};};
// The scripts a turn waits for (module scripts, workers), fetched and given back, until none.
const answerFetches=async(t:Turn):Promise<{t:Turn;ms:number}>=>{
  let ms=0;
  for(let k=0;k<64&&t.fetches?.length;k++){
    const results=[];
    for(const f of t.fetches){
      try{const r=await fetch(new URL(f.url,pageURL));const source=await r.text();
        results.push({id:f.id,status:r.status,url:f.url,contentType:r.headers.get("content-type")??"",source});}
      catch{results.push({id:f.id,status:0,url:f.url,contentType:"",source:""});}
    }
    const next=call("",{action:"fetched",session:t.session,results});ms+=next.ms;note(next.t);t=next.t;
  }
  return {t,ms};
};
let turn:Turn|undefined;
doc.setScriptHost({start:async(source:string,url:string,resources:unknown[],encoding?:string,mode?:Record<string,unknown>)=>{
  const first=call(source,{action:"start",url,resources,width,height,zoomUnit:100,layout:{url,textScalePercent:100,zoomUnit:100,...(mode??{})},
    engine:"bubblepop",...(encoding?{encoding}:{})});
  note(first.t);
  const more=await answerFetches(first.t);
  script.start_ms=first.ms+more.ms;turn=more.t;
  return turn;
}});

try{
  const page=await doc.prepareHTML(timed,pageURL,undefined,undefined,{liberal:true});
  out.parse_ms=order.find(c=>c.call==="inspect")?.ms;
  out.prepare_ms=performance.now()-t0-(out.engine_load_ms as number)-((out.font_ms as number)??0);
  const view={textScalePercent:100,zoomUnit:100};
  let s=performance.now();
  const first=page.compile(width,height,view) as {primitiveCount:number};
  out.first_layout_ms=performance.now()-s;
  out.primitives=first.primitiveCount;
  if(page.script&&turn){
    // The page settles: timers and tasks until none waits (virtual time), with what they fetch.
    s=performance.now();
    let t=call("",{action:"settle",session:turn.session,budgetMs:30000});note(t.t);
    let more=await answerFetches(t.t);
    for(let k=0;k<8&&more.t.fetches===undefined&&(more.t as unknown as {nextTimer:number|null}).nextTimer!=null;k++){
      t=call("",{action:"settle",session:turn.session,budgetMs:30000});note(t.t);more=await answerFetches(t.t);
    }
    script.settle_ms=performance.now()-s;
    page.applyTurn(more.t);
    s=performance.now();
    const settled=page.compile(width,height,view) as {primitiveCount:number};
    out.settled_layout_ms=performance.now()-s;
    out.settled_primitives=settled.primitiveCount;
  }
  s=performance.now();
  page.compile(1024,height,view);
  out.resize_layout_ms=performance.now()-s;
  out.frame_work=eng.frameWork?.() ?? null;
  const done=logs.find(l=>l.includes("perf-fixture-done"));
  if(done)try{out.fixture_report=JSON.parse(done.slice(done.indexOf("{")));}catch{/* not JSON */}
  out.valid=!fixture.scripted||!!done;
  if(fixture.dom_calls_at_least&&((out.fixture_report as {domCalls?:number})?.domCalls??0)<fixture.dom_calls_at_least)out.valid=false;
  if(!out.valid)out.why=fixture.scripted&&!done?"the fixture's scripts did not report that they finished":"fewer DOM calls than the fixture states";
}catch(e){
  out.why=`load failed: ${String(e instanceof Error?e.message:e).slice(0,300)}`;
}
out.script=page_script();
function page_script(){return {...script,errors:errors.length,first_error:errors[0]?.slice(0,200)};}
out.calls=Object.fromEntries(Object.entries(calls).map(([k,v])=>[k,{n:v.n,ms:Math.round(v.ms*10)/10}]));
out.engine_ms=Object.values(calls).reduce((a,c)=>a+c.ms,0);
out.total_ms=performance.now()-t0;
for(const k of Object.keys(out))if(typeof out[k]==="number"&&k.endsWith("_ms"))out[k]=Math.round((out[k] as number)*10)/10;
console.log(JSON.stringify(out));
await server.shutdown();
Deno.exit(0);
