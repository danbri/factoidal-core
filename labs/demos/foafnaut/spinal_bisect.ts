// Which parts of the Spinal Tap page make Foafnaut slow (core issue 450): the variants of
// spinal_variants.ts, each measured on the native engine with no window ("engine") and, with
// --app, in the desktop browser itself drawing off screen ("window"), then ranked by what each
// feature adds to the variant it is compared with.
//
// Engine, per variant, in a process of its own (so RSS and caches are the variant's):
//   load_ms        prepareHTML: fetch over loopback HTTP, web fonts, the scripts' start turn
//   first_ms       the first layered frame (layout and compile, checks off, as the window asks)
//   second_ms      a second layered frame of the unchanged page
//   probe_ms       a whole-page frame with the CPU probe (checks on: the window's idle check)
//   tick           N ticks of 16 ms: script turn (advance) and a layered frame at the page clock;
//                  ms median and p95, and the frame counters: layouts and primitives compiled again
//   scroll         layered frames at 8 scroll offsets 400 rows apart (a new band each)
//   rss_mb         process RSS after the run
// Window (--app DIR: a release folder with native-webgpu-html-darwin-arm64), per variant:
//   a --watch-sweep run (off screen, 1280x800 at scale 2): load to first frame, frames, frame ms,
//   GPU submit to done, the longest pump gap (the window takes no input meanwhile), the idle
//   check's draw ms, CPU % over the last 10 s (settled: idle), RSS; and a --scroll-sweep run
//   (20 wheel steps, interactive rule): input to present p50/p95/max and CPU.
//
// Every timed run holds an exclusive flock on /tmp/foafnaut-timing.lock (other agents measure on
// the same Mac). Fast mode (test.sh, spinal_bisect_check.ts): a few variants, engine only.
//
//   deno run -A --unstable-ffi spinal_bisect.ts [--only a,b] [--ticks N] [--app DIR] [--watch S]
//        [--present offscreen|window] [--out FILE] [--md FILE]
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";
import {generate,VARIANTS,defaultLibrary,defaultOut,root} from "./spinal_variants.ts";

const here=dirname(fileURLToPath(import.meta.url));
const W=1280,H=800,TICK_MS=16;
export const LOCK="/tmp/foafnaut-timing.lock";
const r1=(x:number)=>Math.round(x*10)/10;
const pct=(xs:number[],p:number)=>{const s=[...xs].sort((a,b)=>a-b);return s.length?r1(s[Math.min(s.length-1,Math.floor(p*s.length))]):null;};
const mb=(b:number)=>r1(b/1048576);

/** Run `f` holding the timing lock (flock, as flock(1) takes it). */
export async function locked<T>(f:()=>Promise<T>):Promise<T> {
  const file=await Deno.open(LOCK,{create:true,write:true});
  try{await file.lock(true);return await f();}finally{try{await file.unlock();}catch{/* closed */}file.close();}
}

// ---------------------------------------------------------------- engine, one variant
type FrameWork={layouts:number;kept:number;paintOnly:number;recompiled:number;reused:number};
export type EngineRun={variant:string;valid:boolean;why?:string;load_ms:number;first_ms:number;second_ms:number;probe_ms:number;no_probe_ms:number;
  primitives:number;second_layouts:number;
  tick:{n:number;median:number|null;p95:number|null;max:number|null;turn_median:number|null;layouts:number;recompiled:number;changed:number};
  scroll:{n:number;median:number|null;max:number|null;layouts:number};rss_mb:number;run_ms:number};

async function engineOne(name:string,file:string,ticks:number,library:string):Promise<EngineRun> {
  const t0=performance.now();
  const {loadHTML}=await import("./native_html_engine.ts");
  const {prepareHTML,loadFontFile,setScriptHost}=await import("./native_html_document.ts");
  type Engine={frameWork:(reset?:boolean)=>FrameWork|undefined;compileLayers:(s:string,w:number,h:number,o:Record<string,unknown>)=>{page:{primitiveCount:number}};
    compile:(s:string,w:number,h:number,o:Record<string,unknown>)=>{primitiveCount:number};
    scriptSession:(s:string,r:Record<string,unknown>)=>{session:number;changed:boolean;errors:string[];nextWake?:number|null}};
  const engine=await loadHTML(library) as unknown as Engine;
  await loadFontFile(engine as never,join(root,"third_party/fonts/noto-sans/NotoSans-Regular.ttf"),"Noto Sans");
  const types:Record<string,string>={html:"text/html; charset=utf-8",ttf:"font/ttf",svg:"image/svg+xml",css:"text/css"};
  const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},async req=>{
    const path=decodeURIComponent(new URL(req.url).pathname).replace(/^\/+/,"");
    if(path.includes("..")||!(path.startsWith("labs/demos/foafnaut/")||path.startsWith("third_party/fonts/")))return new Response("no",{status:403});
    try{return new Response(await Deno.readFile(join(root,path)),{headers:{"content-type":types[path.split(".").pop()!]??"application/octet-stream"}});}
    catch{return new Response("not found",{status:404});}
  });
  const url=`http://127.0.0.1:${server.addr.port}/${file.slice(root.length+1)}`;
  const errors:string[]=[];let turn:{session:number;errors:string[]}|undefined;
  setScriptHost({start:(source:string,u:string,resources:unknown,encoding?:string,mode?:Record<string,unknown>)=>{
    turn=engine.scriptSession(source,{action:"start",url:u,resources,width:W,height:H,zoomUnit:100,
      layout:{url:u,textScalePercent:100,zoomUnit:100,...(mode??{})},engine:"bubblepop",...(encoding?{encoding}:{})});
    errors.push(...turn.errors);return turn;
  }} as never);
  const out:Partial<EngineRun>={variant:name,valid:false};
  try{
    const page=await prepareHTML(engine as never,url,undefined,undefined,{liberal:true}) as unknown as {title:string;source:string;
      request:(w:number,h:number,v?:Record<string,unknown>)=>{source:string;options:Record<string,unknown>};applyTurn:(t:unknown)=>boolean};
    out.load_ms=r1(performance.now()-t0);
    let clock=0;
    const shell=(scroll:number)=>({tabs:[{title:page.title??""}],active:0,address:url,cursor:0,focused:false,canBack:false,canForward:false,
      loading:false,scale:1,theme:"light",pages:1,scroll,pressed:""});
    const base=()=>page.request(W,H,{textScalePercent:100,zoomUnit:100}).options;
    const layered=(scroll=0)=>({...base(),shell:shell(scroll),checks:false,animationTime:clock,animationClicks:[]});
    const timed=(f:()=>unknown)=>{engine.frameWork(true);const s=performance.now();const v=f();return {v,ms:performance.now()-s,work:engine.frameWork()!};};
    const l1=timed(()=>engine.compileLayers(page.source,W,H,layered()));
    const l2=timed(()=>engine.compileLayers(page.source,W,H,layered()));
    out.first_ms=r1(l1.ms);out.second_ms=r1(l2.ms);out.second_layouts=l2.work.layouts;
    out.primitives=(l1.v as {page:{primitiveCount:number}}).page.primitiveCount;
    out.probe_ms=r1(timed(()=>engine.compile(page.source,W,H,base())).ms);
    out.no_probe_ms=r1(timed(()=>engine.compile(page.source,W,H,{...base(),checks:false})).ms);
    engine.compileLayers(page.source,W,H,layered());
    // Ticks: the page clock moves 16 ms a tick, as the window's would.
    const frameMs:number[]=[],turnMs:number[]=[];let layouts=0,recompiled=0,changed=0;
    for(let i=0;i<ticks;i++){
      let s=performance.now();
      if(turn){const t=engine.scriptSession("",{action:"advance",session:turn.session,ms:TICK_MS});errors.push(...t.errors);page.applyTurn(t);}
      turnMs.push(performance.now()-s);clock+=TICK_MS;
      const before=engine.frameWork()!;s=performance.now();
      engine.compileLayers(page.source,W,H,layered());
      frameMs.push(performance.now()-s);
      const after=engine.frameWork()!;
      const dl=after.layouts-before.layouts,dr=after.recompiled-before.recompiled;
      layouts+=dl;recompiled+=dr;if(dl||dr)changed++;
    }
    out.tick={n:ticks,median:pct(frameMs.map((f,i)=>f+turnMs[i]),0.5),p95:pct(frameMs.map((f,i)=>f+turnMs[i]),0.95),
      max:frameMs.length?r1(Math.max(...frameMs.map((f,i)=>f+turnMs[i]))):null,turn_median:pct(turnMs,0.5),layouts,recompiled,changed};
    // Scroll: a new band at each of 8 offsets.
    const scrollMs:number[]=[];const w0=engine.frameWork(true);void w0;
    for(let i=1;i<=8;i++){const s=performance.now();engine.compileLayers(page.source,W,H,layered(i*400));scrollMs.push(performance.now()-s);}
    out.scroll={n:8,median:pct(scrollMs,0.5),max:scrollMs.length?r1(Math.max(...scrollMs)):null,layouts:engine.frameWork()!.layouts};
    out.rss_mb=mb(Deno.memoryUsage().rss);
    out.valid=errors.length===0;
    if(errors.length)out.why=`page script errors: ${errors[0].slice(0,200)}`;
  }catch(e){out.why=`failed: ${String(e instanceof Error?e.message:e).slice(0,300)}`;}
  finally{setScriptHost(undefined);await server.shutdown();}
  out.run_ms=r1(performance.now()-t0);
  return out as EngineRun;
}

/** One variant on the engine, in a child process of its own, under the timing lock. */
async function engine(name:string,file:string,ticks:number,library:string):Promise<EngineRun> {
  return await locked(async()=>{
    const r=await new Deno.Command(Deno.execPath(),{args:["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-ffi",
      "--allow-read","--allow-ffi","--allow-env","--allow-net=127.0.0.1",fileURLToPath(import.meta.url),"--engine-one",name,file,String(ticks),library],
      stdout:"piped",stderr:"piped"}).output();
    const text=new TextDecoder().decode(r.stdout).trim().split("\n").at(-1)??"";
    try{return JSON.parse(text) as EngineRun;}
    catch{return {variant:name,valid:false,why:`no result: ${new TextDecoder().decode(r.stderr).slice(-300)}`} as EngineRun;}
  });
}

// ---------------------------------------------------------------- window, one variant
export type WindowRun={variant:string;valid:boolean;why?:string;present:string;watch_s:number;
  first_frame_ms:number|null;frames:number;frame_ms_p50:number|null;frame_ms_max:number|null;layout_ms_p50:number|null;
  gpu_ms_p50:number|null;gpu_ms_p95:number|null;pump_gap_max_ms:number|null;pump_gap_p50_ms:number|null;pumps_per_s:number|null;
  idle_check_ms:number|null;idle_checks:number;cpu_pct_idle:number|null;cpu_s:number;rss_mb_end:number|null;rss_mb_max:number|null;
  slow_calls:Record<string,number>;
  scroll?:{latency_p50:number|null;latency_p95:number|null;latency_max:number|null;events:number;frames:number;cpu_s:number;pump_gap_max_ms:number|null}};

type Sample={t:number;cpu:number;rss:number};
/** Run the window program; sample its CPU time and RSS every 250 ms; return its JSON lines. */
async function runWindow(app:string,args:string[],timeoutMs:number):Promise<{lines:Record<string,unknown>[];samples:Sample[];code:number;start:number}> {
  const bin=join(app,"native-webgpu-html-darwin-arm64");
  const child=new Deno.Command(bin,{args,cwd:app,stdout:"piped",stderr:"null",env:{FACTOIDAL_APP_NAME:"foafnaut"}}).spawn();
  const start=performance.now(),samples:Sample[]=[];
  const cpuTime=(s:string)=>{const p=s.split(/[:.]/).map(Number);return p.length===3?p[0]*60+p[1]+p[2]/100:p.length===4?p[0]*3600+p[1]*60+p[2]+p[3]/100:NaN;};
  let done=false;
  const sampler=(async()=>{
    while(!done){
      const r=await new Deno.Command("ps",{args:["-o","rss=,time=","-p",String(child.pid)],stdout:"piped",stderr:"null"}).output();
      const [rss,time]=new TextDecoder().decode(r.stdout).trim().split(/\s+/);
      // A process that has exited (a zombie) shows 0 CPU time: only rising samples count.
      const cpu=cpuTime(time??"");
      if(rss&&Number.isFinite(cpu)&&cpu>=(samples.at(-1)?.cpu??0))samples.push({t:performance.now()-start,cpu,rss:Number(rss)*1024});
      await new Promise(f=>setTimeout(f,250));
    }
  })();
  const timer=setTimeout(()=>{try{child.kill("SIGTERM");}catch{/* gone */}},timeoutMs);
  const text=await new Response(child.stdout).text();
  const status=await child.status;clearTimeout(timer);done=true;await sampler;
  const lines=text.split("\n").filter(l=>l.startsWith("{")).flatMap(l=>{try{return [JSON.parse(l)];}catch{return [];}});
  return {lines,samples,code:status.code,start};
}
const ofType=(lines:Record<string,unknown>[],type:string)=>lines.filter(l=>l.type===type) as Record<string,any>[];

async function windowOne(name:string,file:string,app:string,watch:number,present:string):Promise<WindowRun> {
  const view=present==="window"?[]:["--offscreen","--offscreen-size","1280x800@2"];
  const common=["--html",file,...view,"--perf-summary","--no-state","--no-splash"];
  const out:Partial<WindowRun>={variant:name,valid:false,present,watch_s:watch};
  const a=await locked(()=>runWindow(app,[...common,"--watch-sweep",String(watch)],(watch+60)*1000));
  const frames=ofType(a.lines,"native-html-frame"),summary=ofType(a.lines,"native-html-perf-summary")[0];
  const checks=ofType(a.lines,"native-html-checked");
  out.first_frame_ms=frames[0]?.t??null;out.frames=frames.length;
  out.frame_ms_p50=pct(frames.map(f=>f.totalMs),0.5);out.frame_ms_max=frames.length?Math.max(...frames.map(f=>f.totalMs)):null;
  out.layout_ms_p50=pct(frames.map(f=>f.layoutMs),0.5);
  out.gpu_ms_p50=summary?.gpu?.submitToDoneMsP50??null;out.gpu_ms_p95=summary?.gpu?.submitToDoneMsP95??null;
  out.pump_gap_max_ms=summary?.pumpGapAfterFirstFrameMs?.max??null;out.pump_gap_p50_ms=summary?.pumpGapAfterFirstFrameMs?.p50??null;
  out.pumps_per_s=summary&&out.first_frame_ms!==null?r1((summary.pumpGapAfterFirstFrameMs?.count??0)/Math.max(1,(summary.t-out.first_frame_ms)/1000)):null;
  out.idle_checks=checks.length;out.idle_check_ms=checks.length?Math.max(...checks.map(c=>c.drawMs)):null;
  out.slow_calls=Object.fromEntries(Object.entries((summary?.slowCalls??{}) as Record<string,{maxMs:number}>).map(([k,v])=>[k,v.maxMs]));
  // Idle CPU: the last 10 s of the watch (the page has settled: the zoom ends 9 s after load).
  const end=a.samples.at(-1),from=end?a.samples.filter(s=>s.t<=end.t-10000).at(-1):undefined;
  out.cpu_pct_idle=end&&from&&end.t>from.t?r1((end.cpu-from.cpu)/((end.t-from.t)/1000)*100):null;
  out.cpu_s=end?r1(end.cpu):0;out.rss_mb_end=end?mb(end.rss):null;out.rss_mb_max=a.samples.length?mb(Math.max(...a.samples.map(s=>s.rss))):null;
  // Scroll: 20 wheel steps of 120 rows, the interactive rule (no readback until idle).
  const b=await locked(()=>runWindow(app,[...common,"--scroll-sweep","--idle-checks-only"],90000));
  const sb=ofType(b.lines,"native-html-perf-summary")[0];
  out.scroll={latency_p50:sb?.inputLatency?.p50Ms??null,latency_p95:sb?.inputLatency?.p95Ms??null,latency_max:sb?.inputLatency?.maxMs??null,
    events:sb?.inputLatency?.count??0,frames:ofType(b.lines,"native-html-frame").length,cpu_s:b.samples.at(-1)?.cpu??0,
    pump_gap_max_ms:sb?.pumpGapAfterFirstFrameMs?.max??null};
  out.valid=a.code===0&&frames.length>0&&!!summary;
  if(!out.valid)out.why=frames.length?`exit ${a.code}`:"no frame presented (a window that can not present waits: use offscreen)";
  return out as WindowRun;
}

// ---------------------------------------------------------------- the ranking
export type Bisect={engine_commit?:string;app?:string;measured:string;ticks:number;variants:Record<string,{bytes:number;feature:string;base?:string;adds?:boolean;
  engine?:EngineRun;window?:WindowRun}>};

/** The metrics of the table: [label, path in a variant's record, unit]. */
const METRICS:[string,string,string][]=[
  ["first frame","engine.first_ms","ms"],["probe frame","engine.probe_ms","ms"],["tick","engine.tick.median","ms"],
  ["scroll band","engine.scroll.median","ms"],["prims","engine.primitives",""],
  ["win first frame","window.first_frame_ms","ms"],["win frame","window.frame_ms_p50","ms"],["GPU","window.gpu_ms_p50","ms"],
  ["pump gap max","window.pump_gap_max_ms","ms"],["idle CPU","window.cpu_pct_idle","%"],["RSS","window.rss_mb_max","MB"],
  ["scroll p95","window.scroll.latency_p95","ms"],
];
const at=(o:unknown,path:string)=>path.split(".").reduce<unknown>((x,k)=>x==null?undefined:(x as Record<string,unknown>)[k],o) as number|null|undefined;

/** Feature -> added cost: for each variant with a base, (with feature) - (without), per metric. */
export function rank(run:Bisect){
  const rows=[] as {feature:string;variant:string;base:string;delta:Record<string,number|null>;key:number}[];
  for(const [name,v] of Object.entries(run.variants)){
    if(!v.base||!run.variants[v.base])continue;
    const withF=v.adds?v:run.variants[v.base],without=v.adds?run.variants[v.base]:v;
    const delta:Record<string,number|null>={};
    for(const [label,path] of METRICS){const a=at(withF,path),b=at(without,path);delta[label]=typeof a==="number"&&typeof b==="number"?r1(a-b):null;}
    // Rank by the window's frame cost when measured, else the engine's first frame and tick.
    const key=(delta["win frame"]??0)*1+(delta["GPU"]??0)+(delta["first frame"]??0)+(delta["tick"]??0)*10;
    rows.push({feature:v.feature,variant:v.adds?`${name} vs ${v.base}`:`${v.base} vs ${name}`,base:v.base,delta,key});
  }
  return rows.sort((a,b)=>b.key-a.key);
}

export function markdown(run:Bisect):string {
  const s=(x:number|null|undefined,u="")=>x==null?"–":`${x}${u}`;
  const sd=(x:number|null|undefined)=>x==null?"–":(x>0?"+":"")+x;
  const labels=METRICS.map(m=>m[0]);
  let md=`Spinal Tap variants (${run.measured}; engine ${run.engine_commit?.slice(0,9)??"?"}${run.app?`, window ${run.app}`:""}; ${run.ticks} ticks)\n\n`;
  md+="| variant | bytes | "+labels.join(" | ")+" |\n|---|---:|"+labels.map(()=>"---:").join("|")+"|\n";
  for(const [name,v] of Object.entries(run.variants))md+=`| ${name} | ${v.bytes} | `+METRICS.map(([,p,u])=>s(at(v,p),u)).join(" | ")+" |\n";
  md+="\nFeature → added cost (with the feature minus without it)\n\n| feature | pair | "+labels.join(" | ")+" |\n|---|---|"+labels.map(()=>"---:").join("|")+"|\n";
  for(const r of rank(run))md+=`| ${r.feature} | ${r.variant} | `+labels.map(l=>sd(r.delta[l])).join(" | ")+" |\n";
  return md;
}

export async function bisect({only,ticks=120,app,watch=25,present="offscreen",library=defaultLibrary,log=console.log}:
  {only?:string[];ticks?:number;app?:string;watch?:number;present?:string;library?:string;log?:(s:string)=>void}={}):Promise<Bisect> {
  const made=await generate({library,out:defaultOut,only});
  const run:Bisect={measured:new Date().toISOString(),ticks,...(app?{app}:{}),variants:{}};
  for(const [name,v] of Object.entries(made)){
    const e=await engine(name,v.file,ticks,library);
    run.variants[name]={bytes:v.bytes,feature:v.feature,...(v.base?{base:v.base}:{}),...(v.adds?{adds:true}:{}),engine:e};
    let line=`${name.padEnd(14)} engine: first ${e.first_ms} ms, probe ${e.probe_ms} ms, tick ${e.tick?.median} ms (layouts ${e.tick?.layouts}, recompiled ${e.tick?.recompiled}), scroll ${e.scroll?.median} ms, ${e.primitives} prims${e.valid?"":" INVALID "+e.why}`;
    if(app){
      const w=await windowOne(name,v.file,app,watch,present);run.variants[name].window=w;
      line+=`\n${"".padEnd(14)} window: first frame ${w.first_frame_ms} ms, ${w.frames} frames p50 ${w.frame_ms_p50} ms, GPU p50 ${w.gpu_ms_p50} ms, pump gap max ${w.pump_gap_max_ms} ms, idle CPU ${w.cpu_pct_idle}%, RSS ${w.rss_mb_max} MB, scroll p95 ${w.scroll?.latency_p95} ms${w.valid?"":" INVALID "+w.why}`;
    }
    log(line);
  }
  try{const {loadHTML}=await import("./native_html_engine.ts");const e=await loadHTML(library) as unknown as {engineBuild?:()=>{commit:string}};run.engine_commit=e.engineBuild?.().commit;}catch{/* old engine */}
  return run;
}

if(import.meta.main){
  const args=Deno.args,opt=(n:string)=>{const i=args.indexOf(n);return i>=0?args[i+1]:undefined;};
  if(args[0]==="--engine-one"){console.log(JSON.stringify(await engineOne(args[1],args[2],Number(args[3]),args[4])));Deno.exit(0);}
  const run=await bisect({only:opt("--only")?.split(","),ticks:Number(opt("--ticks")??120),app:opt("--app"),watch:Number(opt("--watch")??25),
    present:opt("--present")??"offscreen",library:opt("--engine")??defaultLibrary});
  const md=markdown(run);
  const outFile=opt("--out")??join(here,".build/spinal-bisect/run.json"),mdFile=opt("--md")??join(here,".build/spinal-bisect/run.md");
  Deno.writeTextFileSync(outFile,JSON.stringify(run,null,1)+"\n");Deno.writeTextFileSync(mdFile,md);
  console.log("\n"+md);
}
void VARIANTS;void resolve;
