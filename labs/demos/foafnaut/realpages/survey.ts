// The real-page survey: everyday pages, probed live, on one Foafnaut engine library, with the
// numbers that say whether a page is usable (issue 450). One summary.json per run; pictures
// and logs beside it for a short-lived look (never into git: the pages are copyright).
//
//   deno run -A labs/demos/foafnaut/realpages/survey.ts --engine LIB --out DIR
//     [--platform macos|linux] [--host LAB_DIR] [--pages FILE] [--only id,id] [--watch 15]
//     [--timeout 180] [--retries 2] [--chrome PATH | --no-chrome] [--release TAG] [--lock FILE]
//
// macOS (a window library and a GPU): for each page a watch run of run_html.ts off screen
// (first frame, first layout, GPU per frame, idle CPU for --watch seconds after the first
// frame, the longest script turn, what liberal mode skipped, a picture at the end) and a
// scroll run (--scroll-sweep: input latency and composite times), then headless Chrome's
// picture of the same page area and the layout similarity of the two (visual.ts).
// Linux (no window): textnaut --dump --timing on the native library (load, layout, rows,
// links, wall, CPU, peak memory).
// Every run: the exit and how it ended. A page whose own fetch fails (after --retries more
// tries) is "unreachable", not a failure of the browser; a run that ends by a signal or an
// error of the browser is a crash.
// --host is the lab directory whose run_html.ts drives the engine (default: this one). Pass a
// checkout of the engine's own commit (realpages/setup-host.sh makes one runnable); options
// that host lacks (--shot-at-end, --liberal-report) are left out and the summary says so.
// --lock FILE: hold an exclusive lock on FILE during each engine run (on the shared Mac,
// /tmp/foafnaut-timing.lock, so timings do not overlap with other agents' runs).
import {cpuShare,FETCH_FAILURE,overBudget,parseScroll,parseTextnaut,parseWatch,psSeconds,verdictOf,type Budgets} from "./metrics.ts";
import {pageSimilarity} from "./visual.ts";

const here=decodeURIComponent(new URL("./",import.meta.url).pathname);
const args=[...Deno.args];
const opt=(name:string,fallback?:string)=>{const i=args.indexOf(name);return i<0?fallback:args[i+1];};
const flag=(name:string)=>args.includes(name);
if(flag("--help")||!opt("--engine")||!opt("--out")){
  console.log("survey.ts --engine LIB --out DIR [--platform macos|linux] [--host LAB_DIR] [--pages FILE] [--only id,id] [--watch 15] [--timeout 180] [--retries 2] [--chrome PATH | --no-chrome] [--release TAG] [--lock FILE]");
  Deno.exit(flag("--help")?0:2);
}
const engine=opt("--engine")!,out=opt("--out")!;
const platform=opt("--platform",Deno.build.os==="darwin"?"macos":"linux")!;
const host=opt("--host",decodeURIComponent(new URL("../",import.meta.url).pathname))!.replace(/\/?$/,"/");
const pagesFile=opt("--pages",here+"pages.json")!;
const only=opt("--only")?.split(",");
const watchS=Number(opt("--watch","15")),timeoutS=Number(opt("--timeout","180")),retries=Number(opt("--retries","2"));
const lockFile=opt("--lock");
const chrome=flag("--no-chrome")||platform!=="macos"?undefined:opt("--chrome",Deno.env.get("CHROME")??"/Applications/Google Chrome.app/Contents/MacOS/Google Chrome");
const UA_IPHONE="Mozilla/5.0 (iPhone; CPU iPhone OS 18_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/18.0 Mobile/15E148 Safari/604.1";

type Page={id:string;url:string;viewport?:string;mobile?:boolean;scripts?:boolean;scroll?:boolean;budgets?:Budgets;note?:string};
const spec=JSON.parse(await Deno.readTextFile(pagesFile)) as {defaults:{viewport:string;budgets:Budgets};pages:Page[]};
const pages=spec.pages.filter(p=>!only||only.includes(p.id));
await Deno.mkdir(`${out}/shots`,{recursive:true});await Deno.mkdir(`${out}/logs`,{recursive:true});

const hostSource=await Deno.readTextFile(host+"run_html.ts").catch(()=>"");
const caps={shotAtEnd:hostSource.includes('"--shot-at-end"'),liberalReport:hostSource.includes('"--liberal-report"')};
const git=async(dir:string,...a:string[])=>{try{const o=await new Deno.Command("git",{args:["-C",dir,...a],stdout:"piped",stderr:"null"}).output();return o.success?new TextDecoder().decode(o.stdout).trim():null;}catch{return null;}};
const sha256=async(path:string)=>Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256",await Deno.readFile(path)))).map(b=>b.toString(16).padStart(2,"0")).join("");

type Run={rc:number|null;signal:string|null;timedOut:boolean;wall:number;firstAt:number|null;samples:[number,number,number][];log:string};
/** Run a command with its output to logPath; sample CPU seconds and RSS of the process every
250 ms; note the wall time of the first line containing `first`. */
async function run(cmd:string[],logPath:string,first:string|null,cwd?:string):Promise<Run>{
  let lock:Deno.FsFile|undefined;
  if(lockFile){lock=await Deno.open(lockFile,{create:true,write:true});await lock.lock(true);}
  try{
    const t0=performance.now(),now=()=>(performance.now()-t0)/1000;
    const child=new Deno.Command(cmd[0],{args:cmd.slice(1),cwd,stdout:"piped",stderr:"piped",stdin:"null"}).spawn();
    let text="",firstAt:number|null=null,timedOut=false;
    const dec=new TextDecoder();
    const pump=async(stream:ReadableStream<Uint8Array>)=>{for await(const chunk of stream){
      text+=dec.decode(chunk,{stream:true});
      if(first&&firstAt===null&&text.includes(first))firstAt=now();
    }};
    const pumps=Promise.all([pump(child.stdout),pump(child.stderr)]);
    const samples:[number,number,number][]=[];
    let done=false;
    const status=child.status.then(s=>{done=true;return s;});
    const killer=setTimeout(()=>{timedOut=true;try{child.kill("SIGTERM");}catch{/* gone */}
      setTimeout(()=>{if(!done)try{child.kill("SIGKILL");}catch{/* gone */}},3000);},timeoutS*1000);
    while(!done){
      try{
        const o=await new Deno.Command("ps",{args:["-o","time=,rss=","-p",String(child.pid)],stdout:"piped",stderr:"null"}).output();
        const [t,rss]=new TextDecoder().decode(o.stdout).trim().split(/\s+/);
        if(t&&rss)samples.push([now(),psSeconds(t),Number(rss)*1024]);
      }catch{/* the process ended */}
      await Promise.race([status,new Promise(r=>setTimeout(r,250))]);
    }
    clearTimeout(killer);
    const s=await status;await pumps;
    await Deno.writeTextFile(logPath,text);
    return {rc:s.code,signal:s.signal??null,timedOut,wall:now(),firstAt,samples,log:text};
  } finally {lock?.close();}
}
const firstError=(log:string)=>log.split("\n").find(l=>/^(error|Error|Uncaught|panic|thread '|Segmentation|Abort|Native HTML GPU)/.test(l))?.slice(0,200)??null;
const rssPeak=(r:Run)=>Math.round(Math.max(0,...r.samples.map(s=>s[2]))/1048576);
const urlOf=(p:Page)=>p.url.startsWith("lab:")?new URL(p.url.slice(4),"file://"+host).href:p.url;

async function reachable(url:string):Promise<string|null>{
  if(!/^https?:/.test(url))return null;
  let why="";
  for(let i=0;i<=retries;i++){
    try{
      const r=await fetch(url,{redirect:"follow",signal:AbortSignal.timeout(20000),headers:{"user-agent":"Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) Foafnaut-survey"}});
      await r.body?.cancel();
      if(r.status<500&&r.status!==429)return null;
      why=`HTTP ${r.status}`;
    }catch(e){why=String(e).slice(0,160);}
    await new Promise(r=>setTimeout(r,5000*(i+1)));
  }
  return why;
}

const deno=Deno.execPath();
const DENO_RUN=[deno,"run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A"];
type Row=Record<string,unknown>;

async function macPage(p:Page,row:Row){
  const [w,h]=(p.viewport??spec.defaults.viewport).split("x").map(Number);
  const url=urlOf(p),shot=`${out}/shots/${p.id}-foafnaut.png`;
  const base=[...DENO_RUN,host+"run_html.ts","--native-engine",engine,"--offscreen","--offscreen-size",`${w}x${h}@1`,"--text-size","100","--no-state",
    "--be-liberal-in-what-we-accept","--perf-summary",...(p.scripts===false?["--no-scripts"]:[]),"--url",url];
  let watch:Run|undefined;
  for(let attempt=1;attempt<=retries+1;attempt++){
    row.attempts=attempt;
    try{await Deno.remove(shot);}catch{/* none */}
    watch=await run([...base,"--shot",shot,...(caps.shotAtEnd?["--shot-at-end"]:[]),...(caps.liberalReport?["--liberal-report","json"]:[]),"--watch-sweep",String(watchS)],
      `${out}/logs/${p.id}.watch.log`,'"native-html-presented"',host);
    const fetchFailed=watch.firstAt===null&&!watch.timedOut&&watch.rc!==0&&FETCH_FAILURE.test(watch.log);
    if(!fetchFailed)break;
    if(attempt===retries+1){row.state="unreachable";row.unreachable_reason=firstError(watch.log)??"page fetch failed";return;}
    await new Promise(r=>setTimeout(r,5000*attempt));
  }
  const wf=parseWatch(watch!.log);
  const cpu=watch!.firstAt!==null?cpuShare(watch!.samples.map(s=>[s[0],s[1]]),watch!.firstAt):null;
  Object.assign(row,{exit_code:watch!.rc,first_frame_s:watch!.firstAt===null?null:Math.round(watch!.firstAt*10)/10,
    first_layout_ms:wf.first_layout_ms,prims:wf.prims,gpu_p50_ms:wf.gpu_p50_ms,gpu_p95_ms:wf.gpu_p95_ms,
    cpu_idle_pct:cpu?.pct??null,cpu_window_s:cpu?.window_s??null,script_turns:wf.script_turns,script_turn_max_ms:wf.script_turn_max_ms,
    scripts_off:p.scripts===false?"--no-scripts":wf.scripts_off,page_errors:wf.page_errors,
    skips_count:caps.liberalReport?wf.skips.length:null,skips:caps.liberalReport?wf.skips:null,chrome_top:wf.chrome_top,
    shot:wf.shot?(caps.shotAtEnd?"end":"first idle frame"):null,rss_peak_mb:rssPeak(watch!),wall_s:Math.round(watch!.wall*10)/10});
  if(watch!.timedOut&&watch!.firstAt===null){row.state="timeout";return;}
  if(watch!.signal&&!watch!.timedOut){row.state="crash";row.crash_reason=`signal ${watch!.signal}`;return;}
  if(watch!.rc!==0&&!watch!.timedOut){row.state="crash";row.crash_reason=firstError(watch!.log)??`exit ${watch!.rc}`;return;}
  row.state="ok";
  if(p.scroll!==false){
    const sc=await run([...base,"--scroll-sweep","--idle-checks-only"],`${out}/logs/${p.id}.scroll.log`,null,host);
    const sf=parseScroll(sc.log);
    Object.assign(row,{scroll_latency_p50_ms:sf.latency_p50_ms,scroll_latency_p95_ms:sf.latency_p95_ms,
      scroll_composite_p50_ms:sf.composite_p50_ms,scroll_composite_p95_ms:sf.composite_p95_ms,scroll_ratchet:sf.ratchet,scroll_exit_code:sc.rc});
    row.rss_peak_mb=Math.max(row.rss_peak_mb as number,rssPeak(sc));
    if(sc.signal&&!sc.timedOut){row.state="crash";row.crash_reason=`scroll run: signal ${sc.signal}`;}
    else if(sc.rc!==0&&!sc.timedOut&&!sf.ratchet&&!FETCH_FAILURE.test(sc.log)){row.state="crash";row.crash_reason="scroll run: "+(firstError(sc.log)??`exit ${sc.rc}`);}
    else if(sc.timedOut)row.scroll_timed_out=true;
  }
  if(chrome&&wf.shot){
    const top=wf.chrome_top??65,ref=`${out}/shots/${p.id}-chrome.png`,profile=await Deno.makeTempDir();
    try{
      await new Deno.Command(chrome,{args:["--headless=new",`--user-data-dir=${profile}`,"--disable-gpu","--hide-scrollbars","--force-device-scale-factor=1",
        "--no-first-run",...(p.mobile?[`--user-agent=${UA_IPHONE}`]:[]),"--virtual-time-budget=8000",`--window-size=${w},${h-top}`,`--screenshot=${ref}`,url],
        stdout:"null",stderr:"null",signal:AbortSignal.timeout(90000)}).output();
      row.layout_similarity=await pageSimilarity(await Deno.readFile(shot),await Deno.readFile(ref),top);
    }catch(e){row.layout_similarity=null;row.chrome_error=String(e).slice(0,160);}
    finally{await Deno.remove(profile,{recursive:true}).catch(()=>{});}
  }
}

async function linuxPage(p:Page,row:Row){
  const [w]=(p.viewport??spec.defaults.viewport).split("x").map(Number);
  const cmd=[deno,"run","--no-prompt","--allow-read","--allow-ffi","--allow-net","--allow-env",`--import-map=${host}textnaut/import_map.json`,
    host+"textnaut/textnaut.ts","--dump","--width",String(Math.max(40,Math.round(w/8))),"--timing","--engine",engine,...(p.scripts===false?["--no-scripts"]:[]),urlOf(p)];
  let r:Run|undefined;
  for(let attempt=1;attempt<=retries+1;attempt++){
    row.attempts=attempt;
    r=await run(cmd,`${out}/logs/${p.id}.textnaut.log`,"timing: engine",host);
    const tf=parseTextnaut(r.log);
    if(!(r.rc!==0&&!r.timedOut&&tf.refused&&FETCH_FAILURE.test(tf.refused)))break;
    if(attempt===retries+1){row.state="unreachable";row.unreachable_reason=tf.refused;return;}
    await new Promise(res=>setTimeout(res,5000*attempt));
  }
  const tf=parseTextnaut(r!.log);
  Object.assign(row,{exit_code:r!.rc,first_frame_s:r!.firstAt===null?null:Math.round(r!.firstAt*10)/10,load_ms:tf.load_ms,first_layout_ms:tf.layout_ms,
    rows:tf.rows,links:tf.links,scripts_off:p.scripts===false?"--no-scripts":tf.scripts==="off"?"off":null,
    cpu_s:r!.samples.length?r!.samples[r!.samples.length-1][1]:null,rss_peak_mb:rssPeak(r!),wall_s:Math.round(r!.wall*10)/10,refused:tf.refused});
  if(r!.timedOut){row.state="timeout";return;}
  if(r!.signal){row.state="crash";row.crash_reason=`signal ${r!.signal}`;return;}
  // A refusal is the browser's answer (exit 1 with a reason), not a crash; any other exit is.
  if(r!.rc!==0&&!tf.refused){row.state="crash";row.crash_reason=firstError(r!.log)??`exit ${r!.rc}`;return;}
  row.state=tf.refused?"refused":"ok";
}

const started=new Date().toISOString();
const rows:Row[]=[];
for(const p of pages){
  const row:Row={id:p.id,url:p.url,viewport:p.viewport??spec.defaults.viewport,mobile:!!p.mobile};
  const t=performance.now();
  const why=await reachable(urlOf(p));
  if(why){row.state="unreachable";row.unreachable_reason=why;}
  else if(platform==="macos")await macPage(p,row);else await linuxPage(p,row);
  row.crashed=row.state==="crash";
  row.verdict=platform==="macos"?verdictOf({crashed:row.crashed as boolean,unreachable:row.state==="unreachable",first_frame_s:(row.first_frame_s??null) as number|null,
    prims:(row.prims??null) as number|null,scroll_latency_p95_ms:(row.scroll_latency_p95_ms??null) as number|null,cpu_idle_pct:(row.cpu_idle_pct??null) as number|null,
    script_turn_max_ms:(row.script_turn_max_ms??null) as number|null})
    :row.state==="ok"?((row.first_frame_s as number)>10?"slow":"usable"):row.state==="refused"?"blank":row.state;
  row.over_budget=overBudget(row,{...spec.defaults.budgets,...p.budgets});
  rows.push(row);
  console.log(`${p.id}: ${row.verdict} (${row.state}) in ${Math.round((performance.now()-t)/1000)} s`+(row.crash_reason?`: ${row.crash_reason}`:""));
}
const count=(v:string)=>rows.filter(r=>r.verdict===v).length;
const summary={schema:"foafnaut-realpages/1",platform,release:opt("--release")??null,
  engine:{file:engine.slice(engine.lastIndexOf("/")+1),sha256:await sha256(engine)},
  host:{commit:await git(host,"rev-parse","HEAD"),shot_at_end:caps.shotAtEnd,liberal_report:caps.liberalReport},
  survey_commit:await git(here,"rev-parse","HEAD"),runner:{os:Deno.build.os,arch:Deno.build.arch,deno:Deno.version.deno},
  started,finished:new Date().toISOString(),watch_s:watchS,timeout_s:timeoutS,
  totals:{pages:rows.length,usable:count("usable"),slow:count("slow"),unusable:count("unusable"),blank:count("blank"),timeout:count("timeout"),crash:count("crash"),unreachable:count("unreachable")},
  pages:rows};
await Deno.writeTextFile(`${out}/summary.json`,JSON.stringify(summary,null,1)+"\n");
console.log(`summary: ${out}/summary.json; ${JSON.stringify(summary.totals)}`);
