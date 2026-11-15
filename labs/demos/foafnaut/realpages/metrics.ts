// The numbers of one real-page run, read from what run_html.ts (--perf-summary, --liberal-report
// json) and textnaut (--timing) print. Pure: no I/O, so realpages_test.ts checks it on
// logs made up for the test.

export type Skip={feature:string;message:string};
export type WatchFacts={
  first_layout_ms:number|null;prims:number|null;frames:number;chrome_top:number|null;
  gpu_p50_ms:number|null;gpu_p95_ms:number|null;
  script_turns:number;script_turn_max_ms:number|null;script_ms_total:number;scripts_off:string|null;
  page_errors:number;skips:Skip[];shot:boolean;
  /** Trips of the console log gate (native-html-log-flood events) and the first trip's most-said messages. */
  log_floods:number;log_flood_top:string|null;
};
export type ScrollFacts={events:number|null;latency_p50_ms:number|null;latency_p95_ms:number|null;
  composite_p50_ms:number|null;composite_p95_ms:number|null;lean_frames:number|null;ratchet:boolean};
export type TextnautFacts={load_ms:number|null;layout_ms:number|null;rows:number|null;links:number|null;scripts:string|null;refused:string|null};

const events=(log:string)=>{
  const out:Record<string,unknown>[]=[];
  for(const line of log.split("\n")){
    if(!line.startsWith("{\"type\":"))continue;
    try{out.push(JSON.parse(line));}catch{/* a line cut short */}
  }
  return out;
};
const num=(s:string|undefined)=>s===undefined||s==="null"?null:Number(s);
const round=(x:number,d=1)=>Math.round(x*10**d)/10**d;

export function parseWatch(log:string):WatchFacts{
  const ev=events(log);
  const frames=ev.filter(e=>e.type==="native-html-frame");
  const scripts=ev.filter(e=>e.type==="native-html-script");
  const skips=ev.filter(e=>e.type==="native-html-skip");
  const f0=frames[0] as {layoutMs?:number;primitives?:number;layers?:{top?:number}}|undefined;
  const gpu=/submit to done p50 ([\d.]+) ms, p95 ([\d.]+)/.exec(log);
  const turns=scripts.map(s=>Number(s.leanMs)||0);
  const text=log.split("\n").filter(l=>!l.startsWith("{"));
  const off=skips.map(s=>String(s.message??"")).find(m=>/scriptSession: document HTML exceeds/.test(m));
  const seen=new Set<string>();
  const list:Skip[]=[];
  for(const s of skips){
    const k=`${s.feature}\u0000${s.message}`;if(seen.has(k))continue;seen.add(k);
    list.push({feature:String(s.feature??""),message:String(s.message??"").slice(0,160)});
  }
  return {
    first_layout_ms:f0?.layoutMs??null,prims:f0?.primitives??null,frames:frames.length,chrome_top:f0?.layers?.top??null,
    gpu_p50_ms:gpu?Number(gpu[1]):null,gpu_p95_ms:gpu?Number(gpu[2]):null,
    script_turns:turns.length,script_turn_max_ms:turns.length?Math.round(Math.max(...turns)):null,
    script_ms_total:Math.round(turns.reduce((a,b)=>a+b,0)),scripts_off:off?"document HTML over 1 MiB":null,
    page_errors:text.filter(l=>l.startsWith("page error")||l.includes("Uncaught")).length,
    skips:list,shot:ev.some(e=>e.type==="native-html-shot"),
    ...logFloods(log),
  };
}

/** Trips of the log gate in a run's output (run_html.ts and Textnaut write one
{"type":"native-html-log-flood",lines,top} line per trip). */
export function logFloods(log:string):{log_floods:number;log_flood_top:string|null}{
  const trips=events(log).filter(e=>e.type==="native-html-log-flood");
  const top=trips[0]?.top;
  return {log_floods:trips.length,log_flood_top:top===undefined?null:JSON.stringify(top).slice(0,160)};
}

export function parseScroll(log:string):ScrollFacts{
  const a=/input latency: (\d+) events, p50 ([\w.]+) ms, p95 ([\w.]+) ms/.exec(log);
  const b=/scroll presents with no Lean call: (\d+), totalMs p50 ([\w.]+), p95 ([\w.]+)/.exec(log);
  const c=/frames: (\d+) presented/.exec(log);
  return {events:a?Number(a[1]):null,latency_p50_ms:num(a?.[2]),latency_p95_ms:num(a?.[3]),
    composite_p50_ms:num(b?.[2]),composite_p95_ms:num(b?.[3]),lean_frames:c?Number(c[1]):null,
    ratchet:/frame cost ratchet/.test(log)};
}

export function parseTextnaut(stderr:string):TextnautFacts{
  const t=/timing: engine \w+; start \d+ ms; load (\d+) ms; layout (\d+) ms; cells \d+ ms; rows (\d+); links (\d+); scripts (\w+)/.exec(stderr);
  const r=/textnaut: page refused: [^\n]*?: ([^\n]*)/.exec(stderr);
  return {load_ms:num(t?.[1]),layout_ms:num(t?.[2]),rows:num(t?.[3]),links:num(t?.[4]),scripts:t?.[5]??null,refused:r?r[1].slice(0,200):null};
}

/** A failure to fetch the page itself (not a crash of the browser): the run is retried and
then the page is "unreachable". */
export const FETCH_FAILURE=/fetch failed|error sending request|dns error|failed to lookup address|Connection refused|Connection reset|tcp connect error|timed out|certificate|HTTP (?:403|429|5\d\d)\b/i;

/** CPU share between two samples of a process [wall s, cpu s], in percent of one core. The
samples are cut to the ones where CPU time grows (ps can report a smaller value early). */
export function cpuShare(samples:[number,number][],from:number):{pct:number;window_s:number}|null{
  const good:[number,number][]=[];let max=0;
  for(const s of samples)if(s[1]>=max){good.push(s);max=s[1];}
  if(good.length<2)return null;
  const a=good.reduce((best,s)=>Math.abs(s[0]-from)<Math.abs(best[0]-from)?s:best),b=good[good.length-1];
  if(b[0]-a[0]<1)return null;
  return {pct:Math.round(100*(b[1]-a[1])/(b[0]-a[0])),window_s:round(b[0]-a[0])};
}

/** ps -o time= : [[dd-]hh:]mm:ss[.xx] */
export function psSeconds(t:string):number{
  const [days,rest]=t.includes("-")?t.split("-"):["0",t];
  return rest.split(":").map(Number).reduce((a,x)=>a*60+x,0)+Number(days)*86400;
}

export type Budgets=Record<string,number>;
export type Verdict="usable"|"slow"|"unusable"|"blank"|"timeout"|"crash"|"unreachable";
/** Worse verdicts rank higher; unreachable is not ranked (the network, not the browser). */
export const VERDICT_RANK:Record<Verdict,number>={usable:0,slow:1,unusable:2,blank:3,timeout:4,crash:5,unreachable:-1};

/** The automatic verdict. Thresholds, in order: crash (the process ended by a signal or
with an error of its own), timeout (no first frame), blank (fewer than 20 primitives),
unusable (a scroll waits over 5 s at p95, or the first frame is over 60 s), slow (first frame
over 10 s, scroll p95 over 1 s, idle CPU over 50%, or a script turn over 5 s), else usable. */
export function verdictOf(r:{crashed:boolean;unreachable:boolean;first_frame_s:number|null;prims:number|null;
  scroll_latency_p95_ms:number|null;cpu_idle_pct:number|null;script_turn_max_ms:number|null}):Verdict{
  if(r.unreachable)return "unreachable";
  if(r.crashed)return "crash";
  if(r.first_frame_s===null)return "timeout";
  if((r.prims??0)<20)return "blank";
  if((r.scroll_latency_p95_ms??0)>5000||r.first_frame_s>60)return "unusable";
  if(r.first_frame_s>10||(r.scroll_latency_p95_ms??0)>1000||(r.cpu_idle_pct??0)>50||(r.script_turn_max_ms??0)>5000)return "slow";
  return "usable";
}

/** Budget names are summary fields; a field over its budget is listed (information, not a failure). */
export function overBudget(row:Record<string,unknown>,budgets:Budgets):string[]{
  const out:string[]=[];
  for(const [k,limit] of Object.entries(budgets)){
    const v=row[k];
    if(typeof v==="number"&&v>limit)out.push(`${k} ${v} > ${limit}`);
  }
  return out;
}
