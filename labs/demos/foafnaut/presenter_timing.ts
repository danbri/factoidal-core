// Interleaved A/B timing on the Mac. No timing is taken by importing this module.
// deno run -A presenter_timing.ts --engine LIB --snapshots DIR --out DIR
// The input preload gives fixed deadlines after first paint, not hardware enqueue times.
// Ordinary sweeps.sh remains the independent pixel/cost oracle.
export function percentile(values: number[], q: number): number | null {
  if (!values.length) return null;
  const sorted = [...values].sort((a,b)=>a-b);
  return sorted[Math.max(0,Math.ceil(sorted.length*q)-1)];
}
export function distribution(values: number[]) {
  return {count:values.length,p50Ms:percentile(values,.5),p95Ms:percentile(values,.95),
    p99Ms:values.length>=100?percentile(values,.99):null,maxMs:values.length?Math.max(...values):null};
}
export function spread(values: number[]) {
  const mean=values.reduce((a,b)=>a+b,0)/values.length;
  return {runs:values.length,medianMs:percentile(values,.5),worstMs:values.length?Math.max(...values):null,
    minMs:values.length?Math.min(...values):null,
    cv:values.length&&mean?Math.sqrt(values.reduce((s,v)=>s+(v-mean)**2,0)/values.length)/mean:null};
}
type RecordLine=Record<string,unknown>;
export function parseRecords(log:string):RecordLine[] {
  return log.split("\n").flatMap(line=>{try{const x=JSON.parse(line);return typeof x==="object"&&x!==null?[x]:[];}catch{return [];}});
}
export function samples(records:RecordLine[]) {
  return records.filter(r=>r.type==="native-html-input-latency"&&(r.kind===11||r.kind==="scroll")&&typeof r.ms==="number")
    .map(r=>({ms:Number(r.ms),end:Number(r.t),start:Number(r.t)-Number(r.ms),
      inputEpochMs:typeof r.inputEpochMs==="number"?r.inputEpochMs:null}));
}

async function main() {
  const args=[...Deno.args];
  const opt=(name:string,otherwise?:string)=>{const i=args.indexOf(name);return i<0?otherwise:args[i+1];};
  if(args.includes("--help")){
    console.log("presenter_timing.ts --engine LIB --snapshots DIR --out DIR [--runs 5] [--only w3c-flexbox,wp-spinal,wp-us,synthetic] [--timeout 180] [--seconds 15]");
    return;
  }
  const engine=opt("--engine"),snapshots=opt("--snapshots"),out=opt("--out");
  if(!engine||!snapshots||!out)throw new Error("--engine, --snapshots and --out are required");
  if(Deno.build.os!=="darwin")throw new Error("The presenter timing comparison requires macOS");
  const runs=Number(opt("--runs","5")),seconds=Number(opt("--seconds","15")),timeout=Number(opt("--timeout","180"));
  if(!Number.isInteger(runs)||runs<5||!Number.isFinite(seconds)||seconds<8||!Number.isFinite(timeout)||timeout<=seconds)
    throw new Error("Need at least five runs, eight seconds per run and a longer timeout");
  const here=new URL("./",import.meta.url);
  const path=(name:string)=>decodeURIComponent(new URL(name,here).pathname);
  const chosen=(opt("--only","w3c-flexbox,wp-spinal,wp-us,synthetic")!).split(",");
  const spec=JSON.parse(await Deno.readTextFile(new URL("./realpages/pages.json",here))) as {
    pages:{id:string;url:string;snapshot?:string;viewport?:string}[];defaults:{viewport:string}};
  type Scenario={id:string;url:string;snapshot:string|null;busy:boolean;viewport:string};
  const scenarios:Scenario[]=[];
  for(const id of chosen){
    if(id==="synthetic"){
      scenarios.push({id,url:new URL("./fixtures/presenter/busy.html",here).href,snapshot:null,busy:true,viewport:"1280x800"});
      continue;
    }
    const page=spec.pages.find(p=>p.id===id);if(!page)throw new Error(`Unknown page ${id}`);
    const found:string[]=[];
    for await(const site of Deno.readDir(snapshots))if(site.isDirectory)
      for await(const f of Deno.readDir(`${snapshots}/${site.name}`))
        if(f.name.startsWith((page.snapshot??id)+"-")&&/-\d{8}\.zip$/.test(f.name))found.push(`${snapshots}/${site.name}/${f.name}`);
    const snapshot=found.sort().at(-1);if(!snapshot)throw new Error(`No snapshot for ${id}; this run must not fall back to live content`);
    for(const busy of [false,true])scenarios.push({id,url:page.url,snapshot,busy,viewport:page.viewport??spec.defaults.viewport});
  }
  await Deno.mkdir(out,{recursive:true});
  const commandText=async(cmd:string,args:string[])=>{
    try{const r=await new Deno.Command(cmd,{args,stdout:"piped",stderr:"piped"}).output();
      return {code:r.code,text:new TextDecoder().decode(r.stdout).trim(),error:new TextDecoder().decode(r.stderr).trim()};
    }catch(error){return {code:-1,text:"",error:String(error)};}
  };
  const checkDisk=async()=>{
    const disk=await commandText("df",["-k","/"]);
    const available=Number(disk.text.split("\n").at(-1)?.trim().split(/\s+/)[3]);
    if(disk.code||!Number.isFinite(available)||available<4*1024*1024)throw new Error("Disk is below 4 GiB, or df failed; stop timing");
    return available;
  };
  const sha=async(file:string)=>Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256",await Deno.readFile(file))))
    .map(v=>v.toString(16).padStart(2,"0")).join("");
  const engineSha256=await sha(engine);
  const metadata={schema:"foafnaut-presenter-timing/1",at:new Date().toISOString(),engine,engineSha256,
    input:"scheduled-input (fixed deadlines after first successful frame; not hardware enqueue)",
    endpoint:"offscreen present() return; excludes display/compositor latency",runs,warmupsPerMode:1,
    inputCount:120,inputPeriodMs:16,inputDelayMs:1500,inputDelta:-2,
    os:Deno.osRelease(),deno:Deno.version,load:Deno.loadavg(),diskAvailableKiB:await checkDisk(),
    power:await commandText("pmset",["-g","batt"]),thermal:await commandText("pmset",["-g","therm"]),
    revision:await commandText("git",["rev-parse","HEAD"]),
    tree:await commandText("git",["status","--short"]),
    files:await Promise.all(["run_html.ts","native_html_compile.ts","native_html_worker.ts","presenter_timing_input.ts"].map(async file=>({file,sha256:await sha(path(file))})))};
  await Deno.writeTextFile(`${out}/metadata.json`,JSON.stringify(metadata,null,2)+"\n");
  const note=async(message:string)=>await Deno.writeTextFile(
    "/Users/danbri/working/foafnaut/fncg/coordination.log",
    `codex-presenter1: ${new Date().toISOString()} ${message}\n`,{append:true});
  await note(`CLAIM presenter timing ${out}; ${runs} interleaved measured pairs per scenario`);
  const lock=await Deno.open("/tmp/foafnaut-timing.lock",{create:true,write:true});
  console.log("Waiting for /tmp/foafnaut-timing.lock");
  await lock.lock(true);
  type Result={scenario:string;mode:string;iteration:number;warmup:boolean;code:number;timedOut:boolean;valid:boolean;
    reasons:string[];samples:number[];latency:ReturnType<typeof distribution>;busySamples:number[];
    busyLatency:ReturnType<typeof distribution>;busyEvidence:string;maxScriptTurnMs:number;log:string};
  const results:Result[]=[];
  try{
    for(const scenario of scenarios){
      const name=`${scenario.id}-${scenario.busy?"busy":"idle"}`;
      // Warmup A/B, then measured A/B pairs; never all runs of one mode first.
      for(let iteration=0;iteration<=runs;iteration++)for(const mode of ["inline","worker"]){
        await checkDisk();
        const label=`${name}-${mode}-${iteration===0?"warmup":iteration}`;
        const log=`${out}/${label}.log`;
        const cmd=["run","--no-check","--no-config","--no-npm","--node-modules-dir=none","--unstable-webgpu","--unstable-ffi","-A",
          ...(scenario.snapshot?["--preload",path("realpages/replay.ts")]:[]),"--preload",path("presenter_timing_input.ts"),
          path("run_html.ts"),`--presenter=${mode}`,"--native-engine",engine,"--offscreen","--offscreen-size",scenario.viewport+"@1",
          "--text-size","100","--no-state","--no-splash","--perf-summary","--idle-checks-only","--be-liberal-in-what-we-accept",
          "--watch-sweep",String(seconds),...(scenario.busy?[]:["--no-scripts"]),"--url",scenario.url];
        const env:Record<string,string>={PRESENTER_TIMING_INPUT:"1",PRESENTER_TIMING_BUSY_URL:"",REALPAGES_REPLAY:""};
        if(scenario.snapshot)env.REALPAGES_REPLAY=scenario.snapshot;
        if(scenario.busy&&scenario.snapshot)env.PRESENTER_TIMING_BUSY_URL=scenario.url;
        await Deno.writeTextFile(`${out}/${label}.command.json`,JSON.stringify({command:Deno.execPath(),args:cmd,env,load:Deno.loadavg()},null,2)+"\n");
        const child=new Deno.Command(Deno.execPath(),{args:cmd,cwd:path("."),env,stdout:"piped",stderr:"piped"}).spawn();
        let timedOut=false;
        const timer=setTimeout(()=>{timedOut=true;try{child.kill("SIGKILL");}catch{/* already exited */}},timeout*1000);
        const output=await child.output();clearTimeout(timer);
        const text=new TextDecoder().decode(output.stdout)+"\n"+new TextDecoder().decode(output.stderr);
        await Deno.writeTextFile(log,text);
        const records=parseRecords(text),all=samples(records),summary=records.find(r=>r.type==="native-html-perf-summary");
        const turns=records.filter(r=>r.type==="native-html-script"&&Number(r.leanMs)>50&&r.cause!=="start");
        const maxScriptTurnMs=Math.max(0,...turns.map(r=>Number(r.leanMs)));
        // Completion minus leanMs is only an inferred interval; reply delivery may be late.
        // Exact worker epoch records, if available, are preferred by the next block.
        const epochTurns=records.filter(r=>r.type==="presenter-engine-turn"&&r.op==="scriptSession"&&
          typeof r.startEpochMs==="number"&&typeof r.endEpochMs==="number"&&Number(r.endEpochMs)-Number(r.startEpochMs)>50);
        const exact=epochTurns.length>0&&all.length>0&&all.every(s=>s.inputEpochMs!==null);
        const busySamples=all.filter(s=>exact?epochTurns.some(t=>s.inputEpochMs!>=Number(t.startEpochMs)&&s.inputEpochMs!<=Number(t.endEpochMs)):
          turns.some(t=>s.start>=Number(t.t)-Number(t.leanMs)&&s.start<=Number(t.t))).map(s=>s.ms);
        const reasons:string[]=[];
        if(output.code!==0)reasons.push(`exit ${output.code}`);
        if(timedOut)reasons.push("timeout");
        if(!summary)reasons.push("missing perf summary");
        if(all.length!==120)reasons.push(`expected 120 visible scroll samples, got ${all.length}`);
        if(Number(summary?.inputEventsDropped??0)>0)reasons.push("native events dropped");
        if(scenario.busy&&!busySamples.length)reasons.push("no scroll input overlaps a measured script turn over 50 ms");
        if(scenario.busy&&!exact)reasons.push("busy overlap inferred from completion: exact engine execution epochs absent");
        const values=all.map(s=>s.ms);
        const result:Result={scenario:name,mode,iteration,warmup:iteration===0,code:output.code,timedOut,valid:reasons.length===0,
          reasons,samples:values,latency:distribution(values),busySamples,busyLatency:distribution(busySamples),
          busyEvidence:exact?"exact engine execution epochs":"inferred completion minus leanMs",maxScriptTurnMs,log};
        results.push(result);
        await Deno.writeTextFile(`${out}/runs.json`,JSON.stringify(results,null,2)+"\n");
        console.log(JSON.stringify({...result,samples:undefined,busySamples:undefined}));
        await note(`RESULT timing ${label}: ${result.valid?"valid":"invalid"}, p95=${result.latency.p95Ms}, busy p95=${result.busyLatency.p95Ms}; ${log}`);
      }
    }
  }finally{lock.close();await note(`RELEASE presenter timing lock; results ${out}`);}
  const groups=[];
  for(const scenario of new Set(results.map(r=>r.scenario)))for(const mode of ["inline","worker"]){
    const selected=results.filter(r=>r.scenario===scenario&&r.mode===mode&&!r.warmup);
    const valid=selected.length===runs&&selected.every(r=>r.valid);
    groups.push({scenario,mode,valid,reasons:selected.filter(r=>!r.valid).map(r=>({iteration:r.iteration,reasons:r.reasons})),
      latency:distribution(selected.flatMap(r=>r.samples)),busyLatency:distribution(selected.flatMap(r=>r.busySamples)),
      p95Spread:spread(selected.flatMap(r=>r.latency.p95Ms===null?[]:[r.latency.p95Ms])),
      busyP95Spread:spread(selected.flatMap(r=>r.busyLatency.p95Ms===null?[]:[r.busyLatency.p95Ms]))});
  }
  await Deno.writeTextFile(`${out}/summary.json`,JSON.stringify({metadata,groups},null,2)+"\n");
  if(groups.some(g=>!g.valid))Deno.exitCode=1;
}
if(import.meta.main)await main();
