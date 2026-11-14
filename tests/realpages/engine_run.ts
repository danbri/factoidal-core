// One page, one Foafnaut engine, under limits. Spawns the (patched) host run_html.ts off screen,
// timestamps every log line, samples the memory of the process tree, kills at a limit, and writes
// OUT/engine.json (the facts) and OUT/engine.log (the raw log).
// deno run -A engine_run.ts --host HOSTDIR --engine DYLIB --url URL --out DIR --steps JSON
//   [--window 1280x1000] [--first-limit-s 180] [--total-limit-s 300] [--mem-limit-mib 4096] [--sample AT:DUR,...]
const a=Deno.args,opt=(n:string,d?:string)=>{const i=a.indexOf(n);return i<0?d:a[i+1];};
const host=opt("--host")!,engine=opt("--engine")!,url=opt("--url")!,out=opt("--out")!,steps=opt("--steps","[]")!;
const win=opt("--window","1280x1000")!,firstLimit=Number(opt("--first-limit-s","180"))*1000,totalLimit=Number(opt("--total-limit-s","300"))*1000;
const memLimit=Number(opt("--mem-limit-mib","4096"))*1024;
await Deno.mkdir(out,{recursive:true});
const t0=performance.now(),ms=()=>Math.round(performance.now()-t0);
const cmd=new Deno.Command("deno",{args:["run","-A","--unstable-webgpu","--unstable-ffi","run_html.ts","--url",url,"--offscreen","--offscreen-size",`${win}@1`,
  "--text-size","100","--no-splash","--no-state","--perf-summary","--idle-checks-only","--follow-links","--native-engine",engine],
  cwd:host,env:{RP_STEPS:steps},stdout:"piped",stderr:"piped"});
const child=cmd.spawn();
const lines:{t:number;s:string}[]=[];
let firstFrame:number|undefined,killed:string|undefined,peakKiB=0,lastLine=0;
const kill=(why:string)=>{if(killed)return;killed=why;
  for(const p of tree())try{Deno.kill(p,"SIGKILL");}catch{/* gone */}};
function tree():number[]{
  // the child and its descendants (ps once)
  const o=new TextDecoder().decode(new Deno.Command("ps",{args:["-Ao","pid=,ppid=,rss="]}).outputSync().stdout);
  const rows=o.trim().split("\n").map(l=>l.trim().split(/\s+/).map(Number));
  const set=new Set([child.pid]);let grew=true;
  while(grew){grew=false;for(const [p,pp] of rows)if(set.has(pp)&&!set.has(p)){set.add(p);grew=true;}}
  return [...set];
}
function rssKiB():number{
  const o=new TextDecoder().decode(new Deno.Command("ps",{args:["-Ao","pid=,ppid=,rss="]}).outputSync().stdout);
  const rows=o.trim().split("\n").map(l=>l.trim().split(/\s+/).map(Number));
  const set=new Set([child.pid]);let grew=true;
  while(grew){grew=false;for(const [p,pp] of rows)if(set.has(pp)&&!set.has(p)){set.add(p);grew=true;}}
  return rows.filter(r=>set.has(r[0])).reduce((s,r)=>s+r[2],0);
}
const pump=async(stream:ReadableStream<Uint8Array>,tag:string)=>{
  let rest="";const dec=new TextDecoder();
  for await(const chunk of stream){rest+=dec.decode(chunk,{stream:true});let i;
    while((i=rest.indexOf("\n"))>=0){const s=rest.slice(0,i);rest=rest.slice(i+1);const t=ms();lines.push({t,s:tag+s});lastLine=t;
      if(firstFrame===undefined&&s.includes('"type":"native-html-frame"'))firstFrame=t;}}
  if(rest)lines.push({t:ms(),s:tag+rest});
};
const p1=pump(child.stdout,""),p2=pump(child.stderr,"E| ");
// --sample AT:DUR[,AT:DUR...] (seconds): macOS sample(1) of the host process (the engine runs in it through FFI) from AT
// for DUR seconds, into OUT/sample-AT.txt: where the engine's time goes, by function. For diagnosis runs only; it slows
// the process a little, so measured rounds run without it.
const sampleTimers:ReturnType<typeof setTimeout>[]=[];
for(const w of (opt("--sample")??"").split(",").filter(Boolean)){const [at,dur]=w.split(":").map(Number);
  sampleTimers.push(setTimeout(()=>{if(killed)return;new Deno.Command("/usr/bin/sample",{args:[String(child.pid),String(dur),"1","-mayDie","-file",`${out}/sample-${at}.txt`],stdout:"null",stderr:"null"}).spawn();},at*1000));}
const watch=setInterval(()=>{
  const k=rssKiB();peakKiB=Math.max(peakKiB,k);
  if(k>memLimit)kill(`memory limit (${memLimit>>10} MiB)`);
  else if(firstFrame===undefined&&ms()>firstLimit)kill(`no picture in ${firstLimit/1000} s`);
  else if(ms()>totalLimit)kill(`total limit ${totalLimit/1000} s`);
},500);
const status=await child.status;clearInterval(watch);sampleTimers.forEach(clearTimeout);await Promise.allSettled([p1,p2]);
await Deno.writeTextFile(`${out}/engine.log`,lines.map(l=>`${String(l.t).padStart(7)} ${l.s}`).join("\n")+"\n");
const json=(s:string)=>{try{return JSON.parse(s);}catch{return undefined;}};
const ev=lines.map(l=>({t:l.t,j:l.s.startsWith("{")?json(l.s):undefined})).filter(e=>e.j);
const of=(type:string)=>ev.filter(e=>e.j.type===type);
const shots=of("rp-shot").map(e=>({...e.j,at:e.t}));
const quiets=of("rp-quiet").map(e=>({...e.j,at:e.t}));
const refused=of("native-html-refused").map(e=>e.j.reason);
const stderr=lines.filter(l=>l.s.startsWith("E| ")).map(l=>l.s.slice(3));
const panic=stderr.filter(s=>/panic|PANIC|INTERNAL PANIC|Segmentation|SIGSEGV|SIGBUS|stack overflow|uncaught|Uncaught|RangeError|out of memory/i.test(s)).slice(0,10);
const scripts=of("native-html-script");
const fetches=ev.filter(e=>e.j.type==="native-html-fonts");
const facts={
  url,engine,host,window:win,limits:{firstPictureS:firstLimit/1000,totalS:totalLimit/1000,memMiB:memLimit>>10},
  exit:{code:status.code,signal:status.signal,killed:killed??null},
  firstPictureMs:firstFrame??null,
  settledMs:quiets[0]?(quiets[0].quiet?quiets[0].at-quiets[0].lastFrameAgo:null):null,
  settled:quiets[0]?.quiet??false,
  peakMiB:Math.round(peakKiB/1024),
  refused,
  shots,
  nav:of("rp-nav").map(e=>e.j),link:of("rp-link").map(e=>e.j),scroll:of("rp-scroll").map(e=>e.j),
  scriptTurns:scripts.length,scriptStart:scripts.find(e=>e.j.cause==="start")?.j??null,
  fonts:fetches.map(e=>e.j),
  stderrCount:stderr.length,stderrSample:stderr.filter(s=>!/^\s*$/.test(s)).slice(0,30).map(s=>s.slice(0,300)),panic,
  lastLineMs:lastLine,
};
await Deno.writeTextFile(`${out}/engine.json`,JSON.stringify(facts,null,1));
console.log(JSON.stringify({url,exit:facts.exit,firstPictureMs:facts.firstPictureMs,settledMs:facts.settledMs,peakMiB:facts.peakMiB,shots:shots.length,refused:refused.length}));
