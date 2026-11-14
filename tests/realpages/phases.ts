// Where the time to a first picture goes, from the timestamped log engine_run.ts writes (engine.log):
// fetches (span and summed time), script turns (count, built-in engine time, instructions, the longest turn),
// the first compile ("loaded"), the first frame (layout in the worker, session, draw) and the rest (loader, host, waiting).
// deno run -A tests/realpages/phases.ts ROUNDDIR/<page>/<sha>/engine.log [...]   (prints one JSON line per log)
const num=(v:unknown)=>typeof v==="number"?v:0;
for(const file of Deno.args){
  const ev:{t:number;j:Record<string,unknown>}[]=[];
  for(const line of (await Deno.readTextFile(file)).split("\n")){
    const m=/^\s*(\d+) (\{.*\})\s*$/.exec(line);if(!m)continue;
    try{ev.push({t:Number(m[1]),j:JSON.parse(m[2])});}catch{/* not JSON */}
  }
  const fetches=ev.filter(e=>e.j.type==="rp-fetch");
  const navStart=fetches.length?fetches[0].t-num(fetches[0].j.ms):null;
  const frame=ev.find(e=>e.j.type==="native-html-frame");
  const end=frame?.t??ev.at(-1)?.t??0;
  const before=(e:{t:number})=>e.t<=end;
  const f=fetches.filter(before),turns=ev.filter(e=>e.j.type==="native-html-script"&&before(e));
  const longest=turns.reduce<typeof turns[0]|undefined>((m,e)=>!m||num(e.j.leanMs)>num(m.j.leanMs)?e:m,undefined);
  const scriptMs=turns.reduce((s,e)=>s+num(e.j.leanMs),0);
  const kinds:Record<string,number>={};
  for(const x of f){const c=String(x.j.ctype);const k=/css/.test(c)?"sheet":/javascript|ecmascript/.test(c)?"script":/^image\//.test(c)?"image":/font|woff/.test(c)?"font":/html/.test(c)?"html":"other";kinds[k]=(kinds[k]??0)+1;}
  const rel=(t:number|undefined)=>t===undefined||navStart===null?null:t-navStart;
  const out={
    log:file.split("/").slice(-3,-1).join("/"),
    firstPictureMs:frame?rel(frame.t):null,
    // the host's "loaded" line: the document is compiled for the first time (style, layout, paint plan) before the window
    loadedMs:rel(ev.find(e=>e.j.type==="native-html-loaded")?.t),
    fetch:{count:f.length,kinds,lastEndMs:f.length?rel(f.at(-1)!.t):null,sumMs:f.reduce((s,x)=>s+num(x.j.ms),0),failed:f.filter(x=>num(x.j.status)<200||num(x.j.status)>=400).length},
    scripts:{turns:turns.length,leanMs:Math.round(scriptMs),instructions:turns.reduce((s,e)=>s+num(e.j.instructions),0),
      longest:longest?{cause:longest.j.cause,leanMs:longest.j.leanMs,instructions:longest.j.instructions,endMs:rel(longest.t)}:null},
    firstFrame:frame?{layoutMs:frame.j.layoutMs,workerMs:frame.j.workerMs,sessionMs:frame.j.sessionMs,drawMs:frame.j.drawMs,totalMs:frame.j.totalMs}:null,
    slowCalls:Object.entries(ev.filter(e=>e.j.type==="native-html-slow-call"&&before(e)).reduce<Record<string,number>>((m,e)=>{const k=String(e.j.call);m[k]=(m[k]??0)+num(e.j.ms);return m;},{}))
      .sort((x,y)=>y[1]-x[1]).slice(0,5).map(([k,v])=>`${k} ${Math.round(v)} ms`),
    otherMs:frame&&navStart!==null?Math.round(frame.t-navStart-scriptMs-num(frame.j.totalMs)):null,
  };
  console.log(JSON.stringify(out));
}
