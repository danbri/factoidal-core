// The Spinal Tap page (pages/spinal-tap-sparql.html) on the Hub, measured in headless Chrome
// (core issue 450): the frames the Hub draws while the page's zoom runs, for about 45 s.
//
// Recorded for each frame the Hub shows (window.foafnautFrame, browser.mjs): its path
// (`layers`, `band`, `shift` or the whole-page `frame`), layout ms, draw ms, GPU ms, total ms
// and primitives, and for the page layer's draw the CPU ms to submit, the GPU ms until done and
// the shader work counted from the scene (scene-work.mjs: records visited, path edges walked,
// edges walked outside the record's clip, pixels drawn, bytes uploaded). Every 5 s: the JS heap of the page and of the engine's worker
// (Runtime.getHeapUsage) and the RSS of all of Chrome's processes. All the time: the console
// warnings, errors and exceptions of the page and the worker, and among them GPU errors and a
// lost GPU device. The WebGPU adapter is recorded (vendor, architecture, whether it is a
// fallback adapter such as SwiftShader). The result is one JSON file; the budgets are the `hub`
// section of fixtures/spinal-perf/budgets.json, checked here (exit 1 on a budget missed, and
// on a known failure that no longer fails, so that it is moved to the budgets).
//
//   node labs/demos/foafnaut/hub_spinal_perf.mjs [--seconds 45] [--out FILE] [--adapter auto|gpu|swiftshader]
//     [--live | --runtime DIR]
//
// Sources: by default the Hub's host files (docs/web/hub/foafnaut/*.mjs) and the page come from
// this checkout, and the engine (html-webgpu/runtime) from --runtime DIR, else from the published
// Hub. --live loads the published Hub as it is, with no local file. CHROME=/path overrides the
// browser. NOT RUN (exit 0) with no Chrome, or with no WebGPU adapter of either kind.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';import os from 'node:os';
import {spawn,execFileSync} from 'node:child_process';import {fileURLToPath} from 'node:url';
import {checkBudgets,knownFailures} from './spinal_budgets.mjs';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];},flag=n=>args.includes(n);
const SECONDS=Number(opt('--seconds',45)),OUT=opt('--out'),ADAPTER=opt('--adapter','auto'),LIVE_ONLY=flag('--live');
// --profile FILE: a CPU profile (Profiler, 1 ms samples) of each worker for the whole run, written
// as {sessions:[{url,profile}]}: what a worker does in a gap between frames.
const PROFILE=opt('--profile');
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const runtimeDir=opt('--runtime');
const budgetsFile=fileURLToPath(new URL('./fixtures/spinal-perf/budgets.json',import.meta.url));
const LIVE='https://danbri.github.io';
const PAGE='spinal-tap-sparql.html';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_spinal_perf.mjs needs Chrome (set CHROME)');process.exit(0);}
if(runtimeDir&&!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no web-render.wasm in ${runtimeDir}`);process.exit(0);}
const types={'.html':'text/html','.xml':'application/xml','.xsl':'application/xml','.mjs':'text/javascript','.js':'text/javascript',
  '.wasm':'application/wasm','.ttl':'text/turtle','.css':'text/css','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.json':'application/json','.ttf':'font/ttf'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const cache=new Map();
const sources={hostFiles:LIVE_ONLY?'published':'checkout',page:LIVE_ONLY?'published':'checkout',engine:runtimeDir?`local ${runtimeDir}`:'published'};
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(!LIVE_ONLY){
    if(p===pages+PAGE&&(f=local(pagesDir,PAGE)))return {status:200,type:'text/html',body:fs.readFileSync(f)};
    if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  }
  if(runtimeDir&&p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);const gz=zlib.gzipSync(e.body,{level:1});
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':gz.length,'cache-control':'no-store'});res.end(gz);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`;
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const r1=x=>Math.round(x*10)/10;
const stat=xs=>{const s=[...xs].sort((a,b)=>a-b),q=p=>s.length?s[Math.min(s.length-1,Math.floor(p*s.length))]:0;
  return {n:s.length,median:r1(q(0.5)),p95:r1(q(0.95)),max:r1(s.length?s[s.length-1]:0)};};
// The RSS of every process of this Chrome (its profile directory is in each command line), in MB.
const chromeRss=profile=>{try{
  return r1(execFileSync('ps',['-A','-o','rss=,command='],{encoding:'utf8',maxBuffer:1<<26}).split('\n')
    .filter(l=>l.includes(profile)).reduce((a,l)=>a+Number(l.trim().split(/\s+/)[0]||0),0)/1024);}catch{return null;}};

async function session(adapterMode){
  const profile=fs.mkdtempSync(path.join(os.tmpdir(),'hub-spinal-perf-'));
  const port=9400+Math.floor(Math.random()*500);
  const flags=['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run',
    '--window-size=1280,900',...(adapterMode==='swiftshader'?['--use-webgpu-adapter=swiftshader','--enable-unsafe-swiftshader']:[]),'about:blank'];
  const chrome=spawn(CHROME,flags,{stdio:'ignore'});
  const out={adapterMode,flags:flags.filter(f=>!f.includes(profile)&&!f.startsWith('--remote')),sources};
  let socket;
  try{
    let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
    if(!ws)throw Error('Chrome did not start: no answer on /json/version after 30 s');
    socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
    let id=0;const waiting=new Map(),workers=new Set(),messages=[],profiled=[];
    const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
    const t0=Date.now();
    socket.onmessage=({data})=>{const m=JSON.parse(data);
      if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);return;}
      const from=workers.has(m.sessionId)?'worker':'page';
      if(m.method==='Target.attachedToTarget'&&m.params.targetInfo.type.includes('worker')){
        workers.add(m.params.sessionId);
        if(PROFILE){profiled.push({sid:m.params.sessionId,url:m.params.targetInfo.url});
          send('Profiler.enable',{},m.params.sessionId).then(()=>send('Profiler.setSamplingInterval',{interval:1000},m.params.sessionId))
            .then(()=>send('Profiler.start',{},m.params.sessionId)).catch(()=>{});}
        send('Runtime.enable',{},m.params.sessionId).catch(()=>{});
        send('Runtime.runIfWaitingForDebugger',{},m.params.sessionId).catch(()=>{});
      }
      if(m.method==='Runtime.consoleAPICalled'&&['warning','error','assert'].includes(m.params.type))
        messages.push({s:r1((Date.now()-t0)/1000),from,type:m.params.type,text:m.params.args.map(a=>a.value??a.description??'').join(' ').slice(0,400)});
      if(m.method==='Runtime.exceptionThrown')
        messages.push({s:r1((Date.now()-t0)/1000),from,type:'exception',text:(m.params.exceptionDetails.exception?.description??m.params.exceptionDetails.text).slice(0,400)});
    };
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:false,flatten:true});
    await s('Emulation.setDeviceMetricsOverride',{width:1280,height:900,deviceScaleFactor:1,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];
      Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    const evaluate=async(expression,sid=sessionId)=>{const r=await send('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true},sid);
      if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    await s('Page.navigate',{url:base});
    await sleep(500);
    out.adapter=await evaluate(`(async()=>{const a=await navigator.gpu?.requestAdapter();if(!a)return null;const i=a.info??{};
      return {vendor:i.vendor,architecture:i.architecture,device:i.device,description:i.description,fallback:!!(i.isFallbackAdapter??a.isFallbackAdapter)};})()`);
    if(!out.adapter){out.why='no WebGPU adapter';return out;}
    out.userAgent=await evaluate('navigator.userAgent');
    // The page, opened as a visit to ?page= opens it.
    const t1=Date.now();
    await s('Page.navigate',{url:`${base}?page=${PAGE}&stats=1`});
    const frames=[],heap=[],rss=[];
    let nextSample=0;
    while(Date.now()-t1<SECONDS*1000){
      await sleep(1000);
      const got=await evaluate(`(()=>{const f=window.__frames??[];window.__frames=[];return f.map(x=>({t:x.t,path:x.path,url:x.url,layoutMs:x.layoutMs,drawMs:x.drawMs,
        gpuMs:x.gpuMs,totalMs:x.totalMs,primitives:x.primitives,leanRenders:x.leanRenders,leanCalls:x.leanCalls,rows:x.rows,scriptTurns:x.scripts?.turns,scriptMs:x.scripts?.ms,scriptLastMs:x.scripts?.lastMs,draw:x.draws?.page??x.draws?.single,chrome:x.draws?.chrome,composite:x.draws?.composite,planRequests:x.surface?.planRequests,pipelineBuilds:x.surface?.pipelineBuilds}));})()`).catch(()=>[]);
      frames.push(...got);
      if(Date.now()-t1>=nextSample){
        nextSample+=5000;
        const page=await send('Runtime.getHeapUsage',{},sessionId).catch(()=>undefined);
        let worker=0;for(const w of workers){const h=await send('Runtime.getHeapUsage',{},w).catch(()=>undefined);worker+=h?.usedSize??0;}
        heap.push({s:r1((Date.now()-t1)/1000),pageMb:r1((page?.usedSize??0)/1048576),workerMb:r1(worker/1048576)});
        rss.push({s:r1((Date.now()-t1)/1000),mb:chromeRss(profile)});
      }
    }
    out.seconds=SECONDS;out.workers=workers.size;
    if(PROFILE){
      // The page's clock at the run's start, for lining frames up with profile samples (us).
      const pageNow=await evaluate('performance.timeOrigin+performance.now()').catch(()=>null);
      const sessions=[];
      for(const {sid,url} of profiled){const r=await send('Profiler.stop',{},sid).catch(()=>undefined);if(r?.profile)sessions.push({url,profile:r.profile});}
      fs.writeFileSync(PROFILE,JSON.stringify({pageNowMs:pageNow,frames:frames.map(f=>({t:f.t,path:f.path,layoutMs:f.layoutMs,drawMs:f.drawMs})),sessions}));
    }
    const pageFrames=frames.filter(f=>String(f.url??'').endsWith(PAGE));
    const first=pageFrames[0];
    // Frames after the first one of the page: the animation's frames (the zoom starts 0.6 s in).
    const later=pageFrames.slice(1);
    const paths={};for(const f of later)paths[f.path]=(paths[f.path]??0)+1;
    const drawn=later.filter(f=>typeof f.drawMs==='number');
    const tenth=Math.max(1,drawn.length>>2);
    out.frames={count:pageFrames.length,first:first?{path:first.path,layoutMs:first.layoutMs,drawMs:first.drawMs,totalMs:first.totalMs,primitives:first.primitives,
      atS:r1(first.t/1000)}:null,paths,
      whole_page:later.filter(f=>/^frame/.test(f.path??'')).length,
      layered:later.filter(f=>/^(layers|band|shift)/.test(f.path??'')).length,
      draw_ms:stat(drawn.map(f=>f.drawMs)),layout_ms:stat(drawn.map(f=>f.layoutMs)),total_ms:stat(drawn.map(f=>f.totalMs)),
      draw_ms_early:stat(drawn.slice(0,tenth).map(f=>f.drawMs)).median,draw_ms_late:stat(drawn.slice(-tenth).map(f=>f.drawMs)).median,
      primitives_max:Math.max(0,...later.map(f=>f.primitives??0)),
      fps:later.length>1?r1((later.length-1)/((later.at(-1).t-later[0].t)/1000)):0};
    // Where a draw's time goes (layers.mjs drawScene with ?stats=1): CPU ms to submit, GPU ms
    // until done, and the shader's work counted from the scene (scene-work.mjs), in millions of
    // loop trips at four samples a pixel.
    const chromeOf=f=>f.chrome&&!f.chrome.kept&&typeof f.chrome.gpuMs==='number'?f.chrome.cpuMs+f.chrome.gpuMs:0;
    const otherOf=f=>f.drawMs-f.draw.cpuMs-f.draw.gpuMs-chromeOf(f)-(f.composite?f.composite.cpuMs+f.composite.gpuMs:0);
    const draws=drawn.map(f=>f.draw).filter(d=>d&&!d.kept&&typeof d.gpuMs==='number');
    const m=x=>Math.round(x/1e4)/100;
    out.draw_split={n:draws.length,cpu_ms:stat(draws.map(d=>d.cpuMs)),gpu_ms:stat(draws.map(d=>d.gpuMs)),
      segments_m:stat(draws.map(d=>m(d.segments))),outside_clip_m:stat(draws.map(d=>m(d.segmentsOutsideClip))),pieces_m:stat(draws.map(d=>m(d.pieces??0))),listed_m:stat(draws.map(d=>m(d.listed))),
      drawn_pixels:stat(draws.map(d=>d.drawnPixels)),upload_kb:stat(draws.map(d=>Math.round(d.uploadBytes/1024))),partial:draws.filter(d=>d.partial).length,
      // The rest of a frame's draw time: what the page draw, the chrome draw and the composite do not account for.
      other_ms:stat(later.filter(f=>f.draw&&!f.draw.kept&&typeof f.draw.gpuMs==='number').map(otherOf)),
      composite_ms:stat(later.filter(f=>f.composite).map(f=>f.composite.cpuMs+f.composite.gpuMs)),
      // GPU ms for a thousand million edge trips: what the adapter does per unit of the counted work.
      gpu_ms_per_g_segments:(()=>{const a=draws.reduce((t,d)=>t+d.gpuMs,0),b=draws.reduce((t,d)=>t+d.segments,0);return b?r1(a/(b/1e9)):0;})()};
    out.frames.late_over_early=out.frames.draw_ms_early?Math.round(out.frames.draw_ms_late/out.frames.draw_ms_early*100)/100:0;
    out.heap_mb={samples:heap,page_growth:heap.length?r1(heap.at(-1).pageMb-heap[0].pageMb):0,worker_growth:heap.length?r1(heap.at(-1).workerMb-heap[0].workerMb):0,
      worker_end:heap.at(-1)?.workerMb??0};
    const rssOk=rss.filter(x=>x.mb!==null);
    out.rss_mb={samples:rssOk,growth:rssOk.length?r1(rssOk.at(-1).mb-rssOk[0].mb):null,peak:rssOk.length?Math.max(...rssOk.map(x=>x.mb)):null};
    const gpuText=/GPU|WebGPU|device/i,lostText=/device (was )?lost|lost:|GPU layer surface is failed/i;
    out.errors={count:messages.filter(m=>m.type!=='warning').length,warnings:messages.filter(m=>m.type==='warning').length,
      gpu:messages.filter(m=>gpuText.test(m.text)).length,device_lost:messages.some(m=>lostText.test(m.text))?1:0,first:messages.slice(0,12)};
    // With each frame, the page's script turns so far (count, total ms, the last turn's ms) and
    // the engine calls: a gap between frames is a script turn, an engine call or neither.
    out.frames_detail=pageFrames.map(f=>({s:r1((f.t)/1000),path:f.path,layoutMs:f.layoutMs,drawMs:f.drawMs,primitives:f.primitives,
      scriptTurns:f.scriptTurns,scriptMs:f.scriptMs===undefined?undefined:r1(f.scriptMs),scriptLastMs:f.scriptLastMs,leanCalls:f.leanCalls,leanRenders:f.leanRenders,
      ...(f.draw&&!f.draw.kept?{cpuMs:f.draw.cpuMs,gpuMs:f.draw.gpuMs,segmentsM:m(f.draw.segments),outsideClipM:m(f.draw.segmentsOutsideClip),piecesM:m(f.draw.pieces??0),
        listedM:m(f.draw.listed),drawnPixels:f.draw.drawnPixels,uploadKB:Math.round(f.draw.uploadBytes/1024),partial:f.draw.partial,
        chromeMs:r1(chromeOf(f)),chromeGpuMs:f.chrome?.gpuMs,planRequests:f.planRequests,pipelineBuilds:f.pipelineBuilds,compositeMs:f.composite?r1(f.composite.cpuMs+f.composite.gpuMs):undefined,otherMs:r1(otherOf(f))}:{})}));
    out.valid=pageFrames.length>1;
    if(!out.valid)out.why=`the page drew ${pageFrames.length} frames`;
    return out;
  }finally{try{socket?.close();}catch{/* closed */}chrome.kill('SIGKILL');await sleep(300);fs.rmSync(profile,{recursive:true,force:true});}
}

let run;
try{
  run=await session(ADAPTER==='swiftshader'?'swiftshader':'gpu');
  if(!run.adapter&&ADAPTER==='auto')run=await session('swiftshader');
}finally{server.close();}
run.date=new Date().toISOString();run.host=`${os.platform()} ${os.arch()} ${os.cpus()[0]?.model??''}`.trim();
if(!run.adapter){console.log(`NOT RUN: no WebGPU adapter in headless Chrome (${ADAPTER})`);if(OUT)fs.writeFileSync(OUT,JSON.stringify(run)+'\n');process.exit(0);}
// A fallback adapter (SwiftShader) draws on the CPU: the first frame of this page took 74 s on
// an M1, so its times say nothing about the Hub. It is recorded, and the budgets are not applied.
if(run.adapter.fallback){
  if(OUT)fs.writeFileSync(OUT,JSON.stringify(run)+'\n');
  console.log(`NOT RUN against the budgets: fallback adapter ${run.adapter.vendor} ${run.adapter.architecture}; ${run.frames?.count??0} frames in ${SECONDS} s (first frame draw ${run.frames?.first?.drawMs} ms)`);
  process.exit(0);
}
const budgets=JSON.parse(fs.readFileSync(budgetsFile,'utf8')).hub;
const results=checkBudgets(budgets.budgets??{},run),known=knownFailures(budgets.known_failures??{},run);
run.budgets=results;run.known_failures=known;
if(OUT)fs.writeFileSync(OUT,JSON.stringify(run)+'\n');
const {frames_detail:_d,heap_mb:{samples:_h,...heapRest},rss_mb:{samples:_r,...rssRest},...shown}=run;
console.log(JSON.stringify({...shown,heap_mb:heapRest,rss_mb:rssRest},null,1));
let failed=0;
for(const r of results)if(!r.ok){failed++;console.log(`FAIL budget ${r.metric}: ${r.value} (${r.kind} ${r.limit})`);}
for(const k of known)if(!k.stillFails){failed++;console.log(`FAIL known failure ${k.metric} no longer fails (${k.value}, want ${k.want}): move it to the budgets (${k.issue})`);}
else console.log(`KNOWN FAILURE ${k.metric}: ${k.value} (wanted ${k.want}; ${k.issue})`);
if(!run.valid){failed++;console.log(`FAIL not valid: ${run.why}`);}
console.log(failed?`hub spinal perf: ${failed} failures`:`hub spinal perf: pass (${run.adapter.fallback?'fallback adapter':'GPU adapter'} ${run.adapter.vendor??''} ${run.adapter.architecture??''})`);
process.exit(failed?1:0);
