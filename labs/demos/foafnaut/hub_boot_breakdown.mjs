// Where the time goes in starting a page on the Hub: download and compile of each module, the
// engine's first call (its module initializers), fonts, page fetch, first layout, first draw,
// and the start of the page's scripts. Serves this checkout's Hub with an engine directory,
// adds timing probes to the worker as it serves it (nothing on disk changes), opens the page
// `--runs` times in headless Chrome and prints the median and range of each phase. With
// `--cache warm` the files are cacheable and the first run is a warm-up, so the numbers are a
// returning visit (Chrome's compiled-code cache for WebAssembly is in play). With `--profile
// OUT.cpuprofile` the worker's CPU profile is written (useful with an engine linked with
// `--profiling-funcs`, which names the functions).
//
//   node labs/demos/foafnaut/hub_boot_breakdown.mjs --engine DIR [--page home|NAME.html]
//     [--runs 3] [--cache cold|warm] [--script bubblepop|quickjs] [--pages-root CHECKOUT] [--profile F]
// DIR holds web-render.{mjs,wasm}, render-plan.{mjs,wasm} and qjs-wasmvm.wasm. CHROME overrides the browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';import {pathToFileURL} from 'node:url';
import {spawn} from 'node:child_process';import os from 'node:os';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
import {fileURLToPath} from 'node:url';
const root=path.resolve(opt('--root',fileURLToPath(new URL('../../../',import.meta.url))));
const hubDir=path.join(root,'docs/web/hub/foafnaut/'),pagesDir=path.join(opt('--pages-root',root),'labs/demos/foafnaut/pages/');
const engineDir=path.resolve(opt('--engine','.'))+'/';
const pageArg=opt('--page','home'),runs=+opt('--runs','3'),cache=opt('--cache','cold'),script=opt('--script','bubblepop');
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const LIVE='https://danbri.github.io';
const types={'.html':'text/html','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.json':'application/json','.css':'text/css','.ttf':'font/ttf','.png':'image/png','.svg':'image/svg+xml'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const made={'speed-start.html':'<!doctype html><html><head><meta charset="utf-8"><title>start</title></head><body><p id="s">...</p><script>document.getElementById("s").textContent="started";</script></body></html>'};
const live=new Map();
async function liveFetch(p){if(!live.has(p)){const r=await fetch(LIVE+p);live.set(p,{status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())});}return live.get(p);}
const probes=[
 // top of worker
 ["let post=(message,transfer)=>self.postMessage(message,transfer);","let post=(message,transfer)=>self.postMessage(message,transfer);\nconst __marks={workerOrigin:performance.timeOrigin,workerFirstLine:performance.timeOrigin+performance.now()};const __mark=n=>{__marks[n]??=performance.timeOrigin+performance.now();};"],
 ["WebAssembly.instantiate(compiled,imports).then(instance=>{","__mark('instantiateBegin');WebAssembly.instantiate(compiled,imports).then(instance=>{__mark('instantiateDone');"],
 ["const {bytes,sha}=await fontFile(notoSans);\n    const primary=fontLoad(bytes,'Noto Sans',sha);","const {bytes,sha}=await fontFile(notoSans);__mark('fontBytes');try{call('',{op:'scriptSession',action:'info'});}catch{};__mark('leanInit');\n    const primary=fontLoad(bytes,'Noto Sans',sha);__mark('fontLoaded');"],
 ["home=await prepare(homeURL);","home=await prepare(homeURL);__mark('homePrepared');"],
 ["if(await hasScripts()&&doc===page)await startScripts(page,scripts);","__mark('scriptTimerFired');const __has=await hasScripts();__mark('guestLoaded');if(__has&&doc===page)await startScripts(page,scripts);__mark('scriptsStarted');post({type:'phases',phases:{...phases,...__marks,resources:performance.getEntriesByType('resource').map(e=>({n:e.name.split('/').pop(),s:Math.round(e.startTime),e:Math.round(e.responseEnd),b:e.encodedBodySize}))}});"],
 ["if(!phasesPosted){phasesPosted=true;post({type:'phases',phases});firstFrameSeen();}","if(!phasesPosted){phasesPosted=true;post({type:'phases',phases:{...phases,...__marks,resources:performance.getEntriesByType('resource').map(e=>({n:e.name.split('/').pop(),s:Math.round(e.startTime),e:Math.round(e.responseEnd),b:e.encodedBodySize}))}});firstFrameSeen();}"],
];
let extraPatch=[];
if(opt('--patch'))extraPatch=(await import(pathToFileURL(path.resolve(opt('--patch'))).href)).default;
const applyPatches=(text,list)=>{for(const [a,b] of list){if(!text.includes(a))throw Error('probe target missing: '+a.slice(0,80));text=text.replace(a,()=>b);}return text;};
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/',guests='/factoidal/web/hub/wasm-guests/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p.startsWith(pages)&&made[p.slice(pages.length)])return {status:200,type:'text/html',body:Buffer.from(made[p.slice(pages.length)])};
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p===hub+'browser-worker.mjs'){
    let text=applyPatches(fs.readFileSync(path.join(hubDir,'browser-worker.mjs'),'utf8'),[...probes,...extraPatch]);
    if(script==='bubblepop'){const s="let scriptSetting=''";if(!text.includes(s))throw Error('no script setting');text=text.replace(s,"let scriptSetting='bubblepop'");}
    return {status:200,type:'text/javascript',body:Buffer.from(text)};
  }
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(rt)&&(f=local(engineDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p===guests+'qjs-wasmvm.wasm')return {status:200,type:'application/wasm',body:fs.readFileSync(path.join(engineDir,'qjs-wasmvm.wasm'))};
  return liveFetch(p);
}
const gzCache=new Map();
function gz(key,body){if(!gzCache.has(key)||gzCache.get(key).src!==body.length)gzCache.set(key,{src:body.length,data:zlib.gzipSync(body,{level:6})});return gzCache.get(key).data;}
const server=http.createServer(async(req,res)=>{
  try{const u=new URL(req.url,'http://x');const e=await get(u.pathname);const data=gz(u.pathname,e.body);
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':data.length,'cache-control':cache==='warm'?'public, max-age=3600':'no-store','access-control-allow-origin':'*'});res.end(data);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`;
const profile=fs.mkdtempSync(path.join(os.tmpdir(),'hub-boot-'));
const port=9000+Math.floor(Math.random()*400);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
const stop=async()=>{if(chrome.exitCode===null){chrome.kill('SIGKILL');await new Promise(r=>chrome.once('exit',r));}server.close();try{fs.rmSync(profile,{recursive:true,force:true});}catch{}};
for(const signal of ['SIGINT','SIGTERM'])process.on(signal,()=>stop().then(()=>process.exit(1)));
const med=x=>{const s=[...x].sort((a,b)=>a-b);return s[s.length>>1];};
const rows=[];
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error('Chrome did not start');
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map(),logs=[];
  socket.onmessage=({data})=>{const m=JSON.parse(data);
    if(m.method==='Runtime.consoleAPICalled')logs.push(m.params.args.map(a=>a.value??a.description).join(' '));
    if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const profOut=opt('--profile');
  const workerSessions=[];
  const prevHandler=socket.onmessage;
  socket.onmessage=e=>{prevHandler(e);const m=JSON.parse(e.data);if(m.method==='Target.attachedToTarget'&&m.params.targetInfo.type==='worker'){const sid=m.params.sessionId;workerSessions.push(sid);(async()=>{await send('Profiler.enable',{},sid);await send('Profiler.setSamplingInterval',{interval:300},sid);await send('Profiler.start',{},sid);await send('Runtime.runIfWaitingForDebugger',{},sid);})().catch(x=>console.error('prof',x));}};
  await send('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:false,flatten:true});
  const totalRuns=cache==='warm'?runs+1:runs;
  for(let r=0;r<totalRuns;r++){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    if(profOut)await s('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:true,flatten:true});
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width:800,height:900,deviceScaleFactor:1,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    const q=pageArg==='home'?'':`page=${encodeURIComponent(pageArg)}&`;
    await s('Page.navigate',{url:`${base}?${q}stats=1&strict=1`});
    const evaluate=async expression=>{const x=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(x.exceptionDetails)throw Error(x.exceptionDetails.text+' '+expression);return x.result.value;};
    const scripted=pageArg!=='home';
    const t0=Date.now();let phases,frames;
    while(Date.now()-t0<120000){
      await sleep(150);
      phases=await evaluate('window.foafnautPhases??null').catch(()=>null);
      frames=await evaluate(`(window.__frames??[]).map(f=>({t:f.t,path:f.path,layoutMs:f.layoutMs,drawMs:f.drawMs,turns:f.scripts?.turns,startMs:f.scripts?.startMs,engine:f.scripts?.engine,instructions:f.scripts?.instructions,hostCalls:f.scripts?.hostCalls}))`).catch(()=>null);
      if(phases&&frames?.length&&(!scripted||phases.scriptsStarted&&frames.some(f=>f.turns>=1)))break;
    }
    await sleep(300);
    phases=await evaluate('window.foafnautPhases??null');
    frames=await evaluate(`(window.__frames??[]).map(f=>({t:f.t,path:f.path,layoutMs:f.layoutMs,drawMs:f.drawMs,turns:f.scripts?.turns,startMs:f.scripts?.startMs,engine:f.scripts?.engine,instructions:f.scripts?.instructions,hostCalls:f.scripts?.hostCalls}))`);
    const nav=await evaluate(`(()=>{const n=performance.getEntriesByType('navigation')[0];return {origin:performance.timeOrigin,domContentLoaded:n.domContentLoadedEventEnd,load:n.loadEventEnd,resources:performance.getEntriesByType('resource').map(e=>({n:e.name.split('/').pop().split('?')[0],s:Math.round(e.startTime),e:Math.round(e.responseEnd),b:e.encodedBodySize}))}})()`);
    if(profOut&&workerSessions.length){const res=await send('Profiler.stop',{},workerSessions.at(-1));fs.writeFileSync(profOut,JSON.stringify(res.profile));console.error('profile written',profOut);}
    await send('Target.closeTarget',{targetId});
    if(!phases){console.error('no phases',logs.slice(-5));continue;}
    if(cache==='warm'&&r===0){console.error('warm-up run done');continue;}
    const o=nav.origin,rel=k=>phases[k]===undefined?undefined:Math.round(phases[k]-o);
    const span=(a,b)=>phases[a]===undefined||phases[b]===undefined?undefined:Math.round(phases[b]-phases[a]);
    const f0=frames[0]??{},scriptFrame=frames.find(f=>f.turns>=1)??{};
    const row={
      'navigation to worker first line':rel('workerFirstLine'),
      'worker module load (origin->first line)':span('workerOrigin','workerFirstLine'),
      'engine compile done (from worker start)':span('workerStart','engineCompiled'),
      'wait for compiled -> instantiate begin':span('engineCompiled','instantiateBegin'),
      'instantiate':span('instantiateBegin','instantiateDone'),
      'instantiate->engineReady (ctors, mjs)':span('instantiateDone','engineReady'),
      'noto bytes wait':span('engineReady','fontBytes'),
      'lean init (first call)':span('fontBytes','leanInit'),
      'font load (Noto Sans)':span('leanInit','fontLoaded'),
      'home prepare':span('fontReady','homePrepared'),
      'page fetch+inspect':span('homePrepared','pageReady'),
      'pageReady -> first layout (idle+chrome)':span('pageReady','firstLayout'),
      'first layout, Lean (stat)':f0.layoutMs,
      'first draw, GPU (stat)':f0.drawMs,
      'navigation to first frame':Math.round(f0.t??NaN),
      'first frame -> script timer':span('firstFrame','scriptTimerFired'),
      'guest load (hasScripts)':span('scriptTimerFired','guestLoaded'),
      'script start call':span('guestLoaded','scriptsStarted'),
      'script start turn (stat)':scriptFrame.startMs,
      'script instructions':scriptFrame.instructions,'script host calls':scriptFrame.hostCalls,
      'navigation to first scripted frame':Math.round(scriptFrame.t??NaN),
      engine:scriptFrame.engine,
    };
    rows.push({row,phases,frames:frames.slice(0,6),nav});
    console.error('run',r,JSON.stringify(row));
  }
  const keys=[...new Set(rows.flatMap(x=>Object.keys(x.row)))];
  console.log(`page=${pageArg} cache=${cache} script=${script} engine=${path.basename(engineDir)} runs=${rows.length} load=${os.loadavg()[0].toFixed(1)}`);
  for(const k of keys){const v=rows.map(x=>x.row[k]).filter(x=>x!==undefined);if(!v.length)continue;
    if(typeof v[0]==='string'){console.log(`  ${k}: ${v[0]}`);continue;}
    console.log(`  ${String(k).padEnd(44)} ${String(med(v)).padStart(6)}  [${Math.min(...v)}-${Math.max(...v)}]`);}
  if(rows[0]?.phases.resources){console.log('  worker resources (first run; start ms, end ms, encoded bytes):');for(const e of rows[0].phases.resources)console.log(`    ${e.n.padEnd(40)} ${e.s} ${e.e} ${e.b}`);}
  if(rows[0]?.nav.resources){console.log('  main resources:');for(const e of rows[0].nav.resources)console.log(`    ${e.n.padEnd(40)} ${e.s} ${e.e} ${e.b}`);}
  if(opt('--json'))fs.writeFileSync(opt('--json'),JSON.stringify(rows,null,1));
  if(logs.length&&args.includes('--console'))console.log(logs.slice(-20).join('\n'));
}finally{await stop();}
