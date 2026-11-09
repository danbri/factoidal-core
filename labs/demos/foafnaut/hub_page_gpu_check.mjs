// The Hub with a page that draws with WebGPU (docs/designissues/2026-11-08-page-gpu.md):
// pages/webgpu-triangle.html runs in QuickJS in WasmVM inside the engine; Lean validates each
// GPU command (L4Factoidal.PageGpu); the Hub worker replays Lean's host commands on its WebGPU
// device (page-gpu.mjs) and blits the page canvas into the page layer at Lean's rectangle.
// Checks, in headless Chrome with WebGPU: frames with the path "page-gpu" (no Lean layout);
// passes and blits counted by the replay; no replay errors. The frame rate is printed.
//   node labs/demos/foafnaut/hub_page_gpu_check.mjs [--runtime DIR] [--guest FILE] [--shot FILE] [--page webgl-triangle.html|canvas-chart.html]
// --runtime: an engine with gpu_command (build-web-render.sh --wasm); --guest: a QuickJS guest
// built from this prelude (tools/wasmvm/build-quickjs.sh).
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const opt=(name,fallback)=>{const i=process.argv.indexOf(name);return i>0?process.argv[i+1]:fallback;};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const pageName=opt('--page','webgpu-triangle.html');
const guest=opt('--guest',`${process.env.HOME}/working/qjs-wasm/qjs-wasmvm.wasm`),shotFile=opt('--shot','');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_page_gpu_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no engine in ${runtimeDir}`);process.exit(0);}
const types={'.html':'text/html','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/',guests='/factoidal/web/hub/wasm-guests/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p===guests+'qjs-wasmvm.wasm')return {status:200,type:'application/wasm',body:fs.readFileSync(guest)};
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);const gz=zlib.gzipSync(e.body,{level:1});
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':gz.length,'cache-control':'no-store'});res.end(gz);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const base=`http://127.0.0.1:${server.address().port}/factoidal/web/hub/foafnaut/`;
const profile=fs.mkdtempSync('/tmp/hub-page-gpu-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error("Chrome did not start: no answer on /json/version after 30 s");
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map(),logs=[];
  socket.onmessage=({data})=>{const m=JSON.parse(data);
    if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}
    if(m.method==='Runtime.exceptionThrown')logs.push('exception: '+JSON.stringify(m.params.exceptionDetails).slice(0,400));
    if(m.method==='Runtime.consoleAPICalled')logs.push(m.params.args.map(a=>a.value??a.description).join(' '));
    // The engine worker's console too (its warnings name page GPU failures).
    if(m.method==='Target.attachedToTarget')socket.send(JSON.stringify({id:++id,method:'Runtime.enable',params:{},sessionId:m.params.sessionId}));};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const {targetId}=await send('Target.createTarget',{url:'about:blank'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const s=(m,p)=>send(m,p,sessionId);
  await s('Page.enable');await s('Runtime.enable');
  await s('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:false,flatten:true});
  await s('Emulation.setDeviceMetricsOverride',{width:800,height:900,deviceScaleFactor:1,mobile:false});
  await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];
    Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
  await s('Page.navigate',{url:base+`?page=${pageName}&stats=1`});
  const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
  const t0=Date.now();let gpuFrames=[];
  while(Date.now()-t0<60000){
    await sleep(500);
    gpuFrames=await evaluate(`window.__frames.filter(f=>f.path?.startsWith('page-gpu')).map(f=>({t:f.t,pageGpu:f.pageGpu,leanRenders:f.leanRenders,scripts:f.scripts,drawMs:f.drawMs}))`).catch(()=>[]);
    if(gpuFrames.length>=24)break;
  }
  if(gpuFrames.length<10){
    fail(`only ${gpuFrames.length} page-gpu frames`);
    console.log('frame paths:',JSON.stringify(await evaluate(`[...new Set(window.__frames.map(f=>f.path))]`).catch(()=>null)));
    console.log('console:',logs.slice(-15).join(' | '));
    console.log('frames:',await evaluate('window.__frames.length').catch(e=>String(e)),'note:',await evaluate(`document.querySelector('#note')?.textContent??''`).catch(()=>''));
  }
  else{
    const span=(gpuFrames.at(-1).t-gpuFrames[0].t)/1000,rate=(gpuFrames.length-1)/span;
    console.log(`page-gpu frames: ${gpuFrames.length} in ${span.toFixed(2)} s, ${rate.toFixed(1)} a second; last stats`,JSON.stringify(gpuFrames.at(-1).pageGpu));
    const sc=gpuFrames.at(-1).scripts,draws=gpuFrames.map(f=>f.drawMs).sort((a,b)=>a-b);
    if(sc)console.log(`script turns: ${sc.turns}, ${(sc.ms/Math.max(1,sc.turns)).toFixed(1)} ms a turn on average (last ${sc.lastMs} ms, path ${sc.path}); page-gpu draw median ${draws[draws.length>>1]} ms`);
    // The rate is reported, not checked: headless Chrome draws with a software GPU, and the
    // page's callbacks run in WasmVM in the engine (record, section 9, for measurements).
    if(rate>40)fail(`frame rate ${rate.toFixed(1)}: more page canvas frames than the page draws`);
    if(gpuFrames.some(f=>f.leanRenders))fail('a page-gpu frame asked Lean for a render');
    const st=gpuFrames.at(-1).pageGpu;
    // A Canvas 2D page (canvas-chart.html) gives Lean's pixels in place of passes.
    if(!st||(st.passes+(st.pixels??0))<10||st.blits<10||st.errors)fail('replay stats',JSON.stringify(st));
  }
  const replayWarnings=logs.filter(l=>/page GPU|WebGPU:|WebGL:/.test(l));
  if(replayWarnings.length)fail('console:',replayWarnings.slice(0,5).join(' | '));
  if(shotFile){const r=await s('Page.captureScreenshot',{format:'png'});fs.writeFileSync(shotFile,Buffer.from(r.data,'base64'));console.log('screenshot',shotFile);}
}finally{chrome.kill();server.close();await sleep(300);try{fs.rmSync(profile,{recursive:true,force:true});}catch{/* Chrome still closing */}}
console.log(failures?`hub_page_gpu_check: ${failures} failures`:'hub_page_gpu_check: pass');
process.exit(failures?1:0);
