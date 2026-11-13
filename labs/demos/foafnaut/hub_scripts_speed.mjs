// Page script speed on the Hub, with the guest in WasmVM (the interpreter, compiled to Wasm
// with the engine) and with the guest translated by Lean for the browser's own WebAssembly
// engine (AOT, docs/designissues/2026-11-08-wasmvm-aot.md). Headless Chrome through the same
// local stand-in for GitHub Pages as hub_links_check.mjs: the Hub files of this checkout, the
// demo pages, the runtime of a local engine build (--runtime) and the guest module (--guest),
// the rest from the live site.
//
// Each case runs in each mode of --modes (default aot,wasmvm): `aot` (the worker of this
// checkout, pinned to QuickJS-NG), `wasmvm` (the same, with the AOT probe answered false, so the
// same engine runs the guest in WasmVM) and `bubblepop` (the worker with no setting: the Hub's
// default, BubblePopJS, the JavaScript engine written in Lean).
//
// - page start: the start turn of a page whose script writes one text node, the worker's first;
// - fib(24) in QuickJS: the start turn of a page whose script computes fib(24);
// - a WPT page start: the start turn of a testharness.js page (dom/nodes);
// - an animation frame: labs/demos/foafnaut/pages/timers-and-clicks.html, the mean and the
//   largest time of an advance turn over a few seconds, and the turns run.
//
//   node labs/demos/foafnaut/hub_scripts_speed.mjs [--runtime DIR] [--guest FILE] [--seconds N] [--modes aot,wasmvm,bubblepop]
// CHROME=/path/to/chrome overrides the browser. NOT RUN with no browser.
// QUICKJS-EXCEPTION: the aot and wasmvm modes pin QuickJS-NG to compare its speed with BubblePopJS.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const wptDir=fileURLToPath(new URL('../../../third_party/testing/wpt-scripting/',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const guest=opt('--guest',path.join(process.env.HOME??'','working/qjs-wasm/qjs-wasmvm.wasm'));
const seconds=Number(opt('--seconds','4'));
const modes=opt('--modes','aot,wasmvm').split(',');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_scripts_speed.mjs needs Chrome (set CHROME)');process.exit(0);}
const types={'.html':'text/html','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.json':'application/json','.css':'text/css'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
// Pages made here, served from the pages folder.
const made={
  'speed-start.html':'<!doctype html><html><head><meta charset="utf-8"><title>start</title></head><body><p id="s">...</p><script>document.getElementById("s").textContent="started";</script></body></html>',
  'speed-fib.html':'<!doctype html><html><head><meta charset="utf-8"><title>fib(24)</title></head><body><p id="out">...</p>'+
    '<script>function fib(n){return n<2?n:fib(n-1)+fib(n-2);}document.getElementById("out").textContent="fib(24) = "+fib(24);</script></body></html>',
};
const wptPage='dom/nodes/Node-appendChild.html';
let mode='aot';
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/',guests='/factoidal/web/hub/wasm-guests/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p.startsWith(pages)&&made[p.slice(pages.length)])return {status:200,type:'text/html',body:Buffer.from(made[p.slice(pages.length)])};
  if(p===pages+'speed-wpt.html')return {status:200,type:'text/html',body:fs.readFileSync(path.join(wptDir,wptPage))};
  if(p.startsWith('/resources/')&&(f=local(path.join(wptDir,'resources'),p.slice('/resources/'.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p===hub+'browser-worker.mjs'){
    let text=fs.readFileSync(path.join(hubDir,'browser-worker.mjs'),'utf8');
    if(mode==='wasmvm'){const probe='info.aot===true';if(!text.includes(probe))throw Error('no AOT probe in the worker');text=text.replace(probe,'false');}
    // aot and wasmvm pin QuickJS-NG; bubblepop runs the Hub's default, BubblePopJS.
    if(mode!=='bubblepop'){const setting="let scriptSetting=''";if(!text.includes(setting))throw Error('no script setting in the worker');text=text.replace(setting,"let scriptSetting='quickjs'");}
    return {status:200,type:'text/javascript',body:Buffer.from(text)};
  }
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p===guests+'qjs-wasmvm.wasm'&&fs.existsSync(guest))return {status:200,type:'application/wasm',body:fs.readFileSync(guest)};
  const r=await fetch(LIVE+p);
  return {status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())};
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);const gz=zlib.gzipSync(e.body,{level:1});
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':gz.length,'cache-control':'no-store'});res.end(gz);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`;
const profile=fs.mkdtempSync('/tmp/hub-scripts-speed-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
// Chrome and its profile (about 170 MB) go away on every exit, also when the run is killed.
const stop=async()=>{if(chrome.exitCode===null){chrome.kill('SIGKILL');await new Promise(r=>chrome.once('exit',r));}
  server.close();try{fs.rmSync(profile,{recursive:true,force:true});}catch{}};
for(const signal of ['SIGINT','SIGTERM'])process.on(signal,()=>stop().then(()=>process.exit(1)));
const results={};
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error("Chrome did not start: no answer on /json/version after 30 s");
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map(),consoleLines=[];
  socket.onmessage=({data})=>{const m=JSON.parse(data);
    if(m.method==='Runtime.consoleAPICalled')consoleLines.push(m.params.args.map(a=>a.value??a.description).join(' '));
    if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  await send('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:false,flatten:true});
  async function open(page){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width:800,height:900,deviceScaleFactor:1,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];
      Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:`${base}?page=${page}&stats=1&strict=1`});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    return {evaluate,close:()=>send('Target.closeTarget',{targetId})};
  }
  const lastScripts=page=>page.evaluate('(window.__frames.filter(f=>f.scripts).at(-1)??{}).scripts??null');
  async function until(page,test,limit){const t=Date.now();let v;while(Date.now()-t<limit){await sleep(200);v=await lastScripts(page).catch(()=>null);if(v&&test(v))return v;}return v;}
  for(const m of modes){
    mode=m;results[m]={};
    // Page start: a page whose one script writes one text node, so that a frame follows (the first page of the worker, so the
    // realm with the page objects is made in this turn).
    let page=await open('speed-start.html');
    let st0=await until(page,s=>s.turns>=1&&s.startMs!==undefined,240000);
    // The time from navigation to the first frame the Hub shows: boot, the first script turn, a draw.
    const firstFrameMs=await page.evaluate('Math.round(window.__frames[0]?.t??0)');
    // And to the first frame after the page's script has run: boot, guest (QuickJS-NG only), start turn.
    const scriptDoneMs=await page.evaluate('Math.round(window.__frames.find(f=>(f.scripts?.turns??0)>=1)?.t??0)');
    results[m].start={engine:st0?.engine,path:st0?.path,startMs:st0?.startMs,firstFrameMs,scriptDoneMs};
    console.error(m,'start',JSON.stringify(results[m].start));
    await page.close();
    // fib(24): the start turn.
    page=await open('speed-fib.html');
    let st=await until(page,s=>s.turns>=1&&s.startMs!==undefined,240000);
    const text=await page.evaluate('window.__frames.at(-1)?.title??""');
    results[m].fib={engine:st?.engine,path:st?.path,startMs:st?.startMs,instructions:st?.instructions,hostCalls:st?.hostCalls};
    console.error(m,'fib',JSON.stringify(results[m].fib));
    await page.close();
    // A WPT testharness page: the start turn.
    page=await open('speed-wpt.html');
    st=await until(page,s=>s.turns>=1&&s.startMs!==undefined,240000);
    results[m].wpt={file:wptPage,engine:st?.engine,path:st?.path,startMs:st?.startMs,instructions:st?.instructions,hostCalls:st?.hostCalls};
    console.error(m,'wpt',JSON.stringify(results[m].wpt));
    await page.close();
    // An animation: advance turns of timers-and-clicks.html.
    page=await open('timers-and-clicks.html');
    st=await until(page,s=>s.turns>=2,240000);
    const t0=await page.evaluate('window.__frames.length');
    await sleep(seconds*1000);
    const frames=await page.evaluate(`window.__frames.slice(${t0}).filter(f=>f.scripts).map(f=>({t:f.t,ms:f.scripts.lastMs,turns:f.scripts.turns,total:f.totalMs}))`);
    const turns=frames.length?frames.at(-1).turns-frames[0].turns:0;
    const ms=frames.map(f=>f.ms);
    results[m].animation={engine:st?.engine,path:st?.path,framesShown:frames.length,turns,
      meanTurnMs:ms.length?Math.round(ms.reduce((a,b)=>a+b,0)/ms.length*100)/100:null,maxTurnMs:ms.length?Math.max(...ms):null,
      meanFrameTotalMs:frames.length?Math.round(frames.reduce((a,f)=>a+(f.total??0),0)/frames.length):null,seconds};
    console.error(m,'animation',JSON.stringify(results[m].animation));
    await page.close();
    void text;
  }
  console.log(JSON.stringify(results,null,1));
  // `path` is how the QuickJS-NG guest would run; `engine` is the script engine that ran the page.
  for(const m of modes)for(const [k,v] of Object.entries(results[m]))if(v.engine!==(m==='bubblepop'?'bubblepop':'quickjs')){console.error(`FAIL mode ${m}: ${k} ran on ${v.engine}`);process.exitCode=1;}
  const ratio=(a,b)=>a&&b?Math.round(b/a*10)/10:null;
  if(results.aot&&results.wasmvm)console.log(`speedup: fib(24) start ${ratio(results.aot.fib.startMs,results.wasmvm.fib.startMs)}x, WPT start ${ratio(results.aot.wpt.startMs,results.wasmvm.wpt.startMs)}x, animation turn ${ratio(results.aot.animation.meanTurnMs,results.wasmvm.animation.meanTurnMs)}x`);
  if(args.includes('--console'))for(const l of consoleLines.slice(-40))console.log('console:',l);
}finally{await stop();}
