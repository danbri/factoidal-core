// hub_crypto_check.mjs: crypto.subtle of a page on the Hub, in headless Chrome: the engine's
// Wasm build and the QuickJS guest in the Hub worker, Lean deciding every WebCrypto rule and
// the browser's own crypto.subtle doing the primitives (docs/web/hub/foafnaut/crypto-host.mjs;
// record docs/designissues/2026-11-09-hacl-web-crypto.md, "The Hub"). The page runs
// tests/crypto/webcrypto_vectors.js with HOST true, on both of the Hub's paths for the
// guest (AOT, and WasmVM). Exit 1 when a vector fails or the page gives no result.
//
//   node labs/demos/foafnaut/hub_crypto_check.mjs [--runtime DIR] [--guest FILE]
// CHROME=/path/to/chrome overrides the browser. NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const guest=opt('--guest',path.join(process.env.HOME??'','working/qjs-wasm/qjs-wasmvm.wasm'));
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_crypto_check.mjs needs Chrome (set CHROME)');process.exit(0);}
const types={'.html':'text/html','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.json':'application/json','.css':'text/css'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
// Pages made here, served from the pages folder.
const vectors=fs.readFileSync(fileURLToPath(new URL('../../../tests/crypto/webcrypto_vectors.js',import.meta.url)),'utf8');
const made={
  // On the Hub the browser's crypto.subtle does the primitives (HOST).
  'crypto-vectors.html':'<!doctype html><html><head><meta charset="utf-8"><title>crypto</title></head><body><script>const HOST = true;\n'+vectors+'</script></body></html>',
};
let mode='aot';
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/',guests='/factoidal/web/hub/wasm-guests/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p.startsWith(pages)&&made[p.slice(pages.length)])return {status:200,type:'text/html',body:Buffer.from(made[p.slice(pages.length)])};
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p===hub+'browser-worker.mjs'){
    let text=fs.readFileSync(path.join(hubDir,'browser-worker.mjs'),'utf8');
    if(mode==='wasmvm'){const probe='info.aot===true';if(!text.includes(probe))throw Error('no AOT probe in the worker');text=text.replace(probe,'false');}
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
const profile=fs.mkdtempSync('/tmp/hub-crypto-check-');
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
  socket.addEventListener('message',({data})=>{const m=JSON.parse(data);
    if(m.method==='Target.attachedToTarget'){const sid=m.params.sessionId;
      socket.send(JSON.stringify({id:++id,method:'Runtime.enable',params:{},sessionId:sid}));
      socket.send(JSON.stringify({id:++id,method:'Target.setAutoAttach',params:{autoAttach:true,waitForDebuggerOnStart:false,flatten:true},sessionId:sid}));}});
  async function open(page){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width:800,height:900,deviceScaleFactor:1,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];
      Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:`${base}?page=${page}&stats=1`});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    return {evaluate,close:()=>send('Target.closeTarget',{targetId})};
  }
  // The page logs its results (worker console, "page: PASS …"); the last vector is the
  // CryptoKey check.
  let failed=0;
  for(const m of ['aot','wasmvm']){
    mode=m;
    consoleLines.length=0;
    const page=await open('crypto-vectors.html');
    const t0=Date.now();
    const lines=()=>[...new Set(consoleLines.flatMap(l=>l.replace(/^page: /,'').split('\n')).filter(l=>/^(PASS|FAIL) /.test(l)))];
    while(Date.now()-t0<Number(opt('--limit','300'))*1000){await sleep(500);if(lines().some(l=>/CryptoKey has no key bytes|FAIL threw/.test(l)))break;}
    const ls=lines(),fails=ls.filter(l=>l.startsWith('FAIL'));
    results[m]={passed:ls.length-fails.length,failed:fails.length,ms:Date.now()-t0};
    console.log(`${m}: ${ls.length-fails.length} passed, ${fails.length} failed${ls.length?'':' (no result)'} (${Math.round((Date.now()-t0)/1000)} s)`);
    for(const f of fails)console.log('  '+f);
    if(fails.length||!ls.length)failed++;
    await page.close();
  }
  if(failed)process.exitCode=1;
}finally{await stop();}
