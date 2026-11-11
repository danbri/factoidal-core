// The Shadow DOM and sandboxed frames demo page on the Hub (docs/designissues/2026-11-08-shadow-dom-frames.md),
// in headless Chrome through a local stand-in for GitHub Pages: the Hub files of this checkout, the
// demo pages, and a local engine build (.build/web-render/engines, or --runtime DIR). Checks that the
// page draws with no page note and no script exception in the console (the shadow roots, slots and the
// sandboxed frame's session run in its scripts). --shot FILE keeps a picture of an 800x2600 window,
// which shows the slot counts and the frame's message.
//   node labs/demos/foafnaut/hub_shadow_frames_check.mjs [--runtime DIR] [--shot FILE] [--page NAME]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser or engine.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const opt=(name,fallback)=>{const i=process.argv.indexOf(name);return i>0?process.argv[i+1]:fallback;};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=opt('--pages',fileURLToPath(new URL('./pages/',import.meta.url)));
const fontsDir=fileURLToPath(new URL('../../../third_party/fonts/',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const pageName=opt('--page','shadow-and-frames.html');
const guest=opt('--guest',`${process.env.HOME}/working/qjs-wasm/qjs-wasmvm.wasm`),shotFile=opt('--shot','');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_shadow_frames_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no engine in ${runtimeDir}`);process.exit(0);}
const types={'.html':'text/html','.mjs':'text/javascript','.js':'text/javascript','.wasm':'application/wasm','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/',guests='/factoidal/web/hub/wasm-guests/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(hub+'fonts/')&&(f=local(fontsDir,p.slice((hub+'fonts/').length))))return {status:200,type:'font/ttf',body:fs.readFileSync(f)};
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
const profile=fs.mkdtempSync('/tmp/hub-shadow-frames-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error("Chrome did not start");
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map(),logs=[];
  socket.onmessage=({data})=>{const m=JSON.parse(data);
    if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}
    if(m.method==='Runtime.exceptionThrown')logs.push('exception: '+JSON.stringify(m.params.exceptionDetails).slice(0,400));
    if(m.method==='Runtime.consoleAPICalled')logs.push(m.params.args.map(a=>a.value??a.description).join(' '));
    if(m.method==='Target.attachedToTarget')socket.send(JSON.stringify({id:++id,method:'Runtime.enable',params:{},sessionId:m.params.sessionId}));};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const {targetId}=await send('Target.createTarget',{url:'about:blank'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const s=(m,p)=>send(m,p,sessionId);
  await s('Page.enable');await s('Runtime.enable');
  await s('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:false,flatten:true});
  await s('Emulation.setDeviceMetricsOverride',{width:800,height:2600,deviceScaleFactor:1,mobile:false});
  await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];
    Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
  await s('Page.navigate',{url:base+`?page=${pageName}&stats=1`});
  const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
  await sleep(8000);
  const n=await evaluate('window.__frames.length').catch(()=>0);
  const note=await evaluate("(document.querySelector('#note')&&!document.querySelector('#note').hidden)?document.querySelector('#note').textContent:''").catch(e=>String(e));
  console.log(JSON.stringify({frames:n,note,last:await evaluate('JSON.stringify(window.__frames.at(-1)??null)').catch(()=>null)}));
  console.log('console:',JSON.stringify(logs.slice(0,40)));
  if(!n)fail('no frame drawn');
  if(note&&!/Starting/.test(note))fail('page note:',note);
  const bad=logs.filter(l=>/exception|scriptFailed|TypeError|ReferenceError/.test(l));
  if(bad.length)fail('console:',bad.slice(0,5).join(' | '));
  if(shotFile){const r=await s('Page.captureScreenshot',{format:'png'});fs.writeFileSync(shotFile,Buffer.from(r.data,'base64'));console.log('screenshot',shotFile);}
}finally{chrome.kill();server.close();await sleep(300);try{fs.rmSync(profile,{recursive:true,force:true});}catch{/* Chrome still closing */}}
console.log(failures?`hub_shadow_frames_check: ${failures} failures`:'hub_shadow_frames_check: pass');
process.exit(failures?1:0);
