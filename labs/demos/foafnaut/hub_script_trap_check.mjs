// A trap in BubblePopJS must not take the page down (Hub worker, scriptFailed): the page already
// drawn stays, its scripts stop, the console tab says why, and the engine still works.
// Forced by a script that evaluates 200,000 nested array literals: LeanJS.callDepth bounds calls
// and not the nesting of one expression, so this overflows the browser's WebAssembly stack. Headless Chrome through a local stand-in
// for GitHub Pages (as hub_console_check.mjs), with a local build (.build/web-render/engines, or --runtime DIR).
//   node labs/demos/foafnaut/hub_script_trap_check.mjs [--runtime DIR]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser or engine.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const deepPage='<!doctype html><title>Deep recursion</title><p>The page is drawn before its script runs.</p><script>try{eval("[".repeat(200000)+"]".repeat(200000))}catch(e){console.log(e.name)}</script>';
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_script_trap_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no web-render.wasm in ${runtimeDir}`);process.exit(0);}
const types={'.html':'text/html','.xml':'application/xml','.xsl':'application/xml','.mjs':'text/javascript','.js':'text/javascript',
  '.wasm':'application/wasm','.ttl':'text/turtle','.css':'text/css','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p===pages+'deep-recursion.html')return {status:200,type:'text/html',body:Buffer.from(deepPage)};
  if(p===pages+'after-trap.html')return {status:200,type:'text/html',body:Buffer.from("<!doctype html><title>after</title><p id=x>x</p><script>var a=document.createElement('a');a.href='ran-marker.html';a.textContent='ran';document.getElementById('x').appendChild(a)</script>")};
  if(p.startsWith(pages)&&p.endsWith('.css')&&!fs.existsSync(path.join(pagesDir,p.slice(pages.length))))return {status:404,type:'text/plain',body:Buffer.from('not here')};
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);const gz=zlib.gzipSync(e.body,{level:1});
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':gz.length,'cache-control':'no-store'});res.end(gz);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`,deepURL=base+'pages/deep-recursion.html';
const profile=fs.mkdtempSync('/tmp/hub-script-trap-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error('Chrome did not start: no answer on /json/version after 30 s');
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const {targetId}=await send('Target.createTarget',{url:'about:blank'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const s=(m,p)=>send(m,p,sessionId);
  await s('Page.enable');await s('Runtime.enable');
  await s('Emulation.setDeviceMetricsOverride',{width:1000,height:1400,deviceScaleFactor:1,mobile:false});
  await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];
    Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
  await s('Page.navigate',{url:base+'?page=index.html&stats=1&layers=0&strict=1'});
  const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
  const last=()=>evaluate(`({frame:window.__frames.at(-1)??null,title:document.title})`);
  const until=async(test,limit=60000)=>{const t=Date.now();let st;
    while(Date.now()-t<limit){await sleep(150);st=await last().catch(()=>undefined);if(st&&test(st))return st;}
    return st;};
  // The Hub address (#...) goes through Lean's link rules, as a typed address.
  const go=address=>evaluate(`location.hash=${JSON.stringify(address)}`);
  const at=url=>st=>st.frame?.url===url;
  if(!at(base+'pages/index.html')(await until(at(base+'pages/index.html'),90000)??{}))throw Error('the index did not load');
  await go(deepURL);
  let st=await until(st=>at(deepURL)(st)&&/Deep recursion/.test(st.title),30000);
  if(!/Deep recursion/.test(st?.title??''))throw Error('the page was not drawn: '+st?.title);
  // The script ran after the first frame; its trap is in the scripts stats.
  const trapped=await until(st=>at(deepURL)(st)&&st.frame?.scripts?.error,30000);
  const error=trapped?.frame?.scripts?.error??'';
  if(!error)fail('no trap: the script did not overflow the WebAssembly stack');
  else console.log(JSON.stringify({step:'trap',error}));
  // The page is still there, and the engine still draws another page and runs its scripts.
  st=await last();
  if(!at(deepURL)(st)||!/Deep recursion/.test(st.title))fail('the page did not stay after the trap:',st?.title);
  else console.log(JSON.stringify({step:'page stays',title:st.title}));
  // The console tab of the page says why.
  const mac=await evaluate(`/Mac|iPhone|iPad/.test(navigator.platform||navigator.userAgent)`);
  await s('Page.bringToFront');
  for(const type of ['keyDown','keyUp'])await s('Input.dispatchKeyEvent',{type,key:'j',code:'KeyJ',windowsVirtualKeyCode:74,modifiers:mac?1|4:1|2});
  st=await until(st=>at('foafnaut:console')(st)&&/Console/.test(st.title),20000);
  const system=Number(/\((\d+) System/.exec(st?.title??'')?.[1]??0);
  if(system<1)fail('the console tab shows no System entry:',st?.title);
  else console.log(JSON.stringify({step:'console',title:st.title}));
  const after=base+'pages/after-trap.html';
  await go(after);
  const ran=st=>at(after)(st)&&(st.frame?.links??[]).some(l=>String(l[1]).endsWith('ran-marker.html'));
  st=await until(ran,30000);
  if(!ran(st??{}))fail('the engine did not run another page after the trap:',st?.frame?.url,JSON.stringify(st?.frame?.links?.slice(0,3)));
  else console.log(JSON.stringify({step:'another page runs its scripts',engine:st.frame.scripts?.engine}));
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');await new Promise(r=>chrome.once('exit',r));server.close();try{fs.rmSync(profile,{recursive:true,force:true,maxRetries:5,retryDelay:200});}catch{}}
console.log(failures?`hub script trap check: ${failures} failures`:'hub script trap check: pass');
process.exit(failures?1:0);
