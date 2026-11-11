// Page requests on the Hub (issue 374): XMLHttpRequest and fetch of page scripts in headless Chrome,
// through a local stand-in for GitHub Pages (the Hub files of this checkout and a local engine
// build, .build/web-render/engines, or --runtime DIR). The engine decides each request
// (L4Factoidal/Net/PageFetch.lean); the Hub worker (browser-worker.mjs) moves the bytes with the
// browser's own fetch, which enforces CORS for the Hub's origin.
//
// The page (made here, served as pages/net-sample.html, not published) makes an async
// XMLHttpRequest, a sync one in a later task, a fetch(), a fetch() of a data: URL and a
// cross-origin request with no CORS header (which must fail), and adds a link whose address
// holds what it saw (the Hub reports a page's links in window.foafnautFrame).
//
//   node labs/demos/foafnaut/hub_net_check.mjs [--runtime DIR]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser or engine.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_net_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no web-render.wasm in ${runtimeDir}`);process.exit(0);}
// Another origin with no CORS header: its answer must not reach the page.
const other=http.createServer((req,res)=>{res.writeHead(200,{'content-type':'text/plain'});res.end('secret');});
await new Promise(r=>other.listen(0,'127.0.0.1',r));
const page=`<!doctype html><html><head><meta charset="utf-8"><title>net pending</title></head><body><p>net</p><script>
const seen=[];const done=()=>{if(seen.length!==5)return;const a=document.createElement('a');a.href='#'+encodeURIComponent('net '+seen.sort().join(' | '));a.textContent='result';document.body.appendChild(a);};
const add=s=>{seen.push(s);done();};
const x=new XMLHttpRequest();
x.onloadend=()=>{
  add('async '+x.status+' '+x.responseText);
  const y=new XMLHttpRequest();y.open('GET','net-data.txt?s',false);y.send();add('sync '+y.status+' '+y.responseText);
  fetch('net-data.txt?f').then(r=>r.text()).then(t=>add('fetch '+t),e=>add('fetch failed'));
  fetch('data:,inline').then(r=>r.text()).then(t=>add('dataurl '+t),e=>add('dataurl failed'));
  const z=new XMLHttpRequest();z.open('GET','http://127.0.0.1:${other.address().port}/x');
  z.onerror=()=>add('cors refused '+z.status);z.onload=()=>add('cors LEAK '+z.responseText);z.send();
};
x.open('GET','net-data.txt?a');x.send();
</script></body></html>`;
const want='net async 200 oka | cors refused 0 | dataurl inline | fetch okf | sync 200 oks';
const types={'.html':'text/html','.xml':'application/xml','.xsl':'application/xml','.mjs':'text/javascript','.js':'text/javascript',
  '.wasm':'application/wasm','.ttl':'text/turtle','.css':'text/css','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const cache=new Map();
async function get(p,search){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p===pages+'net-sample.html')return {status:200,type:'text/html',body:Buffer.from(page)};
  if(p===pages+'net-data.txt')return {status:200,type:'text/plain',body:Buffer.from('ok'+search.slice(1))};
  if(p.startsWith(pages)&&p.endsWith('.css')&&!fs.existsSync(path.join(pagesDir,p.slice(pages.length))))return {status:404,type:'text/plain',body:Buffer.from('not here')};
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(rt)&&(f=local(runtimeDir,p.slice(rt.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const u=new URL(req.url,'http://x'),e=await get(u.pathname,u.search);const gz=zlib.gzipSync(e.body,{level:1});
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':gz.length,'cache-control':'no-store'});res.end(gz);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`,sampleURL=base+'pages/net-sample.html';
const profile=fs.mkdtempSync('/tmp/hub-net-check-');
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
  const consoleLines=[];
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.method==='Runtime.consoleAPICalled')consoleLines.push(m.params.args.map(a=>a.value??a.description).join(' '));if(m.method==='Target.attachedToTarget'){const sid=m.params.sessionId;socket.send(JSON.stringify({id:++id,method:'Runtime.enable',sessionId:sid}));socket.send(JSON.stringify({id:++id,method:'Runtime.runIfWaitingForDebugger',sessionId:sid}));}if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const {targetId}=await send('Target.createTarget',{url:'about:blank'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const s=(m,p)=>send(m,p,sessionId);
  await s('Page.enable');await s('Runtime.enable');
  await s('Target.setAutoAttach',{autoAttach:true,waitForDebuggerOnStart:false,flatten:true});
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
  await go(sampleURL);
  const result=st=>{const l=(st?.frame?.links??[]).map(l=>String(l[1])).find(h=>h.includes('#net%20'));return l?decodeURIComponent(l.slice(l.indexOf('#')+1)):undefined;};
  const st=await until(st=>at(sampleURL)(st)&&result(st)!==undefined,60000);
  if(result(st)!==want){fail('page requests on the Hub:',JSON.stringify(result(st)),'want',JSON.stringify(want));
    console.log('  frame:',JSON.stringify({scripts:st?.frame?.scripts,url:st?.frame?.url,keys:Object.keys(st?.frame??{})}).slice(0,1500));
    for(const l of consoleLines.slice(-25))console.log('  console:',String(l).slice(0,300));}
  else console.log(JSON.stringify({step:'page requests',result:result(st)}));
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();other.close();fs.rmSync(profile,{recursive:true,force:true,maxRetries:10,retryDelay:200});}
console.log(failures?`hub net check: ${failures} failures`:'hub net check: pass');
process.exit(failures?1:0);
