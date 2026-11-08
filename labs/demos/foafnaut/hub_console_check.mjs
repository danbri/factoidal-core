// Liberal mode and the console tab on the Hub (docs/designissues/2026-11-08-liberal-mode-and-console.md),
// in headless Chrome through a local stand-in for GitHub Pages: the Hub files of this checkout,
// the demo pages, the fixture fixtures/liberal/sample.html (served as pages/liberal-sample.html,
// not published), and a local engine build (.build/web-render/engines, or --runtime DIR).
//
// 1. Strict mode (the default) refuses the sample page.
// 2. foafnaut:liberal/on (the Settings checkbox), then the sample page again: it is drawn, with
//    the note that links to foafnaut:console.
// 3. The console key (Option-Command-J on a Mac, Control-Alt-J elsewhere) opens the console tab,
//    whose title counts its entries: at least one System entry.
// 4. The note's link opens the console too.
//
//   node labs/demos/foafnaut/hub_console_check.mjs [--runtime DIR]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser or engine.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const sample=fileURLToPath(new URL('./fixtures/liberal/sample.html',import.meta.url));
const runtimeDir=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url)));
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_console_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no web-render.wasm in ${runtimeDir}`);process.exit(0);}
const types={'.html':'text/html','.xml':'application/xml','.xsl':'application/xml','.mjs':'text/javascript','.js':'text/javascript',
  '.wasm':'application/wasm','.ttl':'text/turtle','.css':'text/css','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p===pages+'liberal-sample.html')return {status:200,type:'text/html',body:fs.readFileSync(sample)};
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
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`,sampleURL=base+'pages/liberal-sample.html';
const profile=fs.mkdtempSync('/tmp/hub-console-check-');
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
  await s('Page.navigate',{url:base+'?page=index.html&stats=1&layers=0'});
  const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
  const last=()=>evaluate(`({frame:window.__frames.at(-1)??null,title:document.title})`);
  const until=async(test,limit=60000)=>{const t=Date.now();let st;
    while(Date.now()-t<limit){await sleep(150);st=await last().catch(()=>undefined);if(st&&test(st))return st;}
    return st;};
  // The Hub address (#...) goes through Lean's link rules, as a typed address.
  const go=address=>evaluate(`location.hash=${JSON.stringify(address)}`);
  const at=url=>st=>st.frame?.url===url;
  if(!at(base+'pages/index.html')(await until(at(base+'pages/index.html'),90000)??{}))throw Error('the index did not load');
  // 1. Strict: refused.
  await go(sampleURL);
  let st=await until(st=>at(sampleURL)(st)&&/Page refused/.test(st.title),30000);
  if(!/Page refused/.test(st?.title??''))fail('strict mode did not refuse the sample page:',st?.title);
  else console.log(JSON.stringify({step:'strict',title:st.title}));
  // 2. Liberal: drawn, with the note.
  await go('foafnaut:liberal/on');await sleep(500);
  await go(base+'pages/index.html');await until(at(base+'pages/index.html'),20000);
  await go(sampleURL);
  st=await until(st=>at(sampleURL)(st)&&!/Page refused/.test(st.title)&&/Liberal mode sample/.test(st.title),30000);
  if(!/Liberal mode sample/.test(st?.title??''))fail('liberal mode did not draw the sample page:',st?.title);
  const note=st?.frame?.links?.find(l=>l[1]==='foafnaut:console');
  if(!note)fail('the page has no note that links to foafnaut:console');
  else console.log(JSON.stringify({step:'liberal',title:st.title,note:note.slice(2)}));
  // 3. The console key: a new tab with the console of the sample page.
  const mac=await evaluate(`/Mac|iPhone|iPad/.test(navigator.platform||navigator.userAgent)`);
  await s('Page.bringToFront');
  for(const type of ['keyDown','keyUp'])await s('Input.dispatchKeyEvent',{type,key:'j',code:'KeyJ',windowsVirtualKeyCode:74,modifiers:mac?1|4:1|2});
  st=await until(st=>at('foafnaut:console')(st)&&/Console/.test(st.title),20000);
  const system=Number(/\((\d+) System/.exec(st?.title??'')?.[1]??0);
  if(!at('foafnaut:console')(st??{}))fail('the console key did not open foafnaut:console:',st?.frame?.url,st?.title);
  else if(system<1)fail('the console tab shows no System entry:',st.title);
  else console.log(JSON.stringify({step:'console key',title:st.title}));
  // 4. The note's link, in the sample page's tab.
  await go(sampleURL);
  st=await until(st=>at(sampleURL)(st)&&/Liberal mode sample/.test(st.title),30000);
  const link=st?.frame?.links?.find(l=>l[1]==='foafnaut:console');
  if(link){
    const [,,x,y,w,h]=link;
    for(const type of ['mouseMoved','mousePressed','mouseReleased'])await s('Input.dispatchMouseEvent',{type,x:Math.round(x+w/2),y:Math.round(y+h/2),button:'left',buttons:type==='mousePressed'?1:0,clickCount:1});
    st=await until(st=>at('foafnaut:console')(st),20000);
    if(!at('foafnaut:console')(st??{})||!/[1-9]\d* System/.test(st.title))fail('the note did not open a console with a System entry:',st?.title);
    else console.log(JSON.stringify({step:'note link',title:st.title}));
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();fs.rmSync(profile,{recursive:true,force:true});}
console.log(failures?`hub console check: ${failures} failures`:'hub console check: pass');
process.exit(failures?1:0);
