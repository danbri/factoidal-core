// The Hub on a Retina screen (dprfix, 2026-11-09; WebDocument, section "Device pixels"), in
// headless Chrome through a local stand-in for GitHub Pages (as hub_links_check.mjs): the
// Hub files of this checkout, the runtime of a folder (--runtime) or of the live site, and
// pages from the live site. Each page is opened in a 1440 by 900 CSS px window at device
// pixel ratio 1 and 2. The layout must be the same in CSS px: every link region of the 2x
// frame is the 1x one times two (x, width, height, and y from the first link). Before the fix
// the Hub laid out in device pixels and scaled only the text: at 2x a 760px column was 380
// CSS px and the links moved. --shots DIR keeps a screenshot of each window.
//
// node labs/demos/foafnaut/hub_dpr_check.mjs [--runtime DIR] [--pages a.html,b.html] [--shots DIR]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url)),runtimeDir=opt('--runtime',''),shots=opt('--shots','');
const pages=opt('--pages','spinal-tap-sparql.html,showcase.html').split(','),LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_dpr_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(runtimeDir&&!fs.existsSync(path.join(runtimeDir,'web-render.wasm'))){console.log(`NOT RUN: no web-render.wasm in ${runtimeDir}`);process.exit(0);}
if(shots)fs.mkdirSync(shots,{recursive:true});
const sleep=ms=>new Promise(r=>setTimeout(r,ms));

const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&fs.existsSync(path.join(hubDir,p.slice(hub.length))))return {status:200,type:'text/javascript',body:fs.readFileSync(path.join(hubDir,p.slice(hub.length)))};
  if(runtimeDir&&p.startsWith(rt)&&fs.existsSync(path.join(runtimeDir,p.slice(rt.length)))){
    const f=path.join(runtimeDir,p.slice(rt.length));
    return {status:200,type:f.endsWith('.wasm')?'application/wasm':'text/javascript',body:fs.readFileSync(f)};
  }
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);const gz=zlib.gzipSync(e.body,{level:1});
    res.writeHead(e.status,{'content-type':e.type,'content-encoding':'gzip','content-length':gz.length,'cache-control':'max-age=600'});res.end(gz);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const base=`http://127.0.0.1:${server.address().port}/factoidal/web/hub/foafnaut/`;

const profile=fs.mkdtempSync('/tmp/hub-dpr-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error('Chrome did not start: no answer on /json/version after 30 s');
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  // One page at a pixel ratio: its first frame with links (?stats=1&layers=0 posts them).
  async function frameAt(name,dpr){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width:1440,height:900,deviceScaleFactor:dpr,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];window.__t0=performance.now();Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:`${base}?page=${name}&stats=1&layers=0`});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const want=st=>st?.frame?.url?.endsWith('/'+name)&&Array.isArray(st.frame.links)&&st.frame.links.length>0;
    let st;const t=Date.now();
    while(Date.now()-t<120000){await sleep(250);st=await evaluate(`({frame:window.__frames.at(-1)??null,first:window.__frames.find(f=>String(f.url).endsWith('/${name}'))??null,canvas:(()=>{const c=document.querySelector('canvas');return c?[c.width,c.height,c.clientWidth,c.clientHeight]:null;})()})`).catch(()=>undefined);if(want(st))break;}
    // Let the page settle (scripts, fonts), then take the last frame.
    await sleep(3000);st=await evaluate(`({frame:window.__frames.at(-1)??null,first:window.__frames.find(f=>String(f.url).endsWith('/${name}'))??null,n:window.__frames.length})`).catch(()=>st);
    if(shots){const {data}=await s('Page.captureScreenshot',{format:'png'});fs.writeFileSync(path.join(shots,`${name.replace(/\.html$/,'')}-dpr${dpr}.png`),Buffer.from(data,'base64'));}
    await send('Target.closeTarget',{targetId});
    return st;
  }
  for(const name of pages){
    const one=await frameAt(name,1),two=await frameAt(name,2);
    for(const [dpr,st] of [[1,one],[2,two]])console.log(JSON.stringify({page:name,dpr,links:st?.frame?.links?.length,first:st?.first?{layoutMs:st.first.layoutMs,totalMs:st.first.totalMs,percent:st.first.percent}:null,
      last:st?.frame?{layoutMs:st.frame.layoutMs,drawMs:st.frame.drawMs,totalMs:st.frame.totalMs,rows:st.frame.rows,primitives:st.frame.primitives}:null}));
    const a=one?.frame?.links,b=two?.frame?.links;
    if(!a?.length||!b?.length){fail(name,'no links at',a?.length?'dpr 2':'dpr 1');continue;}
    if(a.length!==b.length){fail(name,`${a.length} links at dpr 1, ${b.length} at dpr 2`);continue;}
    // [source, href, x, y, w, h]; y from the first link, so the chrome's rows do not count.
    let worst=0,off=0;
    a.forEach((l,i)=>{const m=b[i];
      const d=[Math.abs(m[2]-2*l[2]),Math.abs((m[3]-b[0][3])-2*(l[3]-a[0][3])),Math.abs(m[4]-2*l[4]),Math.abs(m[5]-2*l[5])];
      worst=Math.max(worst,...d);
      if(m[1]!==l[1]||Math.max(...d)>1){off++;if(off<=3)console.log(`  ${name} link ${i} ${l[1]}: 1x ${JSON.stringify(l.slice(2))}, 2x ${JSON.stringify(m.slice(2))}`);}});
    if(off)fail(name,`${off} of ${a.length} links are not the 1x layout times two`);
    console.log(JSON.stringify({page:name,links:a.length,worstDevicePx:worst}));
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill();server.close();try{fs.rmSync(profile,{recursive:true,force:true});}catch{}}
console.log(failures?`hub_dpr_check: ${failures} failures`:'hub_dpr_check: ok');
process.exit(failures?1:0);
