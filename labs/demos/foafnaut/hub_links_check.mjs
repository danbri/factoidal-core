// Every link of the demo index, clicked in the Hub (WebRoute.lean, owner 2026-11-08), in headless
// Chrome through a local stand-in for GitHub Pages: the Hub files (docs/web/hub/foafnaut/*.mjs)
// and the demo pages of this checkout, with (a) the runtime published on the live site and
// (b) a fresh local engine build (.build/web-render/engines, or --runtime DIR).
//
// For each link: it goes where the link rules say, in the tab; none is handed to the host
// browser (only a link to another origin than the stand-in is, which on Pages is this site);
// none is refused. Back after it returns to the index, and after foafnaut:graph forward
// returns to the graph (history_roundtrip). The published engine predates the shellRoute op,
// so (a) checks the fallback rules of link-route.mjs and (b) Lean's.
//
// Run it before every Pages deploy (docs/web/hub/README.md):
//   node labs/demos/foafnaut/hub_links_check.mjs [--runtime DIR] [--only published|local]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const localRuntime=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url))),only=opt('--only','');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_links_check.mjs needs Chrome (set CHROME)');process.exit(0);}
const types={'.html':'text/html','.xml':'application/xml','.xsl':'application/xml','.mjs':'text/javascript','.js':'text/javascript',
  '.wasm':'application/wasm','.ttl':'text/turtle','.css':'text/css','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.json':'application/json'};
const typeOf=f=>types[path.extname(f)]??'application/octet-stream';

let runtimeDir='';
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',pages=hub+'pages/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  const local=(dir,rest)=>{const f=path.join(dir,decodeURIComponent(rest));return f.startsWith(dir)&&fs.existsSync(f)&&fs.statSync(f).isFile()?f:undefined;};
  let f;
  if(p.startsWith(pages)&&(f=local(pagesDir,p.slice(pages.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&(f=local(hubDir,p.slice(hub.length))))return {status:200,type:typeOf(f),body:fs.readFileSync(f)};
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
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`,indexURL=base+'pages/index.html';

const profile=fs.mkdtempSync('/tmp/hub-links-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  if(!ws)throw Error("Chrome did not start: no answer on /json/version after 30 s");
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  async function open(query,width,height){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width,height,deviceScaleFactor:1,mobile:false});
    // Frames as they come, and what the page hands to the host browser.
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];window.__opened=[];window.open=u=>{window.__opened.push(String(u));return {};};
      Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:base+'?'+query});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const last=()=>evaluate(`({frame:window.__frames.at(-1)??null,n:window.__frames.length,opened:window.__opened,title:document.title,note:document.querySelector('#note').hidden?'':document.querySelector('#note').textContent})`);
    return {
      last,
      // Until the last frame passes `test`, or the time is up: the state then.
      async until(test,limit=30000){const t=Date.now();let st;
        while(Date.now()-t<limit){await sleep(150);st=await last().catch(()=>undefined);if(st&&test(st))return st;}
        return st;},
      async click(x,y){await s('Page.bringToFront');
        for(const type of ['mouseMoved','mousePressed','mouseReleased'])await s('Input.dispatchMouseEvent',{type,x,y,button:'left',buttons:type==='mousePressed'?1:0,clickCount:1});},
      async wheel(x,y,deltaY){await s('Page.bringToFront');await s('Input.dispatchMouseEvent',{type:'mouseWheel',x,y,deltaX:0,deltaY});},
      // Back and forward as Lean's key table has them: Command-Left and Right on a Mac, Alt elsewhere.
      async key(key,code,keyCode){await s('Page.bringToFront');const mac=process.platform==='darwin';
        for(const type of ['keyDown','keyUp'])await s('Input.dispatchKeyEvent',{type,key,code,windowsVirtualKeyCode:keyCode,modifiers:mac?4:1});},
      close:()=>send('Target.closeTarget',{targetId})};
  }
  const runs=[{name:'published',runtime:''},{name:'local',runtime:localRuntime}].filter(r=>!only||r.name===only);
  for(const run of runs){
    if(run.runtime&&!fs.existsSync(path.join(run.runtime,'web-render.wasm'))){console.log(`NOT RUN: ${run.name}: no web-render.wasm in ${run.runtime}`);continue;}
    runtimeDir=run.runtime;cache.clear();
    const width=1000,height=4800; // the index is about 4,100 px tall on 2026-11-09; links below the window cannot be clicked
    const page=await open('page=index.html&stats=1&layers=0',width,height);
    const atIndex=st=>st.frame?.url===indexURL&&Array.isArray(st.frame.links);
    let st=await page.until(atIndex,90000);
    if(!st||!atIndex(st)){fail(run.name,'the index did not load',JSON.stringify(st?.note??st?.title));await page.close();continue;}
    const hrefs=[...new Set(st.frame.links.map(l=>l[1]))];
    console.log(JSON.stringify({run:run.name,routes:st.frame.routes,links:hrefs.length}));
    if(hrefs.length<30)fail(run.name,'the index has',hrefs.length,'links');
    if(!hrefs.includes('foafnaut:graph'))fail(run.name,'foafnaut:graph is not a link of the index');
    const results={navigated:0,host:0,refused:0,other:0};
    for(const href of hrefs){
      st=await page.until(atIndex,20000);
      const link=st?.frame?.links?.find(l=>l[1]===href);
      if(!link){fail(run.name,href,'the index is not on screen to click it');continue;}
      const [,,x,y,w,h]=link,cx=Math.round(x+w/2),cy=Math.round(y+h/2);
      if(cy>=height){fail(run.name,href,'is below the window',cy);continue;}
      const opened=st.opened.length;
      const target=href.startsWith('foafnaut:')?href:new URL(href,indexURL).href;
      const elsewhere=/^https?:/.test(target)&&new URL(target).origin!==origin;
      await page.click(cx,cy);
      const after=await page.until(s=>s.opened.length>opened||(s.frame&&s.frame.url!==indexURL),20000);
      let outcome;
      if(after.opened.length>opened)outcome={kind:'host',url:after.opened.at(-1)};
      else if(!after.frame||after.frame.url===indexURL)outcome={kind:'other',url:'(nothing happened)'};
      else if(/Page refused|Needs a newer engine/.test(after.title))outcome={kind:'refused',url:after.frame.url,title:after.title};
      else outcome={kind:'navigated',url:after.frame.url,title:after.title};
      results[outcome.kind]++;
      console.log(JSON.stringify({run:run.name,href,...outcome}));
      if(elsewhere){if(outcome.kind!=='host'||outcome.url!==target)fail(run.name,href,'another origin than the stand-in should go to the host browser',JSON.stringify(outcome));continue;}
      if(outcome.kind==='host')fail(run.name,href,'was handed to the host browser');
      else if(outcome.kind==='refused')fail(run.name,href,'was refused',outcome.title);
      else if(outcome.kind!=='navigated'||outcome.url!==target)fail(run.name,href,'went to',JSON.stringify(outcome),'not',target);
      // Back returns to the index; after the graph, forward returns to it (history_roundtrip).
      await page.key('ArrowLeft','ArrowLeft',37);
      let back=await page.until(atIndex,20000);
      if(!back||!atIndex(back)){fail(run.name,href,'back did not return to the index',back?.frame?.url);await page.close();break;}
      if(href==='foafnaut:graph'){
        await page.key('ArrowRight','ArrowRight',39);
        const forward=await page.until(s=>s.frame?.url==='foafnaut:graph',20000);
        if(forward?.frame?.url!=='foafnaut:graph')fail(run.name,'forward did not return to foafnaut:graph',forward?.frame?.url);
        await page.key('ArrowLeft','ArrowLeft',37);
        back=await page.until(atIndex,20000);
        if(!back||!atIndex(back))fail(run.name,'back from the graph again did not return to the index');
      }
    }
    console.log(JSON.stringify({run:run.name,...results}));
    await page.close();
    // A link below the first screen, after a scroll, in a short window (2026-11-08: Lean kept
    // link regions only down to the viewport, so rows further down clicked nothing).
    const short=await open('page=sitemap.xml&stats=1&layers=0',width,700),sitemapURL=base+'pages/sitemap.xml';
    const atSitemap=st=>st.frame?.url===sitemapURL&&Array.isArray(st.frame.links);
    if(!atSitemap(await short.until(atSitemap,60000)??{})){fail(run.name,'sitemap.xml did not load');await short.close();continue;}
    for(let i=0;i<20;i++){await short.wheel(500,400,400);await sleep(60);}
    const low=await short.until(st=>atSitemap(st)&&st.frame.scroll>500,20000);
    const row=low?.frame?.links?.find(l=>/\.(html|xml)$/.test(l[1])&&l[3]>100&&l[3]+l[5]<690);
    if(!row){fail(run.name,'sitemap.xml: no page link on screen after a scroll to',low?.frame?.scroll);await short.close();continue;}
    await short.click(Math.round(row[2]+row[4]/2),Math.round(row[3]+row[5]/2));
    const went=await short.until(st=>st.frame&&st.frame.url!==sitemapURL,20000);
    const want=new URL(row[1],sitemapURL).href;
    if(went?.frame?.url!==want)fail(run.name,'sitemap.xml: a link at scroll',low.frame.scroll,'went to',went?.frame?.url,'not',want);
    else console.log(JSON.stringify({run:run.name,scrolledLink:row[1],scroll:low.frame.scroll,kind:'navigated'}));
    await short.close();
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();try{fs.rmSync(profile,{recursive:true,force:true,maxRetries:10,retryDelay:100});}catch{/* Chrome still closing */}}
console.log(failures?`hub links check: ${failures} failures`:'hub links check: pass');
process.exit(failures?1:0);
