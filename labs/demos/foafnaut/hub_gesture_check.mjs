// Back and forward swipes on the Hub (WebGesture.lean), in headless Chrome
// with touch input, through the same local stand-in for GitHub Pages as hub_feel_check.mjs:
// the Hub files of this checkout, the demo pages, and the runtime published on the live site
// (no op `gesture`: no swipes, nothing else changes) or a local build (with it).
//
// - A vertical drag from the edge scrolls; a tap at the edge, a short slow swipe and a swipe
//   from the middle go nowhere; with the op, an edge swipe does not scroll.
// - With the op: a swipe from the left edge goes back, from the right edge forward; a
//   trackpad swipe across (wheel deltaX) goes back and forward, a vertical one does not.
// - A drag in the middle still flings.
// - The address menu (WebShell.menuActions): with the op, a finger's tap on the address bar
//   gives the page Lean's action table; Copy address writes the page's address to the
//   clipboard and Paste and go goes to the address on it. Without the op, no table.
//
//   node labs/demos/foafnaut/hub_gesture_check.mjs [--runtime DIR] [--only published|local]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const localRuntime=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url))),only=opt('--only','');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_gesture_check.mjs needs Chrome (set CHROME)');process.exit(0);}
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
const origin=`http://127.0.0.1:${server.address().port}`,base=`${origin}/factoidal/web/hub/foafnaut/`;
const profile=fs.mkdtempSync('/tmp/hub-gesture-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const sleep=ms=>new Promise(r=>setTimeout(r,ms));
try{
  let ws;for(let i=0;i<100&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await sleep(100);}}
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  async function open(query,width,height){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await send('Browser.grantPermissions',{origin,permissions:['clipboardReadWrite','clipboardSanitizedWrite']});
    await s('Emulation.setDeviceMetricsOverride',{width,height,deviceScaleFactor:1,mobile:true});
    await s('Emulation.setTouchEmulationEnabled',{enabled:true,maxTouchPoints:5});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];window.__opened=[];window.open=u=>{window.__opened.push(String(u));return {};};
      Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:base+'?'+query});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const touch=async(type,points)=>s('Input.dispatchTouchEvent',{type,touchPoints:points.map(([x,y])=>({x,y}))});
    return {
      evaluate,
      frames:(from=0)=>evaluate(`window.__frames.slice(${from}).map(f=>({t:f.t,path:f.path,scroll:f.scroll,leanRenders:f.leanRenders,url:f.url,bandTop:f.bandTop}))`),
      count:()=>evaluate('window.__frames.length'),
      async until(test,limit=30000){const t=Date.now();let st;
        while(Date.now()-t<limit){await sleep(150);st=await evaluate('window.__frames.at(-1)??null').catch(()=>undefined);if(st&&test(st))return st;}
        return st;},
      // A finger from (x,y0) to (x,y1) in `steps` moves `ms` apart, then lifted.
      async drag(x,y0,y1,steps,ms){await s('Page.bringToFront');
        await touch('touchStart',[[x,y0]]);
        for(let i=1;i<=steps;i++){await sleep(ms);await touch('touchMove',[[x,Math.round(y0+(y1-y0)*i/steps)]]);}
        await touch('touchEnd',[]);},
      // A finger from (x0,y0) to (x1,y1) in `steps` moves `ms` apart, then lifted.
      async swipe(x0,y0,x1,y1,steps,ms){await s('Page.bringToFront');
        await touch('touchStart',[[x0,y0]]);
        for(let i=1;i<=steps;i++){await sleep(ms);await touch('touchMove',[[Math.round(x0+(x1-x0)*i/steps),Math.round(y0+(y1-y0)*i/steps)]]);}
        await touch('touchEnd',[]);},
      // Trackpad wheel events across (DOM deltaX), `ms` apart.
      async wheel(x,y,deltas,ms=16){await s('Page.bringToFront');
        for(const [deltaX,deltaY] of deltas){await s('Input.dispatchMouseEvent',{type:'mouseWheel',x,y,deltaX,deltaY});await sleep(ms);}},
      async tap(x,y){await s('Page.bringToFront');await touch('touchStart',[[x,y]]);await sleep(40);await touch('touchEnd',[]);},
      close:()=>send('Target.closeTarget',{targetId})};
  }
  // Settled: no new frame for `quiet` ms.
  async function settle(page,quiet=600,limit=10000){
    const t=Date.now();let n=await page.count(),since=Date.now();
    while(Date.now()-t<limit){await sleep(100);const m=await page.count();if(m!==n){n=m;since=Date.now();}else if(Date.now()-since>=quiet)return;}
  }
  const runs=[{name:'published',runtime:''},{name:'local',runtime:localRuntime}].filter(r=>!only||r.name===only);
  for(const run of runs){
    if(run.runtime&&!fs.existsSync(path.join(run.runtime,'web-render.wasm'))){console.log(`NOT RUN: ${run.name}: no web-render.wasm in ${run.runtime}`);continue;}
    runtimeDir=run.runtime;cache.clear();
    const width=400,height=800,sitemap=base+'pages/sitemap.xml',index=base+'pages/index.html';
    const page=await open('page=sitemap.xml&stats=1',width,height);
    let st=await page.until(f=>f.url===sitemap,90000);
    if(st?.url!==sitemap){fail(run.name,'sitemap.xml did not load');await page.close();continue;}
    await settle(page);
    const has=run.runtime!=='';
    const urlNow=async()=>(await page.frames((await page.count())-1))[0];
    const step=async(name,act,want,check)=>{
      const n=await page.count(),before=await urlNow();
      await act();await sleep(400);await settle(page);
      const frames=await page.frames(n),after=frames.at(-1)??before;
      const renders=frames.reduce((a,f)=>a+(f.leanRenders??0),0);
      console.log(JSON.stringify({run:run.name,step:name,url:after.url.replace(base,''),scroll:[before.scroll,after.scroll],frames:frames.length,leanRenders:renders}));
      if(after.url!==want)fail(run.name,name,': at',after.url,'not',want);
      check?.(before,after,frames);
    };
    // 1. A vertical drag that starts at the left edge scrolls and goes nowhere.
    await step('vertical from the edge',()=>page.drag(5,600,300,8,16),sitemap,(b,a)=>{if(a.scroll<=b.scroll)fail(run.name,'a vertical drag from the edge did not scroll');});
    // 2. A tap at the edge goes nowhere.
    await step('tap at the edge',()=>page.tap(4,500),sitemap);
    // 3. A short slow swipe from the left edge goes nowhere.
    await step('short swipe',()=>page.swipe(5,400,60,402,6,40),sitemap,(b,a)=>{if(has&&a.scroll!==b.scroll)fail(run.name,'a swipe scrolled the page');});
    // 4. A swipe from the left edge across a third of the window: back (with the op).
    await step('swipe back',()=>page.swipe(5,400,200,410,10,16),has?index:sitemap);
    // 5. From the right edge: forward.
    if(has)await step('swipe forward',()=>page.swipe(395,400,200,395,10,16),sitemap);
    // 6. A swipe from the middle of the window is no gesture.
    await step('swipe from the middle',()=>page.swipe(150,400,390,405,10,16),sitemap);
    // 7. Trackpad: content moving right (deltaX < 0) past 140 px, then 160 ms with no wheel: back.
    await step('trackpad back',()=>page.wheel(200,400,Array.from({length:10},()=>[-25,1])),has?index:sitemap);
    if(has)await step('trackpad forward',()=>page.wheel(200,400,Array.from({length:10},()=>[25,-1])),sitemap);
    // 8. A mostly vertical trackpad scroll: no navigation.
    await step('trackpad vertical',()=>page.wheel(200,400,Array.from({length:10},()=>[-20,60])),sitemap);
    // 9. A fling after a drag in the middle still glides on.
    await step('fling',()=>page.drag(200,700,500,6,16),sitemap,(b,a)=>{if(a.scroll-b.scroll<240)fail(run.name,'no fling after a drag:',b.scroll,'->',a.scroll);});
    // 10. The address menu: a finger's tap on the bar (navigation row, right of back and reload).
    const table=async()=>{for(let i=0;i<30;i++){const a=await page.evaluate('window.foafnautActions??[]');if(a.length)return a;await sleep(100);}return [];};
    await page.tap(150,18);
    const menu=await table();
    console.log(JSON.stringify({run:run.name,step:'address menu',actions:menu.map(a=>a.action)}));
    if(has&&menu.length!==2)fail(run.name,'no address menu after a tap on the bar');
    if(!has&&menu.length)fail(run.name,'an engine without the op showed the address menu');
    if(has&&menu.length===2){
      const centre=r=>[Math.round(r[0]+r[2]/2),Math.round(r[1]+r[3]/2)];
      await page.evaluate("navigator.clipboard.writeText('-')");
      await page.tap(...centre(menu.find(a=>a.action==='copy').rect));await sleep(400);
      const copied=await page.evaluate('navigator.clipboard.readText()');
      if(copied!==sitemap)fail(run.name,'Copy address wrote',copied,'not',sitemap);
      await page.evaluate(`navigator.clipboard.writeText(${JSON.stringify(index)})`);
      await page.tap(150,18);
      const again=await table();
      if(again.length!==2)fail(run.name,'no address menu on the second tap');
      else await step('paste and go',()=>page.tap(...centre(again.find(a=>a.action==='paste').rect)),index);
    }
    await page.close();
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();await sleep(300);try{fs.rmSync(profile,{recursive:true,force:true});}catch{/* Chrome still closing */}}
console.log(failures?`hub gesture check: ${failures} failures`:'hub gesture check: pass');
process.exit(failures?1:0);
