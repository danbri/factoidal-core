// How the Hub feels to a finger (owner, 2026-11-08), in headless Chrome with touch input
// through the same local stand-in for GitHub Pages as hub_links_check.mjs: the Hub files of
// this checkout, the demo pages, and the runtime published on the live site or a local build.
//
// - A fling: after a quick drag the page keeps scrolling and slows down as iOS UIScrollView
//   does (velocity times 0.998 per ms); inside a band the steps make no Lean render.
// - A tap during a fling only stops it: no click, no navigation.
// - A fling stops at the top of the page.
// - A tap with no fling still follows a link.
//
//   node labs/demos/foafnaut/hub_feel_check.mjs [--runtime DIR] [--only published|local]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url));
const pagesDir=fileURLToPath(new URL('./pages/',import.meta.url));
const localRuntime=opt('--runtime',fileURLToPath(new URL('./.build/web-render/engines/',import.meta.url))),only=opt('--only','');
const LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_feel_check.mjs needs Chrome (set CHROME)');process.exit(0);}
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
const profile=fs.mkdtempSync('/tmp/hub-feel-check-');
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
    const width=400,height=800,pageURL=base+'pages/sitemap.xml';
    const page=await open('page=sitemap.xml&stats=1',width,height);
    let st=await page.until(f=>f.url===pageURL,90000);
    if(st?.url!==pageURL){fail(run.name,'sitemap.xml did not load');await page.close();continue;}
    // A band is made when the page is idle; a small scroll asks for it.
    await page.drag(200,500,470,3,16);
    st=await page.until(f=>f.bandTop!==undefined,20000);
    if(st?.bandTop===undefined){fail(run.name,'no band: this engine or browser has no layers');await page.close();continue;}
    await settle(page);
    // 1. A gentle fling, inside the band: about 0.6 px/ms at the lift.
    let n=await page.count(),before=(await page.frames(n-1))[0].scroll;
    await page.drag(200,600,540,6,16);
    const afterDrag=(await page.frames(n)).at(-1)?.scroll??before;
    await settle(page);
    let frames=await page.frames(n);
    const end=frames.at(-1).scroll,glide=end-afterDrag;
    const renders=frames.reduce((a,f)=>a+(f.leanRenders??0),0),paths=frames.reduce((a,f)=>(a[f.path]=(a[f.path]??0)+1,a),{});
    console.log(JSON.stringify({run:run.name,fling:'gentle',from:before,afterDrag,end,glide,frames:frames.length,leanRenders:renders,paths}));
    if(glide<40)fail(run.name,'a fling did not glide on after the lift:',glide,'px');
    if(renders!==0)fail(run.name,'a fling inside the band made',renders,'Lean renders');
    // The deceleration: velocity between frames falls about as 0.998^dt.
    const v=[];for(let i=1;i<frames.length;i++){const dt=frames[i].t-frames[i-1].t;if(dt>4)v.push({t:(frames[i].t+frames[i-1].t)/2,v:(frames[i].scroll-frames[i-1].scroll)/dt});}
    const head=v.slice(2,6),tail=v.slice(-8,-4);
    if(head.length&&tail.length){
      const mean=a=>a.reduce((x,y)=>x+y.v,0)/a.length,tm=a=>a.reduce((x,y)=>x+y.t,0)/a.length;
      const perMs=Math.pow(mean(tail)/mean(head),1/(tm(tail)-tm(head)));
      console.log(JSON.stringify({run:run.name,decelerationPerMs:+perMs.toFixed(5),vStart:+mean(head).toFixed(3),vLate:+mean(tail).toFixed(3)}));
      if(!(perMs>0.996&&perMs<0.9995))fail(run.name,'deceleration per ms',perMs,'is not near 0.998');
    }
    // 2. A tap during a fling stops it, and does not click.
    await settle(page);
    n=await page.count();
    await page.drag(200,700,500,6,16);
    await sleep(120);
    const atTap=(await page.frames(n)).at(-1).scroll;
    await page.tap(200,300);
    await sleep(80);
    const stopped=(await page.frames(n)).at(-1).scroll;
    await settle(page);
    frames=await page.frames(n);
    const last=frames.at(-1);
    console.log(JSON.stringify({run:run.name,tapDuringFling:{atTap,stopped,final:last.scroll,url:last.url}}));
    if(last.url!==pageURL)fail(run.name,'a tap during a fling followed a link to',last.url);
    if(last.scroll-stopped>30)fail(run.name,'the fling went on after a tap:',stopped,'->',last.scroll);
    // 3. A fling up stops at the top of the page (no frames go on scrolling at 0).
    n=await page.count();
    await page.drag(200,200,700,5,16);
    await settle(page);
    frames=await page.frames(n);
    console.log(JSON.stringify({run:run.name,flingToTop:{final:frames.at(-1).scroll,frames:frames.length}}));
    if(frames.at(-1).scroll!==0)fail(run.name,'a fling up did not reach the top:',frames.at(-1).scroll);
    const atZero=frames.filter(f=>f.scroll===0).length;
    if(atZero>3)fail(run.name,'the fling went on at the top for',atZero,'frames');
    await page.close();
    // 4. A tap with no fling follows a link (a one-frame view lists its links).
    const flat=await open('page=sitemap.xml&stats=1&layers=0',width,height);
    const listed=await flat.until(f=>f.url===pageURL,60000)&&await flat.evaluate('window.__frames.at(-1).links??null');
    const row=listed?.find(l=>/\.(html|xml)$/.test(l[1])&&l[3]>40&&l[3]+l[5]<height-10);
    if(!row)fail(run.name,'sitemap.xml: no page link on screen to tap',JSON.stringify(listed?.slice(0,4)));
    else{
      await flat.tap(Math.round(row[2]+row[4]/2),Math.round(row[3]+row[5]/2));
      const went=await flat.until(f=>f.url!==pageURL,20000),want=new URL(row[1],pageURL).href;
      console.log(JSON.stringify({run:run.name,tap:row[1],went:went?.url}));
      if(went?.url!==want)fail(run.name,'a tap on',row[1],'went to',went?.url);
    }
    await flat.close();
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();await sleep(300);try{fs.rmSync(profile,{recursive:true,force:true});}catch{/* Chrome still closing */}}
console.log(failures?`hub feel check: ${failures} failures`:'hub feel check: pass');
process.exit(failures?1:0);
