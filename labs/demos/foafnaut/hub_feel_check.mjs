// How the Hub feels to a finger (owner, 2026-11-08), in headless Chrome with touch input
// through the same local stand-in for GitHub Pages as hub_links_check.mjs: the Hub files of
// this checkout, the demo pages, and the runtime published on the live site or a local build.
//
// - A fling: after a quick drag the page keeps scrolling and slows down as iOS UIScrollView
//   does (velocity times 0.998 per ms); inside a band the steps make no Lean render.
// - A tap during a fling only stops it: no click, no navigation.
// - A fling stops at the top of the page.
// - A tap with no fling still follows a link.
// - The folding chrome (an engine that answers shellInfo): the settings checkbox turns the
//   classic UI off; a scroll down folds the chrome to the strip (fold 100, top shrinks) with
//   no Lean render inside a band, only chrome layers; a scroll up unfolds it; a link tapped
//   under a folded chrome goes where it says; a tap on the strip unfolds it.
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
    await s('Emulation.setDeviceMetricsOverride',{width,height,deviceScaleFactor:1,mobile:true});
    await s('Emulation.setTouchEmulationEnabled',{enabled:true,maxTouchPoints:5});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];window.__opened=[];window.open=u=>{window.__opened.push(String(u));return {};};
      Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:base+'?'+query+'&strict=1'});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const touch=async(type,points)=>s('Input.dispatchTouchEvent',{type,touchPoints:points.map(([x,y])=>({x,y}))});
    return {
      evaluate,
      frames:(from=0)=>evaluate(`window.__frames.slice(${from}).map(f=>({t:f.t,path:f.path,scroll:f.scroll,leanRenders:f.leanRenders,url:f.url,bandTop:f.bandTop,collapse:f.collapse,top:f.top,chromeRenders:f.chromeRenders}))`),
      count:()=>evaluate('window.__frames.length'),
      async until(test,limit=30000){const t=Date.now();let st;
        while(Date.now()-t<limit){await sleep(150);st=await evaluate('window.__frames.at(-1)??null').catch(()=>undefined);if(st&&test(st))return st;}
        return st;},
      // A finger from (x,y0) to (x,y1) in `steps` moves `ms` apart, then lifted.
      // With `hold`, the finger rests that long before the lift: no fling.
      async drag(x,y0,y1,steps,ms,hold=0){await s('Page.bringToFront');
        await touch('touchStart',[[x,y0]]);
        for(let i=1;i<=steps;i++){await sleep(ms);await touch('touchMove',[[x,Math.round(y0+(y1-y0)*i/steps)]]);}
        if(hold)await sleep(hold);
        await touch('touchEnd',[]);},
      async tap(x,y){await s('Page.bringToFront');await touch('touchStart',[[x,y]]);await sleep(40);await touch('touchEnd',[]);},
      async shot(file){const r=await s('Page.captureScreenshot',{format:'png'});fs.writeFileSync(file,Buffer.from(r.data,'base64'));},
      close:()=>send('Target.closeTarget',{targetId})};
  }
  // Settled: no new frame for `quiet` ms.
  async function settle(page,quiet=600,limit=10000){
    const t=Date.now();let n=await page.count(),since=Date.now();
    while(Date.now()-t<limit){await sleep(100);const m=await page.count();if(m!==n){n=m;since=Date.now();}else if(Date.now()-since>=quiet)return;}
  }
  async function foldCheck(run,open,settle,width,height){
    const settingsURL=base+'pages/settings.html',pageURL=base+'pages/sitemap.xml',shots=opt('--shots','');
    const linksOf=page=>page.evaluate('window.__frames.at(-1)?.links??null');
    const set=await open('page=settings.html&stats=1&layers=0',width,height);
    await set.until(f=>f.url===settingsURL,60000);await settle(set);
    let links=await linksOf(set);
    let box=links?.find(l=>l[1]==='foafnaut:classic/off');
    // The checkbox is below the text size controls: a finger brings it into the view.
    for(let i=0;box&&i<6&&box[3]+box[5]/2>height-60;i++){
      await set.drag(200,600,600-Math.min(450,Math.round(box[3]+box[5]/2-height/2)),8,16,200);await settle(set);
      links=await linksOf(set);box=links?.find(l=>l[1]==='foafnaut:classic/off');
    }
    if(!box){console.log(`NOT RUN: ${run.name}: the folding chrome (this engine keeps the classic chrome)`);await set.close();return;}
    if(shots)await set.shot(path.join(shots,`${run.name}-settings-classic.png`));
    await set.tap(Math.round(box[2]+box[4]/2),Math.round(box[3]+box[5]/2));
    const n0=await set.count();
    await set.until(async()=>true,500);await settle(set);
    links=await linksOf(set);
    if(!links?.some(l=>l[1]==='foafnaut:classic/on'))fail(run.name,'the checkbox did not turn the classic UI off',JSON.stringify(links?.filter(l=>l[1].startsWith('foafnaut:'))));
    if(shots)await set.shot(path.join(shots,`${run.name}-settings-folding.png`));
    void n0;await set.close();
    // The setting is kept (IndexedDB): a new window folds.
    const page=await open('page=sitemap.xml&stats=1',width,height);
    await page.until(f=>f.url===pageURL,60000);
    await page.drag(200,500,490,2,16);
    await page.until(f=>f.bandTop!==undefined,20000);await settle(page);
    // Unfold first (that small drag folded a little).
    await page.drag(200,300,360,6,16);await settle(page);
    let n=await page.count();
    const start=(await page.frames(n-1))[0];
    // A slow drag down (no fling): 120 px in 12 steps of 50 ms.
    await page.drag(200,600,480,12,50,200);await settle(page);
    let frames=await page.frames(n);
    const folded=frames.at(-1),renders=frames.reduce((a,f)=>a+(f.leanRenders??0),0);
    const chromes=(folded.chromeRenders??0)-(start.chromeRenders??0);
    console.log(JSON.stringify({run:run.name,fold:{from:{scroll:start.scroll,collapse:start.collapse,top:start.top},to:{scroll:folded.scroll,collapse:folded.collapse,top:folded.top},frames:frames.length,leanRenders:renders,chromeLayers:chromes,paths:frames.reduce((a,f)=>(a[f.path]=(a[f.path]??0)+1,a),{})}}));
    if(folded.collapse!==100)fail(run.name,'a scroll down of 120 px did not fold the chrome:',folded.collapse);
    if(!(folded.top<start.top||start.top===undefined))fail(run.name,'the chrome did not get shorter:',start.top,'->',folded.top);
    if(renders!==0)fail(run.name,'folding inside a band made',renders,'Lean renders');
    if(!(chromes>0))fail(run.name,'no chrome layer was drawn while folding');
    const ups=frames.map(f=>f.collapse).filter(c=>c!==undefined);
    if(ups.some((c,i)=>i&&c<ups[i-1]))fail(run.name,'the fold went back during a scroll down',JSON.stringify(ups));
    // The page followed the finger: what the chrome gave up came out of the scroll.
    const moved=folded.scroll-start.scroll,gave=(start.top??0)-(folded.top??0);
    if(Math.abs(moved+gave-120)>6)fail(run.name,'the page did not follow the finger: scroll',moved,'+ chrome',gave,'!= 120');
    if(shots)await page.shot(path.join(shots,`${run.name}-folded.png`));
    // Half way back: a scroll up of a quarter of the folding rows.
    n=await page.count();
    await page.drag(200,400,400+Math.max(4,Math.round(gave/2)),4,50);await settle(page);
    frames=await page.frames(n);
    const half=frames.at(-1);
    console.log(JSON.stringify({run:run.name,unfold:{collapse:half.collapse,top:half.top,scroll:half.scroll,leanRenders:frames.reduce((a,f)=>a+(f.leanRenders??0),0)}}));
    if(!(half.collapse>0&&half.collapse<100))fail(run.name,'a short scroll up did not unfold part way:',half.collapse);
    if(shots)await page.shot(path.join(shots,`${run.name}-half.png`));
    // Fold again, then a tap on the strip unfolds the chrome.
    await page.drag(200,600,500,10,40);await settle(page);
    const strip=(await page.frames((await page.count())-1))[0];
    await page.tap(200,Math.max(2,Math.floor((strip.top??10)/2)));await settle(page);
    const open_=(await page.frames((await page.count())-1))[0];
    console.log(JSON.stringify({run:run.name,tapStrip:{before:strip.collapse,after:open_.collapse,url:open_.url}}));
    if(strip.collapse!==100||open_.collapse!==0)fail(run.name,'a tap on the folded strip did not unfold the chrome',strip.collapse,open_.collapse);
    if(open_.url!==pageURL)fail(run.name,'a tap on the strip left the page');
    await page.close();
    // A link under a folded chrome, in a one-frame view: Lean's links follow the chrome's top.
    const flat=await open('page=sitemap.xml&stats=1&layers=0',width,height);
    await flat.until(f=>f.url===pageURL,60000);await settle(flat);
    await flat.drag(200,600,480,12,50,200);await settle(flat);
    const fl=await flat.evaluate('window.__frames.at(-1)');
    const row=fl?.links?.find(l=>l[3]>30&&l[3]+l[5]<height-10);
    // Where a tap on the link went: the tab's address, or a host tab for another site.
    const want=row&&new URL(row[1],pageURL).href,elsewhere=want&&new URL(want).origin!==new URL(pageURL).origin;
    const outcome=async page=>{
      const st=await page.until(f=>f.url!==pageURL,elsewhere?3000:20000);void st;
      return elsewhere?((await page.evaluate('window.__opened')).at(-1)):(await page.evaluate('window.__frames.at(-1).url'));
    };
    if(fl?.collapse!==100||!row)fail(run.name,'one-frame view: no fold or no link',fl?.collapse,fl?.scroll,JSON.stringify(fl?.links?.map(l=>[l[1],Math.round(l[3])])));
    else{
      await flat.tap(Math.round(row[2]+row[4]/2),Math.round(row[3]+row[5]/2));
      const went=await outcome(flat);
      console.log(JSON.stringify({run:run.name,foldedTap:row[1],at:Math.round(row[3]),went}));
      if(went!==want)fail(run.name,'a tap on',row[1],'under the folded chrome went to',went);
      // The same drag in the two-layer view: the same link at the same place (hit testing
      // there maps the window row through the composite's top, which follows the fold).
      const lay=await open('page=sitemap.xml&stats=1',width,height);
      await lay.until(f=>f.url===pageURL,60000);await settle(lay);await sleep(400);
      await lay.drag(200,600,480,12,50,200);await settle(lay);
      const ls=await lay.evaluate('window.__frames.at(-1)');
      if(ls?.scroll!==fl.scroll||ls?.collapse!==fl.collapse)fail(run.name,'two-layer view: the same drag gave scroll',ls?.scroll,'fold',ls?.collapse,'not',fl.scroll,fl.collapse);
      else{
        await lay.tap(Math.round(row[2]+row[4]/2),Math.round(row[3]+row[5]/2));
        const wentL=await outcome(lay);
        console.log(JSON.stringify({run:run.name,layeredFoldedTap:row[1],went:wentL,path:ls.path,top:ls.top}));
        if(wentL!==want)fail(run.name,'two-layer view: a tap on',row[1],'under the folded chrome went to',wentL);
      }
      await lay.close();
    }
    await flat.close();
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
    await foldCheck(run,open,settle,width,height);
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();await sleep(300);try{fs.rmSync(profile,{recursive:true,force:true});}catch{/* Chrome still closing */}}
console.log(failures?`hub feel check: ${failures} failures`:'hub feel check: pass');
process.exit(failures?1:0);
