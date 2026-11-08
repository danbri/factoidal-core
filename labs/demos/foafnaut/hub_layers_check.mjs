// The Hub's two-layer scroll (issue 1268), in headless Chrome with WebGPU, through a local
// stand-in for GitHub Pages: the Hub files of this checkout (docs/web/hub/foafnaut/*.mjs),
// and the published page, runtime and pages from the live site, or a runtime folder.
//
// 1. Scrolls inside the band on screen make no Lean call: each is a composite ("shift").
// 2. The composite at a scroll equals one Lean frame at that scroll (?layers=0), read back
//    from the page's canvas, within the rounding of native scroll_layers_check.ts.
// 3. ?page=wasm shows its own page, not the demo index.
//
// node labs/demos/foafnaut/hub_layers_check.mjs [--runtime DIR] [--page showcase.html] [--compare status.html,showcase.html] [--shots DIR]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url)),runtimeDir=opt('--runtime',''),shots=opt('--shots','');
const pageName=opt('--page','showcase.html'),comparePages=opt('--compare','status.html,showcase.html').split(','),LIVE='https://danbri.github.io';
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_layers_check.mjs needs Chrome (set CHROME)');process.exit(0);}

// The stand-in for Pages: gzip and max-age=600, as Pages serves.
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

// Chrome over CDP.
const profile=fs.mkdtempSync('/tmp/hub-layers-check-');
const port=9400+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
try{
  let ws;for(let i=0;i<100&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await new Promise(r=>setTimeout(r,100));}}
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  async function open(query,width=800,height=600){
    console.error('open',query);
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width,height,deviceScaleFactor:1,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:base+'?'+query});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const page={s,evaluate,
      // Frames stop: a frame, then quiet for this long.
      async settle(quiet=1500,limit=60000){const t=Date.now();
        while(Date.now()-t<limit){await new Promise(r=>setTimeout(r,200));
          const st=await evaluate(`({n:window.__frames.length,last:window.__frames.at(-1)?.t??0,now:performance.now(),note:document.querySelector('#note').hidden?'':document.querySelector('#note').textContent})`).catch(()=>({n:0}));
          if(st.note&&!/Starting/.test(st.note))throw Error('page note: '+st.note);
          if(st.n&&st.now-st.last>quiet)return;}
        throw Error('no frames settled: '+JSON.stringify(await evaluate('({n:window.__frames.length,note:document.querySelector("#note").textContent})').catch(e=>String(e))));},
      frames:()=>evaluate('window.__frames'),
      // A tab in the background gets no input: bring it to the front first.
      wheel:async deltaY=>{await s('Page.bringToFront');await s('Input.dispatchMouseEvent',{type:'mouseWheel',x:width/2,y:height/2,deltaX:0,deltaY});},
      pixels:()=>evaluate(`(()=>{const c=document.querySelector('#page'),d=c.getContext('2d').getImageData(0,0,c.width,c.height).data;let t='';for(let i=0;i<d.length;i+=32768)t+=String.fromCharCode(...d.subarray(i,i+32768));return {width:c.width,height:c.height,b64:btoa(t)};})()`),
      async shot(name){if(!shots)return;fs.mkdirSync(shots,{recursive:true});const {data}=await s('Page.captureScreenshot',{format:'png'});fs.writeFileSync(path.join(shots,name),Buffer.from(data,'base64'));},
      close:()=>send('Target.closeTarget',{targetId})};
    return page;
  }

  // 1. No Lean call inside the band, on the GPU canvas path.
  {
    const page=await open(`page=${pageName}&stats=1`);await page.settle();
    const start=(await page.frames()).length;
    for(let i=0;i<6;i++){await page.wheel(60);await page.settle(400);}
    const frames=(await page.frames()).slice(start);
    const shifts=frames.filter(f=>f.path==='shift');
    console.log(JSON.stringify({check:'no-lean-in-band',frames:frames.map(f=>({path:f.path,scroll:f.scroll,bandTop:f.bandTop,offset:f.offset,leanRenders:f.leanRenders,leanCalls:f.leanCalls,totalMs:f.totalMs}))}));
    if(!shifts.length)fail('no scroll was a composite: the engine answered no layers, or the band held no scroll');
    for(const f of shifts)if(f.leanRenders!==0)fail('a composite frame made a Lean render',JSON.stringify(f));
    for(let i=1;i<frames.length;i++)if(frames[i].path==='shift'&&frames[i].leanCalls!==frames[i-1].leanCalls)fail('Lean was called between composites',frames[i-1].leanCalls,frames[i].leanCalls);
    await page.shot('hub-check-shift.png');await page.close();
  }

  // 2. Composite pixels against one Lean frame at the same scroll (readback path, ?check=1).
  let compared=0,expected=0;
  for(const name of comparePages){
    const layered=await open(`page=${name}&check=1`),whole=await open(`page=${name}&check=1&layers=0`);
    await layered.settle();await whole.settle();
    const steps=[0,90,90,90,240];
    for(const step of steps){
      if(step){await layered.wheel(step);await layered.settle(600);await whole.wheel(step);await whole.settle(600);}
      const a=(await layered.frames()).at(-1),b=(await whole.frames()).at(-1);
      if(a.scroll!==b.scroll){fail('the two pages are at different scrolls',a.scroll,b.scroll);continue;}
      const [pa,pb]=[await layered.pixels(),await whole.pixels()];
      const x=Buffer.from(pa.b64,'base64'),y=Buffer.from(pb.b64,'base64');
      if(x.length!==y.length){fail('canvas sizes differ',pa.width,pa.height,pb.width,pb.height);continue;}
      let differ=0,worst=0;
      for(let i=0;i<x.length;i+=4){let d=0;for(let c=0;c<3;c++)d=Math.max(d,Math.abs(x[i+c]-y[i+c]));if(d){differ++;worst=Math.max(worst,d);}}
      compared++;
      if(shots){fs.mkdirSync(shots,{recursive:true});for(const [n,b,pp] of [['layered',x,pa],['whole',y,pb]])fs.writeFileSync(path.join(shots,`pixels-${n}-${a.scroll}.ppm`),Buffer.concat([Buffer.from(`P6\n${pp.width} ${pp.height}\n255\n`),Buffer.from(b.filter((_,i)=>i%4!==3))]));}
      // As native scroll_layers_check.ts: the band's geometry rounds to float32 a little
      // differently from one frame, so a few edge pixels may differ. More is a failure.
      // Lean's scene shader takes 16 samples at an edge only in a scene of at most 65536 storage
      // rows (Graphics.lean pixelSampleRefineRowLimit): a band and one frame can fall on different
      // sides, and every glyph edge then differs (https://github.com/danbri/factoidal/issues/1269).
      // Those are an expected failure, counted apart; one that passes fails the run.
      const rule=rows=>rows<=65536,sameRule=rule(a.rows)===rule(b.rows);
      const verdict=sameRule?(differ<=32?'pass':'fail'):(differ<=32?'stale-expected-failure':'expected-failure-1269');
      if(verdict==='expected-failure-1269')expected++;
      console.log(JSON.stringify({check:'composite-equals-frame',page:name,scroll:a.scroll,rows:{band:a.rows,frame:b.rows},layeredPath:a.path,wholePath:b.path,bandTop:a.bandTop,differentPixels:differ,largestDifference:worst,verdict}));
      if(verdict==='fail'||verdict==='stale-expected-failure')fail(verdict,'composite differs from the Lean frame at scroll',a.scroll,differ,'pixels');
      if(!/readback/.test(a.path))fail('the layered page did not draw layers',a.path);
    }
    await layered.shot(`hub-check-${name}-layered.png`);await whole.shot(`hub-check-${name}-whole.png`);
    await layered.close();await whole.close();
  }
  console.log(`composite against frame: ${compared-expected} compared under the same rule, ${expected} expected failures (issue 1269)`);
  if(!compared||compared===expected)fail('no scroll compared under the same sampling rule');

  // 3. ?page=wasm is its own page.
  {
    const page=await open('page=wasm');await page.settle();
    const title=await page.evaluate('document.title');
    console.log(JSON.stringify({check:'wasm-page',title}));
    if(!/WebAssembly|Needs a newer engine/.test(title))fail('?page=wasm showed',title);
    await page.close();
  }
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();fs.rmSync(profile,{recursive:true,force:true});}
console.log(failures?`hub layers check: ${failures} failures`:'hub layers check: pass');
process.exit(failures?1:0);
