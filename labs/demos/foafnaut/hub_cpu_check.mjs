// The Hub with no WebGPU (docs/designissues/2026-11-08-cpu-render-backend.md), in headless
// Chrome started with WebGPU switched off (--disable-blink-features=WebGPU), through a local
// stand-in for GitHub Pages: this checkout's Hub modules, and the runtime from --runtime DIR
// (an engine with the op cpuInfo) or from the live site.
//
// With --runtime (an engine that draws on the CPU):
// 1. The page shows frames, each with stats.cpu, and no refusal note.
// 2. Scrolls inside the band make no Lean render: each is a copy of the CPU layers ("shift").
// 3. With --gpu-compare, the same page in a second Chrome with WebGPU (?check=1): the canvas
//    pixels are compared, as cpu_render_diff_check.mjs compares scenes.
// With --expect-refusal (an engine without cpuInfo, e.g. the live one): the page says, as
// before, that the browser does not provide WebGPU.
//
// node labs/demos/foafnaut/hub_cpu_check.mjs [--runtime DIR] [--page status.html] [--gpu-compare] [--expect-refusal]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser.
import http from 'node:http';import zlib from 'node:zlib';import fs from 'node:fs';import path from 'node:path';import os from 'node:os';
import {spawn} from 'node:child_process';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const hubDir=fileURLToPath(new URL('../../../docs/web/hub/foafnaut/',import.meta.url)),runtimeDir=opt('--runtime','');
const pageName=opt('--page','status.html'),expectRefusal=args.includes('--expect-refusal'),gpuCompare=args.includes('--gpu-compare');
const LIVE='https://danbri.github.io',CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: hub_cpu_check.mjs needs Chrome (set CHROME)');process.exit(0);}

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

let failures=0;const fail=(...m)=>{failures++;console.log('FAIL',...m);};
const browsers=[];
async function browser(gpu){
  const profile=fs.mkdtempSync(path.join(os.tmpdir(),'hub-cpu-check-'));
  const port=9400+Math.floor(Math.random()*500);
  const flags=gpu?['--enable-unsafe-webgpu']:['--disable-blink-features=WebGPU','--disable-gpu'];
  const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,...flags,'--no-first-run','about:blank'],{stdio:'ignore'});
  browsers.push({chrome,profile});
  let ws;for(let i=0;i<100&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await new Promise(r=>setTimeout(r,100));}}
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  return async function open(query,width=800,height=600){
    const {targetId}=await send('Target.createTarget',{url:'about:blank'});
    const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
    const s=(m,p)=>send(m,p,sessionId);
    await s('Page.enable');await s('Runtime.enable');
    await s('Emulation.setDeviceMetricsOverride',{width,height,deviceScaleFactor:1,mobile:false});
    await s('Page.addScriptToEvaluateOnNewDocument',{source:`(()=>{let f;window.__frames=[];Object.defineProperty(window,'foafnautFrame',{configurable:true,get(){return f;},set(v){f=v;window.__frames.push({t:performance.now(),...v});}});})();`});
    await s('Page.navigate',{url:base+'?'+query});
    const evaluate=async expression=>{const r=await s('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true});if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;};
    const note=()=>evaluate(`(()=>{const n=document.querySelector('#note');return n&&!n.hidden?n.textContent:'';})()`).catch(()=>'');
    return {evaluate,note,
      async settle(quiet=1500,limit=120000){const t=Date.now();
        while(Date.now()-t<limit){await new Promise(r=>setTimeout(r,200));
          const st=await evaluate(`({n:window.__frames.length,last:window.__frames.at(-1)?.t??0,now:performance.now()})`).catch(()=>({n:0}));
          const n=await note();if(n&&!/Starting/.test(n))return n;
          if(st.n&&st.now-st.last>quiet)return '';}
        throw Error('no frames settled: '+await note());},
      frames:()=>evaluate('window.__frames'),
      wheel:async deltaY=>{await s('Page.bringToFront');await s('Input.dispatchMouseEvent',{type:'mouseWheel',x:width/2,y:height/2,deltaX:0,deltaY});},
      pixels:async()=>Buffer.from(await evaluate(`(()=>{const c=document.querySelector('#page'),d=c.getContext('2d').getImageData(0,0,c.width,c.height).data;let t='';for(let i=0;i<d.length;i+=32768)t+=String.fromCharCode(...d.subarray(i,i+32768));return btoa(t);})()`),'base64'),
      close:()=>send('Target.closeTarget',{targetId})};
  };
}
try{
  const open=await browser(false);
  if(expectRefusal){
    const page=await open(`page=${pageName}&stats=1`);
    const said=await page.settle().catch(e=>String(e.message));
    console.log(JSON.stringify({check:'refusal',note:said}));
    if(!/does not provide WebGPU/.test(said))fail('an engine without cpuInfo did not refuse as before:',said);
    await page.close();
  }else{
    const page=await open(`page=${pageName}&stats=1&check=1`);
    const said=await page.settle();
    if(said)fail('the page refused:',said);
    let frames=await page.frames();
    const first=frames.at(-1);
    console.log(JSON.stringify({check:'cpu-frames',frames:frames.map(f=>({path:f.path,cpu:f.cpu,layoutMs:f.layoutMs,drawMs:f.drawMs,totalMs:f.totalMs,pixels:f.pixelHash}))}));
    if(!frames.length||!frames.every(f=>f.cpu===true))fail('frames without stats.cpu');
    // The band comes after the first frame, while the page is idle (scheduleBand): on the CPU
    // it takes a while, so wait for it, then each scroll waits for its frame.
    const count=async()=>(await page.frames()).length;
    const waitFrame=async(n,limit=120000)=>{const t=Date.now();while(Date.now()-t<limit){if(await count()>n)return true;await new Promise(r=>setTimeout(r,200));}return false;};
    await new Promise(r=>setTimeout(r,15000));
    const start=await count();
    for(let i=0;i<6;i++){const n=await count();await page.wheel(60);if(!await waitFrame(n))fail('no frame after a scroll');}
    await page.settle(800);
    frames=(await page.frames()).slice(start);
    const shifts=frames.filter(f=>/^shift/.test(f.path));
    console.log(JSON.stringify({check:'cpu-shift',frames:frames.map(f=>({path:f.path,scroll:f.scroll,offset:f.offset,leanRenders:f.leanRenders,totalMs:f.totalMs}))}));
    if(!shifts.length)fail('no scroll was a copy of the CPU layers');
    for(const f of shifts)if(f.leanRenders!==0)fail('a copy frame made a Lean render',JSON.stringify(f));
    if(gpuCompare){
      for(let i=0;i<6;i++){const n=await count();await page.wheel(-60);await waitFrame(n);}await page.settle(3000);
      const cpu=await page.pixels();
      const openGpu=await browser(true),gpuPage=await openGpu(`page=${pageName}&stats=1&check=1`);
      const gsaid=await gpuPage.settle(5000);if(gsaid)fail('the GPU page refused:',gsaid);
      const gpu=await gpuPage.pixels(),last=(await gpuPage.frames()).at(-1);
      if(cpu.length!==gpu.length)fail('canvas sizes differ',cpu.length,gpu.length);
      else{
        let differ=0,over=0,worst=0;
        for(let i=0;i<cpu.length;i+=4){let d=0;for(let c=0;c<3;c++)d=Math.max(d,Math.abs(cpu[i+c]-gpu[i+c]));if(d){differ++;worst=Math.max(worst,d);}if(d>8)over++;}
        const cpuLast=(await page.frames()).at(-1);
        console.log(JSON.stringify({check:'cpu-against-gpu',page:pageName,scroll:[cpuLast?.scroll,last?.scroll],gpuPath:last?.path,pixels:cpu.length/4,differ,over,worst}));
        if(over>0.002*cpu.length/4)fail('the CPU Hub frame differs from the GPU one in',over,'pixels');
      }
      await gpuPage.close();
    }
    await page.close();
  }
}catch(error){fail(String(error?.stack??error));}
finally{for(const b of browsers){b.chrome.kill('SIGKILL');fs.rmSync(b.profile,{recursive:true,force:true});}server.close();}
console.log(failures?`hub cpu check: ${failures} failures`:'hub cpu check: pass');
process.exit(failures?1:0);
