// reftest-gpu-check.mjs: the WPT reftest pages drawn by the engine's two paths, the CPU raster
// (SVGRaster, what wpt-reftests.py scores) and WebGPU (the Hub's layer surface, layers.mjs
// drawSingle, the path a window shows), compared pixel for pixel. A disagreement is a finding
// of its own (skills/wpt-runs section 10): the score is of the CPU raster.
//
//   node tests/browser-wpt/reftest-gpu-check.mjs --scenes DIR [--runtime DIR] [--tolerance 8] [--budget 0.002] [--json OUT]
//
// DIR: the scene files reftest-render.ts --scenes writes (NAME.json, .data, .tiles, .cpu).
// --runtime: the directory of render-plan.mjs and .wasm (default: the lab's .build/engines).
// CHROME=/path/to/chrome overrides the browser. NOT RUN (exit 0) with no Chrome or no WebGPU.
// Verdict per page, as cpu_render_diff_check.mjs: a pixel differs when a channel differs by
// more than --tolerance (binary64 on the CPU and binary32 on the GPU put samples near an edge
// on different sides); a page agrees when at most --budget of its pixels differ.
import http from 'node:http';import fs from 'node:fs';import path from 'node:path';import os from 'node:os';
import {spawn} from 'node:child_process';import {stripTypeScriptTypes} from 'node:module';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const here=fileURLToPath(new URL('.',import.meta.url)),root=path.resolve(here,'../..'),lab=path.join(root,'labs/demos/foafnaut');
const hubDir=path.join(root,'docs/web/hub/foafnaut/');
const scenesDir=opt('--scenes','');
const runtimeDir=opt('--runtime',path.join(lab,'.build/engines'));
const tolerance=Number(opt('--tolerance','8')),budget=Number(opt('--budget','0.002')),jsonOut=opt('--json','');
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
if(!scenesDir||!fs.existsSync(scenesDir)){console.error('--scenes DIR (reftest-render.ts --scenes) is required');process.exit(2);}
if(!fs.existsSync(CHROME)){console.log('NOT RUN: reftest-gpu-check.mjs needs Chrome (set CHROME)');process.exit(0);}
const names=fs.readdirSync(scenesDir).filter(n=>n.endsWith('.json')).map(n=>n.slice(0,-5)).sort();
const file=(n,ext)=>path.join(scenesDir,n+ext);

async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  if(p===hub+'gpu-check.html')return {status:200,type:'text/html',body:Buffer.from('<!doctype html><title>gpu check</title><body></body>')};
  const m=/^\/scene\/(\d+)\/(data|tiles|cpu)$/.exec(p);
  if(m)return {status:200,type:'application/octet-stream',body:fs.readFileSync(file(names[Number(m[1])],'.'+m[2]))};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&fs.existsSync(path.join(hubDir,p.slice(hub.length))))return {status:200,type:'text/javascript',body:fs.readFileSync(path.join(hubDir,p.slice(hub.length)))};
  if(p===rt+'render-plan-host.mjs')return {status:200,type:'text/javascript',body:Buffer.from(stripTypeScriptTypes(fs.readFileSync(path.join(lab,'render_plan.ts'),'utf8')).replace('./.build/engines/render-plan.mjs','./render-plan.mjs').replace('./finite_floats.ts','./finite-floats.mjs'))};
  if(p===rt+'finite-floats.mjs')return {status:200,type:'text/javascript',body:Buffer.from(stripTypeScriptTypes(fs.readFileSync(path.join(lab,'finite_floats.ts'),'utf8')))};
  if(p.startsWith(rt)&&fs.existsSync(path.join(runtimeDir,p.slice(rt.length)))){
    const f=path.join(runtimeDir,p.slice(rt.length));
    return {status:200,type:f.endsWith('.wasm')?'application/wasm':'text/javascript',body:fs.readFileSync(f)};
  }
  // anything else of the Hub (modules layers.mjs imports): the published site, as cpu_render_diff_check.mjs does
  if(!cache.has(p))cache.set(p,fetch('https://danbri.github.io'+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const cache=new Map();
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);if(e.status!==200)console.error('reftest-gpu-check:',e.status,req.url);res.writeHead(e.status,{'content-type':e.type,'content-length':e.body.length});res.end(e.body);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const base=`http://127.0.0.1:${server.address().port}/factoidal/web/hub/foafnaut/`;
const profile=fs.mkdtempSync(path.join(os.tmpdir(),'reftest-gpu-chrome-'));
const port=9900+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
const report=[];let notRun='';
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await new Promise(r=>setTimeout(r,100));}}
  if(!ws)throw Error('Chrome did not start');
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const {targetId}=await send('Target.createTarget',{url:base+'gpu-check.html'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const evaluate=async expression=>{const r=await send('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true},sessionId);if(r.exceptionDetails)throw Error(r.exceptionDetails.exception?.description??r.exceptionDetails.text);return r.result.value;};
  for(let i=0;i<50;i++){if(await evaluate('document.readyState').catch(()=>'')==='complete')break;await new Promise(r=>setTimeout(r,100));}
  const gpu=await evaluate(`(async()=>{const L=await import('./layers.mjs');window.surface=await L.createLayerSurface(null,{check:true});return !!window.surface;})()`);
  if(!gpu){notRun='no WebGPU adapter in headless Chrome';throw Error(notRun);}
  for(let i=0;i<names.length;i++){
    const s=JSON.parse(fs.readFileSync(file(names[i],'.json'),'utf8'));
    const r=await evaluate(`(async()=>{
      const bytes=async k=>new Uint8Array(await (await fetch('/scene/${i}/'+k)).arrayBuffer());
      const [data,tiles,cpu]=await Promise.all([bytes('data'),bytes('tiles'),bytes('cpu')]);
      const frame={width:${s.width},height:${s.height},data:new Float32Array(data.buffer),tiles:new Uint32Array(tiles.buffer),wgsl:${JSON.stringify(s.wgsl)},checks:[]};
      const gpu=await window.surface.drawSingle(frame,{readBack:true});
      if(!gpu||gpu.length!==cpu.length)return {error:'GPU answer of '+(gpu?.length)+' bytes, CPU '+cpu.length};
      let max=0,over=0,any=0;
      for(let p=0;p<cpu.length;p+=4){let d=0;for(let c=0;c<3;c++){const e=Math.abs(cpu[p+c]-gpu[p+c]);if(e>d)d=e;}if(d)any++;if(d>${tolerance})over++;if(d>max)max=d;}
      return {max,differ:any,over,pixels:cpu.length/4};
    })()`);
    if(r.error){report.push({url:s.url,error:r.error});continue;}
    const row={url:s.url,...r,verdict:r.over<=budget*r.pixels?'agree':'disagree'};
    report.push(row);
    if(row.verdict!=='agree')console.log(JSON.stringify(row));
  }
}catch(error){if(!notRun)notRun=String(error?.message??error);}
finally{chrome.kill('SIGKILL');server.close();try{fs.rmSync(profile,{recursive:true,force:true,maxRetries:10,retryDelay:100});}catch{/* closing */}}
const agree=report.filter(r=>r.verdict==='agree').length,dis=report.filter(r=>r.verdict==='disagree').length,err=report.filter(r=>r.error).length;
const summary={pages:names.length,compared:report.length,agree,disagree:dis,errors:err,tolerance,budget,notRun:notRun||undefined};
console.log(JSON.stringify(summary));
if(jsonOut)fs.writeFileSync(jsonOut,JSON.stringify({summary,pages:report},null,1));
if(notRun&&!report.length){console.log('NOT RUN:',notRun);process.exit(0);}
process.exit(dis||err?1:0);
