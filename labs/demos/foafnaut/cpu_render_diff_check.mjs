// The CPU raster (SVGRaster.lean) against WebGPU, pixel for pixel
// (docs/designissues/2026-11-08-cpu-render-backend.md).
//
// For each demo page (pages/*.html) and each SVG test file (svg-wpt shapes, pservers and
// painting reftests by default), the native engine answers one
// scene with its CPU pixels (web-render-native --document-bin with cpu:true, or --svg with
// --cpu-out). Headless Chrome with WebGPU draws the same scene through the Hub's layer
// surface (docs/web/hub/foafnaut/layers.mjs, drawSingle with readback) and the page compares
// the two. The report gives, per scene, the largest channel difference, the mean channel
// difference, and the pixels that differ at all and by more than the tolerance.
//
// node labs/demos/foafnaut/cpu_render_diff_check.mjs [--native PATH] [--runtime DIR]
//   [--pages a.html,b.html] [--svg DIR_OR_FILES] [--width 800] [--height 600]
//   [--tolerance 8] [--budget 0.002] [--json OUT]
// CHROME=/path/to/chrome overrides the browser. Exit 1 on a failure; NOT RUN with no browser
// or no native engine.
//
// Verdict: a pixel "differs" when a channel differs by more than --tolerance. A scene
// passes when at most --budget of its pixels differ. Binary64 (CPU) and binary32 (GPU) put
// a sample that lies within a rounding step of an edge on different sides; such a pixel
// differs by a share of the edge contrast (one sample in four, or in sixteen).
import http from 'node:http';import fs from 'node:fs';import path from 'node:path';import os from 'node:os';
import {spawn,spawnSync} from 'node:child_process';import {stripTypeScriptTypes} from 'node:module';import {fileURLToPath} from 'node:url';
const args=process.argv.slice(2),opt=(n,d)=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const lab=fileURLToPath(new URL('.',import.meta.url)),root=path.resolve(lab,'../../..');
const hubDir=path.join(root,'docs/web/hub/foafnaut/');
const native=opt('--native',path.join(lab,'.build/web-render/web-render-native'));
// The render plan engine (render-plan.mjs and .wasm): a Wasm build of this checkout, else the live one.
const runtimeDir=opt('--runtime',fs.existsSync(path.join(lab,'.build/web-render/engines/render-plan.wasm'))?path.join(lab,'.build/web-render/engines'):'');
const width=Number(opt('--width','800')),height=Number(opt('--height','600'));
const tolerance=Number(opt('--tolerance','8')),budget=Number(opt('--budget','0.002')),jsonOut=opt('--json','');
const font=path.join(root,'third_party/fonts/noto-sans/NotoSans-Regular.ttf');
const CHROME=process.env.CHROME??'/Applications/Google Chrome.app/Contents/MacOS/Google Chrome';
const LIVE='https://danbri.github.io';
if(!fs.existsSync(CHROME)){console.log('NOT RUN: cpu_render_diff_check.mjs needs Chrome (set CHROME)');process.exit(0);}
if(!fs.existsSync(native)){console.log('NOT RUN: no native engine at',native,'(build-web-render.sh --native)');process.exit(0);}

const pagesDir=path.join(lab,'pages');
const pageNames=opt('--pages','')?opt('--pages','').split(','):fs.readdirSync(pagesDir).filter(n=>n.endsWith('.html')).sort();
const svgArg=opt('--svg',['shapes','pservers/reftests','painting/reftests'].map(d=>path.join(root,'tests/external/svg-wpt/upstream/svg',d)).join(','));
const svgFiles=svgArg?svgArg.split(',').flatMap(p=>fs.existsSync(p)&&fs.statSync(p).isDirectory()?fs.readdirSync(p).filter(n=>n.endsWith('.svg')).sort().map(n=>path.join(p,n)):fs.existsSync(p)?[p]:[]):[];

// 1. The native engine's scenes and CPU pixels.
const work=fs.mkdtempSync(path.join(os.tmpdir(),'cpu-render-diff-'));
const scenes=[];
function unpack(bytes){
  const view=new DataView(bytes.buffer,bytes.byteOffset,bytes.byteLength),headSize=view.getUint32(4,true),count=view.getUint32(8,true);
  let offset=12+4*count;const head=JSON.parse(Buffer.from(bytes.subarray(offset,offset+headSize)).toString('utf8'));offset+=headSize;
  const sections=[];for(let i=0;i<count;i++){const length=view.getUint32(12+4*i,true);sections.push(bytes.subarray(offset,offset+length));offset+=(length+3)&~3;}
  return {head,sections};
}
const options=path.join(work,'options.json');
fs.writeFileSync(options,JSON.stringify({op:'render',textScalePercent:150,checks:false,cpu:true}));
for(const name of pageNames){
  const out=path.join(work,name+'.bin');
  const r=spawnSync(native,[path.join(pagesDir,name),String(width),String(height),'--document-bin',options,font,out,'0'],{encoding:'utf8',timeout:600000,maxBuffer:64<<20});
  if(r.status!==0||!fs.existsSync(out)){scenes.push({name,skipped:(r.stdout+r.stderr).slice(0,200)});continue;}
  const {head,sections}=unpack(fs.readFileSync(out));
  if(head.error){scenes.push({name,skipped:head.error});continue;}
  scenes.push({name,kind:'page',width:head.width,height:head.height,primitives:head.primitiveCount,
    data:sections[head.dataSection],tiles:sections[head.tilesSection],pixels:sections[head.pixelsSection],wgsl:head.wgsl});
}
for(const file of svgFiles){
  const name=path.relative(root,file),out=path.join(work,path.basename(file)+'.rgba');
  const r=spawnSync(native,[file,String(width),String(height),'--svg','--cpu-out',out],{encoding:'utf8',timeout:600000,maxBuffer:64<<20});
  let answer;try{answer=JSON.parse(r.stdout);}catch{scenes.push({name,skipped:(r.stdout+r.stderr).slice(0,200)});continue;}
  if(answer.error||!answer.artifact||!fs.existsSync(out)){scenes.push({name,skipped:answer.error??'no artifact'});continue;}
  const a=answer.artifact;
  scenes.push({name,kind:'svg',width:a.width,height:a.height,primitives:a.primitiveCount,
    data:Buffer.from(new Float32Array(a.data).buffer),tiles:Buffer.from(new Uint32Array(a.tiles).buffer),pixels:fs.readFileSync(out),wgsl:a.wgsl});
}
const drawn=scenes.filter(s=>!s.skipped);
console.error(`${drawn.length} scenes drawn on the CPU, ${scenes.length-drawn.length} refused by the engine`);

// 2. A stand-in for Pages: this checkout's Hub modules and the runtime (live, or --runtime).
const cache=new Map();
async function get(p){
  const hub='/factoidal/web/hub/foafnaut/',rt='/factoidal/web/hub/html-webgpu/runtime/';
  if(p===hub+'cpu-diff.html')return {status:200,type:'text/html',body:Buffer.from('<!doctype html><title>cpu diff</title><body></body>')};
  const m=/^\/scene\/(\d+)\/(data|tiles|pixels)$/.exec(p);
  if(m)return {status:200,type:'application/octet-stream',body:drawn[Number(m[1])][m[2]]};
  if(p.startsWith(hub)&&p.endsWith('.mjs')&&fs.existsSync(path.join(hubDir,p.slice(hub.length))))return {status:200,type:'text/javascript',body:fs.readFileSync(path.join(hubDir,p.slice(hub.length)))};
  // The render plan host is this checkout's render_plan.ts, as Builds installs it.
  if(p===rt+'render-plan-host.mjs')return {status:200,type:'text/javascript',body:Buffer.from(stripTypeScriptTypes(fs.readFileSync(path.join(lab,'render_plan.ts'),'utf8')).replace('./.build/engines/render-plan.mjs','./render-plan.mjs'))};
  if(runtimeDir&&p.startsWith(rt)&&fs.existsSync(path.join(runtimeDir,p.slice(rt.length)))){
    const f=path.join(runtimeDir,p.slice(rt.length));
    return {status:200,type:f.endsWith('.wasm')?'application/wasm':'text/javascript',body:fs.readFileSync(f)};
  }
  if(!cache.has(p))cache.set(p,fetch(LIVE+p).then(async r=>({status:r.status,type:r.headers.get('content-type')??'application/octet-stream',body:Buffer.from(await r.arrayBuffer())})));
  return cache.get(p);
}
const server=http.createServer(async(req,res)=>{
  try{const e=await get(new URL(req.url,'http://x').pathname);res.writeHead(e.status,{'content-type':e.type,'content-length':e.body.length});res.end(e.body);}
  catch(error){res.writeHead(502);res.end(String(error));}
});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const base=`http://127.0.0.1:${server.address().port}/factoidal/web/hub/foafnaut/`;

// 3. Headless Chrome with WebGPU over CDP: the GPU pixels and the comparison.
const profile=fs.mkdtempSync(path.join(os.tmpdir(),'cpu-render-diff-chrome-'));
const port=9900+Math.floor(Math.random()*500);
const chrome=spawn(CHROME,['--headless=new',`--remote-debugging-port=${port}`,`--user-data-dir=${profile}`,'--enable-unsafe-webgpu','--no-first-run','about:blank'],{stdio:'ignore'});
let failures=0;const report=[];
const fail=(...m)=>{failures++;console.log('FAIL',...m);};
try{
  let ws;for(let i=0;i<300&&!ws;i++){try{ws=(await (await fetch(`http://127.0.0.1:${port}/json/version`)).json()).webSocketDebuggerUrl;}catch{await new Promise(r=>setTimeout(r,100));}}
  if(!ws)throw Error("Chrome did not start: no answer on /json/version after 30 s");
  const socket=new WebSocket(ws);await new Promise((r,j)=>{socket.onopen=r;socket.onerror=j;});
  let id=0;const waiting=new Map();
  socket.onmessage=({data})=>{const m=JSON.parse(data);if(m.id&&waiting.has(m.id)){const [r,j]=waiting.get(m.id);waiting.delete(m.id);m.error?j(Error(JSON.stringify(m.error))):r(m.result);}};
  const send=(method,params={},sessionId)=>new Promise((r,j)=>{const i=++id;waiting.set(i,[r,j]);socket.send(JSON.stringify({id:i,method,params,sessionId}));});
  const {targetId}=await send('Target.createTarget',{url:base+'cpu-diff.html'});
  const {sessionId}=await send('Target.attachToTarget',{targetId,flatten:true});
  const evaluate=async expression=>{const r=await send('Runtime.evaluate',{expression,awaitPromise:true,returnByValue:true},sessionId);if(r.exceptionDetails)throw Error(r.exceptionDetails.exception?.description??r.exceptionDetails.text);return r.result.value;};
  for(let i=0;i<50;i++){if(await evaluate('document.readyState').catch(()=>'')==='complete')break;await new Promise(r=>setTimeout(r,100));}
  const gpu=await evaluate(`(async()=>{const L=await import('./layers.mjs');window.surface=await L.createLayerSurface(null,{check:true});return !!window.surface;})()`);
  if(!gpu)throw Error('no WebGPU adapter in headless Chrome');
  for(let i=0;i<drawn.length;i++){
    const s=drawn[i];
    const r=await evaluate(`(async()=>{
      const bytes=async k=>new Uint8Array(await (await fetch('/scene/${i}/'+k)).arrayBuffer());
      const [data,tiles,cpu]=await Promise.all([bytes('data'),bytes('tiles'),bytes('pixels')]);
      const frame={width:${s.width},height:${s.height},data:new Float32Array(data.buffer),tiles:new Uint32Array(tiles.buffer),wgsl:${JSON.stringify(s.wgsl)},checks:[]};
      const t=performance.now();const gpu=await window.surface.drawSingle(frame,{readBack:true});const gpuMs=performance.now()-t;
      if(!gpu||gpu.length!==cpu.length)return {error:'size '+(gpu?.length)+' against '+cpu.length};
      let max=0,sum=0,any=0,over=0;const hist=new Array(9).fill(0);let worstAt=-1;
      for(let p=0;p<cpu.length;p+=4){let d=0;for(let c=0;c<3;c++){const e=Math.abs(cpu[p+c]-gpu[p+c]);sum+=e;if(e>d)d=e;}
        if(d){any++;hist[Math.min(8,Math.ceil(Math.log2(d+1)))]++;}if(d>${tolerance})over++;if(d>max){max=d;worstAt=p/4;}}
      return {max,mean:sum/(cpu.length/4*3),differ:any,over,pixels:cpu.length/4,hist,worst:worstAt<0?null:[worstAt%${s.width},Math.floor(worstAt/${s.width})],gpuMs};
    })()`);
    if(r.error){fail(s.name,r.error);report.push({name:s.name,error:r.error});continue;}
    const verdict=r.over<=budget*r.pixels?'pass':'fail';
    const row={name:s.name,kind:s.kind,width:s.width,height:s.height,primitives:s.primitives,...r,mean:Number(r.mean.toFixed(4)),gpuMs:Math.round(r.gpuMs),verdict};
    report.push(row);console.log(JSON.stringify(row));
    if(verdict==='fail')fail(s.name,`${r.over} of ${r.pixels} pixels differ by more than ${tolerance}`);
  }
  await send('Target.closeTarget',{targetId});
}catch(error){fail(String(error?.stack??error));}
finally{chrome.kill('SIGKILL');server.close();try{fs.rmSync(profile,{recursive:true,force:true,maxRetries:10,retryDelay:100});}catch{/* Chrome still closing */}fs.rmSync(work,{recursive:true,force:true});}
const ok=report.filter(r=>r.verdict==='pass').length,sum=k=>report.reduce((t,r)=>t+(r[k]??0),0);
const summary={scenes:report.length,pass:ok,refused:scenes.length-drawn.length,pixels:sum('pixels'),differ:sum('differ'),over:sum('over'),
  max:Math.max(0,...report.map(r=>r.max??0)),tolerance,budget};
console.log(JSON.stringify({summary}));
if(jsonOut)fs.writeFileSync(jsonOut,JSON.stringify({summary,scenes:report,refused:scenes.filter(s=>s.skipped).map(s=>({name:s.name,reason:s.skipped}))},null,1)+'\n');
console.log(failures?`cpu render diff check: ${failures} failures`:'cpu render diff check: pass');
process.exit(failures?1:0);
