import {writeFile,readFile,mkdir} from 'node:fs/promises';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {resolve,dirname} from 'node:path';
import {stripTypeScriptTypes} from 'node:module';
import {createHash} from 'node:crypto';
const [origin,hubURL,playwrightPath,chrome,out]=process.argv.slice(2);
if(!out)throw Error('usage: check-gpu-updates.mjs ORIGIN HUB_URL PLAYWRIGHT CHROME NEW_OUT');
await mkdir(out,{recursive:false});
const here=dirname(fileURLToPath(import.meta.url));
const {chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:chrome,headless:true,args:['--enable-unsafe-webgpu']});
let report={pass:false};
try{
 const page=await browser.newPage();page.setDefaultTimeout(90000);
 await page.goto(origin);
 await page.waitForFunction(()=>window.webRenderResult?.artifact);
 report=await page.evaluate(async()=>{
  const {compile}=await import('/engine.mjs');
  const {createOffscreenSession}=await import('/lab/gpu_transport.ts');
  const source=color=>`<html><body style="margin:0;background:${color}"><div style="width:20px;height:16px;background:blue"></div></body></html>`;
  const artifacts=[];for(const color of ['red','green','white'])artifacts.push(await compile(source(color),32,24,'html'));
  let session;const rows=[];
  try{
   session=await createOffscreenSession(artifacts[0],'svg-offscreen');if(!session)throw Error('adapter absent');
   for(let i=0;i<artifacts.length;i++){
    const begin=performance.now();
    if(i&&!(await session.update(artifacts[i])))throw Error('same topology update refused');
    const reused=await session.draw(),reuseMs=performance.now()-begin;
    const freshStart=performance.now(),fresh=await createOffscreenSession(artifacts[i],'svg-offscreen');if(!fresh)throw Error('fresh adapter absent');
    let expected;try{expected=await fresh.draw();}finally{fresh.close();}
    const freshMs=performance.now()-freshStart;
    if(reused.length!==expected.length||reused.some((v,j)=>v!==expected[j]))throw Error('updated image differs from fresh session');
    rows.push({case:i,pixels:reused.length/4,reuseMs,freshMs,stats:session.stats});
   }
   if(session.stats.devices!==1||session.stats.pipelines!==1||session.stats.uploads!==3||session.stats.frames!==3)throw Error('resource rebuild or skipped upload');
   const bad={...artifacts[2],checks:[{x:0,y:0,rgb:[255,0,255]}]};
   if(!(await session.update(bad)))throw Error('bad expectation update refused');
   let refused=false;try{await session.draw();}catch(e){refused=String(e).includes('readback mismatch');}
   if(!refused||!session.stats.failed)throw Error('changed checks were bypassed');
   return {pass:true,adapter:session.adapterInfo.description,rows,negativeCheck:true};
  }finally{session?.close();}
 });
 await page.locator('#source').fill('<html><body style="margin:0;background:red"><div style="width:20px;height:16px;background:blue"></div></body></html>');
 await page.locator('#width').fill('32');await page.locator('#height').fill('24');await page.locator('#render').click();
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.width===32);
 const before=await page.evaluate(()=>({artifact:window.webRenderResult.artifact,gpu:window.webRenderResult.gpuStats}));
 await page.locator('#source').fill('<html><body style="margin:0;background:green"><div style="width:20px;height:16px;background:blue"></div></body></html>');
 await page.locator('#render').click();
 await page.waitForFunction(previous=>window.webRenderResult?.artifact&&JSON.stringify(window.webRenderResult.artifact)!==previous,JSON.stringify(before.artifact));
 const after=await page.evaluate(()=>window.webRenderResult.gpuStats);
 if(!after||after.devices!==1||after.pipelines!==1||after.frames!==before.gpu.frames+1)throw Error('interactive edit did not reuse the session');
 report.ui={before:before.gpu,after};
 // Test the proposed worker/transport source against the frozen Hub engines.
 // This is an isolated interception, not a published-runtime qualification.
 const workerSource=await readFile(resolve(here,'../../../../docs/web/hub/html-webgpu/worker.mjs'),'utf8');
 const transportSource=await readFile(resolve(here,'../gpu_transport.ts'),'utf8');
 const transportJS=stripTypeScriptTypes(transportSource,{mode:'strip'}).replaceAll('./render_plan.ts','./render-plan-host.mjs');
 const hub=await browser.newPage();
 const workerURL=new URL('worker.mjs',hubURL).href,transportURL=new URL('runtime/gpu-transport.mjs',hubURL).href;
 await hub.route(workerURL,route=>route.fulfill({body:workerSource,contentType:'text/javascript'}));
 await hub.route(transportURL,route=>route.fulfill({body:transportJS,contentType:'text/javascript'}));
 await hub.goto(hubURL);
 report.worker=await hub.evaluate(async workerURL=>{
  const worker=new Worker(workerURL,{type:'module'}),frames=[];
  const source=color=>`<html><body style="margin:0;background:${color}"><div style="width:20px;height:16px;background:blue"></div></body></html>`;
  function wait(id){return new Promise((resolve,reject)=>{
   const timer=setTimeout(()=>{worker.removeEventListener('message',listener);reject(Error('worker timeout'));},90000);
   const listener=({data})=>{if(data.id!==id)return;if(data.type==='error'){clearTimeout(timer);worker.removeEventListener('message',listener);reject(Error(data.error));}else if(data.type==='frame'){clearTimeout(timer);worker.removeEventListener('message',listener);resolve(data);}};
   worker.addEventListener('message',listener);
  });}
  worker.addEventListener('message',({data})=>{if(data.type==='frame')frames.push(data.id);});
  try{
   const one=wait(2);
   worker.postMessage({type:'render',id:1,source:source('white'),width:32,height:24});
   worker.postMessage({type:'render',id:2,source:source('red'),width:32,height:24});
   const first=await one,two=wait(3);
   worker.postMessage({type:'render',id:3,source:source('green'),width:32,height:24});
   const second=await two;
   if(!second.gpuStats||second.gpuStats.pipelines!==1||second.gpuStats.frames!==first.gpuStats.frames+1)throw Error('worker did not reuse GPU resources');
   const a=new Uint8Array(first.rgba),b=new Uint8Array(second.rgba),offset=(8*32+31)*4;
   if(a[offset]!==255||a[offset+1]!==0||b[offset]!==0||b[offset+1]!==128)throw Error(`worker pixels did not update: ${a.slice(offset,offset+4)} -> ${b.slice(offset,offset+4)}`);
   return {frames,first:first.gpuStats,second:second.gpuStats,pixels:768,proposedSourceAgainstFrozenEngines:true};
  }finally{worker.terminate();}
 },workerURL);
 report.sourceHashes={worker:createHash('sha256').update(workerSource).digest('hex'),transport:createHash('sha256').update(transportSource).digest('hex')};
 report.browser=browser.version();
 for(const [name,url]of [['localProvenance',new URL('provenance.json',origin)],['hubRuntimeManifest',new URL('runtime/manifest.json',hubURL)]]){
  const response=await fetch(url);if(!response.ok)throw Error(`provenance unavailable: ${url}`);
  report[name]=await response.json();
 }
 await writeFile(resolve(out,'report.json'),JSON.stringify(report,null,2));console.log(JSON.stringify(report));
}catch(error){await writeFile(resolve(out,'report.json'),JSON.stringify({...report,pass:false,error:String(error.stack??error)},null,2));throw error;}
finally{await browser.close();}
