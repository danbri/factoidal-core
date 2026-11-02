#!/usr/bin/env node
// Test transport: same Lean SVG/WGSL/render-plan and existing raw WebGPU bridge.
// Browser SVG rendering is used only by the separate independent oracle.
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {createServer} from 'node:http';
import {dirname,resolve,relative,sep,basename} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {platform,release,arch} from 'node:os';
import {stripTypeScriptTypes} from 'node:module';
import {sourceSnapshot} from './provenance.mjs';
const root=dirname(fileURLToPath(import.meta.url)),repo=resolve(root,'../../..'),lab=resolve(repo,'labs/demos/foafnaut');
const args=process.argv.slice(2),option=n=>{const i=args.indexOf(n);return i<0?null:args[i+1];};
const fixture=option('--fixture'),artifactPath=option('--artifact'),repeat=Number(option('--repeat')??1);
if(artifactPath&&!fixture)throw Error('--artifact requires --fixture (local diagnostic only)');
const suppliedArtifact=artifactPath?JSON.parse(await readFile(resolve(artifactPath),'utf8')):null;
if(!Number.isInteger(repeat)||repeat<1||repeat>120)throw Error('--repeat must be1..120');
const output=option('--output'),browserPath=option('--browser'),playwright=option('--playwright'),typescript=option('--typescript');
const controls=args.includes('--controls');
if(!output||!browserPath||!playwright)throw Error('Usage: browser_gpu.mjs --output DIR --browser CHROME --playwright /path/to/playwright-core/index.mjs [--typescript /path/to/typescript.js]');
const manifest=JSON.parse(await readFile(resolve(root,'manifest.json'),'utf8')),hash=b=>createHash('sha256').update(b).digest('hex');
// The complete pinned inventory has only 100%/100% or omitted-both relative
// roots. A future pin needs a new embedding review before this retry is valid.
const hostViewportPin='70dae60789ef6220d9b4e60c92c5b2107b4e2b93';
const pinnedViewportFallback=!fixture&&manifest.revision===hostViewportPin;
for(const f of manifest.files)if(hash(await readFile(resolve(root,'upstream',f.path)))!==f.sha256)throw Error(`Fixture hash mismatch: ${f.path}`);
await mkdir(output,{recursive:true});
const ts=typescript?(await import(pathToFileURL(resolve(typescript)).href)).default:null;
const transpile=source=>ts?ts.transpileModule(source,{compilerOptions:{target:ts.ScriptTarget.ES2022,module:ts.ModuleKind.ESNext}}).outputText:stripTypeScriptTypes(source);
// Freeze every served runtime byte before launch, so later builds cannot change
// bytes after their hashes are taken. This does not attest build correspondence.
const runtimeNames=['svg_engine.ts','gpu_transport.ts','render_plan.ts','.build/engines/svg-engine.mjs','.build/engines/svg-engine.wasm','.build/engines/render-plan.mjs','.build/engines/render-plan.wasm'];
const runtime=new Map(),runtimeAssets={};
for(const name of runtimeNames){const bytes=await readFile(resolve(lab,name));const body=name.endsWith('.ts')?Buffer.from(transpile(bytes.toString('utf8'))):bytes;runtime.set(name,body);runtimeAssets[name]={sourceSha256:hash(bytes),servedSha256:hash(body),bytes:body.length};}
const snapshot=await sourceSnapshot(repo,lab);
for(const name of runtimeNames)if(hash(await readFile(resolve(lab,name)))!==runtimeAssets[name].sourceSha256)throw Error('Runtime changed during snapshot: '+name);
const server=createServer(async(req,res)=>{try{
 const name=decodeURIComponent(new URL(req.url,'http://localhost').pathname);
 if(name==='/'){res.writeHead(200,{'Content-Type':'text/html'});res.end('<!doctype html><title>Lean raw WebGPU test transport</title>');return;}
 if(!name.startsWith('/lab/'))throw Error('not a lab module');
 const path=resolve(lab,name.slice(5));if(relative(lab,path).split(sep).includes('..'))throw Error('outside lab');
 const key=relative(lab,path).split(sep).join('/'),body=runtime.get(key);if(!body)throw Error('not a runtime asset');
 res.writeHead(200,{'Content-Type':path.endsWith('.wasm')?'application/wasm':'application/javascript','Cache-Control':'no-store'});res.end(body);
}catch{res.writeHead(404);res.end();}});
await new Promise((r,reject)=>{server.once('error',reject);server.listen(0,'127.0.0.1',r);});
const origin=`http://127.0.0.1:${server.address().port}`;
const {chromium}=await import(pathToFileURL(resolve(playwright)).href);
const cases=fixture?[{test:`local:${basename(fixture)}`,reference:'',requiredRuntime:[]}]:manifest.cases;
const report={scope:fixture?'local regression, not WPT':'unchanged 38-case WPT slice',revision:fixture?null:manifest.revision,host:{platform:platform(),release:release(),arch:arch()},backend:'browser-raw-webgpu',typescript:ts?.version??('node-strip-types '+process.version),browserExecutableSha256:hash(await readFile(browserPath)),viewport:{width:800,height:600,deviceScaleFactor:1},candidateSources:{},cases:[]};
report.sourceSnapshot=snapshot;report.runtimeAssets=runtimeAssets;
report.harnessSha256=hash(await readFile(fileURLToPath(import.meta.url)));report.controlsRequested=controls;
report.viewportPolicy={intrinsicFirst:true,hostFallbackPin:hostViewportPin,hostFallbackEnabled:pinnedViewportFallback,scope:'Pinned standalone roots are absolute,100%/100%,or omitted-both; no general CSS root-sizing claim'};
report.harnessSources={};for(const name of ['browser_gpu.mjs','provenance.mjs','manifest.json'])report.harnessSources[name]=hash(await readFile(resolve(root,name)));
for(const name of ['SVG.lean','SVGPath.lean','render_plan.ts','gpu_transport.ts','.build/engines/svg-engine.mjs','.build/engines/svg-engine.wasm','.build/engines/render-plan.mjs','.build/engines/render-plan.wasm'])report.candidateSources[name]=runtimeAssets[name]?.sourceSha256??hash(await readFile(resolve(lab,name)));
for(const name of ['Math/Affine.lean','Tdb2/Format.lean'])report.candidateSources[name]=hash(await readFile(resolve(repo,'formal/lean4/L4Factoidal',name)));
if(artifactPath)report.suppliedArtifact={sha256:hash(await readFile(resolve(artifactPath))),producer:'external scene artifact; source and WASM correspondence not established by this runner'};
let browser,activeCase=null;const adapterEvents=[];
try{
 browser=await chromium.launch({executablePath:browserPath,headless:true});report.browserVersion=browser.version();
 const context=await browser.newContext({viewport:{width:800,height:600},deviceScaleFactor:1});
 await context.route('**/*',r=>r.request().url().startsWith(origin+'/')?r.continue():r.abort());
 const page=await context.newPage();
 page.on('console',m=>{if(m.text().startsWith('GPU adapter:')){const name=activeCase;adapterEvents.push(m.args()[1].evaluate(i=>({vendor:i.vendor,architecture:i.architecture,device:i.device,description:i.description,isFallbackAdapter:i.isFallbackAdapter})).then(info=>({test:name,info})));}});
 await page.goto(origin+'/');
 await page.evaluate(async supplied=>{const t=await import('/lab/gpu_transport.ts');if(!supplied){const {loadSVG}=await import('/lab/svg_engine.ts');window.engine=await loadSVG();}window.transport=t;},Boolean(suppliedArtifact));
 for(const [i,c] of cases.entries()){
  activeCase=c.test;const row={test:c.test,reference:c.reference,status:'unavailable',viewportPolicy:{mode:'not-attempted'},svgViewport:null};
  if(c.requiredRuntime.length){row.reason='Original runtime/resource requirement: '+c.requiredRuntime.join(', ');report.cases.push(row);continue;}
  try{
   const xml=await readFile(fixture?resolve(fixture):resolve(root,'upstream',c.test),'utf8');row.sourceSha256=hash(Buffer.from(xml));
   const result=await page.evaluate(async ({xml,repeat,artifact,controls,pinnedViewportFallback})=>{
    const digest=async text=>[...new Uint8Array(await crypto.subtle.digest('SHA-256',new TextEncoder().encode(text)))].map(b=>b.toString(16).padStart(2,'0')).join('');
    const start=performance.now();
    let a=artifact,viewportPolicy={mode:'supplied-artifact'};
    if(!a){
     viewportPolicy={mode:'intrinsic',compilerWidth:0,compilerHeight:0};
     try{a=window.engine.compile(xml,0,0);}
     catch(error){
      const reason=String(error?.message??error);
      const needsHost=['SVG profile: percentage root dimensions require explicit host output viewport','SVG profile: root width required unless explicit output viewport is supplied'].includes(reason);
      if(!needsHost)return {compileError:reason,viewportPolicy};
      if(!pinnedViewportFallback)return {blocked:true,viewportPolicy,reason:'Intrinsic viewport unavailable; arbitrary local/future-pin embedding is not inferred: '+reason};
      viewportPolicy={mode:'pinned-document-host',compilerWidth:800,compilerHeight:600,reason};
      try{a=window.engine.compile(xml,800,600);}catch(error){return {compileError:String(error?.message??error),viewportPolicy};}
     }
    }
    if(a.error)throw Error('SVG profile: '+a.error);
    if(!Number.isInteger(a.width)||!Number.isInteger(a.height)||a.width<1||a.height<1||a.width>4096||a.height>4096)throw Error('Invalid artifact viewport');
    const compiled=performance.now();
    const session=await window.transport.createOffscreenSession(a,'svg-offscreen');if(!session)return {blocked:true,viewportPolicy,svgViewport:{width:a.width,height:a.height}};
    const ready=performance.now(),frameMs=[];let rgba;
    try{for(let i=0;i<repeat;i++){const t=performance.now();rgba=await session.draw();frameMs.push(performance.now()-t);}}
    finally{session.close();}
    // Match the oracle's top-left inline SVG on an800x600 white page.
    // Preserve the declared SVG viewport: no stretching of diagnostic pixels.
    const encode=rgba=>{
     let screenshot=rgba;
     if(a.width!==800||a.height!==600){
      screenshot=new Uint8Array(800*600*4).fill(255);
      for(let y=0;y<Math.min(600,a.height);y++)screenshot.set(rgba.subarray(y*a.width*4,(y*a.width+Math.min(800,a.width))*4),y*800*4);
     }
     const ppm=window.transport.encodePPM(screenshot,800,600);let binary='';for(let i=0;i<ppm.length;i+=32768)binary+=String.fromCharCode(...ppm.subarray(i,i+32768));return btoa(binary);
    };
    const controlImages={};
    if(controls){
     // A fresh unchanged session is a positive control for the capture path.
     // Mutated output is isolated from the candidate and never changes its score.
     for(const [name,control] of [['unchangedReplay',a],['gpuFlatMagenta',{...a,checks:[],wgsl:a.wgsl.replace(/@fragment\s+fn\s+fragment\b[\s\S]*$/,'@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {return vec4f(1.0,0.0,1.0,1.0)+clamp(params.rows[0],vec4f(0.0),vec4f(1.0))*0.000001;}')}]]){
      try{const s=await window.transport.createOffscreenSession(control,'svg-offscreen');if(!s)throw Error('GPU adapter unavailable');
       try{controlImages[name]={base64:encode(await s.draw()),stats:s.stats,leanChecks:control.checks.length,wgslSha256:await digest(control.wgsl)};}finally{s.close();}
      }catch(error){controlImages[name]={error:String(error)};}
     }
     // This byte-transport fault deliberately avoids every Lean sample point.
     // It tests that whole-image comparison can see a one-pixel readback error.
     const points=new Set(a.checks.map(p=>p.y*a.width+p.x));let pixel=0;
     while(points.has(pixel)&&pixel<a.width*a.height)pixel++;
     if(pixel<a.width*a.height){const changed=rgba.slice();changed[pixel*4]^=255;
      window.transport.checkPixels(a,changed);
      controlImages.unsampledReadbackPixel={base64:encode(changed),pixel:{x:pixel%a.width,y:Math.floor(pixel/a.width)},leanSamplesStillPass:true};}
     else controlImages.unsampledReadbackPixel={error:'No unsampled viewport pixel'};
    }
    return {base64:encode(rgba),controlImages,viewportPolicy,artifactIdentity:{sha256:await digest(JSON.stringify(a)),wgslSha256:await digest(a.wgsl)},compileMs:compiled-start,gpuSetupMs:ready-compiled,frameReadbackMs:frameMs,
      svgViewport:{width:a.width,height:a.height},resourceStats:session.stats,primitives:a.primitiveCount,floats:a.data.length,samplesVerified:a.checks.length};
   },{xml,repeat,artifact:suppliedArtifact,controls,pinnedViewportFallback});
   if(result.viewportPolicy)row.viewportPolicy=result.viewportPolicy;
   if(result.compileError)throw Error(result.compileError);
   if(result.blocked){row.reason=result.reason??'GPU adapter unavailable';row.svgViewport=result.svgViewport??null;report.cases.push(row);continue;}
   const bytes=Buffer.from(result.base64,'base64'),file=`${String(i).padStart(2,'0')}-actual.ppm`;
   await writeFile(resolve(output,file),bytes);const {base64,controlImages,...facts}=result;
   if(controls){row.controls={};for(const [name,control] of Object.entries(controlImages)){
    const {base64,...metadata}=control;row.controls[name]=metadata;
    if(base64){const bytes=Buffer.from(base64,'base64'),file=`${String(i).padStart(2,'0')}-control-${name}.ppm`;await writeFile(resolve(output,file),bytes);row.controls[name].image={file,sha256:hash(bytes)};}
   }}
   Object.assign(row,{status:'accepted',image:{file,sha256:hash(bytes)},...facts});
  }catch(error){const detail=String(error);row.detail=detail;row.status=detail.includes('WebGPU API absent')?'unavailable':detail.includes('SVG profile:')&&(detail.includes('unsupported')||detail.includes('foreign/non-SVG')||detail.includes('profile limit'))?'unsupported':'rejected';}
  report.cases.push(row);
 }
 report.adapters=await Promise.all(adapterEvents);await context.close();
}finally{await browser?.close();await new Promise(r=>server.close(r));}
report.total=report.cases.length;report.counts=Object.fromEntries(['accepted','unsupported','rejected','unavailable'].map(s=>[s,report.cases.filter(c=>c.status===s).length]));
await writeFile(resolve(output,'candidate.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({total:report.total,counts:report.counts,browserVersion:report.browserVersion,adapters:report.adapters}));
