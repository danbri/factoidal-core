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
const root=dirname(fileURLToPath(import.meta.url)),repo=resolve(root,'../../..'),lab=resolve(repo,'labs/demos/foafnaut');
const args=process.argv.slice(2),option=n=>{const i=args.indexOf(n);return i<0?null:args[i+1];};
const fixture=option('--fixture'),artifactPath=option('--artifact'),repeat=Number(option('--repeat')??1);
if(artifactPath&&!fixture)throw Error('--artifact requires --fixture (local diagnostic only)');
const suppliedArtifact=artifactPath?JSON.parse(await readFile(resolve(artifactPath),'utf8')):null;
if(!Number.isInteger(repeat)||repeat<1||repeat>120)throw Error('--repeat must be1..120');
const output=option('--output'),browserPath=option('--browser'),playwright=option('--playwright'),typescript=option('--typescript');
if(!output||!browserPath||!playwright)throw Error('Usage: browser_gpu.mjs --output DIR --browser CHROME --playwright /path/to/playwright-core/index.mjs [--typescript /path/to/typescript.js]');
const manifest=JSON.parse(await readFile(resolve(root,'manifest.json'),'utf8')),hash=b=>createHash('sha256').update(b).digest('hex');
for(const f of manifest.files)if(hash(await readFile(resolve(root,'upstream',f.path)))!==f.sha256)throw Error(`Fixture hash mismatch: ${f.path}`);
await mkdir(output,{recursive:true});
const ts=typescript?(await import(pathToFileURL(resolve(typescript)).href)).default:null;
const transpile=source=>ts?ts.transpileModule(source,{compilerOptions:{target:ts.ScriptTarget.ES2022,module:ts.ModuleKind.ESNext}}).outputText:stripTypeScriptTypes(source);
const server=createServer(async(req,res)=>{try{
 const name=decodeURIComponent(new URL(req.url,'http://localhost').pathname);
 if(name==='/'){res.writeHead(200,{'Content-Type':'text/html'});res.end('<!doctype html><title>Lean raw WebGPU test transport</title>');return;}
 if(!name.startsWith('/lab/'))throw Error('not a lab module');
 const path=resolve(lab,name.slice(5));if(relative(lab,path).split(sep).includes('..'))throw Error('outside lab');
 const bytes=await readFile(path);const body=path.endsWith('.ts')?transpile(bytes.toString('utf8')):bytes;
 res.writeHead(200,{'Content-Type':path.endsWith('.wasm')?'application/wasm':'application/javascript','Cache-Control':'no-store'});res.end(body);
}catch{res.writeHead(404);res.end();}});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`;
const {chromium}=await import(pathToFileURL(resolve(playwright)).href);
const cases=fixture?[{test:`local:${basename(fixture)}`,reference:'',requiredRuntime:[]}]:manifest.cases;
const report={scope:fixture?'local regression, not WPT':'unchanged 38-case WPT slice',revision:fixture?null:manifest.revision,host:{platform:platform(),release:release(),arch:arch()},backend:'browser-raw-webgpu',typescript:ts?.version??('node-strip-types '+process.version),browserExecutableSha256:hash(await readFile(browserPath)),viewport:{width:800,height:600,deviceScaleFactor:1},candidateSources:{},cases:[]};
for(const name of ['SVG.lean','SVGPath.lean','render_plan.ts','gpu_transport.ts','.build/engines/svg-engine.mjs','.build/engines/svg-engine.wasm','.build/engines/render-plan.mjs','.build/engines/render-plan.wasm'])report.candidateSources[name]=hash(await readFile(resolve(lab,name)));
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
  activeCase=c.test;const row={test:c.test,reference:c.reference,status:'unavailable'};
  if(c.requiredRuntime.length){row.reason='Original runtime/resource requirement: '+c.requiredRuntime.join(', ');report.cases.push(row);continue;}
  try{
   const xml=await readFile(fixture?resolve(fixture):resolve(root,'upstream',c.test),'utf8');row.sourceSha256=hash(Buffer.from(xml));
   const result=await page.evaluate(async ({xml,repeat,artifact})=>{
    const start=performance.now();
    const a=artifact??window.engine.compile(xml,800,600);
    if(a.error)throw Error('SVG profile: '+a.error);
    if(!Number.isInteger(a.width)||!Number.isInteger(a.height)||a.width<1||a.height<1||a.width>4096||a.height>4096)throw Error('Invalid artifact viewport');
    const compiled=performance.now();
    const session=await window.transport.createOffscreenSession(a,'svg-offscreen');if(!session)return {blocked:true};
    const ready=performance.now(),frameMs=[];let rgba;
    try{for(let i=0;i<repeat;i++){const t=performance.now();rgba=await session.draw();frameMs.push(performance.now()-t);}}
    finally{session.close();}
    // Match the oracle's top-left inline SVG on an800x600 white page.
    // Preserve the declared SVG viewport: no stretching of diagnostic pixels.
    let screenshot=rgba;
    if(a.width!==800||a.height!==600){
      screenshot=new Uint8Array(800*600*4).fill(255);
      for(let y=0;y<Math.min(600,a.height);y++)screenshot.set(rgba.subarray(y*a.width*4,(y*a.width+Math.min(800,a.width))*4),y*800*4);
    }
    const ppm=window.transport.encodePPM(screenshot,800,600);let binary='';for(let i=0;i<ppm.length;i+=32768)binary+=String.fromCharCode(...ppm.subarray(i,i+32768));
    return {base64:btoa(binary),compileMs:compiled-start,gpuSetupMs:ready-compiled,frameReadbackMs:frameMs,
      svgViewport:{width:a.width,height:a.height},resourceStats:session.stats,primitives:a.primitiveCount,floats:a.data.length,samplesVerified:a.checks.length};
   },{xml,repeat,artifact:suppliedArtifact});
   if(result.blocked){row.reason='GPU adapter unavailable';report.cases.push(row);continue;}
   const bytes=Buffer.from(result.base64,'base64'),file=`${String(i).padStart(2,'0')}-actual.ppm`;
   await writeFile(resolve(output,file),bytes);const {base64,...facts}=result;
   Object.assign(row,{status:'accepted',image:{file,sha256:hash(bytes)},...facts});
  }catch(error){const detail=String(error);row.detail=detail;row.status=detail.includes('WebGPU API absent')?'unavailable':detail.includes('SVG profile:')&&(detail.includes('unsupported')||detail.includes('foreign/non-SVG')||detail.includes('profile limit'))?'unsupported':'rejected';}
  report.cases.push(row);
 }
 report.adapters=await Promise.all(adapterEvents);await context.close();
}finally{await browser?.close();await new Promise(r=>server.close(r));}
report.total=report.cases.length;report.counts=Object.fromEntries(['accepted','unsupported','rejected','unavailable'].map(s=>[s,report.cases.filter(c=>c.status===s).length]));
await writeFile(resolve(output,'candidate.json'),JSON.stringify(report,null,2)+'\n');console.log(JSON.stringify({total:report.total,counts:report.counts,browserVersion:report.browserVersion,adapters:report.adapters}));
