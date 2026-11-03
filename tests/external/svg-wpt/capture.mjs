#!/usr/bin/env node
// Original WPT documents → independent Chrome images; original markup → Lean
// artifact → unchanged raw WebGPU. No host DOM extraction or layout.
import {readFile,writeFile,mkdir,appendFile,readdir,statfs} from 'node:fs/promises';
import {createServer} from 'node:http';
import {spawn} from 'node:child_process';
import {dirname,resolve,extname} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {gzipSync} from 'node:zlib';
import {stripTypeScriptTypes} from 'node:module';
import {encodeRGBA} from './png.mjs';
import {sourceSnapshot} from '../svg/provenance.mjs';
const here=dirname(fileURLToPath(import.meta.url)),args=process.argv.slice(2),option=name=>{const i=args.indexOf(name);return i<0?null:args[i+1];};
const output=option('--output'),chrome=option('--browser'),playwright=option('--playwright'),svgLab=option('--svg-lab'),htmlEngine=option('--html-engine'),htmlLab=option('--html-lab');
if(htmlLab&&htmlEngine)throw Error('Select one original HTML producer: --html-lab or --html-engine');
if(htmlLab&&!option('--html-witness'))throw Error('--html-lab requires its exact --html-witness');
const requestedCases=args.flatMap((arg,index)=>arg==='--case'?[args[index+1]]:[]);
if(option('--cases'))requestedCases.push(...JSON.parse(await readFile(resolve(option('--cases')),'utf8')));
const selection=requestedCases.length?[...new Set(requestedCases)]:null,controls=args.includes('--controls'),timeout=Number(option('--timeout-ms')??30000);
if(!output||!chrome||!playwright)throw Error('Usage: capture.mjs --output EMPTY_DIR --browser CHROME --playwright CORE [--svg-lab LAB] [--html-engine NATIVE_CLI] [--controls] [--case ORIGINAL_PATH]');
if(!Number.isFinite(timeout)||timeout<1000||timeout>120000)throw Error('Timeout must be 1000..120000ms');
await mkdir(output,{recursive:true});if((await readdir(output)).length)throw Error('Output directory must be empty');
const hash=bytes=>createHash('sha256').update(bytes).digest('hex'),sourceBytes=await readFile(resolve(here,'source.json')),inventoryBytes=await readFile(resolve(here,'inventory.json'));
const source=JSON.parse(sourceBytes),inventory=JSON.parse(inventoryBytes),files=new Map();
if(inventory.cases.length!==601||source.treeTruncated!==false)throw Error('Invalid whole-tree inventory');
for(const entry of source.files){const bytes=await readFile(resolve(here,'upstream',entry.path));if(hash(bytes)!==entry.sha256)throw Error('Fixture hash mismatch: '+entry.path);files.set(entry.path,bytes);}
if(selection&&selection.some(path=>typeof path!=='string'||!inventory.cases.some(c=>c.test===path)))throw Error('Requested path is not an original reftest');
const runtime=new Map(),runtimeAssets={};let svgReady=false,svgUnavailable=null;
const runtimeNames=['svg_engine.ts','render_plan.ts','gpu_transport.ts','.build/engines/svg-engine.mjs','.build/engines/svg-engine.wasm','.build/engines/render-plan.mjs','.build/engines/render-plan.wasm'];
if(svgLab)try{
 for(const name of runtimeNames){const bytes=await readFile(resolve(svgLab,name)),served=name.endsWith('.ts')?Buffer.from(stripTypeScriptTypes(bytes.toString('utf8'))):bytes;runtime.set(name,served);runtimeAssets[name]={sourceSha256:hash(bytes),servedSha256:hash(served),bytes:served.length};await writeFile(resolve(output,'svg-runtime-'+name.replaceAll('/','_')+'.gz'),gzipSync(bytes));}
 for(const name of runtimeNames)if(hash(await readFile(resolve(svgLab,name)))!==runtimeAssets[name].sourceSha256)throw Error('Runtime changed during snapshot');
 svgReady=true;
}catch(error){svgUnavailable=String(error);}
const webRuntime=new Map(),webAssets={};let webReady=false,webUnavailable=null;
const webNames=['web-render/engine.mjs','.build/web-render/engines/web-render.mjs','.build/web-render/engines/web-render.wasm'];
if(htmlLab)try{
 for(const name of webNames){const bytes=await readFile(resolve(htmlLab,name));webRuntime.set(name,bytes);webAssets[name]={sha256:hash(bytes),bytes:bytes.length};await writeFile(resolve(output,'html-runtime-'+name.replaceAll('/','_')+'.gz'),gzipSync(bytes));}
 for(const name of webNames)if(hash(await readFile(resolve(htmlLab,name)))!==webAssets[name].sha256)throw Error('HTML WASM runtime changed during snapshot');
 webReady=true;
}catch(error){webUnavailable=String(error);}
const producer={svg:{lab:svgLab,ready:svgReady,reason:svgUnavailable,runtimeAssets,
 source:svgLab?await sourceSnapshot(resolve(svgLab,'../../..'),resolve(svgLab)):null,
 correspondence:'Existing frozen artifact bytes; current checkout hashes alone do not attest build correspondence'},
 html:htmlEngine?{kind:'native-cli',command:resolve(htmlEngine),sha256:hash(await readFile(htmlEngine)),argv:'INPUT.html WIDTH HEIGHT',correspondence:'Native executable identity; source witness recorded separately'}:htmlLab?{kind:'browser-wasm',lab:resolve(htmlLab),ready:webReady,reason:webUnavailable,runtimeAssets:webAssets,correspondence:'Frozen browser-shipped runtime bytes; exact producer source witness recorded separately',fontInputs:'Default compile only; no font fallback or supplied font data'}:null};
for(const [kind,flag] of [['svg','--svg-witness'],['html','--html-witness']])if(option(flag)){
 const bytes=await readFile(resolve(option(flag)));producer[kind].witness={file:resolve(option(flag)),sha256:hash(bytes),value:JSON.parse(bytes)};
 await writeFile(resolve(output,kind+'-source-witness.json.gz'),gzipSync(bytes));
}
if(htmlLab&&webReady){
 const witness=producer.html.witness.value;
 if(witness.format!=='factoidal-web-render-source-witness-v1')throw Error('Unsupported HTML source witness format');
 for(const name of webNames.filter(n=>n.startsWith('.build/')))if(witness.engines['labs/demos/foafnaut/'+name]!==webAssets[name].sha256)throw Error('Frozen HTML engine differs from source witness: '+name);
 producer.html.witnessValidatedEngines=true;
}
if(svgReady&&producer.svg.witness?.value.enginesSHA256){
 for(const name of runtimeNames)if(producer.svg.witness.value.enginesSHA256[name]!==runtimeAssets[name].sourceSha256)throw Error('Frozen SVG runtime differs from source witness: '+name);
 producer.svg.witnessValidatedEngines=true;
}
if(htmlEngine&&producer.html.witness?.value.nativeSha256){
 if(producer.html.witness.value.nativeSha256!==producer.html.sha256)throw Error('Native HTML executable differs from source witness');
 producer.html.witnessValidatedNativeBytes=true;
}
const report={format:'wpt-svg-whole-tree-capture-v1',revision:source.revision,scope:selection?'Diagnostic selection; all 601 rows retained, unselected unavailable':'All 601 original SVG-subtree reftest relations; old 38 identified separately',selection,
 startedAt:new Date().toISOString(),sourceManifestSha256:hash(sourceBytes),inventorySha256:hash(inventoryBytes),producer,
 browserExecutableSha256:hash(await readFile(chrome)),node:process.version,viewport:{width:800,height:600,deviceScaleFactor:1},
 oraclePolicy:{javascript:false,externalOrigins:false,originalBytes:true,readiness:'load, document.fonts.ready, native screenshot paint flush; no animation-frame timing claim',fonts:'Original declared font faces must load; installed font environment not independently certified',runtime:'JavaScript, animation, reftest-wait, testdriver, WPT dynamic server/print and unresolved xml:base remain unavailable'},controlsRequested:controls,cases:[]};
report.harnessSources={};for(const name of ['capture.mjs','png.mjs','corpus.py']){const bytes=await readFile(resolve(here,name));report.harnessSources[name]=hash(bytes);await writeFile(resolve(output,'harness-'+name+'.gz'),gzipSync(bytes));}
await writeFile(resolve(output,'source.json.gz'),gzipSync(sourceBytes));await writeFile(resolve(output,'inventory.json.gz'),gzipSync(inventoryBytes));
const state={phase:'starting',test:null};
async function checkpoint(message){await appendFile('/tmp/factoidal-overnight-corpus-status.md',`\n## ${new Date().toISOString()}\n${message}\n`);}
const heartbeat=setInterval(()=>checkpoint(`Capture heartbeat: ${state.phase}; ${state.test??''}; ${report.cases.length}/601 rows. Output ${resolve(output)}`).catch(()=>{}),3600000);heartbeat.unref();
async function diskGuard(){const fs=await statfs(output);if(fs.bavail*fs.bsize<3*1024**3)throw Error('Disk guard: less than 3 GiB available');}
const mime=name=>({'.svg':'image/svg+xml','.html':'text/html','.htm':'text/html','.xht':'application/xhtml+xml','.xhtml':'application/xhtml+xml','.xml':'application/xml','.css':'text/css','.js':'text/javascript','.mjs':'text/javascript','.ts':'text/javascript','.wasm':'application/wasm','.png':'image/png','.jpg':'image/jpeg','.woff':'font/woff','.woff2':'font/woff2','.ttf':'font/ttf'}[extname(name)]??'application/octet-stream');
const missingOriginal=new Set(Object.keys(inventory.originallyAbsentDependencyURLs));
const server=createServer((req,res)=>{
 try{
  if(!['GET','HEAD'].includes(req.method)){res.writeHead(405);res.end();return;}
  const url=new URL(req.url,'http://127.0.0.1'),name=decodeURIComponent(url.pathname);
  if(name==='/transport'){res.writeHead(200,{'Content-Type':'text/html','Cache-Control':'no-store'});res.end('<!doctype html><title>Raw WebGPU transport</title>');return;}
  let bytes,type,headers={};
  if(name.startsWith('/engine/')){const key=name.slice(8);bytes=runtime.get(key);type=mime(key);}
  else if(name.startsWith('/lab/')){const key=name.slice(5);bytes=webRuntime.get(key);type=mime(key);}
  else{
   const key=name.slice(1);bytes=files.get(key);type=mime(key);
   const headerFiles=inventory.resourceMetadata[key]?.responseHeaderFiles??[];
   for(const path of [...headerFiles].reverse())for(const line of (files.get(path)?.toString('utf8')??'').split(/\r?\n/)){
    const m=line.match(/^([A-Za-z0-9-]+):\s*(.*)$/);if(m&&!m[2].includes('{{'))headers[m[1]]=m[2];
   }
  }
  if(!bytes){res.writeHead(404,{'Cache-Control':'no-store'});res.end();return;}
  res.writeHead(200,{'Content-Type':type,'Cache-Control':'no-store','X-Content-Type-Options':'nosniff',...headers});res.end(req.method==='HEAD'?undefined:bytes);
 }catch{res.writeHead(404);res.end();}
});
await new Promise((accept,reject)=>{server.once('error',reject);server.listen(0,'127.0.0.1',accept);});
const origin=`http://127.0.0.1:${server.address().port}`,blockedRequirements=new Set(['javascript','animation','reftest-wait','testdriver','wpt-server-template','wpt-server-handler','wpt-server-resource','print-context','xml-base-context-unresolved','non-utf8-source']);
const {chromium}=await import(pathToFileURL(resolve(playwright)).href);let browser,transportContext,transportPage,exitCode=0;
const oracleCache=new Map();
async function bounded(promise,label){let timer;try{return await Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error(label+' timeout')),timeout);})]);}finally{clearTimeout(timer);}}
async function oracle(target,requirements){
 const needs=requirements.filter(r=>blockedRequirements.has(r));if(needs.length)return {status:'unavailable',reason:'Original oracle runtime requirement: '+needs.join(', ')};
 if(!target)return {status:'unavailable',reason:'Unresolved original reference URI'};
 const key=JSON.stringify(target);if(oracleCache.has(key))return oracleCache.get(key);
 if(target.path&&!files.has(target.path))return {status:'unavailable',reason:'Original reference bytes not available'};
 const context=await browser.newContext({viewport:{width:800,height:600},deviceScaleFactor:1,javaScriptEnabled:false,colorScheme:'light',reducedMotion:'no-preference'}),page=await context.newPage(),requests=[];
 await context.route('**/*',route=>route.request().url().startsWith(origin+'/')?route.continue():route.abort());
 page.on('response',response=>{if(response.status()>=400){const url=new URL(response.url());const path=decodeURIComponent(url.pathname).replace(/^\//,'');if(url.pathname!=='/favicon.ico'&&!missingOriginal.has(path))requests.push({url:response.url(),status:response.status()});}});
 page.on('requestfailed',request=>requests.push({url:request.url(),failure:request.failure()}));
 let result;
 try{
  const url=target.special==='about:blank'?'about:blank':origin+'/'+target.path+(target.query?'?'+target.query:'')+(target.fragment?'#'+target.fragment:'');
  const response=await page.goto(url,{waitUntil:'load',timeout});if(response&&!response.ok())throw Error('Original navigation HTTP '+response.status());
  const fonts=await bounded(page.evaluate(async()=>{await document.fonts.ready;return [...document.fonts].map(f=>({family:f.family,status:f.status}));}),'Original font readiness');
  if(fonts.some(f=>f.status==='error'))throw Error('Original declared font failed to load');
  if(requirements.includes('font-Ahem')&&!fonts.some(f=>f.status==='loaded'&&f.family.replaceAll('"','').replaceAll("'",'').toLowerCase()==='ahem'))throw Error('Ahem requirement lacks a loaded declared face; installed fonts not certified');
  if(requests.length)throw Error('Unsupplied original resource/runtime: '+JSON.stringify(requests));
  const bytes=await page.screenshot({fullPage:false,animations:'allow'}),name='oracle-'+hash(Buffer.from(key)).slice(0,20)+'.png';await writeFile(resolve(output,name),bytes);
  result={status:'captured',image:{file:name,sha256:hash(bytes)},sourceSha256:target.path?hash(files.get(target.path)):null,target,fonts};
 }catch(error){result={status:'unavailable',reason:String(error),target};}
 finally{await context.close();}
 oracleCache.set(key,result);return result;
}
async function loadTransport(){
 await transportContext?.close();transportContext=await browser.newContext({viewport:{width:800,height:600},deviceScaleFactor:1});
 await transportContext.route('**/*',r=>r.request().url().startsWith(origin+'/engine/')||r.request().url().startsWith(origin+'/lab/')||r.request().url()===origin+'/transport'?r.continue():r.abort());
 transportPage=await transportContext.newPage();await transportPage.goto(origin+'/transport');
 await bounded(transportPage.evaluate(async()=>{window.transport=await import('/engine/gpu_transport.ts');const svg=await import('/engine/svg_engine.ts');window.validate=svg.validateSVG;window.engine=await svg.loadSVG();}),'Engine initialization');
 if(htmlLab&&producer.html.ready)try{await bounded(transportPage.evaluate(async()=>{window.webEngine=await import('/lab/web-render/engine.mjs');}),'HTML WASM entry initialization');}catch(error){producer.html.ready=false;producer.html.reason=String(error);}
}
async function nativeHTML(path){
 if(!htmlEngine)return {unavailable:'HTML producer not configured; original document not extracted or rewritten'};
 if(hash(await readFile(htmlEngine))!==producer.html.sha256)throw Error('HTML native executable changed during capture');
 const argv=[resolve(here,'upstream',path),'800','600'];
 const result=await new Promise((accept,reject)=>{
  const child=spawn(resolve(htmlEngine),argv,{stdio:['ignore','pipe','pipe']}),out=[],err=[];let size=0;
  const timer=setTimeout(()=>{child.kill('SIGKILL');reject(Error('HTML native timeout'));},timeout);
  child.stdout.on('data',b=>{size+=b.length;if(size>8*1024*1024){child.kill('SIGKILL');reject(Error('HTML native output limit'));}out.push(b);});child.stderr.on('data',b=>{if(Buffer.concat(err).length<8192)err.push(b);});
  child.once('error',reject);child.once('close',(code,signal)=>{clearTimeout(timer);accept({code,signal,stdout:Buffer.concat(out).toString('utf8'),stderr:Buffer.concat(err).toString('utf8')});});
 });
 if(hash(await readFile(htmlEngine))!==producer.html.sha256)throw Error('HTML native executable changed during call');
 if(result.code!==0)return {error:'Native process failure '+JSON.stringify(result)};
 const artifact=JSON.parse(result.stdout);return {artifact,command:[resolve(htmlEngine),...argv],stderr:result.stderr};
}
async function gpu(xml,artifact,eligible,documentURL,isHTML){
 return bounded(transportPage.evaluate(async({xml,artifact,eligible,controls,documentURL,isHTML})=>{
  let a=artifact,policy={mode:'native-original-html-artifact'};
  if(!a&&isHTML){a=await window.webEngine.compile(xml,800,600);policy={mode:'wasm-original-html-artifact',compilerWidth:800,compilerHeight:600,fontInputs:'none'};}
  if(!a){
   if(typeof window.engine.compileDocument==='function'){a=window.engine.compileDocument(xml,800,600);policy={mode:'Lean-document-available-viewport',availableWidth:800,availableHeight:600};}
   else{const compile=(w,h)=>typeof window.engine.compileWithURL==='function'?window.engine.compileWithURL(xml,documentURL,w,h):window.engine.compile(xml,w,h);policy={mode:'intrinsic',compilerWidth:0,compilerHeight:0,documentURL,URLAware:typeof window.engine.compileWithURL==='function'};try{a=compile(0,0);}catch(error){
    const reason=String(error?.message??error),known=['SVG profile: percentage root dimensions require explicit host output viewport','SVG profile: root width required unless explicit output viewport is supplied'].includes(reason);
    if(!known)throw error;if(!eligible)return {unavailable:'Intrinsic viewport unresolved; author sizing not inferred by host',viewportPolicy:policy};
    a=compile(800,600);policy={mode:'inventoried-full-viewport-root',compilerWidth:800,compilerHeight:600,documentURL,URLAware:typeof window.engine.compileWithURL==='function',reason};
   }}
  }
  if(a.error)return {error:a.error,viewportPolicy:policy};
  const identity={artifactJSON:JSON.stringify(a),width:a.width,height:a.height,rootViewport:a.rootViewport??null,viewportPolicy:policy};
  try{window.validate(a);}catch(error){return {...identity,error:String(error)};}
  const encode=rgba=>{let binary='';for(let i=0;i<rgba.length;i+=32768)binary+=String.fromCharCode(...rgba.subarray(i,i+32768));return btoa(binary);};
  async function draw(value){let submitted;const session=await window.transport.createOffscreenSession(value,'svg-offscreen',s=>submitted=s);if(!session)return {unavailable:'GPU adapter unavailable'};
   try{const rgba=await session.draw();return {rgba:encode(rgba),stats:session.stats,adapter:{vendor:session.adapterInfo.vendor,architecture:session.adapterInfo.architecture,isFallbackAdapter:session.adapterInfo.isFallbackAdapter},submittedCode:submitted?.code??value.wgsl};}
   catch(error){return {error:String(error),submittedCode:submitted?.code??null};}finally{session.close();}}
  const frame=await draw(a);if(frame.unavailable)return frame;
  if(frame.error)return {...identity,...frame};
  const controlFrames={};
  if(controls){
   for(const [name,value] of [['unchangedReplay',a],['gpuFlatMagenta',{...a,checks:[],wgsl:a.wgsl.replace(/@fragment\s+fn\s+fragment\b[\s\S]*$/,'@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {return vec4f(1.0,0.0,1.0,1.0)+clamp(params.rows[0],vec4f(0.0),vec4f(1.0))*0.000001;}')}]])try{const control=await draw(value);controlFrames[name]=control.error?{unavailable:control.error}:{...control,leanChecks:value.checks.length};}catch(error){controlFrames[name]={unavailable:String(error)};}
   const original=Uint8Array.from(atob(frame.rgba),c=>c.charCodeAt(0)),changed=original.slice(),sampled=new Set(a.checks.map(p=>p.y*a.width+p.x));let pixel=0;while(sampled.has(pixel)&&pixel<a.width*a.height)pixel++;
   if(pixel<a.width*a.height){changed[pixel*4]^=255;window.transport.checkPixels(a,changed);controlFrames.unsampledReadbackPixel={rgba:encode(changed),pixel:{x:pixel%a.width,y:Math.floor(pixel/a.width)},leanSamplesStillPass:true};}
  }
  return {...frame,controlFrames,...identity,samplesVerified:a.checks.length};
 },{xml,artifact,eligible,controls,documentURL,isHTML}),'Candidate compile/GPU');
}
function fullPageRGBA(bytes,width,height){
 if(width===800&&height===600)return bytes;
 const out=Buffer.alloc(800*600*4,255);for(let y=0;y<Math.min(600,height);y++)bytes.copy(out,y*800*4,y*width*4,(y*width+Math.min(800,width))*4);return out;
}
async function saveFrame(frame,prefix,width,height){
 const {rgba,submittedCode,...metadata}=frame;if(!rgba)return metadata;
 const raw=Buffer.from(rgba,'base64'),full=fullPageRGBA(raw,width,height),png=encodeRGBA(800,600,full),name=prefix+'.png';await writeFile(resolve(output,name),png);
 return {...metadata,image:{file:name,sha256:hash(png),rgbaSha256:hash(full)},submittedShaderSha256:submittedCode?hash(Buffer.from(submittedCode)):null};
}
try{
 await diskGuard();browser=await chromium.launch({executablePath:resolve(chrome),headless:true});report.browserVersion=browser.version();
 if(svgReady)try{await loadTransport();}catch(error){producer.svg.ready=false;producer.svg.reason=String(error);}
 for(const [index,c] of inventory.cases.entries()){
  state.test=c.test;state.phase='oracle/candidate';if(index%20===0){await diskGuard();console.log(JSON.stringify({phase:state.phase,at:index,total:601,test:c.test}));await writeFile(resolve(output,'capture.partial.json'),JSON.stringify(report,null,2)+'\n');}
  const row={...c,index,status:'unavailable',sourceSha256:hash(files.get(c.test))};
  if(selection&&!selection.includes(c.test)){row.reason='Not selected diagnostic';report.cases.push(row);continue;}
  row.oracle={test:await oracle({path:c.test,query:'',fragment:''},c.testRequirements),reference:await oracle(c.reference,c.referenceRequirements)};
  const needs=c.testRequirements.filter(r=>blockedRequirements.has(r));if(needs.length){row.reason='Original candidate runtime requirement: '+needs.join(', ');report.cases.push(row);continue;}
  if(!producer.svg.ready){row.reason='Raw GPU runtime unavailable: '+(producer.svg.reason??'--svg-lab not supplied');report.cases.push(row);continue;}
  try{
   const html=!c.test.endsWith('.svg');let supplied=null;
   if(html&&htmlLab&&!producer.html.ready){row.reason='Original HTML WASM producer unavailable: '+producer.html.reason;report.cases.push(row);continue;}
   if(html&&!htmlLab){const result=await nativeHTML(c.test);row.nativeProducer=result.command?{command:result.command,stderr:result.stderr}:null;
    if(result.unavailable){row.reason=result.unavailable;report.cases.push(row);continue;}if(result.error)throw Error(result.error);supplied=result.artifact;
    if(supplied.error)throw Error(supplied.error);
   }
   const dimensions=inventory.resourceMetadata[c.test].rootSVGDimensions,eligible=dimensions&&((dimensions.width==null&&dimensions.height==null)||(dimensions.width==='100%'&&dimensions.height==='100%'));
   row.producerKind=html?(htmlLab?'html-browser-wasm':'html-native-cli'):'svg-browser-wasm';
   const result=await gpu(files.get(c.test).toString('utf8'),supplied,Boolean(eligible),origin+'/'+c.test,html&&Boolean(htmlLab));
   if(result.artifactJSON){
    const artifact=Buffer.from(result.artifactJSON),name=String(index).padStart(4,'0')+'-artifact.json.gz';await writeFile(resolve(output,name),gzipSync(artifact));row.artifact={file:name,sha256:hash(artifact),wgslSha256:hash(Buffer.from(JSON.parse(result.artifactJSON).wgsl))};
    if(result.submittedCode)row.submittedShaderSha256=hash(Buffer.from(result.submittedCode));
   }
   if(result.unavailable){row.reason=result.unavailable;row.viewportPolicy=result.viewportPolicy;report.cases.push(row);continue;}
   if(result.error)throw Error(result.error);
   const {controlFrames,artifactJSON,rgba,submittedCode,...facts}=result;Object.assign(row,await saveFrame({rgba,submittedCode,...facts},String(index).padStart(4,'0')+'-candidate',result.width,result.height));
   row.controls={};for(const [name,frame] of Object.entries(controlFrames))row.controls[name]=await saveFrame(frame,String(index).padStart(4,'0')+'-control-'+name,result.width,result.height);
   row.status='accepted';
  }catch(error){const detail=String(error);row.detail=detail;row.status=/unsupported|foreign\/non-SVG|profile limit/i.test(detail)?'unsupported':/timeout|WebGPU API absent|GPU adapter unavailable/.test(detail)?'unavailable':'rejected';
   if(detail.includes('timeout'))try{await loadTransport();}catch(error){producer.svg.ready=false;producer.svg.reason=String(error);}
  }
  report.cases.push(row);
 }
}catch(error){report.fatal=String(error);exitCode=2;}
finally{
 clearInterval(heartbeat);await transportContext?.close();await browser?.close();await new Promise(r=>server.close(r));
 while(report.cases.length<inventory.cases.length){const c=inventory.cases[report.cases.length];report.cases.push({...c,status:'unavailable',reason:report.fatal??'Capture interrupted before case'});}
 report.finishedAt=new Date().toISOString();report.total=report.cases.length;report.complete=!report.fatal&&!selection;report.exitCode=exitCode;
 report.counts=Object.fromEntries(['accepted','unsupported','rejected','unavailable'].map(s=>[s,report.cases.filter(c=>c.status===s).length]));
 await writeFile(resolve(output,'capture.json'),JSON.stringify(report,null,2)+'\n');await writeFile(resolve(output,'capture.exit'),String(exitCode)+'\n');
 await checkpoint(`Capture finished rc=${exitCode}; ${report.total} original relations; ${JSON.stringify(report.counts)}; ${resolve(output,'capture.json')}`);
 console.log(JSON.stringify({phase:'CAPTURE_FINISHED',exitCode,total:report.total,counts:report.counts,report:resolve(output,'capture.json')}));
}
process.exitCode=exitCode;
