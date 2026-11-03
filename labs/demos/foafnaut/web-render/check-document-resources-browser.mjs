#!/usr/bin/env node
// Real HTTP resources, original source, Lean discovery/layout, QuickJS mutation
// and WebGPU. Resource identity must follow the commanded DOM, not only nodeId.
import assert from 'node:assert/strict';
import {createServer} from 'node:http';
import {once} from 'node:events';
import {mkdir,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
const [origin,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-document-resources-browser.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});
const html=`<!doctype html><base id="base" href="/old/"><style>body{margin:0;font-family:Arial;font-size:7px;line-height:48px}a{display:block}</style><link id="sheet" rel="stylesheet" href="style.css"><p id="message">Payload</p><p id="count">Count 0</p><a id="switch" href="#switch">Switch resource</a><a id="next" href="target">Next page</a><a id="slow" href="#slow">Slow resource</a><script>
let count=0;
document.getElementById('base').setAttribute('href','/new/');
document.getElementById('sheet').setAttribute('href','style20.css');
document.getElementById('switch').addEventListener('click',function(event){
 event.preventDefault();count++;document.getElementById('count').textContent='Count '+count;
 if(count===1)document.getElementById('sheet').setAttribute('href','alternate.css');
 if(count===2)document.getElementById('base').setAttribute('href','/other/');
 if(count===3)document.getElementById('sheet').setAttribute('media','print');
 if(count===4)document.getElementById('sheet').setAttribute('media','screen');
 if(count===5)document.getElementById('sheet').setAttribute('href','missing.css');
});
document.getElementById('slow').addEventListener('click',function(event){event.preventDefault();document.getElementById('sheet').setAttribute('href','slow.css');});
</script>`;
const requests=[];
const fixture=createServer((req,res)=>{
 requests.push(req.url);const path=new URL(req.url,'http://fixture.test').pathname;
 if(path==='/page'){res.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});res.end(html);return;}
 if(path==='/new/style20.css'){res.writeHead(302,{Location:'/assets/font20.css'});res.end();return;}
 const sizes={'/old/style.css':10,'/assets/font20.css':20,'/new/alternate.css':30,'/other/alternate.css':40};
 if(path in sizes){res.writeHead(200,{'Content-Type':'text/css'});res.end(`body{font-size:${sizes[path]}px}`);return;}
 if(path.endsWith('/slow.css')){setTimeout(()=>{if(!res.destroyed){res.writeHead(200,{'Content-Type':'text/css'});res.end('body{font-size:50px}');}},400);return;}
 if(/^\/budget\d+\.css$/.test(path)){res.writeHead(200,{'Content-Type':'text/css'});res.end(Buffer.alloc(1048576,32));return;}
 if(path==='/other/target'){res.writeHead(200,{'Content-Type':'text/html; charset=utf-8'});res.end('<p>Arrived</p>');return;}
 res.writeHead(404);res.end('Missing resource');
});
fixture.listen(0,'127.0.0.1');await once(fixture,'listening');
const target=`http://127.0.0.1:${fixture.address().port}`,{chromium}=await import(pathToFileURL(playwrightPath)),browser=await chromium.launch({executablePath:browserPath,headless:true,args:['--enable-unsafe-webgpu']}),report={status:'RUNNING',checks:[]};
try{
 const page=await browser.newPage({viewport:{width:1440,height:1050}}),errors=[];page.on('pageerror',error=>errors.push(error.message));
 await page.goto(origin+'?url='+encodeURIComponent(target+'/page'));
 async function size(expected){await page.waitForFunction(expected=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text==='Payload'&&run.size===expected),expected,{timeout:90000});}
 async function click(suffix){
  const link=await page.evaluate(suffix=>window.webRenderResult.artifact.webRender.links.find(row=>row[1].endsWith(suffix)),suffix);assert(link);
  const point=await page.locator('#output').evaluate((canvas,row)=>{const rect=canvas.getBoundingClientRect();return{x:rect.left+(row[2]+row[4]/2)*canvas.clientWidth/canvas.width,y:rect.top+(row[3]+row[5]/2)*canvas.clientHeight/canvas.height};},link);
  await page.mouse.click(point.x,point.y);
 }
 await size(20);assert.equal(await page.locator('#source').inputValue(),html);
 assert(requests.includes('/old/style.css'));assert(requests.includes('/new/style20.css'));assert(requests.includes('/assets/font20.css'));
 report.checks.push('initial script base+href changes fetch new 20px CSS instead of reusing initial 10px bytes');
 await page.locator('#width').fill('700');await page.waitForFunction(()=>window.webRenderResult?.artifact?.width===700,{},{timeout:90000});await size(20);
 assert.equal(requests.filter(path=>path==='/new/style20.css').length,1);report.checks.push('redirect final URL does not invalidate stable requested-URL identity on resize');
 await click('#switch');await size(30);assert.equal(requests.filter(path=>path==='/new/alternate.css').length,1);
 await click('#switch');await size(40);assert.equal(requests.filter(path=>path==='/other/alternate.css').length,1);
 assert(await page.evaluate(()=>window.webRenderResult.artifact.webRender.glyphRuns.some(run=>run.text==='2')));report.checks.push('href-only and base-only commands each refresh CSS while retaining the same script VM');
 await click('#switch');await size(7);await click('#switch');await size(40);assert.equal(requests.filter(path=>path==='/other/alternate.css').length,2);report.checks.push('inactive stylesheet is discarded; reactivation fetches the resource again');
 await page.screenshot({path:resolve(outDir,'updated-resource.png'),fullPage:true});
 await click('target');await page.waitForFunction(expected=>window.webBrowserState?.url===expected&&!window.webBrowserState.loading,target+'/other/target',{timeout:90000});assert(requests.includes('/other/target'));report.checks.push('normal link uses the updated Lean base URL');
 await page.locator('#back').click();await size(20);
 for(const expected of [30,40,7,40]){await click('#switch');await size(expected);}
 await click('#switch');await page.waitForFunction(()=>/404/.test(document.querySelector('#status').textContent),{},{timeout:90000});
 assert(requests.includes('/other/missing.css'));report.checks.push('failed changed resource reports an error without rendering with old CSS');
 const abort=await page.evaluate(async target=>{
  const engine=await import('/engine.mjs'),{prepareDocument}=await import('/document-client.mjs'),response=await fetch('/resource?url='+encodeURIComponent(target+'/page')),source=await response.text();
  let compiles=0;const observed={...engine,compileDocument(...args){compiles++;return engine.compileDocument(...args);}};
  const doc=await prepareDocument(observed,source,{url:target+'/page'});await doc.compile(120,200);
  const resource=doc.options.resources[0];if(doc.baseURL!==target+'/new/'||resource.requestedURL!==target+'/new/style20.css'||resource.url!==target+'/assets/font20.css')throw Error('Requested/final URL metadata or effective base was not retained');
  const snapshot=await engine.inspectDocument(source),id=snapshot.nodes.find(node=>node.attributes.id==='slow').id;
  const controller=new AbortController(),pending=doc.dispatch(id,{signal:controller.signal});setTimeout(()=>controller.abort(),50);
  let failed=false;try{await pending;}catch(error){failed=controller.signal.aborted;}
  doc.close();return {failed,compiles};
 },target);
 assert.deepEqual(abort,{failed:true,compiles:1});report.checks.push('aborted refresh cannot fall through to stale-resource compilation');
 const budgets=await page.evaluate(async target=>{
  const engine=await import('/engine.mjs'),{prepareDocument}=await import('/document-client.mjs');
  const links=Array.from({length:65},(_,i)=>'<link id="s'+i+'" rel="alternate" href="counted.css">').join('');
  const activate="for(let i=0;i<65;i++)document.getElementById('s'+i).setAttribute('rel','stylesheet');";
  let count,bytes;
  try{await prepareDocument(engine,links+'<script>'+activate+'</script>',{url:target+'/page'});}catch(error){count=error.message;}
  const oversized=Array.from({length:5},(_,i)=>'<link rel="stylesheet" href="/budget'+i+'.css">').join('');
  try{await prepareDocument(engine,oversized,{url:target+'/page'});}catch(error){bytes=error.message;}
  return {count,bytes};
 },target);
 assert.match(budgets.count,/resource count exceeds 64/);assert.match(budgets.bytes,/resources exceed 4 MiB/);assert(!requests.some(path=>path.endsWith('counted.css')));report.checks.push('script-activated resource count and aggregate fetched bytes keep their existing limits');
 assert.deepEqual(errors,[]);report.requests=requests;report.status='PASS';
}finally{await browser.close();fixture.closeAllConnections();await new Promise(resolve=>fixture.close(resolve));await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
