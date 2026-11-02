#!/usr/bin/env node
// Runs the real built public page, same-origin WASM, worker and WebGPU.
import assert from 'node:assert/strict';
import {mkdir,writeFile} from 'node:fs/promises';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
const [url,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-public.mjs PAGE_URL PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});const {chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true}),report={status:'RUNNING',page:url,checks:[],browser:await browser.version()};
try{
 const page=await browser.newPage({viewport:{width:1300,height:1000}}),errors=[],requests=[],logs=[];
 page.on('pageerror',e=>errors.push(e.message));page.on('request',r=>requests.push({url:r.url(),method:r.method()}));page.on('console',m=>{if(m.text().startsWith('Lean link click'))logs.push(m.text());});
 await page.goto(url);await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 const frame=await page.evaluate(()=>window.webRenderResult);assert(!frame.error,frame.error);assert(frame.artifact.primitiveCount>0);assert(frame.artifact.webRender.glyphRuns.length>0);assert(frame.artifact.webRender.links.length>0);
 const digest=()=>page.evaluate(async()=>Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',new Uint8Array(window.webRenderResult.rgba))),b=>b.toString(16).padStart(2,'0')).join(''));
 const initial=await digest();report.initial={width:frame.artifact.width,height:frame.artifact.height,primitives:frame.artifact.primitiveCount,glyphRuns:frame.artifact.webRender.glyphRuns.length,sha256:initial};report.checks.push('actual relative-path Lean WASM and WebGPU render from public page worker');
 const target=frame.artifact.webRender.links[0],p=await page.locator('#output').evaluate((c,r)=>{const b=c.getBoundingClientRect();return{x:b.left+c.clientLeft+(r[2]+r[4]/2)*c.clientWidth/c.width,y:b.top+c.clientTop+(r[3]+r[5]/2)*c.clientHeight/c.height};},target);
 await page.mouse.move(p.x,p.y);await page.waitForFunction(()=>document.querySelector('#output').style.cursor==='pointer');await page.mouse.click(p.x,p.y);await page.waitForFunction(()=>!document.querySelector('#events').hidden);
 const event=JSON.parse(await page.locator('#events').textContent());assert.equal(event.href,target[1]);assert.equal(event.sourceNode,target[0]);assert.equal(logs.length,1);assert.equal(page.url(),url);assert(!requests.some(r=>r.method==='POST'));report.checks.push('Lean worker picker gives hand cursor and logs source-mapped link without localhost or navigation');
 const original=await page.locator('#source').inputValue();await page.locator('#auto').uncheck();await page.locator('#source').fill(original.replace('#eaf0f5','#ffeedd'));await page.locator('#render').click();
 await page.waitForFunction(old=>window.webRenderResult?.artifact?.webRender&&document.querySelector('#status').textContent.includes('pixels')&&!document.querySelector('#render').disabled,initial,{timeout:90000});
 const changed=await digest();assert.notEqual(changed,initial);report.changedSha256=changed;report.checks.push('editable CSS changes actual public GPU image');
 await page.locator('#source').fill('<div style="font-family:Ahem">A</div>');await page.locator('#render').click();await page.waitForFunction(()=>window.webRenderResult?.error,{},{timeout:90000});assert.match(await page.locator('#status').textContent(),/unsupported font family/);assert(await page.locator('#output').isHidden());report.checks.push('unsupported font scope is explicit and removes stale output');
 await page.locator('#source').fill(original);await page.locator('#render').click();await page.waitForFunction(()=>window.webRenderResult?.artifact&&!document.querySelector('#render').disabled,{},{timeout:90000});
 await page.screenshot({path:resolve(outDir,'desktop.png'),fullPage:true});await page.setViewportSize({width:390,height:1050});await page.screenshot({path:resolve(outDir,'mobile.png'),fullPage:true});assert(await page.evaluate(()=>document.documentElement.scrollWidth<=innerWidth+1));report.checks.push('mobile layout fits viewport and recovers after refusal');
 const base=new URL(url),outside=requests.filter(r=>!r.url.startsWith(base.origin)&&!r.url.startsWith('data:')&&!r.url.startsWith('blob:'));assert.deepEqual(outside,[]);assert(requests.some(r=>r.url.endsWith('/runtime/web-render.wasm')));assert(requests.some(r=>r.url.endsWith('/runtime/render-plan.wasm')));assert.deepEqual(errors,[]);report.checks.push('runtime assets stay same origin under the Pages path prefix');
 report.requests=requests;report.click=event;report.console=logs;report.status='PASS';
}finally{await browser.close();await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
