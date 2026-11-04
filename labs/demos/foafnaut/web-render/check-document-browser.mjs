#!/usr/bin/env node
// End-to-end source-byte, external CSS/JS, QuickJS DOM commands, HB/FT font
// requests, Lean WASM layout, WebGPU pixels and actual click path.
import assert from 'node:assert/strict';
import {once} from 'node:events';
import {mkdir,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {makeNavigationFixture} from './navigation-fixture.mjs';
const [origin,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-document-browser.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});const fixture=makeNavigationFixture();fixture.server.listen(0,'127.0.0.1');await once(fixture.server,'listening');
const target=`http://127.0.0.1:${fixture.server.address().port}`,{chromium}=await import(pathToFileURL(playwrightPath)),browser=await chromium.launch({executablePath:browserPath,headless:true,args:['--enable-unsafe-webgpu']}),report={status:'RUNNING',checks:[]};
try{
 const page=await browser.newPage({viewport:{width:1440,height:1050}}),errors=[],fontRequests=[];
 page.on('pageerror',error=>errors.push(error.message));page.on('request',request=>{if(request.url()===origin+'font-data')fontRequests.push(request.postDataJSON());});
 await page.goto(origin+'?url='+encodeURIComponent(target+'/dynamic'));
 await page.waitForFunction(()=>window.webBrowserState?.committed||window.webRenderResult?.error,{},{timeout:90000});
 assert(!await page.evaluate(()=>window.webRenderResult.error),await page.locator('#status').textContent());
 assert.equal(await page.locator('#source').inputValue(),fixture.pages['/dynamic']);
 let frame=await page.evaluate(()=>window.webRenderResult);assert(frame.artifact.webRender.fontResource?.fontSha256);assert(frame.artifact.webRender.glyphRuns.some(run=>run.text==='Loaded'));
 assert(fixture.requests.includes('/dynamic.css'));assert(fixture.requests.includes('/dynamic.js'));assert(!fixture.requests.includes('/nested/dynamic.css'));report.checks.push('Lean base URL resolves external CSS and JS; unchanged source renders real shaped Loaded text');
 async function clickChange(){
  const link=await page.evaluate(()=>window.webRenderResult.artifact.webRender.links.find(link=>link[1].endsWith('#changed')));assert(link);
  const point=await page.locator('#output').evaluate((canvas,link)=>{const rect=canvas.getBoundingClientRect();return{x:rect.left+(link[2]+link[4]/2)*canvas.clientWidth/canvas.width,y:rect.top+(link[3]+link[5]/2)*canvas.clientHeight/canvas.height};},link);
  await page.mouse.click(point.x,point.y);
 }
 async function count(value){await page.waitForFunction(value=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text===String(value)),value,{timeout:90000});}
 const before=frame.rgba;await clickChange();await count(1);frame=await page.evaluate(()=>window.webRenderResult);assert.notDeepEqual(frame.rgba,before);assert.equal(await page.locator('#current-url').textContent(),target+'/dynamic');
 assert(fontRequests.some(request=>request.requests.some(item=>item.text==='Count')));assert(fontRequests.some(request=>request.requests.some(item=>item.text==='1')));report.checks.push('actual Lean-picked click runs QuickJS, applies commands in Lean, shapes changed words and changes GPU pixels');
 await page.locator('#width').fill('700');await page.waitForFunction(()=>window.webRenderResult?.artifact?.width===700,{},{timeout:90000});await clickChange();await count(2);report.checks.push('viewport reflow preserves the script VM and command history');
 const edited=fixture.pages['/dynamic'].replace('Before','Original');await page.locator('#source').fill(edited);await page.waitForFunction(()=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text==='Loaded'),{},{timeout:90000});await clickChange();await count(1);report.checks.push('editing source creates a fresh script document and resets its VM');
 assert.deepEqual(errors,[]);report.fontRequestCount=fontRequests.length;report.fixtureRequests=fixture.requests;report.fontResource=frame.artifact.webRender.fontResource;await page.screenshot({path:resolve(outDir,'document-browser.png'),fullPage:true});report.status='PASS';
}finally{await browser.close();fixture.server.closeAllConnections();await new Promise(resolve=>fixture.server.close(resolve));await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
