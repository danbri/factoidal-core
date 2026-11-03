#!/usr/bin/env node
// Stop and failed provisional navigation preserve the committed Lean scene,
// editor state and actual QuickJS counter VM. No host HTML/CSS parsing here.
import assert from 'node:assert/strict';
import {once} from 'node:events';
import {mkdir,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {makeNavigationFixture} from './navigation-fixture.mjs';
const [origin,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-navigation-restoration-browser.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});
const fixture=makeNavigationFixture();
fixture.pages['/bad-layout']="<!doctype html><style>body{font-family:Arial}</style><p id=message>Bad candidate</p><p style='display:grid'>Refuse this layout</p><script>document.getElementById('message').textContent='Candidate VM started';</script>";
fixture.server.listen(0,'127.0.0.1');await once(fixture.server,'listening');
const target=`http://127.0.0.1:${fixture.server.address().port}`,{chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true,args:['--enable-unsafe-webgpu']}),report={status:'RUNNING',checks:[]};
let heldRoute;
try{
 const page=await browser.newPage({viewport:{width:1440,height:1050}}),errors=[];page.on('pageerror',error=>errors.push(error.message));
 await page.goto(origin+'?url='+encodeURIComponent(target+'/dynamic'));
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text==='Loaded'),{},{timeout:90000});
 async function clickCounter(){
  const link=await page.evaluate(()=>window.webRenderResult.artifact.webRender.links.find(row=>row[1]==='#changed'));assert(link);
  const point=await page.locator('#output').evaluate((canvas,row)=>{const rect=canvas.getBoundingClientRect();return{x:rect.left+(row[2]+row[4]/2)*canvas.clientWidth/canvas.width,y:rect.top+(row[3]+row[5]/2)*canvas.clientHeight/canvas.height};},link);
  await page.mouse.click(point.x,point.y);
 }
 async function count(value){await page.waitForFunction(value=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text===String(value)),value,{timeout:90000});}
 async function snapshot(){return page.evaluate(async()=>{
  const canvas=document.querySelector('#output'),bytes=canvas.getContext('2d').getImageData(0,0,canvas.width,canvas.height).data;
  const digest=await crypto.subtle.digest('SHA-256',bytes);
  return{url:window.webBrowser.currentURL,label:document.querySelector('#current-url').textContent,source:document.querySelector('#source').value,
   width:document.querySelector('#width').value,height:document.querySelector('#height').value,canvasWidth:canvas.width,canvasHeight:canvas.height,
   hidden:canvas.hidden,pixelsSha256:Array.from(new Uint8Array(digest),n=>n.toString(16).padStart(2,'0')).join('')};
 });}
 async function stop(){await page.locator('#stop').click();await page.waitForFunction(()=>!window.webBrowserState.loading&&window.webBrowserState.cancelled);}
 await clickCounter();await count(1);const first=await snapshot();
 await page.evaluate(target=>{document.querySelector('#width').value='480';document.querySelector('#height').value='320';window.webBrowser.navigation.go(target+'/slow');},target);
 await page.waitForFunction(()=>window.webBrowserState.loading);await stop();assert.deepEqual(await snapshot(),first,'Stop during source fetch changed committed scene/editor/viewport');
 await clickCounter();await count(2);report.checks.push('Stop during fetch restores source, URL, viewport and exact pixels; committed counter VM continues 1→2');
 const second=await snapshot();
 assert.equal(await page.evaluate(url=>window.webBrowser.navigation.go(url),target+'/missing'),false);
 assert.match(await page.locator('#status').textContent(),/404/);assert.deepEqual(await snapshot(),second,'HTTP failure changed committed scene/editor/viewport');
 await clickCounter();await count(3);report.checks.push('failed HTTP navigation retains exact frame and counter VM continues 2→3');
 const third=await snapshot();
 assert.equal(await page.evaluate(url=>window.webBrowser.navigation.go(url),target+'/bad-layout'),false);
 assert.match(await page.locator('#status').textContent(),/grid|display|unsupported/i);assert.deepEqual(await snapshot(),third,'failed candidate compilation changed committed document');
 await clickCounter();await count(4);report.checks.push('candidate VM starts but unsupported layout discards it; committed counter VM continues 3→4');
 const fourth=await snapshot();let holdNext=true,signalHeld;const paused=new Promise(resolve=>{signalHeld=resolve;});
 await page.route('**/font-data',route=>{if(holdNext){holdNext=false;heldRoute=route;signalHeld();return;}return route.continue();});
 await page.evaluate(target=>{document.querySelector('#width').value='500';document.querySelector('#height').value='350';window.webBrowser.navigation.go(target+'/dynamic?candidate=1');},target);
 let pauseTimer;await Promise.race([paused,new Promise((_,reject)=>{pauseTimer=setTimeout(()=>reject(Error('candidate did not reach font-data stage')),30000);})]).finally(()=>clearTimeout(pauseTimer));
 await stop();await heldRoute.abort().catch(()=>{});heldRoute=undefined;
 assert.deepEqual(await snapshot(),fourth,'Stop after candidate VM/font preflight changed committed document');
 await clickCounter();await count(5);report.checks.push('Stop after candidate VM/font preflight restores exact frame and counter VM continues 4→5');
 assert.equal(await page.evaluate(url=>window.webBrowser.navigation.go(url),target+'/dynamic?fresh=1'),true);
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text==='Loaded'));
 await clickCounter();await count(1);assert.equal(await page.locator('#current-url').textContent(),target+'/dynamic?fresh=1');
 report.checks.push('successful GPU commit replaces document and starts a fresh counter VM');
 const validEditor=await page.locator('#source').inputValue(),invalidEditor='<div style="display:grid">Invalid edited source</div>';
 await page.locator('#source').fill(invalidEditor);
 await page.waitForFunction(()=>typeof window.webRenderResult?.error==='string');
 assert.equal(await page.locator('#source').inputValue(),invalidEditor,'invalid edit was replaced by old source');
 assert(await page.locator('#output').isHidden(),'invalid edit retained a stale visible canvas');
 assert.equal(await page.evaluate(()=>window.webRenderResult.artifact),undefined,'invalid edit retained a stale public artifact');
 await page.locator('#source').fill(validEditor);await count(1);assert(!(await page.locator('#output').isHidden()));
 await clickCounter();await count(2);
 report.checks.push('malformed edit retains new source, clears stale canvas/artifact, and recovers to a working document');
 let pauseEdit=true,signalEdit;const editingPaused=new Promise(resolve=>{signalEdit=resolve;});
 await page.route('**/font-data',route=>{if(pauseEdit){pauseEdit=false;heldRoute=route;signalEdit();return;}return route.continue();});
 const firstEdit='<style>body{font-family:Arial;font-size:20px}</style><p>FirstRace</p>',latestEdit=firstEdit.replace('FirstRace','LatestRace');
 await page.locator('#source').fill(firstEdit);
 let editTimer;await Promise.race([editingPaused,new Promise((_,reject)=>{editTimer=setTimeout(()=>reject(Error('edit did not reach font-data stage')),30000);})]).finally(()=>clearTimeout(editTimer));
 await page.locator('#source').fill(latestEdit);await heldRoute.continue().catch(()=>{});heldRoute=undefined;
 await page.waitForTimeout(100);
 assert.equal(await page.locator('#source').inputValue(),latestEdit,'an older render overwrote newer input before debounce');
 assert(!await page.evaluate(()=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text==='FirstRace')),'old edit committed after new input');
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.webRender.glyphRuns.some(run=>run.text==='LatestRace'));
 assert.equal(await page.locator('#source').inputValue(),latestEdit);
 report.checks.push('new input immediately aborts held font work; old render cannot overwrite editor or commit before debounce');

 assert.deepEqual(errors,[]);report.fixtureRequests=fixture.requests;report.final=await snapshot();
 await page.screenshot({path:resolve(outDir,'navigation-restoration.png'),fullPage:true});report.status='PASS';
}catch(error){report.failure=String(error);throw error;}finally{
 await heldRoute?.abort().catch(()=>{});await browser.close();fixture.server.closeAllConnections();await new Promise(resolve=>fixture.server.close(resolve));
 await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');
}
console.log(JSON.stringify(report,null,2));
