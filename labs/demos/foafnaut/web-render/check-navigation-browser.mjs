#!/usr/bin/env node
// Real fixture HTTP server -> native broker -> unchanged source -> Lean WASM ->
// WebGPU -> Lean link picker -> actual network navigation.
import assert from 'node:assert/strict';
import {once} from 'node:events';
import {mkdir,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {makeNavigationFixture} from './navigation-fixture.mjs';
const [origin,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-navigation-browser.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});
const fixture=makeNavigationFixture();fixture.server.listen(0,'127.0.0.1');await once(fixture.server,'listening');
const target=`http://127.0.0.1:${fixture.server.address().port}`,{chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true,args:['--enable-unsafe-webgpu']}),report={status:'RUNNING',checks:[]};
try{
 const page=await browser.newPage({viewport:{width:1440,height:1050}}),errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto(origin);await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 assert(!await page.evaluate(()=>window.webRenderResult.error));
 async function url(expected){await page.waitForFunction(expected=>window.webBrowserState?.url===expected&&!window.webBrowserState.loading,expected,{timeout:90000});assert.equal(await page.locator('#current-url').textContent(),expected);assert(!await page.evaluate(()=>window.webRenderResult.error));}
 async function go(path){await page.locator('#address').fill(target+path);await page.locator('#go').click();}
 await go('/one');await url(target+'/one');assert.equal(await page.locator('#source').inputValue(),fixture.pages['/one']);
 assert(await page.evaluate(()=>window.webRenderResult.artifact.webRender.links.length>0));
 const first=await page.evaluate(()=>window.webRenderResult.artifact.webRender.links[0]);
 const point=await page.locator('#output').evaluate((c,r)=>{const rect=c.getBoundingClientRect();return{x:rect.left+(r[2]+r[4]/2)*c.clientWidth/c.width,y:rect.top+(r[3]+r[5]/2)*c.clientHeight/c.height};},first);
 const eventPost=page.waitForResponse(r=>r.url()===origin+'events'&&r.request().method()==='POST');
 await page.mouse.click(point.x,point.y);assert.equal((await eventPost).status(),200);await url(target+'/two?from=one');
 assert.equal(await page.locator('#source').inputValue(),fixture.pages['/two']);report.checks.push('address Go fetches exact original HTML and Lean-picked relative link navigates');
 await page.locator('#back').click();await url(target+'/one');await page.locator('#forward').click();await url(target+'/two?from=one');
 const before=fixture.requests.length;await page.locator('#reload').click();await page.waitForFunction(()=>window.webBrowserState?.loading===false);await page.waitForTimeout(50);assert(fixture.requests.length>before);report.checks.push('Back, Forward and Reload use actual HTTP loads');
 await go('/redirect');await url(target+'/two?redirected=1');report.checks.push('redirect commits final network URL');
 await go('/missing');await page.waitForFunction(()=>/404/.test(document.querySelector('#status').textContent));assert.equal(await page.locator('#current-url').textContent(),target+'/two?redirected=1');report.checks.push('HTTP error visible and history keeps last successful URL');
 await page.evaluate(target=>{window.webBrowser.navigation.go(target+'/slow');window.webBrowser.navigation.go(target+'/one');},target);await url(target+'/one');await page.waitForTimeout(300);assert.equal(await page.locator('#source').inputValue(),fixture.pages['/one']);
 await page.evaluate(target=>{window.webBrowser.navigation.go(target+'/slow');window.webBrowser.navigation.cancel();},target);await page.waitForTimeout(300);assert.equal(await page.locator('#current-url').textContent(),target+'/one');report.checks.push('cancelled and stale loads cannot replace source, scene or committed URL');
 assert.deepEqual(errors,[]);report.fixtureRequests=fixture.requests;report.currentState=await page.evaluate(()=>window.webBrowserState);await page.screenshot({path:resolve(outDir,'browser-navigation.png'),fullPage:true});report.status='PASS';
}finally{await browser.close();fixture.server.closeAllConnections();await new Promise(resolve=>fixture.server.close(resolve));await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
