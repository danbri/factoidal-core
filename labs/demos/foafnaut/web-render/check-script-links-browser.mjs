#!/usr/bin/env node
// Actual QuickJS cancellation and Lean-rendered anchor default actions.
import assert from 'node:assert/strict';
import {once} from 'node:events';
import {mkdir,writeFile} from 'node:fs/promises';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {makeNavigationFixture} from './navigation-fixture.mjs';
const [origin,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-script-links-browser.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});
const fixture=makeNavigationFixture();
fixture.pages['/script-links']=`<!doctype html><p id="message">Ready</p><a id="stay" href="/missing">Stay here</a><br><a id="go" href="/missing">Go onward</a><script>
document.getElementById('stay').addEventListener('click',function(event){event.preventDefault();document.getElementById('message').textContent='Stayed';});
document.getElementById('go').addEventListener('click',function(){this.setAttribute('href','/two');document.getElementById('message').textContent='Going';});
</script>`;
fixture.server.listen(0,'127.0.0.1');await once(fixture.server,'listening');
const target=`http://127.0.0.1:${fixture.server.address().port}`,{chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true,args:['--enable-unsafe-webgpu']});
const report={status:'RUNNING',checks:[]};
try{
 const page=await browser.newPage({viewport:{width:1300,height:1000}}),errors=[];page.on('pageerror',e=>errors.push(e.message));
 await page.goto(origin+'?url='+encodeURIComponent(target+'/script-links'));
 await page.waitForFunction(()=>window.webRenderResult?.artifact&&!window.webBrowserState.loading,{},{timeout:90000});
 async function click(index){
  // One anchor can emit separate word and space hit regions. Select an
  // actual Lean anchor handle, rather than indexing those fragment rows.
  const link=await page.evaluate(index=>{const rows=window.webRenderResult.artifact.webRender.links,ids=[...new Set(rows.map(row=>row[0]))];return rows.find(row=>row[0]===ids[index]);},index);assert(link);
  const p=await page.locator('#output').evaluate((canvas,row)=>{const r=canvas.getBoundingClientRect();return{x:r.left+(row[2]+row[4]/2)*canvas.clientWidth/canvas.width,y:r.top+(row[3]+row[5]/2)*canvas.clientHeight/canvas.height};},link);
  await page.mouse.click(p.x,p.y);
 }
 await click(0);
 await page.waitForFunction(()=>document.querySelector('#events').textContent.includes('"defaultPrevented": true'),{},{timeout:90000});
 assert.equal(await page.evaluate(()=>window.webBrowser.currentURL),target+'/script-links');
 assert(await page.evaluate(()=>window.webRenderResult.artifact.webRender.glyphRuns.some(run=>run.text==='Stayed')));
 assert(!fixture.requests.some(url=>url.startsWith('/missing')));
 report.checks.push('preventDefault preserves the page while the Lean DOM change reaches GPU output');
 await click(1);
 await page.waitForFunction(()=>window.webBrowserState.url?.endsWith('/two')&&!window.webBrowserState.loading,{},{timeout:90000});
 assert.equal(await page.evaluate(()=>window.webBrowser.currentURL),target+'/two');
 assert(!fixture.requests.some(url=>url.startsWith('/missing')),'default action used stale pre-listener href');
 assert(await page.evaluate(()=>document.querySelector('#events').textContent.includes('"defaultPrevented": false')));
 report.checks.push('uncancelled listener follows the updated href from the newly rendered Lean anchor');
 assert.deepEqual(errors,[]);report.requests=fixture.requests;report.status='PASS';
 await page.screenshot({path:resolve(outDir,'script-link-navigation.png'),fullPage:true});
}catch(error){report.status='FAIL';report.failure=String(error);throw error;}finally{await browser.close();fixture.server.closeAllConnections();await new Promise(resolve=>fixture.server.close(resolve));await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
