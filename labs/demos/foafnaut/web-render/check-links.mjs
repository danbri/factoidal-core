#!/usr/bin/env node
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {dirname,resolve} from 'node:path';
const [origin,playwrightPath,browserPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-links.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIR');
await mkdir(outDir,{recursive:true});const here=dirname(fileURLToPath(import.meta.url)),{chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true}),report={status:'RUNNING',checks:[],events:[]};
try{
 const page=await browser.newPage({viewport:{width:1300,height:1050}}),errors=[],consoleLogs=[],posts=[];
 page.on('pageerror',e=>errors.push(e.message));page.on('console',m=>{if(m.text().startsWith('Lean link click'))consoleLogs.push(m.text());});page.on('request',r=>{if(r.url()===origin+'events'&&r.method()==='POST')posts.push(JSON.parse(r.postData()));});
 await page.goto(origin);await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 assert(!await page.evaluate(()=>window.webRenderResult.error));
 await page.locator('#source').fill(await readFile(resolve(here,'fixtures/links.html'),'utf8'));
 await page.locator('#width').fill('120');await page.locator('#height').fill('160');
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.width===120&&window.webRenderResult.artifact.webRender.links.some(r=>r[1].includes('/first?')),{},{timeout:90000});
 const frame=await page.evaluate(()=>window.webRenderResult);assert(!frame.error,frame.error);
 const links=frame.artifact.webRender.links,first=links.filter(r=>r[1].startsWith('https://example.test/first'));
 assert(first.some(r=>r[3]===0)&&first.some(r=>r[3]===20),'wrapped link has both line regions');
 async function canvasPoint(x,y){return page.locator('#output').evaluate((c,{x,y})=>{const r=c.getBoundingClientRect();return{x:r.left+c.clientLeft+x*c.clientWidth/c.width,y:r.top+c.clientTop+y*c.clientHeight/c.height};},{x,y});}
 async function clickAt(x,y,href){const point=await canvasPoint(x,y);await page.mouse.move(point.x,point.y);await page.waitForFunction(()=>document.querySelector('#output').style.cursor==='pointer');const response=page.waitForResponse(r=>r.url()===origin+'events'&&r.request().method()==='POST');await page.mouse.click(point.x,point.y);assert.equal((await response).status(),200);assert.equal(posts.at(-1).href,href);}
 await clickAt(6,10,'https://example.test/first?x=1&y=2');
 await clickAt(6,30,'https://example.test/first?x=1&y=2');
 await clickAt(28,10,'https://example.test/first?x=1&y=2');
 assert.equal(posts[0].sourceNode,posts[1].sourceNode);assert.equal(posts[0].sourceNode,posts[2].sourceNode);report.checks.push('wrapped link and retained collapsed space pick the same Lean DOM anchor');
 const run=word=>frame.artifact.webRender.glyphRuns.find(r=>r.text===word);
 const pixel=(x,y)=>frame.rgba.slice((y*frame.artifact.width+x)*4,(y*frame.artifact.width+x)*4+3);
 const aa=run('AA'),red=run('Red'),plain=run('Plain');assert(aa&&red&&plain);
 assert.deepEqual(pixel(Math.floor(aa.glyphs[0][1]+5),Math.floor(aa.glyphs[0][2]+15)),[0,0,255]);
 assert.deepEqual(pixel(Math.floor(red.glyphs[0][1]+5),Math.floor(red.glyphs[0][2]+15)),[255,0,0]);
 assert.deepEqual(pixel(Math.floor(plain.glyphs[0][1]+5),Math.floor(plain.glyphs[0][2]+15)),[255,255,255]);report.checks.push('actual blue underline, author red override, non-href anchor has no underline');
 const point=await canvasPoint(plain.glyphs[0][1]+5,plain.glyphs[0][2]+5),before=posts.length;await page.mouse.move(point.x,point.y);await page.waitForFunction(()=>document.querySelector('#output').style.cursor==='default');await page.mouse.click(point.x,point.y);assert.equal(posts.length,before);report.checks.push('non-href anchor has default cursor and emits no click');
 const icon=links.find(r=>r[1]==='https://example.test/icon');assert(icon);assert.deepEqual(pixel(Math.floor(icon[2]+icon[4]/2),Math.floor(icon[3]+icon[5]/2)),[255,0,0]);await clickAt(icon[2]+icon[4]/2,icon[3]+icon[5]/2,icon[1]);report.checks.push('HTML anchor CSS currentColor reaches affine-mapped embedded SVG and picks source anchor');
 assert.equal(consoleLogs.length,4);assert.equal(posts.length,4);assert(errors.length===0,errors.join('\n'));assert.equal(page.url(),origin);report.checks.push('clicks log bounded URLs/source nodes in browser console and server endpoint without navigation');
 const invalidOrigin=await page.request.post(origin+'events',{headers:{Origin:'https://example.invalid','Content-Type':'application/json'},data:{type:'link-click',sourceNode:1,href:'x',x:1,y:1}});assert.equal(invalidOrigin.status(),403);
 const malformed=await page.request.post(origin+'events',{headers:{Origin:origin.replace(/\/$/,''),'Content-Type':'application/json'},data:null});assert.equal(malformed.status(),400);report.checks.push('event transport rejects foreign origin and malformed event');
 await page.screenshot({path:resolve(outDir,'links.png'),fullPage:true});report.events=posts;report.console=consoleLogs;report.regions=links;report.status='PASS';
}finally{await browser.close();await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
