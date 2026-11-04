// Actual Lean parser/DOM/layout/scene, native CPU and browser GPU integration.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {resolve,dirname} from 'node:path';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
const [origin,playwrightPath,chrome,nativePath,out]=process.argv.slice(2);
if(!out)throw Error('usage: check-rdf.mjs ORIGIN PLAYWRIGHT CHROME NATIVE_CLI NEW_OUT');
await mkdir(out,{recursive:false});
const hash=x=>createHash('sha256').update(x).digest('hex');
const here=dirname(fileURLToPath(import.meta.url)),source=await readFile(resolve(here,'fixtures/graph.nt'),'utf8');
const {chromium}=await import(pathToFileURL(playwrightPath));const browser=await chromium.launch({executablePath:chrome,headless:true});
const report={status:'RUNNING',scope:'Actual N-Triples reader to linked DOM and Lean scene; source fixture is local, not a WPT score',checks:[]};
try{
 const page=await browser.newPage({viewport:{width:1300,height:1050}}),errors=[],logs=[],posts=[];
 page.on('pageerror',e=>errors.push(e.message));page.on('console',m=>{if(m.text().startsWith('Lean link click'))logs.push(m.text());});page.on('request',r=>{if(r.url()===origin+'events'&&r.method()==='POST')posts.push(JSON.parse(r.postData()));});
 await page.goto(origin);await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 await page.locator('#syntax').selectOption('ntriples');await page.locator('#example').click();
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.rdf?.triples===3,{},{timeout:90000});
 let frame=await page.evaluate(()=>window.webRenderResult);assert(!frame.error,frame.error);
 assert.equal(frame.artifact.rdf.syntax,'N-Triples 1.1');assert(frame.artifact.webRender.glyphRuns.some(r=>r.text.includes('Alice')));
 report.checks.push('strict Lean N-Triples fixture renders three triples and literal glyphs through DOM/CSS/layout');
 assert(frame.rgba.some((v,i)=>i%4===0&&v===0&&frame.rgba[i+1]===0&&frame.rgba[i+2]===255),'RDF links have no actual blue pixels');
 await page.screenshot({path:resolve(out,'rdf-graph.png'),fullPage:true});
 const link=frame.artifact.webRender.links.find(r=>r[1]==='https://e.test/alice'&&r[2]+r[4]/2<380&&r[3]+r[5]/2<340);assert(link);
 const point=await page.locator('#output').evaluate((c,r)=>{const b=c.getBoundingClientRect();return{x:b.left+c.clientLeft+(r[2]+r[4]/2)*c.clientWidth/c.width,y:b.top+c.clientTop+(r[3]+r[5]/2)*c.clientHeight/c.height};},link);
 await page.mouse.move(point.x,point.y);await page.waitForFunction(()=>document.querySelector('#output').style.cursor==='pointer');
 const logged=page.waitForResponse(r=>r.url()===origin+'events'&&r.request().method()==='POST');await page.mouse.click(point.x,point.y);assert.equal((await logged).status(),200);assert.equal(posts.at(-1).href,link[1]);assert.equal(logs.length,1);assert.equal(page.url(),origin);
 report.checks.push('RDF IRI is a blue linked DOM anchor; actual Lean picker logs original full IRI without navigating');
 const fixture=resolve(out,'graph.nt');await writeFile(fixture,source);
 function native(path,w,h,pixels=false){const run=spawnSync(nativePath,[path,String(w),String(h),'--rdf',...(pixels?['--pixels']:[])],{encoding:'utf8',maxBuffer:16*1024*1024});assert.equal(run.status,0,run.stderr);return JSON.parse(run.stdout);}
 assert.deepEqual(native(fixture,380,340),frame.artifact);report.checks.push('actual macOS native CLI and browser WASM emit identical complete RDF scene artifacts');
 const before=hash(Buffer.from(frame.rgba));await page.locator('#source').fill(source.replace('Alice','Alicia'));
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.webRender?.glyphRuns.some(r=>r.text.includes('Alicia')),{},{timeout:90000});
 frame=await page.evaluate(()=>window.webRenderResult);assert.notEqual(hash(Buffer.from(frame.rgba)),before);report.checks.push('literal edit changes actual GPU pixels');
 await page.locator('#source').fill(source+'malformed');await page.waitForFunction(()=>window.webRenderResult?.error?.includes('N-Triples error'),{},{timeout:90000});assert(await page.locator('#output').isHidden());report.checks.push('malformed suffix rejects entire graph and clears stale canvas');
 const small='<urn:s> <urn:p> "Hi" .',smallFile=resolve(out,'small.nt');await writeFile(smallFile,small);
 await page.locator('#width').fill('128');await page.locator('#height').fill('96');await page.locator('#source').fill(small);
 await page.waitForFunction(()=>window.webRenderResult?.artifact?.rdf?.triples===1&&window.webRenderResult.artifact.width===128,{},{timeout:90000});
 frame=await page.evaluate(()=>window.webRenderResult);const cpu=native(smallFile,128,96,true);assert.equal(cpu.pixels.length,128*96*3);
 let differing=0,max=0,nonwhite=0;for(let i=0;i<128*96;i++){let different=false;for(let c=0;c<3;c++){const delta=Math.abs(cpu.pixels[i*3+c]-frame.rgba[i*4+c]);different ||=delta!==0;max=Math.max(max,delta);}differing+=Number(different);nonwhite+=Number(frame.rgba[i*4]<250);}assert.equal(differing,0);assert(nonwhite>100,'RDF scene was blank');
 report.image={width:128,height:96,pixels:128*96,differingPixels:differing,maxChannelDifference:max,rgbaSha256:hash(Buffer.from(frame.rgba))};report.checks.push('entire native CPU and browser GPU RDF text image agrees exactly and contains visible glyphs');
 assert.deepEqual(errors,[]);await page.screenshot({path:resolve(out,'rdf.png'),fullPage:true});report.events=posts;report.nativeSha256=hash(await readFile(nativePath));report.provenance=await(await page.request.get(origin+'provenance.json')).json();report.status='PASS';
}finally{await browser.close();await writeFile(resolve(out,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
