#!/usr/bin/env node
// Optional local integration check: uses an already installed Chrome/Playwright.
import assert from 'node:assert/strict';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {readFile,writeFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
const args=process.argv.slice(2),reportIndex=args.indexOf('--report'),reportPath=reportIndex<0?null:args[reportIndex+1],requireTree=args.includes('--require-tree');
if(reportIndex>=0&&!reportPath)throw Error('--report requires a path');
const positional=args.filter((a,i)=>a!=='--require-tree'&&(reportIndex<0||(i!==reportIndex&&i!==reportIndex+1)));
const [origin,playwrightPath,browserPath,screenshot]=positional;
if(!origin||!playwrightPath||!browserPath)throw Error('Usage: node smoke.mjs URL /absolute/playwright-core/index.mjs /absolute/chrome [screenshot.png]');
const digest=bytes=>createHash('sha256').update(bytes).digest('hex');
const harness={capturedAt:new Date().toISOString(),node:process.version,argv:process.argv.slice(2),sha256:digest(await readFile(fileURLToPath(import.meta.url))),browserExecutableSha256:digest(await readFile(browserPath))};
const {chromium}=await import(pathToFileURL(playwrightPath).href);
const browser=await chromium.launch({executablePath:browserPath,headless:true});
try{
 const page=await browser.newPage({viewport:{width:1360,height:1050}}),errors=[],loadedAssets=[];
 page.on('pageerror',e=>errors.push(e.message));
 page.on('response',response=>{if(response.url().startsWith(origin)&&!response.url().endsWith('provenance.json'))loadedAssets.push(response.body().then(bytes=>({url:response.url(),bytes:bytes.length,sha256:createHash('sha256').update(bytes).digest('hex')})).catch(error=>({url:response.url(),error:String(error)})));});
 await page.addInitScript(()=>{window.__previewBlobs=new Map();const create=URL.createObjectURL.bind(URL);URL.createObjectURL=blob=>{const url=create(blob);window.__previewBlobs.set(url,blob);return url;};});
 await page.route('**/*',r=>r.request().url().startsWith(origin)?r.continue():r.abort());
 await page.goto(origin);
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with')||document.querySelector('#status')?.dataset.error==='true',{},{timeout:90000});
 assert.match(await page.locator('#status').innerText(),/^Rendered with/);
 assert.equal(await page.locator('#download').isEnabled(),true);
 let evidence=JSON.parse(await page.locator('#evidence').textContent());assert(evidence.primitives>0);assert(evidence.checks>0);assert.equal(evidence.stats.frames,1);
 const firstFrame=evidence;
 const initial=await page.locator('#source').inputValue();
 await page.locator('#platform').evaluate(img=>img.decode());
 assert.equal(await page.locator('#platform').evaluate(img=>window.__previewBlobs.get(img.src).text()),initial);
 assert.equal(await page.locator('#submitted-code').textContent(),await page.locator('#shader').textContent());
 const treeText=await page.locator('#scene-tree').textContent();let tree={status:'unavailable',reason:treeText};
 if(treeText.trim().startsWith('[')){
  const nodes=JSON.parse(treeText),groups=[],paints=[];
  const walk=nodes=>{for(const node of nodes){if(node.kind==='group'){groups.push({id:node.id,transform:node.transform});walk(node.children);}else paints.push(node.geometry);}};walk(nodes);
  for(const id of ['browser-shell','page-content','interaction-overlay'])assert(groups.some(g=>g.id===id),'Missing retained group '+id);
  assert.equal(paints.length,evidence.primitives);assert(groups.every(g=>g.transform.length===6&&g.transform.every(Number.isFinite)));
  tree={status:'pass',groups,paintNodes:paints.length};
 }
 if(requireTree)assert.equal(tree.status,'pass','--require-tree needs the rebuilt Lean SVG engine');
 // Full-image diagnostic of the actual two UI backends. This does not set a
 // local tolerance or turn the gallery into a WPT conformance result.
 const imageMetrics=await page.evaluate(async()=>{
  const gpu=document.querySelector('#canvas'),img=document.querySelector('#platform');await img.decode();
  const oracle=new OffscreenCanvas(gpu.width,gpu.height),ctx=oracle.getContext('2d');ctx.fillStyle='white';ctx.fillRect(0,0,gpu.width,gpu.height);ctx.drawImage(img,0,0);
  const a=gpu.getContext('2d').getImageData(0,0,gpu.width,gpu.height).data,b=ctx.getImageData(0,0,gpu.width,gpu.height).data;let maximum=0,different=0,edgeAdjacent=0;const bounds={minX:gpu.width,minY:gpu.height,maxX:-1,maxY:-1};
  for(let p=0;p<a.length;p+=4){let changed=false;for(let c=0;c<3;c++){const d=Math.abs(a[p+c]-b[p+c]);maximum=Math.max(maximum,d);changed||=d!==0;}
   if(changed){different++;const x=(p/4)%gpu.width,y=Math.floor(p/4/gpu.width);bounds.minX=Math.min(bounds.minX,x);bounds.maxX=Math.max(bounds.maxX,x);bounds.minY=Math.min(bounds.minY,y);bounds.maxY=Math.max(bounds.maxY,y);let edge=false;
    for(let dy=-1;dy<=1;dy++)for(let dx=-1;dx<=1;dx++){if(x+dx<0||x+dx>=gpu.width||y+dy<0||y+dy>=gpu.height)continue;const q=((y+dy)*gpu.width+x+dx)*4;for(let c=0;c<3;c++)edge||=b[p+c]!==b[q+c];}edgeAdjacent+=edge;
   }
  }
  const digest=async bytes=>[...new Uint8Array(await crypto.subtle.digest('SHA-256',bytes))].map(b=>b.toString(16).padStart(2,'0')).join('');
  const box=element=>{const r=element.getBoundingClientRect();return {x:r.x,y:r.y,width:r.width,height:r.height};};
  return {width:gpu.width,height:gpu.height,totalPixels:gpu.width*gpu.height,maxChannelDifference:maximum,differentPixels:different,differenceBounds:different?bounds:null,browserEdgeAdjacentDifferentPixels:edgeAdjacent,flatBrowserRegionDifferentPixels:different-edgeAdjacent,gpuRgbaSha256:await digest(a),browserRgbaSha256:await digest(b),placement:{gpu:box(gpu),platform:box(img),platformNaturalSize:{width:img.naturalWidth,height:img.naturalHeight},wraps:[...document.querySelectorAll('.outputs .canvas-wrap')].map(box)}};
 });
 assert(Math.abs(imageMetrics.placement.wraps[0].y-imageMetrics.placement.wraps[1].y)<1,'Desktop comparison viewports must align');
 console.log(JSON.stringify({stage:'initial-frame',tree,imageMetrics}));
 if(reportPath)await writeFile(reportPath,JSON.stringify({status:'RUNNING',scope:'Local viewer integration; later checks pending',harness,firstFrame,tree,imageMetrics},null,2)+'\n');
 const canvasHash=()=>page.locator('#canvas').evaluate(async c=>[...new Uint8Array(await crypto.subtle.digest('SHA-256',c.getContext('2d').getImageData(0,0,c.width,c.height).data))].map(b=>b.toString(16).padStart(2,'0')).join(''));
 if(screenshot)await page.screenshot({path:screenshot,fullPage:true});
 // A real GPU fault must change the frame; manual mode must expose that Lean
 // sample checks are disabled. A compile failure must remove the output.
 await page.locator('#wgsl-tab').click();
 const generated=await page.locator('#wgsl-source').inputValue(),fault=generated.replace(/@fragment\s+fn\s+fragment\b[\s\S]*$/,'@fragment fn fragment(@builtin(position) pixel:vec4f)->@location(0) vec4f {return vec4f(1.0,0.0,1.0,1.0)+clamp(params.rows[0],vec4f(0.0),vec4f(1.0))*0.000001;}') ;
 assert.notEqual(fault,generated);await page.locator('#wgsl-source').fill(fault);await page.locator('#shader-apply').click();
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.includes('MANUAL WGSL')&&!document.querySelector('#render').disabled,{},{timeout:90000});
 evidence=JSON.parse(await page.locator('#evidence').textContent());assert.equal(evidence.manualShader,true);assert.equal(evidence.checks,0);
 const faultPixel=await page.locator('#canvas').evaluate(c=>[...c.getContext('2d').getImageData(20,20,1,1).data]);assert.deepEqual(faultPixel,[255,0,255,255]);
 const faultRgbaSha256=await canvasHash();assert.notEqual(faultRgbaSha256,imageMetrics.gpuRgbaSha256);
 assert.equal(await page.locator('#platform').evaluate(img=>window.__previewBlobs.get(img.src).text()),initial);
 await page.locator('#wgsl-source').fill('invalid wgsl');await page.locator('#shader-apply').click();
 await page.waitForFunction(()=>document.querySelector('#status')?.dataset.error==='true',{},{timeout:90000});
 assert.equal(await page.locator('#canvas').isVisible(),false);assert.equal(await page.locator('#download').isEnabled(),false);
 await page.locator('#shader-reset').click();
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with')&&!document.querySelector('#render').disabled,{},{timeout:90000});
 evidence=JSON.parse(await page.locator('#evidence').textContent());assert.equal(evidence.manualShader,false);assert(evidence.checks>0);
 const restoredRgbaSha256=await canvasHash();assert.equal(restoredRgbaSha256,imageMetrics.gpuRgbaSha256);
 await page.locator('#svg-tab').click();
 await page.locator('#fixture').selectOption('affine.svg');
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with')&&!document.querySelector('#render').disabled,{},{timeout:90000});
 evidence=JSON.parse(await page.locator('#evidence').textContent());assert.equal(evidence.width,800);
 await page.locator('#source').fill('<svg xmlns="http://www.w3.org/2000/svg" width="100" height="100"><foreignObject/></svg>');
 assert.equal(await page.locator('#download').isEnabled(),false);assert.equal(await page.locator('#canvas').isVisible(),false);
 await page.locator('#render').click();
 await page.waitForFunction(()=>document.querySelector('#status')?.dataset.error==='true',{},{timeout:90000});
 assert.equal(await page.locator('#canvas').isVisible(),false);
 await page.locator('#source').fill(initial);
 await page.locator('#source').press('Control+Enter');
 await page.waitForFunction(()=>document.querySelector('#status')?.textContent.startsWith('Rendered with'),{},{timeout:90000});
 assert.equal(await page.locator('#download').isEnabled(),true);
 assert.deepEqual(errors,[]);
 const provenance=await (await page.request.get(origin+'provenance.json')).json();assert(provenance.files.some(f=>f.url.endsWith('svg-engine.wasm')));
 assert.equal((await page.request.get(origin+'lab/SVG.lean')).status(),404);
 assert.equal((await page.request.post(origin)).status(),405);
 await page.setViewportSize({width:700,height:1050});
 const mobile=await page.locator('.outputs .output-panel').evaluateAll(panels=>panels.map(p=>{const r=p.getBoundingClientRect();return {x:r.x,y:r.y,width:r.width,height:r.height};}));
 assert(Math.abs(mobile[0].x-mobile[1].x)<1);assert(Math.abs(mobile[0].width-mobile[1].width)<1);assert(mobile[1].y>=mobile[0].y+mobile[0].height,'Mobile outputs must stack');
 const result={status:'PASS',scope:'Local viewer integration and fault controls; not WPT conformance',browser:await browser.version(),harness,firstFrame,tree,imageMetrics,mobile,shaderControl:{faultRgbaSha256,restoredRgbaSha256},affineFrame:evidence,provenance,loadedAssets:await Promise.all(loadedAssets),checks:['real GPU render','same source bytes in browser SVG preview','exact submitted shader','whole-image backend diagnostic','desktop viewport alignment','mobile output stacking','manual GPU fault visible','manual checks disabled','invalid WGSL removes output','reset restores identical full image and generated checks','fixture switching','source edit invalidates output','unsupported SVG refusal','keyboard render recovery','provenance','server allowlist','read-only HTTP']};
 if(reportPath)await writeFile(reportPath,JSON.stringify(result,null,2)+'\n');
 console.log(JSON.stringify(reportPath?{status:result.status,scope:result.scope,browser:result.browser,treeStatus:tree.status,imageMetrics,checks:result.checks,report:reportPath}:result,null,2));
}finally{await browser.close();}
