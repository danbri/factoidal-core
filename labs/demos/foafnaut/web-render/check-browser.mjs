#!/usr/bin/env node
// Whole-image GPU checks against CPU and original HTML rendered by Chrome.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {dirname,resolve} from 'node:path';
import {createHash} from 'node:crypto';
const [origin,playwrightPath,browserPath,nativePath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-browser.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME NATIVE_CLI OUTPUT_DIR');
await mkdir(outDir,{recursive:true});
const here=dirname(fileURLToPath(import.meta.url)),hash=bytes=>createHash('sha256').update(bytes).digest('hex');
const {chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true});
const report={format:'factoidal-web-render-evidence-v1',status:'RUNNING',scope:'Local HTML/CSS profile checks, not a WPT suite score',capturedAt:new Date().toISOString(),browser:await browser.version(),nativeSha256:hash(await readFile(nativePath)),checks:[]};
try{
 const page=await browser.newPage({viewport:{width:1300,height:1000}}),errors=[];
 page.on('pageerror',e=>errors.push(e.message));await page.goto(origin);
 await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 const initial=await page.evaluate(()=>window.webRenderResult);assert(!initial.error,initial.error);
 assert(initial.artifact.webRender.glyphRuns.length>0);assert(initial.artifact.primitiveCount>0);
 await page.screenshot({path:resolve(outDir,'viewer.png'),fullPage:true});
 report.default={width:initial.artifact.width,height:initial.artifact.height,primitives:initial.artifact.primitiveCount,glyphRuns:initial.artifact.webRender.glyphRuns.length,rgbaSha256:hash(Buffer.from(initial.rgba))};
 report.checks.push('default HTML/CSS input through Lean WASM and browser WebGPU');
 // Compile each original fixture through the same real WASM frontend and GPU.
 async function gpu(source,width,height){return page.evaluate(async({source,width,height})=>{
   const {compile}=await import('/engine.mjs'),{createOffscreenSession}=await import('/lab/gpu_transport.ts');
   const artifact=await compile(source,width,height),session=await createOffscreenSession(artifact,'svg-offscreen');
   if(!session)throw Error('WebGPU adapter unavailable');try{return {artifact,rgba:Array.from(await session.draw())};}finally{session.close();}
 },{source,width,height});}
 const fixture=resolve(here,'fixtures/boxes.html'),source=await readFile(fixture,'utf8'),width=96,height=80;
 const rendered=await gpu(source,width,height),rgba=Buffer.from(rendered.rgba);
 const cpuRun=spawnSync(nativePath,[fixture,String(width),String(height),'--pixels'],{encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
 assert.equal(cpuRun.status,0,cpuRun.stderr);const cpu=JSON.parse(cpuRun.stdout);assert(!cpu.error,cpu.error);
 assert.equal(cpu.pixels.length,width*height*3);const rgb=[];for(let i=0;i<rgba.length;i+=4)rgb.push(rgba[i],rgba[i+1],rgba[i+2]);
 assert.deepEqual(rgb,cpu.pixels,'whole CPU and browser GPU image');
 await writeFile(resolve(outDir,'gpu-boxes.rgba'),rgba);
 await writeFile(resolve(outDir,'cpu-boxes.rgb'),Buffer.from(cpu.pixels));
 const oracle=await browser.newPage({viewport:{width,height},deviceScaleFactor:1});
 await oracle.setContent(source);await oracle.screenshot({path:resolve(outDir,'browser-original-boxes.png')});await oracle.close();
 // PNG decoding is transport; oracle image comes from the untouched original HTML.
 const compare=spawnSync('python3',['-c',`from PIL import Image\nfrom pathlib import Path\nimport json,sys\na=Image.open(sys.argv[1]).convert('RGBA').tobytes();b=Path(sys.argv[2]).read_bytes()\nassert len(a)==len(b)\nd=sum(a[i:i+4]!=b[i:i+4] for i in range(0,len(a),4));m=max(abs(x-y) for x,y in zip(a,b));print(json.dumps({'differentPixels':d,'maxChannelDifference':m,'pixels':len(a)//4}));sys.exit(0 if d==0 else 1)`,resolve(outDir,'browser-original-boxes.png'),resolve(outDir,'gpu-boxes.rgba')],{encoding:'utf8'});
 report.boxes={width,height,sourceSha256:hash(source),gpuRgbaSha256:hash(rgba),cpuRgbSha256:hash(Buffer.from(cpu.pixels)),browserComparison:JSON.parse(compare.stdout)};
 assert.equal(compare.status,0,compare.stdout+compare.stderr);report.checks.push('whole CPU/GPU exact image and independent original-HTML browser image');
 const recolored=await gpu(source.replace('background:red','background:yellow'),width,height);assert.notEqual(hash(Buffer.from(recolored.rgba)),hash(rgba));
 const wider=await gpu(source.replace('width:64px','width:72px'),width,height);assert.notEqual(hash(Buffer.from(wider.rgba)),hash(rgba));
 report.checks.push('CSS color and width controls change actual GPU pixels');
 const flow=await readFile(resolve(here,'fixtures/flow.html'),'utf8'),flowA=await gpu(flow,96,64),flowB=await gpu(flow.replace('AA BB','AB BA'),96,64),flowWide=await gpu(flow.replace('width:30px','width:60px'),96,64);
 assert.notEqual(hash(Buffer.from(flowA.rgba)),hash(Buffer.from(flowB.rgba)),'text mutation must change actual glyph paint');
 assert.notDeepEqual(flowA.artifact.webRender.glyphRuns.map(r=>r.glyphs.map(g=>g[2])),flowWide.artifact.webRender.glyphRuns.map(r=>r.glyphs.map(g=>g[2])),'width mutation must change text positions');
 report.flow={sourceSha256:hash(flow),rgbaSha256:hash(Buffer.from(flowA.rgba)),textMutationSha256:hash(Buffer.from(flowB.rgba)),widthMutationSha256:hash(Buffer.from(flowWide.rgba)),glyphRuns:flowA.artifact.webRender.glyphRuns};report.checks.push('text mutation changes glyph pixels and width mutation reflows source-mapped glyphs');
 const error=await page.evaluate(async()=>{try{await(await import('/engine.mjs')).compile('<div style="font-family:Ahem">A</div>',96,64);return null;}catch(e){return e.message;}});assert.match(error,/unsupported font family/);report.checks.push('unsupported font profile refuses output');
 assert.deepEqual(errors,[]);report.provenance=await(await page.request.get(origin+'provenance.json')).json();report.status='PASS';
}finally{await browser.close();await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify({status:report.status,checks:report.checks,boxes:report.boxes,report:resolve(outDir,'report.json')},null,2));
