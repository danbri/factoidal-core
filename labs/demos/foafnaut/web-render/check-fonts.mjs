#!/usr/bin/env node
// Same original HTML in Lean and Chrome; only the independent oracle loads
// the real font in its browser. Candidate shaping data comes from HB/FT.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import {pathToFileURL,fileURLToPath} from 'node:url';
import {dirname,resolve} from 'node:path';
import {createHash} from 'node:crypto';
const [origin,playwrightPath,browserPath,nativePath,fontPath,fontDataPath,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-fonts.mjs ORIGIN PLAYWRIGHT CHROME NATIVE_OR_DASH AHEM_TTF FONT_DATA_JSON OUT');
await mkdir(outDir,{recursive:true});const hash=b=>createHash('sha256').update(b).digest('hex'),fontBytes=await readFile(fontPath),fontData=await readFile(fontDataPath,'utf8'),records=JSON.parse(fontData);
const fontSha=hash(fontBytes);assert.equal(fontSha,'b719ecb31c5b21fc573c03f6421c74ac63c271a5a3ff841e34f9705fb94b8448');assert(records.every(r=>r.fontSha256===fontSha));
const {chromium}=await import(pathToFileURL(playwrightPath)),browser=await chromium.launch({executablePath:browserPath,headless:true}),checkCPU=nativePath!=='-';
const report={status:'RUNNING',scope:'Supplied real-font HTML profile; no full text/WPT conformance claim',cpuComparison:checkCPU?'enabled':'not run (GPU-only diagnostic)',fontSha256:fontSha,fontDataSha256:hash(fontData),nativeSha256:checkCPU?hash(await readFile(nativePath)):null,images:[],checks:[]};
try{
 const page=await browser.newPage();await page.goto(origin);await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 const width=128,height=80;
 async function gpu(source){return page.evaluate(async({source,fontData,width,height})=>{
  const {compileWithFontData}=await import('/engine.mjs'),{createOffscreenSession}=await import('/lab/gpu_transport.ts');
  const artifact=await compileWithFontData(source,fontData,width,height),session=await createOffscreenSession(artifact,'svg-offscreen');
  if(!session)throw Error('WebGPU unavailable');try{return{artifact,rgba:Array.from(await session.draw())};}finally{session.close();}
 },{source,fontData,width,height});}
 async function compare(name,source){
  const input=resolve(outDir,name+'.html');await writeFile(input,source);const rendered=await gpu(source),rgba=Buffer.from(rendered.rgba),raw=resolve(outDir,name+'.rgba');await writeFile(raw,rgba);
  if(checkCPU){
   const compiled=spawnSync(nativePath,[input,String(width),String(height),'--font-data',fontDataPath],{encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});assert.equal(compiled.status,0,compiled.stderr);assert.deepEqual(JSON.parse(compiled.stdout),rendered.artifact,name+' complete native/WASM artifact');
   const run=spawnSync(nativePath,[input,String(width),String(height),'--font-data',fontDataPath,'--pixels'],{encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});assert.equal(run.status,0,run.stderr);const cpu=JSON.parse(run.stdout);assert(!cpu.error,cpu.error);const rgb=[];for(let i=0;i<rgba.length;i+=4)rgb.push(rgba[i],rgba[i+1],rgba[i+2]);assert.deepEqual(rgb,cpu.pixels,name+' whole CPU/GPU image');
  }
  const oracle=await browser.newPage({viewport:{width,height},deviceScaleFactor:1});await oracle.setContent(source);
  await oracle.evaluate(async base64=>{const bytes=Uint8Array.from(atob(base64),c=>c.charCodeAt(0)),face=new FontFace('Ahem',bytes);await face.load();document.fonts.add(face);await document.fonts.load('20px Ahem');await document.fonts.ready;},fontBytes.toString('base64'));
  const png=resolve(outDir,name+'-original.png');await oracle.screenshot({path:png});await oracle.close();
  const diff=spawnSync('python3',['-c',`from PIL import Image\nfrom pathlib import Path\nimport json,sys\na=Image.open(sys.argv[1]).convert('RGBA').tobytes();b=Path(sys.argv[2]).read_bytes()\nassert len(a)==len(b)\nd=sum(a[i:i+4]!=b[i:i+4] for i in range(0,len(a),4));m=max(abs(x-y) for x,y in zip(a,b));print(json.dumps({'differentPixels':d,'maxChannelDifference':m,'pixels':len(a)//4}));sys.exit(0 if d==0 else 1)`,png,raw],{encoding:'utf8'});
  const comparison=JSON.parse(diff.stdout);assert([0,1].includes(diff.status),diff.stderr);report.images.push({name,width,height,sourceSha256:hash(source),rgbaSha256:hash(rgba),comparison});return rendered;
 }
 const here=dirname(fileURLToPath(import.meta.url)),source=await readFile(resolve(here,'fixtures/font-data.html'),'utf8'),base=await compare('real-ahem',source);
 assert.equal(base.artifact.webRender.fontResource.fontSha256,fontSha);assert.equal(base.artifact.webRender.fontResource.family,'Ahem');
 for(const run of base.artifact.webRender.glyphRuns){const record=records.find(r=>r.text===run.text&&r.bitmapPixelSize===run.size);assert(record);assert.deepEqual(run.glyphs.map(g=>g[0]),record.glyphs.map(g=>g.id));}
 assert.deepEqual(base.artifact.webRender.glyphRuns.map(r=>r.glyphs.map(g=>g[2])),[[0,0],[20,20]]);report.checks.push('actual HB glyph IDs, font SHA, 20px real advances, source-mapped wrapping and inline SVG parent strut');
 const variants=[['width',source.replace('width:50px','width:100px')],['color',source.replace('font-family:Ahem','color:blue;font-family:Ahem')],['text',source.replace('AA BB','AAA BB')],['size',source.replace('font-size:20px','font-size:10px')]];
 for(const [name,html]of variants){const frame=await compare('real-ahem-'+name,html);assert.notEqual(hash(Buffer.from(frame.rgba)),hash(Buffer.from(base.rgba)),name+' changes actual font pixels');}
 report.checks.push('five whole actual-font images captured and compared with original Chrome; CSS width/color, text and font-size controls change pixels');
 async function refused(html,data=fontData){return page.evaluate(async({html,data,width,height})=>{try{await(await import('/engine.mjs')).compileWithFontData(html,data,width,height);return null;}catch(e){return e.message;}},{html,data,width,height});}
 assert.match(await refused(source.replace('AA BB','CC')),/missing shaped word data/);assert.match(await refused(source.replace('20px;line-height','21px;line-height')),/missing shaped word data/);assert.match(await refused(source.replace('font-family:Ahem','font-family:Other')),/unsupported font family/);assert.match(await refused(source,'[]'),/require 1 to 4096/);report.checks.push('missing word/size, mismatched family and empty data refuse output');
 const bare=await page.evaluate(async html=>{try{await(await import('/engine.mjs')).compile(html,128,80);return null;}catch(e){return e.message;}},source);assert.match(bare,/unsupported font family/);report.checks.push('Ahem without supplied matching data remains refused by ASCII route');
 report.provenance=await(await page.request.get(origin+'provenance.json')).json();report.status=report.images.every(image=>image.comparison.differentPixels===0)?'PASS':'ORACLE_MISMATCH';if(report.status!=='PASS')process.exitCode=1;
}catch(error){report.status='FAIL';report.failure=String(error);throw error;}finally{await browser.close();await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
