#!/usr/bin/env node
// Original HTML remains the oracle input. Candidate geometry is produced in Lean.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';
import {createHash} from 'node:crypto';
const [origin,playwrightPath,browserPath,nativePath,wptRoot,outDir]=process.argv.slice(2);
if(!outDir)throw Error('usage: check-embedding.mjs ORIGIN PLAYWRIGHT_CORE_MJS CHROME NATIVE_CLI_OR_DASH WPT_ROOT OUTPUT_DIR');
await mkdir(outDir,{recursive:true});
const hash=b=>createHash('sha256').update(b).digest('hex'),{chromium}=await import(pathToFileURL(playwrightPath));
const browser=await chromium.launch({executablePath:browserPath,headless:true});
const checkCPU=nativePath!=='-';
const report={status:'RUNNING',scope:'Original HTML diagnostics and local admitted-profile checks; corpus scores remain separate',cpuComparison:checkCPU?'enabled':'not run (GPU-only diagnostic)',nativeSha256:checkCPU?hash(await readFile(nativePath)):null,images:[],checks:[]};
try{
 const page=await browser.newPage();await page.goto(origin);await page.waitForFunction(()=>window.webRenderResult,{},{timeout:90000});
 async function gpu(source,width,height){return page.evaluate(async({source,width,height})=>{
   const {compile}=await import('/engine.mjs'),{createOffscreenSession}=await import('/lab/gpu_transport.ts');
   const artifact=await compile(source,width,height),session=await createOffscreenSession(artifact,'svg-offscreen');
   if(!session)throw Error('WebGPU unavailable');try{return {artifact,rgba:Array.from(await session.draw())};}finally{session.close();}
 },{source,width,height});}
 async function compare(name,source,width=128,height=128){
   const input=resolve(outDir,name+'.html');await writeFile(input,source);
   const rendered=await gpu(source,width,height),rgba=Buffer.from(rendered.rgba),pixels=resolve(outDir,name+'.rgba');await writeFile(pixels,rgba);
   if(checkCPU){const run=spawnSync(nativePath,[input,String(width),String(height),'--pixels'],{encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});assert.equal(run.status,0,run.stderr);
     const cpu=JSON.parse(run.stdout);assert(!cpu.error,cpu.error);const rgb=[];for(let i=0;i<rgba.length;i+=4)rgb.push(rgba[i],rgba[i+1],rgba[i+2]);assert.deepEqual(rgb,cpu.pixels,name+' CPU/GPU');}
   const oracle=await browser.newPage({viewport:{width,height},deviceScaleFactor:1});await oracle.setContent(source);const png=resolve(outDir,name+'-original.png');await oracle.screenshot({path:png});await oracle.close();
   const diff=spawnSync('python3',['-c',`from PIL import Image\nfrom pathlib import Path\nimport json,sys\na=Image.open(sys.argv[1]).convert('RGBA').tobytes();b=Path(sys.argv[2]).read_bytes()\nassert len(a)==len(b)\nd=sum(a[i:i+4]!=b[i:i+4] for i in range(0,len(a),4));m=max(abs(x-y) for x,y in zip(a,b));print(json.dumps({'differentPixels':d,'maxChannelDifference':m,'pixels':len(a)//4}));sys.exit(0 if d==0 else 1)`,png,pixels],{encoding:'utf8'});
   const comparison=JSON.parse(diff.stdout);report.images.push({name,width,height,sourceSha256:hash(source),rgbaSha256:hash(rgba),comparison});assert.equal(diff.status,0,name+' '+diff.stdout+diff.stderr);return rendered;
 }
 const test=await readFile(resolve(wptRoot,'svg/render/reftests/overflow-clip.html'),'utf8'),reference=await readFile(resolve(wptRoot,'svg/render/reftests/rect-ref.html'),'utf8');
 const a=await compare('original-overflow-clip',test),b=await compare('original-rect-reference',reference);assert.deepEqual(a.rgba,b.rgba);report.checks.push(`two unchanged original WPT HTML documents each ${checkCPU?'CPU/GPU/browser':'GPU/browser'} exact, candidate test/reference exact`);
 await compare('block-overflow','<!doctype html><style>body{margin:0}div{width:20px;height:12px;overflow:hidden;background:red}div div{width:40px;height:24px;background:blue}</style><div><div></div></div>');
 report.checks.push('block overflow clips actual child paint to padding box');
 const svg='<!doctype html><style>body{margin:0}svg{display:block;width:40px;height:30px;background:yellow;color:red}</style><svg viewBox="0 0 20 10" preserveAspectRatio="none"><rect width="10" height="20" fill="currentColor"/></svg>';
 const svgA=await compare('block-svg-viewport',svg),svgB=await compare('block-svg-mutation',svg.replace('width:40px','width:30px').replace('color:red','color:blue'));
 assert.notEqual(hash(Buffer.from(svgA.rgba)),hash(Buffer.from(svgB.rgba)));report.checks.push('CSS block SVG dimensions, viewBox affine mapping, default clip and currentColor mutations');
 const links=await gpu('<style>body{margin:0;font-size:7px;line-height:7px}div{width:24px;height:7px;overflow:clip}</style><div><a href="target">AA BB</a></div>',64,32);
 const hits=await page.evaluate(async artifact=>{const {hitLink}=await import('/engine.mjs');return [await hitLink(artifact,3,3),await hitLink(artifact,3,8)];},links.artifact);assert.equal(hits[0].href,'target');assert.equal(hits[1],null);report.checks.push('Lean hit regions follow ancestor overflow clip');
 const error=await page.evaluate(async()=>{try{await(await import('/engine.mjs')).compile('<style>svg rect{fill:red}</style><svg><rect width="5" height="5"/></svg>',64,64);return null;}catch(e){return e.message;}});assert.match(error,/unsupported HTML stylesheet rule targeting embedded SVG descendants/);report.checks.push('unified descendant CSS gap remains an explicit unsupported result');
 report.provenance=await(await page.request.get(origin+'provenance.json')).json();report.status='PASS';
}finally{await browser.close();await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
