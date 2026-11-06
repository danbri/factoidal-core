#!/usr/bin/env node
// Native artifact / GPU math diagnostic, separate from every WPT denominator.
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {encodeRGBA} from './png.mjs';
const args=process.argv.slice(2),opt=name=>{const i=args.indexOf(name);return i<0?null:args[i+1];};
const lab=opt('--svg-lab'),input=opt('--artifact'),output=opt('--output'),chrome=opt('--browser'),playwright=opt('--playwright'),expectedPath=opt('--expected'),witness=opt('--witness');
if(!lab||!input||!output||!chrome||!playwright)throw Error('Usage: artifact_gpu.mjs --svg-lab LAB --artifact FILE --output DIR --browser CHROME --playwright CORE [--expected PIXELS.json] [--witness FILE]');
await mkdir(output,{recursive:true});const hash=b=>createHash('sha256').update(b).digest('hex'),inputBytes=await readFile(input),a=JSON.parse(inputBytes);
const report={scope:'Native Lean artifact / raw GPU math diagnostic; not WPT or source-SVG conformance',artifact:{file:resolve(input),sha256:hash(inputBytes)},browserExecutableSha256:hash(await readFile(chrome)),runtime:{}};
for(const name of ['gpu_transport.ts','render_plan.ts','.build/engines/render-plan.mjs','.build/engines/render-plan.wasm'])report.runtime[name]=hash(await readFile(resolve(lab,name)));
if(witness){const b=await readFile(witness);report.witness={file:resolve(witness),sha256:hash(b),value:JSON.parse(b)};}
const {makeServer}=await import(pathToFileURL(resolve(lab,'browser-webgpu/server.mjs')).href),server=makeServer();
await new Promise((accept,reject)=>{server.once('error',reject);server.listen(0,'127.0.0.1',accept);});
const origin=`http://127.0.0.1:${server.address().port}`,{chromium}=await import(pathToFileURL(resolve(playwright)).href);let browser,code=2;
try{
 browser=await chromium.launch({executablePath:resolve(chrome),headless:true});report.browserVersion=browser.version();
 const page=await browser.newPage();
 await page.route('**/*',route=>route.request().url()===origin+'/diagnostic'?route.fulfill({contentType:'text/html',body:'<!doctype html><title>Raw GPU artifact diagnostic</title>'}):route.request().url().startsWith(origin+'/lab/')?route.continue():route.abort());
 await page.goto(origin+'/diagnostic');
 const result=await page.evaluate(async a=>{
  const transport=await import('/lab/gpu_transport.ts');let submitted;
  const session=await transport.createOffscreenSession(a,'svg-offscreen',s=>submitted=s);if(!session)throw Error('GPU adapter unavailable');
  try{const rgba=await session.draw();let binary='';for(let i=0;i<rgba.length;i+=32768)binary+=String.fromCharCode(...rgba.subarray(i,i+32768));
   return {rgba:btoa(binary),stats:session.stats,adapter:{vendor:session.adapterInfo.vendor,architecture:session.adapterInfo.architecture,isFallbackAdapter:session.adapterInfo.isFallbackAdapter},submittedCode:submitted?.code??a.wgsl};
  }finally{session.close();}
 },a);
 const rgba=Buffer.from(result.rgba,'base64'),png=encodeRGBA(a.width,a.height,rgba);await writeFile(resolve(output,'actual.png'),png);
 const {rgba:_,submittedCode,...facts}=result;Object.assign(report,facts,{width:a.width,height:a.height,samplesVerified:a.checks.length,image:{file:'actual.png',sha256:hash(png),rgbaSha256:hash(rgba)},submittedShaderSha256:hash(Buffer.from(submittedCode))});
 if(report.submittedShaderSha256!==hash(Buffer.from(a.wgsl)))throw Error('Submitted shader differs from artifact');
 report.status=a.checks.length?'rendered-samples-checked':'rendered-diagnostic-no-samples';code=0;
 if(expectedPath){
  const bytes=await readFile(expectedPath);let pixels,channels;
  if(expectedPath.endsWith('.rgba')){pixels=bytes;channels=4;if(bytes.length!==a.width*a.height*4)throw Error('Expected raw RGBA dimensions differ');}
  else{const e=JSON.parse(bytes);pixels=e.pixels;channels=3;if(e.width!==a.width||e.height!==a.height||!Array.isArray(pixels)||pixels.length!==a.width*a.height*3)throw Error('Expected full RGB raster dimensions differ');}
  let different=0,maximum=0;for(let p=0;p<a.width*a.height;p++){let changed=channels===3&&rgba[p*4+3]!==255;for(let c=0;c<channels;c++){const delta=Math.abs(rgba[p*4+c]-pixels[p*channels+c]);maximum=Math.max(maximum,delta);changed||=delta!==0;}different+=changed;}
  report.expected={file:resolve(expectedPath),sha256:hash(bytes)};report.comparison={differentPixels:different,maxChannelDifference:maximum,totalPixels:a.width*a.height};report.status=different?'MISMATCH':'PASS';code=different?1:0;
 }
}catch(error){report.status='unavailable';report.error=String(error);}
finally{
 await browser?.close();await new Promise(r=>server.close(r));report.exitCode=code;
 await writeFile(resolve(output,'report.json'),JSON.stringify(report,null,2)+'\n');await writeFile(resolve(output,'exit.txt'),String(code)+'\n');console.log(JSON.stringify(report));
}
process.exitCode=code;
