#!/usr/bin/env node
// Independent browser images. No fixture rewriting, geometry extraction or candidate renderer.
import { readFile, writeFile, mkdir } from 'node:fs/promises';
import { createServer } from 'node:http';
import { resolve, dirname, relative, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { platform, release, arch } from 'node:os';
const root=dirname(fileURLToPath(import.meta.url));
const args=process.argv.slice(2), option=(name)=>{const i=args.indexOf(name);return i<0?null:args[i+1];};
const output=option('--output'), executable=option('--browser'), playwright=option('--playwright');
if(!output||!executable||!playwright) throw Error('Usage: capture_reference.mjs --output DIR --browser CHROME --playwright /path/to/playwright-core/index.mjs');
const manifest=JSON.parse(await readFile(resolve(root,'manifest.json'),'utf8'));
const hash=b=>createHash('sha256').update(b).digest('hex');
// Verify the complete pinned inventory before starting a browser or network listener.
for(const f of manifest.files) if(hash(await readFile(resolve(root,'upstream',f.path)))!==f.sha256) throw Error(`Fixture hash mismatch: ${f.path}`);
await mkdir(output,{recursive:true});
const upstream=resolve(root,'upstream');
const server=createServer(async(req,res)=>{try{
 const name=decodeURIComponent(new URL(req.url,'http://localhost').pathname).slice(1), path=resolve(upstream,name);
 if(relative(upstream,path).split(sep).includes('..')) throw Error('outside fixture root');
 const body=await readFile(path);res.writeHead(200,{'Content-Type':path.endsWith('.svg')?'image/svg+xml':'application/octet-stream','Cache-Control':'no-store'});res.end(body);
}catch{res.writeHead(404);res.end();}});
await new Promise(r=>server.listen(0,'127.0.0.1',r));
const origin=`http://127.0.0.1:${server.address().port}`;
const { chromium }=await import(pathToFileURL(resolve(playwright)).href);
let browser;
const report={revision:manifest.revision,mode:'independent-browser-static-candidate',viewport:{width:800,height:600,deviceScaleFactor:1},background:'white browser canvas',scripts:false,externalFetch:false,host:{platform:platform(),release:release(),arch:arch()},fonts:'System fonts not independently enumerated; external-font cases excluded explicitly.',scope:'Original unchanged standalone SVG documents; no general secure-static mode equivalence claim.',browserExecutableSha256:hash(await readFile(executable)),cases:[]};
try{
 browser=await chromium.launch({executablePath:executable,headless:true}); report.browserVersion=browser.version();
 const context=await browser.newContext({viewport:{width:800,height:600},deviceScaleFactor:1,javaScriptEnabled:false,colorScheme:'light',reducedMotion:'reduce'});
 await context.route('**/*',route=>route.request().url().startsWith(origin+'/')?route.continue():route.abort());
 const page=await context.newPage();
 for(const [i,c] of manifest.cases.entries()){
  const row={test:c.test,reference:c.reference,fuzzy:c.fuzzy,status:'unavailable'};
  if(c.requiredRuntime.length){row.reason='Original runtime/resource requirement: '+c.requiredRuntime.join(', ');report.cases.push(row);continue;}
  try{
   row.images={};
   for(const [role,path] of [['test',c.test],['reference',c.reference]]){
    const response=await page.goto(origin+'/'+path,{waitUntil:'load',timeout:15000});if(!response?.ok())throw Error(`HTTP ${response?.status()}`);
    // No animation-bearing case is certified by this restricted capture mode.
    const source=await readFile(resolve(upstream,path),'utf8');if(/<(?:[\w.-]+:)?(?:animate\w*|set)\b/i.test(source))throw Error('Animation requires a documented secure-static oracle');
    const file=`${String(i).padStart(2,'0')}-${role}.png`,bytes=await page.screenshot({path:resolve(output,file),fullPage:false,animations:'disabled'});
    row.images[role]={file,sha256:hash(bytes),sourceSha256:hash(Buffer.from(source))};
   }
   row.status='captured';
  }catch(error){row.reason=String(error);}
  report.cases.push(row);
 }
 await context.close();
}finally{await browser?.close();await new Promise(r=>server.close(r));}
report.total=report.cases.length;report.counts={captured:report.cases.filter(x=>x.status==='captured').length,unavailable:report.cases.filter(x=>x.status==='unavailable').length};
await writeFile(resolve(output,'oracle.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({total:report.total,counts:report.counts,browserVersion:report.browserVersion}));
