#!/usr/bin/env node
// Native/WASM transaction differential: Lean DOM commands + ordered supplied
// stylesheets + dynamic HB/FT data + scene. No host HTML/CSS parsing or layout.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdir} from 'node:fs/promises';
import {spawnSync} from 'node:child_process';
import {dirname,resolve} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import {createFontBroker} from '../tools/font-broker.mjs';
const here=dirname(fileURLToPath(import.meta.url)),lab=resolve(here,'..');
const [nativePath=resolve(lab,'.build/web-render/web-render-native'),wasmPath=resolve(lab,'.build/web-render/engines/web-render.mjs'),outDir='/tmp/factoidal-document-font-check']=process.argv.slice(2);
await mkdir(outDir,{recursive:true});
const createModule=(await import(pathToFileURL(resolve(wasmPath)))).default,module=await createModule();
const broker=createFontBroker(),report={status:'RUNNING',scope:'Actual-font native/WASM document transaction; no full browser conformance claim',checks:[]};
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
let serial=0;
function wasm(html,options,width=420,height=120){
 const pointer=module.ccall('web_document_call','number',['string','string','number','number'],[html,JSON.stringify(options),width,height]);
 assert(pointer,'WASM document allocation');try{return JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
async function native(html,options,width=420,height=120){
 const id=serial++,input=resolve(outDir,`input-${id}.html`),request=resolve(outDir,`request-${id}.json`);
 await writeFile(input,html);await writeFile(request,JSON.stringify(options));
 const result=spawnSync(nativePath,[input,String(width),String(height),'--document',request],{encoding:'utf8',timeout:120000,maxBuffer:32*1024*1024});
 assert.equal(result.status,0,result.stderr);return JSON.parse(result.stdout);
}
async function both(html,options){const n=await native(html,options),w=wasm(html,options);assert.deepEqual(w,n,'complete native/WASM document result');return n;}
try{
 const bitmapRequests=await both('<p>default bitmap words</p>',{op:'fontRequests'});
 assert.deepEqual(bitmapRequests.requests,[],'Lean bitmap profile needs no host font data');
 const bitmap=await both('<p>default bitmap words</p>',{op:'render'});assert(!bitmap.error,bitmap.error);
 assert.equal(bitmap.webRender.profile,'lean-block-inline-ascii-bitmap-v1');
 report.checks.push('Lean chooses default bitmap profile without host generic-family matching');
 const scriptTypes=await both("<script type=' text/ecmascript '>classic()</script><script type='application/json'>{}</script>",{op:'inspect'});
 assert.equal(scriptTypes.scripts.length,1);assert.equal(scriptTypes.scripts[0].kind,'classic');assert.equal(scriptTypes.scripts[0].source,'classic()');
 for(const op of ['inspect','render']){
  const modulePage=await both("<script type=' module '>export{}</script>",{op});
  assert(!modulePage.error,modulePage.error);
  if(op==='inspect')assert.equal(modulePage.scripts.length,0,'module scripts are fetched by the script session, not the host');
 }
 report.checks.push('Lean normalizes classic script MIME types, keeps data blocks inert and leaves module scripts to the script session');
 const html="<!doctype html><base href='./assets/'><style>body{font-family:Arial;font-size:20px;line-height:35px;background:white;color:black}p{font-size:12px}</style><link rel=stylesheet href='../css/main.css'><style>p{font-size:21px}</style><p id=message>stale</p><span style='font-size:28px'>office</span><script src='./scripts/app.js'></script>";
 const inspected=await both(html,{op:'inspect',url:'https://example.test/a/page.html'});
 assert.equal(inspected.baseURL,'https://example.test/a/assets/');
 assert.equal(inspected.stylesheets[0].url,'https://example.test/a/css/main.css');
 assert.equal(inspected.scripts[0].url,'https://example.test/a/assets/scripts/app.js');
 const target=inspected.nodes.find(node=>node.attributes.id==='message').id,link=inspected.stylesheets[0].nodeId;
 const options={url:'https://example.test/a/page.html',commands:[{op:'setTextContent',nodeId:target,value:'November2026 café edited'}],resources:[{nodeId:link,source:'p{font-size:24px!important}'}]};
 const requests=await both(html,{...options,op:'fontRequests'});assert(!requests.error,requests.error);
 assert(requests.requests.some(request=>request.text==='November2026'&&request.pixelSize===24));
 assert(!requests.requests.some(request=>request.text==='stale'));
 const records=await broker(requests),fontData=JSON.stringify(records);
 const rendered=await both(html,{...options,op:'render',fontData});assert(!rendered.error,rendered.error);
 assert.equal(rendered.webRender.fontResource.family,'Arial');assert.match(rendered.webRender.fontResource.fontSha256,/^[0-9a-f]{64}$/);
 assert(rendered.webRender.glyphRuns.some(run=>run.text==='November2026'&&run.size===24));
 report.fontSha256=rendered.webRender.fontResource.fontSha256;report.checks.push('same native/WASM relative URLs, script-modified text, important external CSS, dynamic actual font scene');
 const ordered=await both(html,{...options,op:'fontRequests',resources:[{nodeId:link,source:'p{font-size:24px}'}]});
 assert(ordered.requests.some(request=>request.text==='November2026'&&request.pixelSize===21));
 report.checks.push('later embedded stylesheet wins normal external declaration; important external declaration wins later normal rule');
 for(const resources of [[],[options.resources[0],options.resources[0]]]){
  const refused=await both(html,{...options,op:'fontRequests',resources});assert.match(refused.error,/missing|duplicat/);
 }
 const mixed=await both(html,{...options,op:'fontRequests',commands:[{op:'setTextContent',nodeId:target,value:'Aשלום'}]});assert.match(mixed.error,/bidi/);
 report.checks.push('missing and duplicate stylesheet resources, mixed bidi text refused');
 const editedOptions={...options,commands:[{op:'setTextContent',nodeId:target,value:'ChangedAgain résumé'}]};
 const editedRequests=await both(html,{...editedOptions,op:'fontRequests'}),editedData=JSON.stringify(await broker(editedRequests));
 const edited=await both(html,{...editedOptions,op:'render',fontData:editedData});assert(!edited.error,edited.error);
 assert(edited.webRender.glyphRuns.some(run=>run.text==='ChangedAgain'));
 assert.notEqual(hash(JSON.stringify(edited.data)),hash(JSON.stringify(rendered.data)));
 report.checks.push('second arbitrary edit reshapes fresh words and changes emitted scene geometry');
 await writeFile(resolve(outDir,'artifact.json'),JSON.stringify(rendered));
 report.nativeSha256=hash(await readFile(nativePath));report.wasmModuleSha256=hash(await readFile(resolve(wasmPath).replace(/\.mjs$/,'.wasm')));report.status='PASS';
}catch(error){report.status='FAIL';report.failure=String(error);throw error;}finally{await writeFile(resolve(outDir,'report.json'),JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify(report,null,2));
