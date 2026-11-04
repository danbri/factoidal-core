#!/usr/bin/env node
// Actual native/WASM layout stack controls. No parser, CSS, layout or scene
// implementation is reproduced here; every case enters the compiled Lean ABI.
import assert from 'node:assert/strict';
import {readFile,writeFile,mkdtemp,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join,resolve} from 'node:path';
import {pathToFileURL} from 'node:url';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
const [modulePath,nativePath,reportPath,controlPath]=process.argv.slice(2);
if(!controlPath)throw Error('usage: rendering_layout.mjs WASM_MODULE.mjs NATIVE_CLI NEW_REPORT.json STACK_CONTROL');
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const engine=resolve(modulePath),native=resolve(nativePath),mod=await(await import(pathToFileURL(engine))).default();
const nativeEnv={...process.env,LEAN_STACK_SIZE_KB:'512'};delete nativeEnv.LEAN_MAIN_USE_THREAD;
const defaultEnv={...process.env};delete defaultEnv.LEAN_MAIN_USE_THREAD;delete defaultEnv.LEAN_STACK_SIZE_KB;
const control=resolve(controlPath),controlCases=[];
for(const [name,count,env,overflow] of [['small-budget',100,nativeEnv,false],['large-budget',204800,nativeEnv,true],['large-default',204800,defaultEnv,false]]){
 const result=spawnSync(control,[String(count)],{env,encoding:'utf8',timeout:30000,maxBuffer:1048576});
 if(overflow){assert(result.status!==0||result.signal,`Stack budget did not reach control: ${name}`);assert.match(result.stderr,/stack overflow/i,`${name}: ${result.stderr}`);}
 else{assert.equal(result.status,0,`${name}: ${result.stderr}`);assert.equal(result.stdout.trim(),String(BigInt(count)*BigInt(count-1)/2n));}
 controlCases.push({name,count,status:result.status,signal:result.signal,expectedOverflow:overflow});
}
const dir=await mkdtemp(join(tmpdir(),'factoidal-layout-stack-'));
const nested=(tag,count)=>`<${tag}>`.repeat(count)+'A'+`</${tag}>`.repeat(count);
const rows=[];
for(const tag of ['div','span']){
 for(const count of [1,1000,10000,50000])rows.push({name:`${tag}-siblings-${count}`,source:`<${tag}></${tag}>`.repeat(count)+'A',accept:true});
 for(const count of [60,61,10000])rows.push({name:`${tag}-depth-${count}`,source:nested(tag,count),accept:count===60});
}
rows.push({name:'mixed-depth-60',source:'<div>'.repeat(30)+nested('span',30)+'</div>'.repeat(30),accept:true});
rows.push({name:'mixed-depth-61',source:'<div>'.repeat(31)+nested('span',30)+'</div>'.repeat(31),accept:false});
rows.push({name:'wide-then-deep',source:'<div></div>'.repeat(2000)+nested('div',60),accept:true});
const report={status:'RUNNING',scope:'Unchanged Lean layout, exact native/WASM artifacts, requested Lean main-thread stack512KiB with real non-tail negative control, fixed production fuel64; no general arbitrary-fuel or C-stack theorem.',nativeStack:{LEAN_STACK_SIZE_KB:512,LEAN_MAIN_USE_THREAD:'unset',controlSha256:sha(await readFile(control)),controlCases},nativeSha256:sha(await readFile(native)),engineSha256:sha(await readFile(engine)),wasmSha256:sha(await readFile(engine.replace(/\.mjs$/,'.wasm'))),checks:[]};
try{
 for(const row of rows){
  const sourceBytes=Buffer.byteLength(row.source);assert(sourceBytes<=1048576);
  const input=join(dir,'case.html');await writeFile(input,row.source);
  const start=performance.now();
  // RLIMIT_STACK alone does not limit the separate thread used by lean_run_main.
  // The runtime variable and unset MAIN_USE_THREAD match the verified control.
  const run=spawnSync('/bin/sh',['-c','ulimit -s 512 && exec "$@"','layout-stack',native,input,'120','100'],{env:nativeEnv,encoding:'utf8',timeout:120000,maxBuffer:33554432});
  assert.equal(run.status,0,`${row.name}: native ${run.signal??run.status}: ${run.stderr}`);
  const nativeMs=performance.now()-start,nativeArtifact=JSON.parse(run.stdout);
  const wasmStart=performance.now(),ptr=mod.ccall('web_render_call','number',['string','number','number'],[row.source,120,100]);assert(ptr);
  let wire;try{wire=mod.UTF8ToString(ptr);}finally{mod.ccall('web_render_free',null,['number'],[ptr]);}
  const wasmMs=performance.now()-wasmStart,artifact=JSON.parse(wire);
  assert.deepEqual(artifact,nativeArtifact,`${row.name}: exact native/WASM artifact`);
  if(row.accept){assert(!artifact.error,`${row.name}: ${artifact.error}`);assert.equal(artifact.webRender.glyphRuns.length,1);}
  else assert.equal(artifact.error,'unsupported HTML nesting depth (maximum 64)',row.name);
  const check={name:row.name,status:'PASS',sourceBytes,nativeMs,wasmMs,...(artifact.error?{error:artifact.error}:{boxes:artifact.webRender.boxes.length,primitives:artifact.primitiveCount}),artifactSha256:sha(wire)};
  report.checks.push(check);console.log(JSON.stringify(check));
 }
 report.status='PASS';
}finally{await rm(dir,{recursive:true,force:true});await writeFile(reportPath,JSON.stringify(report,null,2)+'\n',{flag:'wx'});}
console.log(JSON.stringify({status:report.status,checks:report.checks.length,report:resolve(reportPath)}));
