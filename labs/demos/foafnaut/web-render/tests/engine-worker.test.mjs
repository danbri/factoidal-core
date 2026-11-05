import test from 'node:test';
import assert from 'node:assert/strict';
import {readFile,mkdtemp,writeFile,rm} from 'node:fs/promises';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {Worker} from 'node:worker_threads';
import {EventEmitter,once} from 'node:events';
import {pathToFileURL} from 'node:url';
import {createEngine} from '../engine.mjs';
import * as direct from '../engine-core.mjs';
const modulePath=process.env.FACTOIDAL_RENDER_MODULE;
if(!modulePath||!process.env.FACTOIDAL_FONT_DATA)throw Error('Set FACTOIDAL_RENDER_MODULE and FACTOIDAL_FONT_DATA to the actual built renderer and real font records.');
const engineModuleURL=pathToFileURL(modulePath).href;
direct.configureEngineModuleURL(engineModuleURL);
const nodeHost=new URL('./node-worker-host.mjs',import.meta.url);
const wireArgs=message=>JSON.parse(message.argumentsJSON);
const source='<style>body{font-size:16px;line-height:24px;margin:0}</style><p>Worker text</p><a style="display:block" href="https://example.test/target">Go onward</a>';
function real(t,{firstMode,options={},onSend=()=>{},onMessage=()=>{}}={}){
 const workers=[];let count=0;
 const engine=createEngine({...options,engineModuleURL,workerFactory:()=>{
  const worker=new Worker(nodeHost,{type:'module',workerData:{mode:count++===0?firstMode:undefined}});workers.push(worker);
  const post=worker.postMessage.bind(worker);worker.postMessage=message=>{onSend(message,worker);post(message);};worker.on('message',message=>onMessage(message,worker));return worker;
 }});
 t.after(async()=>{engine.dispose();await Promise.all(workers.map(worker=>worker.threadId===-1?undefined:once(worker,'exit')));});
 return{engine,workers,get count(){return count;}};
}

test('real Lean WASM worker preserves complete HTML and RDF artifacts',async t=>{
 const {engine}=real(t);
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));
 const rdf='<https://example.test/s> <https://example.test/p> "Worker" .';
 assert.deepEqual(await engine.compile(rdf,200,160,'ntriples'),await direct.compile(rdf,200,160,'ntriples'));
 assert.equal(engine.stats().pending,0);assert.equal(engine.stats().queuedBytes,0);
});
test('actual document inspection, commands, CSS and text-scale options cross worker unchanged',async t=>{
 const messages=[],{engine}=real(t,{onSend:message=>messages.push(message)});
 const html='<base href="./assets/"><link rel=stylesheet href="../style.css"><p id=message>Before</p>';
 const initial={url:'https://example.test/a/page.html'};
 const snapshot=await engine.inspectDocument(html,initial);assert.deepEqual(snapshot,await direct.inspectDocument(html,initial));
 const id=snapshot.nodes.find(node=>node.attributes.id==='message').id,link=snapshot.stylesheets[0].nodeId;
 const options={...initial,textScalePercent:150,commands:[{op:'setTextContent',nodeId:id,value:'After'}],resources:[{nodeId:link,source:'body{font-family:Arial;font-size:20px}'}]};
 assert.deepEqual(await engine.documentFontRequests(html,options),await direct.documentFontRequests(html,options));
 assert.equal(wireArgs(messages.find(message=>message.op==='documentFontRequests'))[1].textScalePercent,150);
 options.resources[0].source='body{font-family:monospace;font-size:20px}';
 assert.deepEqual(await engine.compileDocument(html,200,120,options),await direct.compileDocument(html,200,120,options));
 const controller=new AbortController();
 await engine.inspectDocument(html,initial,{signal:controller.signal,timeoutMs:2000});
 const wire=messages.at(-1);assert.equal(JSON.stringify(wire).includes('timeoutMs'),false);assert.equal(JSON.stringify(wire).includes('signal'),false);
 await assert.rejects(engine.compileDocument(html,200,120,{...options,resources:[]}),/missing/);
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120),'profile refusal must not poison worker');
});
test('actual supplied font data and aliases preserve canonical font scene',async t=>{
 const {engine}=real(t),fontData=await readFile(process.env.FACTOIDAL_FONT_DATA,'utf8');
 const family=JSON.parse(fontData)[0].family;assert.match(family,/^[A-Za-z0-9 _-]+$/);
 const html=`<style>body{font-family:'${family}';font-size:20px;line-height:28px}span{font-size:28px}</style><p>November2026 café <span>office</span> edited</p>`;
 const expected=await direct.compileWithFontData(html,fontData,420,100);
 assert.deepEqual(await engine.compileWithFontData(html,fontData,420,100),expected);
 assert.deepEqual(await engine.compileFont(html,JSON.parse(fontData),420,100),expected);
 assert.deepEqual(await engine.fontRequests(html),await direct.fontRequests(html));
});
test('Lean link/node picking retains only metadata and recovers original artifact after reset',async t=>{
 const messages=[],{engine}=real(t,{onSend:message=>messages.push(message)}),artifact=await engine.compile(source,200,120);
 const link=artifact.webRender.links[0],x=link[2]+link[4]/2,y=link[3]+link[5]/2;
 assert.deepEqual(await engine.hitLink(artifact,x,y),await direct.hitLink(artifact,x,y));
 assert('handle'in wireArgs(messages.at(-1))[0]);
 const ids=artifact.webRender.boxes.map(row=>row[0]);assert.deepEqual(await engine.hitNode(artifact,x,y,ids),await direct.hitNode(artifact,x,y,ids));
 assert.deepEqual(await engine.hitNode(artifact,x,y,new Set(ids)),await direct.hitNode(artifact,x,y,new Set(ids)));
 engine.abortPending('test recovery');
 assert.deepEqual(await engine.hitLink(artifact,x,y),await direct.hitLink(artifact,x,y));
 const reference=wireArgs(messages.at(-1))[0];assert(reference.metadata);assert.equal('data'in reference.metadata,false);assert.equal('wgsl'in reference.metadata,false);
 assert.equal(await engine.hitLink(artifact,NaN,0),null);
});
test('bounded retained metadata eviction re-registers without resending scene geometry',async t=>{
 const messages=[],{engine}=real(t,{onSend:message=>messages.push(message)}),first=await engine.compile(source,200,120);
 for(let index=0;index<9;index++)await engine.compile(source.replace('Worker text','Cache '+index),200,120);
 const link=first.webRender.links[0],x=link[2]+link[4]/2,y=link[3]+link[5]/2;
 assert.deepEqual(await engine.hitLink(first,x,y),await direct.hitLink(first,x,y));
 const hits=messages.filter(message=>message.op==='hitLink');assert.equal(hits.length,2);assert('handle'in wireArgs(hits[0])[0]);assert(wireArgs(hits[1])[0].metadata);
 assert.equal(JSON.stringify(hits[1]).includes('wgsl'),false);assert.equal('data'in wireArgs(hits[1])[0].metadata,false);
});
test('bounded queue rejects overload and timeout terminates a truly nonreturning worker',async t=>{
 let sawStarted=false;
 const lane=real(t,{firstMode:'nonreturning',options:{timeoutMs:250,maxQueue:2,maxQueuedBytes:4096},onMessage:message=>{if(message.type==='started')sawStarted=true;}}),{engine}=lane;
 const first=engine.compile(source,100,100),firstFailure=assert.rejects(first,error=>error.code==='TIMEOUT');
 await assert.rejects(engine.compile('x'.repeat(8192),100,100),error=>error.code==='QUEUE_FULL','byte overload rejects even while queue has room');
 const second=engine.compile(source,100,100),secondFailure=assert.rejects(second,error=>error.code==='TIMEOUT');
 await assert.rejects(engine.compile(source,100,100),error=>error.code==='QUEUE_FULL');
 await Promise.all([firstFailure,secondFailure]);assert(sawStarted,'nonreturning worker control never started');assert.equal(engine.stats().pending,0);assert.equal(engine.stats().queuedBytes,0);assert.equal(engine.stats().workerActive,false);
 assert.deepEqual(await engine.compile(source,200,120,'html',{timeoutMs:3000}),await direct.compile(source,200,120));assert.equal(lane.count,2);
});
test('queued signal cancellation removes only that call; active abort terminates worker and rejects its backlog',async t=>{
 const {engine}=real(t,{firstMode:'nonreturning',options:{timeoutMs:3000}}),first=engine.compile(source,100,100);
 const firstRejected=assert.rejects(first,error=>error.name==='AbortError');
 const queuedAbort=new AbortController(),queued=engine.compile(source,100,100,'html',{signal:queuedAbort.signal});
 const queuedRejected=assert.rejects(queued,error=>error.name==='AbortError');queuedAbort.abort('superseded queued request');await queuedRejected;
 assert.equal(engine.stats().pending,1);assert.equal(engine.stats().workerActive,true);
 const backlog=engine.compile(source,100,100),backlogRejected=assert.rejects(backlog,error=>error.name==='AbortError');
 engine.abortPending('Stop');await Promise.all([firstRejected,backlogRejected]);
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));
});
test('Stop interrupts real CPU-bound Lean WASM and next call recovers',async t=>{
 const controller=new AbortController();let armed=false,sawStarted=false;
 const {engine}=real(t,{onMessage:message=>{if(armed&&message.type==='started'){armed=false;sawStarted=true;setTimeout(()=>controller.abort('Stop during Lean execution'),10);}}});
 await engine.compile(source,100,100);armed=true;
 const began=Date.now(),input='<p>'+'A'.repeat(900000)+'</p>';
 await assert.rejects(engine.compile(input,200,100,'html',{signal:controller.signal,timeoutMs:3000}),error=>error.name==='AbortError');
 assert(sawStarted);assert(Date.now()-began<2000,'Stop did not promptly terminate CPU work');
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));
});
test('late replies from terminated generation and forged stale generation cannot resolve a new request',async t=>{
 class OldWorker extends EventEmitter{postMessage(message){this.message=message;}terminate(){this.terminated=true;return Promise.resolve(0);}}
 const old=new OldWorker();let calls=0,worker,latest;
 const engine=createEngine({engineModuleURL,timeoutMs:3000,workerFactory:()=>{
  if(calls++===0)return old;
  worker=new Worker(nodeHost,{type:'module',workerData:{}});const post=worker.postMessage.bind(worker);
  worker.postMessage=message=>{latest=message;post(message);};return worker;
 }});
 t.after(async()=>{engine.dispose();if(worker?.threadId!==-1)await once(worker,'exit');});
 const initial=engine.compile(source,100,100),rejected=assert.rejects(initial,error=>error.name==='AbortError');engine.abortPending('superseded');await rejected;assert(old.terminated);
 const fresh=engine.compile(source,200,120);
 old.emit('message',{protocol:1,type:'result',generation:old.message.generation,id:old.message.id,ok:true,value:{wrong:'late old worker'}});
 worker.emit('message',{protocol:1,type:'result',generation:old.message.generation,id:latest.id,ok:true,value:{wrong:'stale generation on current worker'}});
 assert.deepEqual(await fresh,await direct.compile(source,200,120));
});
test('worker factory failure and disposed transport fail explicitly without poisoning recovery',async t=>{
 let first=true;const workers=[];
 const engine=createEngine({engineModuleURL,timeoutMs:3000,workerFactory:()=>{if(first){first=false;throw Error('startup control');}const worker=new Worker(nodeHost,{type:'module',workerData:{}});workers.push(worker);return worker;}});
 t.after(async()=>{engine.dispose();await Promise.all(workers.map(worker=>worker.threadId===-1?undefined:once(worker,'exit')));});
 await assert.rejects(engine.compile(source,100,100),/startup control/);
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));engine.dispose();
 await assert.rejects(engine.compile(source,100,100),error=>error.code==='DISPOSED');
});

test('module initialization failure terminates poisoned worker and later same-URL startup recovers',async t=>{
 const directory=await mkdtemp(join(tmpdir(),'renderer-module-recovery-')),moduleFile=join(directory,'module.mjs'),workers=[];
 const engine=createEngine({engineModuleURL:pathToFileURL(moduleFile).href,timeoutMs:3000,workerFactory:()=>{const worker=new Worker(nodeHost,{type:'module',workerData:{}});workers.push(worker);return worker;}});
 t.after(async()=>{engine.dispose();await Promise.all(workers.map(worker=>worker.threadId===-1?undefined:once(worker,'exit')));await rm(directory,{recursive:true,force:true});});
 await assert.rejects(engine.compile(source,100,100),/initialization failed/);assert.equal(engine.stats().workerActive,false);
 await writeFile(moduleFile,`export {default} from ${JSON.stringify(engineModuleURL)};\n`);
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));assert.equal(workers.length,2);
});

test('queued data is an immutable byte-accounted snapshot, not a mutable caller reference',async t=>{
 const messages=[],{engine}=real(t,{onSend:message=>messages.push(message)});
 const first=engine.compile(source,100,100),html='<style>body{font-family:Arial;font-size:20px}</style><p>Snapshot</p>',options={textScalePercent:150};
 const queued=engine.documentFontRequests(html,options);options.textScalePercent=999;
 await first;assert.deepEqual(await queued,await direct.documentFontRequests(html,{textScalePercent:150}));
 assert.equal(wireArgs(messages.find(message=>message.op==='documentFontRequests'))[1].textScalePercent,150);
});
test('a queued deadline removes only that call while active CPU work remains terminable',async t=>{
 const {engine}=real(t,{firstMode:'nonreturning',options:{timeoutMs:3000}}),first=engine.compile(source,100,100),stopped=assert.rejects(first,error=>error.name==='AbortError');
 await assert.rejects(engine.compile(source,100,100,'html',{timeoutMs:50}),error=>error.code==='TIMEOUT');
 assert.equal(engine.stats().pending,1);assert.equal(engine.stats().workerActive,true);engine.abortPending('Stop');await stopped;
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));
});
test('aggregate argument bytes apply independently of request count and individual request size',async t=>{
 const {engine}=real(t,{firstMode:'nonreturning',options:{timeoutMs:3000,maxQueue:8,maxQueuedBytes:1024}}),first=engine.compile('A'.repeat(500),100,100),stopped=assert.rejects(first,error=>error.name==='AbortError');
 await assert.rejects(engine.compile('B'.repeat(600),100,100),error=>error.code==='QUEUE_FULL');
 assert.equal(engine.stats().pending,1);engine.abortPending('Stop');await stopped;
 assert.deepEqual(await engine.compile(source,200,120),await direct.compile(source,200,120));
});
