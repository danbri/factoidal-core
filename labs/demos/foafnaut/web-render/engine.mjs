// The foreground transfers bounded data only. Lean execution lives in a
// terminable worker, including HTML/CSS, font-data validation and hit testing.
const workerURL=new URL('./engine-worker.mjs',import.meta.url);
const defaultModuleURL=new URL('/lab/.build/web-render/engines/web-render.mjs',import.meta.url).href;
const encoder=new TextEncoder();
const abortError=reason=>Object.assign(new Error(reason instanceof Error?reason.message:String(reason??'Renderer operation aborted')),{name:'AbortError',code:'ABORTED'});
const fault=(message,code='RENDERER_ERROR')=>Object.assign(new Error(message),{code});
const bound=(value,min,max,name)=>{if(!Number.isInteger(value)||value<min||value>max)throw new RangeError(`Invalid ${name}`);return value;};

export function createEngine({workerFactory=()=>new Worker(workerURL,{type:'module'}),engineModuleURL=defaultModuleURL,
 timeoutMs=30000,maxQueue=8,maxQueuedBytes=24*1024*1024}={}){
 bound(timeoutMs,1,120000,'renderer timeout');bound(maxQueue,1,64,'renderer queue bound');bound(maxQueuedBytes,1024,64*1024*1024,'renderer byte bound');
 if(typeof engineModuleURL!=='string'||engineModuleURL.length>4096)throw new TypeError('Invalid renderer module URL');
 let worker,active,queue=[],generation=0,nextId=0,queuedBytes=0,disposed=false;
 const artifacts=new WeakMap();
 function finish(job,error,packet){
  if(job.settled)return;job.settled=true;clearTimeout(job.timer);job.signal?.removeEventListener('abort',job.abort);
  queuedBytes-=job.bytes;error?job.reject(error):job.resolve(packet);
 }
 function reset(error){
  const old=worker;worker=undefined;generation++;
  const jobs=[...(active?[active]:[]),...queue];active=undefined;queue=[];
  for(const job of jobs)finish(job,error);
  if(old)try{Promise.resolve(old.terminate()).catch(()=>{});}catch{}
 }
 function receive(message,owner){
  if(owner!==worker||!active||!message||message.protocol!==1||message.generation!==generation||message.id!==active.id)return;
  if(message.type==='started')return;
  if(message.type!=='result'||typeof message.ok!=='boolean'){reset(fault('Invalid renderer worker reply','WORKER_PROTOCOL'));return;}
  const job=active;
  if(!message.ok&&message.fatal){reset(fault(message.error?.message??'Renderer worker failed','WORKER_FAILED'));return;}
  active=undefined;
  if(message.ok)finish(job,null,{value:message.value,artifactHandle:message.artifactHandle,generation});
  else finish(job,Object.assign(new Error(message.error?.message??'Renderer request failed'),{name:message.error?.name??'Error',code:message.error?.code??'RENDERER_ERROR'}));
  pump();
 }
 function start(){
  const owner=workerFactory();worker=owner;generation++;
  const failed=error=>{if(owner===worker)reset(fault(error?.message??'Renderer worker failed','WORKER_FAILED'));};
  if(typeof owner.addEventListener==='function'){
   owner.addEventListener('message',event=>receive(event.data,owner));
   owner.addEventListener('error',event=>{event.preventDefault?.();failed(event);});
   owner.addEventListener('messageerror',()=>failed(Error('Renderer message could not be decoded')));
  }else{
   owner.on('message',message=>receive(message,owner));owner.on('error',failed);
   owner.on('messageerror',()=>failed(Error('Renderer message could not be decoded')));
   owner.on('exit',code=>failed(Error(`Renderer worker exited (${code})`)));
  }
 }
 function pump(){
  if(active||!queue.length||disposed)return;
  active=queue.shift();
  try{if(!worker)start();worker.postMessage({protocol:1,generation,id:active.id,op:active.op,argumentsJSON:active.argumentsJSON,engineModuleURL});}
  catch(error){reset(fault(error.message,'WORKER_START'));}
 }
 function request(op,args,{signal,timeoutMs:limit=timeoutMs}={}){
  if(disposed)return Promise.reject(fault('Renderer is disposed','DISPOSED'));
  try{bound(limit,1,120000,'renderer timeout');if(signal&&typeof signal.addEventListener!=='function')throw new TypeError('Invalid renderer abort signal');}
  catch(error){return Promise.reject(error);}
  if(signal?.aborted)return Promise.reject(abortError(signal.reason));
  let argumentsJSON,bytes;try{argumentsJSON=JSON.stringify(args);bytes=encoder.encode(argumentsJSON).length;}catch(error){return Promise.reject(error);}
  if(queue.length+(active?1:0)>=maxQueue||bytes>maxQueuedBytes-queuedBytes)return Promise.reject(fault('Renderer queue or byte bound exceeded','QUEUE_FULL'));
  return new Promise((resolve,reject)=>{
   const job={id:++nextId,op,argumentsJSON,bytes,signal,resolve,reject,settled:false};queuedBytes+=bytes;
   job.abort=()=>{
    const error=abortError(signal.reason);
    if(job===active)reset(error);else{queue=queue.filter(item=>item!==job);finish(job,error);pump();}
   };
   job.timer=setTimeout(()=>{
    const error=fault('Renderer operation timed out; worker terminated','TIMEOUT');
    if(job===active)reset(error);else{queue=queue.filter(item=>item!==job);finish(job,error);}
   },limit);
   signal?.addEventListener('abort',job.abort,{once:true});queue.push(job);pump();
  });
 }
 function remember(packet){
  if(packet.value&&typeof packet.value==='object'&&packet.artifactHandle!==undefined)artifacts.set(packet.value,{generation:packet.generation,handle:packet.artifactHandle});
  return packet.value;
 }
 async function render(op,args,control){return remember(await request(op,args,control));}
 const metadata=artifact=>({width:artifact.width,height:artifact.height,webRender:{links:artifact.webRender?.links??[],boxes:artifact.webRender?.boxes??[]}});
 async function hit(op,artifact,args,control){
  let entry=artifacts.get(artifact);
  const reference=entry?.generation===generation?{handle:entry.handle}:{metadata:metadata(artifact)};
  let packet;
  try{packet=await request(op,[reference,...args],control);}
  catch(error){if(error.code!=='ARTIFACT_EXPIRED'||control?.signal?.aborted)throw error;packet=await request(op,[{metadata:metadata(artifact)},...args],control);}
  if(packet.artifactHandle!==undefined)artifacts.set(artifact,{generation:packet.generation,handle:packet.artifactHandle});
  return packet.value;
 }
 const api={
  compile:(source,width,height,syntax='html',control)=>render('compile',[source,width,height,syntax],control),
  compileWithFontData:(source,fontData,width,height,control)=>render('compileWithFontData',[source,fontData,width,height],control),
  inspectDocument:async(source,options={},control)=>(await request('inspectDocument',[source,options],control)).value,
  documentFontRequests:async(source,options={},control)=>(await request('documentFontRequests',[source,options],control)).value,
  compileDocument:(source,width,height,options={},control)=>render('compileDocument',[source,width,height,options],control),
  fontRequests:(source,control)=>api.documentFontRequests(source,{},control),
  compileFont:(source,data,width,height,control)=>api.compileWithFontData(source,typeof data==='string'?data:JSON.stringify(data),width,height,control),
  hitLink:(artifact,x,y,control)=>!Number.isFinite(x)||!Number.isFinite(y)?Promise.resolve(null):hit('hitLink',artifact,[x,y],control),
  async hitNode(artifact,x,y,ids,control){
   if(!Number.isFinite(x)||!Number.isFinite(y))return null;
   if(ids!=null&&typeof ids[Symbol.iterator]!=='function')throw new TypeError('Node handles must be iterable');
   return hit('hitNode',artifact,[x,y,Array.from(ids??[])],control);
  },
  abortPending:reason=>reset(abortError(reason)),
  dispose(){if(disposed)return;disposed=true;reset(abortError('Renderer disposed'));},
  stats:()=>({generation,pending:queue.length+(active?1:0),queuedBytes,workerActive:!!worker,disposed})
 };
 return api;
}
let shared;
const instance=()=>shared??=createEngine();
export const compile=(...args)=>instance().compile(...args);
export const compileWithFontData=(...args)=>instance().compileWithFontData(...args);
export const inspectDocument=(...args)=>instance().inspectDocument(...args);
export const documentFontRequests=(...args)=>instance().documentFontRequests(...args);
export const compileDocument=(...args)=>instance().compileDocument(...args);
export const fontRequests=(...args)=>instance().fontRequests(...args);
export const compileFont=(...args)=>instance().compileFont(...args);
export const hitLink=(...args)=>instance().hitLink(...args);
export const hitNode=(...args)=>instance().hitNode(...args);
export const abortPending=reason=>shared?.abortPending(reason);
export const dispose=()=>{shared?.dispose();shared=undefined;};
