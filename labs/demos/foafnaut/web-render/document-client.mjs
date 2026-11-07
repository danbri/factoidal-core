// Resource orchestration only. Lean owns discovery, URL/base semantics, DOM
// commands, CSS, font request generation, layout and event containment.
import {fetchResource} from './resource-client.mjs';
import {createScriptSession} from './script-engine/session.mjs';

const identity=descriptor=>JSON.stringify([descriptor.nodeId,descriptor.url]);
const wire=record=>({nodeId:record.nodeId,source:record.source,url:record.url,requestedURL:record.requestedURL});
// Bytes pass through as text. Decoding, and all that follows from it, is in Lean.
const base64=bytes=>{let text='';for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));return btoa(text);};

export async function prepareDocument(engine,html,{url,signal,onLog=()=>{}}={}){
 const options={url,resources:[],commands:[]},lifetime=new AbortController();
 let scripts,listeners=[],closed=false,baseURL=url,sheets=new Map(),refreshSequence=0,refreshAbort,mutationVersion=0;
 const operationSignal=signal=>signal?AbortSignal.any([lifetime.signal,signal]):lifetime.signal;
 const check=signal=>{if(closed)throw Error('Document is no longer active');signal.throwIfAborted();};
 const close=()=>{closed=true;lifetime.abort();refreshAbort?.abort();scripts?.reset();};
 const logs=batch=>{for(const value of batch.logs)onLog({type:'script-console',value});};

 async function load(descriptors,previous,signal){
  if(descriptors.length>64)throw Error('Document resource count exceeds 64');
  const result=new Map(),ids=new Set();let totalBytes=0;
  for(const descriptor of descriptors){
   check(signal);
   if(ids.has(descriptor.nodeId))throw Error('Duplicate Lean resource node');ids.add(descriptor.nodeId);
   const key=identity(descriptor);let record=previous.get(key);
   if(!record){
    const resource=await fetchResource(descriptor.url,{signal});check(signal);
    record={nodeId:descriptor.nodeId,requestedURL:descriptor.url,url:resource.url,source:resource.text(),bytes:resource.bytes.length};
   }
   totalBytes+=record.bytes;if(totalBytes>4194304)throw Error('Document resources exceed 4 MiB');
   result.set(key,record);
  }
  return result;
 }

 // The same broker and limits as a stylesheet: HTTP and HTTPS only, no credentials.
 const images=new Map();
 async function loadImages(descriptors,signal){
  if(descriptors.length>64)throw Error('Document image count exceeds 64');
  const result=[];let totalBytes=0;
  for(const {key,url}of descriptors){
   check(signal);
   let record=images.get(url);
   if(!record){const resource=await fetchResource(url,{signal});check(signal);record={key,base64:base64(resource.bytes),bytes:resource.bytes.length};images.set(url,record);}
   totalBytes+=record.bytes;if(totalBytes>4194304)throw Error('Document images exceed 4 MiB');
   result.push({key,base64:record.base64});
  }
  return result;
 }

 async function refresh(signal){
  const request=++refreshSequence;refreshAbort?.abort();refreshAbort=new AbortController();
  signal=AbortSignal.any([operationSignal(signal),refreshAbort.signal]);check(signal);
  // Old records may now refer to disconnected nodes or links whose rel changed.
  // Discovery therefore inspects the commanded DOM with no supplied resources.
  const snapshot=await engine.inspectDocument(html,{...options,resources:[]},{signal});check(signal);
  const next=await load(snapshot.stylesheets??[],sheets,signal);check(signal);
  const nextImages=await loadImages(snapshot.images??[],signal);check(signal);
  if(request!==refreshSequence)throw Error('Superseded resource refresh');
  options.images=nextImages;
  sheets=next;options.resources=Array.from(next.values(),wire);baseURL=snapshot.baseURL??url;
  return request;
 }

 try{
  const initialSignal=operationSignal(signal);check(initialSignal);
  const snapshot=await engine.inspectDocument(html,options,{signal:initialSignal});check(initialSignal);
  if((snapshot.scripts??[]).some(script=>script.kind==='module'))throw Error('Module scripts are not supported by this browser profile');
  const classic=(snapshot.scripts??[]).filter(script=>script.kind==='classic');
  const descriptors=[...(snapshot.stylesheets??[]),...classic.filter(script=>script.src)];
  const initial=await load(descriptors,new Map(),initialSignal);
  sheets=new Map((snapshot.stylesheets??[]).map(descriptor=>[identity(descriptor),initial.get(identity(descriptor))]));
  options.resources=Array.from(sheets.values(),wire);baseURL=snapshot.baseURL??url;
  options.images=await loadImages(snapshot.images??[],initialSignal);
  const sources=classic.map(script=>script.src?initial.get(identity(script))?.source:script.source);
  if(sources.some(source=>typeof source!=='string'))throw Error('Missing Lean-requested script resource');
  if(sources.length){
   scripts=createScriptSession();const abort=()=>scripts.reset();initialSignal.addEventListener('abort',abort,{once:true});
   try{
    const batch=await scripts.start({nodes:snapshot.nodes,sources,budgetMs:100,
     document:{source:html,url,commands:options.commands.slice()}});check(initialSignal);
    options.commands.push(...batch.commands);mutationVersion++;listeners=batch.listeners;logs(batch);
   }finally{initialSignal.removeEventListener('abort',abort);}
  }
  // Initial scripts can change base/href/rel/media/disabled before first paint.
  // Script resources are no longer needed by Lean; only active CSS survives.
  await refresh(initialSignal);
 }catch(error){close();throw error;}

 return {html,url,options,
  get baseURL(){return baseURL;},
  get listeners(){return listeners;},
  close,
  async dispatch(nodeId,{signal}={}){
   signal=operationSignal(signal);check(signal);if(!scripts)throw Error('Script document is no longer active');
   const batch=await scripts.dispatch({type:'click',nodeId});check(signal);
   if(options.commands.length+batch.commands.length>4096)throw Error('Document DOM command history exceeds 4096');
   options.commands.push(...batch.commands);mutationVersion++;listeners=batch.listeners;logs(batch);
   await refresh(signal);
   return {defaultPrevented:batch.defaultPrevented===true};
  },
  async compile(width,height,{signal,textScalePercent=100}={}){
   signal=operationSignal(signal);check(signal);
   const request=await refresh(signal),version=mutationVersion;
   const prepared={...options,commands:options.commands.slice(),resources:options.resources.slice(),textScalePercent};
   const requests=await engine.documentFontRequests(html,prepared,{signal});check(signal);
   if(requests.error)throw Error(requests.error);
   let fontData;
   if(requests.requests?.length){
    const response=await fetch('/font-data',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(requests),signal});
    if(!response.ok)throw Error(await response.text());fontData=await response.json();
   }
   check(signal);
   if(request!==refreshSequence||version!==mutationVersion)throw Error('Superseded document compilation');
   return engine.compileDocument(html,width,height,{...prepared,...(fontData?{fontData}:{})},{signal});
  }
 };
}
