// Resource orchestration only. Lean owns discovery, URL/base semantics, DOM
// commands, CSS, font request generation, layout and event containment.
import {fetchResource} from './resource-client.mjs';
import {createScriptSession} from './script-engine/session.mjs';

export async function prepareDocument(engine,html,{url,signal,onLog=()=>{}}={}){
 const options={url,resources:[],commands:[]};
 const first=await engine.inspectDocument(html,options);
 if((first.scripts??[]).some(script=>script.kind==='module'))throw Error('Module scripts are not supported by this browser profile');
 const resources=[...(first.stylesheets??[]),...(first.scripts??[]).filter(script=>script.kind==='classic'&&script.src)];
 if(resources.length>64)throw Error('Document resource count exceeds 64');
 let resourceBytes=0;
 // Bounded sequential work. Lean later applies CSS in document source order.
 for(const descriptor of resources){
  signal?.throwIfAborted();
  const resource=await fetchResource(descriptor.url,{signal});resourceBytes+=resource.bytes.length;
  if(resourceBytes>4194304)throw Error('Document resources exceed 4 MiB');
  options.resources.push({nodeId:descriptor.nodeId,source:resource.text(),url:resource.url});
 }
 signal?.throwIfAborted();
 const snapshot=await engine.inspectDocument(html,options);
 let scripts,listeners=[];
 const scriptResources=new Map(options.resources.map(resource=>[resource.nodeId,resource.source]));
 const sources=(snapshot.scripts??[]).filter(script=>script.kind==='classic').map(script=>script.src?scriptResources.get(script.nodeId):script.source);
 if(sources.some(source=>typeof source!=='string'))throw Error('Missing Lean-requested script resource');
 if(sources.length){
  scripts=createScriptSession();
  const abort=()=>scripts.reset();signal?.addEventListener('abort',abort,{once:true});
  try{
   const batch=await scripts.start({nodes:snapshot.nodes,sources,budgetMs:100});
   signal?.throwIfAborted();options.commands.push(...batch.commands);listeners=batch.listeners;
   for(const value of batch.logs)onLog({type:'script-console',value});
  }catch(error){scripts.reset();throw error;}
  finally{signal?.removeEventListener('abort',abort);}
 }
 let closed=false;
 return {html,url,baseURL:snapshot.baseURL??url,options,
  get listeners(){return listeners;},
  close(){closed=true;scripts?.reset();},
  async dispatch(nodeId){
   if(closed||!scripts)throw Error('Script document is no longer active');
   const batch=await scripts.dispatch({type:'click',nodeId});
   if(options.commands.length+batch.commands.length>4096)throw Error('Document DOM command history exceeds 4096');
   options.commands.push(...batch.commands);listeners=batch.listeners;
   for(const value of batch.logs)onLog({type:'script-console',value});
  },
  async compile(width,height,{signal}={}){
   if(closed)throw Error('Document is no longer active');signal?.throwIfAborted();
   const requests=await engine.documentFontRequests(html,options);
   if(requests.error)throw Error(requests.error);
   let fontData;
   if(requests.requests?.length){
    const response=await fetch('/font-data',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(requests),signal});
    if(!response.ok)throw Error(await response.text());fontData=await response.json();
   }
   signal?.throwIfAborted();
   return engine.compileDocument(html,width,height,{...options,...(fontData?{fontData}:{})});
  }
 };
}
