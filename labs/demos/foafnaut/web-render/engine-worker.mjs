// Only this worker imports the Lean ABI implementation. Terminating this
// worker interrupts synchronous WASM, which cannot receive a cancel message.
import * as core from './engine-core.mjs';
const allowed=new Set(['compile','compileWithFontData','inspectDocument','documentFontRequests','compileDocument','hitLink','hitNode']);
const encoder=new TextEncoder(),artifacts=new Map();
let busy=false,nextHandle=0,artifactBytes=0;
const MAX_INPUT=24*1024*1024,MAX_CACHE=8*1024*1024,MAX_ARTIFACTS=8;
function retain(artifact){
 const metadata={width:artifact.width,height:artifact.height,webRender:{links:artifact.webRender?.links??[],boxes:artifact.webRender?.boxes??[]}};
 const bytes=encoder.encode(JSON.stringify(metadata)).length;
 if(bytes>MAX_CACHE)return undefined;
 while(artifacts.size&&(artifacts.size>=MAX_ARTIFACTS||artifactBytes+bytes>MAX_CACHE)){
  const first=artifacts.keys().next().value;artifactBytes-=artifacts.get(first).bytes;artifacts.delete(first);
 }
 const handle=++nextHandle;artifacts.set(handle,{metadata,bytes});artifactBytes+=bytes;return handle;
}
function resolveArtifact(reference){
 if(reference?.metadata){const artifact=reference.metadata;return{artifact,handle:retain(artifact)};}
 const entry=artifacts.get(reference?.handle);
 if(!entry)throw Object.assign(Error('Retained renderer artifact expired'),{code:'ARTIFACT_EXPIRED'});
 artifacts.delete(reference.handle);artifacts.set(reference.handle,entry);
 return{artifact:entry.metadata,handle:reference.handle};
}
async function execute(message){
 if(!message||message.protocol!==1||!Number.isSafeInteger(message.id)||message.id<1||!Number.isSafeInteger(message.generation)||message.generation<1||!allowed.has(message.op)||typeof message.argumentsJSON!=='string')throw Error('Invalid renderer worker request');
 if(encoder.encode(message.argumentsJSON).length>MAX_INPUT)throw Error('Renderer input byte bound exceeded');
 const args=JSON.parse(message.argumentsJSON);if(!Array.isArray(args))throw Error('Invalid renderer worker arguments');
 core.configureEngineModuleURL(message.engineModuleURL);
 globalThis.postMessage({protocol:1,type:'started',generation:message.generation,id:message.id});
 if(message.op==='hitLink'||message.op==='hitNode'){
  const [reference,...parameters]=args,{artifact,handle}=resolveArtifact(reference);
  return{value:await core[message.op](artifact,...parameters),artifactHandle:handle};
 }
 const value=await core[message.op](...args);
 return{value,...(['compile','compileWithFontData','compileDocument'].includes(message.op)?{artifactHandle:retain(value)}:{})};
}
globalThis.onmessage=async event=>{
 const message=event.data;
 const reply=payload=>globalThis.postMessage({protocol:1,type:'result',generation:message?.generation,id:message?.id,...payload});
 if(busy){reply({ok:false,error:{message:'Concurrent renderer worker calls are not supported'}});return;}
 busy=true;
 try{
  reply({ok:true,...await execute(message)});
 }catch(error){reply({ok:false,fatal:error instanceof WebAssembly.RuntimeError||error.code==='INITIALIZATION_FAILED',error:{name:error.name,message:String(error.message??error).slice(0,4096),code:error.code}});}
 finally{busy=false;}
};
