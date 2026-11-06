import {runSignatureDemo} from './pipeline.mjs';
import {createStorageHandler} from '../data-compositor/storage-worker.mjs';
const engineURL=new URL(self.location.href).searchParams.get('engine')??new URL('../../../npm/factoidal/browser.js',self.location.href).href;
const corePromise=import(engineURL).then(async core=>{await core.ready();return core;});
const storage=createStorageHandler(()=>corePromise);
let busy=false;
self.onmessage=async({data})=>{
  if(!['run','storage'].includes(data.type))return;
  if(busy){self.postMessage(data.type==='storage'?{type:'storage-result',id:data.id,error:'Worker busy.'}:{type:'error',message:'Worker busy.'});return;}
  busy=true;
  try{
    const core=await corePromise;
    if(data.type==='storage')self.postMessage({type:'storage-result',id:data.id,result:await storage(data.operation,data.args)});
    else self.postMessage({type:'complete',result:{...await runSignatureDemo({engine:await core.loadEngine(),...data.inputs}),coreVersion:core.version}});
  }catch(error){self.postMessage(data.type==='storage'?{type:'storage-result',id:data.id,error:error.message}:{type:'error',message:error.message});}
  finally{busy=false;}
};
