const engineURL=new URL(self.location.href).searchParams.get('engine')??'https://cdn.jsdelivr.net/npm/@factoidal/core@0.29.0/browser.js';
const corePromise=import(engineURL).then(async core=>{
  await core.ready();
  if(core.version!=='0.29.0'&&!(await core.engineTables()).queryOutputs.includes('xml-report'))throw new Error(`This demo requires published core 0.29.0; loaded ${core.version}.`);
  return core;
});
import { runPipeline } from './pipeline.mjs';
import { createStorageHandler } from './storage-worker.mjs';
const storage=createStorageHandler(()=>corePromise);
let busy = false;
self.onmessage = async ({data}) => {
  if(data.type==='storage'){
    if(busy){self.postMessage({type:'storage-result',id:data.id,error:'The worker is busy. Try again after the flow completes.'});return;}
    busy=true;
    try{self.postMessage({type:'storage-result',id:data.id,result:await storage(data.operation,data.args)});}
    catch(error){self.postMessage({type:'storage-result',id:data.id,error:error.message||String(error)});}
    finally{busy=false;}return;
  }
  if (data.type !== 'run') return;
  if(busy){self.postMessage({type:'error',message:'The worker is busy with a pod operation.'});return;}
  busy = true;
  try {
    const core=await corePromise;
    const result = await runPipeline(core, data.inputs, stage => self.postMessage({type:'stage',stage}));
    self.postMessage({type:'complete',result});
  } catch (error) {
    self.postMessage({type:'error',message:error.message || String(error),stack:error.stack});
  } finally { busy = false; }
};
