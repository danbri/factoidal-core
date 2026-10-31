const engineURL=new URL(self.location.href).searchParams.get('engine')??'https://cdn.jsdelivr.net/npm/@factoidal/core@0.27.0/browser.js';
const corePromise=import(engineURL).then(async core=>{
  await core.ready();
  if(core.version!=='0.27.0'&&!(await core.engineTables()).queryOutputs.includes('xml-report'))throw new Error(`This demo requires published core 0.27.0; loaded ${core.version}.`);
  return core;
});
import { runPipeline } from './pipeline.mjs';
let busy = false;
self.onmessage = async ({data}) => {
  if (data.type !== 'run' || busy) return;
  busy = true;
  try {
    const core=await corePromise;
    const result = await runPipeline(core, data.inputs, stage => self.postMessage({type:'stage',stage}));
    self.postMessage({type:'complete',result});
  } catch (error) {
    self.postMessage({type:'error',message:error.message || String(error),stack:error.stack});
  } finally { busy = false; }
};
