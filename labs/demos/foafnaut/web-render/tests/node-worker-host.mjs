// Node-only test host for the unmodified browser worker protocol.
import {parentPort,workerData} from 'node:worker_threads';
globalThis.postMessage=message=>parentPort.postMessage(message);
if(workerData.mode==='nonreturning'){
 parentPort.on('message',message=>{
  postMessage({protocol:1,type:'started',generation:message.generation,id:message.id});
  for(;;){} // Only the parent's Worker.terminate() can interrupt this control.
 });
}else{
 await import(new URL('../engine-worker.mjs',import.meta.url));
 parentPort.on('message',data=>globalThis.onmessage({data}));
}
