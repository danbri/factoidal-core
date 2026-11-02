// The worker keeps Lean compilation and GPU readback off the editing thread.
import {compile,hitLink} from './engine.mjs';
let current;
self.onmessage=async({data})=>{
 if(data.type==='hit'){
  try{const target=current?.id===data.frameId?await hitLink(current.artifact,data.x,data.y):null;self.postMessage({type:'hit',id:data.id,target});}
  catch(error){self.postMessage({type:'hit',id:data.id,error:String(error.message??error)});}return;
 }
 if(data.type!=='render')return;
 let session;
 try{
  if(!navigator.gpu)throw Error('This browser does not provide WebGPU. Use a browser with WebGPU enabled.');
  const start=performance.now(),artifact=await compile(data.source,data.width,data.height),compiled=performance.now();
  const {createOffscreenSession}=await import('./runtime/gpu-transport.mjs');
  session=await createOffscreenSession(artifact,'svg-offscreen');if(!session)throw Error('A WebGPU adapter is unavailable in this browser.');
  const ready=performance.now(),rgba=await session.draw(),finished=performance.now();
  current={id:data.id,artifact};
  self.postMessage({type:'frame',id:data.id,artifact,rgba:rgba.buffer,timing:{compileMs:compiled-start,gpuSetupMs:ready-compiled,drawReadbackMs:finished-ready}},[rgba.buffer]);
 }catch(error){current=undefined;self.postMessage({type:'error',id:data.id,error:String(error.message??error)});}
 finally{session?.close();}
};
