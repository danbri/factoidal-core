// The page's side of the shared engine (engine-worker.mjs): one worker for the page, started on
// the first request, so that a page that loads this module and asks nothing pays nothing.
let worker,serial=0,startedAt;
const waiting=new Map();

function start(){
  if(worker)return worker;
  startedAt=performance.now();
  worker=new Worker(new URL('./engine-worker.mjs',import.meta.url),{type:'module'});
  worker.onmessage=({data})=>{
    const entry=waiting.get(data.id);if(!entry)return;
    waiting.delete(data.id);
    if(data.error!==undefined)entry.reject(Error(data.error));else entry.resolve(data.result);
  };
  worker.onerror=event=>{
    const error=Error(`the engine's worker failed: ${event.message??'no reason given'}`);
    for(const entry of waiting.values())entry.reject(error);
    waiting.clear();worker=undefined;
  };
  return worker;
}
function request(op,...args){
  const w=start(),id=++serial;
  return new Promise((resolve,reject)=>{waiting.set(id,{resolve,reject});w.postMessage({id,op,args});});
}

/** Whether the engine has been asked for yet, and when (performance.now()). */
export const engineState=()=>({started:!!worker,startedAt});
/** Start the engine without a view: its counters (engine and font ms, drawing: gpu, cpu or none). */
export const ready=()=>request('ready');
/** Lay out and draw `input` (a URL of this site, or HTML) in view `id`. */
export const open=(id,input,options)=>request('open',id,input,options);
/** Lay out `input` in view `id` and map it to Textnaut's text grid. */
export const textGrid=(id,input,options)=>request('textGrid',id,input,options);
/** A click at CSS pixel (x, y) of view `id`: to its scripts, or the link there. */
export const click=(id,x,y)=>request('click',id,x,y);
export const linkAt=(id,x,y)=>request('linkAt',id,x,y);
export const close=id=>request('close',id);
/** Check view `id`'s text grid against the engine's own pixels (see engine-core.mjs gridCheck). */
export const gridCheck=id=>request('gridCheck',id);
