// Main-thread side of native_html_worker.ts. Calls answer promises, so the event loop
// keeps pumping. Calls are FIFO within their priority lane (gesture, input, ordinary, low). A worker that fails to start or dies
// rejects its calls; the caller decides what to do and says so in the trace.
import type {HTMLArtifact,HTMLLayers} from "./native_html_engine.ts";
import {REMOTE_CALLS,type RemoteCall} from "./native_html_calls.ts";
import type {WorkerReply,WorkerRequest} from "./native_html_worker.ts";
import type {PageFonts} from "./native_html_fonts.ts";
import {attachLayout} from "./native_html_layout.ts";

export type CompileClient={
  call(name:RemoteCall,...args:unknown[]):Promise<{value:unknown;workerMs:number}>;
  /** Input runs before ordinary work; scriptSession calls always share this FIFO. */
  inputCall(name:RemoteCall,...args:unknown[]):Promise<{value:unknown;workerMs:number}>;
  /** A desktop gesture's read of the page as it is now (issue 1031): it runs right after the
   * call that is running, before queued script turns and renders. Never a scriptSession call. */
  gestureCall(name:RemoteCall,...args:unknown[]):Promise<{value:unknown;workerMs:number}>;
  /** `gesture`: the frame shows a gesture's answer (a selection, a menu): the gesture lane. */
  compile(source:string,width:number,height:number,options:Record<string,unknown>,gesture?:boolean):Promise<{artifact:HTMLArtifact;workerMs:number}>;
  compileLayers(source:string,width:number,height:number,options:Record<string,unknown>,gesture?:boolean):Promise<{layers:HTMLLayers;workerMs:number}>;
  /** A layers render at low priority (a scroll prefetch): it runs when no other call waits,
   * and a newer one replaces it while it has not started. Undefined when it was dropped. */
  prefetchLayers(source:string,width:number,height:number,options:Record<string,unknown>):Promise<{layers:HTMLLayers;workerMs:number}|undefined>;
  /** The fallback fonts a page needs, chosen and loaded in the worker, before later calls. */
  pageFonts(source:string):Promise<PageFonts&{workerMs:number}>;
  /** The serif face (serif_font.ts), loaded in the worker, before later calls. */
  serifFont(path:string,family:string):Promise<{value:unknown;workerMs:number}>;
  /** The monospace face (serif_font.ts), loaded in the worker, before later calls. */
  monoFont(path:string,family:string):Promise<{value:unknown;workerMs:number}>;
  /** Drop the low-priority call that has not started, if there is one. */
  dropLow():void;
  /** Ordinary and input calls sent and not yet answered. */
  readonly pending:number;
  /** Every message sent to the worker and not yet answered (prefetches and fonts too). */
  readonly inFlight:number;
  /** The engine methods that run in the worker, as promise-returning functions. */
  engine:Record<RemoteCall,(...args:unknown[])=>Promise<unknown>>;
  readonly alive:boolean;
  /** The engine uses an engine session of its own in a library that other workers share
   * (docs/designissues/2026-11-26-foafnaut-engine-sessions.md); false with its own copy, Wasm,
   * or an engine from before sessions. */
  readonly session?:boolean;
  /** "task": the engine is a session on its own Lean task, called from this thread
   * (native_engine_tasks.ts); "pooled": such a session, called from a host worker that serves
   * many tabs (native_engine_pool.ts); otherwise an engine worker. */
  readonly kind?:"worker"|"task"|"pooled";
  terminate():void;
};
/** How long a worker with a session may take to free it and close after `terminate` (its call
 * in progress runs to its end) before the worker is stopped. */
const END_GRACE_MS=30000;
export async function startCompileWorker(font?:{path:string;family:string},nativeEngine?:string,logAll=false,session=false):Promise<CompileClient> {
  const worker=new Worker(new URL("./native_html_worker.ts",import.meta.url),{type:"module"});
  const pending=new Map<number,{resolve:(reply:WorkerReply)=>void;reject:(error:Error)=>void}>();
  let next=0,alive=true,ordinary=0;
  const fail=(error:Error)=>{alive=false;for(const p of pending.values())p.reject(error);pending.clear();};
  worker.onmessage=event=>{const reply=event.data as WorkerReply;const p=pending.get(reply.id);
    // A layers answer with layout sections: its decoding getters again on this side (attachLayout).
    if(reply.ok)attachLayout((reply.value as {page?:{webRender?:Record<string,unknown>}}|undefined)?.page?.webRender);
    if(p){pending.delete(reply.id);p.resolve(reply);}};
  worker.onerror=event=>{event.preventDefault();fail(new Error("engine worker: "+event.message));};
  worker.onmessageerror=()=>fail(new Error("engine worker: unreadable message"));
  type Body=WorkerRequest extends infer R?R extends {id:number}?Omit<R,"id">:never:never;
  const send=(request:Body)=>new Promise<WorkerReply>((resolve,reject)=>{
    if(!alive){reject(new Error("engine worker is not running"));return;}
    const id=++next;pending.set(id,{resolve,reject});worker.postMessage({...request,id});
  });
  const init=await send({op:"init",font,nativeEngine,...(logAll?{logAll}:{}),...(session?{session}:{})});
  if(!init.ok)throw new Error(init.error);
  const ownSession=!!(init.value as {session?:boolean}|undefined)?.session;
  const invoke=async(lane:"ordinary"|"input"|"gesture",name:RemoteCall,...args:unknown[])=>{
    ordinary++;
    let reply:WorkerReply;
    try{reply=await send({op:"call",name,args,...(lane==="input"?{input:true}:lane==="gesture"?{gesture:true}:{})});}finally{ordinary--;}
    if(!reply.ok)throw new Error(reply.error);
    return {value:reply.value,workerMs:reply.ms};
  };
  const call=(name:RemoteCall,...args:unknown[])=>invoke("ordinary",name,...args);
  const inputCall=(name:RemoteCall,...args:unknown[])=>invoke("input",name,...args);
  const gestureCall=(name:RemoteCall,...args:unknown[])=>invoke(name==="scriptSession"?"input":"gesture",name,...args);
  const names=REMOTE_CALLS;
  const engine=Object.fromEntries(names.map(name=>[name,async(...args:unknown[])=>(await call(name,...args)).value])) as CompileClient["engine"];
  return {
    session:ownSession,
    get alive(){return alive;},
    get pending(){return ordinary;},
    get inFlight(){return pending.size;},
    async prefetchLayers(source,width,height,options){
      const reply=await send({op:"call",name:"compileLayers",args:[source,width,height,options],low:true});
      if(!reply.ok){if(reply.dropped)return undefined;throw new Error(reply.error);}
      return {layers:reply.value as HTMLLayers,workerMs:reply.ms};
    },
    dropLow(){if(alive)send({op:"dropLow"}).catch(()=>{});},
    async serifFont(path,family){
      const reply=await send({op:"serifFont",path,family});
      if(!reply.ok)throw new Error(reply.error);
      return {value:reply.value,workerMs:reply.ms};
    },
    async monoFont(path,family){
      const reply=await send({op:"monoFont",path,family});
      if(!reply.ok)throw new Error(reply.error);
      return {value:reply.value,workerMs:reply.ms};
    },
    async pageFonts(source){
      const reply=await send({op:"pageFonts",source});
      if(!reply.ok)throw new Error(reply.error);
      return {...reply.value as PageFonts,workerMs:reply.ms};
    },
    call,inputCall,gestureCall,engine,
    async compile(source,width,height,options,gesture=false){
      const {value,workerMs}=await invoke(gesture?"gesture":"ordinary","compile",source,width,height,options);
      return {artifact:value as HTMLArtifact,workerMs};
    },
    async compileLayers(source,width,height,options,gesture=false){
      const {value,workerMs}=await invoke(gesture?"gesture":"ordinary","compileLayers",source,width,height,options);
      return {layers:value as HTMLLayers,workerMs};
    },
    // A worker with a session frees it and closes itself after its call in progress; stopping
    // the worker at once would leave the session's engine state in the shared library.
    terminate(){
      if(!alive)return;
      if(!ownSession){alive=false;worker.terminate();return;}
      const ending=new Error("engine worker ended");
      worker.postMessage({op:"end",id:++next});fail(ending);
      const stop=setTimeout(()=>worker.terminate(),END_GRACE_MS);Deno.unrefTimer(stop);
    },
  };
}
