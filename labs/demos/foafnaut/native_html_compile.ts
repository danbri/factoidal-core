// Main-thread side of native_html_worker.ts. Calls answer promises, so the event loop
// keeps pumping, and they run in the order sent. A worker that fails to start or dies
// rejects its calls; the caller decides what to do and says so in the trace.
import type {HTMLArtifact,HTMLLayers} from "./native_html_engine.ts";
import type {RemoteCall,WorkerReply,WorkerRequest} from "./native_html_worker.ts";
import type {PageFonts} from "./native_html_fonts.ts";

export type CompileClient={
  call(name:RemoteCall,...args:unknown[]):Promise<{value:unknown;workerMs:number}>;
  compile(source:string,width:number,height:number,options:Record<string,unknown>):Promise<{artifact:HTMLArtifact;workerMs:number}>;
  compileLayers(source:string,width:number,height:number,options:Record<string,unknown>):Promise<{layers:HTMLLayers;workerMs:number}>;
  /** A layers render at low priority (a scroll prefetch): it runs when no other call waits,
   * and a newer one replaces it while it has not started. Undefined when it was dropped. */
  prefetchLayers(source:string,width:number,height:number,options:Record<string,unknown>):Promise<{layers:HTMLLayers;workerMs:number}|undefined>;
  /** The fallback fonts a page needs, chosen and loaded in the worker, before later calls. */
  pageFonts(source:string):Promise<PageFonts&{workerMs:number}>;
  /** Drop the low-priority call that has not started, if there is one. */
  dropLow():void;
  /** Ordinary calls sent and not yet answered. */
  readonly pending:number;
  /** The engine methods that run in the worker, as promise-returning functions. */
  engine:Record<RemoteCall,(...args:unknown[])=>Promise<unknown>>;
  readonly alive:boolean;
  terminate():void;
};
export async function startCompileWorker(font?:{path:string;family:string},nativeEngine?:string):Promise<CompileClient> {
  const worker=new Worker(new URL("./native_html_worker.ts",import.meta.url),{type:"module"});
  const pending=new Map<number,{resolve:(reply:WorkerReply)=>void;reject:(error:Error)=>void}>();
  let next=0,alive=true,ordinary=0;
  const fail=(error:Error)=>{alive=false;for(const p of pending.values())p.reject(error);pending.clear();};
  worker.onmessage=event=>{const reply=event.data as WorkerReply;const p=pending.get(reply.id);if(p){pending.delete(reply.id);p.resolve(reply);}};
  worker.onerror=event=>{event.preventDefault();fail(new Error("engine worker: "+event.message));};
  worker.onmessageerror=()=>fail(new Error("engine worker: unreadable message"));
  type Body=WorkerRequest extends infer R?R extends {id:number}?Omit<R,"id">:never:never;
  const send=(request:Body)=>new Promise<WorkerReply>((resolve,reject)=>{
    if(!alive){reject(new Error("engine worker is not running"));return;}
    const id=++next;pending.set(id,{resolve,reject});worker.postMessage({...request,id});
  });
  const init=await send({op:"init",font,nativeEngine});
  if(!init.ok)throw new Error(init.error);
  const call=async(name:RemoteCall,...args:unknown[])=>{
    ordinary++;
    let reply:WorkerReply;
    try{reply=await send({op:"call",name,args});}finally{ordinary--;}
    if(!reply.ok)throw new Error(reply.error);
    return {value:reply.value,workerMs:reply.ms};
  };
  // The same names as REMOTE_CALLS in native_html_worker.ts (not imported: that module runs
  // worker code at load). A merge dropped printLayout here once, and the window could not print.
  const names:RemoteCall[]=["xmlStylesheet","xslt","inspect","fontRequests","graphStart","graphEvent","graphPage","sourcePage","wasmPage","sparqlPage","selectedText","compile","compileLayers","printLayout","imageInfo","imageLoad","imageDrop","frameWork","requestBytes","scriptInfo","scriptLoad","scriptSession","nodeAt","pointerAt","scriptPlan","scriptSetting","scriptChoices"];
  const engine=Object.fromEntries(names.map(name=>[name,async(...args:unknown[])=>(await call(name,...args)).value])) as CompileClient["engine"];
  return {
    get alive(){return alive;},
    get pending(){return ordinary;},
    async prefetchLayers(source,width,height,options){
      const reply=await send({op:"call",name:"compileLayers",args:[source,width,height,options],low:true});
      if(!reply.ok){if(reply.dropped)return undefined;throw new Error(reply.error);}
      return {layers:reply.value as HTMLLayers,workerMs:reply.ms};
    },
    dropLow(){if(alive)send({op:"dropLow"}).catch(()=>{});},
    async pageFonts(source){
      const reply=await send({op:"pageFonts",source});
      if(!reply.ok)throw new Error(reply.error);
      return {...reply.value as PageFonts,workerMs:reply.ms};
    },
    call,engine,
    async compile(source,width,height,options){
      const {value,workerMs}=await call("compile",source,width,height,options);
      return {artifact:value as HTMLArtifact,workerMs};
    },
    async compileLayers(source,width,height,options){
      const {value,workerMs}=await call("compileLayers",source,width,height,options);
      return {layers:value as HTMLLayers,workerMs};
    },
    terminate(){alive=false;worker.terminate();},
  };
}
