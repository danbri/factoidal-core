// Main-thread side of native_html_worker.ts. Calls answer promises, so the event loop
// keeps pumping, and they run in the order sent. A worker that fails to start or dies
// rejects its calls; the caller decides what to do and says so in the trace.
import type {HTMLArtifact} from "./native_html_engine.ts";
import type {RemoteCall,WorkerReply,WorkerRequest} from "./native_html_worker.ts";

export type CompileClient={
  call(name:RemoteCall,...args:unknown[]):Promise<{value:unknown;workerMs:number}>;
  compile(source:string,width:number,height:number,options:Record<string,unknown>):Promise<{artifact:HTMLArtifact;workerMs:number}>;
  /** The engine methods that run in the worker, as promise-returning functions. */
  engine:Record<RemoteCall,(...args:unknown[])=>Promise<unknown>>;
  readonly alive:boolean;
  terminate():void;
};
export async function startCompileWorker(font?:{path:string;family:string},nativeEngine?:string):Promise<CompileClient> {
  const worker=new Worker(new URL("./native_html_worker.ts",import.meta.url),{type:"module"});
  const pending=new Map<number,{resolve:(reply:WorkerReply)=>void;reject:(error:Error)=>void}>();
  let next=0,alive=true;
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
    const reply=await send({op:"call",name,args});
    if(!reply.ok)throw new Error(reply.error);
    return {value:reply.value,workerMs:reply.ms};
  };
  const names:RemoteCall[]=["xmlStylesheet","xslt","inspect","fontRequests","graphStart","graphEvent","graphPage","sourcePage","selectedText","compile"];
  const engine=Object.fromEntries(names.map(name=>[name,async(...args:unknown[])=>(await call(name,...args)).value])) as CompileClient["engine"];
  return {
    get alive(){return alive;},
    call,engine,
    async compile(source,width,height,options){
      const {value,workerMs}=await call("compile",source,width,height,options);
      return {artifact:value as HTMLArtifact,workerMs};
    },
    terminate(){alive=false;worker.terminate();},
  };
}
