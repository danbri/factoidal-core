// Main-thread side of native_html_worker.ts. compile() answers a promise, so the
// event loop keeps pumping. A worker that fails to start or dies gives an error
// to the caller; the caller then compiles on the main thread, once, and says so.
import type {HTMLArtifact} from "./native_html_engine.ts";
import type {WorkerReply,WorkerRequest} from "./native_html_worker.ts";

export type CompileClient={
  compile(source:string,width:number,height:number,options:Record<string,unknown>):Promise<{artifact:HTMLArtifact;workerMs:number}>;
  readonly alive:boolean;
  terminate():void;
};
export async function startCompileWorker(font?:{path:string;family:string}):Promise<CompileClient> {
  const worker=new Worker(new URL("./native_html_worker.ts",import.meta.url),{type:"module"});
  const pending=new Map<number,{resolve:(reply:WorkerReply)=>void;reject:(error:Error)=>void}>();
  let next=0,alive=true;
  const fail=(error:Error)=>{alive=false;for(const p of pending.values())p.reject(error);pending.clear();};
  worker.onmessage=event=>{const reply=event.data as WorkerReply;const p=pending.get(reply.id);if(p){pending.delete(reply.id);p.resolve(reply);}};
  worker.onerror=event=>{event.preventDefault();fail(new Error("compile worker: "+event.message));};
  worker.onmessageerror=()=>fail(new Error("compile worker: unreadable message"));
  type Body=WorkerRequest extends infer R?R extends {id:number}?Omit<R,"id">:never:never;
  const send=(request:Body)=>new Promise<WorkerReply>((resolve,reject)=>{
    if(!alive){reject(new Error("compile worker is not running"));return;}
    const id=++next;pending.set(id,{resolve,reject});worker.postMessage({...request,id});
  });
  const init=await send({op:"init",font});
  if(!init.ok)throw new Error(init.error);
  return {
    get alive(){return alive;},
    async compile(source,width,height,options){
      const reply=await send({op:"compile",source,width,height,options});
      if(!reply.ok)throw new Error(reply.error);
      return {artifact:reply.artifact!,workerMs:reply.ms};
    },
    terminate(){alive=false;worker.terminate();},
  };
}
