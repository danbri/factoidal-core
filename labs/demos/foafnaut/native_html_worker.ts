// The Lean HTML engine in a Deno Worker. Every engine call that can take more than
// about 2 ms runs here, in one queue, so calls stay in order and the main thread keeps
// only the window, the event pump, input and the GPU (issue 1268). The engine is the
// Wasm module or, when a path is given, a native dylib; all Lean calls stay on this
// one thread. The worker holds no page state: each request carries its inputs, and
// the font is loaded once at start. No GPU or native window is used here.
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

/** The engine methods a caller may run in the worker. */
export const REMOTE_CALLS=["xmlStylesheet","xslt","inspect","fontRequests","graphStart","graphEvent","graphPage","sourcePage","selectedText","compile","compileLayers"] as const;
export type RemoteCall=typeof REMOTE_CALLS[number];
export type WorkerRequest={id:number;op:"init";font?:{path:string;family:string};nativeEngine?:string}
  |{id:number;op:"call";name:RemoteCall;args:unknown[]};
export type WorkerReply={id:number;ok:true;value?:unknown;ms:number}|{id:number;ok:false;error:string};

let engine:Promise<HTMLEngine>|undefined;
let queue:Promise<void>=Promise.resolve();
const scope=globalThis as unknown as {onmessage:(event:MessageEvent<WorkerRequest>)=>void;postMessage(message:unknown,transfer?:Transferable[]):void};
const handle=async(request:WorkerRequest)=>{
  try{
    const start=performance.now();
    if(request.op==="init"){
      engine=loadHTML(request.nativeEngine);const e=await engine;
      if(request.font)await loadFontFile(e,request.font.path,request.font.family);
      scope.postMessage({id:request.id,ok:true,ms:performance.now()-start} satisfies WorkerReply);
      return;
    }
    if(!engine)throw new Error("engine worker was not initialised");
    if(!(REMOTE_CALLS as readonly string[]).includes(request.name))throw new Error(`Engine call ${request.name} is not available in the worker`);
    const e=await engine as unknown as Record<string,(...args:unknown[])=>unknown>;
    const value=e[request.name](...request.args);
    // The storage floats move to the main thread, not copied: one scene, or the two layers.
    const scenes=[value,(value as {page?:unknown})?.page,(value as {chrome?:unknown})?.chrome] as (Partial<HTMLArtifact>|null|undefined)[];
    const transfer:Transferable[]=scenes.flatMap(scene=>scene?.data instanceof Float32Array?[scene.data.buffer as ArrayBuffer]:[]);
    scope.postMessage({id:request.id,ok:true,value,ms:performance.now()-start} satisfies WorkerReply,transfer);
  }catch(error){
    scope.postMessage({id:request.id,ok:false,error:String(error instanceof Error?error.message:error)} satisfies WorkerReply);
  }
};
// One queue: a request starts when the one before it has ended.
scope.onmessage=event=>{queue=queue.then(()=>handle(event.data));};
