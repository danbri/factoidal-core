// One tab's engine as an engine session on its own Lean task (web_session_new_task, WebSession.lean;
// docs/designissues/2026-11-26-foafnaut-engine-sessions.md, stage 3), called from this thread
// (the window's main thread) through nonblocking FFI: no engine worker, and one loaded library for
// every tab. The session's task runs on a thread of its own, so a long call of one tab does not
// delay another tab, and this thread never waits for the engine.
//
// The order of calls is the engine worker's (native_html_queue.ts): a gesture runs right after
// the call in progress, then input in arrival order, then ordinary calls, then one low request
// that a newer one replaces while it has not started. One call of a session is in flight at a
// time, so these lanes decide the order, as in the worker. The fallback fonts, the serif and the
// monospace faces are loaded here, in that order with the other calls, as the worker loads them.
//
// What runs on this thread that ran in the worker: the checks and the JSON text of each request,
// the reading of each answer (JSON head, sections as views), and the fallback-font choice of a
// page with characters above ASCII (font-coverage.mjs reads every character of the source).
import type {CompileClient} from "./native_html_compile.ts";
import {loadHTMLSession,type HTMLArtifact,type HTMLEngine,type HTMLLayers} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {fallbackFontHost,loadFallbackFonts,type PageFonts} from "./native_html_fonts.ts";
import {htmlQueue} from "./native_html_queue.ts";
import {REMOTE_CALLS,type RemoteCall} from "./native_html_calls.ts";

type Reply={value:unknown;ms:number;dropped?:boolean};
type Job={op:"call"|"pageFonts"|"serifFont"|"monoFont";name?:RemoteCall;args?:unknown[];input?:boolean;low?:boolean;gesture?:boolean;
  source?:string;path?:string;family?:string;resolve:(reply:Reply)=>void;reject:(error:Error)=>void};

/** A CompileClient whose engine is a task session of the native library at `nativeEngine`.
Throws when the library has no task sessions; the caller then uses engine workers. */
export async function startTaskClient(font:{path:string;family:string}|undefined,nativeEngine:string):Promise<CompileClient>{
  const engine=loadHTMLSession(nativeEngine);
  // The font helpers await each engine answer, so they take the session engine as it is.
  const helperEngine=engine as unknown as HTMLEngine;
  let fallbackFonts:ReturnType<typeof fallbackFontHost>|undefined;
  try{
    // Only an engine that answers its first font with `fonts` (the count held) adds fallback fonts.
    if(font&&typeof (await loadFontFile(helperEngine,font.path,font.family))?.fonts==="number")
      fallbackFonts=fallbackFontHost(fonts=>loadFallbackFonts(helperEngine,fonts));
  }catch(error){await engine.endSession().catch(()=>{});throw error;}
  const queue=htmlQueue<Job>();
  // Jobs sent and not answered (in the lanes, or running).
  let alive=true,busy=false,ordinary=0,open=0;
  const run=async(job:Job)=>{
    const start=performance.now();
    try{
      let value:unknown;
      if(job.op==="pageFonts"){
        if(!fallbackFonts)throw new Error("this engine has no first font, or holds one font: no fallback fonts");
        value=await fallbackFonts.page(job.source!);
      }else if(job.op==="serifFont"||job.op==="monoFont")
        value=await loadFontFile(helperEngine,job.path!,job.family!,"bytes",job.op==="serifFont"?"serif":"mono");
      else{
        if(!(REMOTE_CALLS as readonly string[]).includes(job.name!))throw new Error(`Engine call ${job.name} is not available in a session`);
        value=await (engine as unknown as Record<string,(...a:unknown[])=>Promise<unknown>>)[job.name!](...job.args!);
      }
      job.resolve({value,ms:performance.now()-start});
    }catch(error){job.reject(error instanceof Error?error:new Error(String(error)));}
    finally{open--;}
  };
  // One call of the session at a time; calls sent meanwhile wait in their lanes.
  const pump=async()=>{
    if(busy)return;
    busy=true;
    try{
      for(;;){
        const job=queue.shift();
        if(!job)break;
        if(!alive){open--;job.reject(new Error("engine session ended"));continue;}
        await run(job);
      }
    }finally{busy=false;}
  };
  const submit=(job:Omit<Job,"resolve"|"reject">)=>new Promise<Reply>((resolve,reject)=>{
    if(!alive){reject(new Error("engine session ended"));return;}
    open++;
    const dropped=queue.push({...job,resolve,reject} as Job);
    if(dropped){open--;dropped.resolve({value:undefined,ms:0,dropped:true});}
    pump();
  });
  const invoke=async(lane:"ordinary"|"input"|"gesture",name:RemoteCall,...args:unknown[])=>{
    ordinary++;
    try{
      const reply=await submit({op:"call",name,args,...(lane==="input"?{input:true}:lane==="gesture"?{gesture:true}:{})});
      return {value:reply.value,workerMs:reply.ms};
    }finally{ordinary--;}
  };
  const call=(name:RemoteCall,...args:unknown[])=>invoke("ordinary",name,...args);
  const engineCalls=Object.fromEntries(REMOTE_CALLS.map(name=>[name,async(...args:unknown[])=>(await call(name,...args)).value])) as CompileClient["engine"];
  return {
    session:true,
    kind:"task",
    get alive(){return alive;},
    get pending(){return ordinary;},
    get inFlight(){return open;},
    call,
    inputCall:(name,...args)=>invoke("input",name,...args),
    gestureCall:(name,...args)=>invoke(name==="scriptSession"?"input":"gesture",name,...args),
    engine:engineCalls,
    async compile(source,width,height,options,gesture=false){
      const {value,workerMs}=await invoke(gesture?"gesture":"ordinary","compile",source,width,height,options);
      return {artifact:value as HTMLArtifact,workerMs};
    },
    async compileLayers(source,width,height,options,gesture=false){
      const {value,workerMs}=await invoke(gesture?"gesture":"ordinary","compileLayers",source,width,height,options);
      return {layers:value as HTMLLayers,workerMs};
    },
    async prefetchLayers(source,width,height,options){
      const reply=await submit({op:"call",name:"compileLayers",args:[source,width,height,options],low:true});
      if(reply.dropped)return undefined;
      return {layers:reply.value as HTMLLayers,workerMs:reply.ms};
    },
    dropLow(){const low=queue.dropLow();if(low){open--;low.resolve({value:undefined,ms:0,dropped:true});}},
    async pageFonts(source){
      const reply=await submit({op:"pageFonts",source});
      return {...reply.value as PageFonts,workerMs:reply.ms};
    },
    async serifFont(path,family){const reply=await submit({op:"serifFont",path,family});return {value:reply.value,workerMs:reply.ms};},
    async monoFont(path,family){const reply=await submit({op:"monoFont",path,family});return {value:reply.value,workerMs:reply.ms};},
    // The calls not started fail; the session's task is canceled, so the call in progress stops
    // at the engine's next check (a layout in progress runs to its end); then the session is freed.
    terminate(){
      if(!alive)return;
      alive=false;
      const ended=new Error("engine session ended");
      for(const job of queue.drain()){open--;job.reject(ended);}
      engine.cancel();
      engine.endSession().catch(()=>{});
    },
  };
}
