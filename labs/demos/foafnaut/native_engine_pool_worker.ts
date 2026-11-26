// A host worker of the pooled engine mode (--engine-mode pooled; native_engine_pool.ts;
// docs/designissues/2026-11-26-foafnaut-engine-sessions.md section 7). It holds the engine
// sessions of many tabs. Each session runs on its own Lean task (web_session_new_task), as in
// `tasks` mode; this worker makes the checks and the JSON text of each request, calls the session
// through nonblocking FFI, and reads each answer (JSON head, sections as views), so the window's
// main thread does none of that work. Calls of different tabs are in flight at the same time:
// an engine call does not hold this thread. The main thread keeps each tab's lanes and sends at
// most one call of a tab at a time.
//
// Messages: init (the library and the first font), open (a tab's session), call, pageFonts,
// serifFont and monoFont (as the engine worker, native_html_worker.ts), close (cancel and free a
// tab's session). Each answer moves the storage floats and tile words, not a copy.
import {loadHTMLSession,type HTMLArtifact,type HTMLEngine,type SessionEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {fallbackFontHost,loadFallbackFonts} from "./native_html_fonts.ts";
import {gateConsole} from "../../../docs/web/hub/foafnaut/log-gate.mjs";
import {REMOTE_CALLS,type RemoteCall} from "./native_html_calls.ts";

export type PoolRequest={id:number;op:"init";nativeEngine:string;font?:{path:string;family:string};logAll?:boolean}
  |{id:number;op:"open";tab:number}
  |{id:number;op:"close";tab:number}
  |{id:number;op:"call";tab:number;name:RemoteCall;args:unknown[]}
  |{id:number;op:"pageFonts";tab:number;source:string}
  |{id:number;op:"serifFont"|"monoFont";tab:number;path:string;family:string};
export type PoolReply={id:number;ok:true;value?:unknown;ms:number}|{id:number;ok:false;error:string};

type Tab={engine:SessionEngine;fallbackFonts?:ReturnType<typeof fallbackFontHost>};
const logGate=gateConsole(console,{name:"foafnaut host worker"});
const scope=globalThis as unknown as {onmessage:(event:MessageEvent<PoolRequest>)=>void;postMessage(message:unknown,transfer?:Transferable[]):void};
let nativeEngine:string|undefined,firstFont:{path:string;family:string}|undefined;
const tabs=new Map<number,Promise<Tab>>();

const open=async(tab:number):Promise<Tab>=>{
  if(!nativeEngine)throw new Error("host worker was not initialised");
  const engine=await loadHTMLSession(nativeEngine);
  const helper=engine as unknown as HTMLEngine;
  try{
    // Only an engine that answers its first font with `fonts` (the count held) adds fallback fonts.
    const fallbackFonts=firstFont&&typeof (await loadFontFile(helper,firstFont.path,firstFont.family))?.fonts==="number"
      ?fallbackFontHost(fonts=>loadFallbackFonts(helper,fonts)):undefined;
    return {engine,fallbackFonts};
  }catch(error){await engine.endSession().catch(()=>{});tabs.delete(tab);throw error;}
};
const tabOf=(tab:number)=>{const t=tabs.get(tab);if(!t)throw new Error(`host worker: no session for tab ${tab}`);return t;};

const handle=async(request:PoolRequest)=>{
  const start=performance.now();
  try{
    let value:unknown,transfer:ArrayBuffer[]=[];
    if(request.op==="init"){
      if(request.logAll)logGate.setAll(true);
      nativeEngine=request.nativeEngine;firstFont=request.font;
    }else if(request.op==="open"){
      const t=open(request.tab);tabs.set(request.tab,t);await t;
    }else if(request.op==="close"){
      const t=tabs.get(request.tab);tabs.delete(request.tab);
      if(t){const {engine}=await t;engine.cancel();await engine.endSession();}
    }else if(request.op==="pageFonts"){
      const t=await tabOf(request.tab);
      if(!t.fallbackFonts)throw new Error("this engine has no first font, or holds one font: no fallback fonts");
      value=await t.fallbackFonts.page(request.source);
    }else if(request.op==="serifFont"||request.op==="monoFont"){
      const t=await tabOf(request.tab);
      value=await loadFontFile(t.engine as unknown as HTMLEngine,request.path,request.family,"bytes",request.op==="serifFont"?"serif":"mono");
    }else if(request.op==="call"){
      if(!(REMOTE_CALLS as readonly string[]).includes(request.name))throw new Error(`Engine call ${request.name} is not available in a session`);
      const t=await tabOf(request.tab);
      value=await (t.engine as unknown as Record<string,(...a:unknown[])=>Promise<unknown>>)[request.name](...request.args);
      // The storage floats and tile words move, as from the engine worker (native_html_worker.ts).
      const scenes=[value,(value as {page?:unknown})?.page,(value as {chrome?:unknown})?.chrome] as (Partial<HTMLArtifact>|null|undefined)[];
      const buffers=new Set<ArrayBuffer>();
      for(const scene of scenes)for(const part of [scene?.data,scene?.tiles])
        if(part instanceof Float32Array||part instanceof Uint32Array)buffers.add(part.buffer as ArrayBuffer);
      transfer=[...buffers];
    }
    scope.postMessage({id:request.id,ok:true,value,ms:performance.now()-start} satisfies PoolReply,transfer);
  }catch(error){
    scope.postMessage({id:request.id,ok:false,error:String(error instanceof Error?error.message:error)} satisfies PoolReply);
  }
};
// Every request starts at once: the main thread sends at most one call of a tab at a time.
scope.onmessage=event=>{handle(event.data);};
