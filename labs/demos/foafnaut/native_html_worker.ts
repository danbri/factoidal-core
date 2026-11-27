// The Lean HTML engine in a Deno Worker. Every engine call that can take more than
// about 2 ms runs here, one at a time, so the main thread keeps
// only the window, the event pump, input and the GPU (issue 1268). The engine is the
// Wasm module or, when a path is given, a native dylib; all Lean calls stay on this
// one thread. The worker holds no page state: each request carries its inputs, and
// the font is loaded once at start. No GPU or native window is used here.
//
// A gesture (issue 1031: copy's selected text, the frame of a new selection or menu) runs
// first, right after the call that is running, before queued script turns and renders; it
// writes no script session. Input runs next, before ordinary work, in arrival order. All scriptSession turns use that
// lane too, so input cannot pass an earlier resize or timer turn of the same session.
// A request with `low` (a scroll prefetch) runs only when no other request waits, and a
// newer low request replaces a low one that has not started; the replaced one is answered
// `dropped`. `dropLow` drops the low request that has not started. A low request that has
// started runs to its end: a Lean call can not be stopped.
//
// With `session` at init (native library only), the engine uses an engine session of its own,
// so every worker shares one loaded library (docs/designissues/2026-11-26-foafnaut-engine-sessions.md).
// `end` drops the requests that have not started, frees the session after the call that runs,
// and closes the worker.
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {fallbackFontHost,loadFallbackFonts} from "./native_html_fonts.ts";
import {htmlPump,htmlQueue} from "./native_html_queue.ts";
import {gateConsole} from "../../../docs/web/hub/foafnaut/log-gate.mjs";

import {REMOTE_CALLS,type RemoteCall} from "./native_html_calls.ts";
export {REMOTE_CALLS};
export type {RemoteCall};
export type WorkerRequest={id:number;op:"init";font?:{path:string;family:string};nativeEngine?:string;logAll?:boolean;session?:boolean}
  |{id:number;op:"end"}
  |{id:number;op:"call";name:RemoteCall;args:unknown[];input?:boolean;low?:boolean;gesture?:boolean}
  |{id:number;op:"dropLow"}
  // The fallback fonts a page needs (native_html_fonts.ts): chosen and read here, as bytes,
  // into this engine, before the calls sent after it.
  |{id:number;op:"pageFonts";source:string}
  // The serif face or the monospace face (serif_font.ts), into this engine, before the calls
  // sent after it.
  |{id:number;op:"serifFont"|"monoFont";path:string;family:string};
export type WorkerReply={id:number;ok:true;value?:unknown;ms:number}|{id:number;ok:false;error:string;dropped?:boolean};

let engine:Promise<HTMLEngine>|undefined;
// The worker's lines go through the log gate too (log-gate.mjs); --log-all comes with init.
const logGate=gateConsole(console,{name:"foafnaut worker"});
// Only an engine that answers its first font with `fonts` (the count held) adds a fallback
// font after it; an older one would take it as a replacement (issue 1274).
let fallbackFonts:ReturnType<typeof fallbackFontHost>|undefined;
const scope=globalThis as unknown as {onmessage:(event:MessageEvent<WorkerRequest>)=>void;postMessage(message:unknown,transfer?:Transferable[]):void};
const handle=async(request:WorkerRequest)=>{
  try{
    const start=performance.now();
    if(request.op==="init"){
      if(request.logAll)logGate.setAll(true);
      engine=loadHTML(request.nativeEngine,"bytes",{session:!!request.session});const e=await engine;
      if(request.font&&typeof (await loadFontFile(e,request.font.path,request.font.family))?.fonts==="number")
        fallbackFonts=fallbackFontHost(fonts=>loadFallbackFonts(e,fonts));
      // `value.session`: the engine has a session of its own (false with an engine from before sessions).
      scope.postMessage({id:request.id,ok:true,value:{session:e.sessionOwn},ms:performance.now()-start} satisfies WorkerReply);
      return;
    }
    if(request.op==="serifFont"||request.op==="monoFont"){
      if(!engine)throw new Error("engine worker was not initialised");
      const value=await loadFontFile(await engine,request.path,request.family,"bytes",request.op==="serifFont"?"serif":"mono");
      scope.postMessage({id:request.id,ok:true,value,ms:performance.now()-start} satisfies WorkerReply);
      return;
    }
    if(request.op==="pageFonts"){
      if(!fallbackFonts)throw new Error("this engine has no first font, or holds one font: no fallback fonts");
      const value=await fallbackFonts.page(request.source);
      scope.postMessage({id:request.id,ok:true,value,ms:performance.now()-start} satisfies WorkerReply);
      return;
    }
    if(request.op!=="call")return;
    if(!engine)throw new Error("engine worker was not initialised");
    if(!(REMOTE_CALLS as readonly string[]).includes(request.name))throw new Error(`Engine call ${request.name} is not available in the worker`);
    const e=await engine as unknown as Record<string,(...args:unknown[])=>unknown>;
    const value=e[request.name](...request.args);
    // The storage floats and tile words move to the main thread, not copied: one scene,
    // or the two layers. With a bytes answer they are views of one buffer, sent once.
    const scenes=[value,(value as {page?:unknown})?.page,(value as {chrome?:unknown})?.chrome] as (Partial<HTMLArtifact>|null|undefined)[];
    const buffers=new Set<ArrayBuffer>();
    for(const scene of scenes)for(const part of [scene?.data,scene?.tiles])
      if(part instanceof Float32Array||part instanceof Uint32Array)buffers.add(part.buffer as ArrayBuffer);
    scope.postMessage({id:request.id,ok:true,value,ms:performance.now()-start} satisfies WorkerReply,[...buffers]);
  }catch(error){
    scope.postMessage({id:request.id,ok:false,error:String(error instanceof Error?error.message:error)} satisfies WorkerReply);
  }
};
const queue=htmlQueue<WorkerRequest>();
const drop=(request:WorkerRequest)=>scope.postMessage({id:request.id,ok:false,error:"dropped",dropped:true} satisfies WorkerReply);
// A Lean call holds this thread. The pump takes in messages waiting as tasks before choosing
// the next request, even with ordinary work queued: one of them may be input or a gesture.
const pump=htmlPump(queue,async request=>{if(request.op==="end"){await finish();return;}await handle(request);});
// `end`: no request after it runs; the session is freed when the call that runs is done.
let ending=false;
const finish=async()=>{
  for(const r of queue.drain())drop(r);
  // The engine's real-time audio runs end first: the default session of this worker's library copy
  // is never freed, and their threads would run on after the worker (WebAudioRun.endAll).
  try{(await engine)?.audioEnd();}catch{/* never started */}
  try{(await engine)?.endSession();}catch{/* never started */}
  (globalThis as unknown as {close():void}).close();
};
scope.onmessage=event=>{
  const request=event.data;
  if(request.op==="end"){ending=true;for(const r of queue.drain())drop(r);queue.push(request);pump();return;}
  if(ending){drop(request);return;}
  if(request.op==="dropLow"){const low=queue.dropLow();if(low)drop(low);scope.postMessage({id:request.id,ok:true,ms:0} satisfies WorkerReply);return;}
  const dropped=queue.push(request);if(dropped)drop(dropped);
  pump();
};
