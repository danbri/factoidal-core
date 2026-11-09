// The Lean HTML engine in a Deno Worker. Every engine call that can take more than
// about 2 ms runs here, in one queue, so calls stay in order and the main thread keeps
// only the window, the event pump, input and the GPU (issue 1268). The engine is the
// Wasm module or, when a path is given, a native dylib; all Lean calls stay on this
// one thread. The worker holds no page state: each request carries its inputs, and
// the font is loaded once at start. No GPU or native window is used here.
//
// A request with `low` (a scroll prefetch) runs only when no other request waits, and a
// newer low request replaces a low one that has not started; the replaced one is answered
// `dropped`. `dropLow` drops the low request that has not started. A low request that has
// started runs to its end: a Lean call can not be stopped.
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {fallbackFontHost,loadFallbackFonts} from "./native_html_fonts.ts";

/** The engine methods a caller may run in the worker. */
export const REMOTE_CALLS=["xmlStylesheet","xslt","inspect","fontRequests","graphStart","graphEvent","graphPage","sourcePage","wasmPage","sparqlPage","selectedText","decodeDocument","encodingSetting","encodingChoices","compile","compileLayers","printLayout","imageInfo","imageLoad","imageDrop","frameWork","requestBytes","scriptInfo","scriptLoad","scriptSession","nodeAt","pointerAt","scriptPlan","scriptSetting","scriptChoices"] as const;
export type RemoteCall=typeof REMOTE_CALLS[number];
export type WorkerRequest={id:number;op:"init";font?:{path:string;family:string};nativeEngine?:string}
  |{id:number;op:"call";name:RemoteCall;args:unknown[];low?:boolean}
  |{id:number;op:"dropLow"}
  // The fallback fonts a page needs (native_html_fonts.ts): chosen and read here, as bytes,
  // into this engine, before the calls sent after it.
  |{id:number;op:"pageFonts";source:string};
export type WorkerReply={id:number;ok:true;value?:unknown;ms:number}|{id:number;ok:false;error:string;dropped?:boolean};

let engine:Promise<HTMLEngine>|undefined;
// Only an engine that answers its first font with `fonts` (the count held) adds a fallback
// font after it; an older one would take it as a replacement (issue 1274).
let fallbackFonts:ReturnType<typeof fallbackFontHost>|undefined;
const scope=globalThis as unknown as {onmessage:(event:MessageEvent<WorkerRequest>)=>void;postMessage(message:unknown,transfer?:Transferable[]):void};
const handle=async(request:WorkerRequest)=>{
  try{
    const start=performance.now();
    if(request.op==="init"){
      engine=loadHTML(request.nativeEngine);const e=await engine;
      if(request.font&&typeof (await loadFontFile(e,request.font.path,request.font.family))?.fonts==="number")
        fallbackFonts=fallbackFontHost(fonts=>loadFallbackFonts(e,fonts));
      scope.postMessage({id:request.id,ok:true,ms:performance.now()-start} satisfies WorkerReply);
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
// One queue: a request starts when the one before it has ended. Ordinary requests run in
// the order sent; the one low request runs when none of them waits.
const ordinary:WorkerRequest[]=[];
let low:WorkerRequest|undefined,busy=false;
const drop=(request:WorkerRequest)=>scope.postMessage({id:request.id,ok:false,error:"dropped",dropped:true} satisfies WorkerReply);
const pump=async()=>{
  if(busy)return;
  busy=true;
  try{
    for(;;){
      // Messages that came while a Lean call ran are taken in before a low request starts:
      // a Lean call holds the thread, so they wait as tasks behind this loop.
      if(!ordinary.length&&low)await new Promise(resolve=>setTimeout(resolve,0));
      const next=ordinary.shift()??low;
      if(!next)break;
      if(next===low)low=undefined;
      await handle(next);
    }
  }finally{busy=false;}
};
scope.onmessage=event=>{
  const request=event.data;
  if(request.op==="dropLow"){if(low){drop(low);low=undefined;}scope.postMessage({id:request.id,ok:true,ms:0} satisfies WorkerReply);return;}
  if(request.op==="call"&&request.low){if(low)drop(low);low=request;}
  else ordinary.push(request);
  pump();
};
