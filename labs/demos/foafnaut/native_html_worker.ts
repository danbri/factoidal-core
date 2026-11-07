// A second copy of the Lean HTML engine, in a Deno Worker, for the one slow
// call: compile (layout and scene). The window and every other engine call stay
// on the main thread, which must keep pumping Cocoa events (issue 1268).
// The worker holds no page state: each request carries the source and options,
// and the font is loaded once at start. No GPU or native window is used here.
import {loadHTML,type HTMLArtifact} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

export type WorkerRequest={id:number;op:"init";font?:{path:string;family:string}}
  |{id:number;op:"compile";source:string;width:number;height:number;options:Record<string,unknown>};
export type WorkerReply={id:number;ok:true;artifact?:HTMLArtifact;ms:number}|{id:number;ok:false;error:string};

const ready=loadHTML();
const scope=globalThis as unknown as {onmessage:(event:MessageEvent<WorkerRequest>)=>void;postMessage(message:unknown,transfer?:Transferable[]):void};
scope.onmessage=async event=>{
  const request=event.data;
  try{
    const engine=await ready,start=performance.now();
    if(request.op==="init"){
      if(request.font)await loadFontFile(engine,request.font.path,request.font.family);
      scope.postMessage({id:request.id,ok:true,ms:performance.now()-start} satisfies WorkerReply);
      return;
    }
    const artifact=engine.compile(request.source,request.width,request.height,request.options);
    const transfer:Transferable[]=artifact.data instanceof Float32Array?[artifact.data.buffer as ArrayBuffer]:[];
    scope.postMessage({id:request.id,ok:true,artifact,ms:performance.now()-start} satisfies WorkerReply,transfer);
  }catch(error){
    scope.postMessage({id:request.id,ok:false,error:String(error instanceof Error?error.message:error)} satisfies WorkerReply);
  }
};
