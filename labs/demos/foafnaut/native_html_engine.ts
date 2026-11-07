// Byte/JSON transport for the published Lean HTML engine. No host markup parser.
// This ignored runtime is installed only after checking the Builds manifest.
// @ts-ignore generated release module
import createModule from "./.build/native-html/runtime/web-render.mjs";

export type HTMLArtifact = {
  abi:string; width:number; height:number; data:number[]|Float32Array; wgsl:string; tiles:number[];
  primitiveCount:number; checks:{x:number;y:number;rgb:number[]}[];
  webRender:{links:unknown[][];[name:string]:unknown};
};
export type Inspection = {
  baseURL:string;
  title:string;
  scripts:{kind:string;type:string;src:string}[];
  stylesheets:{nodeId:number;url:string}[];
};
export type History = {entries:string[];index:number};
export type HistoryAnswer = {history:History;url:string|null;canBack:boolean;canForward:boolean};
export type GraphFrame = {model:string;commands:string[]};
export type ShellEdit = {address:string;cursor:number};
export type ShellGo = {go:"page";url:string}|{go:"system";url:string}|{go:"command";name:string;argument:string};
export type HTMLResource = {nodeId:number;url:string;source:string};
type Module = {ccall(name:string,result:string|null,types:string[],values:unknown[]):number;
  UTF8ToString(pointer:number):string};
const encoder = new TextEncoder();
export const MAX_SOURCE_BYTES = 1048576;
export function sourceBound(source:string) {
  if(source.includes("\0") || encoder.encode(source).length>MAX_SOURCE_BYTES)
    throw new Error("HTML/CSS input contains NUL or exceeds 1 MiB");
}
/** One call into Lean's document engine: HTML text, a JSON request, a viewport; a JSON answer. */
export type DocumentBackend=(html:string,requestJSON:string,width:number,height:number)=>string;
/** Backend 2: a native dylib of the same Lean objects. Every call must come from one thread; no nonblocking FFI. */
export function nativeBackend(path:string):DocumentBackend {
  const library=Deno.dlopen(path,{
    web_document_call:{parameters:["buffer","buffer","u32","u32"],result:"pointer"},
    web_render_free:{parameters:["pointer"],result:"void"},
  } as const);
  const cstring=(text:string)=>{if(text.includes("\0"))throw new Error("Native engine input contains NUL");return encoder.encode(text+"\0");};
  return (html,request,width,height)=>{
    const pointer=library.symbols.web_document_call(cstring(html),cstring(request),width,height);
    if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
    try{return new Deno.UnsafePointerView(pointer).getCString();}
    finally{library.symbols.web_render_free(pointer);}
  };
}
/** Backend 1: the Wasm module. */
function wasmBackend(module:Module):DocumentBackend {
  return (html,request,width,height)=>{
    const pointer=module.ccall("web_document_call","number",["string","string","number","number"],[html,request,width,height]);
    if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
    try{return module.UTF8ToString(pointer);}
    finally{module.ccall("web_render_free",null,["number"],[pointer]);}
  };
}
export async function loadHTML(nativeEngine?:string) {
  const module = await createModule() as unknown as Module;
  const backend=nativeEngine?nativeBackend(nativeEngine):wasmBackend(module);
  function call(name:string,types:string[],args:unknown[]) {
    const pointer=module.ccall(name,"number",types,args);
    if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
    try {
      const result=JSON.parse(module.UTF8ToString(pointer));
      if(result?.error)throw new Error(`Lean HTML: ${result.error}`);
      return result;
    } finally {module.ccall("web_render_free",null,["number"],[pointer]);}
  }
  const documentCall=(source:string,options:Record<string,unknown>,width=1,height=1)=>{
    sourceBound(source);
    if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))
      throw new Error("Native HTML viewport must be 1..4096 backing pixels");
    const request=JSON.stringify(options);
    if(encoder.encode(request).length>20971520)throw new Error("Document request exceeds 20 MiB");
    const result=JSON.parse(backend(source,request,width,height));
    if(result?.error)throw new Error(`Lean HTML: ${result.error}`);
    return result;
  };
  return {
    xmlStylesheet:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"xmlStylesheet"}) as {url:string|null},
    xslt:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"xslt"}) as {source:string;engine:string},
    inspect:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"inspect"}) as Inspection,
    // Lean reads the font once and holds it; later renders draw with it.
    fontLoad:(fontBase64:string,fontFamily:string,fontSha256:string)=>documentCall("",{op:"fontLoad",fontBase64,fontFamily,fontSha256}) as {family:string;glyphs:number},
    fontRequests:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"fontRequests"}),
    compile(source:string,width:number,height:number,options:Record<string,unknown>):HTMLArtifact {
      // Lean sends the storage floats as the bytes the GPU reads; this only decodes them.
      const result=documentCall(source,{binary:true,...options,op:"render"},width,height);
      if(typeof result.dataBase64==="string"){
        const text=atob(result.dataBase64),bytes=new Uint8Array(text.length);
        for(let i=0;i<text.length;i++)bytes[i]=text.charCodeAt(i);
        result.data=new Float32Array(bytes.buffer);delete result.dataBase64;
      }
      if(result.abi!=="lean-svg-v1" || result.width!==width || result.height!==height ||
         !(Array.isArray(result.data)||result.data instanceof Float32Array) || !result.data.length || !result.data.every(Number.isFinite) ||
         typeof result.wgsl!=="string" || !Array.isArray(result.checks) || !Array.isArray(result.webRender?.links))
        throw new Error("Unexpected published Lean HTML scene ABI");
      return result;
    },
    // Lean decides what a chrome click, a key, an address and a link mean.
    shellHit:(shell:unknown,x:number,y:number,width:number)=>(documentCall("",{op:"shellHit",shell,x,y,width}) as {control:string|null}).control,
    shellText:(shell:unknown,text:string)=>documentCall("",{op:"shellText",shell,text}) as ShellEdit,
    shellKey:(shell:unknown,key:number)=>documentCall("",{op:"shellKey",shell,key}) as ShellEdit,
    shellSubmit:(address:string)=>documentCall("",{op:"shellSubmit",address}) as ShellGo,
    // The FOAF graph page: the model is Lean's; the host keeps it as text.
    graphStart:(rdf:string,width:number,height:number,shell:unknown)=>documentCall("",{op:"graphStart",rdf,width,height,shell}) as GraphFrame,
    graphEvent:(model:string,kind:number,a:number,b:number,width:number,shell:unknown)=>documentCall("",{op:"graphEvent",model,kind,a,b,width,shell}) as GraphFrame,
    graphPage:(model:string)=>(documentCall("",{op:"graphPage",model}) as {source:string}).source,
    sourcePage:(kind:string,url:string,source:string)=>(documentCall("",{op:"sourcePage",kind,url,source}) as {source:string}).source,
    shellLink:(href:string)=>documentCall("",{op:"shellLink",href}) as ShellGo,
    // Lean decides what a menu command and a pointer release mean.
    command:(command:number,textScalePercent:number,history?:History)=>documentCall("",{op:"command",command,textScalePercent,...(history?{history}:{})}) as
      {action:string;textScalePercent:number}&Partial<HistoryAnswer>,
    historyPush:(history:History,url:string)=>documentCall("",{op:"historyPush",history,url}) as HistoryAnswer,
    keyCommand:(platform:string,modifier:string,key:string)=>(documentCall("",{op:"keyCommand",platform,modifier,key}) as {command:number|null}).command,
    pointerUp:(selection:number[])=>(documentCall("",{op:"pointerUp",selection}) as {action:string}).action,
    selectedText:(source:string,width:number,height:number,options:Record<string,unknown>)=>
      (documentCall(source,{...options,op:"selectedText"},width,height) as {text:string}).text,
    hit(artifact:HTMLArtifact,x:number,y:number):{href:string;sourceNode:number}|null {
      if(!Number.isFinite(x)||!Number.isFinite(y))return null;
      return call("web_render_hit",["string","number","number","number","number"],
        [JSON.stringify(artifact.webRender.links),artifact.width,artifact.height,x,y]);
    },
  };
}
export type HTMLEngine = Awaited<ReturnType<typeof loadHTML>>;
