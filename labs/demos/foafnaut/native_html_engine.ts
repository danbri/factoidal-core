// Byte/JSON transport for the published Lean HTML engine. No host markup parser.
// This ignored runtime is installed only after checking the Builds manifest.
// @ts-ignore generated release module
import createModule from "./.build/native-html/runtime/web-render.mjs";

export type HTMLArtifact = {
  abi:string; width:number; height:number; data:number[]|Float32Array; wgsl:string; tiles:number[]|Uint32Array;
  primitiveCount:number; checks:{x:number;y:number;rgb:number[]}[];
  webRender:{links:unknown[][];[name:string]:unknown};
};
/** A render with `layers:true` (WebDocument.layersJSON): the chrome layer in window
rows, the page layer in band rows from page row `bandTop`, and the WGSL that puts them
in the window. `keepFrom`..`keepTo` are the scrolls that this band shows with no new render. */
export type HTMLLayerPlace = {top:number;view:number;bandTop:number;bandHeight:number;keepFrom:number;keepTo:number;composite:string};
export type HTMLLayers = {layers:HTMLLayerPlace;page:HTMLArtifact;chrome:HTMLArtifact};
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
  UTF8ToString(pointer:number):string;HEAPU8:Uint8Array;_malloc?(size:number):number;_free?(pointer:number):void};
const encoder = new TextEncoder();
export const MAX_SOURCE_BYTES = 1048576;
export function sourceBound(source:string) {
  if(source.includes("\0") || encoder.encode(source).length>MAX_SOURCE_BYTES)
    throw new Error("HTML/CSS input contains NUL or exceeds 1 MiB");
}
/** One call into Lean's document engine: HTML text, a JSON request, a viewport; a JSON answer. */
export type DocumentBackend=(html:string,requestJSON:string,width:number,height:number)=>string;
/** The same call with a bytes answer (`web_document_call_bin`, WebDocument.packAnswer):
a JSON head and raw sections, with no Base64. The buffer is the host's own copy. */
export type BytesBackend=(html:string,requestJSON:string,width:number,height:number)=>ArrayBuffer;
/** A font file as bytes (`web_document_font_call_bin`, WebDocument.fontLoadBin): no Base64
and no JSON, so the file is not copied onto the call stack. The answer is the fontLoad JSON. */
export type FontBackend=(bytes:Uint8Array,family:string,sha256:string)=>string;
type Backends={text:DocumentBackend;bytes:BytesBackend;font:FontBackend};
/** Backend 2: a native dylib of the same Lean objects. Every call must come from one thread; no nonblocking FFI. */
export function nativeBackends(path:string):Backends {
  const library=Deno.dlopen(path,{
    web_document_call:{parameters:["buffer","buffer","u32","u32"],result:"pointer"},
    web_document_call_bin:{parameters:["buffer","buffer","u32","u32","buffer"],result:"pointer"},
    web_document_font_call_bin:{parameters:["buffer","u32","buffer","buffer"],result:"pointer"},
    web_render_free:{parameters:["pointer"],result:"void"},
  } as const);
  const cstring=(text:string)=>{if(text.includes("\0"))throw new Error("Native engine input contains NUL");return encoder.encode(text+"\0");};
  const size=new Uint32Array(1);
  return {
    text:(html,request,width,height)=>{
      const pointer=library.symbols.web_document_call(cstring(html),cstring(request),width,height);
      if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
      try{return new Deno.UnsafePointerView(pointer).getCString();}
      finally{library.symbols.web_render_free(pointer);}
    },
    bytes:(html,request,width,height)=>{
      const pointer=library.symbols.web_document_call_bin(cstring(html),cstring(request),width,height,size);
      if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
      // One copy out of the engine's memory; the engine frees its buffer.
      try{return Deno.UnsafePointerView.getArrayBuffer(pointer,size[0]).slice(0);}
      finally{library.symbols.web_render_free(pointer);}
    },
    font:(bytes,family,sha256)=>{
      const pointer=library.symbols.web_document_font_call_bin(bytes,bytes.length,cstring(family),cstring(sha256));
      if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
      try{return new Deno.UnsafePointerView(pointer).getCString();}
      finally{library.symbols.web_render_free(pointer);}
    },
  };
}
export function nativeBackend(path:string):DocumentBackend {return nativeBackends(path).text;}
/** Backend 1: the Wasm module. */
function wasmBackends(module:Module):Backends {
  return {
    text:(html,request,width,height)=>{
      const pointer=module.ccall("web_document_call","number",["string","string","number","number"],[html,request,width,height]);
      if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
      try{return module.UTF8ToString(pointer);}
      finally{module.ccall("web_render_free",null,["number"],[pointer]);}
    },
    bytes:(html,request,width,height)=>{
      const pointer=module.ccall("web_document_call_bin","number",["string","string","number","number","number"],[html,request,width,height,0]);
      if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
      // The first word is the total length. One copy out of the Wasm memory.
      try{const heap=module.HEAPU8,total=new DataView(heap.buffer,heap.byteOffset+pointer,4).getUint32(0,true);
        return heap.slice(pointer,pointer+total).buffer;}
      finally{module.ccall("web_render_free",null,["number"],[pointer]);}
    },
    font:(bytes,family,sha256)=>{
      if(!module._malloc||!module._free)throw new Error("Published Lean HTML engine has no font bytes call");
      // The file goes into the engine's heap, not onto its 4 MB stack.
      const input=module._malloc(Math.max(1,bytes.length));
      if(!input)throw new Error("Published Lean HTML engine allocation failed");
      try{
        module.HEAPU8.set(bytes,input);
        const pointer=module.ccall("web_document_font_call_bin","number",["number","number","string","string"],[input,bytes.length,family,sha256]);
        if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
        try{return module.UTF8ToString(pointer);}
        finally{module.ccall("web_render_free",null,["number"],[pointer]);}
      }finally{module._free(input);}
    },
  };
}
const decoder=new TextDecoder();
/** Read a bytes answer (WebDocument.packAnswer): the JSON head, and for each section its
byte offset and length in `buffer`. Every section starts at a multiple of 4 bytes. */
export function unpackAnswer(buffer:ArrayBuffer):{head:Record<string,unknown>;sections:[number,number][]} {
  const view=new DataView(buffer);
  if(buffer.byteLength<12||view.getUint32(0,true)!==buffer.byteLength)throw new Error("Unexpected Lean bytes answer length");
  const headSize=view.getUint32(4,true),count=view.getUint32(8,true);
  let offset=12+4*count;
  const head=JSON.parse(decoder.decode(new Uint8Array(buffer,offset,headSize)));
  offset+=headSize;
  const sections:[number,number][]=[];
  for(let i=0;i<count;i++){
    const length=view.getUint32(12+4*i,true);
    if(offset+length>buffer.byteLength)throw new Error("Lean bytes answer section out of range");
    sections.push([offset,length]);offset+=(length+3)&~3;
  }
  return {head,sections};
}
/** Put the sections that a scene names in place: storage floats as a Float32Array and
tile words as a Uint32Array, views of the one buffer, with no copy. */
function placeSections(scene:Record<string,unknown>,buffer:ArrayBuffer,sections:[number,number][]) {
  const at=(key:string)=>{
    const k=scene[key];if(typeof k!=="number")return undefined;
    const s=sections[k];if(!s||s[1]%4)throw new Error("Unexpected Lean bytes answer section");
    delete scene[key];return s;
  };
  const data=at("dataSection"),tiles=at("tilesSection");
  if(data)scene.data=new Float32Array(buffer,data[0],data[1]/4);
  if(tiles)scene.tiles=new Uint32Array(buffer,tiles[0],tiles[1]/4);
}
/** Lean sends the storage floats as the bytes the GPU reads; this only decodes and checks them. */
function sceneOf(result:Record<string,unknown>&{dataBase64?:unknown},width:number,height:number):HTMLArtifact {
  if(typeof result.dataBase64==="string"){
    const text=atob(result.dataBase64),bytes=new Uint8Array(text.length);
    for(let i=0;i<text.length;i++)bytes[i]=text.charCodeAt(i);
    result.data=new Float32Array(bytes.buffer);delete result.dataBase64;
  }
  const data=result.data as number[]|Float32Array,web=result.webRender as {links?:unknown}|undefined;
  if(result.abi!=="lean-svg-v1" || result.width!==width || result.height!==height ||
     !(Array.isArray(data)||data instanceof Float32Array) || !data.length || !data.every(Number.isFinite) ||
     typeof result.wgsl!=="string" || !Array.isArray(result.checks) || !Array.isArray(web?.links))
    throw new Error("Unexpected published Lean HTML scene ABI");
  return result as unknown as HTMLArtifact;
}
/** `answers:"bytes"` (the default) takes render answers as bytes with raw sections;
`"text"` takes the JSON text with Base64, the reference that tests compare with. */
export async function loadHTML(nativeEngine?:string,answers:"bytes"|"text"="bytes") {
  const module = await createModule() as unknown as Module;
  const backends=nativeEngine?nativeBackends(nativeEngine):wasmBackends(module);
  const backend=backends.text;
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
  /** A render through the bytes answer; the scenes get their sections as views. */
  const renderCall=(source:string,options:Record<string,unknown>,width:number,height:number)=>{
    // Decimal floats (binary:false) are a text answer only.
    if(answers==="text"||options.binary===false)return documentCall(source,options,width,height);
    sourceBound(source);
    if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))
      throw new Error("Native HTML viewport must be 1..4096 backing pixels");
    const request=JSON.stringify(options);
    if(encoder.encode(request).length>20971520)throw new Error("Document request exceeds 20 MiB");
    const buffer=backends.bytes(source,request,width,height);
    const {head,sections}=unpackAnswer(buffer);
    if(head?.error)throw new Error(`Lean HTML: ${head.error}`);
    for(const scene of [head,head.page,head.chrome])
      if(scene&&typeof scene==="object")placeSections(scene as Record<string,unknown>,buffer,sections);
    return head;
  };
  return {
    xmlStylesheet:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"xmlStylesheet"}) as {url:string|null},
    xslt:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"xslt"}) as {source:string;engine:string},
    inspect:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"inspect"}) as Inspection,
    // Lean reads the font once and holds it; later renders draw with it.
    fontLoad:(fontBase64:string,fontFamily:string,fontSha256:string)=>documentCall("",{op:"fontLoad",fontBase64,fontFamily,fontSha256}) as {family:string;glyphs:number},
    // The same, with the file as bytes: no Base64, and no size limit from the call stack.
    fontLoadBytes:(bytes:Uint8Array,fontFamily:string,fontSha256:string)=>{
      const result=JSON.parse(backends.font(bytes,fontFamily,fontSha256));
      if(result?.error)throw new Error(`Lean HTML: ${result.error}`);
      return result as {family:string;glyphs:number};
    },
    fontRequests:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"fontRequests"}),
    compile(source:string,width:number,height:number,options:Record<string,unknown>):HTMLArtifact {
      return sceneOf(renderCall(source,{binary:true,...options,op:"render"},width,height),width,height);
    },
    /** One render as two layers; the options must carry a shell. */
    compileLayers(source:string,width:number,height:number,options:Record<string,unknown>):HTMLLayers {
      const result=renderCall(source,{binary:true,...options,layers:true,op:"render"},width,height);
      const place=result.layers as HTMLLayerPlace|undefined;
      if(!place||!["top","view","bandTop","bandHeight","keepFrom","keepTo"].every(k=>Number.isSafeInteger((place as Record<string,unknown>)[k]))||typeof place.composite!=="string")
        throw new Error("Unexpected published Lean HTML layers ABI");
      return {layers:place,page:sceneOf(result.page,width,place.bandHeight),chrome:sceneOf(result.chrome,width,Math.max(1,place.top))};
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
