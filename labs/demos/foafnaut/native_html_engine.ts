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
export type HTMLLayerPlace = {top:number;view:number;bandTop:number;bandHeight:number;keepFrom:number;keepTo:number;composite:string;hoverRules?:boolean};
/** Lean's answer to a pointer press: the chrome control or the link pressed, and the rectangles the composite darkens. */
export type PressAnswer = {control:string|null;sourceNode?:number|null;href?:string;rects:number[][]};
export type HTMLLayers = {layers:HTMLLayerPlace;page:HTMLArtifact;chrome:HTMLArtifact};
export type Inspection = {
  baseURL:string;
  title:string;
  scripts:{kind:string;type:string;src:string}[];
  stylesheets:{nodeId:number;url:string}[];
  /** Images that Lean wants (SVG `image`, HTML `img`), by store key; an older engine lists none for `img`. */
  images?:{key:string;url:string}[];
};
export type History = {entries:string[];index:number};
/** The answer of a font load: the font's family and glyph count, and how many fonts the engine holds. */
export type FontLoaded = {family:string;glyphs:number;fonts:number};
export type HistoryAnswer = {history:History;url:string|null;canBack:boolean;canForward:boolean};
export type GraphFrame = {model:string;commands:string[]};
/** The address bar's edit state; the host keeps it and sends it back in `shell`. */
export type ShellEdit = {address:string;cursor:number;anchor:number;undo:unknown;redo:unknown;typing:boolean};
export type PrintLayout = {contentHeight:number;pages:[number,number][]};
export type WasmValue = {type:string;value:string;shown?:string};
export type WasmRequest = {wasmBase64:string;export?:string;args?:WasmValue[];fuel?:number};
export type WasmInfo = {engine:string;ops:string[];maxModuleBytes:number;defaultFuel:number;maxFuel:number;pageLimit:number;imports:string[]};
/** A run: the stage reached, and the values, trap or exception, with counts and time. */
export type WasmRun = {engine:string;bytes:number;stage:string;outcome:string;message?:string;values?:WasmValue[];
  stages?:{decode:number;validate:number;instantiate:number};exports?:{name:string;kind:string;params?:string[];results?:string[]}[];
  imports?:{module:string;name:string}[];instructions?:number;ns?:number;perSecond?:number;fuel?:number;prints?:string[]};
export type WasmSpecSample = {pass:number;fail:number;notRun:number;files:{name:string;pass:number;fail:number;notRun:number;ns:number;fails:string[]}[]};
/** An operator of a SPARQL plan, in execution order; `children` are earlier operators. */
export type SparqlOperator = {id:number;kind:string;label:string;why:string;children:number[];estimate:number|null;actual:number|null;ns:number};
export type SparqlCapabilityPlan = {bgp:number;family:number;approximate:boolean;cost:number;rows:number;note:string;
  steps:{source:string;args:string;inputs:string;estimatedCalls:number;estimatedRows:number;estimatedCost:number;rows:number}[]};
export type SparqlExplain = {ok:true;form:string;operators:SparqlOperator[];root:number;capability:SparqlCapabilityPlan[];
  capabilityWholeQuery:boolean;answer:string;ns:number;vars:string[];rows:Record<string,string|null>[];rowCount:number};
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
export type FontBackend=(bytes:Uint8Array,family:string,sha256:string,fallback:boolean)=>string;
type Backends={text:DocumentBackend;bytes:BytesBackend;font:FontBackend};
/** Backend 2: a native dylib of the same Lean objects. Every call must come from one thread; no nonblocking FFI. */
export function nativeBackends(path:string):Backends {
  const library=Deno.dlopen(path,{
    web_document_call:{parameters:["buffer","buffer","u32","u32"],result:"pointer"},
    web_document_call_bin:{parameters:["buffer","buffer","u32","u32","buffer"],result:"pointer"},
    web_document_font_call_bin:{parameters:["buffer","u32","buffer","buffer","u32"],result:"pointer"},
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
    font:(bytes,family,sha256,fallback)=>{
      const pointer=library.symbols.web_document_font_call_bin(bytes,bytes.length,cstring(family),cstring(sha256),fallback?1:0);
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
    font:(bytes,family,sha256,fallback)=>{
      if(!module._malloc||!module._free)throw new Error("Published Lean HTML engine has no font bytes call");
      // The file goes into the engine's heap, not onto its 4 MB stack.
      const input=module._malloc(Math.max(1,bytes.length));
      if(!input)throw new Error("Published Lean HTML engine allocation failed");
      try{
        module.HEAPU8.set(bytes,input);
        const pointer=module.ccall("web_document_font_call_bin","number",["number","number","string","string","number"],[input,bytes.length,family,sha256,fallback?1:0]);
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
    // fallback:true adds the font to the engine's list, after the fonts it holds;
    // otherwise the font replaces the list. The answer counts the fonts held.
    fontLoad:(fontBase64:string,fontFamily:string,fontSha256:string,fallback=false)=>
      documentCall("",{op:"fontLoad",fontBase64,fontFamily,fontSha256,...(fallback?{fallback:true}:{})}) as FontLoaded,
    // The same, with the file as bytes: no Base64, and no size limit from the call stack.
    fontLoadBytes:(bytes:Uint8Array,fontFamily:string,fontSha256:string,fallback=false)=>{
      const result=JSON.parse(backends.font(bytes,fontFamily,fontSha256,fallback));
      if(result?.error)throw new Error(`Lean HTML: ${result.error}`);
      return result as FontLoaded;
    },
    fontRequests:(source:string,options:Record<string,unknown>)=>documentCall(source,{...options,op:"fontRequests"}),
    // The CSS declarations that Lean's profile can not read and drops, "property: value (reason)".
    droppedCSS:(source:string,options:Record<string,unknown>)=>(documentCall(source,{...options,op:"droppedCSS"}) as {dropped:string[]}).dropped,
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
    // A press: the control or the link under the pointer (`row` is the page-layer row) and what to darken.
    press:(shell:unknown,x:number,y:number,width:number,row:number,links:unknown[])=>documentCall("",{op:"press",shell,x,y,width,row:Math.max(0,Math.floor(row)),links}) as PressAnswer,
    // The system pointer for a window point: "arrow", "hand" or "text" (issue 1268).
    pointerCursor:(request:{shell:unknown;x:number;y:number;width:number;model?:string;links?:string;pageY?:number})=>
      (documentCall("",{...request,op:"pointerCursor"}) as {cursor:string}).cursor,
    shellText:(shell:unknown,text:string)=>documentCall("",{op:"shellText",shell,text}) as ShellEdit,
    shellKey:(shell:unknown,key:number,modifiers=0)=>documentCall("",{op:"shellKey",shell,key,modifiers}) as ShellEdit,
    // Select all, copy, cut, paste, undo, redo and focus in the address bar; `clipboard` is the text to copy.
    shellEdit:(shell:unknown,action:string,text="")=>documentCall("",{op:"shellEdit",shell,action,text}) as ShellEdit&{clipboard:string|null},
    // Where the pages of a print layout break (`media:"print"` in the options).
    printLayout:(source:string,width:number,height:number,options:Record<string,unknown>)=>
      documentCall(source,{...options,op:"printLayout"},width,height) as PrintLayout,
    shellSubmit:(address:string)=>documentCall("",{op:"shellSubmit",address}) as ShellGo,
    // The FOAF graph page: the model is Lean's; the host keeps it as text.
    graphStart:(rdf:string,width:number,height:number,shell:unknown)=>documentCall("",{op:"graphStart",rdf,width,height,shell}) as GraphFrame,
    graphEvent:(model:string,kind:number,a:number,b:number,width:number,shell:unknown)=>documentCall("",{op:"graphEvent",model,kind,a,b,width,shell}) as GraphFrame,
    graphPage:(model:string)=>(documentCall("",{op:"graphPage",model}) as {source:string}).source,
    sourcePage:(kind:string,url:string,source:string)=>(documentCall("",{op:"sourcePage",kind,url,source}) as {source:string}).source,
    // WebAssembly run by WasmVM, Lean's engine, inside this engine (WebWasm.lean, issue 1244).
    // Modules are Base64 in the request; values use the spec-test JSON form.
    wasmInfo:()=>documentCall("",{op:"wasmInfo"}) as WasmInfo,
    wasmRun:(request:WasmRequest)=>documentCall("",{...request,op:"wasmRun"}) as WasmRun,
    wasmSpecSample:()=>documentCall("",{op:"wasmSpecSample"}) as WasmSpecSample,
    /** The page foafnaut:wasm, as HTML that Lean then lays out. */
    wasmPage:(request:Partial<WasmRequest>&{url?:string}={})=>documentCall("",{...request,op:"wasmPage"}) as {source:string;title:string},
    // The SPARQL planner drawn as live debug (WebSparql.lean). An older engine answers
    // "unknown document operation".
    sparqlInfo:()=>documentCall("",{op:"sparqlInfo"}) as {engine:string;ops:string[];datasets:string[];examples:{name:string;query:string}[]},
    sparqlExplain:(request:{query:string;dataset?:string;data?:string;run?:boolean})=>documentCall("",{...request,op:"sparqlExplain"}) as SparqlExplain,
    /** The page foafnaut:sparql; `argument` is the address after `foafnaut:sparql/`. */
    sparqlPage:(argument:string)=>documentCall("",{op:"sparqlPage",argument}) as {source:string;title:string;next:string},
    shellLink:(href:string)=>documentCall("",{op:"shellLink",href}) as ShellGo,
    // Browser state (WebState.lean): bookmarks, history, settings and tabs as LWS resources.
    state:(op:string,request:Record<string,unknown>={})=>documentCall("",{...request,op}),
    // Lean decides what a menu command and a pointer release mean.
    command:(command:number,textScalePercent:number,history?:History,focused=false)=>documentCall("",{op:"command",command,textScalePercent,focused,...(history?{history}:{})}) as
      {action:string;target?:"address"|"page";textScalePercent:number}&Partial<HistoryAnswer>,
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
