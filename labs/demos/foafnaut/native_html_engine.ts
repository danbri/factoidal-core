// Byte/JSON transport for the published Lean HTML engine. No host markup parser.
// This ignored runtime is installed only after checking the Builds manifest.
// @ts-ignore generated release module
import createModule from "./.build/native-html/runtime/web-render.mjs";

/** What a tab or scroll command needs: tab count and active tab; scroll, view height, scroll limit and screen scale. */
export type CommandState={tabs?:number;active?:number;scroll?:number;view?:number;scrollLimit?:number;scale?:number};
export type HTMLArtifact = {
  abi:string; width:number; height:number; data:number[]|Float32Array; wgsl:string; tiles:number[]|Uint32Array;
  primitiveCount:number; checks:{x:number;y:number;rgb:number[]}[];
  webRender:{links:unknown[][];[name:string]:unknown};
};
/** A render with `layers:true` (WebDocument.layersJSON): the chrome layer in window
rows, the page layer in band rows from page row `bandTop`, and the WGSL that puts them
in the window. `keepFrom`..`keepTo` are the scrolls that this band shows with no new render. */
export type HTMLLayerPlace = {top:number;view:number;bandTop:number;bandHeight:number;keepFrom:number;keepTo:number;composite:string;hoverRules?:boolean;scrollLimit?:number};
/** Lean's answer to a pointer press: the chrome control or the link pressed, and the rectangles the composite darkens. */
export type PressAnswer = {control:string|null;sourceNode?:number|null;href?:string;rects:number[][]};
export type HTMLLayers = {layers:HTMLLayerPlace;page:HTMLArtifact;chrome:HTMLArtifact};
export type Inspection = {
  baseURL:string;
  title:string;
  scripts:{kind:string;type:string;src:string;nodeId:number;url:string}[];
  stylesheets:{nodeId:number;url:string}[];
  /** Images that Lean wants (SVG `image`, HTML `img`), by store key; an older engine lists none for `img`. */
  images?:{key:string;url:string}[];
  /** The icon Lean chose for the tab (HTML §4.6.7.8), or null. */
  icon?:string|null;
};
/** A tab icon as Lean prepared it (WebDocument.iconPrepare). */
export type TabIcon={kind:"svg";source:string}|{kind:"bitmap";width:number;height:number;rgba:string};
export type History = {entries:string[];index:number};
/** The answer of a font load: the font's family and glyph count, and how many fonts the engine holds. */
export type FontLoaded = {family:string;glyphs:number;fonts:number};
export type HistoryAnswer = {history:History;url:string|null;canBack:boolean;canForward:boolean};
export type GraphFrame = {model:string;commands:string[]};
/** The address bar's edit state; the host keeps it and sends it back in `shell`. */
export type ShellEdit = {address:string;cursor:number;anchor:number;undo:unknown;redo:unknown;typing:boolean;menu?:boolean};
/** One button of the address menu (WebShell.menuActions): its rectangle in CSS px, and for copy the text. */
export type MenuAction = {action:"copy"|"paste";control:string;rect:[number,number,number,number];text?:string};
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
/** What a touch or a trackpad gesture means (WebGesture.lean, op gesture). */
export type GestureAnswer = {phase:"pending"|"swipe"|"other";direction:"back"|"forward"|null;progress:number;navigate:boolean;hint:number};
/** Where a link or an address goes (WebRoute.lean, docs/web/hub/foafnaut/link-route.mjs). */
export type LinkRoute = {route:"page";name:string;url:string}|{route:"graph";url:string}|{route:"navigate";url:string}|
  {route:"system";url:string}|{route:"command";name:string;argument:string}|{route:"refuse";url:string;reason:string};
export type HTMLResource = {nodeId:number;url:string;source:string};
/** One turn of a script session (WebScripts.turnAnswer). `commands` is the whole command
list, given only when `changed`: a host lays the page out again only then. */
export type ScriptTurn = {session:number;clock:number;changed:boolean;commandCount:number;commands?:unknown[];
  logs:string[];errors:string[];timers:number;nextTimer:number|null;frames:number;nextWake:number|null;quiet:boolean;
  instructions:number;jobs:number;tasks:number;ns:number;
  /** Lean-validated page GPU commands of this turn (L4Factoidal.PageGpu) and their page session. */
  gpu?:unknown[];gpuPage?:number};
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
/** An image as bytes (`web_document_image_call_bin`, WebDocument.imageLoadBin), held by key
and SHA-256; undefined when the engine has no such export. The answer is the imageLoad JSON. */
export type ImageBackend=(bytes:Uint8Array,key:string,sha256:string)=>string;
type Backends={text:DocumentBackend;bytes:BytesBackend;font:FontBackend;image?:ImageBackend};
/** The answer of `imageInfo`: the engine holds images (WebDocument, issue 1292). */
export type ImageInfo={engine:string;ops:string[];maxImages:number;maxBytes:number;held:number;layoutSlots:number};
/** The answer of `frameWork`: layouts, kept layouts used and pointer states painted with no layout. */
export type FrameWork={layouts:number;kept:number;repaints:number;layoutSlots:number;pagesMade?:number;pagesKept?:number};
/** Backend 2: a native dylib of the same Lean objects. Every call must come from one thread; no nonblocking FFI. */
export function nativeBackends(path:string):Backends {
  const library=Deno.dlopen(path,{
    web_document_call:{parameters:["buffer","buffer","u32","u32"],result:"pointer"},
    web_document_call_bin:{parameters:["buffer","buffer","u32","u32","buffer"],result:"pointer"},
    web_document_font_call_bin:{parameters:["buffer","u32","buffer","buffer","u32"],result:"pointer"},
    // An engine from before held images has no such symbol (issue 1274): it stays null.
    web_document_image_call_bin:{parameters:["buffer","u32","buffer","buffer"],result:"pointer",optional:true},
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
    image:library.symbols.web_document_image_call_bin?(bytes,key,sha256)=>{
      const pointer=library.symbols.web_document_image_call_bin!(bytes,bytes.length,cstring(key),cstring(sha256));
      if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
      try{return new Deno.UnsafePointerView(pointer).getCString();}
      finally{library.symbols.web_render_free(pointer);}
    }:undefined,
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
    // An engine from before held images has no such export (issue 1274).
    image:typeof (module as unknown as Record<string,unknown>)._web_document_image_call_bin==="function"&&module._malloc&&module._free?(bytes,key,sha256)=>{
      const input=module._malloc!(Math.max(1,bytes.length));
      if(!input)throw new Error("Published Lean HTML engine allocation failed");
      try{
        module.HEAPU8.set(bytes,input);
        const pointer=module.ccall("web_document_image_call_bin","number",["number","number","string","string"],[input,bytes.length,key,sha256]);
        if(!pointer)throw new Error("Published Lean HTML engine allocation failed");
        try{return module.UTF8ToString(pointer);}
        finally{module.ccall("web_render_free",null,["number"],[pointer]);}
      }finally{module._free!(input);}
    }:undefined,
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
/** The link regions of a frame as text, made once per array: `hit` and `press` on the same
 * frame send the same string, and Lean decodes it once (WebDocument.decodeLinks). */
const linkTexts=new WeakMap<object,string>();
function linksText(links:unknown[]):string {
  let text=linkTexts.get(links);
  if(text===undefined){text=JSON.stringify(links);linkTexts.set(links,text);}
  return text;
}
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
  // Bytes of JSON request sent to Lean for renders: the last one and the most (frame_work_test.ts).
  const sent={renders:0,lastRenderBytes:0,maxRenderBytes:0};
  const countRender=(request:string)=>{
    const n=encoder.encode(request).length;
    sent.renders++;sent.lastRenderBytes=n;sent.maxRenderBytes=Math.max(sent.maxRenderBytes,n);
    return n;
  };
  const documentCall=(source:string,options:Record<string,unknown>,width=1,height=1)=>{
    sourceBound(source);
    if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))
      throw new Error("Native HTML viewport must be 1..4096 backing pixels");
    const request=JSON.stringify(options);
    if(options.op==="render")countRender(request);
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
    if(countRender(request)>20971520)throw new Error("Document request exceeds 20 MiB");
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
    // Held images (WebDocument, issue 1292): sent once, named by renders in `heldImages`.
    // `imageInfo` answers undefined for an engine from before them, which then gets
    // `images` with the bytes in each request, as before (issue 1274).
    imageInfo:():ImageInfo|undefined=>{
      try{const info=documentCall("",{op:"imageInfo"}) as ImageInfo;return Array.isArray(info?.ops)&&info.ops.includes("imageLoad")?info:undefined;}
      catch{return undefined;}
    },
    imageLoad:(bytes:Uint8Array,key:string,sha256:string)=>{
      if(backends.image){
        const result=JSON.parse(backends.image(bytes,key,sha256));
        if(result?.error)throw new Error(`Lean HTML: ${result.error}`);
        return result as {key:string;sha256:string;bytes:number;held:number};
      }
      let text="";
      for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
      return documentCall("",{op:"imageLoad",key,sha256,imageBase64:btoa(text)}) as {key:string;sha256:string;bytes:number;held:number};
    },
    imageDrop:()=>documentCall("",{op:"imageDrop"}) as {held:number},
    /** Lean's count of its frame work; undefined for an engine without it. */
    frameWork:(reset=false):FrameWork|undefined=>{
      try{return documentCall("",{op:"frameWork",...(reset?{reset:true}:{})}) as FrameWork;}catch{return undefined;}
    },
    /** Bytes of JSON request this host sent to Lean for renders. */
    requestBytes:()=>({...sent}),
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
    // The control under a press, and whether this press opens the address menu (`how`: tap, hold or context).
    shellMenu:(shell:unknown,x:number,y:number,width:number,how:string,touch=false)=>
      documentCall("",{op:"shellHit",shell,x,y,width,how,touch}) as {control:string|null;menu?:boolean},
    // The address menu's buttons and the text Copy writes; empty with the menu closed.
    shellActions:(shell:unknown,width:number)=>(documentCall("",{op:"shellActions",shell,width}) as {actions:MenuAction[]}).actions,
    // A press: the control or the link under the pointer (`row` is the page-layer row) and what to darken.
    press:(shell:unknown,x:number,y:number,width:number,row:number,links:unknown[])=>documentCall("",{op:"press",shell,x,y,width,row:Math.max(0,Math.floor(row)),linksText:linksText(links)}) as PressAnswer,
    // The system pointer for a window point: "arrow", "hand" or "text" (issue 1268).
    pointerCursor:(request:{shell:unknown;x:number;y:number;width:number;model?:string;links?:string;pageY?:number})=>
      (documentCall("",{...request,op:"pointerCursor"}) as {cursor:string}).cursor,
    shellText:(shell:unknown,text:string)=>documentCall("",{op:"shellText",shell,text}) as ShellEdit,
    shellKey:(shell:unknown,key:number,modifiers=0)=>documentCall("",{op:"shellKey",shell,key,modifiers}) as ShellEdit,
    // Select all, copy, cut, paste, undo, redo and focus in the address bar; `clipboard` is the text to copy.
    shellEdit:(shell:unknown,action:string,text="")=>documentCall("",{op:"shellEdit",shell,action,text}) as ShellEdit&{clipboard?:string|null;go?:string|null},
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
    // The final action for a link (`href`) or a typed address (`address`). An older engine
    // answers "unknown document operation" (link-route.mjs then answers instead).
    shellRoute:(request:Record<string,unknown>)=>documentCall("",{...request,op:"shellRoute"}) as LinkRoute,
    // A back or forward swipe (WebGesture.lean): `action` info, touch or wheel. An older engine
    // answers "unknown document operation"; a host then has no swipes.
    gesture:(request:Record<string,unknown>)=>documentCall("",{...request,op:"gesture"}) as GestureAnswer,
    // Browser state (WebState.lean): bookmarks, history, settings and tabs as LWS resources.
    state:(op:string,request:Record<string,unknown>={})=>documentCall("",{...request,op}),
    // Page scripts run by Lean (WebScripts.lean): QuickJS-NG in WasmVM on the page's arena,
    // the Lean event loop deciding each callback. An older engine answers "unknown document
    // operation" to scriptInfo; a host then keeps refusing scripted pages (issue 1274).
    scriptInfo:()=>documentCall("",{op:"scriptSession",action:"info"}) as {ops:string[];module:boolean;bytes:number;engine:string},
    /** The guest module, as bytes through the font byte call (family `guest:quickjs`). */
    scriptLoad:(bytes:Uint8Array)=>{
      const result=JSON.parse(backends.font(bytes,"guest:quickjs","",false));
      if(result?.error)throw new Error(`Lean HTML: ${result.error}`);
      return result as {module:boolean;bytes:number};
    },
    scriptSession:(source:string,request:Record<string,unknown>)=>documentCall(source,{...request,op:"scriptSession"}) as ScriptTurn,
    /** The node under a window point, for a click that page scripts receive. */
    nodeAt:(source:string,width:number,height:number,options:Record<string,unknown>)=>
      (documentCall(source,{...options,op:"nodeAt"},width,height) as {node:number|null}).node,
    /** The node under a window point and the coordinates of its pointer events (WebHit). */
    pointerAt:(source:string,width:number,height:number,options:Record<string,unknown>)=>
      documentCall(source,{...options,op:"nodeAt"},width,height) as {node:number|null}&Record<string,number>,
    // Lean decides what a menu command and a pointer release mean.
    // `state` gives the tab count, the scroll and the view, from which Lean answers a tab or a scroll.
    command:(command:number,textScalePercent:number,history?:History,focused=false,state:CommandState={})=>documentCall("",{op:"command",command,textScalePercent,focused,...state,...(history?{history}:{})}) as
      {action:string;target?:"address"|"page";textScalePercent:number;tab?:number;scrollTo?:number;refused?:string}&Partial<HistoryAnswer>,
    // The settings page's text size (WebSelection.textZoom): the zoom for `zoom` (up, down,
    // reset, a percent; empty: no change) and the text size shown. An older engine answers
    // "unknown document operation".
    textZoom:(zoom:string,textScalePercent:number,zoomUnit=100)=>documentCall("",{op:"textZoom",zoom,textScalePercent,zoomUnit}) as
      {textScalePercent:number;shown:number;default:number;min:number;max:number;step:number;refused?:string},
    // The tab icon from the Base64 bytes of an icon resource, for a screen of `scale`.
    iconPrepare:(base64:string,scale:number)=>documentCall("",{op:"iconPrepare",base64,scale}) as TabIcon,
    // A key that the macOS menu did not take: the command of Lean's key table, or null.
    pageKey:(key:number,modifiers:number)=>(documentCall("",{op:"pageKey",key,modifiers}) as {command:number|null}).command,
    historyPush:(history:History,url:string)=>documentCall("",{op:"historyPush",history,url}) as HistoryAnswer,
    keyCommand:(platform:string,modifier:string,key:string)=>(documentCall("",{op:"keyCommand",platform,modifier,key}) as {command:number|null}).command,
    pointerUp:(selection:number[])=>(documentCall("",{op:"pointerUp",selection}) as {action:string}).action,
    selectedText:(source:string,width:number,height:number,options:Record<string,unknown>)=>
      (documentCall(source,{...options,op:"selectedText"},width,height) as {text:string}).text,
    hit(artifact:HTMLArtifact,x:number,y:number):{href:string;sourceNode:number}|null {
      if(!Number.isFinite(x)||!Number.isFinite(y))return null;
      return call("web_render_hit",["string","number","number","number","number"],
        [linksText(artifact.webRender.links),artifact.width,artifact.height,x,y]);
    },
  };
}
export type HTMLEngine = Awaited<ReturnType<typeof loadHTML>>;
