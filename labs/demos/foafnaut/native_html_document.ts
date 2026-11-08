import {pathToFileURL} from "node:url";
import {resolve} from "node:path";
import {sourceBound,MAX_SOURCE_BYTES,type HTMLEngine,type HTMLResource,type ScriptTurn} from "./native_html_engine.ts";

/** The view state of a page. Lean applies it; the host only keeps the values. */
export type PageView={textScalePercent?:number;selection?:"all"|number[];shell?:unknown;live?:boolean};
const MAX_RESOURCES=16, MAX_RESOURCE_BYTES=4*MAX_SOURCE_BYTES;
export function inputURL(input:string,file=false) {
  const url=file?pathToFileURL(resolve(input)):new URL(input);
  if(!["file:","http:","https:"].includes(url.protocol))throw new Error("Native HTML accepts file, HTTP and HTTPS inputs only");
  if(url.username||url.password)throw new Error("Credentials in native HTML URLs are unsupported");
  if(url.protocol==="file:"&&url.hostname&&url.hostname!=="localhost")throw new Error("Remote file URL hosts are unsupported");
  return url.href;
}
export function navigationURL(href:string,baseURL:string,documentURL:string) {
  const target=inputURL(new URL(href,baseURL).href);
  if(new URL(documentURL).protocol!=="file:"&&new URL(target).protocol==="file:")
    throw new Error("Remote HTML cannot read or navigate to local files");
  return target;
}
export async function readSource(url:string,signal?:AbortSignal):Promise<{url:string;source:string;bytes:number}> {
  const parsed=new URL(inputURL(url));
  const abort=()=>signal?.throwIfAborted();abort();
  let bytes:Uint8Array,finalURL=url;
  if(parsed.protocol==="file:") {
    if((await Deno.stat(parsed)).size>MAX_SOURCE_BYTES)throw new Error("Native HTML resource exceeds 1 MiB");
    bytes=await Deno.readFile(parsed);abort();
  } else {
    const response=await fetch(parsed,{signal:AbortSignal.any([AbortSignal.timeout(10000),...(signal?[signal]:[])])});
    finalURL=inputURL(response.url);
    if(!response.ok){await response.body?.cancel();throw new Error(`HTTP ${response.status}: ${url}`);}
    const reader=response.body?.getReader();
    if(!reader)throw new Error("Native HTML resource has no response body");
    const chunks:Uint8Array[]=[];let length=0;
    try {
      while(true){const next=await reader.read();if(next.done)break;
        length+=next.value.length;if(length>MAX_SOURCE_BYTES)throw new Error("Native HTML resource exceeds 1 MiB");
        chunks.push(next.value);
      }
    } finally {await reader.cancel();}
    bytes=new Uint8Array(length);let offset=0;
    for(const chunk of chunks){bytes.set(chunk,offset);offset+=chunk.length;}
  }
  abort();if(bytes.length>MAX_SOURCE_BYTES)throw new Error("Native HTML resource exceeds 1 MiB");
  // Older pages are often Latin-1 and say nothing about it. Browsers read those as windows-1252.
  let source:string;
  try{source=new TextDecoder("utf-8",{fatal:true}).decode(bytes);}
  catch{source=new TextDecoder("windows-1252").decode(bytes);}
  sourceBound(source);
  return {url:finalURL,source,bytes:bytes.length};
}
/** Limits on image bytes: each image, and all images of a page (Lean takes at most
8 MiB of Base64 text for a page, which is 6 MiB of bytes). */
export const MAX_IMAGE_BYTES=4*1048576, MAX_PAGE_IMAGE_BYTES=6*1048576;
/** Limit on the bytes of a tab icon (WebDocument.maxIconBytes). */
export const MAX_ICON_BYTES=65536;
/** An image may come from the page's own origin only: a file page reads local files, an
HTTP page its own scheme, host and port. There is no proxy. */
export function imageAllowed(url:string,documentURL:string) {
  const target=new URL(url),page=new URL(documentURL);
  if(page.protocol==="file:")return target.protocol==="file:";
  return target.protocol!=="file:"&&target.origin===page.origin;
}
async function readBytes(url:string,limit:number,signal?:AbortSignal):Promise<Uint8Array> {
  const parsed=new URL(inputURL(url));
  if(parsed.protocol==="file:") {
    if((await Deno.stat(parsed)).size>limit)throw new Error("image too large");
    return await Deno.readFile(parsed);
  }
  const response=await fetch(parsed,{signal:AbortSignal.any([AbortSignal.timeout(10000),...(signal?[signal]:[])])});
  if(!response.ok){await response.body?.cancel();throw new Error(`HTTP ${response.status}`);}
  const reader=response.body?.getReader();if(!reader)throw new Error("no body");
  const chunks:Uint8Array[]=[];let length=0;
  try {
    while(true){const next=await reader.read();if(next.done)break;
      length+=next.value.length;if(length>limit)throw new Error("image too large");chunks.push(next.value);}
  } finally {await reader.cancel();}
  const bytes=new Uint8Array(length);let offset=0;
  for(const chunk of chunks){bytes.set(chunk,offset);offset+=chunk.length;}
  return bytes;
}
/** Fetch the images Lean listed, as `{key,bytes}`. */
export async function fetchImageBytes(wanted:{key:string;url:string}[],documentURL:string,signal?:AbortSignal) {
  const images:{key:string;bytes:Uint8Array}[]=[];let total=0;
  for(const {key,url} of wanted) {
    signal?.throwIfAborted();
    try {
      if(!imageAllowed(url,documentURL))continue;
      const bytes=await readBytes(url,MAX_IMAGE_BYTES,signal);
      if(total+bytes.length>MAX_PAGE_IMAGE_BYTES)continue;
      total+=bytes.length;
      images.push({key,bytes});
    } catch(error) {
      if(signal?.aborted)throw error;
    }
  }
  return images;
}
function base64(bytes:Uint8Array) {
  let text="";
  for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
  return btoa(text);
}
export async function sha256Hex(bytes:Uint8Array) {
  return [...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes as Uint8Array<ArrayBuffer>))].map(b=>b.toString(16).padStart(2,"0")).join("");
}
/** Fetch the images Lean listed, as `{key,base64}` records for the compile request. */
export async function fetchImages(wanted:{key:string;url:string}[],documentURL:string,signal?:AbortSignal) {
  return (await fetchImageBytes(wanted,documentURL,signal)).map(({key,bytes})=>({key,base64:base64(bytes)}));
}
/** An engine that may hold images (WebDocument, issue 1292). */
type ImageHolder={
  imageInfo?:()=>unknown;
  imageLoad?:(bytes:Uint8Array,key:string,sha256:string)=>unknown;
};
/** The request fields for the fetched images: `heldImages` names, once the engine holds
them (it says so in `imageInfo`), so a render request does not carry the bytes; else
`images` with the bytes, for an engine from before held images (issue 1274). */
export async function imageOptions(engine:ImageHolder,fetched:{key:string;bytes:Uint8Array}[]):Promise<Record<string,unknown>> {
  if(!fetched.length)return {};
  const info=typeof engine.imageInfo==="function"&&typeof engine.imageLoad==="function"?await engine.imageInfo():undefined;
  if(!info)return {images:fetched.map(({key,bytes})=>({key,base64:base64(bytes)}))};
  const heldImages:{key:string;sha256:string}[]=[];
  for(const {key,bytes} of fetched){
    const sha256=await sha256Hex(bytes);
    await engine.imageLoad!(bytes,key,sha256);
    heldImages.push({key,sha256});
  }
  return {heldImages};
}
/** A refused page must say so in the window, not only in a log. */
export function refusalHTML(url:string,message:string) {
  const text=(s:string)=>s.replace(/&/g,"&amp;").replace(/</g,"&lt;");
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Page refused</title></head><body><h1>This page can not be shown</h1><p>${text(url)}</p><p>${text(message)}</p></body></html>`;
}
/** Page scripts (WebScripts.lean): the engine that holds the script session. A host sets
one when its engine answers `scriptSession` info (with BubblePopJS, or the QuickJS
guest module loaded); with none, a page with scripts is refused, as before. `start`
answers no turn when the setting says the scripts do not run (`scriptPlan`), and throws
when they are refused. */
export type ScriptHost={start(source:string,url:string,resources:{nodeId:number;source:string}[]):Promise<ScriptTurn|undefined>|ScriptTurn|undefined};
let scriptHost:ScriptHost|undefined;
export function setScriptHost(host:ScriptHost|undefined){scriptHost=host;}
/** The engine, or the same calls in a worker, which answer promises. prepareHTML awaits every call. */
export type PageEngine=(Pick<HTMLEngine,"xmlStylesheet"|"xslt"|"inspect"|"compile"|"selectedText">&ImageHolder)|ImageHolder&{
  xmlStylesheet(...a:Parameters<HTMLEngine["xmlStylesheet"]>):Promise<ReturnType<HTMLEngine["xmlStylesheet"]>>;
  xslt(...a:Parameters<HTMLEngine["xslt"]>):Promise<ReturnType<HTMLEngine["xslt"]>>;
  inspect(...a:Parameters<HTMLEngine["inspect"]>):Promise<ReturnType<HTMLEngine["inspect"]>>;
  compile(...a:Parameters<HTMLEngine["compile"]>):Promise<ReturnType<HTMLEngine["compile"]>>;
  selectedText(...a:Parameters<HTMLEngine["selectedText"]>):Promise<ReturnType<HTMLEngine["selectedText"]>>;
};
export async function prepareHTML(engine:PageEngine,url:string,signal?:AbortSignal,inline?:string) {
  const document=inline===undefined?await readSource(url,signal):{url,source:inline,bytes:inline.length},resources:HTMLResource[]=[];
  // View source shows each input and the result. Lean makes the page.
  const sources=[{kind:"Source",url:document.url,source:document.source}];
  // Lean finds the stylesheet and runs it. The host only fetches the bytes.
  const xml=await engine.xmlStylesheet(document.source,{url:document.url});
  if(xml.url) {
    navigationURL(xml.url,document.url,document.url);
    const sheet=await readSource(xml.url,signal);
    document.source=(await engine.xslt(document.source,{url:document.url,stylesheet:sheet.source,stylesheetURL:sheet.url})).source;
    sources[0].kind="XML source";
    sources.push({kind:"XSLT source",url:sheet.url,source:sheet.source},{kind:"Generated page",url:document.url,source:document.source});
  }
  const inspection=await engine.inspect(document.source,{url:document.url});
  const scripted=inspection.scripts.some(script=>script.kind!=="data");
  if(scripted&&!scriptHost)
    throw new Error("Page scripts need the QuickJS guest module (--quickjs-wasm FILE) and an engine with scriptSession; this page is refused");
  if(inspection.stylesheets.length>MAX_RESOURCES)throw new Error("Native HTML exceeds 16 external stylesheets");
  let resourceBytes=0;
  for(const descriptor of inspection.stylesheets) {
    signal?.throwIfAborted();
    // The URL and owning node are selected and resolved by Lean.
    navigationURL(descriptor.url,inspection.baseURL,document.url);
    const resource=await readSource(descriptor.url,signal);
    resourceBytes+=resource.bytes;if(resourceBytes>MAX_RESOURCE_BYTES)throw new Error("Native HTML stylesheets exceed 4 MiB");
    resources.push({nodeId:descriptor.nodeId,url:resource.url,source:resource.source});
  }
  // Lean lists the images it wants; the host fetches each one of the page's origin, with
  // size caps. One that fails or is refused is left out, and the page shows its alt text.
  // An engine that holds images gets each one once, and renders name them.
  const images=await imageOptions(engine,await fetchImageBytes(inspection.images??[],document.url,signal));
  // The tab icon that Lean chose (WebDocument.iconURL), by the rules of images: the page's
  // own origin only. One that fails or is refused leaves the tab with no icon.
  let iconBase64:string|undefined;
  if(inspection.icon)try{
    if(imageAllowed(inspection.icon,document.url))iconBase64=base64(await readBytes(inspection.icon,MAX_ICON_BYTES,signal));
  }catch(error){if(signal?.aborted)throw error;console.error(`Native HTML icon refused: ${inspection.icon}: ${String(error instanceof Error?error.message:error)}`);}
  const options:Record<string,unknown>={url:document.url,resources,...images};
  // Page scripts: Lean runs them (WebScripts). The host only fetches the bytes of `src`
  // scripts, as for stylesheets. The script session's commands are part of each render
  // request, so a render replays them over the parsed page.
  let script:{session:number;turn:ScriptTurn}|undefined;
  if(scripted&&scriptHost) {
    const supplied:{nodeId:number;source:string}[]=[];
    for(const descriptor of inspection.scripts) {
      if(descriptor.kind!=="classic"||!descriptor.src)continue;
      signal?.throwIfAborted();
      navigationURL(descriptor.url,inspection.baseURL,document.url);
      const resource=await readSource(descriptor.url,signal);
      sources.push({kind:"Script",url:resource.url,source:resource.source});
      supplied.push({nodeId:descriptor.nodeId,source:resource.source});
    }
    const turn=await scriptHost.start(document.source,document.url,supplied);
    if(turn){
      script={session:turn.session,turn};
      if(turn.commands?.length)options.commands=turn.commands;
    }
  }
  // Pages show in the font of loadFontFile, or else in the Lean bitmap face.
  signal?.throwIfAborted();
  return {
    url:document.url,baseURL:inspection.baseURL,title:inspection.title,source:document.source,sources,script,iconBase64,
    /** Whether the page has classic scripts (they run, or the setting says why not). */
    scripted,
    /** A later turn of the page's script session: its commands, when the DOM changed. */
    applyTurn:(turn:ScriptTurn)=>{if(script)script.turn=turn;if(turn.changed&&turn.commands)options.commands=turn.commands;return turn.changed;},
    // What compile needs, as plain data, so the engine in a worker can run it.
    request:(_width:number,_height:number,view:PageView={})=>({source:document.source,options:{...options,...view} as Record<string,unknown>}),
    compile:(width:number,height:number,view:PageView={})=>engine.compile(document.source,width,height,{...options,...view}),
    selectedText:(width:number,height:number,view:PageView={})=>engine.selectedText(document.source,width,height,{...options,...view}),
  };
}

/** Give the engine a font file. Lean reads it, shapes words and takes outlines; this only moves bytes.
`via:"bytes"` (the default) copies the file into engine memory; `"text"` sends it as Base64
in the JSON request, the reference path that tests compare with. */
export async function loadFontFile(engine:HTMLEngine,path:string,family="font",via:"bytes"|"text"="bytes",fallback=false) {
  return loadFontData(engine,await Deno.readFile(path),family,via,fallback);
}
/** As loadFontFile, for a file already in memory. */
/** `fallback:true` adds the font after the fonts the engine holds, for characters they lack. */
export async function loadFontData(engine:HTMLEngine,bytes:Uint8Array<ArrayBuffer>,family="font",via:"bytes"|"text"="bytes",fallback=false) {
  const sha=[...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("");
  if(via==="bytes")return engine.fontLoadBytes(bytes,family,sha,fallback);
  let text="";
  for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
  return engine.fontLoad(btoa(text),family,sha,fallback);
}
