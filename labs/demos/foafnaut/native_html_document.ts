import {pathToFileURL} from "node:url";
import {resolve} from "node:path";
import {sourceBound,MAX_SOURCE_BYTES,type HTMLEngine,type HTMLResource} from "./native_html_engine.ts";

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
/** Fetch the images Lean listed, as `{key,base64}` records for the compile request. */
export async function fetchImages(wanted:{key:string;url:string}[],documentURL:string,signal?:AbortSignal) {
  const images:{key:string;base64:string}[]=[];let total=0;
  for(const {key,url} of wanted) {
    signal?.throwIfAborted();
    try {
      if(!imageAllowed(url,documentURL))continue;
      const bytes=await readBytes(url,MAX_IMAGE_BYTES,signal);
      if(total+bytes.length>MAX_PAGE_IMAGE_BYTES)continue;
      total+=bytes.length;
      let text="";
      for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
      images.push({key,base64:btoa(text)});
    } catch(error) {
      if(signal?.aborted)throw error;
    }
  }
  return images;
}
/** A refused page must say so in the window, not only in a log. */
export function refusalHTML(url:string,message:string) {
  const text=(s:string)=>s.replace(/&/g,"&amp;").replace(/</g,"&lt;");
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Page refused</title></head><body><h1>This page can not be shown</h1><p>${text(url)}</p><p>${text(message)}</p></body></html>`;
}
/** The engine, or the same calls in a worker, which answer promises. prepareHTML awaits every call. */
export type PageEngine=Pick<HTMLEngine,"xmlStylesheet"|"xslt"|"inspect"|"compile"|"selectedText">|{
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
  if(inspection.scripts.some(script=>script.kind!=="data"))
    throw new Error("Native HTML milestone does not execute scripts; classic/module script input is refused");
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
  const images=await fetchImages(inspection.images??[],document.url,signal);
  const options={url:document.url,resources,...(images.length?{images}:{})};
  // Pages show in the font of loadFontFile, or else in the Lean bitmap face.
  signal?.throwIfAborted();
  return {
    url:document.url,baseURL:inspection.baseURL,title:inspection.title,source:document.source,sources,
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
