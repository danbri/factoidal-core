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
/** The page script state of a document (issue 1271): the DOM commands that Lean replays,
the notice Lean puts on the page and the marker the chrome shows. A host that runs scripts
(native_html_scripts.ts) changes them; every request of the page carries them. */
export type ScriptState={commands:unknown[];notice:string;marker:string;
  sources:string[];nodes:unknown[];next:number;runtime?:{stop(reason:string):void;readonly stopped:string|null}};
/** Called before prepareHTML returns, so the first frame has the scripts' first changes. */
export type ScriptHook=(page:{url:string;baseURL:string;source:string;script:ScriptState})=>Promise<void>;
const MAX_SCRIPTS=64;
export async function prepareHTML(engine:PageEngine,url:string,signal?:AbortSignal,inline?:string,scripts?:ScriptHook) {
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
  // Lean lists the classic scripts (a module script is refused by Lean). The host fetches
  // the bytes of an external one, under the rules of a stylesheet.
  const classic=inspection.scripts.filter(script=>script.kind==="classic");
  if(classic.length>MAX_SCRIPTS)throw new Error("Native HTML exceeds 64 scripts");
  const script:ScriptState={commands:[],notice:"",marker:"",sources:[],nodes:inspection.nodes??[],next:inspection.next??0};
  let scriptBytes=0;
  for(const item of classic){
    signal?.throwIfAborted();
    let text=item.source;
    if(item.src){
      navigationURL(item.url,inspection.baseURL,document.url);
      const resource=await readSource(item.url,signal);text=resource.source;
      sources.push({kind:"Script",url:resource.url,source:text});
    }
    scriptBytes+=text.length;if(scriptBytes>MAX_SOURCE_BYTES)throw new Error("Native HTML scripts exceed 1 MiB");
    script.sources.push(text);
  }
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
  const options={url:document.url,resources};
  // The commands and the notice of the page scripts, as they are when the call is made.
  const scripted=()=>({...(script.commands.length?{commands:script.commands}:{}),...(script.notice?{scriptNotice:script.notice}:{})});
  // Pages show in the font of loadFontFile, or else in the Lean bitmap face.
  signal?.throwIfAborted();
  const page={
    url:document.url,baseURL:inspection.baseURL,title:inspection.title,source:document.source,sources,script,
    // What compile needs, as plain data, so the engine in a worker can run it.
    request:(_width:number,_height:number,view:PageView={})=>({source:document.source,options:{...options,...scripted(),...view} as Record<string,unknown>}),
    compile:(width:number,height:number,view:PageView={})=>engine.compile(document.source,width,height,{...options,...scripted(),...view}),
    selectedText:(width:number,height:number,view:PageView={})=>engine.selectedText(document.source,width,height,{...options,...scripted(),...view}),
  };
  if(script.sources.length){
    if(scripts)await scripts(page);
    // A host with no script engine says so on the page: the scripts are never silently inert.
    else script.notice="Page scripts did not run: this host has no script engine (issue 1271)";
  }
  signal?.throwIfAborted();
  return page;
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
