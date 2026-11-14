import {pathToFileURL} from "node:url";
import {resolve} from "node:path";
import {sourceBound,MAX_SOURCE_BYTES,type HTMLEngine,type HTMLResource,type ScriptTurn} from "./native_html_engine.ts";
import {addEntries,noteDiagnostics,noteTurn} from "./native_console.ts";
import {netAnswer,type NetWire} from "./native_net.ts";
import {loadSubresource} from "../../../docs/web/hub/foafnaut/page-load.mjs";

/** The view state of a page. Lean applies it; the host only keeps the values. */
// zoomUnit: the backing pixels for each point, in percent (WebDocument.zoomUnit): Lean lays the page
// out in points (CSS px) and draws it at the backing scale.
export type PageView={textScalePercent?:number;zoomUnit?:number;selection?:"all"|number[];shell?:unknown;live?:boolean;find?:{query:string;current:number}};
// The most linked style sheets fetched for a page. It was 16 until 2026-11-14: developer.mozilla.org links 18 and
// lean-lang.org 31, and the rest were drawn without. The engine bounds the sheets' text (WebDocument.sheetsIn, 2 MiB).
const MAX_RESOURCES=64, MAX_RESOURCE_BYTES=2*MAX_SOURCE_BYTES;
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
/** Lean's decode of a page's bytes (HTMLEngine.decodeDocument: HTML encoding sniffing and the
Encoding Standard's decoders), given the HTTP Content-Type ("" for none); undefined when the
engine has no such op. */
export type PageDecoder=(bytes:Uint8Array,contentType:string,fallback?:string,locale?:string)=>{encoding:string;source:string}|undefined|Promise<{encoding:string;source:string}|undefined>;
/** The user's default for pages that declare no encoding (the setting, "" is detect) and the
system's language; the host sets them, Lean decides with them (WebDocument.decodeBinWith). */
let pageDecoding={fallback:"",locale:""};
export function setPageDecoding(next:{fallback?:string;locale?:string}){pageDecoding={...pageDecoding,...next};}
export async function readSource(url:string,signal?:AbortSignal,decode?:PageDecoder):Promise<{url:string;source:string;bytes:number;encoding?:string;raw:Uint8Array;contentType:string;contentTypeOptions:string}> {
  const parsed=new URL(inputURL(url));
  const abort=()=>signal?.throwIfAborted();abort();
  let bytes:Uint8Array,finalURL=url,contentType="",contentTypeOptions="";
  if(parsed.protocol==="file:") {
    if((await Deno.stat(parsed)).size>MAX_SOURCE_BYTES)throw new Error("Native HTML resource exceeds 16 MiB");
    bytes=await Deno.readFile(parsed);abort();
  } else {
    const response=await fetch(parsed,{signal:AbortSignal.any([AbortSignal.timeout(10000),...(signal?[signal]:[])])});
    finalURL=inputURL(response.url);contentType=response.headers.get("content-type")??"";
    // For a script fetch, Lean decides with this header whether the answer is a script (nosniff).
    contentTypeOptions=response.headers.get("x-content-type-options")??"";
    if(!response.ok){await response.body?.cancel();throw new Error(`HTTP ${response.status}: ${url}`);}
    const reader=response.body?.getReader();
    if(!reader)throw new Error("Native HTML resource has no response body");
    const chunks:Uint8Array[]=[];let length=0;
    try {
      while(true){const next=await reader.read();if(next.done)break;
        length+=next.value.length;if(length>MAX_SOURCE_BYTES)throw new Error("Native HTML resource exceeds 16 MiB");
        chunks.push(next.value);
      }
    } finally {await reader.cancel();}
    bytes=new Uint8Array(length);let offset=0;
    for(const chunk of chunks){bytes.set(chunk,offset);offset+=chunk.length;}
  }
  abort();if(bytes.length>MAX_SOURCE_BYTES)throw new Error("Native HTML resource exceeds 16 MiB");
  // Lean turns the bytes into text (WebDocument.decodeBin): the BOM, the HTTP charset, the page's
  // meta declaration, else UTF-8 for UTF-8 bytes and windows-1252 otherwise. An engine from before
  // that op leaves UTF-8 decoding (the Encoding Standard's "UTF-8 decode").
  const decoded=decode?await decode(bytes,contentType):undefined;
  const source=decoded?decoded.source:new TextDecoder("utf-8").decode(bytes);
  sourceBound(source);
  return {url:finalURL,source,bytes:bytes.length,raw:bytes,contentType,contentTypeOptions,...(decoded?{encoding:decoded.encoding}:{})};
}
/** Limits on image bytes: each image, and all images of a page (Lean takes at most
8 MiB of Base64 text for a page, which is 6 MiB of bytes). */
export const MAX_IMAGE_BYTES=4*1048576, MAX_PAGE_IMAGE_BYTES=6*1048576;
/** Limit on the bytes of a tab icon (WebDocument.maxIconBytes). */
export const MAX_ICON_BYTES=65536;
/** The rule for a host with an engine from before the op `subresource`, and for local
files: an image may come from the page's own origin only: a file page reads local files, an
HTTP page its own scheme, host and port. With the op, the engine decides (Net.Subresource):
a page's images, style sheets and fonts may be of any origin, each request and redirect is
checked there, and this function is asked only about `file:` URLs. */
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
/** An engine that decides subresource transfers (WebDocument op `subresource`). */
export type SubresourceEngine={subresource?:(request:Record<string,unknown>)=>unknown};
const noSubresourceOp=new WeakSet<object>();
/** The bytes of one subresource of a page (kind "image", "style", "font"), with its final URL.
A `file:` URL is read here, for a `file:` page only. Every other URL is the engine's to decide
(Net.Subresource, through page-load.mjs `loadSubresource`): this host makes the requests it
is told to (native_net.ts: redirect "manual", the address the engine chose). An engine from
before the op gets the rule of before: the page's own origin, by a plain fetch. */
export async function readSubresource(engine:SubresourceEngine|undefined,kind:"image"|"style"|"font",url:string,documentURL:string,
  limit:number,signal?:AbortSignal,before?:()=>Promise<{url:string;bytes:Uint8Array;contentType:string}>):Promise<{url:string;bytes:Uint8Array;contentType:string}> {
  const local=new URL(url).protocol==="file:";
  if(!local&&engine&&typeof engine.subresource==="function"&&!noSubresourceOp.has(engine)) {
    const step=async(request:Record<string,unknown>)=>{
      try{return await engine.subresource!(request);}
      catch(error){
        if(/unknown document operation/.test(String(error))){noSubresourceOp.add(engine);return undefined;}
        throw error;
      }
    };
    // Is the op there? One call that sends nothing: an unknown kind is answered with `fail`.
    if(await step({page:documentURL,kind:"",url})!==undefined) {
      const got=await loadSubresource(step,(wire:NetWire)=>netAnswer(wire,{timeoutMs:10000}),{url:documentURL},kind,url,signal) as
        {url:string;contentType:string;base64:string};
      const text=atob(got.base64);
      if(text.length>limit)throw new Error(`${kind} too large`);
      const bytes=new Uint8Array(text.length);
      for(let i=0;i<text.length;i++)bytes[i]=text.charCodeAt(i);
      return {url:got.url,bytes,contentType:got.contentType};
    }
  }
  // A local file, or an engine from before the op: `before` (a style sheet: as it was read
  // then), else the page's own origin only.
  if(before)return await before();
  if(!imageAllowed(url,documentURL))throw new Error("not of the page's origin");
  return {url,bytes:await readBytes(url,limit,signal),contentType:""};
}
/** Limits on web font bytes (CSS Fonts 4 @font-face): each face, and all faces of a page. */
export const MAX_FONT_BYTES=8*1048576, MAX_PAGE_FONT_BYTES=16*1048576;
type WebFontEngine={
  fontFaces?:(source:string,options:Record<string,unknown>)=>{faces?:{family:string;sources:string[]}[]}|Promise<{faces?:{family:string;sources:string[]}[]}>;
  webFontLoad?:(bytes:Uint8Array,sha256:string)=>unknown;
};
/** Web fonts (CSS Fonts 4 §4): Lean says which @font-face faces the page's rendered text
uses (WebDocument.fontFaces), each with its URLs in order. The host fetches the first URL of
each face that it can, from the page's own origin and within the size caps, and gives the bytes
to Lean (webFontLoad), which checks the font with the font policy and holds it. A face that
fails or is refused is left out: its text falls back to the next family, as CSS says. A page
whose sheets have no @font-face makes no call. The answer is the request field `webFonts`. */
export async function loadWebFonts(engine:WebFontEngine,url:string,source:string,resources:HTMLResource[],signal?:AbortSignal) {
  const webFonts:{url:string;sha256:string}[]=[];
  if(typeof engine.fontFaces!=="function"||typeof engine.webFontLoad!=="function")return webFonts;
  const hasRule=(text:string)=>/@font-face/i.test(text);
  if(!hasRule(source)&&!resources.some(r=>hasRule(r.source)))return webFonts;
  // An engine from before @font-face answers "unknown document operation": no web fonts.
  let answer;
  try{answer=await engine.fontFaces(source,{url,resources});}catch{return webFonts;}
  const loaded=new Map<string,string>();let total=0;
  for(const face of answer?.faces??[]) {
    for(const src of face.sources) {
      signal?.throwIfAborted();
      const known=loaded.get(src);
      if(known!==undefined){if(known)break;continue;}
      try {
        const {bytes}=await readSubresource(engine as SubresourceEngine,"font",src,url,MAX_FONT_BYTES,signal);
        if(total+bytes.length>MAX_PAGE_FONT_BYTES)throw new Error("the page's fonts exceed 16 MiB");
        const sha256=await sha256Hex(bytes);
        await engine.webFontLoad(bytes,sha256);
        total+=bytes.length;loaded.set(src,sha256);webFonts.push({url:src,sha256});
        break;
      } catch(error) {
        if(signal?.aborted)throw error;
        loaded.set(src,"");
        console.error(`Native HTML web font refused: ${src}: ${String(error instanceof Error?error.message:error)}`);
      }
    }
  }
  return webFonts;
}
/** Fetch the images Lean listed, as `{key,bytes}`, six at a time, kept in the order listed.
`failed` hears of each image that was not read. `engine`: the engine that decides each
transfer (readSubresource); with none, the page's own origin only. */
export async function fetchImageBytes(wanted:{key:string;url:string}[],documentURL:string,signal?:AbortSignal,
  failed?:(url:string,reason:string)=>void,engine?:SubresourceEngine) {
  const read:({bytes:Uint8Array}|{reason:string})[]=new Array(wanted.length);
  let next=0;
  const worker=async()=>{
    for(;;){
      const index=next++;if(index>=wanted.length)return;
      signal?.throwIfAborted();
      try{read[index]={bytes:(await readSubresource(engine,"image",wanted[index].url,documentURL,MAX_IMAGE_BYTES,signal)).bytes};}
      catch(error){
        if(signal?.aborted)throw error;
        read[index]={reason:String(error instanceof Error?error.message:error)};
      }
    }
  };
  await Promise.all(Array.from({length:Math.min(6,wanted.length)},worker));
  const images:{key:string;bytes:Uint8Array}[]=[];let total=0;
  for(const [index,{key,url}] of wanted.entries()) {
    const got=read[index];
    if("reason" in got){failed?.(url,got.reason);continue;}
    if(total+got.bytes.length>MAX_PAGE_IMAGE_BYTES){failed?.(url,"past the limit on the image bytes of a page");continue;}
    total+=got.bytes.length;
    images.push({key,bytes:got.bytes});
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
export async function fetchImages(wanted:{key:string;url:string}[],documentURL:string,signal?:AbortSignal,engine?:SubresourceEngine) {
  return (await fetchImageBytes(wanted,documentURL,signal,undefined,engine)).map(({key,bytes})=>({key,base64:base64(bytes)}));
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
  // The reader sees the reason, not which part of the browser gave it.
  message=message.replace(/^(Error: )?Lean HTML: /,"");
  return `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Page refused</title></head><body><h1>This page can not be shown</h1><p>${text(url)}</p><p>${text(message)}</p></body></html>`;
}
/** Page scripts (WebScripts.lean): the engine that holds the script session. A host sets
one when its engine answers `scriptSession` info (with BubblePopJS, or the QuickJS
guest module loaded); with none, a page with scripts is refused, as before. `start`
answers no turn when the setting says the scripts do not run (`scriptPlan`), and throws
when they are refused. */
/** `mode`: request fields of the page's renders that its scripts' layout reads need too (the
mode, the stylesheets, and the web fonts that document.fonts reads). */
export type ScriptHost={start(source:string,url:string,resources:{nodeId:number;source:string}[],encoding?:string,mode?:Record<string,unknown>):Promise<ScriptTurn|undefined>|ScriptTurn|undefined};
let scriptHost:ScriptHost|undefined;
export function setScriptHost(host:ScriptHost|undefined){scriptHost=host;}
// Fallback fonts (native_html_fonts.ts): given the page source, puts the fonts it needs into
// the engine that lays it out. Started when the source is known; awaited before the page's
// scripts start and before it is returned to be laid out.
let fontHost:((source:string)=>Promise<unknown>)|undefined;
export function setFontHost(host:typeof fontHost){fontHost=host;}
/** The engine, or the same calls in a worker, which answer promises. prepareHTML awaits every call. */
export type PageEngine=((Pick<HTMLEngine,"xmlStylesheet"|"xslt"|"inspect"|"compile"|"selectedText"|"findInPage">&ImageHolder)|ImageHolder&{
  xmlStylesheet(...a:Parameters<HTMLEngine["xmlStylesheet"]>):Promise<ReturnType<HTMLEngine["xmlStylesheet"]>>;
  xslt(...a:Parameters<HTMLEngine["xslt"]>):Promise<ReturnType<HTMLEngine["xslt"]>>;
  inspect(...a:Parameters<HTMLEngine["inspect"]>):Promise<ReturnType<HTMLEngine["inspect"]>>;
  compile(...a:Parameters<HTMLEngine["compile"]>):Promise<ReturnType<HTMLEngine["compile"]>>;
  selectedText(...a:Parameters<HTMLEngine["selectedText"]>):Promise<ReturnType<HTMLEngine["selectedText"]>>;
  findInPage(...a:Parameters<HTMLEngine["findInPage"]>):Promise<ReturnType<HTMLEngine["findInPage"]>>;
})&{decodeDocument?:PageDecoder};
/** How a page is accepted. `liberal`: liberal mode (WebAccept.lean, --be-liberal-in-what-we-accept
and the Settings checkbox): Lean skips what it may skip and says so, and this host passes on
the fetches that failed instead of refusing the page. */
export type AcceptOptions={liberal?:boolean};
export async function prepareHTML(engine:PageEngine,url:string,signal?:AbortSignal,inline?:string,accept:AcceptOptions={}) {
  const decode:PageDecoder|undefined=typeof engine.decodeDocument==="function"?(b,c)=>engine.decodeDocument!(b,c,pageDecoding.fallback,pageDecoding.locale):undefined;
  const document:{url:string;source:string;bytes:number;encoding?:string;raw?:Uint8Array}=inline===undefined?await readSource(url,signal,decode):{url,source:inline,bytes:inline.length},resources:HTMLResource[]=[];
  // The page's console (native_console.ts): System entries now, script lines later.
  const page={};
  const fetchFailed=(feature:string,where:string,message:string,action:string)=>
    addEntries(page,[{source:"System",severity:"error",feature,where,message,action}]);
  // Liberal mode is a field of every request; scripting:false tells Lean that no page script runs here.
  const mode:Record<string,unknown>=accept.liberal?{liberal:true,...(scriptHost?{}:{scripting:false})}:{};
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
  const fonts=fontHost?.(document.source).catch(error=>console.error("Native HTML: fallback fonts:",String(error)));
  const inspection=await engine.inspect(document.source,{url:document.url,...mode});
  noteDiagnostics(page,inspection,false);
  const scripted=inspection.scripts.some(script=>script.kind!=="data");
  if(scripted&&!scriptHost)
    throw new Error("Page scripts need the QuickJS guest module (--quickjs-wasm FILE) and an engine with scriptSession; this page is refused");
  if(inspection.stylesheets.length>MAX_RESOURCES&&!accept.liberal)throw new Error(`Native HTML exceeds ${MAX_RESOURCES} external stylesheets`);
  // In liberal mode a stylesheet that is not read goes to Lean as a failure, with the reason;
  // Lean draws the page without it and says so (WebAccept.Skip.stylesheetMissing).
  const resourceFailures:{nodeId:number;url:string;reason:string}[]=[];
  let resourceBytes=0;
  for(const [index,descriptor] of inspection.stylesheets.entries()) {
    signal?.throwIfAborted();
    try{
      if(index>=MAX_RESOURCES)throw new Error(`Native HTML exceeds ${MAX_RESOURCES} external stylesheets`);
      // The URL and owning node are selected and resolved by Lean.
      navigationURL(descriptor.url,inspection.baseURL,document.url);
      // The engine decides the transfer of a sheet of any origin (readSubresource: each request
      // and redirect, and that a sheet of another origin is text/css).
      const sheet=await readSubresource(engine as SubresourceEngine,"style",descriptor.url,document.url,MAX_SOURCE_BYTES,signal,
        async()=>{const read=await readSource(descriptor.url,signal);return {url:read.url,bytes:read.raw,contentType:read.contentType};});
      const resource={url:sheet.url,source:new TextDecoder("utf-8").decode(sheet.bytes),bytes:sheet.bytes.length};
      sourceBound(resource.source);
      if(resourceBytes+resource.bytes>MAX_RESOURCE_BYTES)throw new Error("Native HTML stylesheets exceed 32 MiB");
      resourceBytes+=resource.bytes;
      resources.push({nodeId:descriptor.nodeId,url:resource.url,source:resource.source});
    }catch(error){
      if(!accept.liberal||signal?.aborted)throw error;
      resourceFailures.push({nodeId:descriptor.nodeId,url:descriptor.url,reason:String(error instanceof Error?error.message:error)});
    }
  }
  // Lean lists the images it wants and decides each transfer (any origin: Net.Subresource);
  // the host makes the requests, with size caps. One that fails or is refused is left out, and the page shows its alt text.
  // An engine that holds images gets each one once, and renders name them.
  const images=await imageOptions(engine,await fetchImageBytes(inspection.images??[],document.url,signal,
    (imageURL,reason)=>fetchFailed("image",imageURL,`image not read: ${reason}`,"alt text shown"),engine as SubresourceEngine));
  // The tab icon that Lean chose (WebDocument.iconURL), by the rules of images. One that fails or is refused leaves the tab with no icon.
  let iconBase64:string|undefined;
  if(inspection.icon)try{
    iconBase64=base64((await readSubresource(engine as SubresourceEngine,"image",inspection.icon,document.url,MAX_ICON_BYTES,signal)).bytes);
  }catch(error){if(signal?.aborted)throw error;console.error(`Native HTML icon refused: ${inspection.icon}: ${String(error instanceof Error?error.message:error)}`);
    fetchFailed("tab icon",inspection.icon,`icon not read: ${String(error instanceof Error?error.message:error)}`,"tab shown with no icon");}
  const webFonts=await loadWebFonts(engine as WebFontEngine,document.url,document.source,resources,signal);
  // `diagnostics:true` asks Lean for the skips in the answer: the first frame only (noteDiagnostics).
  const options:Record<string,unknown>={url:document.url,resources,...images,...mode,...(webFonts.length?{webFonts}:{}),...(resourceFailures.length?{resourceFailures}:{}),
    ...(accept.liberal?{diagnostics:true}:{})};
  // Page scripts: Lean runs them (WebScripts). The host only fetches the bytes of `src`
  // scripts, as for stylesheets. The script session's commands are part of each render
  // request, so a render replays them over the parsed page.
  let script:{session:number;turn:ScriptTurn}|undefined;
  await fonts;
  if(scripted&&scriptHost) {
    const supplied:{nodeId:number;source:string}[]=[];
    for(const descriptor of inspection.scripts) {
      if(descriptor.kind!=="classic"||!descriptor.src)continue;
      signal?.throwIfAborted();
      try{
        navigationURL(descriptor.url,inspection.baseURL,document.url);
        const resource=await readSource(descriptor.url,signal);
        sources.push({kind:"Script",url:resource.url,source:resource.source});
        supplied.push({nodeId:descriptor.nodeId,source:resource.source});
      }catch(error){
        // Liberal mode: a script that is not fetched does not run, as in a browser after a failed fetch.
        if(!accept.liberal||signal?.aborted)throw error;
        fetchFailed("script",descriptor.url,`script not read: ${String(error instanceof Error?error.message:error)}`,"script not run");
      }
    }
    // Liberal mode: when the script engine refuses to start (the setting names an engine this
    // host does not have), the page is drawn with its scripts not run, as Lean's scriptsOff skip.
    const turn=await Promise.resolve(scriptHost.start(document.source,document.url,supplied,document.encoding,
      // The layout fields of the render request above (WebDocument.layoutFields): the layout
      // the page's scripts read is then the one the page is drawn with (its images' sizes, a
      // sheet that failed), and the engine keeps one layout for both, not two.
      {...mode,...(resources.length?{resources}:{}),...(webFonts.length?{webFonts}:{}),...images,
        ...(resourceFailures.length?{resourceFailures}:{})})).catch(error=>{
      if(!accept.liberal||signal?.aborted)throw error;
      addEntries(page,[{source:"System",severity:"warning",feature:"page scripts",where:document.url,
        message:String(error instanceof Error?error.message:error),action:"scripts not run"}]);
      return undefined;
    });
    if(turn){
      noteTurn(page,turn);
      script={session:turn.session,turn};
      if(turn.commands?.length)options.commands=turn.commands;
    }
  }
  // Pages show in the font of loadFontFile, or else in the Lean bitmap face.
  signal?.throwIfAborted();
  return Object.assign(page,{
    url:document.url,baseURL:inspection.baseURL,title:inspection.title,source:document.source,sources,script,iconBase64,
    /** The page's bytes as fetched (File > Save Page As); a page made here, its source as UTF-8. */
    sourceBytes:()=>document.raw??new TextEncoder().encode(sources[0].source),
    /** Whether the page has classic scripts (they run, or the setting says why not). */
    scripted,
    /** The mode the page was prepared in: a change of the setting loads it again. */
    liberal:!!accept.liberal,
    /** A render answered with the skips: later renders do not ask for them. */
    diagnosticsSeen:()=>{delete options.diagnostics;},
    /** A later turn of the page's script session: its commands, when the DOM changed. */
    applyTurn:(turn:ScriptTurn)=>{noteTurn(page,turn);if(script)script.turn=turn;if(turn.changed&&turn.commands)options.commands=turn.commands;return turn.changed;},
    // What compile needs, as plain data, so the engine in a worker can run it.
    request:(_width:number,_height:number,view:PageView={})=>({source:document.source,options:{...options,...view} as Record<string,unknown>}),
    compile:(width:number,height:number,view:PageView={})=>{
      const frame=engine.compile(document.source,width,height,{...options,...view});
      Promise.resolve(frame).then(answer=>noteDiagnostics(page,answer),()=>{});
      return frame;
    },
    selectedText:(width:number,height:number,view:PageView={})=>engine.selectedText(document.source,width,height,{...options,...view}),
    findInPage:(width:number,height:number,view:PageView={})=>engine.findInPage(document.source,width,height,{...options,...view}),
  });
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
