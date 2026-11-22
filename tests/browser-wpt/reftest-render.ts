// reftest-render.ts: draw WPT reftest pages (tests and references) with the native engine and
// write each picture as a PNG, for wpt-reftests.py to compare (skills/wpt-runs, section 10).
//
//   deno run -A --unstable-ffi tests/browser-wpt/reftest-render.ts --native-engine LIB \
//     --list JOBS.jsonl --out DIR [--font FILE] [--bitmap-font]
//
// JOBS.jsonl: one job a line, {"url":"http://127.0.0.1:PORT/svg/x.svg","width":800,"height":600,"file":"name.png"}.
// Each page is loaded the way the window and Textnaut load one (native_html_document.ts
// prepareHTML: its style sheets, imported sheets, images and web fonts fetched as the engine
// lists them), its scripts run on BubblePopJS (a script session as run_html.ts starts it, time
// moved 16 ms a step), and drawn once by the engine's CPU raster (op render with cpu:true,
// SVGRaster) at the job's size, CSS pixels = device pixels. The default face is Noto Sans
// (third_party/fonts) with the Hub's fallback fonts, and serif and monospace text draw with
// Liberation Serif and Liberation Mono (serif_font.ts), as in the window; --bitmap-font draws
// with the engine's bitmap face instead (a diagnostic, never a score).
//
// When the page is drawn: WPT's rule (wptrunner reftest-wait.js): after the load, and while the
// root element's class has `reftest-wait`, when a script removes it. Here: after the first
// script turn and two 16 ms frames; with `reftest-wait`, the page's time moves on in 16 ms
// steps until the class is gone, for at most --wait-ms of page time (default 6000), else the
// job is TIMEOUT.
//
// Output, one line a job on stdout: `__job {"i":N}` before a job starts (so a caller that sees
// the process die knows which job crashed it), then `__done {...}`: status ("ok", "error",
// "timeout"), ms, sha256 of the RGB pixels, waited (ms of page time), message. The engine is
// loaded once; a job that throws does not end the process.
import {loadHTML,nativeBackends,unpackAnswer} from "../../labs/demos/foafnaut/native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML,readSource,setFontHost,setScriptHost,setImagesAfterFirstFrame} from "../../labs/demos/foafnaut/native_html_document.ts";
import {fallbackFontHost,loadFallbackFonts,mayNeedFallbackFonts} from "../../labs/demos/foafnaut/native_html_fonts.ts";
import {MONO_FAMILY,SERIF_FAMILY,monoFontPath,serifFontPath} from "../../labs/demos/foafnaut/serif_font.ts";
import {netAnswer} from "../../labs/demos/foafnaut/native_net.ts";
import {pngOf} from "../../labs/demos/foafnaut/png_write.ts";
// @ts-ignore plain JavaScript module of the Hub
import {fetchedAnswer} from "../../docs/web/hub/foafnaut/page-load.mjs";

const args=Deno.args,opt=(n:string,d="")=>{const i=args.indexOf(n);return i<0?d:args[i+1];};
const library=opt("--native-engine");
if(!library){console.error("--native-engine LIB is required");Deno.exit(2);}
const outDir=opt("--out","reftest-out"),waitMs=Number(opt("--wait-ms","6000"));
const here=new URL(".",import.meta.url).pathname;
const fontFile=opt("--font",decodeURIComponent(new URL("../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname));
const bitmap=args.includes("--bitmap-font");
// --scenes DIR: also write each page's scene (the storage floats, tile words and WGSL the GPU
// path draws) and its CPU pixels, for reftest-gpu-check.mjs to draw on WebGPU and compare.
const scenesDir=opt("--scenes");
if(scenesDir)await Deno.mkdir(scenesDir,{recursive:true});
await Deno.mkdir(outDir,{recursive:true});

type Turn=import("../../labs/demos/foafnaut/native_html_engine.ts").ScriptTurn&{netSync?:unknown;netRequests?:unknown[];fetches?:{id:number;url:string}[];logs:string[];errors:string[]};
const engine=await loadHTML(library);
const bytesBackend=nativeBackends(library).bytes;
if(!bitmap){
  const answer=await loadFontFile(engine,fontFile,"Noto Sans","bytes");
  if(typeof (answer as {fonts?:unknown})?.fonts==="number"){
    const fallbacks=fallbackFontHost(fonts=>loadFallbackFonts(engine,fonts));
    setFontHost(async(source:string)=>{if(mayNeedFallbackFonts(source))await fallbacks.page(source);});
  }
}
// Images go with the first frame: there is one frame.
setImagesAfterFirstFrame(false);
/** The generic faces given to the engine so far (each once a run). */
const faces={serif:false,mono:false};
let size={width:800,height:600};
const call=(source:string,request:Record<string,unknown>)=>engine.scriptSession(source,request) as unknown as Turn;
const synced=async(turn:Turn):Promise<Turn>=>{
  for(let i=0;turn.netSync&&i<4096;i++)turn=call("",{action:"syncAnswer",session:turn.session,answer:await netAnswer(turn.netSync as never)});
  return turn;
};
setScriptHost({start:async(source,pageURL,resources,encoding,mode={})=>synced(call(source,{action:"start",url:pageURL,resources,
  width:size.width,height:size.height,zoomUnit:100,layout:{url:pageURL,textScalePercent:100,zoomUnit:100,...mode},engine:"bubblepop",
  ...(encoding?{encoding}:{}),network:true}))});

/** Whether the root element's class names reftest-wait, in the tree the scripts made. */
function waiting(source:string,url:string,options:Record<string,unknown>):boolean {
  const facts=engine.inspect(source,{url,liberal:true,...(options.commands?{commands:options.commands}:{})}) as unknown as
    {nodes?:{id:number;tagName:string;attributes?:Record<string,string>;parent:number|null}[]};
  const nodes=facts.nodes??[];
  const ids=new Set(nodes.map(n=>n.id));
  const root=nodes.find(n=>n.parent===null||!ids.has(n.parent));
  return !!root&&/(^|\s)reftest-wait(\s|$)/.test(root.attributes?.class??"");
}

/** wptrunner fires `TestRendered` at the root element once the page is drawn while it has
`reftest-wait` (reftest-wait_webdriver.js). A page that listens for it gets a script that does
the same: after the load event and two frames, if the root still has the class. The script
removes its own element first, so the tree the page is drawn from is the page's. Only pages
that name the event get it. */
const testRendered=`(function(){var s=document.currentScript;if(s&&s.parentNode)s.parentNode.removeChild(s);`+
  `function go(){requestAnimationFrame(function(){requestAnimationFrame(function(){var r=document.documentElement;`+
  `if(r&&r.classList.contains("reftest-wait"))r.dispatchEvent(new Event("TestRendered"));});});}`+
  `if(document.readyState==="complete")go();else addEventListener("load",go);})();`;
function withTestRendered(source:string):string {
  if(!source.includes("TestRendered"))return source;
  const xml=/^\s*(<\?xml[^>]*\?>\s*)?(<!--[\s\S]*?-->\s*)*<svg[\s>]/.test(source);
  if(xml){
    const at=source.lastIndexOf("</");
    return at<0?source:source.slice(0,at)+`<script xmlns="http://www.w3.org/2000/svg"><![CDATA[${testRendered}]]></script>`+source.slice(at);
  }
  return source+`<script>${testRendered}</script>`;
}

async function draw(job:{url:string;width:number;height:number;file:string}) {
  size={width:job.width,height:job.height};
  // The page's own bytes, decoded by the engine, with the TestRendered script when it listens for it.
  const read=await readSource(inputURL(job.url),undefined,(b,c)=>(engine as {decodeDocument?:(b:Uint8Array,c:string)=>{encoding:string;source:string}|undefined}).decodeDocument?.(b,c));
  const source0=withTestRendered(read.source);
  const page=await prepareHTML(engine,read.url,undefined,source0===read.source?undefined:source0,{liberal:true});
  let waited=0,timedOut=false;
  const script=page.script;
  const scriptErrors:string[]=[];
  if(script){
    const take=async(next:Turn)=>{
      // the turn's errors, and the console lines of uncaught exceptions
      for(const e of [...(next.errors??[]),...(next.logs??[]).filter(l=>/^Uncaught /.test(String(l)))])if(scriptErrors.length<4)scriptErrors.push(String(e).slice(0,200));
      if(Deno.env.get("REFTEST_DEBUG"))console.error(JSON.stringify({logs:next.logs,errors:next.errors,changed:(next as {changed?:boolean}).changed,clock:(next as {clock?:number}).clock}).slice(0,600));
      page.applyTurn(next as never);
      for(const wire of next.netRequests??[])await take(await synced(call("",{action:"net",session:next.session,results:[await netAnswer(wire as never)]})));
      if(next.fetches?.length){
        const results=await Promise.all(next.fetches.map(f=>fetchedAnswer(f,async(target:string)=>{
          const r=await readSource(target);
          return {status:200,url:r.url,contentType:r.contentType,contentTypeOptions:r.contentTypeOptions,source:r.source};})));
        await take(await synced(call("",{action:"fetched",session:next.session,results})));
      }
    };
    await take(script.turn as unknown as Turn);
    const advance=async()=>{await take(await synced(call("",{action:"advance",session:script.session,ms:16})));waited+=16;
      const layout=page.takeLayoutChange();if(layout)await take(await synced(call("",{action:"advance",session:script.session,ms:0,layout})));};
    for(let i=0;i<2;i++)await advance();
    const req=()=>page.request(job.width,job.height);
    if(waiting(req().source,page.url,req().options)){
      while(waited<waitMs){
        await advance();
        if(!waiting(req().source,page.url,req().options))break;
      }
      // two frames after the class went, as wptrunner waits for paint
      if(waited<waitMs){await advance();await advance();}
      else timedOut=true;
    }
  }
  const {source,options}=page.request(job.width,job.height,{textScalePercent:100,zoomUnit:100});
  const request=JSON.stringify({...options,op:"render",checks:false,cpu:true});
  let buffer=bytesBackend(source,request,job.width,job.height);
  // The serif and monospace faces, as the window holds them (serif_font.ts): given the first time
  // a render says its text wants one, then the page is drawn again. Only an engine that holds
  // such a face says so, so an older engine never gets a font load mode it does not know.
  if(!bitmap){
    const wants=unpackAnswer(buffer).head as {wantsSerif?:unknown;wantsMono?:unknown};
    let again=false;
    if(wants.wantsSerif===true&&!faces.serif){faces.serif=true;again=true;await loadFontFile(engine,serifFontPath(),SERIF_FAMILY,"bytes","serif");}
    if(wants.wantsMono===true&&!faces.mono){faces.mono=true;again=true;await loadFontFile(engine,monoFontPath(),MONO_FAMILY,"bytes","mono");}
    if(again)buffer=bytesBackend(source,request,job.width,job.height);
  }
  if(script)try{engine.scriptSession("",{action:"close"});}catch{/* closed */}
  const {head,sections}=unpackAnswer(buffer);
  if((head as {error?:string}).error)throw new Error(String((head as {error?:string}).error));
  const scene=(head.page??head) as Record<string,unknown>;
  const k=scene.pixelsSection;
  if(typeof k!=="number")throw new Error("render answer has no CPU pixels (engine without cpu:true)");
  const [offset,length]=sections[k];
  if(length!==job.width*job.height*4)throw new Error(`CPU pixels ${length} bytes for ${job.width}x${job.height}`);
  const rgba=new Uint8Array(buffer,offset,length);
  if(scenesDir){
    const section=(key:string)=>{const i=scene[key];if(typeof i!=="number")return undefined;const [o,l]=sections[i];return new Uint8Array(buffer,o,l);};
    const data=section("dataSection"),tiles=section("tilesSection");
    if(data&&tiles&&typeof scene.wgsl==="string"){
      await Deno.writeFile(`${scenesDir}/${job.file}.data`,data);
      await Deno.writeFile(`${scenesDir}/${job.file}.tiles`,tiles);
      await Deno.writeFile(`${scenesDir}/${job.file}.cpu`,rgba);
      await Deno.writeTextFile(`${scenesDir}/${job.file}.json`,JSON.stringify({url:job.url,width:job.width,height:job.height,wgsl:scene.wgsl}));
    }
  }
  // A page is drawn on an opaque canvas: what is left transparent is white, as in a browser's screenshot.
  const rgb=new Uint8Array(job.width*job.height*3),out=new Uint8Array(length);
  for(let p=0,q=0;p<length;p+=4,q+=3){
    const a=rgba[p+3];
    for(let c=0;c<3;c++){const v=a===255?rgba[p+c]:Math.round((rgba[p+c]*a+255*(255-a))/255);rgb[q+c]=v;out[p+c]=v;}
    out[p+3]=255;
  }
  await Deno.writeFile(`${outDir}/${job.file}`,await pngOf(job.width,job.height,out));
  const sha=Array.from(new Uint8Array(await crypto.subtle.digest("SHA-256",rgb))).map(b=>b.toString(16).padStart(2,"0")).join("");
  // What the engine skipped on the page (liberal mode: WebAccept diagnostics), for finding causes.
  const diags=((scene.diagnostics??head.diagnostics) as {feature?:string;message?:string}[]|undefined)??[];
  const skipped=[...new Set(diags.map(d=>`${d.feature??""}: ${d.message??""}`.slice(0,160)))].slice(0,12);
  return {status:timedOut?"timeout":"ok",sha,waited,scripted:!!script,...(skipped.length?{skipped}:{}),...(scriptErrors.length?{scriptErrors}:{})};
}

const jobs=(await Deno.readTextFile(opt("--list"))).split("\n").filter(Boolean).map(l=>JSON.parse(l));
for(const [i,job] of jobs.entries()){
  console.log(`__job ${JSON.stringify({i,url:job.url})}`);
  const t=performance.now();
  try{
    const r=await draw(job);
    console.log(`__done ${JSON.stringify({i,file:job.file,...r,ms:Math.round(performance.now()-t)})}`);
  }catch(error){
    try{engine.scriptSession("",{action:"close"});}catch{/* none open */}
    console.log(`__done ${JSON.stringify({i,file:job.file,status:"error",ms:Math.round(performance.now()-t),message:String(error instanceof Error?error.message:error).slice(0,500)})}`);
  }
}
void here;
