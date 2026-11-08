// The browser loop for a web page. It matches run_html.ts, the native loop: the
// shell, history and every decision are Lean values and Lean calls.
// It runs in a worker, or on the page's own thread where a worker can not start:
// an iframe sandbox without allow-same-origin has an opaque origin, and the worker
// constructor refuses that (Foafos guests). `post` is the only way out of the loop.
let post=(message,transfer)=>self.postMessage(message,transfer);
// Bookmarks, history and settings in this browser's IndexedDB, in the resource format Lean
// decides for the native browser's local pod (browser-state.mjs, WebState.lean).
import {createBrowserState,indexedDbStore,memoryStore,stateAvailable} from './browser-state.mjs';
// Where a link or an address goes: Lean's route (WebRoute.lean), done as it says; with an
// engine from before the op, the same rules in JavaScript (link-route.mjs, issue 1274).
import {createRouter} from './link-route.mjs';
let browserState,stateReason='starting';
const statePages=['foafnaut:bookmarks','foafnaut:history'];
const inWorker=typeof WorkerGlobalScope!=='undefined'&&self instanceof WorkerGlobalScope;
const pagesBase=new URL('./pages/',import.meta.url).href,siteOrigin=new URL(import.meta.url).origin;
const homeURL=pagesBase+'index.html',settingsURL=pagesBase+'settings.html';
// The site this browser loads pages from: other sites go to the host browser.
const site={origin:siteOrigin,pages:pagesBase,files:false};
const router=createRouter(request=>call('',request));
let module,createSession,renderOffscreen,session,createSurface,hashPixels,surface,surfaceCanvas,checkMode=false,statsMode=false;
// The two-layer view (issue 1268, layers.mjs): undefined until the first render with a canvas
// says whether this engine answers layers:true; false for an engine that answers one frame.
// `current` is the band on screen and the state it was made for; a scroll inside its keep
// range only moves the composite.
let layered,layerSurface,current,shownOffset=0,shiftPending=false,prefetched,motion,bandMs=100,prefetchTimer;
// layers.mjs, imported beside the engine (a static import would hold this script back
// until it and the plan engine it imports had loaded).
let L;const layersModule=import('./layers.mjs');layersModule.catch(()=>{});
// A band is asked for when a scroll needs one. A page's first frame, and a frame after a change
// that is not a scroll, is one Lean frame, which costs about half a band; the band for it is
// made when the page is idle.
let bandWanted=false,bandTimer;
// A band on its way to the screen: Lean has made it and the GPU is drawing it. A scroll that
// comes meanwhile is measured against it, not against the band it replaces.
let incoming;
let firstFrameSeen;const firstFrame=new Promise(resolve=>{firstFrameSeen=resolve;});
// Input that arrives before the engine is ready, and moves and scrolls that arrive while a
// frame builds, wait here. Every press, release, key, text and command is applied in the
// order it arrived; only moves and scrolls are merged.
let ready=false,currentStamp,pendingStamp,pendingMove,pendingScroll,flushPort;
const early=[];
let width=800,height=600,scale=1,theme='next',percent=150,pages=1,pinchBase;
// The folding chrome (owner, 2026-11-08). With the classic UI (the default) the chrome is
// always full. Off, a scroll down first folds the chrome, up to the strip with the domain,
// and a scroll up first unfolds it: the rows the chrome gives up or takes back come out of
// the scroll, so the page follows the finger. Lean draws the chrome at every fold
// (WebShell.nodes with `collapse`); the host only keeps the folded rows (`folded`, backing
// pixels) and sends the fold in percent. An engine that does not answer shellInfo keeps
// the classic chrome (issue 1274).
let classicUI=true,folded=0,engineFolds,foldRowsKey='',foldRowsValue=0,chromeRenders=0;
// The address bar's text, cursor, selection and undo step: a Lean value (WebShell.editJson).
const showURL=url=>({address:url,cursor:url.length,anchor:url.length,undo:null,redo:null,typing:false});
let field=showURL(''),focused=false,loading=false,scroll=0,active=0;
let doc,history,frame,home,checked,dirty=false,drawing=false,serial=0,ticking=false;
const tabs=[];
// Loading (issue 1268): the engine's own WebAssembly module, its fonts and the first pages are
// fetched as soon as this script runs, side by side, and the module compiles while it downloads.
// Before, each waited for the one before it: on a slow phone network the engine started about
// four seconds later, and the fonts and pages came one after another after it.
const runtimeBase=new URL('../html-webgpu/runtime/',import.meta.url);
const phases={workerStart:performance.timeOrigin+performance.now()};
const phase=name=>{phases[name]??=performance.timeOrigin+performance.now();};
let phasesPosted=false;
const preloaded=new Map();
function fetchEarly(url,kind){
  if(!preloaded.has(url)){const p=fetch(url).then(r=>{if(!r.ok)throw Error(`HTTP ${r.status}`);return kind==='text'?r.text().then(text=>({url:r.url||url,source:text})):r.arrayBuffer();});p.catch(()=>{});preloaded.set(url,p);}
  return preloaded.get(url);
}
// The engine's module (web-render.wasm): streaming compile, else a compile of the bytes.
const engineCompiled=(async()=>{
  const url=new URL('web-render.wasm',runtimeBase);
  try{if(typeof WebAssembly.compileStreaming==='function')return await WebAssembly.compileStreaming(fetch(url,{credentials:'same-origin'}));}
  catch(error){console.warn('foafnaut: streaming compile failed, compiling the bytes:',String(error));}
  const response=await fetch(url,{credentials:'same-origin'});
  if(!response.ok)throw Error(`HTTP ${response.status}`);
  return WebAssembly.compile(await response.arrayBuffer());
})().then(compiled=>{phase('engineCompiled');return compiled;});
engineCompiled.catch(()=>{});
const runtimeModules=[import('../html-webgpu/runtime/web-render.mjs'),import('../html-webgpu/runtime/gpu-transport.mjs')];
for(const p of runtimeModules)p.catch(()=>{});
// The plan engine's module goes into the HTTP cache now; its own loader reads it at the first draw.
fetch(new URL('render-plan.wasm',runtimeBase),{credentials:'same-origin'}).then(r=>r.arrayBuffer()).catch(()=>{});
const notoSans='./fonts/noto-sans/NotoSans-Regular.ttf';
fetchEarly(new URL(notoSans,import.meta.url).href,'bytes');
// Fonts after Noto Sans, for the characters it lacks (fallback-fonts.mjs, made by
// labs/demos/foafnaut/fallback_fonts.py): scripts, maths, and CJK in slices. Each is fetched
// only for a page with a character that it adds, so a page of Latin text fetches none, and a
// line of Japanese fetches the kana and common Han slices (about 1.1 MB), not all of CJK.
// Lean picks the font for each character.
const fontCoverage=import('./font-coverage.mjs');
fontCoverage.catch(()=>{});
const coverageFiles=new Map();
function coverage(path){
  const url=new URL(path,import.meta.url).href;
  if(!coverageFiles.has(url)){const p=fetch(url).then(r=>{if(!r.ok)throw Error(`HTTP ${r.status}`);return r.json();});p.catch(()=>{});coverageFiles.set(url,p);}
  return coverageFiles.get(url);
}
// The fallback fonts that a page needs and the engine does not hold yet. Their files start
// to come at once.
const heldFallbacks=new Set();
// How long a page waits for its fallback fonts before it is laid out without the late ones.
const fallbackWait=600;
async function fontsWanted(source){
  const wanted=await (await fontCoverage).fontsFor(source,coverage,heldFallbacks);
  for(const font of wanted)fontFile(font.path).catch(()=>{});
  return wanted;
}
fetchEarly(pagesBase+'index.html','text');
const pageURL=page=>page&&/^[a-z0-9-]+\.(html|xml)$/.test(page)?pagesBase+page:undefined;
// Lean calls made, for ?stats=1 and the tests: a scroll inside a band makes none.
let leanCalls=0,leanRenders=0;
function call(source,options,w=1,h=1,counted=true){
  if(counted)leanCalls++;
  const pointer=module.ccall('web_document_call','number',['string','string','number','number'],[source,JSON.stringify(options),w,h]);
  if(!pointer)throw Error('Lean engine allocation failed');
  try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
const shell=()=>({tabs:tabs.map((tab,i)=>({title:(i===active?doc:tab.doc)?.title??''})),active,...field,focused,
  canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll,
  ...(folding()?{collapsible:true,collapse:foldPercent()}:{}),...(swipeHint?{swipe:swipeHint}:{})});
/** This engine draws a folding chrome: it answers shellInfo with the op chromeLayer. */
function canFold(){
  if(engineFolds===undefined){
    try{const answer=call('',{op:'shellInfo',shell:{scale},width});engineFolds=answer.collapse===true&&(answer.ops??[]).includes('chromeLayer');}
    catch{engineFolds=false;}
  }
  return engineFolds;
}
const folding=()=>!classicUI&&canFold();
/** The rows the chrome gives up when it folds all the way, from Lean (shellInfo). */
function foldRows(){
  const key=`${width}|${scale}`;
  if(key!==foldRowsKey){
    try{const answer=call('',{op:'shellInfo',shell:{scale},width});foldRowsValue=Math.max(0,answer.full-answer.strip);}catch{foldRowsValue=0;}
    foldRowsKey=key;
  }
  return foldRowsValue;
}
const foldPercent=()=>{const rows=foldRows();return rows?Math.max(0,Math.min(100,Math.round(100*folded/rows))):0;};
/** Unfold the chrome (a new page, the address bar, a tap on the strip). */
function unfold(){
  if(!folded)return;
  folded=0;
  if(canShift()){shiftPending=true;if(!drawing)draw();}else request();
}
const push=(state,url)=>call('',{op:'historyPush',history:state,url});
const refusal=(url,message)=>{
  const text=value=>String(value).replace(/&/g,'&amp;').replace(/</g,'&lt;');
  return {url,title:'Page refused',source:`<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Page refused</title></head><body><h1>This page can not be shown</h1><p>${text(url)}</p><p>${text(message)}</p></body></html>`};
};
// Lean sends the storage floats as the bytes the GPU reads. This only decodes them.
function frameFloats(frame){
  if(typeof frame.dataBase64!=='string')return frame;
  const text=atob(frame.dataBase64),bytes=new Uint8Array(text.length);
  for(let i=0;i<text.length;i++)bytes[i]=text.charCodeAt(i);
  frame.data=new Float32Array(bytes.buffer);delete frame.dataBase64;
  return frame;
}
// A render as bytes (issue 1268): a JSON head and the storage floats and tile words as
// raw sections (WebDocument.packAnswer), with no Base64. A runtime with no such export
// answers JSON text with Base64.
const textDecoder=new TextDecoder();
function render(source,options,w,h,chromeOnly=false,counted=true){
  if(counted){leanCalls++;if(chromeOnly)chromeRenders++;else leanRenders++;}
  if(typeof module._web_document_call_bin!=='function')return frameFloats(call(source,options,w,h,counted));
  const pointer=module.ccall('web_document_call_bin','number',['string','string','number','number','number'],[source,JSON.stringify(options),w,h,0]);
  if(!pointer)throw Error('Lean engine allocation failed');
  let buffer;
  try{const heap=module.HEAPU8;buffer=heap.slice(pointer,pointer+new DataView(heap.buffer,pointer,4).getUint32(0,true)).buffer;}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  const view=new DataView(buffer),headSize=view.getUint32(4,true),count=view.getUint32(8,true);
  let offset=12+4*count;
  const frame=JSON.parse(textDecoder.decode(new Uint8Array(buffer,offset,headSize)));
  if(frame?.error)throw Error(frame.error);
  offset+=headSize;
  const sections=[];
  for(let i=0;i<count;i++){const length=view.getUint32(12+4*i,true);sections.push([offset,length]);offset+=(length+3)&~3;}
  // A render with layers has a scene for the chrome and one for the page band, each with its sections.
  for(const scene of [frame,frame.page,frame.chrome]){
    if(!scene||typeof scene!=='object')continue;
    if(typeof scene.dataSection==='number'){const [o,l]=sections[scene.dataSection];scene.data=new Float32Array(buffer,o,l/4);delete scene.dataSection;}
    if(typeof scene.tilesSection==='number'){const [o,l]=sections[scene.tilesSection];scene.tiles=new Uint32Array(buffer,o,l/4);delete scene.tilesSection;}
  }
  return frame;
}
// A font file into the engine. As bytes it goes into the engine's heap: a font above about
// 3 MB does not fit as a Base64 string, which Wasm copies onto its 4 MB stack. A runtime
// with no such export takes Base64 in the JSON request. fallback adds the font after the
// fonts the engine holds, for the characters they lack; otherwise it replaces them.
//
// The bytes call gained its fallback argument after it was first published, and a Wasm
// engine built with assertions aborts when a call has the wrong number of arguments. The
// page cannot read the count from the export, so it uses bytes only once an answer has shown
// that the engine holds several fonts (fonts in the answer): such an engine takes five.
let fontBytesTakeFallback=false;
function fontLoad(bytes,family,sha,fallback=false){
  if(!fontBytesTakeFallback||typeof module._web_document_font_call_bin!=='function'||typeof module._malloc!=='function'){
    let text='';
    for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
    return call('',{op:'fontLoad',fontBase64:btoa(text),fontFamily:family,fontSha256:sha,...(fallback?{fallback:true}:{})});
  }
  const input=module._malloc(Math.max(1,bytes.length));
  if(!input)throw Error('Lean engine allocation failed');
  try{
    module.HEAPU8.set(bytes,input);
    const pointer=module.ccall('web_document_font_call_bin','number',['number','number','string','string','number'],[input,bytes.length,family,sha,fallback?1:0]);
    if(!pointer)throw Error('Lean engine allocation failed');
    try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
    finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  }finally{module._free(input);}
}
async function fontFile(path){
  const bytes=new Uint8Array(await fetchEarly(new URL(path,import.meta.url).href,'bytes'));
  const sha=[...new Uint8Array(await crypto.subtle.digest('SHA-256',bytes))].map(b=>b.toString(16).padStart(2,'0')).join('');
  return {bytes,sha};
}
// Noto Sans is the default face. Lean reads and shapes it; if it does not load, the
// page stays in the bitmap face. Fallback fonts need an engine that takes fonts as
// bytes: an older one would read a fallback font as a replacement.
async function loadFont(){
  try{
    const {bytes,sha}=await fontFile(notoSans);
    const primary=fontLoad(bytes,'Noto Sans',sha);
    // Only an engine that holds several fonts answers with `fonts` (the count held). An older
    // engine would take a fallback font as a replacement for Noto Sans, or abort on the
    // fallback argument: on 2026-11-07 the published engine did both (issue 1274).
    if(typeof primary?.fonts==='number')fontBytesTakeFallback=true;
  }catch(error){console.warn('foafnaut: bitmap font, because Noto Sans did not load:',String(error));}
}
// The fallback fonts a page needs, into the engine. Those that come within `wait` ms go in
// before the page is laid out; the rest go in together when they have all come, and the
// page is drawn again then. Each font load starts Lean's word memo again, so they go in at once.
// An engine that holds one font would take a fallback font as a replacement (issue 1274).
async function loadFallbackFonts(source,wait){
  if(!fontBytesTakeFallback)return;
  let wanted;
  try{wanted=await fontsWanted(source);}catch(error){console.warn('foafnaut: no fallback font table:',String(error));return;}
  if(!wanted.length)return;
  for(const font of wanted)heldFallbacks.add(font.family);
  const files=wanted.map(font=>fontFile(font.path).then(file=>({...file,font}),error=>({error,font})));
  const settled=[];
  files.forEach((p,i)=>p.then(file=>{settled[i]=file;}));
  const all=Promise.all(files);
  const late=Symbol();
  const early=await Promise.race([all,new Promise(r=>setTimeout(r,wait,late))]);
  const put=list=>{
    for(const file of list){
      if(file.error){console.warn(`foafnaut: no ${file.font.family}:`,String(file.error));heldFallbacks.delete(file.font.family);continue;}
      try{fontLoad(file.bytes,file.font.family,file.sha,true);}catch(error){console.warn(`foafnaut: no ${file.font.family}:`,String(error));}
    }
  };
  if(early!==late){put(early);return;}
  // In order: those that have come now, the rest when all have come.
  const now=settled.filter(Boolean);put(now);
  all.then(list=>{put(list.filter(file=>!now.includes(file)));if(doc){current=undefined;prefetched=undefined;request();}});
}
async function fetchText(url){
  // A page fetched early is used once; a reload fetches it again.
  if(preloaded.has(url)){const page=preloaded.get(url);preloaded.delete(url);try{return await page;}catch{/* fetch it again */}}
  const response=await fetch(url);if(!response.ok)throw Error(`HTTP ${response.status}`);
  return {url:response.url||url,source:await response.text()};
}
// The settings page has the checkbox of the classic UI where it says <!--foafnaut:classic-ui-->,
// in the state of now. Lean draws it as it draws the rest of the page.
const classicMark='<!--foafnaut:classic-ui-->';
function settingsSource(source){
  if(!source.includes(classicMark))return source;
  const box=`<span class="box">${classicUI?'<span class="tick"></span>':''}</span>`;
  const row=canFold()
    ?`<p class="check"><a href="foafnaut:classic/${classicUI?'off':'on'}">${box} Classic browser UI</a></p>`+
      `<p>On: the whole chrome stays at the top. Off: scrolling down folds it away to the site's name at the very top, and scrolling up brings it back.</p>`
    :`<p class="check">${box} Classic browser UI</p><p>The engine this page loaded is older and always shows the whole chrome. The next engine release can fold it as you scroll.</p>`;
  return source.replace(classicMark,row);
}
async function prepare(url){
  const page=await fetchText(url);
  if(url===settingsURL)page.source=settingsSource(page.source);
  const sources=[{kind:'Source',url:page.url,source:page.source}];
  const sheet=call(page.source,{op:'xmlStylesheet',url:page.url});
  if(sheet.url){
    const xsl=await fetchText(sheet.url);
    page.source=call(page.source,{op:'xslt',url:page.url,stylesheet:xsl.source,stylesheetURL:xsl.url}).source;
    sources[0].kind='XML source';
    sources.push({kind:'XSLT source',url:xsl.url,source:xsl.source},{kind:'Generated page',url:page.url,source:page.source});
  }
  await loadFallbackFonts(page.source,fallbackWait);
  const facts=call(page.source,{op:'inspect',url:page.url});
  const images=await pageImages(facts.images);
  const next={url:page.url,title:facts.title,baseURL:facts.baseURL,source:page.source,sources,...images};
  if(facts.scripts?.some(s=>s.kind==='classic')&&await hasScripts())await startScripts(next,facts.scripts);
  return next;
}
// Lean lists the images a page wants (SVG image, HTML img) by key. The page fetches only
// those of this site, with size caps, and gives the bytes back with the key. One that
// fails is left out and shows its alt text. An engine that lists no images gets none,
// so an older engine never sees the field (issue 1274).
// An engine that answers imageInfo holds images (WebDocument, issue 1292): each is sent once,
// as bytes when the engine has web_document_image_call_bin, and renders name it in
// heldImages, so a frame's request does not carry the image. Others get `images`.
const maxImageBytes=4194304,maxPageImageBytes=6291456;
let engineHoldsImages;
function holdsImages(){
  if(engineHoldsImages===undefined){try{engineHoldsImages=(call('',{op:'imageInfo'}).ops??[]).includes('imageLoad');}catch{engineHoldsImages=false;}}
  return engineHoldsImages;
}
function imageLoad(bytes,key,sha){
  if(typeof module._web_document_image_call_bin!=='function'||typeof module._malloc!=='function'){
    let text='';
    for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
    return call('',{op:'imageLoad',key,sha256:sha,imageBase64:btoa(text)});
  }
  const input=module._malloc(Math.max(1,bytes.length));
  if(!input)throw Error('Lean engine allocation failed');
  try{
    module.HEAPU8.set(bytes,input);
    const pointer=module.ccall('web_document_image_call_bin','number',['number','number','string','string'],[input,bytes.length,key,sha]);
    if(!pointer)throw Error('Lean engine allocation failed');
    try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
    finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  }finally{module._free(input);}
}
async function pageImages(wanted){
  const fetched=await pageImageBytes(wanted);
  if(!fetched.length)return {};
  if(holdsImages()){
    const heldImages=[];
    for(const {key,bytes} of fetched){
      const sha=[...new Uint8Array(await crypto.subtle.digest('SHA-256',bytes))].map(b=>b.toString(16).padStart(2,'0')).join('');
      try{imageLoad(bytes,key,sha);heldImages.push({key,sha256:sha});}catch(error){console.warn('foafnaut: image not held:',key,String(error));}
    }
    return {heldImages};
  }
  return {images:fetched.map(({key,bytes})=>{
    let text='';
    for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
    return {key,base64:btoa(text)};
  })};
}
async function pageImageBytes(wanted){
  const images=[];let total=0;
  for(const {key,url} of wanted??[]){
    try{
      const target=new URL(url);if(target.origin!==siteOrigin)continue;
      const response=await fetch(target);if(!response.ok)continue;
      if(Number(response.headers.get('content-length')??0)>maxImageBytes){response.body?.cancel();continue;}
      const bytes=new Uint8Array(await response.arrayBuffer());
      if(bytes.length>maxImageBytes||total+bytes.length>maxPageImageBytes)continue;
      total+=bytes.length;
      images.push({key,bytes});
    }catch{}
  }
  return images;
}
// Page scripts run by Lean (WebScripts.lean): QuickJS-NG compiled to WebAssembly runs in
// WasmVM inside this engine, on the page's Lean DOM, and the Lean event loop decides every
// callback. The host browser's JavaScript never runs a page script. Only when the engine
// answers scriptSession info AND the guest module (docs/web/hub/wasm-guests/, published beside
// the engine runtime by factoidal-builds) loads; otherwise the page shows without its scripts, as before. An
// older engine answers "unknown document operation" (no new export is called, issue 1274).
let engineScripts;
async function hasScripts(){
  if(engineScripts!==undefined)return engineScripts;
  engineScripts=false;
  try{if(!call('',{op:'scriptSession',action:'info'}).ops?.includes('start'))return false;}catch{return false;}
  try{
    const response=await fetch(new URL('../wasm-guests/qjs-wasmvm.wasm',import.meta.url));
    if(!response.ok)return false;
    const bytes=new Uint8Array(await response.arrayBuffer());
    // An engine with scriptSession takes the five arguments of the bytes call.
    fontBytesTakeFallback=true;
    fontLoad(bytes,'guest:quickjs','',false);
    engineScripts=true;
  }catch(error){console.warn('foafnaut: page scripts off:',String(error.message??error));}
  return engineScripts;
}
async function startScripts(page,scripts){
  const resources=[];
  for(const s of scripts)if(s.kind==='classic'&&s.src){
    try{const r=await fetchText(s.url);resources.push({nodeId:s.nodeId,source:r.source});page.sources.push({kind:'Script',url:r.url,source:r.source});}
    catch(error){console.warn('foafnaut: script not fetched:',s.url,String(error.message??error));}
  }
  const turn=call(page.source,{op:'scriptSession',action:'start',url:page.url,resources});
  page.script={session:turn.session,turn,epoch:performance.now()-turn.clock};
  scriptTurn(page,turn);
}
// A turn's logs, and a new frame only when the DOM changed: no DOM change, no layout (the
// commands are part of the render request and so of the layout key).
function scriptTurn(page,turn){
  for(const line of turn.logs)console.log('page:',line);
  for(const line of turn.errors)console.warn('page error:',line);
  if(page.script)page.script.turn=turn;
  if(turn.gpu?.length&&page===doc)gpuTake(turn.gpuPage,turn.gpu);
  if(turn.changed&&turn.commands){page.commands=turn.commands;if(page===doc)request();}
}
// Page GPU commands (docs/designissues/2026-11-08-page-gpu.md): Lean validated each one
// (L4Factoidal.PageGpu) and gives them in the turn; the layer surface replays them and draws
// the page canvases into the page layer. The log is what a new device needs to make the
// page's objects again: every command but passes, and only the last write of each range.
let gpuPage=-1,gpuLog=[],gpuPending=[],gpuFed,gpuBusy=false,gpuAgain=false;
function gpuTake(p,commands){
  if(p!==gpuPage){gpuPage=p;gpuLog=[];gpuPending=[];}
  for(const c of commands){
    if(c.k==='write'){const i=gpuLog.findIndex(x=>x.k==='write'&&x.g[1]===c.g[1]&&x.offset===c.offset&&x.data.length===c.data.length);if(i>=0)gpuLog.splice(i,1);}
    if(c.k!=='pass')gpuLog.push(c);
  }
  gpuPending.push(...commands);
  gpuShow();
}
/** Give the layer surface what it has not had: the whole log for a new surface or page. */
async function gpuFeed(){
  if(!layerSurface||gpuPage<0)return;
  if(gpuFed!==layerSurface||layerSurface.pageGpuStats?.page!==gpuPage){
    gpuFed=layerSurface;const log=gpuLog;gpuPending=[];await layerSurface.replayGpu(gpuPage,log);
  }else if(gpuPending.length){const now=gpuPending;gpuPending=[];await layerSurface.replayGpu(gpuPage,now);}
}
/** A new page canvas frame on screen: replay, blit into the page layer, composite. No Lean call. */
async function gpuShow(){
  if(gpuBusy){gpuAgain=true;return;}
  if(drawing||!layerSurface||!current||current.doc!==doc)return;
  gpuBusy=true;
  try{
    do{
      gpuAgain=false;
      const start=performance.now();
      await gpuFeed();
      if(drawing||!current||current.doc!==doc||!layerSurface.refreshCanvases())continue;
      const {offset}=L.clampOffset(current.answer.layers,scroll);
      const pixels=await layerSurface.composite(width,height,offset);
      shownOffset=offset;
      const done=performance.now(),rgba=surfaceCanvas?undefined:pixels;
      post({type:'frame',width,height,title:doc.title,rgba:rgba?.buffer,presented:!rgba,
        stats:{path:surfaceCanvas?'page-gpu':'page-gpu-readback',layoutMs:0,drawMs:Math.round(done-start),totalMs:Math.round(done-start),
          primitives:0,url:doc.url,address:field.address,scroll,tabs:tabs.length,theme,percent,leanRenders:0,leanCalls,chromeRenders,
          pageGpu:layerSurface.pageGpuStats,bandTop:current.answer.layers.bandTop,offset}},rgba?[rgba.buffer]:[]);
    }while(gpuAgain);
  }catch(error){console.warn('foafnaut: page GPU frame:',String(error.message??error));}
  finally{gpuBusy=false;}
}
// Timers and animation frames: the page's virtual clock follows real time since its scripts started.
setInterval(()=>{
  const script=doc?.script;
  if(!script||script.turn.nextWake===null||script.turn.nextWake===undefined)return;
  const elapsed=performance.now()-script.epoch;
  if(elapsed<script.turn.nextWake)return;
  try{scriptTurn(doc,call('',{op:'scriptSession',action:'advance',session:script.session,ms:Math.max(0,Math.ceil(elapsed-script.turn.clock))}));}
  catch(error){console.warn('foafnaut: page script timers:',String(error.message??error));script.turn.nextWake=null;}
},16);
function scriptClick(x,y){
  const script=doc?.script;if(!script)return;
  try{
    const node=call(doc.source,{op:'nodeAt',url:doc.url,textScalePercent:percent,shell:shell(),...(doc.commands?{commands:doc.commands}:{}),x,y},width,height).node;
    if(typeof node==='number')scriptTurn(doc,call('',{op:'scriptSession',action:'click',session:script.session,node}));
  }catch(error){console.warn('foafnaut: page script click:',String(error.message??error));}
}
// foafnaut:wasm (issue 1244): WebAssembly run by WasmVM, the engine written in Lean, inside this
// Lean engine. The host browser's WebAssembly never runs the module: the page only fetches its
// bytes (same origin, .wasm only) and Lean decodes, checks and runs them. Lean draws the page.
// An engine from before these ops answers wasmInfo with "unknown document operation" (no new
// export is called, issue 1274), and the page then says that it needs a newer engine.
const wasmURL='foafnaut:wasm',maxWasmBytes=1048576;
let engineWasm;
function hasWasm(){
  if(engineWasm===undefined){try{engineWasm=call('',{op:'wasmInfo'}).engine==='WasmVM';}catch{engineWasm=false;}}
  return engineWasm;
}
const wasmNeedsEngine=url=>({url,title:'Needs a newer engine',sources:[],source:'<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Needs a newer engine</title>'+
  '<style>body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:#f4f4ee}h1{margin:0 0 8px 0;font-size:22px;line-height:28px;color:#a0186a}p{margin:0 0 8px 0}</style></head><body>'+
  '<h1>WebAssembly in Lean needs a newer engine</h1><p>This page runs WebAssembly modules with WasmVM, the WebAssembly engine written in Lean, inside the Foafnaut engine.</p>'+
  '<p>The engine this page loaded is older and does not have it. The next engine release carries it.</p></body></html>'});
async function wasmModule(argument){
  const [path,exportName]=argument.split('#');
  const url=new URL(path,pagesBase);
  if(url.origin!==siteOrigin||!url.pathname.endsWith('.wasm'))throw Error('Only .wasm files of this site are run');
  const response=await fetch(url);if(!response.ok)throw Error(`HTTP ${response.status}`);
  const bytes=new Uint8Array(await response.arrayBuffer());
  if(bytes.length>maxWasmBytes)throw Error(`The module has ${bytes.length} bytes; the page takes at most ${maxWasmBytes}`);
  let text='';
  for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
  return {url:url.href,wasmBase64:btoa(text),...(exportName?{export:exportName}:{})};
}
async function wasmPage(url){
  if(!hasWasm())return wasmNeedsEngine(url);
  const argument=url.slice(wasmURL.length+1);
  const answer=call('',{op:'wasmPage',...(argument?await wasmModule(argument):{})});
  return {url,title:answer.title,source:answer.source,sources:[{kind:'Generated page',url,source:answer.source}]};
}
async function statePage(url){
  if(!browserState)throw Error(`Browser state is off: ${stateReason}`);
  const answer=await browserState.page(url.slice(9));
  return {url,title:answer.title,source:answer.source,sources:[{kind:'Generated page',url,source:answer.source}]};
}
// foafnaut:sparql (owner, 2026-11-08): the SPARQL planner drawn as live debug. Lean parses,
// plans and runs the query and writes the page; the address after `foafnaut:sparql/` is
// `q=QUERY&step=N`. An engine from before these ops answers sparqlInfo with "unknown document
// operation" (no new export is called, issue 1274), and the page then says that it needs a
// newer engine.
const sparqlURL='foafnaut:sparql';
let engineSparql;
function hasSparql(){
  if(engineSparql===undefined){try{engineSparql=Array.isArray(call('',{op:'sparqlInfo'}).ops);}catch{engineSparql=false;}}
  return engineSparql;
}
const sparqlNeedsEngine=url=>({url,title:'Needs a newer engine',sources:[],source:'<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Needs a newer engine</title>'+
  '<style>body{margin:16px;font-size:14px;line-height:20px;color:#203040;background:#f4f4ee}h1{margin:0 0 8px 0;font-size:22px;line-height:28px;color:#184078}p{margin:0 0 8px 0}</style></head><body>'+
  '<h1>The SPARQL planner page needs a newer engine</h1><p>This page draws how Factoidal plans and runs a SPARQL query, from the Lean engine.</p>'+
  '<p>The engine this page loaded is older and does not have it. The next engine release carries it.</p></body></html>'});
function sparqlPage(url){
  if(!hasSparql())return sparqlNeedsEngine(url);
  const answer=call('',{op:'sparqlPage',argument:url.slice(sparqlURL.length+1)});
  return {url,title:answer.title,source:answer.source,next:answer.next,sources:[{kind:'Generated page',url,source:answer.source}]};
}
const isSparql=url=>url===sparqlURL||url.startsWith(sparqlURL+'/');
function show(next,remember=true){
  if(remember&&doc&&!next.title?.startsWith('Page refused'))browserState?.visit(next.url,next.title??'',doc.url).catch(()=>{});
  doc=next;if(!focused)field=showURL(next.url);scroll=0;loading=false;folded=0;
  if(remember){history=push(history.history,next.url);pages++;}
  post({type:'location',url:next.url,home:next.url===homeURL,push:remember});
  request();
}
// An address from the host browser's history or from the Hub address (#…): Lean's link rules
// route it as a typed address. One that leaves this site is refused, not opened: only the
// person's own tap may open a host tab.
function visit(address){
  // The address is absolute (the page made it from a URL), so the link rules route it, with
  // their fallback on an engine from before the route op.
  const route=router.route({...site,href:address,base:homeURL});
  if(!route)return;
  if(route.route==='system')show(refusal(route.url,'This address is not on this site. Type it in the address bar to open it.'),false);
  else if(route.route==='command')shellCommand(route.name,route.argument);
  else if(route.route==='refuse')show(refusal(route.url,route.reason),false);
  else navigate(route.url,false);
}
const pageFor=url=>url===graphURL?graphPage():statePages.includes(url)?statePage(url):url===wasmURL||url.startsWith(wasmURL+'/')?wasmPage(url):isSparql(url)?sparqlPage(url):prepare(url);
async function navigate(url,remember=true){
  const mine=++serial;loading=true;request();
  const stamp=currentStamp;
  let next;try{next=await pageFor(url);}catch(error){next=refusal(url,String(error.message??error));}
  if(mine===serial){const before=currentStamp;currentStamp=stamp;try{show(next,remember);}finally{currentStamp=before;}
    if(next.start){const frame=next.start;delete next.start;graphFrame(next,frame);}}
}
// An edit in the address bar. Lean gives the new state and the text for the clipboard,
// which the page writes (issue 1268).
function edit(action,text=''){
  const {clipboard,...next}=call('',{op:'shellEdit',shell:shell(),action,text});
  field=next;request();
  if(clipboard)post({type:'clipboard',text:clipboard});
}
function command(id,text=''){
  const answer=call('',{op:'command',command:id,textScalePercent:percent,history:history.history,focused});
  if(answer.target==='address'){if(!focused)focusAddress();edit(answer.action,text);return;}
  if(['back','forward','reload'].includes(answer.action)){if(answer.url)navigate(answer.url,false);history=answer;request();}
  if(answer.textScalePercent!==percent){percent=answer.textScalePercent;request();browserState?.settings({textZoom:percent}).catch(()=>{});}
  if(answer.action==='focusAddress')focusAddress();
  if(answer.action==='newTab')newTab();
  if(answer.action==='closeTab')closeTab(active);
  if(answer.action==='settings')navigate(settingsURL);
  if(answer.action==='viewSource')viewSource();
  if(answer.action==='print')printNow();
}
function viewSource(){
  for(const item of doc.sources??[]){
    const source=call('',{op:'sourcePage',kind:item.kind,url:item.url,source:item.source}).source;
    const facts=call(source,{op:'inspect',url:item.url+'#source'});
    const page={url:item.url+'#source',title:facts.title,source,sources:[]};
    keep();tabs.push({doc:page,history:push({entries:[],index:0},page.url),scroll:0});showTab(tabs.length-1);
  }
}
// The FOAF graph is a page whose model and frames come from Lean's graph app.
function graphFrame(page,frame){
  page.graph.model=frame.model;
  if(frame.commands.includes('startClock')){page.graph.clock=true;page.graph.last=performance.now();tick();}
  if(frame.commands.includes('stopClock'))page.graph.clock=false;
  if(frame.commands.includes('render')){page.source=call('',{op:'graphPage',model:frame.model}).source;request();}
}
function graphInput(kind,a,b){
  try{graphFrame(doc,call('',{op:'graphEvent',model:doc.graph.model,kind,a,b,width,shell:shell()}));}
  catch(error){doc=refusal(doc.url,String(error.message??error));request();}
}
function tick(){
  if(ticking)return;ticking=true;
  setTimeout(()=>{ticking=false;
    const graph=doc?.graph;if(!graph?.clock)return;
    if(!drawing){const now=performance.now();graphInput(7,Math.min(1000,Math.floor(now-graph.last)),0);graph.last=now;}
    tick();
  },33);
}
// The FOAF graph is a page of the tab (issue 1268): it goes into the tab's history like any
// page, so back leaves it and forward comes back to it (WebRoute.history_roundtrip).
const graphURL='foafnaut:graph';
async function graphPage(){
  const {source:rdf}=await fetchText(pagesBase+'foaf-demo.ttl');
  const frame=call('',{op:'graphStart',rdf,width,height,shell:shell()});
  const page={url:graphURL,title:'FOAF graph',source:'',sources:[],graph:{model:frame.model,clock:false,last:0},start:frame};
  page.source=call('',{op:'graphPage',model:frame.model}).source;
  return page;
}
function keep(){tabs[active]={doc,history,scroll};}
function showTab(index){serial++;loading=false;setFocus(false);active=index;({doc,history,scroll}=tabs[index]);field=showURL(doc.url);request();}
function newTab(){if(!home)return;keep();tabs.push({doc:home,history:push({entries:[],index:0},homeURL),scroll:0});showTab(tabs.length-1);focusAddress();}
function closeTab(index){if(tabs.length===1)return;keep();tabs.splice(index,1);showTab(Math.min(active>index?active-1:active,tabs.length-1));}
function setFocus(value){if(focused!==value){focused=value;post({type:'focus',focused});}}
// Lean selects the whole address when the bar takes the focus; typing then replaces it.
function focusAddress(){
  folded=0;
  try{const {clipboard:_,...next}=call('',{op:'shellEdit',shell:shell(),action:'focus',text:doc.url});field=next;}
  catch{field=showURL(doc.url);/* older engine: no selection */}
  setFocus(true);request();
}
function leaveAddress(){setFocus(false);field=showURL(doc.url);request();}
function scrollLimit(){
  const bottom=Math.max(0,...(frame?.webRender.boxes??[]).map(box=>box[2]+box[4]));
  return Math.max(0,bottom-height+60*scale);
}
// The request for a frame of this page at a scroll; its signature leaves the scroll out, so
// a band made at one scroll is known to be for the same state at another.
const renderOptions=at=>({op:'render',url:doc.url,...(doc.images?{images:doc.images}:{}),...(doc.heldImages?{heldImages:doc.heldImages}:{}),...(doc.commands?{commands:doc.commands}:{}),textScalePercent:percent,shell:{...shell(),scroll:at},live:doc===checked,binary:true});
const signature=options=>JSON.stringify({...options,images:undefined,shell:{...options.shell,scroll:0,collapse:undefined}});
// The graph page keeps its document and changes its source: the band must be of this source.
const canShift=()=>!!(layerSurface&&current&&current.doc===doc&&current.source===doc.source&&current.width===width&&current.height===height&&current.sig===signature(renderOptions(scroll)));
// A band made ahead (prefetch) that shows this scroll for the state of now.
const swapReady=()=>!!(prefetched&&prefetched.doc===doc&&prefetched.source===doc.source&&prefetched.width===width&&prefetched.height===height
  &&L.keeps(prefetched.answer.layers,scroll)&&prefetched.sig===signature(renderOptions(scroll)));
function scrollBy(amount){
  // A folding chrome takes its rows from the scroll first: down folds it, up unfolds it.
  let refolded=false;
  if(folding()&&amount){
    const rows=foldRows(),before=folded;
    if(rows&&(amount<0||scrollLimit()>0)){folded=Math.max(0,Math.min(rows,folded+Math.round(amount)));amount-=folded-before;refolded=folded!==before;}
  }
  const want=scroll+Math.round(amount),next=Math.max(0,Math.min(scrollLimit(),want));
  // At the top or bottom: the page stops a touch fling there.
  if(next!==want&&!refolded)post({type:'edge',direction:Math.sign(amount)});
  if(next===scroll){
    if(refolded){if(canShift()){shiftPending=true;if(!drawing)draw();}else request();}
    return;
  }
  const at=performance.now(),delta=next-scroll;scroll=next;
  // Scroll speed and direction (scroll_prefetch.ts trackMotion): when the next band is asked for.
  if(!motion||at-motion.at>250)motion={direction:Math.sign(delta),rowsPerMs:0,at};
  else{const instant=Math.abs(delta)/Math.max(1,at-motion.at),direction=Math.sign(delta);
    motion={direction,rowsPerMs:direction===motion.direction?(motion.rowsPerMs+instant)/2:instant,at};}
  // Inside the band on screen, a scroll only moves the composite: no Lean call. Past it, a
  // band made ahead for the same state is shown; with none, Lean makes one.
  if(canShift()||incoming){
    clearTimeout(bandTimer);
    shiftPending=true;
    if(!L.keeps((incoming??current.answer).layers,scroll)&&!swapReady()){dirty=true;bandWanted=true;}
    if(currentStamp!==undefined&&(pendingStamp===undefined||currentStamp<pendingStamp))pendingStamp=currentStamp;
    if(!drawing)draw();
  }else{bandWanted=layered!==false&&!!L;request();}
}
// The band for the frame on screen, made while the page is idle: from then on a scroll inside
// it is a composite. Its first answer also says whether this engine makes layers at all.
function scheduleBand(){
  clearTimeout(bandTimer);
  if(layered===false||!L||!doc||canShift())return;
  bandTimer=setTimeout(async()=>{
    if(drawing||dirty||shiftPending||canShift()||layered===false)return;
    const options=renderOptions(scroll),shownDoc=doc,at=scroll;
    let answer;
    try{answer=L.layersOf(render(doc.source,{...options,layers:true},width,height));}catch{return;}
    layered=!!answer;
    if(!answer||doc!==shownDoc||dirty)return;
    drawing=true;
    try{
      layerSurface??=await L.createLayerSurface(surfaceCanvas,{check:checkMode,waitForGpu:statsMode});
      if(!layerSurface)return;
      // Into the layer textures only: the screen already shows this state.
      incoming=answer;
      await gpuFeed();
      await layerSurface.drawLayers(answer);
      current={answer,doc:shownDoc,source:shownDoc.source,width,height,sig:signature(options),fold:options.shell.collapse??0};
      shownOffset=L.clampOffset(answer.layers,at).offset;frame=answer.page;
      if(scroll!==at||current.fold!==foldNow())shiftPending=true;
    }catch(error){console.warn('foafnaut: the band was not drawn:',String(error));current=undefined;}
    finally{drawing=false;incoming=undefined;}
    if(shiftPending||dirty)draw();
  },60);
}
// Near the edge of the keep range, or moving fast enough to pass it within two frames and the
// time of a band, Lean makes the next band while the page is otherwise idle. It runs on this
// thread, so it waits until no input is queued.
function schedulePrefetch(){
  clearTimeout(prefetchTimer);
  if(!canShift()||!motion||!motion.direction)return;
  const band=current.answer.layers,reach=L.keepReach(band),down=motion.direction>0,limit=scrollLimit();
  if(reach<=0||!L.keeps(band,scroll)||(down?band.keepTo>=limit:band.keepFrom<=0))return;
  const distance=down?band.keepTo-scroll:scroll-band.keepFrom;
  if(distance>256&&motion.rowsPerMs*(2*1000/60+bandMs)<distance)return;
  const target=Math.max(0,Math.min(limit,down?band.keepTo+reach:band.keepFrom-reach));
  if(prefetched&&prefetched.doc===doc&&prefetched.target===target&&prefetched.sig===current.sig)return;
  prefetchTimer=setTimeout(()=>{
    if(drawing||dirty||shiftPending||!canShift())return;
    const options=renderOptions(target),sig=signature(options);
    if(sig!==current.sig)return;
    try{
      const answer=L.layersOf(render(doc.source,{...options,layers:true},width,height));
      if(answer)prefetched={answer,target,sig,doc,source:doc.source,width,height,fold:options.shell.collapse??0};
    }catch{/* the ordinary frame path answers at the edge */}
  },20);
}
function shellCommand(name,argument){
  if(name==='back')command(6);else if(name==='forward')command(7);else if(name==='reload')command(8);
  else if(name==='new')newTab();else if(name==='close')closeTab(active);
  else if(name==='home')navigate(homeURL);else if(name==='source')viewSource();
  else if(name==='graph')navigate(graphURL);
  else if(name==='theme'){theme=argument||(theme==='next'?'arcade':'next');request();browserState?.settings({theme}).catch(()=>{});}
  else if(name==='classic'){
    // The settings checkbox: foafnaut:classic/on, /off, or a toggle with no argument.
    classicUI=argument==='on'?true:argument==='off'?false:!classicUI;folded=0;
    browserState?.settings({classicUI}).catch(()=>{});
    if(doc?.url===settingsURL)navigate(settingsURL,false);else request();
  }
  else if(name==='zoom'&&/^[0-9]+$/.test(argument)){percent=Math.max(50,Number(argument));request();browserState?.settings({textZoom:percent}).catch(()=>{});}
  else if(['bookmarks','history'].includes(name))navigate('foafnaut:'+name);
  else if(['bookmark','unbookmark','pod','sync'].includes(name))stateCommand(name,argument);
  else if(name==='wasm')navigate(wasmURL+(argument?'/'+argument:''));
  else if(name==='sparql')navigate(sparqlURL+(argument?'/'+argument:''));
  else if(name==='sparql-step')navigate(doc?.next??sparqlURL);
  else navigate(settingsURL);
}
// :bookmark [tags], :unbookmark, :pod URL. :sync needs the LWS client in the page, which the Hub
// does not load yet; the native browser syncs.
async function stateCommand(name,argument){
  try{
    if(!browserState)throw Error(`Browser state is off: ${stateReason}`);
    if(name==='bookmark')await browserState.bookmark(doc.url,doc.title??'',argument?argument.split(',').map(t=>t.trim()).filter(Boolean):undefined);
    else if(name==='unbookmark')await browserState.unbookmark(doc.url);
    else if(name==='pod'){await browserState.settings({remotePod:argument});return;}
    else throw Error('Sync with a pod runs in the native browser; the Hub keeps its state in this browser only.');
    navigate('foafnaut:bookmarks');
  }catch(error){doc=refusal('foafnaut:'+name,String(error.message??error));request();}
}
async function openState(){
  const stateCall=(op,request)=>call('',{...request,op});
  const available=await stateAvailable(stateCall);
  if(!available.available){stateReason=available.reason;return;}
  let store;try{store=await indexedDbStore();}catch{store=memoryStore('/','this tab only (no IndexedDB)');}
  browserState=createBrowserState({call:stateCall,store});stateReason='';
  const saved=await browserState.read();
  if(saved.settings){theme=saved.settings.theme;percent=saved.settings.textZoom;
    // An engine from before the setting does not keep it: the classic chrome then.
    if(typeof saved.settings.classicUI==='boolean')classicUI=saved.settings.classicUI;
    if(doc?.url===settingsURL)navigate(settingsURL,false);else request();}
}
// Lean's route for a link or an address (link-route.mjs), done as it says. This host tests
// no URL: a refused link shows Lean's reason and stays out of the history.
function follow(route){
  if(route.route==='command')shellCommand(route.name,route.argument);
  else if(route.route==='system')post({type:'open',url:route.url});
  else if(route.route==='refuse')show(refusal(route.url,route.reason),false);
  else navigate(route.url);
}
// An address typed in the bar, with an engine from before the route op (issue 1274).
function legacyGo(answer){
  if(answer.go==='command')shellCommand(answer.name,answer.argument);
  else if(answer.url?.startsWith('foafnaut:'))navigate(answer.url);
  else if(answer.go==='system'||!answer.url.startsWith(siteOrigin))post({type:'open',url:answer.url});
  else navigate(answer.url);
}
function chrome(control){
  const [name,index]=control.split(':');
  if(name==='back')command(6);else if(name==='forward')command(7);else if(name==='reload')command(8);
  else if(name==='settings')navigate(settingsURL);else if(name==='home')navigate(homeURL);else if(name==='source')viewSource();
  else if(name==='address')focusAddress();else if(name==='newTab')newTab();
  else if(name==='tab'&&Number(index)!==active){keep();showTab(Number(index));}
  else if(name==='close')closeTab(Number(index));
  else if(name==='tabs'){keep();showTab((active+1)%tabs.length);}
  else if(name==='expand')unfold();
}
function hit(x,y){
  // With layers, links are in the rows of the page band: the composite maps the window row to them.
  if(current&&frame===current.answer.page)y=y-current.answer.layers.top+shownOffset;
  const pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[JSON.stringify(frame.webRender.links??[]),frame.width,frame.height,x,y]);
  try{return JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
/** The fold the shell sends now: 0 with the classic chrome. */
const foldNow=()=>folding()?foldPercent():0;
function request(){dirty=true;if(currentStamp!==undefined&&(pendingStamp===undefined||currentStamp<pendingStamp))pendingStamp=currentStamp;if(!drawing)draw();}
async function draw(){
  drawing=true;
  while(dirty||shiftPending){
    // Past the band, the frame path below shows a band made ahead, or asks Lean for one.
    if(!dirty&&canShift()&&L.keeps(current.answer.layers,scroll)){await shift();continue;}
    dirty=false;shiftPending=false;
    const start=performance.now(),inputAt=pendingStamp,shown=doc;pendingStamp=undefined;
    const calls=leanRenders;
    try{
      // A page already on screen had Lean's full probe set on its first frame.
      const options=renderOptions(scroll),wantLayers=layered!==false&&bandWanted;bandWanted=false;
      let next,layers,swapped=false,fold=options.shell.collapse??0;
      if(layered&&swapReady()){layers=prefetched.answer;fold=prefetched.fold;prefetched=undefined;swapped=true;}
      else{
        next=render(doc.source,wantLayers?{...options,layers:true}:options,width,height);
        // An engine with no layers answers one frame: this page then draws frames as before.
        if(wantLayers){layers=L.layersOf(next);layered=!!layers;}
      }
      checked=doc;
      const laid=performance.now();
      if(!swapped)bandMs=laid-start;
      phase('firstLayout');
      let rgba,pixelHash,gpuMs,path;
      // The layer surface draws every frame when this engine makes layers or may (the first
      // frame comes before its band says), with one device for the canvas.
      if(layers||layerSurface||layered!==false){
        // With no canvas in this thread, each frame is read back and the page paints it.
        layerSurface??=await L.createLayerSurface(surfaceCanvas,{check:checkMode,waitForGpu:statsMode});
        if(!layerSurface)throw Error('A WebGPU adapter is unavailable in this browser.');
        let pixels;
        if(layers){
          incoming=layers;
          await gpuFeed();
          await layerSurface.drawLayers(layers);
          const {offset}=L.clampOffset(layers.layers,scroll);
          pixels=await layerSurface.composite(width,height,offset);
          current={answer:layers,doc,source:doc.source,width,height,sig:signature(options),fold};shownOffset=offset;frame=layers.page;
          path=swapped?'band':'layers';
          // A band made at another fold: the chrome layer is drawn again at the next shift.
          if(fold!==foldNow())shiftPending=true;
        }else{pixels=await layerSurface.drawSingle(next);frame=next;path='frame';}
        pixelHash=pixels?L.hashPixels(pixels):undefined;
        if(!surfaceCanvas){rgba=pixels;path+='-readback';}
      }else if(surfaceCanvas){
        // Straight to the canvas: no readback unless ?check=surface asked for it.
        surface??=await createSurface(surfaceCanvas,{check:checkMode,waitForGpu:statsMode});
        if(!surface)throw Error('A WebGPU adapter is unavailable in this browser.');
        const result=await surface.draw(next);
        pixelHash=result.pixelHash||undefined;gpuMs=Math.round(result.gpuMs);frame=next;path='surface';
      }else{
        if(session&&(typeof session.update!=='function'||!(await session.update(next)))){session.close();session=undefined;}
        session??=await createSession(next,'svg-offscreen');
        if(!session)throw Error('A WebGPU adapter is unavailable in this browser.');
        rgba=await session.draw();
        if(hashPixels)pixelHash=hashPixels(rgba);
        frame=next;path='readback';
      }
      const done=performance.now();incoming=undefined;
      phase('firstFrame');
      post({type:'frame',width,height,title:shown.title,rgba:rgba?.buffer,presented:!rgba,inputAt,
        stats:{path,layoutMs:Math.round(laid-start),drawMs:Math.round(done-laid),gpuMs,totalMs:Math.round(done-start),
          pixelHash,primitives:frame.primitiveCount,url:shown.url,address:field.address,scroll,tabs:tabs.length,theme,percent,
          leanRenders:leanRenders-calls,leanCalls,chromeRenders,collapse:foldNow(),rows:Math.round(frame.data.length/4),...(current?{bandTop:current.answer.layers.bandTop,offset:shownOffset}:{}),
          // For hub_links_check.mjs: the links of a one-frame view, and who routes them.
          ...(statsMode&&layered===false?{links:frame.webRender.links,routes:router.lean?'lean':'fallback'}:{})}},rgba?[rgba.buffer]:[]);
      if(!phasesPosted){phasesPosted=true;post({type:'phases',phases});firstFrameSeen();}
    }catch(error){
      incoming=undefined;
      session?.close();session=undefined;
      try{surface?.close();}catch{/* the frame is over */}surface=undefined;
      try{layerSurface?.close();}catch{/* the frame is over */}layerSurface=undefined;current=undefined;prefetched=undefined;
      if(doc.title==='Page refused'){post({type:'error',error:String(error.message??error)});break;}
      doc=refusal(doc.url,String(error.message??error));dirty=true;
    }
  }
  drawing=false;
  schedulePrefetch();scheduleBand();schedulePrint();
}
// A scroll inside the band on screen: the composite at the new offset, with no Lean call.
async function shift(){
  shiftPending=false;
  const start=performance.now(),inputAt=pendingStamp;pendingStamp=undefined;
  try{
    // The fold changed: Lean draws the chrome layer alone (no layout, no page band) and
    // the composite takes its new top.
    const fold=foldNow();let chromeMs;
    if(current.fold!==fold){
      const at=performance.now(),held=current;
      const answer=render('',{op:'chromeLayer',shell:shell(),binary:true,live:doc===checked},width,height,true);
      await layerSurface.setChrome(answer.chrome,answer.top);
      if(current===held){current={...current,answer:{...current.answer,chrome:answer.chrome,layers:{...current.answer.layers,top:answer.top}},fold};}
      chromeMs=Math.round(performance.now()-at);
    }
    const {offset}=L.clampOffset(current.answer.layers,scroll);
    const pixels=await layerSurface.composite(width,height,offset);
    shownOffset=offset;
    const done=performance.now(),rgba=surfaceCanvas?undefined:pixels;
    post({type:'frame',width,height,title:doc.title,rgba:rgba?.buffer,presented:!rgba,inputAt,
      stats:{path:surfaceCanvas?'shift':'shift-readback',layoutMs:0,drawMs:Math.round(done-start),totalMs:Math.round(done-start),pixelHash:pixels?L.hashPixels(pixels):undefined,
        primitives:0,url:doc.url,address:field.address,scroll,tabs:tabs.length,theme,percent,leanRenders:0,leanCalls,chromeRenders,collapse:fold,chromeMs,top:current.answer.layers.top,rows:Math.round(current.answer.page.data.length/4),bandTop:current.answer.layers.bandTop,offset}},rgba?[rgba.buffer]:[]);
  }catch(error){
    console.warn('foafnaut: composite failed, drawing a Lean frame:',String(error));
    try{layerSurface?.close();}catch{/* gone */}layerSurface=undefined;current=undefined;dirty=true;
  }
}
// The page asks first whether this worker can draw to an OffscreenCanvas with WebGPU,
// because a canvas can be handed over once.
async function hello(data){
  // The page asked for: its fetch starts now, beside the engine's.
  const first=pageURL(data?.page);if(first)fetchEarly(first,'text');
  let surfaceOk=false;
  try{
    const transport=await import('../html-webgpu/runtime/gpu-transport.mjs');
    surfaceOk=inWorker&&typeof transport.createSurfaceSession==='function'&&typeof OffscreenCanvas==='function'
      &&!!navigator.gpu&&!!new OffscreenCanvas(1,1).getContext('webgpu');
  }catch{surfaceOk=false;}
  post({type:'caps',surface:surfaceOk});
}
// The engine from the module compiled while it downloaded (engineCompiled). The loader is
// given the compiled module; with none, it fetches and compiles as before.
async function startEngine(createModule){
  let compiled;
  try{compiled=await engineCompiled;}catch(error){console.warn('foafnaut: the engine module did not compile early:',String(error));}
  if(!compiled)return createModule();
  let fail;const failed=new Promise((_,reject)=>{fail=reject;});
  return Promise.race([failed,createModule({instantiateWasm(imports,done){
    WebAssembly.instantiate(compiled,imports).then(instance=>{
      // The instance's own export says how many arguments the bytes font call takes (a Wasm
      // function's length is its parameter count): five is the engine with the fallback
      // argument, so even the first font goes in as bytes, with no Base64 (issue 1274).
      if(instance.exports.web_document_font_call_bin?.length===5)fontBytesTakeFallback=true;
      done(instance,compiled);},fail);return {};}})]);
}
async function start(data){
  ({width,height,scale}=data);
  // Page text in CSS pixels, as a browser has it: the canvas is in device pixels, so the
  // starting text zoom follows the pixel ratio (150 on a 1x screen, 450 on a 3x phone).
  // Before this, a phone drew page text at about 5 CSS px. A saved zoom still wins.
  percent=Math.max(50,Math.round(150*scale/5)*5);
  checkMode=data.check===true;statsMode=data.stats===true;
  // ?layers=0: one Lean frame for each scroll, as before the two-layer view.
  if(data.layers===false)layered=false;
  if(!navigator.gpu)throw Error('This browser does not provide WebGPU.');
  const wanted=pageURL(data.page)??(data.page==='sparql'?sparqlURL:undefined)??(data.page==='wasm'||/^wasm\/[a-z0-9-]+\.wasm(#[A-Za-z0-9_-]+)?$/.test(data.page??'')?'foafnaut:'+data.page:undefined);
  // The page's fallback fonts start to come with the page, beside the engine.
  if(wanted?.startsWith('http'))fetchEarly(wanted,'text').then(page=>fontsWanted(page.source)).catch(()=>{});
  const [{default:createModule},transport]=await Promise.all(runtimeModules);
  try{L=await layersModule;}catch(error){layered=false;console.warn('foafnaut: no layers:',String(error));}
  module=await startEngine(createModule);phase('engineReady');
  createSession=transport.createOffscreenSession;renderOffscreen=transport.render;hashPixels=transport.hashPixels;
  if(data.canvas&&typeof transport.createSurfaceSession==='function'){surfaceCanvas=data.canvas;createSurface=transport.createSurfaceSession;}
  await loadFont();phase('fontReady');
  home=await prepare(homeURL);
  // A page asked for in the address is the first frame: the demo index is not drawn first.
  let first=home;
  if(wanted){try{first=await pageFor(wanted);}catch(error){first=refusal(wanted,String(error.message??error));}}
  phase('pageReady');
  history=push({entries:[],index:0},homeURL);
  if(first!==home){history=push(history.history,first.url);pages++;}
  doc=first;field=showURL(first.url);tabs.push({doc,history,scroll:0});
  // The page keeps the keys of Lean's table for a host with no menu, and needs them at once.
  // An engine from before these ops (issue 1268) has no key table and no address edits.
  try{post({type:'keys',table:call('',{op:'keyTable',platform:data.platform==='mac'?'mac':'other'})});}catch{/* older engine */}
  // Back and forward swipes (WebGesture.lean): asked once; an engine without the op has none.
  try{gestures=call('',{op:'gesture',action:'info'});post({type:'gestures',edgeZone:gestures.edgeZone});}catch{gestures=undefined;}
  ready=true;
  openState().then(()=>{if(first!==home&&!first.title?.startsWith('Page refused'))browserState?.visit(first.url,first.title??'',homeURL).catch(()=>{});})
    .catch(error=>{stateReason=String(error.message??error);});
  // A new window starts in the address bar with the address selected (issue 1268).
  if(data.address)visit(data.address);
  else if(wanted)request();else focusAddress();
  for(const message of early.splice(0))receive(message);
}
// Printing (issue 1268). The canvas is drawn by WebGPU and does not print, so the page
// prints images that Lean draws: Lean lays the current document out for the paper with the
// print media rules and says where the pages break (op printLayout); it draws each page
// (render with printPage); the GPU reads it back and it becomes a PNG. The page only places
// the images in its print-only container (browser.mjs). The paper is A4 inside 36-point
// margins (index.njk @page), at 2 device pixels a point; CSS text is 150% at the default
// text zoom, so 16 CSS pixels print as 12 points, as in the native browser (native_print.ts).
// The browser's own print (menu, share sheet) can not wait for this worker, so the pages
// of the document on screen are made ahead, one Lean call at a time, after the page has
// been idle for a while; any input puts the work off again. Until they are ready, an image
// of the view on screen prints instead. Command/Control+P (Lean's key table, command 18)
// waits for the pages and then prints. An engine without printLayout prints the view only.
const PRINT_POINTS=[523,769],PRINT_PIXELS_PER_POINT=2,PRINT_MAX_PAGES=30,PRINT_IDLE_MS=1500,PRINT_VIEW_IDLE_MS=400;
const printWidth=PRINT_POINTS[0]*PRINT_PIXELS_PER_POINT,printHeight=PRINT_POINTS[1]*PRINT_PIXELS_PER_POINT;
let printOps,printJob,printTimer,printBusy=false,printWanted=false;
/** This engine paginates for print: it answers printLayout (asked once). */
function hasPrintOps(){
  if(printOps===undefined){
    try{printOps=Array.isArray(call('<!doctype html><html><head><title>print</title></head><body><p>print</p></body></html>',
      {op:'printLayout',url:pagesBase+'print-probe.html',media:'print',textScalePercent:150},printWidth,printHeight,false).pages);}
    catch{printOps=false;}
  }
  return printOps;
}
/** The text zoom on paper: the zoom on screen for one device pixel, 150 by default. */
const printPercent=()=>Math.max(50,Math.min(1000,Math.round(percent/scale/5)*5));
// The prepared pages are of this document, its source, its scripts' DOM changes, text zoom and
// theme. While Command/Control+P waits, script changes do not start them again.
const printFits=job=>!!job&&job.doc===doc&&job.source===doc.source&&(printWanted||job.commands===doc.commands)&&job.percent===percent&&job.scale===scale&&job.theme===theme;
function printOptions(){
  return {url:doc.url,...(doc.images?{images:doc.images}:{}),...(doc.heldImages?{heldImages:doc.heldImages}:{}),...(doc.commands?{commands:doc.commands}:{}),
    textScalePercent:printPercent(),media:'print'};
}
async function printPNG(frame){
  const rgba=await renderOffscreen(frame,'svg-offscreen');
  if(!rgba)throw Error('A WebGPU adapter is unavailable in this browser.');
  const canvas=new OffscreenCanvas(frame.width,frame.height);
  canvas.getContext('2d').putImageData(new ImageData(new Uint8ClampedArray(rgba.buffer,rgba.byteOffset,rgba.byteLength),frame.width,frame.height),0,0);
  return canvas.convertToBlob({type:'image/png'});
}
/** Tell the page what it can print now. */
function printPost(go=false){
  const job=printJob;
  post({type:'print',go,ready:!!job?.done,pages:job?.done?job.pages:[],total:job?.total??0,
    view:job?.view?.blob,viewOnly:!!job?.viewOnly,width:printWidth,height:printHeight,
    viewWidth:job?.view?.width,viewHeight:job?.view?.height,error:job?.error,longestStepMs:job?.longest??0});
}
/** The view image is made sooner after the page settles than the pages: it costs one draw. */
const printViewStale=()=>!printFits(printJob)||!printJob.done&&(!printJob.view||printJob.view.scroll!==scroll||printJob.view.width!==width||printJob.view.height!==height);
function schedulePrint(delay){
  clearTimeout(printTimer);
  if(!ready||typeof OffscreenCanvas!=='function')return;
  delay??=printViewStale()?PRINT_VIEW_IDLE_MS:PRINT_IDLE_MS;
  printTimer=setTimeout(printStep,printWanted?0:delay);
}
/** One step of the print work: the view image, the page breaks, or one page. */
async function printStep(){
  if(printBusy||!ready||!doc)return;
  if(!printWanted&&(drawing||dirty||shiftPending||pendingMove||pendingScroll)){schedulePrint();return;}
  if(!printFits(printJob)){
    printJob={doc,source:doc.source,commands:doc.commands,percent,scale,theme,pages:[],breaks:undefined,total:0,done:false,viewOnly:false};
    printPost();
  }
  const job=printJob;
  // An engine with no print ops prints the view: it follows the scroll.
  if(job.done&&job.viewOnly&&!job.error&&job.view&&(job.view.scroll!==scroll||job.view.width!==width||job.view.height!==height))job.done=false;
  if(job.done){if(printWanted){printWanted=false;printPost(true);}return;}
  printBusy=true;let viewMade=false;const began=performance.now();
  try{
    if(!job.view||(job.view.scroll!==scroll||job.view.width!==width||job.view.height!==height)&&!printWanted){
      // The view on screen, chrome and all: the layout is the one on screen, so Lean only draws.
      const at=scroll,w=width,h=height;
      const frame=render(doc.source,{...renderOptions(at),live:false,checks:false},w,h,false,false);
      job.view={blob:await printPNG(frame),scroll:at,width:w,height:h};viewMade=true;
      if(!hasPrintOps()){job.viewOnly=true;job.done=true;}
    }else if(!job.breaks){
      const layout=call(doc.source,{...printOptions(),op:'printLayout'},printWidth,printHeight,false);
      job.total=layout.pages.length;job.breaks=layout.pages.slice(0,PRINT_MAX_PAGES);
    }else{
      const [top,rows]=job.breaks[job.pages.length];
      const frame=render(doc.source,{...printOptions(),op:'render',binary:true,checks:false,printPage:[top,rows]},printWidth,printHeight,false,false);
      job.pages.push(await printPNG(frame));
    }
    if(job.breaks&&job.pages.length>=job.breaks.length)job.done=true;
  }catch(error){
    // A page Lean or the GPU could not draw: the view prints, with the reason.
    job.error=String(error.message??error);job.viewOnly=true;job.done=true;
  }finally{printBusy=false;job.longest=Math.max(job.longest??0,Math.round(performance.now()-began));}
  if(job!==printJob)return schedulePrint();
  if(job.done&&printWanted){printWanted=false;printPost(true);return;}
  if(job.done||viewMade)printPost();
  if(!job.done)schedulePrint(printWanted?0:30);
}
/** Command 18: the pages of this document, then the host's print. */
function printNow(){
  // With no OffscreenCanvas there are no images: the host prints what it can.
  if(typeof OffscreenCanvas!=='function'){printPost(true);return;}
  printWanted=true;
  post({type:'print-status',preparing:!(printFits(printJob)&&printJob.done)});
  schedulePrint(0);
}
// Back and forward swipes. Lean (WebGesture.lean, op gesture) says what
// a touch from the window's edge or a trackpad's horizontal swipe means; the worker puts
// its hint in the shell, where WebShell draws the arrow, and goes back or forward when it
// says so. A trackpad gesture has no end on the web: 160 ms with no wheel event ends it
// (its momentum included). The page keeps wheel events from the host browser, so the host's
// own swipe never navigates as well.
let gestures,swipeHint=0,wheelSum,wheelTimer;
const wheelIdleMs=160;
function setHint(value){if(value!==swipeHint){swipeHint=value;request();}}
function gestureAnswer(answer){
  setHint(answer.navigate?0:answer.hint);
  if(answer.navigate)command(answer.direction==='back'?6:7);
}
function swipe(data){
  if(!gestures)return;
  if(data.phase==='cancel'){setHint(0);return;}
  const answer=call('',{op:'gesture',action:'touch',width:data.width,startX:data.startX,startY:data.startY,x:data.x,y:data.y,
    vx:data.vx??0,fingers:1,ended:data.phase==='end'});
  if(data.phase==='end'){gestureAnswer({...answer,hint:0});return;}
  post({type:'swipe',id:data.id,phase:answer.phase});
  setHint(answer.hint);
}
function wheel(data){
  if(!gestures)return;
  clearTimeout(wheelTimer);
  wheelTimer=setTimeout(()=>{
    const sum=wheelSum;wheelSum=undefined;
    if(sum)gestureAnswer({...call('',{op:'gesture',action:'wheel',dx:Math.round(sum.dx),dy:Math.round(sum.dy),ended:true}),hint:0});
  },wheelIdleMs);
  wheelSum??={dx:0,dy:0};
  wheelSum.dx+=data.dx;wheelSum.dy+=data.dy;
  setHint(call('',{op:'gesture',action:'wheel',dx:Math.round(wheelSum.dx),dy:Math.round(wheelSum.dy),ended:false}).hint);
}
function flush(){
  const move=pendingMove,scrolled=pendingScroll;pendingMove=pendingScroll=undefined;
  if(move)handle(move);
  if(scrolled)handle(scrolled);
}
function receive(data){
  if(data.type==='hello'){hello(data);return;}
  if(data.type==='start'){start(data).catch(error=>post({type:'error',error:String(error.message??error)}));return;}
  if(!ready){early.push(data);return;}
  // Input puts off the print pages made ahead (an explicit print goes on).
  if(!printWanted)schedulePrint();
  if(data.type==='move'||data.type==='scroll'){
    if(data.type==='move')pendingMove=data;
    else pendingScroll=pendingScroll?{...data,amount:pendingScroll.amount+data.amount,t:pendingScroll.t}:data;
    if(!flushPort){flushPort=new MessageChannel();flushPort.port1.onmessage=flush;}
    flushPort.port2.postMessage(0);
    return;
  }
  flush();handle(data);
}
function handle(data){
  currentStamp=data.t;
  try{apply(data);}finally{currentStamp=undefined;}
}
function apply(data){
  if(data.type==='visit'){visit(data.address);return;}
  if(data.type==='resize'){({width,height,scale}=data);folded=Math.min(folded,foldRows());if(doc.graph)graphInput(1,width,height);request();}
  if(data.type==='scroll')scrollBy(data.amount);
  if(data.type==='swipe')swipe(data);
  if(data.type==='wheel')wheel(data);
  if(data.type==='command')command(data.command);
  // A touch pinch: the zoom at its start times the finger ratio, in steps of 5 percent,
  // from Lean's smallest (50) to 1000. Lean lays the page out again at each new step.
  if(data.type==='pinch'){
    if(data.phase==='start')pinchBase=percent;
    else if(data.phase==='move'&&pinchBase&&Number.isFinite(data.ratio)){
      const next=Math.max(50,Math.min(1000,Math.round(pinchBase*data.ratio/5)*5));
      if(next!==percent){percent=next;request();}
    }else if(data.phase==='end')pinchBase=undefined;
  }
  if(data.type==='paste')command(14,data.text);
  if(data.type==='press'){
    const control=call('',{op:'shellHit',shell:shell(),x:data.x,y:data.y,width}).control;
    if(control)chrome(control);else{if(focused)leaveAddress();if(doc.graph)graphInput(2,data.x,data.y);}
  }
  if(data.type==='move'&&doc.graph&&!focused)graphInput(3,data.x,data.y);
  if(data.type==='release'&&doc.graph){graphInput(4,data.x,data.y);return;}
  if(data.type==='release'&&frame&&!data.scrolled){
    if(call('',{op:'shellHit',shell:shell(),x:data.x,y:data.y,width}).control)return;
    scriptClick(data.x,data.y);
    const target=hit(data.x,data.y);
    if(target?.href)follow(router.route({...site,href:target.href,base:doc.baseURL||doc.url}));
  }
  if(data.type==='text'&&focused){const {clipboard:_,...next}=call('',{op:'shellText',shell:shell(),text:data.text});field=next;request();}
  if(data.type==='key'&&focused){
    if(data.key===36){const target=field.address;leaveAddress();
      const route=router.address({...site,address:target,base:doc.baseURL||doc.url});
      if(route)follow(route);else legacyGo(call('',{op:'shellSubmit',address:target}));}
    else if(data.key===53)leaveAddress();
    else{field=call('',{op:'shellKey',shell:shell(),key:data.key,modifiers:data.modifiers??0});request();}
  }
}
if(inWorker)self.onmessage=({data})=>receive(data);
/** Start the loop on this thread. Returns the function that takes input messages. */
export function onThisThread(deliver){post=message=>deliver({data:message});return receive;}
