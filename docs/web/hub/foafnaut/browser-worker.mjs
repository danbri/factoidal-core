// The browser loop for a web page. It matches run_html.ts, the native loop: the
// shell, history and every decision are Lean values and Lean calls.
// It runs in a worker, or on the page's own thread where a worker can not start:
// an iframe sandbox without allow-same-origin has an opaque origin, and the worker
// constructor refuses that (Foafos guests). `post` is the only way out of the loop.
let post=(message,transfer)=>self.postMessage(message,transfer);
// Bookmarks, history and settings in this browser's IndexedDB, in the resource format Lean
// decides for the native browser's local pod (browser-state.mjs, WebState.lean).
import {createBrowserState,indexedDbStore,memoryStore,stateAvailable} from './browser-state.mjs';
let browserState,stateReason='starting';
const statePages=['foafnaut:bookmarks','foafnaut:history'];
const inWorker=typeof WorkerGlobalScope!=='undefined'&&self instanceof WorkerGlobalScope;
const pagesBase=new URL('./pages/',import.meta.url).href,siteOrigin=new URL(import.meta.url).origin;
const homeURL=pagesBase+'index.html',settingsURL=pagesBase+'settings.html';
let module,createSession,session,createSurface,hashPixels,surface,surfaceCanvas,checkMode=false,statsMode=false;
// Input that arrives before the engine is ready, and moves and scrolls that arrive while a
// frame builds, wait here. Every press, release, key, text and command is applied in the
// order it arrived; only moves and scrolls are merged.
let ready=false,currentStamp,pendingStamp,pendingMove,pendingScroll,flushPort;
const early=[];
let width=800,height=600,scale=1,theme='next',percent=150,pages=1,pinchBase;
// The address bar's text, cursor, selection and undo step: a Lean value (WebShell.editJson).
const showURL=url=>({address:url,cursor:url.length,anchor:url.length,undo:null,redo:null,typing:false});
let field=showURL(''),focused=false,loading=false,scroll=0,active=0;
let doc,history,frame,home,checked,dirty=false,drawing=false,serial=0,ticking=false;
const tabs=[];
function call(source,options,w=1,h=1){
  const pointer=module.ccall('web_document_call','number',['string','string','number','number'],[source,JSON.stringify(options),w,h]);
  if(!pointer)throw Error('Lean engine allocation failed');
  try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
  finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
const shell=()=>({tabs:tabs.map((tab,i)=>({title:(i===active?doc:tab.doc)?.title??''})),active,...field,focused,
  canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll});
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
function render(source,options,w,h){
  if(typeof module._web_document_call_bin!=='function')return frameFloats(call(source,options,w,h));
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
  if(typeof frame.dataSection==='number'){const [o,l]=sections[frame.dataSection];frame.data=new Float32Array(buffer,o,l/4);delete frame.dataSection;}
  if(typeof frame.tilesSection==='number'){const [o,l]=sections[frame.tilesSection];frame.tiles=new Uint32Array(buffer,o,l/4);delete frame.tilesSection;}
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
  const response=await fetch(new URL(path,import.meta.url));
  if(!response.ok)throw Error(`HTTP ${response.status}`);
  const bytes=new Uint8Array(await response.arrayBuffer());
  const sha=[...new Uint8Array(await crypto.subtle.digest('SHA-256',bytes))].map(b=>b.toString(16).padStart(2,'0')).join('');
  return {bytes,sha};
}
// Fonts after Noto Sans, for the characters it lacks. Lean picks the font for each one.
const fallbackFonts=[['./fonts/noto-sans-armenian/NotoSansArmenian-Regular.ttf','Noto Sans Armenian']];
// Noto Sans is the default face. Lean reads and shapes it; if it does not load, the
// page stays in the bitmap face. Fallback fonts need an engine that takes fonts as
// bytes: an older one would read a fallback font as a replacement.
async function loadFont(){
  let primary;
  try{
    const {bytes,sha}=await fontFile('./fonts/noto-sans/NotoSans-Regular.ttf');
    primary=fontLoad(bytes,'Noto Sans',sha);
  }catch(error){console.warn('foafnaut: bitmap font, because Noto Sans did not load:',String(error));return;}
  // Only an engine that holds several fonts answers with `fonts` (the count held). An older
  // engine would take a fallback font as a replacement for Noto Sans, or abort on the
  // fallback argument: on 2026-11-07 the published engine did both (issue 1274).
  if(typeof primary?.fonts!=='number')return;
  fontBytesTakeFallback=true;
  for(const [path,family] of fallbackFonts){
    try{const {bytes,sha}=await fontFile(path);fontLoad(bytes,family,sha,true);}
    catch(error){console.warn(`foafnaut: no ${family}:`,String(error));}
  }
}
async function fetchText(url){
  const response=await fetch(url);if(!response.ok)throw Error(`HTTP ${response.status}`);
  return {url:response.url||url,source:await response.text()};
}
async function prepare(url){
  const page=await fetchText(url);
  const sources=[{kind:'Source',url:page.url,source:page.source}];
  const sheet=call(page.source,{op:'xmlStylesheet',url:page.url});
  if(sheet.url){
    const xsl=await fetchText(sheet.url);
    page.source=call(page.source,{op:'xslt',url:page.url,stylesheet:xsl.source,stylesheetURL:xsl.url}).source;
    sources[0].kind='XML source';
    sources.push({kind:'XSLT source',url:xsl.url,source:xsl.source},{kind:'Generated page',url:page.url,source:page.source});
  }
  const facts=call(page.source,{op:'inspect',url:page.url});
  const images=await pageImages(facts.images);
  return {url:page.url,title:facts.title,baseURL:facts.baseURL,source:page.source,sources,...(images.length?{images}:{})};
}
// Lean lists the images a page wants (SVG image, HTML img) by key. The page fetches only
// those of this site, with size caps, and gives the bytes back with the key. One that
// fails is left out and shows its alt text. An engine that lists no images gets none,
// so an older engine never sees the field (issue 1274).
const maxImageBytes=4194304,maxPageImageBytes=6291456;
async function pageImages(wanted){
  const images=[];let total=0;
  for(const {key,url} of wanted??[]){
    try{
      const target=new URL(url);if(target.origin!==siteOrigin)continue;
      const response=await fetch(target);if(!response.ok)continue;
      if(Number(response.headers.get('content-length')??0)>maxImageBytes){response.body?.cancel();continue;}
      const bytes=new Uint8Array(await response.arrayBuffer());
      if(bytes.length>maxImageBytes||total+bytes.length>maxPageImageBytes)continue;
      total+=bytes.length;
      let text='';
      for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
      images.push({key,base64:btoa(text)});
    }catch{}
  }
  return images;
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
  doc=next;if(!focused)field=showURL(next.url);scroll=0;loading=false;
  if(remember){history=push(history.history,next.url);pages++;}
  request();
}
async function navigate(url,remember=true){
  const mine=++serial;loading=true;request();
  const stamp=currentStamp;
  let next;try{next=await (statePages.includes(url)?statePage(url):url===wasmURL||url.startsWith(wasmURL+'/')?wasmPage(url):isSparql(url)?sparqlPage(url):prepare(url));}catch(error){next=refusal(url,String(error.message??error));}
  if(mine===serial){const before=currentStamp;currentStamp=stamp;try{show(next,remember);}finally{currentStamp=before;}}
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
async function openGraph(){
  const {source:rdf}=await fetchText(pagesBase+'foaf-demo.ttl');
  const frame=call('',{op:'graphStart',rdf,width,height,shell:shell()});
  const page={url:'foafnaut:graph',title:'FOAF graph',source:'',sources:[],graph:{model:frame.model,clock:false,last:0}};
  page.source=call('',{op:'graphPage',model:frame.model}).source;
  keep();tabs.push({doc:page,history:push({entries:[],index:0},page.url),scroll:0});showTab(tabs.length-1);graphFrame(page,frame);
}
function keep(){tabs[active]={doc,history,scroll};}
function showTab(index){serial++;loading=false;setFocus(false);active=index;({doc,history,scroll}=tabs[index]);field=showURL(doc.url);request();}
function newTab(){keep();tabs.push({doc:home,history:push({entries:[],index:0},homeURL),scroll:0});showTab(tabs.length-1);focusAddress();}
function closeTab(index){if(tabs.length===1)return;keep();tabs.splice(index,1);showTab(Math.min(active>index?active-1:active,tabs.length-1));}
function setFocus(value){if(focused!==value){focused=value;post({type:'focus',focused});}}
// Lean selects the whole address when the bar takes the focus; typing then replaces it.
function focusAddress(){
  try{const {clipboard:_,...next}=call('',{op:'shellEdit',shell:shell(),action:'focus',text:doc.url});field=next;}
  catch{field=showURL(doc.url);/* older engine: no selection */}
  setFocus(true);request();
}
function leaveAddress(){setFocus(false);field=showURL(doc.url);request();}
function scrollBy(amount){
  const bottom=Math.max(0,...(frame?.webRender.boxes??[]).map(box=>box[2]+box[4]));
  const next=Math.max(0,Math.min(Math.max(0,bottom-height+60*scale),scroll+Math.round(amount)));
  if(next!==scroll){scroll=next;request();}
}
function shellCommand(name,argument){
  if(name==='back')command(6);else if(name==='forward')command(7);else if(name==='reload')command(8);
  else if(name==='new')newTab();else if(name==='close')closeTab(active);
  else if(name==='home')navigate(homeURL);else if(name==='source')viewSource();
  else if(name==='graph')openGraph().catch(error=>{doc=refusal('foafnaut:graph',String(error.message??error));request();});
  else if(name==='theme'){theme=argument||(theme==='next'?'arcade':'next');request();browserState?.settings({theme}).catch(()=>{});}
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
  if(saved.settings){theme=saved.settings.theme;percent=saved.settings.textZoom;request();}
}
function go(answer){
  if(answer.go==='command')shellCommand(answer.name,answer.argument);
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
}
function hit(x,y){
  const pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[JSON.stringify(frame.webRender.links??[]),frame.width,frame.height,x,y]);
  try{return JSON.parse(module.UTF8ToString(pointer));}finally{module.ccall('web_render_free',null,['number'],[pointer]);}
}
function request(){dirty=true;if(currentStamp!==undefined&&(pendingStamp===undefined||currentStamp<pendingStamp))pendingStamp=currentStamp;if(!drawing)draw();}
async function draw(){
  drawing=true;
  while(dirty){
    dirty=false;
    const start=performance.now(),inputAt=pendingStamp;pendingStamp=undefined;
    try{
      // A page already on screen had Lean's full probe set on its first frame.
      const next=render(doc.source,{op:'render',url:doc.url,...(doc.images?{images:doc.images}:{}),textScalePercent:percent,shell:shell(),live:doc===checked,binary:true},width,height);
      checked=doc;
      const laid=performance.now();
      let rgba,pixelHash,gpuMs;
      if(surfaceCanvas){
        // Straight to the canvas: no readback unless ?check=surface asked for it.
        surface??=await createSurface(surfaceCanvas,{check:checkMode,waitForGpu:statsMode});
        if(!surface)throw Error('A WebGPU adapter is unavailable in this browser.');
        const result=await surface.draw(next);
        pixelHash=result.pixelHash||undefined;gpuMs=Math.round(result.gpuMs);
      }else{
        if(session&&(typeof session.update!=='function'||!(await session.update(next)))){session.close();session=undefined;}
        session??=await createSession(next,'svg-offscreen');
        if(!session)throw Error('A WebGPU adapter is unavailable in this browser.');
        rgba=await session.draw();
        if(hashPixels)pixelHash=hashPixels(rgba);
      }
      frame=next;
      const done=performance.now();
      post({type:'frame',width:next.width,height:next.height,title:doc.title,rgba:rgba?.buffer,presented:!rgba,inputAt,
        stats:{path:surfaceCanvas?'surface':'readback',layoutMs:Math.round(laid-start),drawMs:Math.round(done-laid),gpuMs,totalMs:Math.round(done-start),
          pixelHash,primitives:next.primitiveCount,url:doc.url,address:field.address,scroll,tabs:tabs.length,theme,percent}},rgba?[rgba.buffer]:[]);
    }catch(error){
      session?.close();session=undefined;
      try{surface?.close();}catch{/* the frame is over */}surface=undefined;
      if(doc.title==='Page refused'){post({type:'error',error:String(error.message??error)});break;}
      doc=refusal(doc.url,String(error.message??error));dirty=true;
    }
  }
  drawing=false;
}
// The page asks first whether this worker can draw to an OffscreenCanvas with WebGPU,
// because a canvas can be handed over once.
async function hello(){
  let surfaceOk=false;
  try{
    const transport=await import('../html-webgpu/runtime/gpu-transport.mjs');
    surfaceOk=inWorker&&typeof transport.createSurfaceSession==='function'&&typeof OffscreenCanvas==='function'
      &&!!navigator.gpu&&!!new OffscreenCanvas(1,1).getContext('webgpu');
  }catch{surfaceOk=false;}
  post({type:'caps',surface:surfaceOk});
}
async function start(data){
  ({width,height,scale}=data);
  checkMode=data.check===true;statsMode=data.stats===true;
  if(!navigator.gpu)throw Error('This browser does not provide WebGPU.');
  const [{default:createModule},transport]=await Promise.all([
    import('../html-webgpu/runtime/web-render.mjs'),import('../html-webgpu/runtime/gpu-transport.mjs')]);
  module=await createModule();createSession=transport.createOffscreenSession;hashPixels=transport.hashPixels;
  if(data.canvas&&typeof transport.createSurfaceSession==='function'){surfaceCanvas=data.canvas;createSurface=transport.createSurfaceSession;}
  await loadFont();
  home=await prepare(homeURL);
  history=push({entries:[],index:0},homeURL);doc=home;field=showURL(home.url);tabs.push({doc,history,scroll:0});
  // The page keeps the keys of Lean's table for a host with no menu, and needs them at once.
  // An engine from before these ops (issue 1268) has no key table and no address edits.
  try{post({type:'keys',table:call('',{op:'keyTable',platform:data.platform==='mac'?'mac':'other'})});}catch{/* older engine */}
  ready=true;
  openState().catch(error=>{stateReason=String(error.message??error);});
  // A new window starts in the address bar with the address selected (issue 1268).
  if(data.page&&/^[a-z0-9-]+\.(html|xml)$/.test(data.page))navigate(pagesBase+data.page);
  else if(data.page==='sparql')navigate(sparqlURL);
  else if(data.page==='wasm'||/^wasm\/[a-z0-9-]+\.wasm(#[A-Za-z0-9_-]+)?$/.test(data.page??''))navigate('foafnaut:'+data.page);
  else focusAddress();
  for(const message of early.splice(0))receive(message);
}
function flush(){
  const move=pendingMove,scrolled=pendingScroll;pendingMove=pendingScroll=undefined;
  if(move)handle(move);
  if(scrolled)handle(scrolled);
}
function receive(data){
  if(data.type==='hello'){hello();return;}
  if(data.type==='start'){start(data).catch(error=>post({type:'error',error:String(error.message??error)}));return;}
  if(!ready){early.push(data);return;}
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
  if(data.type==='resize'){({width,height,scale}=data);if(doc.graph)graphInput(1,width,height);request();}
  if(data.type==='scroll')scrollBy(data.amount);
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
    const target=hit(data.x,data.y);
    if(target?.href){
      const answer=call('',{op:'shellLink',href:target.href});
      if(answer.go==='page')go({go:'page',url:new URL(target.href,doc.baseURL||doc.url).href});else go(answer);
    }
  }
  if(data.type==='text'&&focused){const {clipboard:_,...next}=call('',{op:'shellText',shell:shell(),text:data.text});field=next;request();}
  if(data.type==='key'&&focused){
    if(data.key===36){const target=field.address;leaveAddress();go(call('',{op:'shellSubmit',address:target}));}
    else if(data.key===53)leaveAddress();
    else{field=call('',{op:'shellKey',shell:shell(),key:data.key,modifiers:data.modifiers??0});request();}
  }
}
if(inWorker)self.onmessage=({data})=>receive(data);
/** Start the loop on this thread. Returns the function that takes input messages. */
export function onThisThread(deliver){post=message=>deliver({data:message});return receive;}
