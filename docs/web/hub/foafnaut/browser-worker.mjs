// The browser loop for a web page. It matches run_html.ts, the native loop: the
// shell, history and every decision are Lean values and Lean calls.
// It runs in a worker, or on the page's own thread where a worker can not start:
// an iframe sandbox without allow-same-origin has an opaque origin, and the worker
// constructor refuses that (Foafos guests). `post` is the only way out of the loop.
let post=(message,transfer)=>self.postMessage(message,transfer);
// Page scripts (issue 1271): the same session and runtime as the desktop window, with the
// QuickJS-NG reactor and the Lean module of this site's runtime directory.
import {createScriptSession} from './script-engine/session.mjs';
import {createPageScripts} from './script-engine/page-scripts.mjs';
import {verifiedJSAvailable} from './script-engine/verifiedjs/adapter.mjs';
const runtimeBase=new URL('../html-webgpu/runtime/',import.meta.url);
let scriptSetting='quickjs',scriptNote='';
const inWorker=typeof WorkerGlobalScope!=='undefined'&&self instanceof WorkerGlobalScope;
const pagesBase=new URL('./pages/',import.meta.url).href,siteOrigin=new URL(import.meta.url).origin;
const homeURL=pagesBase+'index.html',settingsURL=pagesBase+'settings.html';
let module,createSession,session,createSurface,hashPixels,surface,surfaceCanvas,checkMode=false,statsMode=false;
// Input that arrives before the engine is ready, and moves and scrolls that arrive while a
// frame builds, wait here. Every press, release, key, text and command is applied in the
// order it arrived; only moves and scrolls are merged.
let ready=false,currentStamp,pendingStamp,pendingMove,pendingScroll,flushPort;
const early=[];
let width=800,height=600,scale=1,theme='next',percent=150,pages=1;
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
  canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll,script:doc?.script?.marker||scriptNote});
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
function fontLoad(bytes,family,sha,fallback=false){
  if(typeof module._web_document_font_call_bin!=='function'||typeof module._malloc!=='function'){
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
  // Only an engine that holds several fonts answers with `fonts` (the count held). An engine
  // with the bytes call but no fallback argument would replace Noto Sans with the fallback
  // font: on 2026-11-07 the published engine did, and Latin text on the Hub page broke.
  if(typeof primary?.fonts!=='number')return;
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
  const prepared={url:page.url,title:facts.title,baseURL:facts.baseURL,source:page.source,sources};
  // Lean lists the classic scripts; this host fetches the bytes of an external one.
  const classic=(facts.scripts??[]).filter(script=>script.kind==='classic');
  if(classic.length){
    const texts=[];
    for(const script of classic){
      if(!script.src){texts.push(script.source);continue;}
      const fetched=await fetchText(script.url);texts.push(fetched.source);sources.push({kind:'Script',url:fetched.url,source:fetched.source});
    }
    prepared.script={sources:texts,nodes:facts.nodes??[],next:facts.next??0,commands:[],notice:'',marker:''};
    await startScripts(prepared);
  }
  return prepared;
}
// Lean says what the setting means for the page; an engine that can not start refuses the
// page, and one that fails later has stopped. Either way the page and the chrome say why.
let scriptWaiters=[];
async function startScripts(page){
  const script=page.script;
  let plan;
  try{plan=call('',{op:'scriptPlan',setting:scriptSetting,scripts:script.sources.length});}
  catch{post({type:'note',text:'This engine build has no page scripts; the scripts of this page did not run.'});return;}
  const unavailable=plan.run&&plan.engine==='verifiedjs'?verifiedJSAvailable():'';
  if(unavailable)plan=call('',{op:'scriptPlan',setting:scriptSetting,scripts:script.sources.length,unavailable});
  script.marker=plan.marker;script.notice=plan.notice;
  if(!plan.run)return;
  let starting=true;
  const session=createScriptSession({wasmURL:new URL('qjs-wasi-reactor.wasm',runtimeBase).href,leanModuleURL:new URL('web-render.mjs',runtimeBase).href});
  const runtime=createPageScripts({session,
    compact:async commands=>call(page.source,{op:'compactCommands',url:page.url,commands}).commands,
    onBatch:(batch,kind)=>{
      script.commands=runtime.commands;
      for(const value of batch.errors)console.warn('foafnaut page script:',value);
      if(kind==='start'||!batch.commands.length)return Promise.resolve();
      if(page!==doc)return new Promise(resolve=>setTimeout(resolve,1000));
      return new Promise(resolve=>{scriptWaiters.push(resolve);request();});
    },
    onStop:reason=>{
      const stop=call('',{op:'scriptPlan',setting:scriptSetting,scripts:script.sources.length,...(starting?{unavailable:reason}:{failure:reason})});
      script.marker=stop.marker;script.notice=stop.notice;if(page===doc)request();
    }});
  script.runtime=runtime;
  try{await runtime.start({nodes:script.nodes,next:script.next,sources:script.sources,budgetMs:200,document:{source:page.source,url:page.url,commands:[]}});}
  catch{/* onStop put the reason on the page */}
  finally{starting=false;}
}
const scripted=page=>({...(page?.script?.commands.length?{commands:page.script.commands}:{}),...(page?.script?.notice?{scriptNotice:page.script.notice}:{})});
const runtimeOf=page=>page?.script?.runtime&&!page.script.runtime.stopped?page.script.runtime:undefined;
// The element a click goes to: Lean's hit test over the boxes of the elements with a click
// listener, in document rows (the frame is composed under the chrome).
function scriptTarget(runtime,x,y){
  const ids=new Set(runtime.listeners.filter(l=>l.type==='click').map(l=>l.nodeId));
  const boxes=(frame?.webRender.boxes??[]).filter(box=>ids.has(box[0]));
  if(boxes.length){
    const top=call('',{op:'shellHeight',shell:shell(),width}).height;
    const rows=boxes.map(([id,bx,by,bw,bh])=>[id,'',bx,by,bw,bh]);
    const bottom=Math.max(1,...boxes.map(b=>Math.ceil(b[2]+b[4])+1));
    const pointer=module.ccall('web_render_hit','number',['string','number','number','number','number'],[JSON.stringify(rows),frame.width,bottom,x,y-top+scroll]);
    try{const hit=JSON.parse(module.UTF8ToString(pointer));if(hit?.sourceNode!==undefined)return hit.sourceNode;}
    finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  }
  return runtime.documentListeners.includes('click')?null:undefined;
}
function retire(page){if(page&&page!==doc&&!tabs.some(tab=>tab.doc===page))runtimeOf(page)?.stop('the page was closed');}
function show(next,remember=true){
  const previous=doc;scriptNote='';
  doc=next;retire(previous);if(!focused)field=showURL(next.url);scroll=0;loading=false;
  if(remember){history=push(history.history,next.url);pages++;}
  request();
}
async function navigate(url,remember=true){
  const mine=++serial;loading=true;request();
  const stamp=currentStamp;
  let next;try{next=await prepare(url);}catch(error){next=refusal(url,String(error.message??error));}
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
  if(answer.textScalePercent!==percent){percent=answer.textScalePercent;request();}
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
  else if(name==='theme'){theme=argument||(theme==='next'?'arcade':'next');request();}
  else if(name==='zoom'&&/^[0-9]+$/.test(argument)){percent=Math.max(50,Number(argument));request();}
  // The page script setting (issue 1271): pages opened from now on use it.
  else if(name==='scripts'){
    try{scriptSetting=call('',{op:'scriptSetting',setting:argument}).setting;scriptNote=call('',{op:'scriptPlan',setting:scriptSetting,scripts:1}).marker;request();}
    catch(error){post({type:'error',error:String(error.message??error)});}
  }
  else navigate(settingsURL);
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
      const next=render(doc.source,{op:'render',url:doc.url,...scripted(doc),textScalePercent:percent,shell:shell(),live:doc===checked,binary:true},width,height);
      const shown=scriptWaiters;scriptWaiters=[];
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
      for(const resolve of shown)resolve();
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
  // A new window starts in the address bar with the address selected (issue 1268).
  if(data.page&&/^[a-z0-9-]+\.(html|xml)$/.test(data.page))navigate(pagesBase+data.page);else focusAddress();
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
    // A click on an element with a script listener is a script turn first (issue 1271).
    const runtime=runtimeOf(doc),node=runtime?scriptTarget(runtime,data.x,data.y):undefined;
    if(runtime&&node!==undefined){
      const page=doc;
      runtime.dispatch({type:'click',nodeId:node??undefined}).then(batch=>{
        if(!batch.defaultPrevented&&target?.href&&page===doc){const answer=call('',{op:'shellLink',href:target.href});
          if(answer.go==='page')go({go:'page',url:new URL(target.href,doc.baseURL||doc.url).href});else go(answer);}
      }).catch(()=>{});
      return;
    }
    if(target?.href){
      const answer=call('',{op:'shellLink',href:target.href});
      if(answer.go==='page')go({go:'page',url:new URL(target.href,doc.baseURL||doc.url).href});else go(answer);
    }
  }
  // Keys to the page's scripts when the address bar does not have the focus.
  if(data.type==='pagekey'&&!focused){const runtime=runtimeOf(doc);if(runtime?.documentListeners.includes('keydown'))runtime.dispatch({type:'keydown',key:String(data.key)}).catch(()=>{});}
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
