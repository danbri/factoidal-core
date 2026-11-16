// engine-core.mjs: one instance of the built-in engine (BubblePopKit, web-render.wasm) for the
// Hub's Textnaut page and the notebook's cells. It lays a page out, draws it (WebGPU, or the
// engine's own CPU pixels when there is no GPU), maps it to Textnaut's text grid, follows links
// and runs page scripts on BubblePopJS. Every decision about the page is the engine's: this file
// moves bytes between the engine, the network of this site and the GPU, as the Foafnaut Hub
// host (../foafnaut/browser-worker.mjs) does, with the same shared steps (../foafnaut/page-load.mjs).
//
// It has no DOM and no worker API, so the same code runs in the page's worker
// (engine-worker.mjs) and in the Node tests (tests/hub/textnaut_engine_test.mjs).
//
// Pages: this site only. The Hub has no fetch proxy, so a URL of another site is refused with a
// reason; pasted or typed HTML is laid out as a page of the address it is given (the notebook's).
import {loadStyleSheets,loadImports,pageLayoutFields} from '../foafnaut/page-load.mjs';

/** Bounds on page-controlled work in one call: the page source, views held, script turns. */
export const LIMITS=Object.freeze({imageBytes:4194304,pageImageBytes:6291456,sourceBytes:4*1048576,views:24,settleTurns:8,settleMs:1000,netAnswers:16,width:4096,height:4096});

const round=x=>Math.round(x*10)/10;
const textDecoder=new TextDecoder();

/** Whether an input is a URL to load or markup to lay out. A string that starts with `<` is
markup; one that names a scheme, or starts with `/`, `./` or `../`, or is a bare `name.html`, is
an address. `{url}` and `{html, url?}` say which they are. */
export function classifyInput(input,base){
  if(input&&typeof input==='object'){
    if(typeof input.html==='string')return {html:input.html,url:input.url?new URL(input.url,base).href:base};
    if(typeof input.url==='string')return {url:new URL(input.url,base).href};
    throw Error('give a URL or HTML: {url} or {html}');
  }
  if(typeof input!=='string')throw Error('give a URL or HTML as a string');
  const text=input.trim();
  if(text.startsWith('<')||!text)return {html:input,url:base};
  if(/^[a-z][a-z0-9+.-]*:/i.test(text)||/^(\.{0,2}\/)/.test(text)||/^[\w.-]+\.(html?|xml|svg)([?#].*)?$/i.test(text))return {url:new URL(text,base).href};
  return {html:input,url:base};
}

/** The engine answer of a render as bytes (WebDocument.packAnswer): a JSON head and the storage
floats, tile words and CPU pixels as raw sections. */
export function decodePacked(buffer){
  const view=new DataView(buffer),headSize=view.getUint32(4,true),count=view.getUint32(8,true);
  let offset=12+4*count;
  const frame=JSON.parse(textDecoder.decode(new Uint8Array(buffer,offset,headSize)));
  if(frame?.error)throw Error(frame.error);
  offset+=headSize;
  const sections=[];
  for(let i=0;i<count;i++){const length=view.getUint32(12+4*i,true);sections.push([offset,length]);offset+=(length+3)&~3;}
  for(const scene of [frame,frame.page,frame.chrome]){
    if(!scene||typeof scene!=='object')continue;
    if(typeof scene.dataSection==='number'){const [o,l]=sections[scene.dataSection];scene.data=new Float32Array(buffer,o,l/4);delete scene.dataSection;}
    if(typeof scene.tilesSection==='number'){const [o,l]=sections[scene.tilesSection];scene.tiles=new Uint32Array(buffer,o,l/4);delete scene.tilesSection;}
    if(typeof scene.pixelsSection==='number'){const [o,l]=sections[scene.pixelsSection];scene.pixels=new Uint8Array(buffer,o,l);delete scene.pixelsSection;}
  }
  return frame;
}

/** The text grid's viewport for `cols` columns (as textnaut.ts pageViewport): one cell is one
character of the body text, `charWidth` CSS pixels wide. */
export function gridViewport(cols,charWidth,grid){
  const c=Math.max(10,Math.min(400,Math.floor(cols))),cellWidth=Math.min(charWidth,4080/c);
  return {cols:c,cellWidth,cellHeight:charWidth*grid.CELL_HEIGHT/grid.CELL_WIDTH,width:Math.round(c*cellWidth+16)};
}

/**
 * The engine for one page of the Hub. `host`:
 * - `createModule(options)`: the Emscripten loader of web-render.mjs;
 * - `compiled`: a promise of the compiled WebAssembly module, or undefined (the loader fetches it);
 * - `fetchBytes(url)`: `{url, bytes, contentType}` of a URL of this site, or a throw;
 * - `origin`: this site's origin; only its URLs are read, and with `copies` true also the
 *   addresses of other sites that `fetchBytes` answers from the Hub's copies (copies.mjs);
 * - `fontURL`: the default face (Noto Sans), or undefined for the engine's bitmap face;
 * - `gpu()`: a promise of `{draw(artifact) -> {rgba, gpuMs}}`, or of undefined with no WebGPU;
 * - `grid()`: a promise of the grid module (grid.mjs, made from textnaut/grid.ts).
 */
export function createEngineCore(host){
  // The engine holds one script session: a scripted view that is not the current one starts its
  // page's scripts again when it is used (its script state is that of a new load).
  let module,starting,gpu,cpuMode=false,fontBytesFallback=false,scriptEngines=[],currentSession;
  const views=new Map();
  const counters={engineMs:0,fontMs:0,calls:0,renders:0};
  const now=()=>performance.now();

  function call(source,options,w=1,h=1){
    counters.calls++;
    const pointer=module.ccall('web_document_call','number',['string','string','number','number'],[source,JSON.stringify(options),w,h]);
    if(!pointer)throw Error('engine allocation failed');
    try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
    finally{module.ccall('web_render_free',null,['number'],[pointer]);}
  }
  function render(source,options,w,h,pixels=true){
    counters.renders++;counters.calls++;
    if(cpuMode&&pixels)options={...options,cpu:true};
    if(typeof module._web_document_call_bin!=='function'){
      const frame=call(source,options,w,h);
      if(Array.isArray(frame.data))frame.data=Float32Array.from(frame.data);
      return frame;
    }
    const pointer=module.ccall('web_document_call_bin','number',['string','string','number','number','number'],[source,JSON.stringify({...options,binary:true}),w,h,0]);
    if(!pointer)throw Error('engine allocation failed');
    let buffer;
    try{const heap=module.HEAPU8;buffer=heap.slice(pointer,pointer+new DataView(heap.buffer,pointer,4).getUint32(0,true)).buffer;}
    finally{module.ccall('web_render_free',null,['number'],[pointer]);}
    return decodePacked(buffer);
  }
  function fontLoad(bytes,family,sha){
    if(fontBytesFallback&&typeof module._web_document_font_call_bin==='function'&&typeof module._malloc==='function'){
      const input=module._malloc(Math.max(1,bytes.length));
      try{
        module.HEAPU8.set(bytes,input);
        const pointer=module.ccall('web_document_font_call_bin','number',['number','number','string','string','number'],[input,bytes.length,family,sha,0]);
        try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
        finally{module.ccall('web_render_free',null,['number'],[pointer]);}
      }finally{module._free(input);}
    }
    let text='';for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
    return call('',{op:'fontLoad',fontBase64:btoa(text),fontFamily:family,fontSha256:sha});
  }
  // Images (as the Foafnaut Hub host): the engine lists them by key; this site's are fetched,
  // within the size caps, and held by the engine by SHA-256 (op imageLoad, issue 1292).
  function imageLoad(bytes,key,sha){
    if(typeof module._web_document_image_call_bin!=='function'||typeof module._malloc!=='function'){
      let text='';for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
      return call('',{op:'imageLoad',key,sha256:sha,imageBase64:btoa(text)});
    }
    const input=module._malloc(Math.max(1,bytes.length));
    if(!input)throw Error('engine allocation failed');
    try{
      module.HEAPU8.set(bytes,input);
      const pointer=module.ccall('web_document_image_call_bin','number',['number','number','string','string'],[input,bytes.length,key,sha]);
      if(!pointer)throw Error('engine allocation failed');
      try{const result=JSON.parse(module.UTF8ToString(pointer));if(result?.error)throw Error(result.error);return result;}
      finally{module.ccall('web_render_free',null,['number'],[pointer]);}
    }finally{module._free(input);}
  }
  let holdsImages;
  async function pageImages(wanted){
    holdsImages??=(()=>{try{return (call('',{op:'imageInfo'}).ops??[]).includes('imageLoad');}catch{return false;}})();
    if(!holdsImages||!wanted?.length)return [];
    const held=[];let total=0;
    for(const {key,url} of wanted){
      try{
        if(new URL(url).origin!==host.origin&&!host.copies)continue;
        const {bytes}=await host.fetchBytes(url);
        if(bytes.length>LIMITS.imageBytes||total+bytes.length>LIMITS.pageImageBytes)continue;
        total+=bytes.length;
        const sha=await hex(bytes);
        imageLoad(bytes,key,sha);held.push({key,sha256:sha});
      }catch{/* the image is left out and its alt text shows */}
    }
    return held;
  }
  const hex=async bytes=>[...new Uint8Array(await crypto.subtle.digest('SHA-256',bytes))].map(b=>b.toString(16).padStart(2,'0')).join('');

  /** Start the engine once: the module, the default face, and whether the GPU draws. */
  function ready(){
    return starting??=(async()=>{
      const t0=now();
      const compiled=await host.compiled?.catch(()=>undefined);
      const options=compiled?{instantiateWasm(imports,done){
        WebAssembly.instantiate(compiled,imports).then(instance=>{
          if(instance.exports.web_document_font_call_bin?.length===5)fontBytesFallback=true;
          done(instance,compiled);});return {};}}:{};
      module=await host.createModule(options);
      counters.engineMs=round(now()-t0);
      const t1=now();
      if(host.fontURL){
        try{const {bytes}=await host.fetchBytes(host.fontURL);const answer=fontLoad(bytes,'Noto Sans',await hex(bytes));if(typeof answer?.fonts==='number')fontBytesFallback=true;}
        catch(error){counters.fontNote=`bitmap face: ${String(error.message??error)}`;}
      }
      counters.fontMs=round(now()-t1);
      try{scriptEngines=call('',{op:'scriptSession',action:'info'}).engines??[];}catch{scriptEngines=[];}
      gpu=await host.gpu?.().catch(()=>undefined);
      if(!gpu){try{cpuMode=call('',{op:'cpuInfo'}).engine==='cpu';}catch{cpuMode=false;}}
      return {...counters,drawing:gpu?'gpu':cpuMode?'cpu':'none',scriptEngines:[...scriptEngines]};
    })();
  }

  const siteOnly=url=>{
    const u=new URL(url);
    if(!/^https?:$/.test(u.protocol))throw Error(`${u.href}: not a web address; open it in Foafnaut`);
    if(u.origin!==host.origin&&!host.copies)throw Error(`${u.origin} is another site: the Hub reads pages of this site only (it has no fetch proxy)`);
    return u.href;
  };
  const siteText=async url=>{const got=await host.fetchBytes(siteOnly(url));return {url:got.url??url,source:textDecoder.decode(got.bytes)};};

  /** A page: its source and what the engine asked for (sheets, imports), and its scripts. */
  async function prepare(input,base){
    const t0=now(),given=classifyInput(input,base);
    let page;
    if(given.html!==undefined)page={url:given.url,source:given.html,given:'html'};
    else{const got=await siteText(given.url);page={url:got.url,source:got.source,given:'url'};}
    if(new TextEncoder().encode(page.source).length>LIMITS.sourceBytes)throw Error(`the page is larger than ${LIMITS.sourceBytes} bytes`);
    page.liberal=true;
    const facts=call(page.source,{op:'inspect',url:page.url,liberal:true});
    const sheets=await loadStyleSheets(facts.stylesheets,siteText);
    const imported=await loadImports(list=>call(page.source,{op:'inspect',url:page.url,liberal:true,
      ...(sheets.resources.length?{resources:sheets.resources}:{}),...(list.length?{imported:list}:{})}),siteText,[]);
    if(sheets.resources.length)page.resources=sheets.resources;
    if(sheets.resourceFailures.length)page.resourceFailures=sheets.resourceFailures;
    if(imported.length)page.imported=imported;
    const heldImages=await pageImages(facts.images);
    if(heldImages.length)page.heldImages=heldImages;
    page.title=facts.title??'';page.baseURL=facts.baseURL??page.url;
    page.scripts=(facts.scripts??[]).filter(s=>s.kind==='classic');
    page.prepareMs=round(now()-t0);
    return page;
  }

  /** Run the page's classic scripts on BubblePopJS, then let it settle: its timers, at most
  `LIMITS.settleTurns` turns and `LIMITS.settleMs` of page time (as Textnaut's settle). */
  async function startScripts(page,width,height,scale){
    if(!page.scripts.length||!scriptEngines.includes('bubblepop'))return;
    const t0=now(),resources=[];
    for(const s of page.scripts)if(s.src){try{resources.push({nodeId:s.nodeId,source:(await siteText(s.url)).source});}catch{/* the engine runs the page without it */}}
    let turn=call(page.source,{op:'scriptSession',action:'start',url:page.url,resources,width,height,engine:'bubblepop',
      layout:{...pageLayoutFields({...page,commands:undefined}),textScalePercent:100*scale,zoomUnit:100*scale},zoomUnit:100*scale});
    page.script={session:turn.session,turns:1,logs:[],errors:[],size:[width,height,scale]};currentSession=turn.session;
    take(page,turn);
    let budget=LIMITS.settleMs;
    for(let i=0;i<LIMITS.settleTurns&&turn.nextWake!==null&&turn.nextWake!==undefined;i++){
      const ms=Math.max(0,Math.ceil(turn.nextWake-turn.clock));
      if(ms>budget)break;
      budget-=ms;
      turn=call('',{op:'scriptSession',action:'advance',session:page.script.session,ms});
      take(page,turn);
    }
    page.scriptMs=round(now()-t0);
  }
  function take(page,turn){
    if(!page.script)return;
    page.script.turns++;
    page.script.logs.push(...(turn.logs??[]).slice(0,50));page.script.errors.push(...(turn.errors??[]).slice(0,50));
    page.script.logs.length=Math.min(page.script.logs.length,200);page.script.errors.length=Math.min(page.script.errors.length,200);
    if(turn.changed&&turn.commands)page.commands=turn.commands;
  }

  function layoutOptions(page,scale){
    return {op:'render',checks:false,...pageLayoutFields(page),textScalePercent:100*scale,zoomUnit:100*scale};
  }
  /** Lay the page out at `width` CSS pixels; with `autoHeight`, as tall as its content (to `maxHeight`). */
  function layOut(page,width,height,scale,autoHeight,maxHeight){
    const w=Math.max(1,Math.min(LIMITS.width,Math.round(width*scale)));
    let h=Math.max(1,Math.min(LIMITS.height,Math.round(height*scale)));
    const t0=now();
    let frame=render(page.source,layoutOptions(page,scale),w,h),layouts=1;
    if(autoHeight){
      const content=Math.ceil(frame.webRender?.boxes?.[0]?.[4]??0);
      const want=Math.max(Math.round(40*scale),Math.min(Math.round(maxHeight*scale),LIMITS.height,content));
      if(want!==h){h=want;frame=render(page.source,layoutOptions(page,scale),w,h);layouts++;}
    }
    return {frame,layoutMs:round(now()-t0),layouts};
  }
  const frameWork=()=>{try{return call('',{op:'frameWork'});}catch{return undefined;}};

  function viewOf(id){const view=views.get(id);if(!view)throw Error(`no view ${id}`);return view;}
  function keep(id,view){
    views.delete(id);views.set(id,view);
    while(views.size>LIMITS.views){const [old,v]=views.entries().next().value;views.delete(old);closeScripts(v.page);}
  }
  function closeScripts(page){
    if(!page?.script)return;
    if(page.script.session===currentSession){try{call('',{op:'scriptSession',action:'close',session:page.script.session});}catch{}currentSession=undefined;}
    page.script=undefined;
  }

  /** Open `input` in view `id` and draw it. `options`: width, height (CSS px), scale (device
  pixels per CSS pixel), autoHeight, maxHeight, scripts (run them on BubblePopJS), draw (pixels
  or not), base (the address that relative URLs and pasted HTML belong to). */
  async function open(id,input,options={}){
    const t0=now(),start=await ready(),fresh=counters.used===undefined;
    counters.used??=true;
    const scale=Math.max(1,Math.min(3,options.scale??1));
    const before=frameWork();
    closeScripts(views.get(id)?.page);
    const page=await prepare(input,options.base??host.origin+'/');
    const width=options.width??640,height=options.height??400;
    if(options.scripts)await startScripts(page,Math.round(width*scale),Math.round(height*scale),scale);
    const view={page,options:{...options,scale,width,height}};
    keep(id,view);
    const out=await paint(view,before);
    out.timing={...out.timing,prepareMs:page.prepareMs,...(page.scriptMs!==undefined?{scriptMs:page.scriptMs}:{}),
      totalMs:round(now()-t0),...(fresh?{engineMs:start.engineMs,fontMs:start.fontMs}:{})};
    return out;
  }
  async function paint(view,before=frameWork()){
    const {page,options}=view,{scale,width,height}=options;
    const laid=layOut(page,width,height,scale,options.autoHeight!==false,options.maxHeight??2400);
    view.frame=laid.frame;
    const after=frameWork();
    const artifact=laid.frame;
    const out={url:page.url,title:page.title,given:page.given,width:artifact.width,height:artifact.height,scale,
      timing:{layoutMs:laid.layoutMs},
      counters:{layouts:laid.layouts,engineLayouts:after&&before?after.layouts-before.layouts:undefined,kept:after&&before?after.kept-before.kept:undefined,
        primitives:artifact.primitiveCount??0,glyphRuns:artifact.webRender?.glyphRuns?.length??0,links:artifact.webRender?.links?.length??0,
        sceneBytes:(artifact.data?.length??0)*4+(artifact.tiles?.length??0)*4},
      links:(artifact.webRender?.links??[]).map(([node,href,x,y,w,h])=>({node,href,x:x/scale,y:y/scale,w:w/scale,h:h/scale})),
      ...(page.script?{scripts:{engine:'bubblepop',turns:page.script.turns,logs:page.script.logs.slice(-20),errors:page.script.errors.slice(-20)}}:{})};
    if(options.draw!==false){
      const t0=now();
      if(artifact.pixels instanceof Uint8Array){out.rgba=artifact.pixels.slice();out.drawing='cpu';}
      else if(gpu){const drawn=await gpu.draw(artifact);out.rgba=drawn.rgba;out.drawing='gpu';if(drawn.gpuMs!==undefined)out.timing.gpuMs=round(drawn.gpuMs);}
      else out.drawing='none';
      out.timing.drawMs=round(now()-t0);
    }
    return out;
  }

  /** Open `input` in view `id` as Textnaut's text grid of `cols` columns. */
  async function textGrid(id,input,options={}){
    const t0=now(),start=await ready(),fresh=counters.used===undefined;counters.used??=true;
    const grid=await host.grid();
    closeScripts(views.get(id)?.page);
    const page=await prepare(input,options.base??host.origin+'/');
    const view={page,options:{...options,scale:1,grid:true}};
    if(options.scripts)await startScripts(page,Math.round(gridViewport(options.cols??80,grid.CELL_WIDTH,grid).width),options.height??600,1);
    keep(id,view);
    const out=gridOf(view,grid);
    out.timing={...out.timing,prepareMs:page.prepareMs,...(page.scriptMs!==undefined?{scriptMs:page.scriptMs}:{}),totalMs:round(now()-t0),
      ...(fresh?{engineMs:start.engineMs,fontMs:start.fontMs}:{})};
    return out;
  }
  function gridOf(view,grid){
    const {page,options}=view,cols=options.cols??80;
    const before=frameWork(),t0=now();
    const compile=charWidth=>{const v=gridViewport(cols,charWidth,grid);return {v,frame:render(page.source,layoutOptions(page,1),v.width,Math.max(240,options.height??600),false)};};
    let charWidth=grid.CELL_WIDTH,{v,frame}=compile(charWidth),layouts=1;
    // One cell is one character of the body text: a page whose body is not 16 px is laid out again (textnaut.ts layoutDoc).
    const measured=grid.bodySize(frame.webRender.glyphRuns)*grid.CELL_WIDTH/16;
    if(Math.abs(measured-charWidth)>0.5){charWidth=measured;({v,frame}=compile(charWidth));layouts++;}
    const t1=now();
    const g=grid.layoutGrid({runs:frame.webRender.glyphRuns,links:frame.webRender.links,cols:v.cols,cellWidth:v.cellWidth,cellHeight:v.cellHeight,trimLeft:true,
      paint:grid.readPaint(frame),boxes:frame.webRender.boxes,resolve:href=>new URL(href,page.baseURL).href});
    const t2=now(),after=frameWork();
    view.frame=frame;view.grid=g;view.gridWidth=v.width;
    return {url:page.url,title:page.title,given:page.given,grid:g,text:grid.dumpText(g),
      timing:{layoutMs:round(t1-t0),cellsMs:round(t2-t1)},
      counters:{layouts,engineLayouts:after&&before?after.layouts-before.layouts:undefined,primitives:frame.primitiveCount??0,glyphRuns:frame.webRender.glyphRuns.length,
        links:g.targets.length,rows:g.rows.length,cols:g.cols},
      ...(page.script?{scripts:{engine:'bubblepop',turns:page.script.turns,logs:page.script.logs.slice(-20),errors:page.script.errors.slice(-20)}}:{})};
  }

  /** The link at (x, y) CSS pixels of view `id`, as the engine's link rows place it. */
  function linkAt(id,x,y){
    const view=viewOf(id),s=view.options.scale??1;
    const links=view.frame?.webRender?.links??[];
    for(const [node,href,lx,ly,w,h] of links)if(x*s>=lx&&x*s<=lx+w&&y*s>=ly&&y*s<=ly+h)
      return {node,href,url:new URL(href,view.page.baseURL).href};
    return null;
  }
  /** A click at (x, y): to the page's scripts (the engine finds the node), then, if the page did
  not change and the point is on a link, the link's URL to follow. */
  async function click(id,x,y){
    const view=viewOf(id),{page,options}=view,s=options.scale??1;
    if(page.script&&page.script.session!==currentSession){
      const [w,h,sc]=page.script.size;page.script=undefined;page.commands=undefined;
      await startScripts(page,w,h,sc);
      view.frame=layOut(page,options.width,options.height,s,options.autoHeight!==false,options.maxHeight??2400).frame;
    }
    if(page.script){
      const at=call(page.source,{op:'nodeAt',...pageLayoutFields(page),textScalePercent:100*s,zoomUnit:100*s,x:Math.round(x*s),y:Math.round(y*s)},view.frame.width,view.frame.height);
      if(typeof at.node==='number'){
        const turn=call('',{op:'scriptSession',action:'click',session:page.script.session,node:at.node});
        take(page,turn);
        if(turn.changed&&turn.commands)return {changed:true,frame:await paint(view)};
      }
    }
    return {changed:false,link:linkAt(id,x,y)};
  }
  /** Check view `id`'s text grid against the engine's own pixels of the same page (its CPU
  drawing, as tall as the content up to 4096 px): every cell with a background must have that
  colour painted under it (grid.mjs backgroundMismatches). */
  async function gridCheck(id){
    const view=viewOf(id),grid=await host.grid();
    if(!view.grid)throw Error(`view ${id} is not a text grid`);
    const content=Math.ceil(view.frame?.webRender?.boxes?.[0]?.[4]??600);
    const h=Math.max(240,Math.min(LIMITS.height,content));
    const frame=render(view.page.source,{...layoutOptions(view.page,1),cpu:true},view.gridWidth,h,false);
    if(!(frame.pixels instanceof Uint8Array))return {available:false};
    const found=grid.backgroundMismatches(view.grid,frame.pixels,frame.width,frame.height);
    const coloured=view.grid.rows.reduce((n,row)=>n+row.filter(c=>c.bg).length,0);
    return {available:true,coloured,checked:found.checked,mismatches:found.mismatches.length,examples:found.mismatches.slice(0,5)};
  }
  function close(id){const view=views.get(id);if(view){closeScripts(view.page);views.delete(id);}}
  return {ready,open,textGrid,gridCheck,linkAt,click,close,counters,get views(){return views.size;}};
}
