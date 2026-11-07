import {loadHTML,type HTMLArtifact,type HTMLLayers,type HistoryAnswer,type ShellEdit} from "./native_html_engine.ts";
import {printImages,pdfPageCount,DEFAULT_PAPER} from "./native_print.ts";
import {clampOffset,keeps} from "./layer_compositor.ts";
import {prefetchTarget,trackMotion,stateKey,sameState,canSwap,keepReach,PREFETCH_MARGIN_ROWS,FRAME_MS,type Motion,type StateKey} from "./scroll_prefetch.ts";
import {inputURL,navigationURL,loadFontFile,prepareHTML,refusalHTML,type PageView} from "./native_html_document.ts";
import {loadNativeWindow} from "./native_window.ts";
import {nativePreflight} from "./native_preflight.ts";
import {cocoaSurfaceOptions} from "./cocoa_surface.ts";
import {createHTMLWindowSession} from "./native_html_session.ts";
import {cleanupUI} from "./ui_cleanup.ts";
import {requestRenderPlan} from "./render_plan.ts";
import {startCompileWorker,type CompileClient} from "./native_html_compile.ts";
import type {UIEvent} from "./ui_engine.ts";

async function main() {
  const args=[...Deno.args];
  if(args.includes("--help")){
    console.log("Native HTML: --html FILE | --url HTTP_OR_HTTPS_URL [--font FONT_FILE] [--bitmap-font] [--follow-links] [--check-engine] [--trace-input] [--resize-sweep] [--command-sweep] [--history-sweep] [--back-sweep] [--graph-sweep] [--edit-sweep] [--print-pdf FILE] [--scroll-sweep] [--single-frame] [--check-pixels] [--perf-summary] [--idle-checks-only] [--native-engine DYLIB | --wasm-engine]\nCommand-Q quits; R reloads; Command-Left and Command-[ go back; Command-Right and Command-] go forward; Command-= and Command-- zoom text; Command-0 resets; drag selects; Command-A, Command-C, Command-X, Command-V and Command-Z edit the address bar when it has the focus, else select and copy page text; Command-P prints. HTML/CSS/layout/link picking run in published Lean WASM. No scripts, scrolling, WebView or supplied fonts in this milestone.");return;
  }
  let url:string|undefined,follow=false,check=false,traceInput=false,sweep:number[][]|undefined,commands:(string|number[])[]|undefined,pasted:string|undefined,bitmapFont=false,fontFile:string|undefined,checkAll=false,idleChecksOnly=false,perfSummary=false,nativeEngine:string|undefined,wasmEngine=false,layered=true,pressLook=true,printPDF:string|undefined;
  while(args.length){const arg=args.shift();
    if(arg==="--html"||arg==="--url"){
      const value=args.shift();if(!value||url)throw new Error("Supply exactly one --html FILE or --url URL");
      url=inputURL(value,arg==="--html");
    } else if(arg==="--follow-links")follow=true;
    else if(arg==="--check-engine")check=true;
    else if(arg==="--trace-input")traceInput=true;
    else if(arg==="--check-pixels")checkAll=true;
    else if(arg==="--perf-summary")perfSummary=true;
    // Sweeps read back every frame. This flag gives them the interactive rule (check when idle), to measure input latency without the check cost.
    else if(arg==="--idle-checks-only")idleChecksOnly=true;
    else if(arg==="--wasm-engine")wasmEngine=true;
    // One Lean frame for each scroll step, as before the two layers (for comparison).
    else if(arg==="--single-frame")layered=false;
    // No press look (no darkening, no :active frame): the behaviour before issue 1268, for comparison.
    else if(arg==="--no-press-look")pressLook=false;
    else if(arg==="--native-engine"){nativeEngine=args.shift();if(!nativeEngine)throw new Error("--native-engine needs a dylib path");}
    else if(arg==="--font")fontFile=args.shift();
    else if(arg==="--bitmap-font")bitmapFont=true;
    else if(arg==="--resize-sweep")sweep=[[800,500],[700,500],[600,500],[500,500],[400,500],[800,300],[800,500]];
    else if(arg==="--paste-sweep")pasted=args.shift();
    // The window starts with the address bar focused; Escape leaves it, so A and C act on the page.
    else if(arg==="--command-sweep")commands=["=","+","-","_","0",[5,53,0],"a","c",[2,60,60],[3,300,60],[4,300,60],"c",[2,60,60],[4,60,60],"link"];
    // The address bar as a Mac text field (issue 1268): focused and all selected at start and in a
    // new tab; typing replaces; Command-Z, Shift-Command-Z, A, C, X, V; Shift and Option with arrows.
    // "focus:all" checks the start state; "addr=X", "sel=X" and "clip=X" check the text (@url: the page URL).
    else if(arg==="--edit-sweep")commands=["focus:all",[9,120,0],"addr=x","z","addr=@url","Z","addr=x","a","c","clip=x","x","addr=","clip=x",
      "v","addr=x",[9,121,0],"addr=xy",[5,123,1],"sel=y","c","clip=y",[5,51,0],"addr=x","v","addr=xy",[5,123,4],"sel=","addr=xy",
      "z","addr=x","t","focus:all",[5,53,0],"unfocused"];
    // Print to a PDF with no panel, then check its page count (issue 1268).
    else if(arg==="--print-pdf"){printPDF=args.shift();if(!printPDF)throw new Error("--print-pdf needs a file path");commands=["print"];}
    else if(arg==="--graph-sweep")commands=["graph",[2,800,565],[3,900,640],[3,1000,720],[4,1000,720]];
    // Twenty scroll steps of 120 backing pixels down the page: per-step frame time and input latency.
    else if(arg==="--scroll-sweep")commands=Array.from({length:20},()=>[11,-120,0]);
    else if(arg==="--history-sweep")commands=["left","link","left","right","[","]","]","[","link1","]","[","]"];
    // Press and hold a link, then the reload button, then release each (issue 1268): the
    // press acknowledgement, the Lean frame of a held press, and the release.
    else if(arg==="--press-sweep")commands=["press-link","hold","release","hold","press-reload","hold","release","hold"];
    // Back and forward to and from the FOAF graph page (issue 1268): the index's first link opens it;
    // "url:X" fails the run unless the page shown ends with X; "back" presses the chrome's back button.
    else if(arg==="--back-sweep")commands=["overLink","pointer:hand",[3,640,780],"pointer:arrow","link","url:foafnaut:graph",[2,640,500],[4,640,500],"[","url:index.html","]","url:foafnaut:graph",
      [2,700,450],[3,720,470],[4,720,470],"back","url:index.html","right","url:foafnaut:graph","left","url:index.html"];
    else throw new Error(`Unknown native HTML argument: ${arg}`);
  }
  // Lean engine for compile: --native-engine PATH, else libweb-render.dylib beside the program, else Wasm.
  // The app goes into the Dock and Command-Tab, with its menu, before the engine loads (issue 1268).
  const early=check||Deno.build.os!=="darwin"?undefined:await nativePreflight(()=>loadNativeWindow());
  early?.appStart();
  if(nativeEngine&&wasmEngine)throw new Error("Use one of --native-engine and --wasm-engine");
  if(wasmEngine)nativeEngine=undefined;
  else if(!nativeEngine){
    const beside=Deno.execPath().slice(0,Deno.execPath().lastIndexOf("/")+1)+"libweb-render.dylib";
    try{if(Deno.statSync(beside).isFile)nativeEngine=beside;}catch{/* none beside the program: Wasm */}
  }
  const engineInfo:Promise<{backend:string;path:string|null;sha256:string|null}>=nativeEngine
    ?Deno.readFile(nativeEngine).then(async bytes=>({backend:"native",path:nativeEngine!,
      sha256:[...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("")}))
    :Promise.resolve({backend:"wasm",path:null,sha256:null});
  url??=new URL("./pages/index.html",import.meta.url).href;
  // The main-thread engine answers only small calls that input needs at once (shellHit, hit,
  // pointerUp, command, history, shell text). Each is timed; one over 2 ms is traced.
  const slowCalls:Record<string,{count:number;maxMs:number}>={};
  const timed=<T extends Record<string,unknown>>(raw:T):T=>Object.fromEntries(Object.entries(raw).map(([name,fn])=>
    [name,typeof fn!=="function"?fn:(...args:unknown[])=>{
      const start=performance.now(),result=(fn as (...a:unknown[])=>unknown)(...args),took=performance.now()-start;
      if(took>2){const entry=slowCalls[name]??={count:0,maxMs:0};entry.count++;entry.maxMs=Math.max(entry.maxMs,Math.round(took*10)/10);
        console.log(JSON.stringify({type:"native-html-slow-call",t:Math.round(performance.now()),call:name,ms:Math.round(took*10)/10}));}
      return result;
    }])) as T;
  const engine=timed(await loadHTML());
  // Noto Sans is the default face; the bitmap face is the safe mode, and the fallback.
  const defaultFont=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url);
  let workerFont:{path:string;family:string}|undefined;
  if(!bitmapFont)workerFont={path:fontFile??decodeURIComponent(defaultFont.pathname),family:fontFile?"font":"Noto Sans"};
  // Every engine call that can take more than about 2 ms runs in one worker, in order. `lean` is that
  // engine (promises), or the main-thread engine when the worker can not start (said once, loudly) or in --check-engine.
  let worker:CompileClient|undefined,mainFont=false;
  type Lean=Pick<typeof engine,"xmlStylesheet"|"xslt"|"inspect"|"compile"|"selectedText"|"graphStart"|"graphEvent"|"graphPage"|"sourcePage"|"printLayout">;
  let lean:Lean=engine;
  // The engine that runs Lean's renders: the native library in the worker, or Wasm (in the
  // worker, or on the main thread, which has only the Wasm engine). Said at start and in the summary.
  let engineRan="wasm";
  const sayEngine=(where:string)=>{
    engineRan=worker&&nativeEngine?`native ${nativeEngine}`:"wasm";
    console.log(`engine: ${engineRan}`);
    console.log(JSON.stringify({type:"native-html-engine",t:Math.round(performance.now()),engine:engineRan,where}));
  };
  const useMainEngine=async(reason:string)=>{
    console.error("Native HTML: ENGINE WORKER UNAVAILABLE, so Lean runs on the main thread and the window can miss input:",reason);
    console.log(JSON.stringify({type:"native-html-worker",state:"main-thread-fallback",reason}));
    worker=undefined;lean=engine;sayEngine("main-thread");
    if(workerFont&&!mainFont){mainFont=true;try{await loadFontFile(engine,workerFont.path,workerFont.family);}catch(error){if(fontFile)throw error;workerFont=undefined;}}
  };
  if(check){
    sayEngine("main-thread");
    if(workerFont)try{await loadFontFile(engine,workerFont.path,workerFont.family);}catch(error){if(fontFile)throw error;console.error("Native HTML: bitmap font, because Noto Sans did not load:",String(error));}
  } else {
    try{worker=await startCompileWorker(workerFont,nativeEngine);}
    catch(error){
      if(workerFont&&!fontFile){
        console.error("Native HTML: bitmap font, because Noto Sans did not load or the worker failed:",String(error));
        workerFont=undefined;
        try{worker=await startCompileWorker(undefined,nativeEngine);}catch(error2){await useMainEngine(String(error2));}
      } else if(fontFile)throw error;
      else await useMainEngine(String(error));
    }
    if(worker){lean=worker.engine as unknown as Lean;sayEngine("worker");}
  }
  let document=await prepareHTML(lean,url),width=1280,height=800;
  // The first compile runs in the worker too: it warms the worker, and no frame is compiled on the main thread.
  let frame:HTMLArtifact=await document.compile(width,height);
  console.log(JSON.stringify({type:"native-html-loaded",url:document.url,primitives:frame.primitiveCount,links:frame.webRender.links.length,width,height}));
  if(check){
    // Synthetic limits exercise only the published planner ABI. Window rendering
    // always passes the real device limits in createHTMLWindowSession.
    const plan=await requestRenderPlan("svg-offscreen","rgba8unorm",frame as unknown as {width:number;height:number;data:number[]},{
      maxUniformBufferBindingSize:65536,maxStorageBufferBindingSize:134217728,
      maxTextureDimension2D:4096,maxBufferSize:268435456});
    console.log(`Native HTML CPU plan: ${plan.abi}; ${plan.uniform.bindingType}; ${plan.uniform.bytes} bytes`);
    console.log("Native HTML CPU engine check complete; GPU/window not requested");return;
  }
  const adapter=await navigator.gpu?.requestAdapter();
  if(!adapter){console.error("GPU BLOCKED: native HTML adapter unavailable in this launch context");Deno.exitCode=2;return;}
  console.log("Native HTML GPU adapter:",adapter.info);
  let device:GPUDevice|undefined,native:ReturnType<typeof loadNativeWindow>|undefined;
  let session:Awaited<ReturnType<typeof createHTMLWindowSession>>|undefined;
  let running=true,dirty=true,controller:AbortController|undefined;
  // Frame trace, one JSON line for each event: every number a tool needs to find
  // where the time goes. A pump stall means AppKit held the thread in its own loop.
  let resizeAt:number|undefined,frameNumber=0,waiting=false,waitingSince=0;
  const trace=(type:string,fields:Record<string,unknown>)=>console.log(JSON.stringify({type,t:Math.round(performance.now()),...fields}));
  const ms=(start:number,end:number)=>Math.round((end-start)*10)/10;
  let candidate:Awaited<ReturnType<typeof prepareHTML>>|undefined;
  const refuse=(target:string,error:unknown)=>{
    console.error("Native HTML refused:",target,String(error));
    trace("native-html-refused",{url:target,reason:String(error)});
    prepareHTML(lean,target,undefined,refusalHTML(target,String(error))).then(next=>{if(running){candidate=next;dirty=true;}})
      .catch(failure=>console.error("Native HTML refusal page failed:",String(failure)));
  };
  // View state is held here and applied by Lean. Pointer positions are in the
  // coordinates of the presented frame, as link picking is.
  const view:PageView={textScalePercent:150};
  let press:number[]|undefined,lastCopied:string|undefined,loading=false;
  // The press on screen (issue 1268): Lean's `press` answer (a chrome control, or the link's
  // node for `:active`, and the rectangles that the composite darkens), the time its event was
  // queued, and whether a Lean frame that includes it was asked for and presented.
  // `hoverNode` is the link under the pointer, sent only when an author rule names `:hover`.
  type Pressed={control?:string;active?:number;rects:number[][];at:number;framed:boolean;asked:boolean};
  let pressed:Pressed|undefined,pressPresent=false,hoverNode:number|undefined,eventAt=0;
  const pressOverlayMs:number[]=[],pressFrameMs:number[]=[];
  // A press held this long gets a Lean frame with `:active` (and the sunken chrome button).
  const PRESS_FRAME_MS=150;
  // Session history is a Lean value. The host keeps it and loads the URLs Lean returns.
  let history=engine.historyPush({entries:[],index:0},document.url);
  // The chrome is a Lean value too. The host stores it and shows what Lean draws.
  const home=document;
  // The address bar's text, cursor, selection and undo step: a Lean value (WebShell.editJson).
  type Field=Omit<ShellEdit,"clipboard">;
  const showURL=(url:string):Field=>({address:url,cursor:url.length,anchor:url.length,undo:null,redo:null,typing:false});
  let field=showURL(document.url),focused=false,theme="next",pages=1,scale=1,active=0,scroll=0;
  const tabs:{document:typeof document;history:typeof history;scroll:number}[]=[{document,history,scroll:0}];
  const shell=()=>({tabs:tabs.map((tab,index)=>({title:(index===active?document:tab.document).title??""})),active,...field,focused,
    canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll,pressed:pressed?.control??""});
  // The URLs of the session history of every tab: Lean matches `:visited` against them.
  const visited=()=>[...new Set([...tabs.flatMap((tab,index)=>(index===active?history:tab.history).history.entries)])].slice(-100);
  const shown=()=>({...view,shell:shell(),visited:visited(),
    ...(pressed?.active!==undefined?{active:pressed.active}:{}),...(hoverNode!==undefined?{hover:hoverNode}:{})});
  const showTab=(index:number)=>{
    controller?.abort();candidate=undefined;loading=false;focused=false;active=index;
    ({document,history,scroll}=tabs[index]);field=showURL(document.url);dirty=true;
    native?.setHistory(history.canBack,history.canForward);
  };
  const keepTab=()=>{tabs[active]={document,history,scroll};};
  // The composite darkens Lean's rectangles at once (no Lean call); a Lean frame that
  // includes the press replaces the darkening (renderFrame).
  const startPress=(answer:{control?:string;active?:number;rects:number[][]})=>{
    if(!pressLook)return;
    pressed={...answer,at:eventAt,framed:false,asked:false};
    if(layered&&current&&session){session.setPress(answer.rects);pressPresent=true;}
  };
  const endPress=()=>{
    const was=pressed;if(!was)return;pressed=undefined;
    session?.setPress(undefined);
    if(was.framed||was.asked)dirty=true;else if(layered&&current)pressPresent=true;
  };
  const newTab=()=>{keepTab();tabs.push({document:home,history:engine.historyPush({entries:[],index:0},home.url),scroll:0});showTab(tabs.length-1);focusAddress();};
  const closeTab=(index:number)=>{
    if(tabs.length===1){running=false;return;}
    keepTab();tabs.splice(index,1);showTab(Math.min(active>index?active-1:active,tabs.length-1));
  };
  // One tab for each source: an XML page opens its XML, its XSLT and the result.
  const viewSource=async()=>{
    for(const item of document.sources){
      const page=await prepareHTML(lean,item.url+"#source",undefined,await lean.sourcePage(item.kind,item.url,item.source));
      keepTab();tabs.push({document:page,history:engine.historyPush({entries:[],index:0},page.url),scroll:0});showTab(tabs.length-1);
    }
  };
  // The FOAF graph is a page whose model and frames come from Lean's graph app.
  type Page=typeof document&{graph?:{model:string;clock:boolean;last:number}};
  const graphFrame=async(page:Page,frame:{model:string;commands:string[]})=>{
    page.graph!.model=frame.model;
    if(frame.commands.includes("startClock")){page.graph!.clock=true;page.graph!.last=performance.now();}
    if(frame.commands.includes("stopClock"))page.graph!.clock=false;
    // The frame is built from the model (`graphModel`), with no SVG text; `graphPage` stays for export.
    if(frame.commands.includes("render"))dirty=true;
  };
  // Graph input runs in the worker, in the order it arrived. Each call takes the model the call before it
  // returned. A queued move, resize or clock tick that has not started is replaced by a later one of the same
  // kind (the clock keeps the sum of its elapsed time); presses, releases and keys are never merged or dropped.
  const graphQueue:{kind:number;a:number;b:number;page:Page}[]=[];
  let graphRunning=false;
  const graphBusy=()=>graphRunning||graphQueue.length>0;
  const runGraph=async()=>{
    graphRunning=true;
    try{
      while(graphQueue.length){
        const op=graphQueue.shift()!,page=op.page;
        if(!page.graph)continue;
        try{await graphFrame(page,await lean.graphEvent(page.graph.model,op.kind,op.a,op.b,width,shell()));}
        catch(error){refuse(page.url,error);}
      }
    }finally{graphRunning=false;}
  };
  const graphInput=(kind:number,a:number,b:number)=>{
    const page=document as Page,last=graphQueue[graphQueue.length-1];
    if(last&&last.page===page&&last.kind===kind&&(kind===1||kind===3||kind===7)){
      if(kind===7)last.a+=a;else{last.a=a;last.b=b;}
    } else graphQueue.push({kind,a,b,page});
    if(!graphRunning)runGraph();
  };
  // Lean's link and address rules make the graph a page (`WebShell.graphURL`): it opens in the
  // tab and goes into its history like any page, so back leaves it (issue 1268).
  const graphURL="foafnaut:graph";
  const graphPage=async()=>{
    const rdf=await Deno.readTextFile(new URL("./pages/foaf-demo.ttl",import.meta.url));
    const frame=await lean.graphStart(rdf,width,height,shell());
    const page={url:graphURL,baseURL:graphURL,title:"FOAF graph",source:"",sources:[] as typeof document.sources,
      graph:{model:frame.model,clock:false,last:0},
      request(_w:number,_h:number,view:PageView={}){return {source:"",options:{url:page.url,resources:[],graphModel:page.graph!.model,...view} as Record<string,unknown>};},
      compile(w:number,h:number,view:PageView={}){return lean.compile("",w,h,{url:page.url,resources:[],graphModel:page.graph!.model,...view});},
      selectedText:()=>""} as unknown as Page;
    await graphFrame(page,frame);
    return page as typeof document;
  };
  // The system pointer for a window point: Lean answers from the chrome, the graph model or the
  // link regions of the frame on screen. One small main-thread call for each coalesced move; the
  // window library is told only when the answer changes (issue 1268).
  let pointerShown="arrow",lastPointer:number[]|undefined;
  const linkText=new WeakMap<object,string>();
  const pointAt=(x:number,y:number)=>{
    lastPointer=[x,y];
    if(!session?.frames||!native)return;
    const page=document as Page,request:{shell:unknown;x:number;y:number;width:number;model?:string;links?:string;pageY?:number}={shell:shell(),x,y,width};
    if(page.graph)request.model=page.graph.model;
    else if(!candidate&&frame.webRender.links.length){
      let links=linkText.get(frame);
      if(links===undefined){links=JSON.stringify(frame.webRender.links);linkText.set(frame,links);}
      request.links=links;request.pageY=Math.round(pageRow(y));
    }
    const kind=engine.pointerCursor(request);
    if(kind!==pointerShown){pointerShown=kind;native.setCursor(kind);}
  };
  // Lean selects the whole address when the bar takes the focus; typing then replaces it.
  const focusAddress=()=>{const {clipboard:_,...next}=engine.shellEdit(shell(),"focus",document.url);field=next;focused=true;dirty=true;};
  const leaveAddress=()=>{focused=false;field=showURL(document.url);dirty=true;};
  const scrollLimit=()=>{
    const boxes=frame.webRender.boxes as number[][]|undefined;
    const bottom=Math.max(0,...(boxes??[]).map(box=>box[2]+box[4]));
    return Math.max(0,bottom-height+Math.round(60*scale));
  };
  const scrollBy=(amount:number)=>{
    const next=Math.max(0,Math.min(scrollLimit(),scroll+Math.round(amount)));
    if(next===scroll)return;
    scroll=next;motion=trackMotion(motion,scroll,performance.now());
    // Inside the band of the layers on screen, a scroll only moves the composite: no Lean call.
    // Lean's keep range says when to ask for a new band; until it comes, the view stays in the old one.
    // A prefetched band of the same state that keeps the scroll, ready or coming, takes the place of a new render.
    if(canShift()){shiftPending=true;shiftedByEvent=true;if(!keeps(current!.layers.layers,scroll)&&!bandComing())dirty=true;}
    else dirty=true;
  };
  // Scroll prefetch (scroll_prefetch.ts). `everyFrame` is set when the window opens.
  let everyFrame=false,motion:Motion|undefined,bandMs=100;
  type RequestRecord={request:ReturnType<typeof document.request>;width:number;height:number;document:typeof document};
  let prefetched:{key:StateKey;layers:HTMLLayers;target:number;record:RequestRecord}|undefined;
  let prefetching:{key:StateKey;target:number;reach:number}|undefined;
  const prefetchStats={sent:0,ready:0,swaps:0,dropped:0,stale:0,missed:0};
  // The request that a frame of `page` at this scroll sends to Lean, and its state with no scroll.
  const requestAt=(page:typeof document,at:number)=>{
    const view0=shown();view0.shell={...view0.shell,scroll:at};
    return page.request(width,height,{...view0,live:page===checked,...(everyFrame?{}:{checks:false})});
  };
  const stateNow=()=>stateKey(document,requestAt(document,scroll).options,width,height);
  // The prefetched band can be shown now in place of a Lean frame.
  const swapReady=()=>!!current&&!!prefetched&&canSwap(current.layers.layers,{key:prefetched.key,band:prefetched.layers.layers},stateNow(),scroll);
  // A band that keeps this scroll is ready, or is being made for the same state: wait for it.
  const bandComing=()=>{
    if(swapReady())return true;
    if(!prefetching||Math.abs(scroll-prefetching.target)>prefetching.reach)return false;
    return sameState(prefetching.key,stateNow());
  };
  // The layers on screen, and the page row of the band shown at the top of the view.
  let current:{layers:HTMLLayers;document:typeof document;width:number;height:number}|undefined,shownOffset=0;
  let shiftPending=false,shiftedByEvent=false;
  let checked:typeof document|undefined;
  // A selection is in window coordinates, so with one a scroll needs a Lean frame.
  const canShift=()=>layered&&!!current&&current.document===document&&!candidate&&current.width===width&&current.height===height&&!Array.isArray(view.selection);
  // Window and page-layer rows, for link picking: the composite maps one to the other.
  const pageRow=(y:number)=>current?y-current.layers.layers.top+shownOffset:y;
  const windowRow=(y:number)=>current?y+current.layers.layers.top-shownOffset:y;
  const settingsURL=new URL("./pages/settings.html",import.meta.url).href;
  const shellCommand=(name:string,argument:string)=>{
    if(name==="back")windowCommand(6);
    else if(name==="forward")windowCommand(7);
    else if(name==="reload")windowCommand(8);
    else if(name==="new")newTab();
    else if(name==="close")closeTab(active);
    else if(name==="home")navigate(home.url);
    else if(name==="graph")navigate(graphURL);
    else if(name==="source")viewSource().catch(error=>refuse(document.url,error));
    else if(name==="theme"){theme=argument||(theme==="next"?"arcade":"next");dirty=true;}
    else if(name==="zoom"&&/^[0-9]+$/.test(argument)){view.textScalePercent=Math.max(50,Number(argument));dirty=true;}
    else navigate(settingsURL);
  };
  const go=(answer:ReturnType<typeof engine.shellSubmit>)=>{
    trace("native-html-go",answer);
    if(answer.go==="system")try{native!.openURL(answer.url);}catch(error){refuse(answer.url,error);}
    else if(answer.go==="page")navigate(answer.url);
    else shellCommand(answer.name,answer.argument);
  };
  const chrome=(control:string)=>{
    const [name,index]=control.split(":");
    if(name==="back")windowCommand(6);
    else if(name==="forward")windowCommand(7);
    else if(name==="reload")windowCommand(8);
    else if(name==="settings")navigate(settingsURL);
    else if(name==="home")navigate(home.url);
    else if(name==="source")viewSource().catch(error=>refuse(document.url,error));
    else if(name==="address")focusAddress();
    else if(name==="newTab")newTab();
    else if(name==="tab"&&Number(index)!==active){keepTab();showTab(Number(index));}
    else if(name==="close")closeTab(Number(index));
    else if(name==="tabs"){keepTab();showTab((active+1)%tabs.length);}
  };
  const edit=(answer:ShellEdit&{clipboard?:string|null})=>{const {clipboard:_,...next}=answer;field=next;dirty=true;};
  const remember=(answer:HistoryAnswer,action:string)=>{
    history=answer;native?.setHistory(answer.canBack,answer.canForward);
    if(action==="push")pages++;
    trace("native-html-history",{action,index:answer.history.index,size:answer.history.entries.length,url:answer.url});
  };
  const windowCommand=(id:number)=>{
    const answer=engine.command(id,view.textScalePercent??100,history.history,focused);
    // Lean says when an edit command acts on the address bar: when it has the focus, and paste
    // always. The host only reads and writes the clipboard (issue 1268).
    if(answer.target==="address"){
      if(!focused)focusAddress();
      const result=engine.shellEdit(shell(),answer.action,answer.action==="paste"?native!.readClipboard():"");
      edit(result);
      if(result.clipboard){native!.writeClipboard(result.clipboard);lastCopied=result.clipboard;trace("native-html-copy",{characters:result.clipboard.length,from:"address"});}
      trace("native-html-edit",{action:answer.action,characters:field.address.length,anchor:field.anchor,cursor:field.cursor});
      return;
    }
    if(["back","forward","reload"].includes(answer.action)){
      if(answer.url)navigate(answer.url,false);
      remember(answer as HistoryAnswer,answer.action);
    }
    if(answer.textScalePercent!==view.textScalePercent){
      view.textScalePercent=answer.textScalePercent;view.selection=undefined;dirty=true;
      trace("native-html-zoom",{textScalePercent:answer.textScalePercent});
    }
    if(answer.action==="focusAddress")focusAddress();
    if(answer.action==="newTab")newTab();
    if(answer.action==="closeTab")closeTab(active);
    if(answer.action==="settings")navigate(settingsURL);
    if(answer.action==="print")printDocument().catch(error=>console.error("Native HTML print failed:",String(error)));
    if(answer.action==="viewSource")viewSource().catch(error=>refuse(document.url,error));
    if(answer.action==="selectAll"){view.selection="all";dirty=true;}
    if(answer.action==="copy"&&view.selection){
      // The selected text is made in the worker; the clipboard is written when it arrives.
      Promise.resolve(document.selectedText(width,height,shown())).then(text=>{
        if(text){native!.writeClipboard(text);lastCopied=text;trace("native-html-copy",{characters:text.length});}
      }).catch(error=>console.error("Native HTML copy failed:",String(error)));
    }
  };
  // Printing (issue 1268). Lean lays the page out for the paper of the page setup with the
  // print media type and says where the pages break; it draws each page; the GPU renders it;
  // the window library gives the images to the system print panel (or, with a path, to a PDF
  // with no panel). Device pixels are 2 for each point (144 dpi), so CSS text is 150%.
  let printing=false;
  const printDocument=async(pdfPath?:string)=>{
    if(printing||!native)return false;
    printing=true;
    try{
      const start=performance.now(),page=document;
      const paper=native.printPaper()??DEFAULT_PAPER;
      const job=await printImages(lean,page,paper);
      const drawn=performance.now();
      const sent=native.print(job.images,job.count,job.width,job.height,job.pointWidth,job.pointHeight,page.title||page.url,pdfPath);
      const record:Record<string,unknown>={pages:job.count,breaks:job.breaks,paper,width:job.width,height:job.height,drawMs:ms(start,drawn),sent};
      if(pdfPath&&sent>0){
        record.pdfPages=pdfPageCount(await Deno.readFile(pdfPath));
        if(record.pdfPages!==job.count){console.error(`Native HTML print: ${job.count} pages laid out, ${record.pdfPages} in the PDF`);Deno.exitCode=1;}
      }
      trace("native-html-print",record);
      return sent>0;
    }finally{printing=false;}
  };
  // A new page goes into history when its load ends, and a refused page does too.
  const navigate=(target:string,push=true)=>{
    controller?.abort();candidate=undefined;controller=new AbortController();const current=controller;loading=true;
    console.log(JSON.stringify({type:"native-html-loading",url:target}));
    (target===graphURL?graphPage():prepareHTML(lean,target,current.signal)).then(next=>{
      if(current===controller&&!current.signal.aborted&&running){
        candidate=next;dirty=true;loading=false;
        if(push)remember(engine.historyPush(history.history,next.url),"push");
      }
    }).catch(error=>{
      if(current.signal.aborted)return;
      loading=false;if(push)remember(engine.historyPush(history.history,target),"push");
      refuse(target,error);
    });
  };
  let lastStep=0,stepAt=0,pressAt=[0,0];
  let lastActivity=performance.now(),queueMax=0,fatal:unknown,rendering:Promise<void>|undefined;
  let awaiting:{kind:number;at:number}[]=[],awaitingShift:{kind:number;at:number}[]=[],awaitingBand:{kind:number;at:number}[]=[],checkedFrames=0,workerFrames=0,mainFrames=0;
  let shifting:Promise<void>|undefined;const shifts:number[]=[];
  const latencies:number[]=[],totals:number[]=[],pumpGaps:number[]=[],pumpGapsLate:number[]=[];let lastPump:number|undefined,firstFrameAt:number|undefined;
  const percentile=(values:number[],q:number)=>{if(!values.length)return null;const sorted=[...values].sort((a,b)=>a-b);return Math.round(sorted[Math.min(sorted.length-1,Math.ceil(q*sorted.length)-1)]*10)/10;};
  // Latency starts when the window library queued the event, or at dequeue with an older library.
  const latencyFrom=()=>native?.eventClock()===null?"dequeued":"queued";
  // Exit summary: input to present latency, and frame totals. Always traced; --perf-summary also prints it.
  const summary=()=>{
    const line={type:"native-html-perf-summary",inputEventsDropped:native?.eventsDropped()??0,inputLatency:{from:latencyFrom(),count:latencies.length,p50Ms:percentile(latencies,0.5),p95Ms:percentile(latencies,0.95),maxMs:latencies.length?Math.max(...latencies):null},
      engine:engineRan,compileBackend:engineRan.startsWith("native")?"native":"wasm",layered,
      scrollPresents:{count:shifts.length,totalMsP50:percentile(shifts,0.5),totalMsP95:percentile(shifts,0.95),maxMs:shifts.length?Math.round(Math.max(...shifts)*10)/10:null},
      frames:{presented:totals.length,checked:checkedFrames,compiledInWorker:workerFrames,compiledOnMain:mainFrames,totalMsP50:percentile(totals,0.5),totalMsP95:percentile(totals,0.95)},
      // Time between two native event pumps: the longest time the window takes no input.
      // After the first frame is presented: the figure the 50 ms target is judged on.
      pumpGapAfterFirstFrameMs:{count:pumpGapsLate.length,p50:percentile(pumpGapsLate,0.5),p95:percentile(pumpGapsLate,0.95),max:pumpGapsLate.length?Math.round(Math.max(...pumpGapsLate)*10)/10:null},
      slowCalls,
      pumpGapMs:{p50:percentile(pumpGaps,0.5),p95:percentile(pumpGaps,0.95),max:pumpGaps.length?Math.round(Math.max(...pumpGaps)*10)/10:null},
      prefetch:prefetchStats,queueMax,sessionStats:session?.stats,
      // Pointer press to the present that shows it: the composite darkening, and the Lean frame of a held press.
      press:{overlay:{count:pressOverlayMs.length,p50Ms:percentile(pressOverlayMs,0.5),maxMs:pressOverlayMs.length?Math.round(Math.max(...pressOverlayMs)*10)/10:null},
        frame:{count:pressFrameMs.length,p50Ms:percentile(pressFrameMs,0.5),maxMs:pressFrameMs.length?Math.round(Math.max(...pressFrameMs)*10)/10:null}}};
    trace(line.type,line);
    if(perfSummary)console.log(`engine: ${engineRan}\ninput latency: ${line.inputLatency.count} events, p50 ${line.inputLatency.p50Ms} ms, p95 ${line.inputLatency.p95Ms} ms, max ${line.inputLatency.maxMs} ms\nframes: ${line.frames.presented} presented (${line.frames.checked} checked), totalMs p50 ${line.frames.totalMsP50}, p95 ${line.frames.totalMsP95}; pipeline builds ${session?.stats.pipelineBuilds}\nscroll presents with no Lean call: ${line.scrollPresents.count}, totalMs p50 ${line.scrollPresents.totalMsP50}, p95 ${line.scrollPresents.totalMsP95}, max ${line.scrollPresents.maxMs}\npress to present: darkening ${line.press.overlay.count}, p50 ${line.press.overlay.p50Ms} ms, max ${line.press.overlay.maxMs} ms; Lean frame ${line.press.frame.count}, p50 ${line.press.frame.p50Ms} ms, max ${line.press.frame.maxMs} ms\nscroll prefetch: ${prefetchStats.sent} sent, ${prefetchStats.ready} ready, ${prefetchStats.swaps} shown, ${prefetchStats.dropped} dropped, ${prefetchStats.stale} stale, ${prefetchStats.missed} missed\npump gap after first frame: p50 ${line.pumpGapAfterFirstFrameMs.p50} ms, p95 ${line.pumpGapAfterFirstFrameMs.p95} ms, max ${line.pumpGapAfterFirstFrameMs.max} ms\npump gap all: p50 ${line.pumpGapMs.p50} ms, p95 ${line.pumpGapMs.p95} ms, max ${line.pumpGapMs.max} ms`);
  };
  try {
    device=await adapter.requestDevice();native=early??await nativePreflight(()=>loadNativeWindow());
    native.setInputTrace(traceInput);native.setHistory(history.canBack,history.canForward);
    // The command sweep copies text. It gives the clipboard back unless the person
    // copied something else meanwhile.
    const savedClipboard=commands||pasted?native.readClipboard():"";
    // Paste a URL into the address bar through the real menu key, then press Return.
    if(pasted){native.writeClipboard(pasted);lastCopied=pasted;commands=["v",[5,36,0],"settle"];}
    // The window title is the page title, as in Safari.
    const windowTitle=(page:typeof document)=>page.title||"foafnaut";
    const handles=native.create(800,500,windowTitle(document));
    const surface=new Deno.UnsafeWindowSurface(cocoaSurfaceOptions(handles,width,height));
    native.showAfterSurface();
    // A new window starts in the address bar with the address selected (issue 1268).
    focusAddress();
    scale=Math.max(1,Math.round(native.surfaceState().contentsScale||1));
    if(commands)native.testRaise();
    device.addEventListener("uncapturederror",event=>{console.error("Native HTML GPU error:",(event as GPUUncapturedErrorEvent).error.message);running=false;Deno.exitCode=1;});
    device.lost.then(info=>{if(running){console.error("Native HTML GPU lost:",info.message);running=false;Deno.exitCode=1;}});
    // One session for the window's life. It keeps the pipeline and buffers (issue 1268).
    session=await createHTMLWindowSession(device,surface,native);
    // Lean's compile runs in a worker so this loop keeps pumping. If the worker
    // can not start or dies, compile runs here instead, and the trace says so.
    // Readback, pixel checks and the frame hash are test work. They run on every frame
    // in sweeps and with --check-pixels; interactively, once after input has been idle.
    everyFrame=checkAll||(!idleChecksOnly&&(!!sweep||!!commands));
    const IDLE_CHECK_MS=500,QUEUE_WARN=1024;
    const STAMPED=new Set([2,4,5,11]);
    const KIND_NAMES:Record<number,string>={2:"pointer-down",4:"pointer-up",5:"key",11:"scroll"};
    // Events carry the time the window library queued them (see the event loop).
    const settle=(stamps:{kind:number;at:number}[],at:number)=>{
      for(const stamp of stamps){
        const latency=Math.round((at-stamp.at)*10)/10;latencies.push(latency);
        trace("native-html-input-latency",{kind:KIND_NAMES[stamp.kind]??stamp.kind,ms:latency,frame:frameNumber,from:latencyFrom()});
      }
    };
    const renderFrame=async()=>{
      const nextDocument=candidate??document;
      const frameStart=performance.now();
      const stamps=awaiting;awaiting=[];
      // An interactive frame asks Lean for no CPU probe (checks:false, about a fifth of a
      // frame); the idle check below asks for the same frame with its probe and checks it.
      // A new page starts at the top, so its band does too.
      const request=requestAt(nextDocument,nextDocument!==document?0:scroll);
      const sentWidth=width,sentHeight=height;
      // The press this frame includes (`active`, `shell.pressed`), if any.
      const carried=pressed;if(carried)carried.asked=true;
      // A prefetch for another state would only hold the worker: drop it if it has not started.
      if(prefetching&&!sameState(prefetching.key,stateKey(nextDocument,request.options,sentWidth,sentHeight)))worker?.dropLow();
      // Events from here on mark the page dirty again: latest state wins, in the next frame.
      dirty=false;
      let next:HTMLArtifact,nextLayers:HTMLLayers|undefined,where="worker",workerMs:number|undefined;
      try{
        if(layered){
          if(worker?.alive){({layers:nextLayers,workerMs}=await worker.compileLayers(request.source,sentWidth,sentHeight,request.options));bandMs=workerMs;}
          else{where="main";nextLayers=engine.compileLayers(request.source,sentWidth,sentHeight,request.options);}
          next=nextLayers.page;
        }
        else if(worker?.alive){({artifact:next,workerMs}=await worker.compile(request.source,sentWidth,sentHeight,request.options));}
        else{where="main";next=engine.compile(request.source,sentWidth,sentHeight,request.options);}
      }catch(error){
        if(worker&&!worker.alive){
          // The worker died: Lean runs on the main thread from now on, and the trace says so.
          await useMainEngine("worker died: "+String(error));
          awaiting=[...stamps,...awaiting];dirty=true;return;
        }
        awaiting=[...stamps,...awaiting];candidate=undefined;dirty=false;refuse(nextDocument.url,error);return;
      }
      const compiled=performance.now();
      // A newer page was chosen while this one compiled: drop this scene.
      if((candidate??document)!==nextDocument){awaiting=[...stamps,...awaiting];dirty=true;return;}
      // With layers, the composite shows the scroll of now, kept in the new band.
      const scrollNow=nextDocument!==document?0:scroll;
      const place=nextLayers?clampOffset(nextLayers.layers,scrollNow):undefined;
      // Lean draws the press in this frame: the composite does not darken it again.
      if(carried&&carried===pressed)session!.setPress(undefined);
      const result=nextLayers?await session!.drawLayers(nextLayers,sentWidth,sentHeight,place!.offset,everyFrame):await session!.draw(next,everyFrame);
      if(carried&&carried===pressed){
        if(result.presented){carried.framed=true;pressFrameMs.push(result.presentedAt-carried.at);
          trace("native-html-press",{state:"frame",control:carried.control??null,active:carried.active??null,fromQueuedMs:ms(carried.at,result.presentedAt)});}
        else session!.setPress(carried.rects);
      }
      // Released while Lean made this frame with the press: draw it again without.
      if(carried&&carried!==pressed)dirty=true;
      if(result.presented)lastRequest={request,width:sentWidth,height:sentHeight,document:nextDocument};
      const finished=performance.now();
      const stats=session!.stats;
      const engineFact=frameNumber===0?{engine:await engineInfo}:{};
      trace("native-html-frame",{frame:++frameNumber,width:sentWidth,height:sentHeight,primitives:next.primitiveCount,wgslBytes:next.wgsl.length,dataFloats:next.data.length,
        layoutMs:ms(frameStart,compiled),sessionMs:Math.round(result.prepareMs*10)/10,drawMs:Math.round(result.drawMs*10)/10,totalMs:ms(frameStart,finished),
        resizeToFrameMs:resizeAt===undefined?null:ms(resizeAt,finished),presented:result.presented,compiledIn:where,workerMs:workerMs===undefined?null:Math.round(workerMs*10)/10,
        checked:result.checked,steps:result.steps,pixelHash:result.checked?result.pixelHash:null,pipelineBuilds:stats.pipelineBuilds,configures:stats.configures,
        ...(nextLayers?{layers:{bandTop:nextLayers.layers.bandTop,bandHeight:nextLayers.layers.bandHeight,offset:place!.offset,chromeFloats:nextLayers.chrome.data.length}}:{}),...engineFact});
      resizeAt=undefined;
      if(!result.presented){awaiting=[...stamps,...awaiting];dirty=true;return;}
      firstFrameAt??=finished;totals.push(finished-frameStart);if(where==="worker")workerFrames++;else mainFrames++;
      if(result.checked)checkedFrames++;
      lastActivity=Math.max(lastActivity,finished);
      settle(stamps,result.presentedAt);
      if(nextLayers){
        current={layers:nextLayers,document:nextDocument,width:sentWidth,height:sentHeight};shownOffset=place!.offset;
        // Scrolls taken while Lean worked: shown now if the band holds them, else after the next band.
        if(place!.exact){settle(awaitingShift,result.presentedAt);settle(awaitingBand,result.presentedAt);awaitingShift=[];awaitingBand=[];}
        if(nextDocument===document&&!keeps(nextLayers.layers,scroll)&&!bandComing())dirty=true;
      } else {current=undefined;settle(awaitingBand,result.presentedAt);awaitingBand=[];}
      if(nextDocument!==document)prefetched=undefined;
      checked=nextDocument;
      if(nextDocument!==document)view.selection=undefined;
      if(nextDocument!==document){scroll=0;if(!focused)field=showURL(nextDocument.url);}frame=next;document=nextDocument;candidate=undefined;native!.setTitle(windowTitle(document));
      // A new page under a pointer that has not moved.
      if(lastPointer)pointAt(lastPointer[0],lastPointer[1]);
      console.log(JSON.stringify({type:"native-html-presented",url:document.url,width:sentWidth,height:sentHeight,primitives:frame.primitiveCount,links:frame.webRender.links.length,frames:session!.frames}));
    };
    let lastRequest:RequestRecord|undefined;
    const idleCheck=async()=>{
      const idleStart=performance.now();
      let result;
      if(layered&&current&&lastRequest&&lastRequest.request.options.checks===false&&worker?.alive){
        // The layers on screen were made with no probe: Lean makes them again with probes, at this scroll.
        const shownRequest=lastRequest,options:Record<string,unknown>={...shownRequest.request.options,shell:shell()};delete options.checks;
        const {layers}=await worker.compileLayers(shownRequest.request.source,shownRequest.width,shownRequest.height,options);
        if(dirty||shiftPending||shifting||lastRequest!==shownRequest||document!==shownRequest.document)return;
        const {offset}=clampOffset(layers.layers,scroll);
        result=await session!.drawLayers(layers,shownRequest.width,shownRequest.height,offset,true);
        if(result.presented){current={layers,document,width:shownRequest.width,height:shownRequest.height};frame=layers.page;shownOffset=offset;}
      } else if(lastRequest&&lastRequest.request.options.checks===false&&worker?.alive){
        // The frame on screen was made with no probe: Lean makes it again with its probe.
        // The page must not have changed meanwhile; if it has, the next idle time checks.
        const shownRequest=lastRequest,options={...shownRequest.request.options};delete options.checks;
        const {artifact}=await worker.compile(shownRequest.request.source,shownRequest.width,shownRequest.height,options);
        if(dirty||lastRequest!==shownRequest||document!==shownRequest.document)return;
        result=await session!.draw(artifact,true);
      } else result=await session!.checkLast();
      if(!result?.presented)return;
      checkedFrames++;
      trace("native-html-checked",{frame:frameNumber,why:"idle",idleMs:ms(lastActivity,idleStart),drawMs:Math.round(result.drawMs*10)/10,pixelHash:result.pixelHash});
    };
    const handle=(event:UIEvent)=>{
        if(event.kind===6){running=false;return;}
        // A release ends the press look, on the graph page too.
        if(event.kind===4&&pressed)endPress();
        if(event.kind===1){
          if(event.a<1||event.b<1)return;
          if(event.a>4096||event.b>4096)throw new Error("Native HTML window exceeds 4096 backing pixels; close or use a smaller window");
          if(event.a!==width||event.b!==height){width=event.a;height=event.b;dirty=true;if((document as Page).graph)graphInput(1,width,height);resizeAt??=performance.now();trace("native-html-resize",{width,height});}
        }
        if(event.kind===8&&event.a)dirty=true;
        if(event.kind===3)pointAt(event.a,event.b);
        const graph=(document as Page).graph;
        if(graph&&!focused&&(event.kind===3||event.kind===4||event.kind===9||(event.kind===5&&!(event.b&2)))){graphInput(event.kind,event.a,event.b);return;}
        if(event.kind===5&&focused&&!(event.b&2)){
          if(event.a===36){const target=field.address;leaveAddress();go(engine.shellSubmit(target));}
          else if(event.a===53)leaveAddress();
          // Shift, Option and Command change what the key does; Lean decides.
          else edit(engine.shellKey(shell(),event.a,event.b));
          return;
        }
        if(event.kind===9&&focused){
          edit(engine.shellText(shell(),String.fromCodePoint(event.a)));
          return;
        }
        if(event.kind===9)return;
        // Page keys: arrows, page up and down, space.
        if(event.kind===5&&!(event.b&2)){
          const page=height*0.8;
          if(event.a===125)scrollBy(80*scale);
          if(event.a===126)scrollBy(-80*scale);
          if(event.a===121||event.a===49)scrollBy(page);
          if(event.a===116)scrollBy(-page);
        }
        if(event.kind===11)scrollBy(-event.a);
        if(event.kind===5&&event.a===15)windowCommand(8);
        if(event.kind===10)windowCommand(event.a);
        if(event.kind===2){
          // Hit coordinates and boxes belong to the successfully presented frame.
          if(!session?.frames)return;
          // One small Lean call: the control or the link pressed, and what the composite darkens.
          const answer=engine.press(shell(),event.a,event.b,width,pageRow(event.b),layered&&current?frame.webRender.links as unknown[]:[]);
          const control=answer.control;
          if(control){if(answer.rects.length)startPress({control,rects:answer.rects});chrome(control);return;}
          if(focused)leaveAddress();
          if((document as Page).graph){graphInput(2,event.a,event.b);return;}
          press=[event.a,event.b,event.a,event.b];
          if(typeof answer.sourceNode==="number")startPress({active:answer.sourceNode,rects:answer.rects});
          if(view.selection){view.selection=undefined;dirty=true;}
        }
        // `:hover` (links only): a new frame when the link under the pointer changes, and only
        // when an author rule names `:hover`.
        if(event.kind===3&&!press&&layered&&current?.layers.layers.hoverRules){
          const node=engine.hit(frame,event.a,pageRow(event.b))?.sourceNode;
          if(node!==hoverNode){hoverNode=node;dirty=true;}
        }
        if(event.kind===3&&press){press=[press[0],press[1],event.a,event.b];view.selection=press;dirty=true;}
        if(event.kind===4&&press){
          const released=press;press=undefined;
          if(engine.pointerUp(released)!=="click")return;
          if(view.selection){view.selection=undefined;dirty=true;}
          const target=engine.hit(frame,released[0],pageRow(released[1]));
          if(target){console.log(JSON.stringify({type:"native-html-link",...target,url:document.url}));
            const answer=engine.shellLink(target.href);
            if(answer.go!=="page"||answer.url===graphURL)go(answer);
            else if(follow)try{navigate(navigationURL(target.href,document.baseURL,document.url));}catch(error){console.error("Native HTML link refused:",String(error));}}
        }
    };
    while(running){
      const pumpStart=performance.now();if(lastPump!==undefined){pumpGaps.push(pumpStart-lastPump);if(firstFrameAt!==undefined&&lastPump>=firstFrameAt)pumpGapsLate.push(pumpStart-lastPump);if(pumpStart-lastPump>50)trace("native-html-pump-gap",{ms:ms(lastPump,pumpStart),frames:frameNumber,rendering:!!rendering});}lastPump=pumpStart;native.pump();const pumpEnd=performance.now();
      if(pumpEnd-pumpStart>30)trace("native-html-pump-stall",{ms:ms(pumpStart,pumpEnd)});
      // Take every native event now and keep each with the time it was taken. None is dropped here.
      // The window library stamps each event when it is queued; its clock maps onto
      // performance.now() through one reading of both. An older library has no clock.
      const arrived=performance.now(),queueClock=native.eventClock(),offset=queueClock===null?null:arrived-queueClock,batch:{event:UIEvent;at:number}[]=[];let taken;
      while((taken=native.next()))batch.push({event:taken,at:offset===null||!taken.time?arrived:Math.min(arrived,taken.time+offset)});
      if(batch.length){lastActivity=arrived;queueMax=Math.max(queueMax,batch.length);
        if(batch.length>QUEUE_WARN)trace("native-html-queue-high",{queued:batch.length});}
      for(const {event,at} of batch){
        if(!running)break;
        shiftedByEvent=false;eventAt=at;
        handle(event);
        // An event with a visible effect waits until a frame that includes it is presented.
        // A scroll in the band waits only for the composite at its offset.
        if(STAMPED.has(event.kind)&&shiftedByEvent){if(awaitingShift.length<256)awaitingShift.push({kind:event.kind,at});}
        else if(STAMPED.has(event.kind)&&(dirty||loading||graphBusy())){if(awaiting.length<256)awaiting.push({kind:event.kind,at});else trace("native-html-latency-overflow",{kind:event.kind});}
      }
      if(!running)break;
      const clock=(document as Page).graph;
      if(clock?.clock&&!dirty&&!rendering&&!graphBusy()&&performance.now()-clock.last>=33){
        const now=performance.now();graphInput(7,Math.min(1000,Math.floor(now-clock.last)),0);clock.last=now;
      }
      // A covered, hidden or minimized window can not present. Say so, once.
      if(dirty&&!native.canPresent()&&!waiting){waiting=true;waitingSince=performance.now();trace("native-html-waiting",{reason:"window can not present",surface:native.surfaceState()});}
      // A person's window draws when it is seen again. A sweep has no one to wait for:
      // it ends with a result, and exit code 3 says that no frames could be drawn.
      if(waiting&&(sweep||commands)&&performance.now()-waitingSince>20000){
        const result={reason:"window not visible for 20 seconds, so a sweep can not draw",surface:native.surfaceState()};
        trace("native-html-sweep-blocked",result);console.error(JSON.stringify({type:"native-html-sweep-blocked",...result}));
        Deno.exitCode=3;running=false;continue;
      }
      if(fatal)throw fatal;
      // A press or a release: present the composite with Lean's press rectangles, or with none.
      // No Lean call; it waits only for GPU work already asked for.
      if(pressPresent&&!shifting&&current&&native.canPresent()){
        pressPresent=false;
        const start=performance.now(),p=pressed;
        shifting=session!.shift(shownOffset,false).then(result=>{
          trace("native-html-press",{state:p?"down":"up",control:p?.control??null,active:p?.active??null,rects:p?.rects.length??0,
            presented:result.presented,totalMs:ms(start,performance.now()),...(p?{fromQueuedMs:ms(p.at,result.presentedAt)}:{})});
          if(!result.presented){pressPresent=true;return;}
          if(p&&p===pressed)pressOverlayMs.push(result.presentedAt-p.at);
          lastActivity=Math.max(lastActivity,performance.now());
        }).catch(error=>{fatal=error;}).finally(()=>{shifting=undefined;});
      }
      if(pressed&&!pressed.asked&&!dirty&&!rendering&&performance.now()-pressed.at>=PRESS_FRAME_MS){pressed.asked=true;dirty=true;}
      // A scroll in the band: present the composite at the new offset. A Lean frame in the
      // worker does not wait for this, and this does not wait for it.
      if(shiftPending&&!shifting&&current&&native.canPresent()){
        shiftPending=false;
        const stamps=awaitingShift;awaitingShift=[];
        // Past the band on screen, a prefetched band of the same state that keeps the scroll is drawn
        // and shown: no Lean wait. Without one, the view stays at the band edge until a band comes.
        const swap=!keeps(current.layers.layers,scroll)&&swapReady()?prefetched!:undefined;
        // Press rectangles are in the rows of the band on screen; another band needs a Lean frame.
        if(swap&&pressed&&session!.pressed){session!.setPress(undefined);dirty=true;}
        if(!swap&&!keeps(current.layers.layers,scroll)&&!bandComing())dirty=true;
        const shownLayers=swap?swap.layers:current.layers;
        const start=performance.now(),{offset,exact}=clampOffset(shownLayers.layers,scroll),at=scroll;
        shifting=(swap?session!.drawLayers(swap.layers,swap.record.width,swap.record.height,offset,everyFrame):session!.shift(offset,everyFrame)).then(result=>{
          const finished=performance.now();
          trace("native-html-scroll",{frame:frameNumber,scroll:at,offset,exact,swap:!!swap,totalMs:ms(start,finished),drawMs:Math.round(result.drawMs*10)/10,
            presented:result.presented,checked:result.checked,pixelHash:result.checked?result.pixelHash:null,...(swap?{bandTop:swap.layers.layers.bandTop,target:swap.target}:{})});
          if(swap){
            // The textures hold the prefetched layers now, presented or not.
            current={layers:swap.layers,document:swap.record.document,width:swap.record.width,height:swap.record.height};
            frame=swap.layers.page;lastRequest=swap.record;if(prefetched===swap)prefetched=undefined;
          }
          if(!result.presented){awaitingShift=[...stamps,...awaitingShift];shiftPending=true;return;}
          if(swap)prefetchStats.swaps++;
          shownOffset=offset;shifts.push(finished-start);lastActivity=Math.max(lastActivity,finished);if(result.checked)checkedFrames++;
          // A scroll past the band is not fully shown: it waits for the next band.
          if(exact){settle(stamps,result.presentedAt);settle(awaitingBand,result.presentedAt);awaitingBand=[];}
          else awaitingBand=[...awaitingBand,...stamps];
        }).catch(error=>{fatal=error;}).finally(()=>{shifting=undefined;});
      }
      // Scroll prefetch: when the scroll nears the edge of the keep range, or its speed says it
      // will pass the edge within two frames and the time of a band, the worker makes the next
      // band at low priority. Only when the worker has nothing else to do and no frame is due.
      if(layered&&worker?.alive&&!prefetching&&motion&&current&&canShift()&&!dirty&&!rendering&&!loading&&!graphBusy()&&worker.pending===0){
        const band=current.layers.layers;
        const target=prefetchTarget(band,scroll,motion,{marginRows:PREFETCH_MARGIN_ROWS,horizonMs:2*FRAME_MS+bandMs,limit:scrollLimit()});
        const request=target===undefined?undefined:requestAt(document,target);
        const key=request?stateKey(document,request.options,width,height):undefined;
        if(target!==undefined&&request&&key&&!(prefetched&&prefetched.target===target&&sameState(prefetched.key,key))){
          const record:RequestRecord={request,width,height,document},sent=performance.now(),from=scroll,client=worker;
          const job={key,target,reach:keepReach(band)};prefetching=job;prefetchStats.sent++;
          trace("native-html-prefetch",{state:"sent",scroll:from,target,keepFrom:band.keepFrom,keepTo:band.keepTo,rowsPerMs:Math.round(motion.rowsPerMs*100)/100});
          client.prefetchLayers(request.source,width,height,request.options).then(answer=>{
            const took=ms(sent,performance.now());
            if(!answer){prefetchStats.dropped++;trace("native-html-prefetch",{state:"dropped",target,ms:took});return;}
            bandMs=answer.workerMs;
            if(!running||!sameState(key,stateNow())){prefetchStats.stale++;trace("native-html-prefetch",{state:"stale",target,ms:took});return;}
            prefetched={key,layers:answer.layers,target,record};prefetchStats.ready++;
            trace("native-html-prefetch",{state:"ready",target,bandTop:answer.layers.layers.bandTop,keepFrom:answer.layers.layers.keepFrom,keepTo:answer.layers.layers.keepTo,
              ms:took,workerMs:Math.round(answer.workerMs*10)/10,scroll});
          }).catch(error=>{prefetchStats.dropped++;trace("native-html-prefetch",{state:"failed",target,reason:String(error)});}).finally(()=>{
            if(prefetching===job)prefetching=undefined;
            // A scroll that waited for this band: show it now, or ask Lean for a frame.
            if(!running||!current||current.document!==document||keeps(current.layers.layers,scroll))return;
            if(swapReady())shiftPending=true;
            else if(!bandComing()){prefetchStats.missed++;dirty=true;}
          });
        }
      }
      if(dirty&&native.canPresent()&&!rendering){
        waiting=false;
        rendering=renderFrame().catch(error=>{fatal=error;}).finally(()=>{rendering=undefined;});
      } else if(!everyFrame&&!dirty&&!rendering&&!shifting&&!shiftPending&&!pressed&&!pressPresent&&session?.frames&&!session.lastChecked&&native.canPresent()&&performance.now()-lastActivity>=IDLE_CHECK_MS){
        // Interactive frames are not read back. When input has been idle, the last frame is drawn again with the checks.
        rendering=idleCheck().catch(error=>{fatal=error;}).finally(()=>{rendering=undefined;});
      }
      // A repeatable measurement: step the window through fixed sizes, then exit.
      if(sweep&&!dirty&&!rendering&&!graphBusy()&&session?.frames){
        const size=sweep.shift();
        if(size)native.setContentSize(size[0],size[1]);else running=false;
      }
      // Each step runs on a settled page: a key through real menu matching, or an input event.
      // A scroll step with layers waits only for the composite of the step before, 16 ms apart:
      // a Lean frame for a new band runs meanwhile, as when a person scrolls.
      const scrollStep=layered&&Array.isArray(commands?.[0])&&(commands![0] as number[])[0]===11;
      const settled=!dirty&&!rendering&&!graphBusy()&&!loading&&!shiftPending&&!shifting;
      if(commands&&session?.frames&&performance.now()>=stepAt&&(settled||(scrollStep&&!loading&&!shiftPending&&!shifting&&performance.now()-lastStep>=16))){
        lastStep=performance.now();
        const step=commands.shift();
        if(step==="graph")shellCommand("graph","");
        else if(typeof step==="string"&&step.startsWith("link")){
          // A press and release on a link of the page: link is the first, link1 the second.
          const link=frame.webRender.links[Number(step.slice(4))] as number[],x=Math.round(link[2]+link[4]/2),y=Math.round(windowRow(link[3]+link[5]/2));
          native.testEvent(2,x,y);native.testEvent(4,x,y);
        }
        else if(step==="settle")trace("native-html-paste",{url:document.url,title:document.title});
        else if(step==="hold")stepAt=performance.now()+300;
        else if(step==="press-link"){
          const link=frame.webRender.links[0] as number[];pressAt=[Math.round(link[2]+link[4]/2),Math.round(windowRow(link[3]+link[5]/2))];
          native.testEvent(2,pressAt[0],pressAt[1]);
        }
        else if(step==="press-reload"){
          // The reload button's centre: WebShell.boxes at this scale, checked with Lean's hit.
          pressAt=[78*scale,44*scale];
          if(engine.shellHit(shell(),pressAt[0],pressAt[1],width)!=="reload")trace("native-html-press",{state:"sweep-miss",at:pressAt});
          native.testEvent(2,pressAt[0],pressAt[1]);
        }
        else if(step==="release")native.testEvent(4,pressAt[0],pressAt[1]);
        else if(typeof step==="string"&&step.startsWith("url:")){
          const ok=document.url.endsWith(step.slice(4));trace("native-html-test-url",{expected:step.slice(4),url:document.url,ok});
          if(!ok){console.error(`Native HTML sweep: expected a page ending ${step.slice(4)}, shown ${document.url}`);Deno.exitCode=1;}
        }
        else if(typeof step==="string"&&step.startsWith("pointer:")){
          const ok=pointerShown===step.slice(8);trace("native-html-test-pointer",{expected:step.slice(8),pointer:pointerShown,ok});
          if(!ok){console.error(`Native HTML sweep: expected the ${step.slice(8)} pointer, shown ${pointerShown}`);Deno.exitCode=1;}
        }
        else if(step==="overLink"){
          const link=frame.webRender.links[0] as number[];
          native.testEvent(3,Math.round(link[2]+link[4]/2),Math.round(windowRow(link[3]+link[5]/2)));
        }
        else if(step==="back"){
          // The chrome's back button, found through Lean's own hit test of the chrome.
          let at:number[]|undefined;
          for(let y=0;y<200&&!at;y+=2)for(let x=0;x<200&&!at;x+=2)if(engine.shellHit(shell(),x,y,width)==="back")at=[x+4,y+4];
          if(!at)throw new Error("back sweep: no back button in the chrome");
          native.testEvent(2,at[0],at[1]);native.testEvent(4,at[0],at[1]);
        }
        else if(step==="print"){
          const done=await printDocument(printPDF);
          if(!done){console.error("Native HTML print sweep: no PDF");Deno.exitCode=1;}
        }
        else if(typeof step==="string"&&/^(focus:all|unfocused|addr=|sel=|clip=)/.test(step)){
          const url=step.endsWith("@url")?document.url:undefined,value=step.slice(step.indexOf("=")+1);
          const selected=field.address.slice(Math.min(field.anchor,field.cursor),Math.max(field.anchor,field.cursor));
          const ok=step==="focus:all"?focused&&field.anchor===0&&field.cursor===field.address.length&&field.address===document.url
            :step==="unfocused"?!focused
            :step.startsWith("addr=")?field.address===(url??value)
            :step.startsWith("sel=")?selected===value
            :native.readClipboard()===value;
          trace("native-html-test-edit",{step,ok,address:field.address,anchor:field.anchor,cursor:field.cursor,focused});
          if(!ok){console.error(`Native HTML edit sweep: ${step} failed; address ${JSON.stringify(field.address)}, selection ${JSON.stringify(selected)}, focused ${focused}`);Deno.exitCode=1;}
        }
        else if(typeof step==="string")trace("native-html-test-key",{key:step,handled:native.testKey(step,"+_Z".includes(step))});
        else if(step)native.testEvent(step[0],step[1],step[2]);else{if(native.readClipboard()===lastCopied)native.writeClipboard(savedClipboard);running=false;}
      }
      // Wake at least every 8 ms to pump; wake at once when a frame ends.
      const nap=new Promise(resolve=>setTimeout(resolve,8));
      await Promise.race([nap,...(rendering?[rendering]:[]),...(shifting?[shifting]:[])]);
    }
  } finally {
    running=false;controller?.abort();
    // A frame in progress ends before its session is disposed.
    try{await rendering;await shifting;}catch(error){console.error("Native HTML frame ended with an error:",String(error));}
    worker?.terminate();
    try{summary();}catch(error){console.error("Native HTML summary failed:",String(error));}
    if(!cleanupUI({session,device,native}))Deno.exitCode=1;
  }
}
try{await main();}catch(error){console.error(error);Deno.exitCode=1;}
// Match the existing native UI: do not unload Cocoa classes under a live NSView.
Deno.exit(Deno.exitCode);
