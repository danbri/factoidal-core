import {loadHTML,type HTMLArtifact,type HTMLLayers,type HistoryAnswer} from "./native_html_engine.ts";
import {clampOffset,keeps} from "./layer_compositor.ts";
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
    console.log("Native HTML: --html FILE | --url HTTP_OR_HTTPS_URL [--font FONT_FILE] [--bitmap-font] [--follow-links] [--check-engine] [--trace-input] [--resize-sweep] [--command-sweep] [--history-sweep] [--graph-sweep] [--scroll-sweep] [--single-frame] [--check-pixels] [--perf-summary] [--idle-checks-only] [--native-engine DYLIB | --wasm-engine]\nCommand-Q quits; R reloads; Command-Left and Command-[ go back; Command-Right and Command-] go forward; Command-= and Command-- zoom text; Command-0 resets; drag selects; Command-A and Command-C select and copy. HTML/CSS/layout/link picking run in published Lean WASM. No scripts, scrolling, WebView or supplied fonts in this milestone.");return;
  }
  let url:string|undefined,follow=false,check=false,traceInput=false,sweep:number[][]|undefined,commands:(string|number[])[]|undefined,pasted:string|undefined,bitmapFont=false,fontFile:string|undefined,checkAll=false,idleChecksOnly=false,perfSummary=false,nativeEngine:string|undefined,wasmEngine=false,layered=true;
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
    else if(arg==="--native-engine"){nativeEngine=args.shift();if(!nativeEngine)throw new Error("--native-engine needs a dylib path");}
    else if(arg==="--font")fontFile=args.shift();
    else if(arg==="--bitmap-font")bitmapFont=true;
    else if(arg==="--resize-sweep")sweep=[[800,500],[700,500],[600,500],[500,500],[400,500],[800,300],[800,500]];
    else if(arg==="--paste-sweep")pasted=args.shift();
    else if(arg==="--command-sweep")commands=["=","+","-","_","0","a","c",[2,60,60],[3,300,60],[4,300,60],"c",[2,60,60],[4,60,60],"link"];
    else if(arg==="--graph-sweep")commands=["graph",[2,800,565],[3,900,640],[3,1000,720],[4,1000,720]];
    // Twenty scroll steps of 120 backing pixels down the page: per-step frame time and input latency.
    else if(arg==="--scroll-sweep")commands=Array.from({length:20},()=>[11,-120,0]);
    else if(arg==="--history-sweep")commands=["left","link","left","right","[","]","]","[","link1","]","[","]"];
    else throw new Error(`Unknown native HTML argument: ${arg}`);
  }
  // Lean engine for compile: --native-engine PATH, else libweb-render.dylib beside the program, else Wasm.
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
  type Lean=Pick<typeof engine,"xmlStylesheet"|"xslt"|"inspect"|"compile"|"selectedText"|"graphStart"|"graphEvent"|"graphPage"|"sourcePage">;
  let lean:Lean=engine;
  const useMainEngine=async(reason:string)=>{
    console.error("Native HTML: ENGINE WORKER UNAVAILABLE, so Lean runs on the main thread and the window can miss input:",reason);
    console.log(JSON.stringify({type:"native-html-worker",state:"main-thread-fallback",reason}));
    worker=undefined;lean=engine;
    if(workerFont&&!mainFont){mainFont=true;try{await loadFontFile(engine,workerFont.path,workerFont.family);}catch(error){if(fontFile)throw error;workerFont=undefined;}}
  };
  if(check){
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
    if(worker)lean=worker.engine as unknown as Lean;
  }
  let document=await prepareHTML(lean,url),width=1280,height=800;
  // The first compile runs in the worker too: it warms the worker, and no frame is compiled on the main thread.
  let frame:HTMLArtifact=await document.compile(width,height);
  console.log(JSON.stringify({type:"native-html-loaded",url:document.url,primitives:frame.primitiveCount,links:frame.webRender.links.length,width,height}));
  if(check){
    // Synthetic limits exercise only the published planner ABI. Window rendering
    // always passes the real device limits in createHTMLWindowSession.
    const plan=await requestRenderPlan("svg-offscreen","rgba8unorm",frame,{
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
  // Session history is a Lean value. The host keeps it and loads the URLs Lean returns.
  let history=engine.historyPush({entries:[],index:0},document.url);
  // The chrome is a Lean value too. The host stores it and shows what Lean draws.
  const home=document;
  let checked:typeof document|undefined;
  let address=document.url,cursor=0,focused=false,fresh=false,theme="next",pages=1,scale=1,active=0,scroll=0;
  const tabs:{document:typeof document;history:typeof history;scroll:number}[]=[{document,history,scroll:0}];
  const shell=()=>({tabs:tabs.map((tab,index)=>({title:(index===active?document:tab.document).title??""})),active,address,cursor,focused,
    canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll});
  const shown=()=>({...view,shell:shell()});
  const showTab=(index:number)=>{
    controller?.abort();candidate=undefined;loading=false;focused=false;active=index;
    ({document,history,scroll}=tabs[index]);address=document.url;dirty=true;
    native?.setHistory(history.canBack,history.canForward);
  };
  const keepTab=()=>{tabs[active]={document,history,scroll};};
  const newTab=()=>{keepTab();tabs.push({document:home,history:engine.historyPush({entries:[],index:0},home.url),scroll:0});showTab(tabs.length-1);};
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
    if(frame.commands.includes("render")){page.source=await lean.graphPage(frame.model);dirty=true;}
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
  const openGraph=async()=>{
    const rdf=await Deno.readTextFile(new URL("./pages/foaf-demo.ttl",import.meta.url));
    const frame=await lean.graphStart(rdf,width,height,shell());
    const page={url:"foafnaut:graph",baseURL:"foafnaut:graph",title:"FOAF graph",source:await lean.graphPage(frame.model),sources:[] as typeof document.sources,
      graph:{model:frame.model,clock:false,last:0},
      request(_w:number,_h:number,view:PageView={}){return {source:page.source,options:{url:page.url,resources:[],...view} as Record<string,unknown>};},
      compile(w:number,h:number,view:PageView={}){return lean.compile(page.source,w,h,{url:page.url,resources:[],...view});},
      selectedText:()=>""} as unknown as Page;
    await graphFrame(page,frame);
    keepTab();tabs.push({document:page,history:engine.historyPush({entries:[],index:0},page.url),scroll:0});showTab(tabs.length-1);
  };
  const focusAddress=()=>{focused=true;fresh=true;address=document.url;cursor=address.length;dirty=true;};
  const leaveAddress=()=>{focused=false;address=document.url;dirty=true;};
  const scrollBy=(amount:number)=>{
    const boxes=frame.webRender.boxes as number[][]|undefined;
    const bottom=Math.max(0,...(boxes??[]).map(box=>box[2]+box[4]));
    const limit=Math.max(0,bottom-height+Math.round(60*scale));
    const next=Math.max(0,Math.min(limit,scroll+Math.round(amount)));
    if(next===scroll)return;
    scroll=next;
    // Inside the band of the layers on screen, a scroll only moves the composite: no Lean call.
    // Lean's keep range says when to ask for a new band; until it comes, the view stays in the old one.
    if(canShift()){shiftPending=true;shiftedByEvent=true;if(!keeps(current!.layers.layers,scroll))dirty=true;}
    else dirty=true;
  };
  // The layers on screen, and the page row of the band shown at the top of the view.
  let current:{layers:HTMLLayers;document:typeof document;width:number;height:number}|undefined,shownOffset=0;
  let shiftPending=false,shiftedByEvent=false;
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
    else if(name==="graph")openGraph().catch(error=>refuse("foafnaut:graph",error));
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
  const edit=(answer:{address:string;cursor:number})=>{({address,cursor}=answer);fresh=false;dirty=true;};
  const remember=(answer:HistoryAnswer,action:string)=>{
    history=answer;native?.setHistory(answer.canBack,answer.canForward);
    if(action==="push")pages++;
    trace("native-html-history",{action,index:answer.history.index,size:answer.history.entries.length,url:answer.url});
  };
  const windowCommand=(id:number)=>{
    const answer=engine.command(id,view.textScalePercent??100,history.history);
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
    // Paste always lands in the address bar: it is the only text field there is.
    if(answer.action==="paste"){
      if(!focused)focusAddress();
      if(fresh){address="";cursor=0;}
      edit(engine.shellText(shell(),native!.readClipboard().replace(/\s*[\r\n]+\s*/g,"").trim()));
    }
    if(answer.action==="viewSource")viewSource().catch(error=>refuse(document.url,error));
    if(answer.action==="selectAll"){view.selection="all";dirty=true;}
    if(answer.action==="copy"&&view.selection){
      // The selected text is made in the worker; the clipboard is written when it arrives.
      Promise.resolve(document.selectedText(width,height,shown())).then(text=>{
        if(text){native!.writeClipboard(text);lastCopied=text;trace("native-html-copy",{characters:text.length});}
      }).catch(error=>console.error("Native HTML copy failed:",String(error)));
    }
  };
  // A new page goes into history when its load ends, and a refused page does too.
  const navigate=(target:string,push=true)=>{
    controller?.abort();candidate=undefined;controller=new AbortController();const current=controller;loading=true;
    console.log(JSON.stringify({type:"native-html-loading",url:target}));
    prepareHTML(lean,target,current.signal).then(next=>{
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
  let lastStep=0;
  let lastActivity=performance.now(),queueMax=0,fatal:unknown,rendering:Promise<void>|undefined;
  let awaiting:{kind:number;at:number}[]=[],awaitingShift:{kind:number;at:number}[]=[],checkedFrames=0,workerFrames=0,mainFrames=0;
  let shifting:Promise<void>|undefined;const shifts:number[]=[];
  const latencies:number[]=[],totals:number[]=[],pumpGaps:number[]=[],pumpGapsLate:number[]=[];let lastPump:number|undefined,firstFrameAt:number|undefined;
  const percentile=(values:number[],q:number)=>{if(!values.length)return null;const sorted=[...values].sort((a,b)=>a-b);return Math.round(sorted[Math.min(sorted.length-1,Math.ceil(q*sorted.length)-1)]*10)/10;};
  // Latency starts when the window library queued the event, or at dequeue with an older library.
  const latencyFrom=()=>native?.eventClock()===null?"dequeued":"queued";
  // Exit summary: input to present latency, and frame totals. Always traced; --perf-summary also prints it.
  const summary=()=>{
    const line={type:"native-html-perf-summary",inputEventsDropped:native?.eventsDropped()??0,inputLatency:{from:latencyFrom(),count:latencies.length,p50Ms:percentile(latencies,0.5),p95Ms:percentile(latencies,0.95),maxMs:latencies.length?Math.max(...latencies):null},
      compileBackend:nativeEngine?"native":"wasm",layered,
      scrollPresents:{count:shifts.length,totalMsP50:percentile(shifts,0.5),totalMsP95:percentile(shifts,0.95),maxMs:shifts.length?Math.round(Math.max(...shifts)*10)/10:null},
      frames:{presented:totals.length,checked:checkedFrames,compiledInWorker:workerFrames,compiledOnMain:mainFrames,totalMsP50:percentile(totals,0.5),totalMsP95:percentile(totals,0.95)},
      // Time between two native event pumps: the longest time the window takes no input.
      // After the first frame is presented: the figure the 50 ms target is judged on.
      pumpGapAfterFirstFrameMs:{count:pumpGapsLate.length,p50:percentile(pumpGapsLate,0.5),p95:percentile(pumpGapsLate,0.95),max:pumpGapsLate.length?Math.round(Math.max(...pumpGapsLate)*10)/10:null},
      slowCalls,
      pumpGapMs:{p50:percentile(pumpGaps,0.5),p95:percentile(pumpGaps,0.95),max:pumpGaps.length?Math.round(Math.max(...pumpGaps)*10)/10:null},
      queueMax,sessionStats:session?.stats};
    trace(line.type,line);
    if(perfSummary)console.log(`input latency: ${line.inputLatency.count} events, p50 ${line.inputLatency.p50Ms} ms, p95 ${line.inputLatency.p95Ms} ms, max ${line.inputLatency.maxMs} ms\nframes: ${line.frames.presented} presented (${line.frames.checked} checked), totalMs p50 ${line.frames.totalMsP50}, p95 ${line.frames.totalMsP95}; pipeline builds ${session?.stats.pipelineBuilds}\nscroll presents with no Lean call: ${line.scrollPresents.count}, totalMs p50 ${line.scrollPresents.totalMsP50}, p95 ${line.scrollPresents.totalMsP95}, max ${line.scrollPresents.maxMs}\npump gap after first frame: p50 ${line.pumpGapAfterFirstFrameMs.p50} ms, p95 ${line.pumpGapAfterFirstFrameMs.p95} ms, max ${line.pumpGapAfterFirstFrameMs.max} ms\npump gap all: p50 ${line.pumpGapMs.p50} ms, p95 ${line.pumpGapMs.p95} ms, max ${line.pumpGapMs.max} ms`);
  };
  try {
    device=await adapter.requestDevice();native=await nativePreflight(()=>loadNativeWindow());
    native.setInputTrace(traceInput);native.setHistory(history.canBack,history.canForward);
    // The command sweep copies text. It gives the clipboard back unless the person
    // copied something else meanwhile.
    const savedClipboard=commands||pasted?native.readClipboard():"";
    // Paste a URL into the address bar through the real menu key, then press Return.
    if(pasted){native.writeClipboard(pasted);lastCopied=pasted;commands=["v",[5,36,0],"settle"];}
    const windowTitle=(page:typeof document)=>page.title?`foafnaut - ${page.title}`:"foafnaut";
    const handles=native.create(800,500,windowTitle(document));
    const surface=new Deno.UnsafeWindowSurface(cocoaSurfaceOptions(handles,width,height));
    native.showAfterSurface();
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
    const everyFrame=checkAll||(!idleChecksOnly&&(!!sweep||!!commands));
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
      const view0=shown();if(nextDocument!==document)view0.shell={...view0.shell,scroll:0};
      const request=nextDocument.request(width,height,{...view0,live:nextDocument===checked,...(everyFrame?{}:{checks:false})});
      const sentWidth=width,sentHeight=height;
      // Events from here on mark the page dirty again: latest state wins, in the next frame.
      dirty=false;
      let next:HTMLArtifact,nextLayers:HTMLLayers|undefined,where="worker",workerMs:number|undefined;
      try{
        if(layered){
          if(worker?.alive){({layers:nextLayers,workerMs}=await worker.compileLayers(request.source,sentWidth,sentHeight,request.options));}
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
      const result=nextLayers?await session!.drawLayers(nextLayers,sentWidth,sentHeight,place!.offset,everyFrame):await session!.draw(next,everyFrame);
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
        if(place!.exact){settle(awaitingShift,result.presentedAt);awaitingShift=[];}
        if(nextDocument===document&&!keeps(nextLayers.layers,scroll))dirty=true;
      } else current=undefined;
      checked=nextDocument;
      if(nextDocument!==document)view.selection=undefined;
      if(nextDocument!==document){scroll=0;if(!focused)address=nextDocument.url;}frame=next;document=nextDocument;candidate=undefined;native!.setTitle(windowTitle(document));
      console.log(JSON.stringify({type:"native-html-presented",url:document.url,width:sentWidth,height:sentHeight,primitives:frame.primitiveCount,links:frame.webRender.links.length,frames:session!.frames}));
    };
    let lastRequest:{request:ReturnType<typeof document.request>;width:number;height:number;document:typeof document}|undefined;
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
        if(event.kind===1){
          if(event.a<1||event.b<1)return;
          if(event.a>4096||event.b>4096)throw new Error("Native HTML window exceeds 4096 backing pixels; close or use a smaller window");
          if(event.a!==width||event.b!==height){width=event.a;height=event.b;dirty=true;if((document as Page).graph)graphInput(1,width,height);resizeAt??=performance.now();trace("native-html-resize",{width,height});}
        }
        if(event.kind===8&&event.a)dirty=true;
        const graph=(document as Page).graph;
        if(graph&&!focused&&(event.kind===3||event.kind===4||event.kind===9||(event.kind===5&&!(event.b&2)))){graphInput(event.kind,event.a,event.b);return;}
        if(event.kind===5&&focused&&!(event.b&2)){
          if(event.a===36){const target=address;leaveAddress();go(engine.shellSubmit(target));}
          else if(event.a===53)leaveAddress();
          else if(event.a===51&&fresh)edit({address:"",cursor:0});
          else edit(engine.shellKey(shell(),event.a));
          return;
        }
        if(event.kind===9&&focused){
          if(fresh){address="";cursor=0;}
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
          const control=engine.shellHit(shell(),event.a,event.b,width);
          if(control){chrome(control);return;}
          if(focused)leaveAddress();
          if((document as Page).graph){graphInput(2,event.a,event.b);return;}
          press=[event.a,event.b,event.a,event.b];
          if(view.selection){view.selection=undefined;dirty=true;}
        }
        if(event.kind===3&&press){press=[press[0],press[1],event.a,event.b];view.selection=press;dirty=true;}
        if(event.kind===4&&press){
          const released=press;press=undefined;
          if(engine.pointerUp(released)!=="click")return;
          if(view.selection){view.selection=undefined;dirty=true;}
          const target=engine.hit(frame,released[0],pageRow(released[1]));
          if(target){console.log(JSON.stringify({type:"native-html-link",...target,url:document.url}));
            const answer=engine.shellLink(target.href);
            if(answer.go!=="page")go(answer);
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
        shiftedByEvent=false;
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
      // A scroll in the band: present the composite at the new offset. A Lean frame in the
      // worker does not wait for this, and this does not wait for it.
      if(shiftPending&&!shifting&&current&&native.canPresent()){
        shiftPending=false;
        const stamps=awaitingShift;awaitingShift=[];
        const start=performance.now(),{offset,exact}=clampOffset(current.layers.layers,scroll),at=scroll;
        shifting=session!.shift(offset,everyFrame).then(result=>{
          const finished=performance.now();
          trace("native-html-scroll",{frame:frameNumber,scroll:at,offset,exact,totalMs:ms(start,finished),drawMs:Math.round(result.drawMs*10)/10,
            presented:result.presented,checked:result.checked,pixelHash:result.checked?result.pixelHash:null});
          if(!result.presented){awaitingShift=[...stamps,...awaitingShift];shiftPending=true;return;}
          shownOffset=offset;shifts.push(finished-start);lastActivity=Math.max(lastActivity,finished);if(result.checked)checkedFrames++;
          // A scroll past the band is not fully shown: it waits for the next Lean frame.
          if(exact)settle(stamps,result.presentedAt);else awaiting=[...stamps,...awaiting];
        }).catch(error=>{fatal=error;}).finally(()=>{shifting=undefined;});
      }
      if(dirty&&native.canPresent()&&!rendering){
        waiting=false;
        rendering=renderFrame().catch(error=>{fatal=error;}).finally(()=>{rendering=undefined;});
      } else if(!everyFrame&&!dirty&&!rendering&&!shifting&&!shiftPending&&session?.frames&&!session.lastChecked&&native.canPresent()&&performance.now()-lastActivity>=IDLE_CHECK_MS){
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
      if(commands&&session?.frames&&(settled||(scrollStep&&!loading&&!shiftPending&&!shifting&&performance.now()-lastStep>=16))){
        lastStep=performance.now();
        const step=commands.shift();
        if(step==="graph"){shellCommand("graph","");loading=true;setTimeout(()=>{loading=false;},600);}
        else if(typeof step==="string"&&step.startsWith("link")){
          // A press and release on a link of the page: link is the first, link1 the second.
          const link=frame.webRender.links[Number(step.slice(4))] as number[],x=Math.round(link[2]+link[4]/2),y=Math.round(windowRow(link[3]+link[5]/2));
          native.testEvent(2,x,y);native.testEvent(4,x,y);
        }
        else if(step==="settle")trace("native-html-paste",{url:document.url,title:document.title});
        else if(typeof step==="string")trace("native-html-test-key",{key:step,handled:native.testKey(step,"+_".includes(step))});
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
