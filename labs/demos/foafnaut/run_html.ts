import {loadHTML,type HTMLArtifact,type HTMLLayers,type HistoryAnswer,type ShellEdit} from "./native_html_engine.ts";
import {printImages,pdfPageCount,DEFAULT_PAPER} from "./native_print.ts";
import {clampOffset,keeps} from "./layer_compositor.ts";
import {prefetchTarget,trackMotion,stateKey,sameState,canSwap,keepReach,PREFETCH_MARGIN_ROWS,FRAME_MS,type Motion,type StateKey} from "./scroll_prefetch.ts";
import {inputURL,loadFontFile,prepareHTML,refusalHTML,setFontHost,setPageDecoding,setScriptHost,type PageView} from "./native_html_document.ts";
import {fallbackFontHost,loadFallbackFonts,mayNeedFallbackFonts,type FallbackFont,type PageFonts} from "./native_html_fonts.ts";
import type {ScriptPlan,ScriptTurn} from "./native_html_engine.ts";
import {addEntries,consoleRequest,noteDiagnostics} from "./native_console.ts";
import {createGpuGuard} from "./gpu_pacing.ts";
import {loadNativeWindow} from "./native_window.ts";
import {POINTER_CANCEL,beginPress,movePress,pointerNode,pointerRequest,pressPointers,beforeFirstFrame,type NativePress,type PointerKind,type PresentedState} from "./native_press.ts";
import {nativePreflight} from "./native_preflight.ts";
import {cocoaSurfaceOptions} from "./cocoa_surface.ts";
import {createHTMLWindowSession,type PresentTarget} from "./native_html_session.ts";
import {hostState,STATE_PAGES,STATE_COMMANDS} from "./native_state.ts";
import {cleanupUI} from "./ui_cleanup.ts";
import {createRouter} from "../../../docs/web/hub/foafnaut/link-route.mjs";
import type {LinkRoute} from "./native_html_engine.ts";
import {requestRenderPlan} from "./render_plan.ts";
import {pngOf,texturePixels} from "./png_write.ts";
import {startCompileWorker,type CompileClient} from "./native_html_compile.ts";
import type {UIEvent} from "./ui_engine.ts";

/** What this program was built from: the record build-executables.sh compiles into it. */
async function buildInfo():Promise<{commit?:string;dirty?:boolean;builtAt?:string}> {
  try{return JSON.parse(await Deno.readTextFile(new URL("./.build/native-html/build-info.json",import.meta.url)));}
  catch{return {};} // run from source with no app build
}
async function main() {
  const args=[...Deno.args];
  // What this program was built from: the record build-executables.sh compiled into it.
  if(args.includes("--version")){
    const info=await buildInfo();
    console.log(info.commit?`foafnaut ${info.commit}${info.dirty?" (with uncommitted changes)":""}, built ${info.builtAt}`:"foafnaut: no build record (run from source, or an older build)");
    return;
  }
  if(args.includes("--help")){
    console.log("Native HTML: --html FILE | --url HTTP_OR_HTTPS_URL [--font FONT_FILE] [--bitmap-font] [--follow-links] [--check-engine] [--trace-input] [--resize-sweep] [--command-sweep] [--history-sweep] [--back-sweep] [--graph-sweep] [--edit-sweep] [--shortcut-sweep] [--print-pdf FILE] [--scroll-sweep] [--watch-sweep SECONDS] [--single-frame] [--offscreen] [--check-pixels] [--perf-summary] [--idle-checks-only] [--native-engine DYLIB | --wasm-engine] [--no-state] [--state-dir DIR] [--restore-session] [--quickjs-wasm FILE | --no-scripts] [--strict | --be-liberal-in-what-we-accept]\nCommand-Q quits; Command-R and R reload; Command-T, Command-W and Shift-Command-T open, close and reopen tabs; Command-1 to 9, Control-Tab and Shift-Command-[ ] change tab; Space, Page Up, Page Down, Home, End and arrows scroll; Escape stops loading; Command-Left and Command-[ go back; Command-Right and Command-] go forward; Command-= and Command-- zoom text; Command-0 resets; drag selects; Command-A, Command-C, Command-X, Command-V and Command-Z edit the address bar when it has the focus, else select and copy page text; Command-P prints; Option-Command-J opens the console tab (foafnaut:console). By default the browser draws a page without what the built-in engine may skip (module scripts, media conditions it can not read, stylesheets not fetched, scripts when they are off, inline SVG it can not draw) and lists each skip in the console; --strict refuses such a page. HTML/CSS/layout/link picking run in published Lean WASM. Page scripts run in QuickJS-NG inside Lean's WasmVM, with Lean's DOM and event loop, when the guest module is found (--quickjs-wasm FILE, default ~/working/qjs-wasm/qjs-wasmvm.wasm); else a page with scripts is refused. No WebView.");return;
  }
  let scrollSweep=false,watchSeconds=0,framesInFlight=1;
  let shotFile:string|undefined;
  let url:string|undefined,follow=false,check=false,traceInput=false,sweep:number[][]|undefined,commands:(string|number[])[]|undefined,pasted:string|undefined,quickjsWasm:string|undefined,scriptsOff=false,bitmapFont=false,fontFile:string|undefined,checkAll=false,idleChecksOnly=false,perfSummary=false,nativeEngine:string|undefined,wasmEngine=false,layered=true,pressLook=true,printPDF:string|undefined,stateDir:string|undefined,stateOff=false,restoreSession=false,offscreen=false,swipeSweep=false,cliLiberal=false,cliStrict=false;
  while(args.length){const arg=args.shift();
    if(arg==="--html"||arg==="--url"){
      const value=args.shift();if(!value||url)throw new Error("Supply exactly one --html FILE or --url URL");
      url=inputURL(value,arg==="--html");
    } else if(arg==="--follow-links")follow=true;
    else if(arg==="--check-engine")check=true;
    else if(arg==="--trace-input")traceInput=true;
    else if(arg==="--check-pixels")checkAll=true;
    else if(arg==="--perf-summary")perfSummary=true;
    // Off screen: a PNG of the window after the 120th present of page canvases, a picture of
    // what the native engine drew (the page's layers, its canvases and the chrome).
    else if(arg==="--shot"){shotFile=args.shift();if(!shotFile)throw new Error("--shot needs a file path");}
    // No visible window (issue 1268): frames are drawn into a GPU texture of the window size, and
    // events go through the window library's queue as before, from a window that is never shown.
    // Sweeps then run with the screen locked, the display asleep, or on a machine with no display.
    else if(arg==="--offscreen")offscreen=true;
    // Browser state in a local LWS server (native_state.ts): on in an interactive window, off in sweeps and checks.
    else if(arg==="--no-state")stateOff=true;
    else if(arg==="--state-dir"){stateDir=args.shift();if(!stateDir)throw new Error("--state-dir needs a folder");}
    else if(arg==="--restore-session")restoreSession=true;
    // Sweeps read back every frame. This flag gives them the interactive rule (check when idle), to measure input latency without the check cost.
    else if(arg==="--idle-checks-only")idleChecksOnly=true;
    else if(arg==="--wasm-engine")wasmEngine=true;
    // One Lean frame for each scroll step, as before the two layers (for comparison).
    else if(arg==="--single-frame")layered=false;
    // No press look (no darkening, no :active frame): the behaviour before issue 1268, for comparison.
    else if(arg==="--no-press-look")pressLook=false;
    else if(arg==="--native-engine"){nativeEngine=args.shift();if(!nativeEngine)throw new Error("--native-engine needs a dylib path");}
    else if(arg==="--font")fontFile=args.shift();
    else if(arg==="--quickjs-wasm"){quickjsWasm=args.shift();if(!quickjsWasm)throw new Error("--quickjs-wasm needs a file");}
    else if(arg==="--no-scripts")scriptsOff=true;
    // Liberal mode (WebAccept.lean): Lean skips what it may skip and says so in the console.
    else if(arg==="--be-liberal-in-what-we-accept")cliLiberal=true;
    // Strict mode: a page with a feature the built-in engine may skip is refused. Tests,
    // sweeps and WPT runs give it, so their results do not depend on the default.
    else if(arg==="--strict")cliStrict=true;
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
    // Tab and scroll keys of Lean's key table through the real menu and key path (issue 1268):
    // "tabs=N:A" checks N tabs with tab A shown; "scroll=0" and "scroll=end" check the scroll.
    else if(arg==="--shortcut-sweep")commands=["t","t","tabs=3:2","1","tabs=3:0","9","tabs=3:2","{","tabs=3:1","}","tabs=3:2",
      "w","tabs=2:1","T","tabs=3:2","1",[5,119,0],"scroll=end",[5,115,0],"scroll=0",[5,121,0],[5,126,2],"scroll=0","r","tabs=3:0"];
    // Print to a PDF with no panel, then check its page count (issue 1268).
    else if(arg==="--print-pdf"){printPDF=args.shift();if(!printPDF)throw new Error("--print-pdf needs a file path");commands=["print"];}
    else if(arg==="--graph-sweep")commands=["graph",[2,800,565],[3,900,640],[3,1000,720],[4,1000,720]];
    // Twenty scroll steps of 120 backing pixels down the page: per-step frame time and input latency.
    // Watch a page that moves by itself (an SVG animation, page script timers) for N seconds
    // after its first frame, then exit: frame times of an animation with no input.
    else if(arg==="--watch-sweep")watchSeconds=Number(args.shift())||5;
    // GPU submissions that may be in flight (gpu_pacing.ts). 0 lifts the bound: for measurement only.
    else if(arg==="--gpu-frames-in-flight")framesInFlight=Math.max(0,Math.floor(Number(args.shift())));
    else if(arg==="--scroll-sweep"){commands=Array.from({length:20},()=>[11,-120,0]);scrollSweep=true;}
    // Scroll to the end of the page, then check that the last row of the layout is in the
    // view, and hold the window still for a screenshot (issue 1270 report: long SVG pages).
    else if(arg==="--scroll-end-sweep")commands=[...Array.from({length:60},()=>[11,-600,0]),...Array.from({length:20},()=>"hold"),"end"];
    // Each page link of the page (showcase.html): wheel steps down to it (in the band and
    // past it), the hand pointer over it, a click at its drawn place, the page it names,
    // and back (issue 1268 report: a showcase link below the first screen did nothing).
    else if(arg==="--link-scroll-sweep")commands=["pageLinks"];
    else if(arg==="--history-sweep")commands=["left","link","left","right","[","]","]","[","link1","]","[","]"];
    // Press and hold a link, then the reload button, then release each (issue 1268): the
    // press acknowledgement, the Lean frame of a held press, and the release.
    else if(arg==="--press-sweep")commands=["press-link","hold","release","hold","press-reload","hold","release","hold"];
    // Back and forward to and from the FOAF graph page (issue 1268): the index's first link opens it;
    // "url:X" fails the run unless the page shown ends with X; "back" presses the chrome's back button.
    else if(arg==="--back-sweep")commands=["overLink","pointer:hand",[3,640,780],"pointer:arrow","link","url:foafnaut:graph",[2,640,500],[4,640,500],"[","url:index.html","]","url:foafnaut:graph",
      [2,700,450],[3,720,470],[4,720,470],"back","url:index.html","right","url:foafnaut:graph","left","url:index.html"];
    // A trackpad swipe back and one forward (WebGesture.lean), as kind 12 events: began,
    // 400 backing px across, ended. A vertical one and a short one go nowhere.
    else if(arg==="--swipe-sweep"&&(swipeSweep=true))commands=["link","url:foafnaut:graph",[12,0,65537],[12,400,65540],[12,0,65544],"url:index.html",
      [12,0,65537],[12,-400,65540],[12,0,65544],"url:foafnaut:graph",[12,0,65537],[11,-600,0],[12,-60,65540],[12,0,65544],"url:foafnaut:graph",
      [12,0,65537],[12,100,65540],[12,0,65544],"url:foafnaut:graph"];
    else throw new Error(`Unknown native HTML argument: ${arg}`);
  }
  // Lean engine for compile: --native-engine PATH, else libweb-render.dylib beside the program, else Wasm.
  // The app goes into the Dock and Command-Tab, with its menu, before the engine loads (issue 1268).
  const early=check||offscreen||Deno.build.os!=="darwin"?undefined:await nativePreflight(()=>loadNativeWindow());
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
  // No page given: the start page (start.html; owner, 2026-11-09). A sweep, a check, a paste or a
  // print with no page keeps the demo index: those runs press its links and check its URL.
  const indexURL=new URL("./pages/index.html",import.meta.url).href;
  const startDefault=url===undefined&&!(sweep||commands||pasted||printPDF||check);
  url??=startDefault?new URL("./pages/start.html",import.meta.url).href:indexURL;
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
  const browserState=stateOff||check||sweep||commands||printPDF?undefined:
    hostState({engineState:engine.state,dir:stateDir,log:record=>console.log(JSON.stringify({t:Math.round(performance.now()),...record}))});
  // Noto Sans is the default face; the bitmap face is the safe mode, and the fallback.
  const defaultFont=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url);
  let workerFont:{path:string;family:string}|undefined;
  if(!bitmapFont)workerFont={path:fontFile??decodeURIComponent(defaultFont.pathname),family:fontFile?"font":"Noto Sans"};
  // Every engine call that can take more than about 2 ms runs in one worker, in order. `lean` is that
  // engine (promises), or the main-thread engine when the worker can not start (said once, loudly) or in --check-engine.
  let worker:CompileClient|undefined,mainFont=false;
  type Lean=Pick<typeof engine,"xmlStylesheet"|"xslt"|"inspect"|"compile"|"selectedText"|"graphStart"|"graphEvent"|"graphPage"|"sourcePage"|"wasmPage"|"sparqlPage"|"printLayout"|"encodingSetting"|"encodingChoices">;
  let lean:Lean=engine;
  // The engine that runs Lean's renders: the native library in the worker, or Wasm (in the
  // worker, or on the main thread, which has only the Wasm engine). Said at start and in the summary.
  let engineRan="wasm";
  const sayEngine=(where:string)=>{
    engineRan=worker&&nativeEngine?`native ${nativeEngine}`:"wasm";
    console.log(`engine: ${engineRan}`);
    console.log(JSON.stringify({type:"native-html-engine",t:Math.round(performance.now()),engine:engineRan,where}));
  };
  // Fallback fonts for the characters the first font lacks (native_html_fonts.ts: the Hub's
  // table and choice), per page, before its first layout, into the engine that lays pages out.
  // The worker chooses and reads them beside its engine; the main thread only looks for a
  // character above ASCII. The main-thread engine takes them only when its first font answered
  // with a count of fonts held (an older engine would take them as replacements).
  let mainFallbacks=false,workerFonts:FallbackFont[]|undefined=[];
  const mainFonts=fallbackFontHost(fonts=>loadFallbackFonts(engine,fonts));
  const pageFonts=async(source:string)=>{
    if(!mayNeedFallbackFonts(source))return;
    const start=performance.now(),where=worker?.alive?"worker":"main";
    let answer:PageFonts;
    if(worker?.alive&&workerFonts){
      // A worker engine that holds one font says so once; its pages then get none.
      try{answer=await worker.pageFonts(source);workerFonts=answer.held;}
      catch(error){if(!worker?.alive)throw error;workerFonts=undefined;console.error("Native HTML: no fallback fonts:",String(error));return;}
    }
    else if(mainFallbacks&&workerFont)answer=await mainFonts.page(source);
    else return;
    if(answer.loaded.length||answer.failed.length)console.log(JSON.stringify({type:"native-html-fonts",t:Math.round(performance.now()),where,
      ms:Math.round((performance.now()-start)*10)/10,fonts:answer.loaded,...(answer.failed.length?{failed:answer.failed}:{}),held:answer.held.length}));
  };
  const useMainEngine=async(reason:string)=>{
    console.error("Native HTML: ENGINE WORKER UNAVAILABLE, so Lean runs on the main thread and the window can miss input:",reason);
    console.log(JSON.stringify({type:"native-html-worker",state:"main-thread-fallback",reason}));
    worker=undefined;lean=engine;sayEngine("main-thread");
    if(workerFont&&!mainFont){mainFont=true;try{
      mainFallbacks=typeof (await loadFontFile(engine,workerFont.path,workerFont.family))?.fonts==="number";
      // The fallback fonts the worker held, so the pages open keep their scripts.
      if(mainFallbacks&&workerFonts?.length)await mainFonts.add(workerFonts);
    }catch(error){if(fontFile)throw error;workerFont=undefined;}}
  };
  if(check){
    sayEngine("main-thread");
    if(workerFont)try{mainFallbacks=typeof (await loadFontFile(engine,workerFont.path,workerFont.family))?.fonts==="number";}catch(error){if(fontFile)throw error;console.error("Native HTML: bitmap font, because Noto Sans did not load:",String(error));}
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
  // With the bitmap face (safe mode) a page gets no fallback fonts.
  if(workerFont)setFontHost(pageFonts);
  // Page scripts (WebScripts.lean): the QuickJS guest module goes into the engine that runs
  // the renders (the worker), once. The engine must answer scriptSession info first: an older
  // engine has no such op, and then a page with scripts is refused as before (issue 1274).
  type ScriptCall=(name:"scriptInfo"|"scriptLoad"|"scriptSession"|"nodeAt"|"pointerAt"|"scriptPlan"|"scriptSetting"|"scriptChoices",...args:unknown[])=>Promise<unknown>;
  const scriptCall:ScriptCall=async(name,...args)=>worker?await worker.engine[name](...args)
    :(engine as unknown as Record<string,(...a:unknown[])=>unknown>)[name](...args);
  const scriptInput:ScriptCall=async(name,...args)=>worker?(await worker.inputCall(name,...args)).value:await scriptCall(name,...args);
  let session:Awaited<ReturnType<typeof createHTMLWindowSession>>|undefined;
  // Page GPU commands (docs/designissues/2026-11-08-page-gpu.md): Lean validated each one; the
  // window session replays them in order and presents the page canvases. Before the session
  // exists they wait here. Declared before the first page, whose scripts start before the window.
  const gpuTurns:{page:number;commands:unknown[]}[]=[];
  // Presents of page canvases with no Lean frame (a turn's replay, blit and composite), and
  // their times, for the exit summary.
  const pageGpuMs:number[]=[];
  const takeShot=async()=>{
    const texture=session?.offscreenTexture,file=shotFile;
    if(!texture||!file||!device)return;
    shotFile=undefined;
    await Deno.writeFile(file,await pngOf(texture.width,texture.height,await texturePixels(device,texture)));
    console.log(JSON.stringify({type:"native-html-shot",file,width:texture.width,height:texture.height}));
  };
  const gpuFlush=()=>{
    if(!session)return;
    while(gpuTurns.length){const t=gpuTurns.shift()!,start=performance.now();
      session.pageGpu(t.page,t.commands).then(r=>{if(!r?.presented)return;const ms=Math.round((performance.now()-start)*10)/10;
        pageGpuMs.push(ms);if(perfSummary)console.log(JSON.stringify({type:"native-html-page-canvas",t:Math.round(performance.now()),ms}));
        if(shotFile&&pageGpuMs.length===120)takeShot();})
        .catch(error=>console.error("Native HTML: page GPU failed:",String(error)));}
  };
  let scriptsOn=false,scriptOps:string[]=[];
  // The page script setting (WebRenderScript.plan): "" is Lean's default for this host (the
  // Lean engine where the engine has it). Lean says what a setting means; an engine from
  // before the op (probed once) runs QuickJS-NG, as before.
  let scriptSetting="",scriptEngines:string[]=[],quickjsLoaded=false,planOp=true;
  // Pages that declare no encoding: the setting ("" detect) and the system's language. The
  // language is Deno's navigator.language (from LANG / LC_ALL); Lean maps it by HTML
  // §13.2.3.2's table of suggested defaults (WHATWG.Encoding.Sniff.localeEncoding).
  let encodingSetting="";const systemLocale=navigator.language??"";
  setPageDecoding({fallback:encodingSetting,locale:systemLocale});
  const sessionEngines=new Map<number,string>();
  // Lean's plan, from the engine that runs the scripts (the worker's); the plans of the
  // settings are kept for the chrome marker, which is drawn without waiting.
  const plans=new Map<string,ScriptPlan>();
  const askPlan=async(setting:string,unavailable=""):Promise<ScriptPlan>=>{
    if(planOp)try{return await scriptCall("scriptPlan",{setting,scripts:1,host:scriptHostKind(),...(unavailable?{unavailable}:{})}) as ScriptPlan;}catch{planOp=false;}
    return {engine:"quickjs",name:"QuickJS-NG",run:!unavailable,marker:"",notice:unavailable};
  };
  // The host name Lean's default engine is asked for: "native", for the native library and for
  // the engine's WebAssembly build alike (BubblePopJS is the default on both).
  const scriptHostKind=()=>"native";
  const keepPlans=async()=>{for(const setting of ["","bubblepop","quickjs","none"])plans.set(setting,await askPlan(setting));};
  const planFor=(setting:string)=>plans.get(setting)??plans.get("");
  // The real time at which each session's virtual clock was 0.
  const scriptEpochs=new Map<number,number>();
  // The guest module: --quickjs-wasm FILE, else a local build (tools/wasmvm/build-quickjs.sh),
  // else the one tools/fetch-builds.sh --set foafnaut-web installs.
  const installed=decodeURIComponent(new URL("../../../docs/web/hub/wasm-guests/qjs-wasmvm.wasm",import.meta.url).pathname);
  const local=`${Deno.env.get("HOME")}/working/qjs-wasm/qjs-wasmvm.wasm`;
  const quickjsPath=quickjsWasm??[local,installed].find(p=>{try{return Deno.statSync(p).isFile;}catch{return false;}})??local;
  if(!scriptsOff&&!check) {
    try{
      const t0=performance.now();
      const info=(await scriptCall("scriptInfo")) as {ops?:string[];engines?:string[]};
      scriptOps=info.ops??[];scriptEngines=info.engines??["quickjs"];
      let loaded:unknown;
      try{loaded=await scriptCall("scriptLoad",await Deno.readFile(quickjsPath));quickjsLoaded=true;}
      catch(error){if(!scriptEngines.includes("bubblepop"))throw error;
        console.log(JSON.stringify({type:"native-html-scripts",engine:"quickjs",state:"off",module:quickjsPath,reason:String(error instanceof Error?error.message:error)}));}
      scriptsOn=true;
      setScriptHost({start:async(source,pageURL,resources,encoding,mode={})=>{
        // The setting: Lean's plan says which engine runs the page, or why none does.
        let plan=await askPlan(scriptSetting);
        if(plan.run&&!scriptEngines.includes(plan.engine))plan=await askPlan(scriptSetting,`this engine has no ${plan.name}`);
        else if(plan.run&&plan.engine==="quickjs"&&!quickjsLoaded)plan=await askPlan(scriptSetting,`no guest module (${quickjsPath})`);
        if(!plan.run){if(plan.notice)throw new Error(plan.notice);return undefined;}
        // The viewport (innerWidth, innerHeight) and the render request that lays the page out
        // for its scripts' layout reads; an engine without them ignores the fields.
        // (The first page starts before the window's size and chrome are set: then 1280 by 800.)
        const at=(()=>{try{return {width,height,shell:shell(),textScalePercent:view.textScalePercent??100,zoomUnit:view.zoomUnit??100};}
          catch{return {width:1280,height:800,textScalePercent:150,zoomUnit:100};}})();
        const turn=await scriptCall("scriptSession",source,{action:"start",url:pageURL,resources,width:at.width,height:at.height,zoomUnit:at.zoomUnit,
          ...(at.shell?{shell:at.shell}:{}),layout:{url:pageURL,textScalePercent:at.textScalePercent,zoomUnit:at.zoomUnit,...mode},
          ...(plan.engine==="bubblepop"?{engine:"bubblepop"}:{}),...(encoding?{encoding}:{})}) as ScriptTurn;
        scriptEpochs.set(turn.session,performance.now()-turn.clock);sessionEngines.set(turn.session,plan.engine);
        // The start turn makes the page's GPU objects (canvas, buffers, pipelines); the later turns use them.
        if(turn.gpu?.length){gpuTurns.push({page:turn.gpuPage!,commands:turn.gpu});gpuFlush();}
        for(const line of turn.logs)console.log(`page: ${line.replace(/^\u0001(\w+)\u0001/,"$1: ")}`);
        for(const line of turn.errors)console.error(`page error: ${line}`);
        console.log(JSON.stringify({type:"native-html-script",cause:"start",engine:plan.engine,t:Math.round(performance.now()),session:turn.session,
          commands:turn.commandCount,instructions:turn.instructions,jobs:turn.jobs,tasks:turn.tasks,leanMs:Math.round(turn.ns/1e5)/10,nextWake:turn.nextWake}));
        return turn;
      }});
      console.log(JSON.stringify({type:"native-html-scripts",state:"on",engines:scriptEngines,default:(await keepPlans(),planFor("")?.engine),module:quickjsLoaded?quickjsPath:null,loaded,ms:Math.round(performance.now()-t0)}));
    }catch(error){
      console.log(JSON.stringify({type:"native-html-scripts",state:"off",module:quickjsPath,reason:String(error instanceof Error?error.message:error)}));
    }
  }
  // Liberal mode: the command line, else the saved setting (read when the window opens).
  // Liberal is the default (owner, 2026-11-09): the browser shows what it can and lists the rest
  // in the console tab. --strict, or the Settings choice, refuses such pages instead.
  if(cliLiberal&&cliStrict)throw new Error("Use one of --strict and --be-liberal-in-what-we-accept");
  let liberal=!cliStrict;
  // The start page has a script. A host that can run no page script (the Wasm engine with no
  // QuickJS guest module) refuses it; then the window opens the demo index, which has none.
  let document=await prepareHTML(lean,url,undefined,undefined,{liberal}).catch(error=>{
    if(!startDefault)throw error;
    console.log(JSON.stringify({type:"native-html-start-fallback",url,to:indexURL,reason:String(error instanceof Error?error.message:error)}));
    return prepareHTML(lean,indexURL,undefined,undefined,{liberal});
  }),width=1280,height=800;
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
  let running=true,dirty=true,controller:AbortController|undefined;
  // Frame trace, one JSON line for each event: every number a tool needs to find
  // where the time goes. A pump stall means AppKit held the thread in its own loop.
  let resizeAt:number|undefined,frameNumber=0,waiting=false,waitingSince=0,animationFrames=0;
  // The heavy-page guard (gpu_pacing.ts): while the GPU time of frames stays high, the next
  // animation frame and the next page script turn wait until gpuHoldUntil. Input does not wait.
  const gpuGuard=createGpuGuard();
  let animationDue=false,gpuHoldUntil=0,quitAt:number|undefined;
  const gpuSlowedNote="SLOWED: HEAVY PAGE";
  const trace=(type:string,fields:Record<string,unknown>)=>console.log(JSON.stringify({type,t:Math.round(performance.now()),...fields}));
  const ms=(start:number,end:number)=>Math.round((end-start)*10)/10;
  let refusing=0;
  let candidate:Awaited<ReturnType<typeof prepareHTML>>|undefined;
  const refuse=(target:string,error:unknown)=>{
    console.error("Native HTML refused:",target,String(error));
    trace("native-html-refused",{url:target,reason:String(error)});
    refusing++;prepareHTML(lean,target,undefined,refusalHTML(target,String(error))).then(next=>{
      addEntries(next,[{source:"System",severity:"error",feature:"page",where:target,message:String(error),action:"page refused"}]);
      if(running){candidate=next;dirty=true;}}).finally(()=>refusing--)
      .catch(failure=>console.error("Native HTML refusal page failed:",String(failure)));
  };
  // A turn of a page's script session: its logs, and a new frame only when the DOM changed
  // (no DOM change, no layout; the commands are part of the layout key).
  let scriptBusy=false;
  // Pointer input for page scripts (WebScripts pointer): Lean finds the target and the
  // coordinates (nodeAt), then dispatches pointer and mouse events, a click on release, at
  // most one move in a frame. A move waits while one is on its way. An engine without the
  // action gets a click on release.
  const queuePointer=pressPointers();
  const scriptPointer=(kind:PointerKind,x:number,y:number,held:NativePress<typeof document>)=>{
    const page=held.page;
    if(!scriptsOn||!page.script||!scriptOps.includes("pointer"))return;
    // WebHit returns this event's coordinates; the engine keeps the down target
    // separately. Use what is shown for each event, not a frame frozen at press.
    // Capture before queueing so a later present cannot change this event's request.
    const session=page.script.session,hit=scriptHitRequest(page),options={...hit.options,x,y};
    queuePointer(kind,async()=>{
      const at=await scriptInput("pointerAt",page.source,hit.width,hit.height,options) as {node:number|null};
      const node=pointerNode(held,kind,at.node);
      if(node===undefined)return;
      const ended=kind==="up"||kind==="cancel";
      const turn=await scriptInput("scriptSession","",{action:"pointer",session,kind,...at,node,button:0,
        buttons:ended?0:1,pressure:ended?0:0.5,pointerType:"mouse"}) as ScriptTurn;
      scriptTurn(page,turn,`pointer ${kind}`);
    }).catch(error=>console.error("Native HTML: page script pointer failed:",String(error)));
  };
  const scriptTurn=(page:typeof document,turn:ScriptTurn,cause:string)=>{
    for(const line of turn.logs)console.log(`page: ${line.replace(/^\u0001(\w+)\u0001/,"$1: ")}`);
    for(const line of turn.errors)console.error(`page error: ${line}`);
    trace("native-html-script",{cause,session:turn.session,clock:turn.clock,changed:turn.changed,commands:turn.commandCount,
      instructions:turn.instructions,jobs:turn.jobs,tasks:turn.tasks,leanMs:Math.round(turn.ns/1e5)/10,nextWake:turn.nextWake});
    // A turn that draws a page canvas is activity: no idle check (a Lean frame drawn again
    // with probes, which held up the next turns) while the page animates its canvas.
    if(turn.gpu?.length){gpuTurns.push({page:turn.gpuPage!,commands:turn.gpu});gpuFlush();lastActivity=Math.max(lastActivity,performance.now());}
    if(page.applyTurn(turn)&&page===document)dirty=true;
  };
  // View state is held here and applied by Lean. Pointer positions are in the
  // coordinates of the presented frame, as link picking is.
  // Text zoom 200 (WebSelection.defaultPercent; it was 150) until the window's backing scale is
  // known; then zoom unit 100*scale and zoom 200*scale, which the settings page shows as 200%.
  const view:PageView={textScalePercent:200};
  let press:NativePress<typeof document>|undefined,lastCopied:string|undefined,loading=false;
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
  let field=showURL(document.url),focused=false,theme="next",pages=1,scale=1,active=0,scroll=0,swipeHint=0;
  const tabs:{document:typeof document;history:typeof history;scroll:number}[]=[{document,history,scroll:0}];
  // The tab icon of a page: Lean prepares it once from the bytes the page fetched (HTML §4.6.7.8).
  const icons=new WeakMap<object,unknown>();
  const iconOf=(page:typeof document)=>{
    const bytes=(page as {iconBase64?:string}).iconBase64;
    if(!bytes)return undefined;
    if(!icons.has(page))try{icons.set(page,engine.iconPrepare(bytes,2));}catch(error){icons.set(page,null);console.error("Native HTML icon refused:",String(error));}
    return icons.get(page)??undefined;
  };
  const shell=()=>({tabs:tabs.map((tab,index)=>{const page=index===active?document:tab.document;return {title:page.title??"",icon:iconOf(page)};}),active,...field,focused,
    canBack:history.canBack,canForward:history.canForward,loading,scale,theme,pages,scroll,pressed:pressed?.control??"",...(swipeHint?{swipe:swipeHint}:{}),
    script:[scriptMarker(),gpuGuard.slowed?gpuSlowedNote:""].filter(Boolean).join("  ")});
  // The chrome marker of the page's scripts: the engine of its session, else what the setting says.
  function scriptMarker(){
    if(!scriptsOn||!document?.scripted)return "";
    const running=document.script?sessionEngines.get(document.script.session):undefined;
    return planFor(running??scriptSetting)?.marker??"";
  }
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
  // Closed tabs, the last one last, for Shift-Command-T (issue 1268).
  const closed:typeof tabs=[];
  const closeTab=(index:number)=>{
    if(tabs.length===1){running=false;return;}
    keepTab();closed.push(tabs[index]);if(closed.length>25)closed.shift();tabs.splice(index,1);showTab(Math.min(active>index?active-1:active,tabs.length-1));
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
  const graphInput=(kind:number,a:number,b:number,page=document as Page)=>{
    const last=graphQueue[graphQueue.length-1];
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
  // foafnaut:wasm (issue 1244): WebAssembly run by WasmVM, Lean's engine, inside this engine. The page is
  // Lean's HTML; `:wasm NAME.wasm#export` adds a module from the pages folder, read here and run by Lean.
  const wasmURL="foafnaut:wasm",pagesURL=new URL("./pages/",import.meta.url);
  const wasmPage=async(target:string)=>{
    const argument=target.slice(wasmURL.length+1),request:Record<string,unknown>={};
    if(argument){
      const [path,exportName]=argument.split("#"),file=new URL(path,pagesURL);
      if(!file.href.startsWith(pagesURL.href)||!file.pathname.endsWith(".wasm"))throw new Error("Only .wasm files of the pages folder are run");
      const bytes=await Deno.readFile(file);
      if(bytes.length>1048576)throw new Error(`The module has ${bytes.length} bytes; the page takes at most 1048576`);
      let text="";for(let i=0;i<bytes.length;i+=32768)text+=String.fromCharCode(...bytes.subarray(i,i+32768));
      Object.assign(request,{url:file.href,wasmBase64:btoa(text)},exportName?{export:exportName}:{});
    }
    const answer=await lean.wasmPage(request);
    return await prepareHTML(lean,target,undefined,answer.source);
  };
  // foafnaut:sparql (owner, 2026-11-08): the SPARQL planner drawn as live debug. Lean parses, plans and
  // runs the query and writes the page; the address after `foafnaut:sparql/` is `q=QUERY&step=N`.
  // `:sparql-step` goes to the address Lean gives as the next step.
  const sparqlURL="foafnaut:sparql";let sparqlNext=sparqlURL;
  const isSparql=(target:string)=>target===sparqlURL||target.startsWith(sparqlURL+"/");
  // about:foafnaut: which build this is, from the record compiled into the program.
  const aboutURL="foafnaut:about";
  const aboutPage=async()=>{
    const info=await buildInfo();
    const esc=(t:unknown)=>String(t).replace(/[&<>]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;"}[c]!));
    const row=(k:string,v:unknown)=>`<tr><th>${esc(k)}</th><td>${esc(v)}</td></tr>`;
    return `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>About Foafnaut</title><style>body{margin:24px;font-size:15px;line-height:22px;color:#203040;background:white}h1{margin:0 0 12px;font-size:24px;line-height:32px;color:#184078}th{text-align:left;padding:4px 18px 4px 0;font-weight:normal;color:#5b6876}td{padding:4px 0}</style></head><body><h1>Foafnaut</h1><table>`+
      row("Build commit",(info.commit??"unknown: run from source")+(info.dirty?" (with uncommitted changes)":""))+
      row("Built",info.builtAt??"unknown")+
      row("Rendering engine",engineRan.startsWith("native")?"native library":"WebAssembly")+
      row("Page scripts",planFor(scriptSetting)?.name??"none")+
      row("Liberal mode",liberal?"on":"off")+
      row("Platform",`${Deno.build.os} ${Deno.build.arch}`)+
      row("Runtime",`Deno ${Deno.version.deno}, V8 ${Deno.version.v8}`)+
      `</table></body></html>`;
  };
  const sparqlPage=async(target:string)=>{
    let answer:{source:string;next?:string};
    try{answer=await lean.sparqlPage(target.slice(sparqlURL.length+1));}
    catch(error){
      if(!/unknown document operation/.test(String(error)))throw error;
      answer={source:'<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Needs a newer engine</title></head><body>'+
        "<h1>The SPARQL planner page needs a newer engine</h1><p>This engine is older and does not have the SPARQL planner ops.</p></body></html>"};
    }
    sparqlNext=answer.next??sparqlURL;
    return await prepareHTML(lean,target,undefined,answer.source);
  };
  // foafnaut:console (WebConsole.lean): the console of a tab as a page, written and drawn by Lean
  // from the entries this host kept (native_console.ts). `foafnaut:console/N` is the console of tab
  // N; with no number, of the page shown when it was asked for (or that a console tab showed).
  const consoleURL="foafnaut:console",consoleSources=new WeakMap<object,typeof document>();
  let consoleFrom:typeof document|undefined;
  const isConsole=(target:string)=>target===consoleURL||target.startsWith(consoleURL+"/");
  const tabPage=(index:number)=>index===active?document:tabs[index]?.document;
  const consolePage=async(target:string)=>{
    const number=Number(target.slice(consoleURL.length+1));
    let source=Number.isInteger(number)&&number>0&&tabPage(number-1)?tabPage(number-1)!:consoleFrom??document;
    consoleFrom=undefined;
    source=consoleSources.get(source)??source;
    const index=Math.max(0,tabs.findIndex((_,i)=>consoleSources.get(tabPage(i)!)===source||tabPage(i)===source));
    let answer:{source:string};
    try{answer=engine.consolePage(consoleRequest(source,index,tabs.map((_,i)=>tabPage(i)!)));}
    catch(error){
      if(!/unknown document operation/.test(String(error)))throw error;
      answer={source:'<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Needs a newer engine</title></head><body>'+
        "<h1>The console needs a newer engine</h1><p>This engine is older and does not have the console op.</p></body></html>"};
    }
    const page=await prepareHTML(lean,target,undefined,answer.source);
    consoleSources.set(page,source);
    return page;
  };
  // Option-Command-J and View > Console: the console of the page shown, in a new tab.
  const openConsole=()=>{const source=document;newTab();leaveAddress();consoleFrom=source;navigate(consoleURL);};
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
    // Lean's limit for the layers on screen (WebDocument.scrollLimit): the view then ends at the last page row.
    const limit=current?.layers.layers.scrollLimit;
    if(typeof limit==="number")return limit;
    const boxes=frame.webRender.boxes as number[][]|undefined;
    const bottom=Math.max(0,...(boxes??[]).map(box=>box[2]+box[4]));
    return Math.max(0,bottom-height+Math.round(60*scale));
  };
  const scrollBy=(amount:number)=>{
    const next=Math.max(0,Math.min(scrollLimit(),scroll+Math.round(amount)));
    if(next===scroll)return;
    frameCost.scrollEvents++;frameCost.scrollRows+=Math.abs(next-scroll);
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
  // Frame cost ratchet (L4Factoidal/FrameCost, section Ratchet): Lean frames and rows
  // scrolled after the first frame. --scroll-sweep fails when the frames pass the bound.
  const frameCost={leanFrames:0,scrollEvents:0,scrollRows:0,reach:0};
  // SVG animation of each page (WebPaint, SMIL timing in Lean): its clock starts at the page's
  // first frame; `time` is the clock of the last frame asked for, so a page whose animations
  // have ended keeps one state. `has`: Lean said the page has animations; `running`: one runs
  // or begins by the clock, so the next frame is asked for at once.
  const animation=new WeakMap<object,{epoch:number;time:number;running:boolean;has:boolean;clicks:number[][]}>();
  const animationOf=(page:object)=>{let a=animation.get(page);if(!a){a={epoch:performance.now(),time:0,running:false,has:false,clicks:[]};animation.set(page,a);}return a;};
  // The request that a frame of `page` at this scroll sends to Lean, and its state with no scroll.
  const requestAt=(page:typeof document,at:number)=>{
    const view0=shown();view0.shell={...view0.shell,scroll:at};
    // SVG animation (WebPaint): the page clock and clicks, only for a page with animations,
    // so that other pages keep one state key whatever the time.
    const clock=animation.get(page);
    const animated=clock&&(clock.has||clock.clicks.length)?{animationTime:clock.time,animationClicks:clock.clicks}:{};
    return page.request(width,height,{...view0,...animated,live:page===checked,...(everyFrame?{}:{checks:false})});
  };
  let presented:PresentedState<typeof document>|undefined;
  const recordPresented=(record:RequestRecord,at:number)=>{
    if(record.document===document)presented={document:record.document,width:record.width,height:record.height,scroll:at,options:record.request.options};
  };
  const scriptHitRequest=(page:typeof document)=>pointerRequest(page,presented,()=>({width,height,options:requestAt(page,page===document?scroll:0).options}));
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
  let current:({layers:HTMLLayers}&RequestRecord)|undefined,shownOffset=0;
  let shiftPending=false,shiftedByEvent=false;
  let checked:typeof document|undefined;
  // A selection is in window coordinates, so with one a scroll needs a Lean frame.
  const canShift=()=>layered&&!!current&&current.document===document&&!candidate&&current.width===width&&current.height===height&&!Array.isArray(view.selection);
  // Window and page-layer rows, for link picking: the composite maps one to the other.
  const pageRow=(y:number)=>current?y-current.layers.layers.top+shownOffset:y;
  const windowRow=(y:number)=>current?y+current.layers.layers.top-shownOffset:y;
  const settingsURL=new URL("./pages/settings.html",import.meta.url).href;
  // The settings page's text size: Lean's textZoom (asked once; an older engine keeps the zoom
  // of before: a number is the zoom, up, down and reset are window commands 1, 2 and 3).
  let zoomOps:boolean|undefined;
  const textZoom=(argument="")=>{
    if(zoomOps===false)return undefined;
    try{const answer=engine.textZoom(argument,view.textScalePercent??200,view.zoomUnit??100);zoomOps=true;return answer;}
    catch{zoomOps=false;return undefined;}
  };
  const zoomTo=(next:number)=>{
    if(next===view.textScalePercent)return;
    view.textScalePercent=next;view.selection=undefined;dirty=true;
    trace("native-html-zoom",{textScalePercent:next});
    browserState?.settings({textZoom:next});
    if(document.url===settingsURL)navigate(settingsURL,false);
  };
  const zoomCommand=(argument:string)=>{
    if(!argument){navigate(settingsURL);return;}
    const answer=textZoom(argument);
    if(answer)zoomTo(answer.textScalePercent);
    else if(/^[0-9]+$/.test(argument))zoomTo(Math.max(50,Number(argument)));
    else if(["up","down","reset"].includes(argument))windowCommand(["up","down","reset"].indexOf(argument)+1);
  };
  // The settings page with the text size now where it says <!--foafnaut:text-size-->.
  // The page script rows too, as Lean makes them for the current setting (scriptChoices).
  const settingsSource=async()=>{
    let source=await Deno.readTextFile(new URL(settingsURL));
    const open="<!--foafnaut:scripts-->",close="<!--/foafnaut:scripts-->",i=source.indexOf(open),j=source.indexOf(close);
    if(planOp&&scriptsOn&&i>=0&&j>i)try{source=source.slice(0,i+open.length)+await scriptCall("scriptChoices",scriptSetting,scriptHostKind())+source.slice(j);}catch{/* the static links */}
    // The default encoding section, as Lean makes it for the setting and the system's language.
    const eOpen="<!--foafnaut:encoding-->",eClose="<!--/foafnaut:encoding-->",ei=source.indexOf(eOpen),ej=source.indexOf(eClose);
    const choices=ei>=0&&ej>ei?await lean.encodingChoices(encodingSetting,systemLocale):undefined;
    if(choices)source=source.slice(0,ei+eOpen.length)+choices+source.slice(ej);
    const size=textZoom();
    // A ticked box is filled (boxon), as WebRenderScript.choicesHTML does for the script rows.
    const box=`<span class="box${liberal?" boxon":""}"></span>`;
    return source.replace("<!--foafnaut:liberal-->",`<p class="check"><a href="foafnaut:liberal/${liberal?"off":"on"}">${box} Be liberal in what we accept</a></p>`+
      "<p>On (the default): a page with a feature this browser does not support is drawn without it (a module script, a stylesheet that did not load, a media condition or inline SVG it can not read), and the console (Option-Command-J) lists what was skipped. Off: strict, such a page is refused.</p>")
      .replace("<!--foafnaut:text-size-->",size
      ?`<h2 class="size">Text size: ${size.shown}%</h2>`
      :"<h2>Text size</h2><p>The engine of this window is older: these sizes are the text zoom itself, and A+ and A\u2212 step by a tenth.</p>");
  };
  const shellCommand=(name:string,argument:string)=>{
    if(name==="back")windowCommand(6);
    else if(name==="forward")windowCommand(7);
    else if(name==="reload")windowCommand(8);
    else if(name==="new")newTab();
    else if(name==="close")closeTab(active);
    else if(name==="home")navigate(home.url);
    else if(name==="graph")navigate(graphURL);
    else if(name==="source")viewSource().catch(error=>refuse(document.url,error));
    else if(name==="theme"){theme=argument||(theme==="next"?"arcade":"next");dirty=true;browserState?.settings({theme});}
    else if(name==="zoom")zoomCommand(argument);
    else if(name==="scripts"&&planOp){
      // The page script engine: Lean checks the name; pages opened after it use it.
      (scriptCall("scriptSetting",argument) as Promise<{setting:string}>).then(chosen=>{
        scriptSetting=chosen.setting;browserState?.settings({scripts:scriptSetting});
        trace("native-html-script-setting",{setting:scriptSetting});
        if(document.url===settingsURL)navigate(settingsURL,false);else dirty=true;
      }).catch(error=>refuse(`foafnaut:scripts/${argument}`,error));
    }
    else if(name==="liberal"){
      // The Settings checkbox: foafnaut:liberal/on, /off, or a toggle. Pages load in the new mode from now on.
      liberal=argument==="on"?true:argument==="off"?false:!liberal;
      browserState?.settings({liberal});trace("native-html-liberal",{liberal});
      if(document.url===settingsURL)navigate(settingsURL,false);
    }
    else if(name==="encoding"){
      // The default for pages that declare no encoding: Lean checks the value; pages opened after it use it.
      Promise.resolve(lean.encodingSetting(argument)).then(chosen=>{
        if(chosen===undefined){refuse(`foafnaut:encoding/${argument}`,"this engine has no encoding setting");return;}
        encodingSetting=chosen;setPageDecoding({fallback:chosen});browserState?.settings({encoding:chosen});
        trace("native-html-encoding-setting",{setting:chosen});
        if(document.url===settingsURL)navigate(settingsURL,false);else dirty=true;
      }).catch(error=>refuse(`foafnaut:encoding/${argument}`,error));
    }
    else if(STATE_COMMANDS.includes(name)){
      if(!browserState){refuse(`foafnaut:${name}`,"Browser state is off (--no-state, a sweep or a check)");return;}
      browserState.command(name,argument,{url:document.url,title:document.title??""}).then(page=>{if(page)navigate(page);}).catch(error=>refuse(`foafnaut:${name}`,error));
    }
    else if(name==="wasm")navigate(wasmURL+(argument?"/"+argument:""));
    else if(name==="sparql")navigate(sparqlURL+(argument?"/"+argument:""));
    else if(name==="sparql-step")navigate(sparqlNext);
    else navigate(settingsURL);
  };
  // Where a link or an address goes: Lean's route (WebRoute.lean), done as it says. This
  // browser loads every web site itself and reads local files from a local page. With an
  // engine from before the op, link-route.mjs gives the same answers (issue 1274).
  const site={origin:"",pages:new URL("./pages/",import.meta.url).href,files:true};
  const router=createRouter((request:Record<string,unknown>)=>engine.shellRoute(request));
  // Back and forward swipes on the trackpad (WebGesture.lean). The window sends kind 12 for each
  // scroll of a trackpad gesture: its horizontal movement and phase (native_window.m). The
  // deltas of one gesture are added up, in CSS px and the DOM sign (content moving right is a
  // negative dx), and Lean says what they mean; its momentum is left alone. A Mac window gets
  // no touch-screen touches. An engine without the op has no swipes.
  const gestures=(()=>{try{return engine.gesture({action:"info"});}catch{return undefined;}})();
  // The swipe sweep needs the op; with an older engine it is not run, with exit code 4 (sweeps.sh says NOT RUN).
  if(swipeSweep&&!gestures){console.error("Native HTML: NOT RUN: --swipe-sweep needs the engine op gesture, which this engine does not have");worker?.terminate();Deno.exitCode=4;return;}
  let wheelSum:{dx:number;dy:number}|undefined;
  const gestureWheel=(a:number,b:number)=>{
    const phase=b&0xff,momentum=(b>>8)&0xff,enabled=(b&65536)!==0;
    if(!gestures||momentum||!enabled)return;
    if(phase&(1|32))wheelSum={dx:0,dy:0};
    if(!wheelSum)return;
    wheelSum.dx-=a/scale;
    const ended=(phase&(8|16))!==0;
    const answer=engine.gesture({action:"wheel",dx:Math.round(wheelSum.dx),dy:Math.round(wheelSum.dy),ended:(phase&8)!==0});
    trace("native-html-gesture",{dx:Math.round(wheelSum.dx),dy:Math.round(wheelSum.dy),phase,answer});
    const hint=ended||answer.navigate?0:answer.hint;
    if(hint!==swipeHint){swipeHint=hint;dirty=true;}
    if(ended)wheelSum=undefined;
    if(answer.navigate)windowCommand(answer.direction==="back"?6:7);
  };
  // Lean chose to hand this URL to the system browser. Off screen it is traced and not opened,
  // so a sweep never opens a browser window on the person's screen.
  const openSystem=(target:string)=>{
    if(offscreen){trace("native-html-system-url",{url:target,opened:false,why:"offscreen"});return;}
    try{native!.openURL(target);}catch(error){refuse(target,error);}
  };
  const followRoute=(route:LinkRoute)=>{
    trace("native-html-route",route);
    if(route.route==="command")shellCommand(route.name,route.argument);
    else if(route.route==="system")openSystem(route.url);
    else if(route.route==="refuse")refuse(route.url,route.reason);
    // A page link loads only with --follow-links; the browser's own pages always do.
    else if(route.route!=="navigate"||follow)navigate(route.url);
  };
  const go=(answer:ReturnType<typeof engine.shellSubmit>)=>{
    trace("native-html-go",answer);
    if(answer.go==="system")openSystem(answer.url);
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
    // The address menu (WebShell): the Mac pasteboard needs no user gesture, so the buttons act
    // on the press. Copy writes the text Lean chose; Paste and go reads the pasteboard and Lean
    // routes it as a typed address.
    else if(name==="copyAddress"){
      const copy=engine.shellActions(shell(),width).find(action=>action.action==="copy");
      if(copy?.text){native!.writeClipboard(copy.text);lastCopied=copy.text;trace("native-html-copy",{characters:copy.text.length,from:"menu"});}
      closeMenu();
    }
    else if(name==="pasteGo"){
      const {go,clipboard:_,...next}=engine.shellEdit(shell(),"pasteGo",native!.readClipboard());
      field=next;dirty=true;trace("native-html-paste-go",{characters:go?.length??0});
      if(go)goTo(go);
    }
    else if(name==="newTab")newTab();
    else if(name==="tab"&&Number(index)!==active){keepTab();showTab(Number(index));}
    else if(name==="close")closeTab(Number(index));
    else if(name==="tabs"){keepTab();showTab((active+1)%tabs.length);}
  };
  const edit=(answer:ShellEdit&{clipboard?:string|null})=>{const {clipboard:_,...next}=answer;field=next;dirty=true;};
  // The address menu: Lean says when a press opens it; any other edit closes it. An engine
  // without the op shellActions has none.
  const menuOps=(()=>{try{return Array.isArray(engine.shellActions({},1));}catch{return false;}})();
  const openMenu=()=>{if(!menuOps)return;if(!focused)focusAddress();edit(engine.shellEdit(shell(),"menu"));trace("native-html-menu",{open:field.menu===true});};
  const closeMenu=()=>{if(field.menu)edit(engine.shellEdit(shell(),"closeMenu"));};
  const menuPress=(x:number,y:number,how:string)=>{if(menuOps&&engine.shellMenu(shell(),x,y,width,how).menu)openMenu();};
  // An address from the bar (Return, or Paste and go): Lean routes it as typed.
  const goTo=(target:string)=>{
    leaveAddress();
    const route=router.address({...site,address:target,base:document.baseURL||document.url}) as LinkRoute|undefined;
    if(route)followRoute(route);else go(engine.shellSubmit(target));
  };
  // A long press of the mouse (WebGesture hold): asked once when Lean's time has passed with
  // the button still down at the press.
  const holdInfo=gestures as unknown as {actions?:string[];holdMs?:number}|undefined;
  const holdMs=holdInfo?.actions?.includes("hold")?Number(holdInfo.holdMs)||0:0;
  let holding:{x:number;y:number;startX:number;startY:number;at:number}|undefined;
  const checkHold=()=>{
    if(!holding||!holdMs||performance.now()-holding.at<holdMs)return;
    const held=holding;holding=undefined;
    const answer=engine.gesture({action:"hold",startX:Math.round(held.startX/scale),startY:Math.round(held.startY/scale),
      x:Math.round(held.x/scale),y:Math.round(held.y/scale),elapsed:Math.round(performance.now()-held.at)}) as unknown as {phase:string};
    if(answer.phase==="hold")menuPress(held.startX,held.startY,"hold");
  };
  const remember=(answer:HistoryAnswer,action:string)=>{
    history=answer;native?.setHistory(answer.canBack,answer.canForward);
    if(action==="push")pages++;
    trace("native-html-history",{action,index:answer.history.index,size:answer.history.entries.length,url:answer.url});
  };
  const windowCommand=(id:number)=>{
    const answer=engine.command(id,view.textScalePercent??100,history.history,focused,
      {tabs:tabs.length,active,scroll:Math.round(scroll),view:height,scrollLimit:Math.floor(scrollLimit()),scale,zoomUnit:view.zoomUnit??100});
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
    zoomTo(answer.textScalePercent);
    if(answer.action==="focusAddress")focusAddress();
    if(answer.action==="newTab")newTab();
    // Lean answers the tab to show and the scroll; the host shows them.
    if(answer.tab!==undefined&&answer.tab!==active){keepTab();showTab(answer.tab);}
    if(answer.scrollTo!==undefined)scrollBy(answer.scrollTo-scroll);
    if(answer.action==="stop"&&loading){controller?.abort();loading=false;dirty=true;trace("native-html-stop",{url:document.url});}
    if(answer.action==="reopenTab"){const tab=closed.pop();if(tab){keepTab();tabs.push(tab);showTab(tabs.length-1);}}
    if(answer.refused)console.error(`Native HTML ${answer.action}: ${answer.refused}`);
    if(answer.action==="closeTab")closeTab(active);
    if(answer.action==="settings")navigate(settingsURL);
    if(answer.action==="console")openConsole();
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
  // Open tabs go to the browser state (at most once a second), for --restore-session.
  const saveSession=()=>browserState?.session(tabs.map((tab,index)=>{const page=index===active?document:tab.document;
    return {url:page.url,title:page.title??"",scroll:index===active?scroll:tab.scroll};}),active);
  // The settings page with the page script rows that Lean makes for the current setting.
  const navigate=(target:string,push=true)=>{
    const from=document.url;
    controller?.abort();candidate=undefined;controller=new AbortController();const current=controller;loading=true;
    // The loading state is drawn now (a chrome-only frame: the page layer is kept), so a click
    // is answered on screen before the new page is prepared and laid out.
    dirty=true;
    console.log(JSON.stringify({type:"native-html-loading",url:target}));
    (target===aboutURL?aboutPage().then(source=>prepareHTML(lean,target,undefined,source)):STATE_PAGES.includes(target)?(browserState?browserState.page(target):Promise.reject(new Error("Browser state is off"))).then(source=>prepareHTML(lean,target,undefined,source)):target===settingsURL?settingsSource().then(source=>prepareHTML(lean,target,current.signal,source)):target===graphURL?graphPage():target===wasmURL||target.startsWith(wasmURL+"/")?wasmPage(target):isSparql(target)?sparqlPage(target):isConsole(target)?consolePage(target):prepareHTML(lean,target,current.signal,undefined,{liberal})).then(next=>{
      if(current===controller&&!current.signal.aborted&&running){
        candidate=next;dirty=true;loading=false;
        if(push)remember(engine.historyPush(history.history,next.url),"push");
        if(push)browserState?.visit(next.url,next.title??"",from);
        saveSession();
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
    const line={type:"native-html-perf-summary",present:offscreen?"offscreen-texture":"window",inputEventsDropped:native?.eventsDropped()??0,inputLatency:{from:latencyFrom(),count:latencies.length,p50Ms:percentile(latencies,0.5),p95Ms:percentile(latencies,0.95),maxMs:latencies.length?Math.max(...latencies):null},
      engine:engineRan,compileBackend:engineRan.startsWith("native")?"native":"wasm",layered,
      scrollPresents:{count:shifts.length,totalMsP50:percentile(shifts,0.5),totalMsP95:percentile(shifts,0.95),maxMs:shifts.length?Math.round(Math.max(...shifts)*10)/10:null},
      frames:{presented:totals.length,checked:checkedFrames,compiledInWorker:workerFrames,compiledOnMain:mainFrames,totalMsP50:percentile(totals,0.5),totalMsP95:percentile(totals,0.95)},
      // Time between two native event pumps: the longest time the window takes no input.
      // After the first frame is presented: the figure the 50 ms target is judged on.
      pumpGapAfterFirstFrameMs:{count:pumpGapsLate.length,p50:percentile(pumpGapsLate,0.5),p95:percentile(pumpGapsLate,0.95),max:pumpGapsLate.length?Math.round(Math.max(...pumpGapsLate)*10)/10:null},
      slowCalls,
      pumpGapMs:{p50:percentile(pumpGaps,0.5),p95:percentile(pumpGaps,0.95),max:pumpGaps.length?Math.round(Math.max(...pumpGaps)*10)/10:null},
      prefetch:prefetchStats,frameCost,animationFrames,queueMax,sessionStats:session?.stats,
      gpu:{framesInFlight,submitToDoneMsP50:percentile(session?.gpuTimes??[],0.5),submitToDoneMsP95:percentile(session?.gpuTimes??[],0.95),
        maxInFlight:session?.stats.gpu.maxInFlight??0,gateWaits:session?.stats.gpu.waits??0,gateWaitMs:session?.stats.gpu.waitMs??0,blockedMs:session?.stats.gpu.blockedMs??0,submits:session?.stats.gpu.submits??0,guardSlowed:gpuGuard.slowed,guardChanges:gpuGuard.changes},
      pageCanvasPresents:{count:pageGpuMs.length,p50Ms:percentile(pageGpuMs,0.5),p95Ms:percentile(pageGpuMs,0.95)},
      // Pointer press to the present that shows it: the composite darkening, and the Lean frame of a held press.
      press:{overlay:{count:pressOverlayMs.length,p50Ms:percentile(pressOverlayMs,0.5),maxMs:pressOverlayMs.length?Math.round(Math.max(...pressOverlayMs)*10)/10:null},
        frame:{count:pressFrameMs.length,p50Ms:percentile(pressFrameMs,0.5),maxMs:pressFrameMs.length?Math.round(Math.max(...pressFrameMs)*10)/10:null}}};
    trace(line.type,line);
    // Off screen, "presented" means drawn and submitted to the texture: no compositor, no display.
    if(perfSummary)console.log(`engine: ${engineRan}\npresent: ${line.present}\n${offscreen?"offscreen ":""}input latency: ${line.inputLatency.count} events, p50 ${line.inputLatency.p50Ms} ms, p95 ${line.inputLatency.p95Ms} ms, max ${line.inputLatency.maxMs} ms\nframes: ${line.frames.presented} presented (${line.frames.checked} checked), totalMs p50 ${line.frames.totalMsP50}, p95 ${line.frames.totalMsP95}; pipeline builds ${session?.stats.pipelineBuilds}\nscroll presents with no Lean call: ${line.scrollPresents.count}, totalMs p50 ${line.scrollPresents.totalMsP50}, p95 ${line.scrollPresents.totalMsP95}, max ${line.scrollPresents.maxMs}\npress to present: darkening ${line.press.overlay.count}, p50 ${line.press.overlay.p50Ms} ms, max ${line.press.overlay.maxMs} ms; Lean frame ${line.press.frame.count}, p50 ${line.press.frame.p50Ms} ms, max ${line.press.frame.maxMs} ms\nscroll prefetch: ${prefetchStats.sent} sent, ${prefetchStats.ready} ready, ${prefetchStats.swaps} shown, ${prefetchStats.dropped} dropped, ${prefetchStats.stale} stale, ${prefetchStats.missed} missed\npump gap after first frame: p50 ${line.pumpGapAfterFirstFrameMs.p50} ms, p95 ${line.pumpGapAfterFirstFrameMs.p95} ms, max ${line.pumpGapAfterFirstFrameMs.max} ms\npump gap all: p50 ${line.pumpGapMs.p50} ms, p95 ${line.pumpGapMs.p95} ms, max ${line.pumpGapMs.max} ms\ngpu: ${line.gpu.framesInFlight||"unbounded"} in flight, submit to done p50 ${line.gpu.submitToDoneMsP50} ms, p95 ${line.gpu.submitToDoneMsP95} ms, max in flight ${line.gpu.maxInFlight}, ${line.gpu.submits} submits, gate waits ${line.gpu.gateWaits} (${line.gpu.gateWaitMs} ms), blocked in poll ${line.gpu.blockedMs} ms, guard ${line.gpu.guardSlowed?"slowed":"full rate"} (${line.gpu.guardChanges} changes)`);
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
    // Off screen the backing scale is 2, as on a Retina display, so the sweeps' backing-pixel
    // coordinates mean the same on every machine.
    let target:PresentTarget={offscreen:true};
    if(offscreen)native.createOffscreen(800,500,2,windowTitle(document));
    else{
      const handles=native.create(800,500,windowTitle(document));
      target=new Deno.UnsafeWindowSurface(cocoaSurfaceOptions(handles,width,height));
      native.showAfterSurface();
    }
    // A new window starts in the address bar with the address selected (issue 1268).
    focusAddress();
    // Saved settings (theme, text zoom), and with --restore-session the tabs of the last run.
    browserState?.read().then(saved=>{
      if(saved.settings){theme=saved.settings.theme;view.textScalePercent=saved.settings.textZoom;dirty=true;
        if(typeof saved.settings.scripts==="string")scriptSetting=saved.settings.scripts;
        if(!cliLiberal&&!cliStrict&&typeof saved.settings.liberal==="boolean"&&saved.settings.liberal!==liberal){
          liberal=saved.settings.liberal;if(liberal&&document.title==="Page refused")navigate(document.url,false);}
        if(typeof saved.settings.encoding==="string"){encodingSetting=saved.settings.encoding;setPageDecoding({fallback:encodingSetting});}}
      if(restoreSession)(saved.session?.tabs??[]).forEach((tab:{url:string},index:number)=>{if(index>0)newTab();navigate(tab.url);});
    }).catch(()=>{/* state off: said once in the log */});
    scale=Math.max(1,Math.round(native.surfaceState().contentsScale||1));
    // Layout in points, drawn at the backing scale (WebDocument, Device pixels): Lean lays the page
    // out width/scale CSS px wide. The starting text zoom is 200% of a usual browser's text at this
    // scale (WebSelection.unitPercent), as on the Hub; a saved zoom (read above, applied later) wins.
    view.zoomUnit=scale*100;view.textScalePercent=Math.max(50,Math.round(200*scale/5)*5);
    if(commands)native.testRaise();
    device.addEventListener("uncapturederror",event=>{console.error("Native HTML GPU error:",(event as GPUUncapturedErrorEvent).error.message);running=false;Deno.exitCode=1;});
    device.lost.then(info=>{if(running){console.error("Native HTML GPU lost:",info.message);running=false;Deno.exitCode=1;}});
    // One session for the window's life. It keeps the pipeline and buffers (issue 1268).
    session=await createHTMLWindowSession(device,target,native,{framesInFlight,onGpuDone:gpuMs=>{
      const changed=gpuGuard.record(gpuMs);
      gpuHoldUntil=gpuGuard.slowed?performance.now()+gpuGuard.gapMs():0;
      if(!changed)return;
      const slowed=gpuGuard.slowed,fact={state:slowed?"slowed":"full-rate",gpuMs:Math.round(gpuMs),gapMs:Math.round(gpuGuard.gapMs()),url:document.url};
      trace("native-html-gpu-guard",fact);
      if(slowed)addEntries(document,[{source:"System",severity:"warning",feature:"animation",where:document.url,
        message:`Each frame of this page takes the GPU about ${Math.round(gpuMs)} ms: animation runs at a lower rate so the computer stays usable. It returns to the full rate when frames are fast again.`,action:"animation slowed"}]);
      // The chrome shows the note, or stops showing it.
      dirty=true;
    }});
    gpuFlush();
    // Lean's compile runs in a worker so this loop keeps pumping. If the worker
    // can not start or dies, compile runs here instead, and the trace says so.
    // Readback, pixel checks and the frame hash are test work. They run on every frame
    // in sweeps and with --check-pixels; interactively, once after input has been idle.
    everyFrame=checkAll||(!idleChecksOnly&&(!!sweep||!!commands));
    const IDLE_CHECK_MS=500,QUEUE_WARN=1024;
    // Off screen the texture can always take a frame; a window can not while it is hidden or occluded.
    const canPresent=()=>offscreen||native!.canPresent();
    const STAMPED=new Set([2,4,5,11,POINTER_CANCEL]);
    const readyInput=beforeFirstFrame<{event:UIEvent;at:number}>();
    const KIND_NAMES:Record<number,string>={2:"pointer-down",4:"pointer-up",[POINTER_CANCEL]:"pointer-cancel",5:"key",11:"scroll"};
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
      if(session?.frames)frameCost.leanFrames++;
      const stamps=awaiting;awaiting=[];
      // An interactive frame asks Lean for no CPU probe (checks:false, about a fifth of a
      // frame); the idle check below asks for the same frame with its probe and checks it.
      // A new page starts at the top, so its band does too.
      const clock=animationOf(nextDocument);
      if(clock.running)clock.time=Math.round(performance.now()-clock.epoch);
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
      // Liberal mode: what Lean skipped goes to the page's console.
      noteDiagnostics(nextDocument,nextLayers??next);
      const engineFact=frameNumber===0?{engine:await engineInfo}:{};
      const compiled=performance.now();
      // A newer page was chosen while this one compiled: drop this scene.
      if((candidate??document)!==nextDocument){awaiting=[...stamps,...awaiting];dirty=true;return;}
      // With layers, the composite shows the scroll of now, kept in the new band.
      const scrollNow=nextDocument!==document?0:scroll;
      const place=nextLayers?clampOffset(nextLayers.layers,scrollNow):undefined;
      // Lean draws the press in this frame: the composite does not darken it again.
      if(carried&&carried===pressed)session!.setPress(undefined);
      // A tab chosen during the draw must not be replaced by this page. A page that a navigation
      // prepares during the draw is not a reason to drop the frame: see the candidate check below.
      const shownBefore=document;
      const result=nextLayers?await session!.drawLayers(nextLayers,sentWidth,sentHeight,place!.offset,everyFrame):await session!.draw(next,everyFrame);
      if(document!==shownBefore){awaiting=[...stamps,...awaiting];dirty=true;return;}
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
        current={layers:nextLayers,request,document:nextDocument,width:sentWidth,height:sentHeight};shownOffset=place!.offset;
        // Scrolls taken while Lean worked: shown now if the band holds them, else after the next band.
        if(place!.exact){settle(awaitingShift,result.presentedAt);settle(awaitingBand,result.presentedAt);awaitingShift=[];awaitingBand=[];}
        if(nextDocument===document&&!keeps(nextLayers.layers,scroll)&&!bandComing())dirty=true;
        clock.has=!!nextLayers.layers.animations;clock.running=!!nextLayers.layers.animating;
        if(clock.running){animationDue=true;animationFrames++;}
      } else {current=undefined;settle(awaitingBand,result.presentedAt);awaitingBand=[];}
      if(nextDocument!==document)prefetched=undefined;
      checked=nextDocument;
      if(nextDocument!==document)view.selection=undefined;
      if(nextDocument!==document){scroll=0;if(!focused)field=showURL(nextDocument.url);}frame=next;document=nextDocument;
      // Composite offsets are relative to the band; nodeAt takes document scroll.
      recordPresented({request,width:sentWidth,height:sentHeight,document:nextDocument},nextLayers?nextLayers.layers.bandTop+shownOffset:(request.options.shell as {scroll:number}).scroll);
      // A page that a navigation prepared while this frame was drawn is still to come: keep it.
      if(candidate===nextDocument)candidate=undefined;else if(candidate)dirty=true;native!.setTitle(windowTitle(document));
      // A new page under a pointer that has not moved.
      if(lastPointer)pointAt(lastPointer[0],lastPointer[1]);
      console.log(JSON.stringify({type:"native-html-presented",url:document.url,width:sentWidth,height:sentHeight,primitives:frame.primitiveCount,links:frame.webRender.links.length,frames:session!.frames}));
    };
    let lastRequest:RequestRecord|undefined,urlWaitSince:number|undefined;
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
        if(result.presented)recordPresented({...shownRequest,request:{...shownRequest.request,options}},layers.layers.bandTop+offset);
        if(dirty||shiftPending||shifting||lastRequest!==shownRequest||document!==shownRequest.document){dirty=true;return;}
        if(result.presented){current={...shownRequest,request:{...shownRequest.request,options},layers};frame=layers.page;shownOffset=offset;}
      } else if(lastRequest&&lastRequest.request.options.checks===false&&worker?.alive){
        // The frame on screen was made with no probe: Lean makes it again with its probe.
        // The page must not have changed meanwhile; if it has, the next idle time checks.
        const shownRequest=lastRequest,options={...shownRequest.request.options};delete options.checks;
        const {artifact}=await worker.compile(shownRequest.request.source,shownRequest.width,shownRequest.height,options);
        if(dirty||lastRequest!==shownRequest||document!==shownRequest.document)return;
        result=await session!.draw(artifact,true);
        if(result.presented)recordPresented({...shownRequest,request:{...shownRequest.request,options}},(options.shell as {scroll:number}).scroll);
        if(dirty||lastRequest!==shownRequest||document!==shownRequest.document){dirty=true;return;}
      } else result=await session!.checkLast();
      if(!result?.presented)return;
      checkedFrames++;
      trace("native-html-checked",{frame:frameNumber,why:"idle",idleMs:ms(lastActivity,idleStart),drawMs:Math.round(result.drawMs*10)/10,pixelHash:result.pixelHash});
      // --shot on a page with no animated page canvas: the first idle-checked frame.
      if(shotFile&&!pageGpuMs.length)await takeShot();
    };
    const handle=(event:UIEvent)=>{
        if(event.kind===6){running=false;return;}
        // End input on its owning page, even after a tab change or address focus.
        if(event.kind===4||event.kind===POINTER_CANCEL){
          endPress();holding=undefined;
          if(event.kind===POINTER_CANCEL){
            const cancelled=press;press=undefined;
            if(view.selection){view.selection=undefined;dirty=true;}
            if(cancelled){
              if((cancelled.page as Page).graph)graphInput(4,cancelled.points[2],cancelled.points[3],cancelled.page);
              else scriptPointer("cancel",cancelled.points[2],cancelled.points[3],cancelled);
            }
            return;
          }
          if(press&&((press.page as Page).graph||press.page!==document)){
            const released=press;press=undefined;movePress(released,event.a,event.b);
            if((released.page as Page).graph)graphInput(4,event.a,event.b,released.page);
            else scriptPointer("up",event.a,event.b,released);
            return;
          }
        }
        if(event.kind===1){
          if(event.a<1||event.b<1)return;
          if(event.a>4096||event.b>4096)throw new Error("Native HTML window exceeds 4096 backing pixels; close or use a smaller window");
          if(event.a!==width||event.b!==height){width=event.a;height=event.b;dirty=true;if((document as Page).graph)graphInput(1,width,height);
            if(scriptsOn&&document.script&&scriptOps.includes("resize")){const page=document;
              (scriptCall("scriptSession","",{action:"resize",session:document.script.session,width,height,zoomUnit:view.zoomUnit??100,shell:shell()}) as Promise<ScriptTurn>)
                .then(turn=>scriptTurn(page,turn,"resize")).catch(error=>console.error("Native HTML: page script resize failed:",String(error)));}resizeAt??=performance.now();trace("native-html-resize",{width,height});}
        }
        if(event.kind===8&&event.a)dirty=true;
        if(event.kind===3)pointAt(event.a,event.b);
        const graph=(document as Page).graph;
        if(graph&&!focused&&(event.kind===3||event.kind===9||(event.kind===5&&!(event.b&2)))){
          if(event.kind===3&&press?.page===document)movePress(press,event.a,event.b);
          graphInput(event.kind,event.a,event.b);return;
        }
        if(event.kind===5&&focused&&!(event.b&2)){
          if(event.a===36)goTo(field.address);
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
        // Keys the menu did not take: space, page up and down, home, end, arrows, escape,
        // Control-Tab. Lean's key table gives the command (issue 1268).
        if(event.kind===5){const id=engine.pageKey(event.a,event.b);if(id!==null)windowCommand(id);}
        if(event.kind===11){closeMenu();if(wheelSum)wheelSum.dy-=event.a/scale;scrollBy(-event.a);}
        // Kind 13, a right click (native_window.m): Lean may open the address menu.
        if(event.kind===13)menuPress(event.a,event.b,"context");
        if(event.kind===3&&holding){holding.x=event.a;holding.y=event.b;}
        if(event.kind===4)holding=undefined;
        if(event.kind===12)gestureWheel(event.a,event.b);
        if(event.kind===5&&event.a===15)windowCommand(8);
        if(event.kind===10)windowCommand(event.a);
        if(event.kind===2){
          // Hit coordinates and boxes belong to the successfully presented frame.
          // One small Lean call: the control or the link pressed, and what the composite darkens.
          const answer=engine.press(shell(),event.a,event.b,width,pageRow(event.b),layered&&current?frame.webRender.links as unknown[]:[]);
          const control=answer.control;
          if(control){
            if(answer.rects.length)startPress({control,rects:answer.rects});
            if(control!=="address"&&control!=="copyAddress"&&control!=="pasteGo")closeMenu();
            chrome(control);
            if(control==="address")holding={x:event.a,y:event.b,startX:event.a,startY:event.b,at:performance.now()};
            return;
          }
          if(focused)leaveAddress();
          press=beginPress(document,event.a,event.b);
          if((document as Page).graph){graphInput(2,event.a,event.b);return;}
          scriptPointer("down",event.a,event.b,press);
          if(typeof answer.sourceNode==="number")startPress({active:answer.sourceNode,rects:answer.rects});
          if(view.selection){view.selection=undefined;dirty=true;}
        }
        // `:hover` (links only): a new frame when the link under the pointer changes, and only
        // when an author rule names `:hover`.
        if(event.kind===3&&!press&&layered&&current?.layers.layers.hoverRules){
          const node=engine.hit(frame,event.a,pageRow(event.b))?.sourceNode;
          if(node!==hoverNode){hoverNode=node;dirty=true;}
        }
        if(event.kind===3&&press&&press.page===document&&!(press.page as Page).graph){view.selection=movePress(press,event.a,event.b);dirty=true;scriptPointer("move",event.a,event.b,press);}
        if(event.kind===4&&press){
          const held=press,released=movePress(held,event.a,event.b);press=undefined;
          scriptPointer("up",released[2],released[3],held);
          if(engine.pointerUp(released)!=="click")return;
          // A click begins the SVG animations whose `begin` is a click on what it hits.
          const clock=animation.get(document);
          if(clock?.has&&current){clock.clicks=[...clock.clicks,[Math.round(performance.now()-clock.epoch),released[0],released[1]-current.layers.layers.top+scroll]].slice(-16);clock.running=true;dirty=true;}
          if(view.selection){view.selection=undefined;dirty=true;}
          // A page with scripts: Lean finds the node under the point, and the click is a task of
          // the page's event loop; Lean runs the listeners in QuickJS and changes its DOM.
          if(scriptsOn&&document.script&&!scriptOps.includes("pointer")){
            const page=held.page,session=page.script!.session,hit=scriptHitRequest(page);
            scriptInput("nodeAt",page.source,hit.width,hit.height,{...hit.options,x:released[0],y:released[1]})
              .then(node=>typeof node==="number"?scriptInput("scriptSession","",{action:"click",session,node}) as Promise<ScriptTurn>:undefined)
              .then(turn=>{if(turn)scriptTurn(page,turn,"click");})
              .catch(error=>console.error("Native HTML: page script click failed:",String(error)));
          }
          const target=engine.hit(frame,released[0],pageRow(released[1]));
          if(target){console.log(JSON.stringify({type:"native-html-link",...target,url:document.url}));
            followRoute(router.route({...site,href:target.href,base:document.baseURL||document.url}) as LinkRoute);}
        }
    };
    while(running){
      const pumpStart=performance.now();if(lastPump!==undefined){pumpGaps.push(pumpStart-lastPump);if(firstFrameAt!==undefined&&lastPump>=firstFrameAt)pumpGapsLate.push(pumpStart-lastPump);if(pumpStart-lastPump>50)trace("native-html-pump-gap",{ms:ms(lastPump,pumpStart),frames:frameNumber,rendering:!!rendering});}lastPump=pumpStart;native.pump();checkHold();const pumpEnd=performance.now();
      if(pumpEnd-pumpStart>30)trace("native-html-pump-stall",{ms:ms(pumpStart,pumpEnd)});
      // Take every native event now and keep each with the time it was taken. None is dropped here.
      // The window library stamps each event when it is queued; its clock maps onto
      // performance.now() through one reading of both. An older library has no clock.
      const arrived=performance.now(),queueClock=native.eventClock(),offset=queueClock===null?null:arrived-queueClock,batch:{event:UIEvent;at:number}[]=[];let taken;
      while((taken=native.next()))batch.push({event:taken,at:offset===null||!taken.time?arrived:Math.min(arrived,taken.time+offset)});
      if(batch.length){lastActivity=arrived;queueMax=Math.max(queueMax,batch.length);
        if(batch.length>QUEUE_WARN)trace("native-html-queue-high",{queued:batch.length});}
      for(const {event,at} of readyInput(batch,firstFrameAt!==undefined)){
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
      if(dirty&&!canPresent()&&!waiting){waiting=true;waitingSince=performance.now();trace("native-html-waiting",{reason:"window can not present",surface:native.surfaceState()});}
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
      if(pressPresent&&!shifting&&current&&canPresent()){
        pressPresent=false;
        const start=performance.now(),p=pressed,shown=current,offset=shownOffset;
        shifting=session!.shift(offset,false).then(result=>{
          trace("native-html-press",{state:p?"down":"up",control:p?.control??null,active:p?.active??null,rects:p?.rects.length??0,
            presented:result.presented,totalMs:ms(start,performance.now()),...(p?{fromQueuedMs:ms(p.at,result.presentedAt)}:{})});
          if(!result.presented){pressPresent=true;return;}
          recordPresented(shown,shown.layers.layers.bandTop+offset);
          if(p&&p===pressed)pressOverlayMs.push(result.presentedAt-p.at);
          lastActivity=Math.max(lastActivity,performance.now());
        }).catch(error=>{fatal=error;}).finally(()=>{shifting=undefined;});
      }
      if(pressed&&!pressed.asked&&!dirty&&!rendering&&performance.now()-pressed.at>=PRESS_FRAME_MS){pressed.asked=true;dirty=true;}
      // A scroll in the band: present the composite at the new offset. A Lean frame in the
      // worker does not wait for this, and this does not wait for it.
      if(shiftPending&&!shifting&&current&&canPresent()){
        shiftPending=false;
        const stamps=awaitingShift;awaitingShift=[];
        // Past the band on screen, a prefetched band of the same state that keeps the scroll is drawn
        // and shown: no Lean wait. Without one, the view stays at the band edge until a band comes.
        const swap=!keeps(current.layers.layers,scroll)&&swapReady()?prefetched!:undefined;
        // Press rectangles are in the rows of the band on screen; another band needs a Lean frame.
        if(swap&&pressed&&session!.pressed){session!.setPress(undefined);dirty=true;}
        if(!swap&&!keeps(current.layers.layers,scroll)&&!bandComing())dirty=true;
        const shown=swap?{...swap.record,layers:swap.layers}:current,shownLayers=shown.layers;
        const start=performance.now(),{offset,exact}=clampOffset(shownLayers.layers,scroll),at=scroll;
        shifting=(swap?session!.drawLayers(swap.layers,swap.record.width,swap.record.height,offset,everyFrame):session!.shift(offset,everyFrame)).then(result=>{
          if(swap&&document!==swap.record.document){awaitingShift=[...stamps,...awaitingShift];dirty=true;return;}
          const finished=performance.now();
          trace("native-html-scroll",{frame:frameNumber,scroll:at,offset,exact,swap:!!swap,totalMs:ms(start,finished),drawMs:Math.round(result.drawMs*10)/10,
            presented:result.presented,checked:result.checked,pixelHash:result.checked?result.pixelHash:null,...(swap?{bandTop:swap.layers.layers.bandTop,target:swap.target}:{})});
          if(swap){
            // The textures hold the prefetched layers now, presented or not.
            current={...swap.record,layers:swap.layers};
            frame=swap.layers.page;lastRequest=swap.record;if(prefetched===swap)prefetched=undefined;
          }
          if(!result.presented){awaitingShift=[...stamps,...awaitingShift];shiftPending=true;return;}
          if(swap)prefetchStats.swaps++;
          shownOffset=offset;shifts.push(finished-start);lastActivity=Math.max(lastActivity,finished);if(result.checked)checkedFrames++;
          recordPresented(shown,shownLayers.layers.bandTop+offset);
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
      if(animationDue&&!rendering&&performance.now()>=gpuHoldUntil){animationDue=false;dirty=true;}
      if(dirty&&canPresent()&&!rendering){
        waiting=false;
        rendering=renderFrame().catch(error=>{fatal=error;}).finally(()=>{rendering=undefined;});
      } else if(!everyFrame&&!dirty&&!animationDue&&!rendering&&!shifting&&!shiftPending&&!pressed&&!pressPresent&&session?.frames&&!session.lastChecked&&canPresent()&&performance.now()-lastActivity>=IDLE_CHECK_MS){
        // Interactive frames are not read back. When input has been idle, the last frame is drawn again with the checks.
        rendering=idleCheck().catch(error=>{fatal=error;}).finally(()=>{rendering=undefined;});
      }
      if(watchSeconds&&firstFrameAt!==undefined&&performance.now()-firstFrameAt>=watchSeconds*1000)running=false;
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
        else if(step==="end"){
          // The page's last row: the bottom of the lowest layout box. The view is the window below the chrome.
          const boxes=frame.webRender.boxes as number[][],bottom=Math.max(0,...boxes.map(box=>box[2]+box[4]));
          const top=current?.layers.layers.top??0,ok=scroll+height-top>=bottom;
          trace("native-html-test-end",{scroll,limit:scrollLimit(),bottom,view:height-top,ok});
          if(!ok){console.error(`Native HTML scroll sweep: the view ends at row ${scroll+height-top}, the page at row ${bottom}`);Deno.exitCode=1;}
        }
        // A page on its way (loading, or prepared and not yet drawn, or a refusal page coming):
        // check the URL after it is shown, at most 20 s later.
        else if(typeof step==="string"&&step.startsWith("url:")&&(loading||candidate||rendering||refusing>0)&&(urlWaitSince??=performance.now())>performance.now()-20000){
          commands.unshift(step);stepAt=performance.now()+50;
        }
        else if(typeof step==="string"&&step.startsWith("url:")){
          urlWaitSince=undefined;
          const ok=document.url.endsWith(step.slice(4));trace("native-html-test-url",{expected:step.slice(4),url:document.url,ok});
          if(!ok){console.error(`Native HTML sweep: expected a page ending ${step.slice(4)}, shown ${document.url}`);Deno.exitCode=1;}
        }
        else if(typeof step==="string"&&step.startsWith("pointer:")){
          const ok=pointerShown===step.slice(8);trace("native-html-test-pointer",{expected:step.slice(8),pointer:pointerShown,ok});
          if(!ok){console.error(`Native HTML sweep: expected the ${step.slice(8)} pointer, shown ${pointerShown}`);Deno.exitCode=1;}
        }
        else if(step==="pageLinks"){
          // The local pages the links name, each once, in page order.
          const hrefs=[...new Set((frame.webRender.links as unknown[][]).map(link=>String(link[1])).filter(href=>/^[a-z0-9-]+\.html$/.test(href)&&href!=="index.html"))];
          trace("native-html-test-links",{count:hrefs.length,hrefs});
          if(hrefs.length<5){console.error(`Native HTML link sweep: ${hrefs.length} page links on the first frame`);Deno.exitCode=1;}
          const start=document.url.slice(document.url.lastIndexOf("/")+1);
          // Each link from the top; then the last one again from the end of the page, so the
          // way back up leaves the band of the end and the click is on a new band.
          const last=hrefs.at(-1)!;
          commands!.unshift(...hrefs.flatMap(href=>[`reveal:${href}`,"hold","hold",`over:${href}`,"pointer:hand",`click:${href}`,`url:${href}`,"[",`url:${start}`]),
            ...Array.from({length:16},()=>[11,-400,0]),"hold","hold","hold",`reveal:${last}`,"hold","hold",`over:${last}`,"pointer:hand",`click:${last}`,`url:${last}`);
        }
        else if(typeof step==="string"&&/^(reveal|over|click):/.test(step)){
          // The link's region in page rows: band rows plus the band top of the layers on screen.
          const href=step.slice(step.indexOf(":")+1),bandTop=current?.layers.layers.bandTop??0;
          const link=(frame.webRender.links as number[][]).find(l=>String(l[1])===href);
          if(!link){console.error(`Native HTML link sweep: no region for ${href} at scroll ${scroll}`);Deno.exitCode=1;}
          else if(step.startsWith("reveal:")){
            // Wheel steps of at most 400 rows, so a long way crosses the band edge on the way.
            let rest=Math.round(link[3]+bandTop+link[5]/2-scroll-(height-(current?.layers.layers.top??0))/2);
            while(rest!==0){const d=Math.max(-400,Math.min(400,rest));native.testEvent(11,-d,0);rest-=d;}
          } else {
            const x=Math.round(link[2]+link[4]/2),y=Math.round(windowRow(link[3]+link[5]/2)),top=current?.layers.layers.top??0;
            const inView=y>=top&&y<height;
            trace("native-html-test-link",{step,scroll,x,y,inView});
            if(!inView){console.error(`Native HTML link sweep: ${href} is drawn at row ${y}, outside the view`);Deno.exitCode=1;}
            if(step.startsWith("over:"))native.testEvent(3,x,y);else{native.testEvent(2,x,y);native.testEvent(4,x,y);}
          }
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
        else if(typeof step==="string"&&/^(tabs|scroll)=/.test(step)){
          const ok=step.startsWith("tabs=")?step===`tabs=${tabs.length}:${active}`:scroll===(step==="scroll=0"?0:Math.floor(scrollLimit()));
          trace("native-html-test-shortcut",{step,ok,tabs:tabs.length,active,scroll,limit:scrollLimit()});
          if(!ok){console.error(`Native HTML shortcut sweep: ${step} failed; ${tabs.length} tabs, tab ${active} shown, scroll ${scroll} of ${scrollLimit()}`);Deno.exitCode=1;}
        }
        else if(typeof step==="string")trace("native-html-test-key",{key:step,handled:native.testKey(step,"+_ZT{}".includes(step))});
        else if(step)native.testEvent(step[0],step[1],step[2]);else{if(native.readClipboard()===lastCopied)native.writeClipboard(savedClipboard);running=false;}
      }
      // Page script timers and animation frames: the virtual clock of the page's event loop
      // follows real time since the page's scripts started. Lean decides what runs, at most
      // one animation frame a turn. Frame pacing: no turn while a frame is pending (asked for
      // or being made), so each presented frame has at most one turn before it.
      const script=document.script;
      if(scriptsOn&&script&&!scriptBusy&&!dirty&&!rendering&&script.turn.nextWake!==null&&performance.now()>=gpuHoldUntil){
        const elapsed=performance.now()-(scriptEpochs.get(script.session)??performance.now());
        if(elapsed>=script.turn.nextWake){
          const page=document;scriptBusy=true;
          (scriptCall("scriptSession","",{action:"advance",session:script.session,ms:Math.max(0,Math.ceil(elapsed-script.turn.clock))}) as Promise<ScriptTurn>)
            .then(turn=>scriptTurn(page,turn,"timers"))
            .catch(error=>console.error("Native HTML: page script timers failed:",String(error)))
            .finally(()=>{scriptBusy=false;});
        }
      }
      // Wake at least every 8 ms to pump, sooner for the page's next timer or animation frame
      // (a fixed 8 ms paced 16 ms frames at about 21 ms); wake at once when a frame ends.
      const wakeIn=scriptsOn&&script&&script.turn.nextWake!==null
        ?script.turn.nextWake-(performance.now()-(scriptEpochs.get(script.session)??performance.now())):8;
      const nap=new Promise(resolve=>setTimeout(resolve,Math.max(1,Math.min(8,Math.ceil(wakeIn)))));
      await Promise.race([nap,...(rendering?[rendering]:[]),...(shifting?[shifting]:[])]);
    }
  } finally {
    running=false;controller?.abort();quitAt=performance.now();
    // Quit or close: no new GPU work from here on; a frame in progress ends with what it has.
    const gpuIdle=session?.halt();
    // A frame in progress ends before its session is disposed.
    try{await rendering;await shifting;}catch(error){console.error("Native HTML frame ended with an error:",String(error));}
    worker?.terminate();
    await browserState?.close().catch(error=>console.error("Native HTML: browser state did not close:",String(error)));
    try{summary();}catch(error){console.error("Native HTML summary failed:",String(error));}
    // The bound of FrameCost.band_render_bound, with one more frame for a prefetch that came late.
    if(scrollSweep&&layered&&current){
      frameCost.reach=keepReach(current.layers.layers);
      const bound=Math.floor(frameCost.scrollRows/(frameCost.reach+1))+1;
      if(frameCost.leanFrames>bound||prefetchStats.sent>bound){
        console.error(`Native HTML frame cost ratchet: ${frameCost.leanFrames} Lean frames and ${prefetchStats.sent} prefetches over ${frameCost.scrollRows} rows; the bound is ${bound} each`);
        Deno.exitCode=1;
      } else console.log(`frame cost: ${frameCost.leanFrames} Lean frames, ${prefetchStats.sent} prefetches over ${frameCost.scrollRows} rows (bound ${bound} each)`);
    }
    try{await gpuIdle;}catch{/* a lost device has nothing in flight */}
    const quitFact={ms:Math.round(performance.now()-quitAt),gpu:session?.stats.gpu??null};
    trace("native-html-quit",quitFact);
    if(!cleanupUI({session,device,native}))Deno.exitCode=1;
  }
}
try{await main();}catch(error){console.error(error);Deno.exitCode=1;}
// Match the existing native UI: do not unload Cocoa classes under a live NSView.
Deno.exit(Deno.exitCode);
