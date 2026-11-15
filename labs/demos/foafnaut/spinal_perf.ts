// The Spinal Tap page (pages/spinal-tap-sparql.html, our own demo page) as a measured run on
// the native engine, with no window and no GPU, so that it runs in test.sh and on CI
// (core issue 450). spinal_perf_test.ts asserts fixtures/spinal-perf/budgets.json on it.
//
// The page is loaded as the window loads it: prepareHTML of these host sources, its web font
// (Noto Sans Math, 657 KB) over HTTP from a loopback server, its scripts on BubblePopJS, the
// window's font Noto Sans. Then:
//
// 1. Three layered frames of the page as it is (compileLayers with a shell and checks:false,
//    as the window and the Hub ask for an interactive frame): first layout, then two frames of
//    an unchanged document.
// 2. Three whole-page frames with the CPU probe (compile with checks on: the window's idle
//    check, and the request of perf-run.ts that issue 450 measured), and one without it.
// 3. N animation ticks of 16 ms: one script turn (`advance`: timers, requestAnimationFrame,
//    SVG animation values) and one layered frame at the page clock's time. The page's zoom
//    starts at 600 ms and runs 8.4 s, so 600 ticks (9.6 s of page time) hold all of it.
//
// For each tick: the engine's ms (turn and frame), its frame counters (frameWork: layouts,
// kept layouts, paint-only frames, primitives compiled again and reused), whether the tick
// drew the whole page (a layout, or every primitive compiled again), and the process's RSS
// and JS heap (the engine's Lean heap is in the RSS). Times are wall times of the engine
// calls in this process; the counters are exact and the same on every run of one engine.
//
//   deno run -A --unstable-ffi spinal_perf.ts [--engine LIB] [--ticks N] [--out FILE]
import {dirname,join,resolve} from "node:path";
import {fileURLToPath} from "node:url";
import {loadHTML,type HTMLLayers,type FrameWork} from "./native_html_engine.ts";
import {prepareHTML,loadFontFile,setScriptHost} from "./native_html_document.ts";
import {sceneWork} from "../../../docs/web/hub/foafnaut/scene-work.mjs";

const here=dirname(fileURLToPath(import.meta.url));
const root=resolve(here,"../../..");
// The native library of build-web-render.sh --native: .dylib on macOS, .so on Linux.
export const defaultLibrary=Deno.env.get("WEB_RENDER_DYLIB")??join(here,".build/web-render/engines/libweb-render"+(Deno.build.os==="darwin"?".dylib":".so"));
export const PAGE="labs/demos/foafnaut/pages/spinal-tap-sparql.html";
export const DEFAULT_TICKS=600;
const W=1280,H=800,TICK_MS=16;

type Turn={session:number;changed:boolean;commandCount:number;commands?:unknown[];logs:string[];errors:string[];
  instructions:number;jobs:number;tasks:number;layouts?:number;ns:number;animated?:unknown[]};
type Frame={primitiveCount:number};
type Engine={frameWork:(reset?:boolean)=>FrameWork|undefined;compileLayers:(s:string,w:number,h:number,o:Record<string,unknown>)=>HTMLLayers;
  compile:(s:string,w:number,h:number,o:Record<string,unknown>)=>Frame;scriptSession:(s:string,r:Record<string,unknown>)=>Turn;
  engineBuild?:()=>{commit:string;version:string}};
export type Tick={i:number;turnMs:number;frameMs:number;changed:boolean;animated:number;layouts:number;kept:number;
  paintOnly:number;recompiled:number;reused:number;primitives:number;wholePage:boolean;scriptLayouts:number;
  instructions:number;rss:number;heap:number;
  /** The GPU work of drawing the tick's page layer (scene-work.mjs), in millions of shader
  loop trips: records visited, path edges walked, and edges walked outside the record's clip. */
  drawnPixels:number;listedM:number;segmentsM:number;outsideClipM:number;binnedM:number;rowsM:number;piecesM:number;uploadKB:number;partial:boolean};
type Stat={median:number;p95:number;max:number};
export type SpinalRun={page:string;engine:string;engine_commit?:string;valid:boolean;why?:string;ticks:number;tick_ms:number;
  load_ms:number;web_fonts:string[];
  layered:{first_ms:number;second_ms:number;third_ms:number;second_over_first:number;primitives:number;
    first_work?:FrameWork;second_work?:FrameWork};
  probe:{first_ms:number;second_ms:number;third_ms:number;second_over_first:number;no_probe_ms:number;primitives:number;
    second_work?:FrameWork};
  compile_ms:number;compile_calls:number;
  tick:{turn_ms:Stat;frame_ms:Stat;engine_ms:Stat&{total:number};
    layouts:number;kept:number;paint_only:number;whole_page_ticks:number;layered_ticks:number;changed_ticks:number;
    animated_ticks:number;script_layouts:number;primitives_max:number;recompiled_max:number;recompiled_total:number;
    zoom_driver:string;frame_ms_early:number;frame_ms_late:number;late_over_early:number;
    draw:{segments_m:Stat&{total:number};outside_clip_m:Stat&{total:number};binned_m:Stat&{total:number};rows_m:Stat&{total:number};pieces_m:Stat&{total:number};listed_m:Stat;drawn_pixels:Stat;upload_kb:Stat;partial_ticks:number}};
  rss_mb:{start:number;end:number;growth:number;growth_after_warmup:number;peak:number};
  heap_mb:{start:number;end:number;growth:number};
  script:{errors:number;first_error?:string};
  ticks_detail:Tick[];run_ms:number};

const r1=(x:number)=>Math.round(x*10)/10;
const r2=(x:number)=>Math.round(x*100)/100;
const stat=(xs:number[]):Stat=>{
  const s=[...xs].sort((a,b)=>a-b),q=(p:number)=>s.length?s[Math.min(s.length-1,Math.floor(p*s.length))]:0;
  return {median:r1(q(0.5)),p95:r1(q(0.95)),max:r1(s.length?s[s.length-1]:0)};
};
const mb=(b:number)=>r1(b/1048576);
const delta=(a:FrameWork|undefined,b:FrameWork|undefined,k:keyof FrameWork)=>((b?.[k] as number|undefined)??0)-((a?.[k] as number|undefined)??0);

/** One run: load the page, the layered and whole-page frames, then `ticks` animation ticks. */
export async function measure({library=defaultLibrary,ticks=DEFAULT_TICKS}:{library?:string;ticks?:number}={}):Promise<SpinalRun> {
  const t0=performance.now();
  const engine=await loadHTML(library) as unknown as Engine;
  await loadFontFile(engine as never,join(root,"third_party/fonts/noto-sans/NotoSans-Regular.ttf"),"Noto Sans");
  let compileMs=0,compileCalls=0;
  const timed=<T>(f:()=>T):{v:T;ms:number}=>{const s=performance.now();const v=f();const ms=performance.now()-s;compileMs+=ms;compileCalls++;return {v,ms};};
  // The page and its font over HTTP, as a site serves them: only the lab's files and the fonts.
  const types:Record<string,string>={html:"text/html; charset=utf-8",css:"text/css; charset=utf-8",js:"text/javascript; charset=utf-8",
    svg:"image/svg+xml",ttf:"font/ttf",json:"application/json"};
  const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen(){}},async req=>{
    const path=decodeURIComponent(new URL(req.url).pathname).replace(/^\/+/,"");
    if(path.includes("..")||!(path.startsWith("labs/demos/foafnaut/")||path.startsWith("third_party/fonts/")))return new Response("no",{status:403});
    try{return new Response(await Deno.readFile(join(root,path)),{headers:{"content-type":types[path.split(".").pop()!]??"application/octet-stream"}});}
    catch{return new Response("not found",{status:404});}
  });
  const url=`http://127.0.0.1:${server.addr.port}/${PAGE}`;
  const errors:string[]=[];
  let turn:Turn|undefined;
  setScriptHost({start:(source:string,u:string,resources:unknown,encoding?:string,mode?:Record<string,unknown>)=>{
    turn=engine.scriptSession(source,{action:"start",url:u,resources,width:W,height:H,zoomUnit:100,
      layout:{url:u,textScalePercent:100,zoomUnit:100,...(mode??{})},engine:"bubblepop",...(encoding?{encoding}:{})});
    errors.push(...turn.errors);
    return turn;
  }} as never);
  const out:Partial<SpinalRun>={page:PAGE,engine:library,valid:false,ticks,tick_ms:TICK_MS};
  try{out.engine_commit=engine.engineBuild?.().commit;}catch{/* an engine from before engineBuild */}
  try{
    const page=await prepareHTML(engine as never,url,undefined,undefined,{liberal:true}) as unknown as {source:string;title:string;
      request:(w:number,h:number,v?:Record<string,unknown>)=>{source:string;options:Record<string,unknown>};applyTurn:(t:Turn)=>boolean};
    out.load_ms=r1(performance.now()-t0);
    out.web_fonts=((page.request(W,H).options.webFonts as {url:string}[]|undefined)??[]).map(f=>new URL(f.url).pathname.slice(1));
    const shell={tabs:[{title:page.title??""}],active:0,address:url,cursor:0,focused:false,canBack:false,canForward:false,
      loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};
    let clock=0;
    const base=()=>page.request(W,H,{textScalePercent:100,zoomUnit:100}).options;
    const layered=()=>({...base(),shell,checks:false,animationTime:clock,animationClicks:[]});
    // 1. Layered frames of the unchanged page.
    const frame=<T>(f:()=>T)=>{engine.frameWork(true);const r=timed(f);return {...r,work:engine.frameWork()};};
    const l1=frame(()=>engine.compileLayers(page.source,W,H,layered()));
    const l2=frame(()=>engine.compileLayers(page.source,W,H,layered()));
    const l3=frame(()=>engine.compileLayers(page.source,W,H,layered()));
    out.layered={first_ms:r1(l1.ms),second_ms:r1(l2.ms),third_ms:r1(l3.ms),second_over_first:Math.round(l2.ms/l1.ms*1000)/1000,
      primitives:l1.v.page.primitiveCount,first_work:l1.work,second_work:l2.work};
    // 2. Whole-page frames with the CPU probe (checks on), then one without.
    const p1=frame(()=>engine.compile(page.source,W,H,base()));
    const p2=frame(()=>engine.compile(page.source,W,H,base()));
    const p3=frame(()=>engine.compile(page.source,W,H,base()));
    const p0=frame(()=>engine.compile(page.source,W,H,{...base(),checks:false}));
    out.probe={first_ms:r1(p1.ms),second_ms:r1(p2.ms),third_ms:r1(p3.ms),second_over_first:Math.round(p2.ms/p1.ms*1000)/1000,
      no_probe_ms:r1(p0.ms),primitives:p1.v.primitiveCount,second_work:p2.work};
    // 3. The animation ticks, each on the layered path as the window draws them.
    engine.compileLayers(page.source,W,H,layered());
    const mem0=Deno.memoryUsage();
    const list:Tick[]=[];
    for(let i=0;i<ticks;i++){
      let s=performance.now();
      const t=engine.scriptSession("",{action:"advance",session:turn!.session,ms:TICK_MS});
      const turnMs=performance.now()-s;
      errors.push(...t.errors);
      turn=t;clock+=TICK_MS;
      page.applyTurn(t);
      const before=engine.frameWork();
      s=performance.now();
      const l=timed(()=>engine.compileLayers(page.source,W,H,layered())).v;
      const frameMs=performance.now()-s;
      const after=engine.frameWork();
      const primitives=l.page.primitiveCount,recompiled=delta(before,after,"recompiled"),layouts=delta(before,after,"layouts");
      const mem=Deno.memoryUsage();
      // The draw the Hub makes of this answer: the damage rectangles over the last frame, or all.
      const damage=(l.page as unknown as {damage?:{base:number|null;rects:number[][]|null}}).damage;
      const work=sceneWork(l.page,damage?.rects&&damage.base!==null?damage.rects:undefined);
      list.push({drawnPixels:work.drawnPixels,listedM:r2(work.listed/1e6),segmentsM:r2(work.segments/1e6),
        outsideClipM:r2(work.segmentsOutsideClip/1e6),binnedM:r2(work.segmentsBinned/1e6),rowsM:r2(work.segmentsRows/1e6),piecesM:r2(work.pieces/1e6),uploadKB:Math.round(work.uploadBytes/1024),partial:work.partial,i,turnMs:r1(turnMs),frameMs:r1(frameMs),changed:!!t.changed,animated:Array.isArray(t.animated)?t.animated.length:0,
        layouts,kept:delta(before,after,"kept"),paintOnly:delta(before,after,"paintOnly"),recompiled,reused:delta(before,after,"reused"),
        primitives,wholePage:layouts>0||(primitives>0&&recompiled>=primitives),scriptLayouts:t.layouts??0,instructions:t.instructions??0,
        rss:mem.rss,heap:mem.heapUsed});
    }
    const mem1=Deno.memoryUsage();
    const engineMs=list.map(t=>t.turnMs+t.frameMs);
    // Frame time early and late in the animation (the Hub's frames grew slower until the GPU
    // device was lost): the median of the first and of the last quarter of the ticks that moved.
    const moving=list.filter(t=>t.changed||t.animated>0),q=Math.max(1,moving.length>>2);
    const early=stat(moving.slice(0,q).map(t=>t.frameMs)).median,late=stat(moving.slice(-q).map(t=>t.frameMs)).median;
    const animated=list.filter(t=>t.animated>0).length,changed=list.filter(t=>t.changed).length;
    out.tick={turn_ms:stat(list.map(t=>t.turnMs)),frame_ms:stat(list.map(t=>t.frameMs)),
      engine_ms:{...stat(engineMs),total:r1(engineMs.reduce((a,b)=>a+b,0))},
      layouts:list.reduce((a,t)=>a+t.layouts,0),kept:list.reduce((a,t)=>a+t.kept,0),paint_only:list.reduce((a,t)=>a+t.paintOnly,0),
      whole_page_ticks:list.filter(t=>t.wholePage).length,layered_ticks:list.filter(t=>!t.wholePage).length,
      changed_ticks:changed,animated_ticks:animated,script_layouts:list.reduce((a,t)=>a+t.scriptLayouts,0),
      primitives_max:Math.max(0,...list.map(t=>t.primitives)),
      recompiled_max:Math.max(0,...list.filter(t=>!t.wholePage).map(t=>t.recompiled)),
      recompiled_total:list.reduce((a,t)=>a+t.recompiled,0),
      zoom_driver:animated?"svg-animation":changed?"requestAnimationFrame":"none",
      frame_ms_early:early,frame_ms_late:late,late_over_early:early?Math.round(late/early*100)/100:0,
      draw:{segments_m:{...stat(list.map(t=>t.segmentsM)),total:r1(list.reduce((a,t)=>a+t.segmentsM,0))},
        outside_clip_m:{...stat(list.map(t=>t.outsideClipM)),total:r1(list.reduce((a,t)=>a+t.outsideClipM,0))},
        binned_m:{...stat(list.map(t=>t.binnedM)),total:r1(list.reduce((a,t)=>a+t.binnedM,0))},
        rows_m:{...stat(list.map(t=>t.rowsM)),total:r1(list.reduce((a,t)=>a+t.rowsM,0))},
        pieces_m:{...stat(list.map(t=>t.piecesM)),total:r1(list.reduce((a,t)=>a+t.piecesM,0))},
        listed_m:stat(list.map(t=>t.listedM)),drawn_pixels:stat(list.map(t=>t.drawnPixels)),upload_kb:stat(list.map(t=>t.uploadKB)),
        partial_ticks:list.filter(t=>t.partial).length}};
    // Growth after warm-up: from a quarter of the ticks to the end (the first frames of the
    // zoom allocate what every later frame reuses).
    const warm=list[list.length>>2];
    out.rss_mb={start:mb(mem0.rss),end:mb(mem1.rss),growth:mb(mem1.rss-mem0.rss),
      growth_after_warmup:warm?mb(mem1.rss-warm.rss):0,peak:mb(Math.max(mem0.rss,...list.map(t=>t.rss)))};
    out.heap_mb={start:mb(mem0.heapUsed),end:mb(mem1.heapUsed),growth:mb(mem1.heapUsed-mem0.heapUsed)};
    out.ticks_detail=list;
    out.valid=errors.length===0&&list.length===ticks&&(out.web_fonts?.length??0)>0;
    if(errors.length)out.why=`page script errors: ${errors[0].slice(0,200)}`;
    else if(!out.web_fonts?.length)out.why="the page's web font was not loaded";
  }catch(e){
    out.why=`load failed: ${String(e instanceof Error?e.message:e).slice(0,300)}`;
  }finally{
    setScriptHost(undefined);
    await server.shutdown();
  }
  out.compile_ms=r1(compileMs);out.compile_calls=compileCalls;
  out.script={errors:errors.length,...(errors[0]?{first_error:errors[0].slice(0,200)}:{})};
  out.run_ms=r1(performance.now()-t0);
  return out as SpinalRun;
}

/** The run without the per-tick rows: what a report or an issue comment shows. */
export const summary=(run:SpinalRun)=>{const {ticks_detail:_d,...rest}=run;return rest;};

if(import.meta.main){
  const args=Deno.args,opt=(n:string)=>{const i=args.indexOf(n);return i>=0?args[i+1]:undefined;};
  const run=await measure({library:opt("--engine")??defaultLibrary,ticks:Number(opt("--ticks")??DEFAULT_TICKS)});
  const file=opt("--out");
  if(file)Deno.writeTextFileSync(file,JSON.stringify(run)+"\n");
  console.log(JSON.stringify(summary(run),null,1));
  Deno.exit(run.valid?0:1);
}
