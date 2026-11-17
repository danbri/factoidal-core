// Two-layer scroll (issue 1268), off screen on the real GPU.
//
// Check (default): for scrolls inside a band made at another scroll, the composite of
// the two Lean layers is compared with one Lean frame at that scroll, pixel by pixel.
// Each layer and each frame is also checked against Lean's CPU probes. The bytes are
// not always equal; the verdicts below say by how much and why.
// --bench: 20 scroll steps of 120 backing pixels down the page. For each step, the
// time of one Lean frame and its draw (the path before layers), and of the composite
// alone (the path with layers), each to the end of the GPU work.
//
// deno run --unstable-webgpu --unstable-ffi --allow-read --allow-ffi scroll_layers_check.ts
//   [--native-engine DYLIB] [--presenter=inline|worker] [--bench] [--html FILE] [--bitmap-font]
// Worker mode compares worker CPU layers through the shared frame slot with the serial
// single-frame GPU oracle. Every worker call finishes before the next serial engine call.
import {loadHTML,loadPresenter,type HTMLArtifact,type HTMLLayers} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML} from "./native_html_document.ts";
import {createLayerRenderer,clampOffset,keeps} from "./layer_compositor.ts";
import {startCompileWorker,type CompileClient} from "./native_html_compile.ts";
import {createPresenter} from "./presenter_host.ts";

const args=[...Deno.args];
let presenterMode:"inline"|"worker"="inline";
let nativeEngine:string|undefined,bench=false,bitmap=false,page=new URL("./pages/status.html",import.meta.url).pathname;
while(args.length){const arg=args.shift();
  if(arg==="--native-engine")nativeEngine=args.shift();
  else if(arg==="--presenter=inline")presenterMode="inline";
  else if(arg==="--presenter=worker")presenterMode="worker";
  else if(arg==="--bench")bench=true;
  else if(arg==="--bitmap-font")bitmap=true;
  else if(arg==="--html")page=args.shift()!;
  else throw new Error(`unknown argument ${arg}`);
}
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter){console.log("NOT RUN: scroll_layers_check.ts needs a GPU adapter");Deno.exit(0);}
const device=await adapter.requestDevice();
// Complete the pure entry's initialisation and serial document preparation before the
// worker loads this same dylib. Its document state must never be called concurrently.
const presenterCall=presenterMode==="worker"?await loadPresenter(nativeEngine):undefined;
const engine=await loadHTML(nativeEngine);
const font={path:new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname,family:"Noto Sans"};
if(!bitmap)await loadFontFile(engine,font.path,font.family);
const doc=await prepareHTML(engine,inputURL(page,true));
const pressDoc=bench?undefined:await prepareHTML(engine,inputURL(new URL("./pages/index.html",import.meta.url).pathname,true));
const W=1600,H=1000,scale=2,format=navigator.gpu.getPreferredCanvasFormat();
const shell=(scroll:number)=>({tabs:[{title:doc.title??""}],active:0,address:doc.url,cursor:0,focused:false,canBack:false,canForward:false,
  loading:false,scale,theme:"next",pages:1,scroll});
const options=(scroll:number,checks:boolean)=>({...doc.request(W,H).options,textScalePercent:150,shell:shell(scroll),...(checks?{}:{checks:false})});
const renderer=createLayerRenderer(device,format);
const target=()=>device.createTexture({size:[W,H],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});
const single=target(),composed=target();
const done=()=>device.queue.onSubmittedWorkDone();
const ms=(a:number,b:number)=>Math.round((b-a)*10)/10;

// The furthest scroll, as the window host computes it from Lean's boxes.
const first:HTMLArtifact=engine.compile(doc.source,W,H,options(0,false));
const bottom=Math.max(0,...((first.webRender.boxes as number[][]|undefined)??[]).map(box=>box[2]+box[4]));
const limit=Math.max(0,bottom-H+60*scale);
console.log(JSON.stringify({type:"scroll-layers-page",presenter:presenterMode,url:doc.url,engine:nativeEngine?"native":"wasm",format,width:W,height:H,limit}));

let worker:CompileClient|undefined;
const presenter=presenterCall?createPresenter(presenterCall,scroll=>worker?.requestBand(scroll)):undefined;
const placement=(layers:HTMLLayers["layers"],scroll:number)=>presenter?presenter.show(layers,scroll):
  {...clampOffset(layers,scroll),kept:keeps(layers,scroll)};
const compileLayers=async(source:string,options:Record<string,unknown>):Promise<HTMLLayers>=>{
  if(!worker)return engine.compileLayers(source,W,H,options);
  const {layers}=await worker.compileLayers(source,W,H,options);
  if(!(layers.chrome.pixels instanceof Uint8Array)||!(layers.page.pixels instanceof Uint8Array))
    throw new Error("worker presenter test requires CPU pixels for both layers");
  return layers;
};
try{
if(presenterMode==="worker")worker=await startCompileWorker(bitmap?undefined:font,nativeEngine,false,true);
if(!bench){
  // Lean's scene shader takes 16 samples at an edge only in a scene of at most this many
  // storage rows (Graphics.lean pixelSampleRefineRowLimit). A band and one frame can fall on
  // different sides: https://github.com/danbri/factoidal/issues/1269 (refinement depends on the
  // row count). Those cases are an expected failure, counted apart, that fails the run if it passes.
  const REFINE_ROWS=65536;
  // Where both take the same rule, the moved geometry rounds to float32 a little differently
  // in the band than in one frame: a few edge pixels differ. More than this is a failure.
  const ROUNDING_PIXELS=32;
  let compared=0,failed=0,expected=0,chromeExpected=0;
  for(const frameScroll of [0,Math.min(limit,1200)]){
    const layers=await compileLayers(doc.source,options(frameScroll,true));
    await renderer.drawLayers(layers,true);
    const place=layers.layers;
    const scrolls=[...new Set([place.keepFrom,frameScroll,frameScroll+120,place.keepTo,place.bandTop+place.bandHeight-place.view,frameScroll-200])]
      .filter(s=>s>=0&&s<=limit&&s>=place.bandTop&&s+place.view<=place.bandTop+place.bandHeight);
    for(const scroll of scrolls){
      const one=engine.compile(doc.source,W,H,options(scroll,true));
      const want=await renderer.drawSingle(one,single,true);
      const {offset,exact}=placement(place,scroll);
      if(!exact)throw new Error(`scroll ${scroll} is not in the band`);
      const got=await renderer.composite(composed,W,H,offset,true);
      compared++;
      let differ=0,worst=0;
      const pixels=new Set<number>();
      for(let i=0;i<want.pixels!.length;i++){const d=Math.abs(want.pixels![i]-got.pixels![i]);if(d){differ++;worst=Math.max(worst,d);pixels.add(i>>2);}}
      const rule=(rows:number)=>rows<=REFINE_ROWS;
      // The chrome rows (above place.top) come from the chrome layer, which is small and so always
      // takes the 16-sample rule; in one frame they take the frame's rule. A chrome with sloped or
      // curved edges (the flat look's round fields and icons) then differs at those edges when the
      // frame is past REFINE_ROWS: issue 1269 again, counted apart. A chrome of whole-pixel
      // rectangles (classic) has no such edges and matches either way.
      const width=W;
      const chromePixels=[...pixels].filter(i=>Math.floor(i/width)<place.top).length;
      const pagePixels=pixels.size-chromePixels;
      const sameRule=rule(one.data.length/4)===rule(layers.page.data.length/4);
      const chromeSameRule=rule(one.data.length/4)===rule(layers.chrome.data.length/4);
      const verdict=sameRule?(pagePixels<=ROUNDING_PIXELS?"pass":"fail"):(pagePixels<=ROUNDING_PIXELS?"stale-expected-failure":"expected-failure-1269");
      const chromeVerdict=chromeSameRule?(chromePixels<=ROUNDING_PIXELS?"pass":"fail"):(chromePixels?"expected-failure-1269":"pass");
      if(verdict==="fail"||verdict==="stale-expected-failure"||chromeVerdict==="fail")failed++;
      if(verdict==="expected-failure-1269")expected++;
      if(chromeVerdict==="expected-failure-1269")chromeExpected++;
      console.log(JSON.stringify({type:"scroll-layers-compare",presenter:presenterMode,frameScroll,bandTop:place.bandTop,scroll,offset,verdict,chromeVerdict,chromePixels,pagePixels,sameBytes:want.hash===got.hash&&differ===0,
        frameHash:want.hash,compositeHash:got.hash,differentPixels:pixels.size,largestDifference:worst,
        rows:{frame:one.data.length/4,page:layers.page.data.length/4,chrome:layers.chrome.data.length/4}}));
    }
  }
  console.log(`scroll layers: ${compared-failed-expected} pass, ${failed} fail, ${expected} expected failures (https://github.com/danbri/factoidal/issues/1269) (out of ${compared} scrolls); chrome edges by the other sampling rule (1269): ${chromeExpected}; presenter=${presenterMode}`);
  if(!compared||compared===expected||failed)Deno.exitCode=1;

  // Press (issue 1268). (1) The composite with Lean's press rectangles of a link: the pixels in
  // the rectangles are darkened (3/4 of each channel, within 1 for rounding), every other pixel
  // is unchanged. (2) A Lean frame with the reload button pressed differs from one with it raised,
  // and only inside the button's box.
  let pressFailed=0;
  // The status page has no link: the press checks use the index page.
  if(!pressDoc)throw new Error("press fixture was not prepared");
  const pressOptions=(checks:boolean,extra:Record<string,unknown>={})=>({...pressDoc.request(W,H).options,textScalePercent:150,shell:{...shell(0),address:pressDoc.url},...(checks?{}:{checks:false}),...extra});
  const layers=await compileLayers(pressDoc.source,pressOptions(true));
  await renderer.drawLayers(layers,true);
  renderer.setPress(undefined);
  const idle=await renderer.composite(composed,W,H,placement(layers.layers,0).offset,true);
  const top=layers.layers.top,links=layers.page.webRender.links as unknown[][];
  const link=links[0] as number[];
  const answer=engine.press({...shell(0),address:pressDoc.url},Math.round(link[2]+link[4]/2),Math.round(link[3]+link[5]/2+top),W,Math.round(link[3]+link[5]/2),links);
  renderer.setPress(answer.rects);
  const down=await renderer.composite(composed,W,H,placement(layers.layers,0).offset,true);
  renderer.setPress(undefined);
  const inside=(x:number,y:number)=>answer.rects.some(([rx,ry,rw,rh])=>x>=rx&&x<rx+rw&&y>=ry&&y<ry+rh);
  let darkened=0,wrong=0;
  for(let i=0;i<idle.pixels!.length;i+=4){
    const x=(i>>2)%W,y=Math.floor((i>>2)/W);
    for(let c=0;c<3;c++){
      const want=inside(x,y)?idle.pixels![i+c]*0.75:idle.pixels![i+c];
      if(Math.abs(down.pixels![i+c]-want)>1)wrong++;
    }
    if(inside(x,y))darkened++;
  }
  if(!answer.rects.length||!darkened||wrong)pressFailed++;
  console.log(JSON.stringify({type:"press-composite",presenter:presenterMode,href:answer.href,rects:answer.rects,darkenedPixels:darkened,wrongChannels:wrong,verdict:answer.rects.length&&darkened&&!wrong?"pass":"fail"}));
  const box=[64*scale,30*scale,28*scale,28*scale];
  const raised=await compileLayers(pressDoc.source,pressOptions(true,{shell:{...shell(0),address:pressDoc.url,pressed:"reload"}}));
  await renderer.drawLayers(raised,true);
  const pressedFrame=await renderer.composite(composed,W,H,placement(raised.layers,0).offset,true);
  let changed=0,outside=0;
  for(let i=0;i<idle.pixels!.length;i+=4){
    if(idle.pixels![i]===pressedFrame.pixels![i]&&idle.pixels![i+1]===pressedFrame.pixels![i+1]&&idle.pixels![i+2]===pressedFrame.pixels![i+2])continue;
    const x=(i>>2)%W,y=Math.floor((i>>2)/W);
    if(x>=box[0]&&x<box[0]+box[2]&&y>=box[1]&&y<box[1]+box[3])changed++;else outside++;
  }
  if(!changed||outside)pressFailed++;
  console.log(JSON.stringify({type:"press-frame",presenter:presenterMode,control:"reload",box,changedPixels:changed,changedOutside:outside,verdict:changed&&!outside?"pass":"fail"}));
  console.log(`press: ${2-pressFailed} pass, ${pressFailed} fail (out of 2); presenter=${presenterMode}`);
  if(pressFailed)Deno.exitCode=1;
} else {
  // Warm both paths once: plans, pipelines and the kept layout.
  await renderer.drawSingle(engine.compile(doc.source,W,H,options(0,false)),single,false);await done();
  let layers=await compileLayers(doc.source,options(0,false));await renderer.drawLayers(layers,false);
  await renderer.composite(composed,W,H,placement(layers.layers,0).offset,false);await done();
  const leanMs:number[]=[],drawSubmitMs:number[]=[],compositeSubmitMs:number[]=[],emptyWaitMs:number[]=[];
  const before:number[]=[],after:number[]=[],refresh:{step:number;ms:number}[]=[];
  let scroll=0;
  for(let step=1;step<=20;step++){
    scroll=Math.min(limit,scroll+120);
    const a=performance.now();
    const one=engine.compile(doc.source,W,H,options(scroll,false));const compiled=performance.now();
    await renderer.drawSingle(one,single,false);const submitted=performance.now();await done();
    before.push(ms(a,performance.now()));leanMs.push(ms(a,compiled));drawSubmitMs.push(ms(compiled,submitted));
    // With layers: the composite at the new offset. A new band is made when Lean's keep range
    // ends; in the window host that runs in the worker while composites go on, so it is timed apart.
    const b=performance.now();
    const {offset,kept}=placement(layers.layers,scroll);
    await renderer.composite(composed,W,H,offset,false);const sent=performance.now();await done();
    after.push(ms(b,performance.now()));compositeSubmitMs.push(ms(b,sent));
    const e=performance.now();device.queue.submit([]);await done();emptyWaitMs.push(ms(e,performance.now()));
    if(!kept){
      const c=performance.now();
      layers=await compileLayers(doc.source,options(scroll,false));await renderer.drawLayers(layers,false);await done();
      refresh.push({step,ms:ms(c,performance.now())});
    }
  }
  // GPU time with the wait's own delay taken out: 20 passes, one wait, less one empty wait.
  const batch=async(draw:()=>Promise<unknown>)=>{const t=performance.now();for(let i=0;i<20;i++)await draw();await done();return Math.round((performance.now()-t-emptyWaitMs[0])/20*100)/100;};
  const compositeBatchMs=await batch(()=>renderer.composite(composed,W,H,placement(layers.layers,scroll).offset,false));
  const lastFrame=engine.compile(doc.source,W,H,options(scroll,false));
  const frameDrawBatchMs=await batch(()=>renderer.drawSingle(lastFrame,single,false));
  const p=(v:number[],q:number)=>[...v].sort((x,y)=>x-y)[Math.min(v.length-1,Math.ceil(q*v.length)-1)];
  console.log(JSON.stringify({type:"scroll-layers-bench",presenter:presenterMode,engine:nativeEngine?"native":"wasm",steps:20,stepPixels:120,
    frameMs:before,compositeMs:after,frameP50:p(before,0.5),compositeP50:p(after,0.5),compositeMax:Math.max(...after),refresh,
    leanP50:p(leanMs,0.5),frameDrawSubmitP50:p(drawSubmitMs,0.5),compositeSubmitP50:p(compositeSubmitMs,0.5),compositeSubmitMax:Math.max(...compositeSubmitMs),emptySubmitWaitP50:p(emptyWaitMs,0.5),compositeGpuMsPerPass:compositeBatchMs,frameDrawGpuMsPerPass:frameDrawBatchMs}));
}
}finally{
  worker?.terminate();
  renderer.dispose();single.destroy();composed.destroy();
}
