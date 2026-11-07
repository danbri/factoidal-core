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
//   [--native-engine DYLIB] [--bench] [--html FILE] [--bitmap-font]
import {loadHTML,type HTMLArtifact} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML} from "./native_html_document.ts";
import {createLayerRenderer,clampOffset,keeps} from "./layer_compositor.ts";

const args=[...Deno.args];
let nativeEngine:string|undefined,bench=false,bitmap=false,page=new URL("./pages/status.html",import.meta.url).pathname;
while(args.length){const arg=args.shift();
  if(arg==="--native-engine")nativeEngine=args.shift();
  else if(arg==="--bench")bench=true;
  else if(arg==="--bitmap-font")bitmap=true;
  else if(arg==="--html")page=args.shift()!;
  else throw new Error(`unknown argument ${arg}`);
}
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter){console.log("NOT RUN: scroll_layers_check.ts needs a GPU adapter");Deno.exit(0);}
const device=await adapter.requestDevice();
const engine=await loadHTML(nativeEngine);
if(!bitmap)await loadFontFile(engine,new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname,"Noto Sans");
const doc=await prepareHTML(engine,inputURL(page,true));
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
console.log(JSON.stringify({type:"scroll-layers-page",url:doc.url,engine:nativeEngine?"native":"wasm",format,width:W,height:H,limit}));

if(!bench){
  // Lean's scene shader takes 16 samples at an edge only in a scene of at most this many
  // storage rows (Graphics.lean pixelSampleRefineRowLimit). A band and one frame can fall on
  // different sides: https://github.com/danbri/factoidal/issues/1269 (refinement depends on the
  // row count). Those cases are an expected failure, counted apart, that fails the run if it passes.
  const REFINE_ROWS=65536;
  // Where both take the same rule, the moved geometry rounds to float32 a little differently
  // in the band than in one frame: a few edge pixels differ. More than this is a failure.
  const ROUNDING_PIXELS=32;
  let compared=0,failed=0,expected=0;
  for(const frameScroll of [0,Math.min(limit,1200)]){
    const layers=engine.compileLayers(doc.source,W,H,options(frameScroll,true));
    await renderer.drawLayers(layers,true);
    const place=layers.layers;
    const scrolls=[...new Set([place.keepFrom,frameScroll,frameScroll+120,place.keepTo,place.bandTop+place.bandHeight-place.view,frameScroll-200])]
      .filter(s=>s>=0&&s<=limit&&s>=place.bandTop&&s+place.view<=place.bandTop+place.bandHeight);
    for(const scroll of scrolls){
      const one=engine.compile(doc.source,W,H,options(scroll,true));
      const want=await renderer.drawSingle(one,single,true);
      const {offset,exact}=clampOffset(place,scroll);
      if(!exact)throw new Error(`scroll ${scroll} is not in the band`);
      const got=await renderer.composite(composed,W,H,offset,true);
      compared++;
      let differ=0,worst=0;
      const pixels=new Set<number>();
      for(let i=0;i<want.pixels!.length;i++){const d=Math.abs(want.pixels![i]-got.pixels![i]);if(d){differ++;worst=Math.max(worst,d);pixels.add(i>>2);}}
      const rule=(rows:number)=>rows<=REFINE_ROWS;
      const sameRule=rule(one.data.length/4)===rule(layers.page.data.length/4);
      const verdict=sameRule?(pixels.size<=ROUNDING_PIXELS?"pass":"fail"):(pixels.size<=ROUNDING_PIXELS?"stale-expected-failure":"expected-failure-1269");
      if(verdict==="fail"||verdict==="stale-expected-failure")failed++;
      if(verdict==="expected-failure-1269")expected++;
      console.log(JSON.stringify({type:"scroll-layers-compare",frameScroll,bandTop:place.bandTop,scroll,offset,verdict,sameBytes:want.hash===got.hash&&differ===0,
        frameHash:want.hash,compositeHash:got.hash,differentPixels:pixels.size,largestDifference:worst,
        rows:{frame:one.data.length/4,page:layers.page.data.length/4,chrome:layers.chrome.data.length/4}}));
    }
  }
  console.log(`scroll layers: ${compared-failed-expected} pass, ${failed} fail, ${expected} expected failures (https://github.com/danbri/factoidal/issues/1269) (out of ${compared} scrolls)`);
  if(!compared||compared===expected||failed)Deno.exitCode=1;
} else {
  // Warm both paths once: plans, pipelines and the kept layout.
  await renderer.drawSingle(engine.compile(doc.source,W,H,options(0,false)),single,false);await done();
  let layers=engine.compileLayers(doc.source,W,H,options(0,false));await renderer.drawLayers(layers,false);
  await renderer.composite(composed,W,H,0,false);await done();
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
    const {offset}=clampOffset(layers.layers,scroll);
    await renderer.composite(composed,W,H,offset,false);const sent=performance.now();await done();
    after.push(ms(b,performance.now()));compositeSubmitMs.push(ms(b,sent));
    const e=performance.now();device.queue.submit([]);await done();emptyWaitMs.push(ms(e,performance.now()));
    if(!keeps(layers.layers,scroll)){
      const c=performance.now();
      layers=engine.compileLayers(doc.source,W,H,options(scroll,false));await renderer.drawLayers(layers,false);await done();
      refresh.push({step,ms:ms(c,performance.now())});
    }
  }
  // GPU time with the wait's own delay taken out: 20 passes, one wait, less one empty wait.
  const batch=async(draw:()=>Promise<unknown>)=>{const t=performance.now();for(let i=0;i<20;i++)await draw();await done();return Math.round((performance.now()-t-emptyWaitMs[0])/20*100)/100;};
  const compositeBatchMs=await batch(()=>renderer.composite(composed,W,H,clampOffset(layers.layers,scroll).offset,false));
  const lastFrame=engine.compile(doc.source,W,H,options(scroll,false));
  const frameDrawBatchMs=await batch(()=>renderer.drawSingle(lastFrame,single,false));
  const p=(v:number[],q:number)=>[...v].sort((x,y)=>x-y)[Math.min(v.length-1,Math.ceil(q*v.length)-1)];
  console.log(JSON.stringify({type:"scroll-layers-bench",engine:nativeEngine?"native":"wasm",steps:20,stepPixels:120,
    frameMs:before,compositeMs:after,frameP50:p(before,0.5),compositeP50:p(after,0.5),compositeMax:Math.max(...after),refresh,
    leanP50:p(leanMs,0.5),frameDrawSubmitP50:p(drawSubmitMs,0.5),compositeSubmitP50:p(compositeSubmitMs,0.5),compositeSubmitMax:Math.max(...compositeSubmitMs),emptySubmitWaitP50:p(emptyWaitMs,0.5),compositeGpuMsPerPass:compositeBatchMs,frameDrawGpuMsPerPass:frameDrawBatchMs}));
}
renderer.dispose();single.destroy();composed.destroy();
