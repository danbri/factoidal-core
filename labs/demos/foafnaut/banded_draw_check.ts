// A heavy frame drawn in bands (layer_compositor.ts drawScene `bands`, native_html_session.ts,
// issue 450) gives the bytes of the frame drawn in one pass: the Spinal Tap page and the
// status page, at 1, 3 and 7 bands, on this machine's GPU. NOT RUN with no GPU adapter or no
// native engine. Also prints the time of each way (one sample each; the shared Mac is loaded).
// Run: deno run --no-check --unstable-webgpu --unstable-ffi --allow-read --allow-ffi --allow-env --allow-net=127.0.0.1 banded_draw_check.ts
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML} from "./native_html_document.ts";
import {createLayerRenderer} from "./layer_compositor.ts";

const library=Deno.env.get("WEB_RENDER_DYLIB")??new URL("./.build/web-render/engines/libweb-render."+(Deno.build.os==="darwin"?"dylib":"so"),import.meta.url).pathname;
try{Deno.statSync(library);}catch{console.log(`NOT RUN: banded_draw_check.ts needs the native engine (${library})`);Deno.exit(0);}
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter){console.log("NOT RUN: banded_draw_check.ts needs a GPU adapter");Deno.exit(0);}
const device=await adapter.requestDevice();
const engine=await loadHTML(library);
await loadFontFile(engine,new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname,"Noto Sans");
const W=1280,H=800,format=navigator.gpu.getPreferredCanvasFormat();
const target=()=>device.createTexture({size:[W,H],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});
let failed=0;
for(const name of ["status.html","spinal-tap-sparql.html"]){
  const doc=await prepareHTML(engine,inputURL(new URL(`./pages/${name}`,import.meta.url).pathname,true),undefined,undefined,{liberal:true});
  const shell={tabs:[{title:doc.title??""}],active:0,address:doc.url,cursor:0,focused:false,canBack:false,canForward:false,loading:false,scale:1,theme:"light",pages:1,scroll:0};
  const layers=engine.compileLayers(doc.source,W,H,{...doc.request(W,H).options,shell,checks:false});
  const hashes:string[]=[];
  for(const count of [1,3,7]){
    // A new renderer each time: no texture holds an earlier draw.
    const renderer=createLayerRenderer(device,format);
    let betweens=0;
    const t=performance.now();
    await renderer.drawLayers(layers,false,count>1?{count,between:async()=>{betweens++;await device.queue.onSubmittedWorkDone();}}:undefined);
    const result=await renderer.composite(target(),W,H,0,true);
    await device.queue.onSubmittedWorkDone();
    const ms=Math.round(performance.now()-t);
    hashes.push(result.hash);
    console.log(JSON.stringify({page:name,bands:count,betweens,ms,hash:result.hash}));
  }
  if(new Set(hashes).size!==1){failed++;console.log(`FAIL ${name}: the bands give other pixels`);}
}
console.log(failed?`banded draw check: ${failed} failures`:"banded draw check: pass");
Deno.exit(failed?1:0);
