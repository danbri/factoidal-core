// Chrome pixels on the real GPU (issue 1268), off screen. A selected address differs from
// the same address with the caret only inside the address box (Lean's own hit test of the
// chrome gives the box), and some pixels there have the selection colour. The SVG tab
// icon of the page changes only the tab box.
//
// deno run --unstable-webgpu --unstable-ffi --allow-read --allow-ffi chrome_pixels_check.ts [--native-engine DYLIB]
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,prepareHTML} from "./native_html_document.ts";
import {createLayerRenderer} from "./layer_compositor.ts";

const args=[...Deno.args];
let nativeEngine:string|undefined;
while(args.length){const arg=args.shift();if(arg==="--native-engine")nativeEngine=args.shift();else throw new Error(`unknown argument ${arg}`);}
const adapter=await navigator.gpu?.requestAdapter();
if(!adapter){console.log("NOT RUN: chrome_pixels_check.ts needs a GPU adapter");Deno.exit(0);}
const device=await adapter.requestDevice();
const engine=await loadHTML(nativeEngine);
const doc=await prepareHTML(engine,inputURL(new URL("./pages/index.html",import.meta.url).pathname,true));
const W=1200,H=400,scale=2,format=navigator.gpu.getPreferredCanvasFormat();
const renderer=createLayerRenderer(device,format);
const target=device.createTexture({size:[W,H],format,usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});
const base={tabs:[{title:doc.title??""}],active:0,address:doc.url,focused:true,canBack:false,canForward:false,
  loading:false,scale,theme:"next",pages:1,scroll:0};
const draw=async(shell:Record<string,unknown>)=>
  (await renderer.drawSingle(engine.compile(doc.source,W,H,{...doc.request(W,H).options,textScalePercent:150,shell,checks:false}),target,true)).pixels!;
// The box of a control: every point where Lean's hit test answers its name.
const boxOf=(shell:Record<string,unknown>,name:string)=>{
  let x0=W,y0=H,x1=-1,y1=-1;
  for(let y=0;y<120*scale;y+=2)for(let x=0;x<W;x+=2)if(engine.shellHit(shell,x,y,W)===name){x0=Math.min(x0,x);y0=Math.min(y0,y);x1=Math.max(x1,x+2);y1=Math.max(y1,y+2);}
  return [x0,y0,x1,y1];
};
// Pixels that differ, inside and outside a box (BGRA or RGBA: all channels compared).
const compare=(a:Uint8Array,b:Uint8Array,[x0,y0,x1,y1]:number[])=>{
  let inside=0,outside=0;
  for(let i=0;i<a.length;i+=4){
    if(a[i]===b[i]&&a[i+1]===b[i+1]&&a[i+2]===b[i+2])continue;
    const x=(i>>2)%W,y=Math.floor((i>>2)/W);
    if(x>=x0&&x<x1&&y>=y0&&y<y1)inside++;else outside++;
  }
  return {inside,outside};
};
let failed=0;
const caret=await draw({...base,cursor:doc.url.length,anchor:doc.url.length});
const selected=await draw({...base,cursor:doc.url.length,anchor:0});
const box=boxOf(base,"address");
const diff=compare(caret,selected,box);
// The selection blue, rgb(0,99,225), in either byte order.
let blue=0;
for(let i=0;i<selected.length;i+=4){
  const [p,g,q]=[selected[i],selected[i+1],selected[i+2]];
  if(g>=95&&g<=103&&((p<=4&&q>=221)||(q<=4&&p>=221)))blue++;
}
const ok=diff.inside>0&&diff.outside===0&&blue>0;
if(!ok)failed++;
console.log(JSON.stringify({type:"chrome-pixels-selection",box,changedInside:diff.inside,changedOutside:diff.outside,selectionBluePixels:blue,verdict:ok?"pass":"fail"}));
// The tab icon (HTML §4.6.7.8): the page's SVG icon changes only the tab, and draws its pink.
const icon=engine.iconPrepare(doc.iconBase64??"",scale);
const plain={...base,focused:false,cursor:0,anchor:0};
const without=await draw(plain);
const withIcon=await draw({...plain,tabs:[{title:doc.title??"",icon}]});
const tab=boxOf(plain,"tab:0");
const iconDiff=compare(without,withIcon,tab);
let pink=0;
for(let i=0;i<withIcon.length;i+=4){
  const [p,g,q]=[withIcon[i],withIcon[i+1],withIcon[i+2]];
  if(g>=24&&g<=40&&((p>=216&&q>=130&&q<=146)||(q>=216&&p>=130&&p<=146)))pink++;
}
const iconOk=icon.kind==="svg"&&iconDiff.inside>0&&iconDiff.outside===0&&pink>0;
if(!iconOk)failed++;
console.log(JSON.stringify({type:"chrome-pixels-icon",kind:icon.kind,box:tab,changedInside:iconDiff.inside,changedOutside:iconDiff.outside,iconPinkPixels:pink,verdict:iconOk?"pass":"fail"}));
console.log(`chrome pixels: ${2-failed} pass, ${failed} fail (out of 2)`);
if(failed)Deno.exitCode=1;
