// Host counters for the frame cost ratchet (docs/designissues/2026-11-08-cost-theorems.md,
// issues 1268 and 1292), on the Wasm engine and, when it is built, the native library:
//
// * Hover and :active repaint: a pointer state whose styles change colours only costs no
//   layout (FrameCost.hover_never_layouts); one whose styles change geometry lays out
//   once, and on, off and on again stays at one (hover_geometry_layouts,
//   layout_once_per_distinct_key). Lean counts its own work (`frameWork`).
// * Held images: a render request names its images, so its bytes do not depend on the
//   size of the images; an engine without held images gets the bytes in every request.
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {prepareHTML} from "./native_html_document.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const pageURL=new URL("./pages/frame-work.html",import.meta.url).href;

const colourPage=`<!doctype html><style>p{margin:0}a{color:#0000ee;background-color:#eeeeee}
a:hover{color:#ff0000;background-color:#ffff00}</style><p><a href="https://x.test/a">first link</a> and text</p>`;
const geometryPage=`<!doctype html><style>p{margin:0}a:hover{font-size:30px}</style><p><a href="https://x.test/a">first link</a> and text</p>`;

function hoverWork(engine:HTMLEngine,html:string) {
  const options={url:pageURL};
  const idle=engine.compile(html,400,200,options) as HTMLArtifact;
  const link=idle.webRender.links[0] as [number,string,number,number,number,number];
  assert(link,"the page has a link");
  const hover={...options,hover:link[0]};
  engine.frameWork(true);
  const on=engine.compile(html,400,200,hover);
  const off=engine.compile(html,400,200,options);
  const again=engine.compile(html,400,200,hover);
  const work=engine.frameWork(true)!;
  return {work,changed:JSON.stringify(on.data)!==JSON.stringify(off.data),same:JSON.stringify(on.data)===JSON.stringify(again.data)};
}

function hoverCounts(engine:HTMLEngine) {
  assert(engine.frameWork(),"this engine counts its frame work");
  // Colours only: the layout of the idle page is kept and painted; no layout.
  const colour=hoverWork(engine,colourPage);
  assert.equal(colour.work.layouts,0,`a colour-only hover laid out: ${JSON.stringify(colour.work)}`);
  // On, off, on: the second hover frame is the painted layout kept from the first (WebDocument.keptPainted).
  assert.equal(colour.work.repaints,1,`one hover frame painted, then kept: ${JSON.stringify(colour.work)}`);
  assert(colour.changed,"the hover frame differs from the idle one");
  assert(colour.same,"hover on twice gives one picture");
  // A hover style that changes geometry: one layout with the pointer in the key, kept.
  const geometry=hoverWork(engine,geometryPage);
  assert.equal(geometry.work.layouts,1,`a geometry hover on, off and on: ${JSON.stringify(geometry.work)}`);
  assert.equal(geometry.work.repaints,0);
  assert(geometry.changed&&geometry.same);
  return {colour:colour.work,geometry:geometry.work};
}

// Two pages that differ only in the size of their image: 272 bytes, and a 500 KB file.
const smallImage=`<!doctype html><p><img src="images-badge.png" alt="small"></p>`;
const bigImage=`<!doctype html><p><img src="../../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf" alt="big"></p>`;
const bigBytes=Deno.statSync(new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url)).size;

async function frameBytes(engine:HTMLEngine,html:string,hold=true) {
  // `hold:false` is a host for an engine from before held images: it sends the bytes.
  const host=hold?engine:{...engine,imageInfo:undefined} as unknown as HTMLEngine;
  const document=await prepareHTML(host,pageURL,undefined,html);
  const bytes:number[]=[];
  for(let frame=0;frame<3;frame++){engine.compile(document.source,400,200,document.request(400,200).options);bytes.push(engine.requestBytes().lastRenderBytes);}
  return {bytes,options:document.request(400,200).options};
}

async function imageCounts(engine:HTMLEngine) {
  assert(engine.imageInfo(),"this engine holds images");
  const small=await frameBytes(engine,smallImage),big=await frameBytes(engine,bigImage);
  assert(Array.isArray(small.options.heldImages)&&!("images" in small.options),"renders name held images");
  const key=(o:Record<string,unknown>)=>JSON.stringify(o.heldImages).length;
  for(const bytes of [small.bytes,big.bytes])assert(bytes.every(n=>n===bytes[0]),`the same bytes in each frame: ${bytes}`);
  // The difference is the length of the names, not of the images.
  assert.equal(big.bytes[0]-small.bytes[0],key(big.options)-key(small.options),`bytes per frame ${small.bytes[0]} and ${big.bytes[0]}`);
  assert(big.bytes[0]<4096,`a frame of the big image page sends ${big.bytes[0]} bytes`);
  // Without held images every frame carries the image as Base64.
  const before=await frameBytes(engine,bigImage,false);
  assert(before.bytes[0]>bigBytes,`an old host sends ${before.bytes[0]} bytes for a ${bigBytes} byte image`);
  return {held:big.bytes[0],inline:before.bytes[0],imageBytes:bigBytes};
}

// A frame whose only change is in the chrome (here `loading`) gives the page layer it gave
// before: Lean keeps the page layer answer for the same scene objects (WebDocument.pageArtifact).
function chromeOnlyCounts(engine:HTMLEngine) {
  const html=`<!doctype html><p>${Array.from({length:40},(_,i)=>`<a href="https://x.test/${i}">link ${i}</a>`).join(" ")}</p>`;
  const shell=(loading:boolean)=>({tabs:[{title:"t"}],active:0,address:"https://x.test/",focused:false,canBack:false,canForward:false,loading,scale:1,theme:"light",pages:1,scroll:0,pressed:""});
  const options=(loading:boolean)=>({url:pageURL,shell:shell(loading),checks:false});
  const first=engine.compileLayers(html,800,600,options(false));
  engine.frameWork(true);
  const second=engine.compileLayers(html,800,600,options(true));
  const third=engine.compileLayers(html,800,600,options(false));
  const work=engine.frameWork(true)!;
  assert.equal(work.layouts,0,"no layout: the layout is kept");
  assert.equal(work.pagesMade,0,`no page layer made again: ${JSON.stringify(work)}`);
  assert.equal(work.pagesKept,2,`the page layer kept twice: ${JSON.stringify(work)}`);
  for(const next of [second,third]){
    assert.deepEqual(Array.from(next.page.data),Array.from(first.page.data),"the same page floats");
    assert.equal(next.page.wgsl,first.page.wgsl,"the same page shader");
  }
  assert.notDeepEqual(Array.from(second.chrome.data),Array.from(first.chrome.data),"the chrome is drawn again");
  return work;
}
Deno.test("frame work: a chrome-only frame keeps the page layer, Wasm engine",async()=>{console.log(JSON.stringify(chromeOnlyCounts(await loadHTML())));});
Deno.test({name:"frame work: a chrome-only frame keeps the page layer, native library",ignore:noLibrary,fn:async()=>{console.log(JSON.stringify(chromeOnlyCounts(await loadHTML(library))));}});
Deno.test("frame work: hover repaints, Wasm engine",async()=>{console.log(JSON.stringify(hoverCounts(await loadHTML())));});
Deno.test("frame work: request bytes do not grow with images, Wasm engine",async()=>{console.log(JSON.stringify(await imageCounts(await loadHTML())));});
Deno.test({name:"frame work: hover repaints, native library",ignore:noLibrary,fn:async()=>{console.log(JSON.stringify(hoverCounts(await loadHTML(library))));}});
Deno.test({name:"frame work: request bytes do not grow with images, native library",ignore:noLibrary,fn:async()=>{
  console.log(JSON.stringify(await imageCounts(await loadHTML(library))));
}});
