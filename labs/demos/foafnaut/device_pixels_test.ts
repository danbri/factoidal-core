// Device pixels (dprfix, 2026-11-09; WebDocument, section "Device pixels"): a render with
// `zoomUnit` lays the page out in CSS pixels and draws it at that ratio. The same window on
// a 1x and a 2x screen (twice the device pixels on each side, twice the zoom, zoom unit 200)
// must give the same layout: every box, glyph run and link of the 2x frame is the 1x one
// times two. Before, the Hub and the native window laid out in device pixels and scaled only
// the text, so on a Retina screen a 16px margin drew as 8 CSS px and a 760px column as 380.
// Also: no zoomUnit is the answer of before (zoom unit 100), and page scripts see CSS pixels.
// Wasm engine, and the native library when it is built. Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML,setScriptHost} from "./native_html_document.ts";

const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const pagesDir=new URL("./pages/",import.meta.url).pathname;
const pages=["spinal-tap-sparql.html","showcase.html"];
// The Hub's desktop window: 1440 by 900 CSS px, text zoom 200% of a usual browser's.
const W=1440,H=900,PERCENT=200;

type Box=[number,number,number,number,number];
const boxesOf=(a:HTMLArtifact)=>a.webRender.boxes as Box[];
const runsOf=(a:HTMLArtifact)=>a.webRender.glyphRuns as {source:number;size:number;glyphs:number[][]}[]|undefined;
function scaled(one:HTMLArtifact,two:HTMLArtifact,k:number,label:string){
  const a=boxesOf(one),b=boxesOf(two);
  assert.equal(b.length,a.length,`${label}: box count`);
  a.forEach((box,i)=>{
    assert.equal(b[i][0],box[0],`${label}: box ${i} source`);
    for(let j=1;j<5;j++)assert.ok(Math.abs(b[i][j]-box[j]*k)<1e-6,`${label}: box ${i} [${j}] is ${b[i][j]} at ${k}x, ${box[j]} at 1x`);
  });
  const ra=runsOf(one)??[],rb=runsOf(two)??[];
  assert.equal(rb.length,ra.length,`${label}: glyph run count`);
  ra.forEach((run,i)=>assert.ok(Math.abs(rb[i].size-run.size*k)<1e-6&&rb[i].glyphs.length===run.glyphs.length,`${label}: run ${i} size`));
  assert.equal(two.webRender.links.length,one.webRender.links.length,`${label}: link count`);
  return a.length;
}
async function check(nativeEngine?:string){
  const engine:HTMLEngine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,font,"Noto Sans","bytes");
  let boxes=0;
  for(const name of pages){
    const doc=await prepareHTML(engine,inputURL(pagesDir+name,true));
    // 2x at the reported 1440 by 900; 3x (a phone's ratio) at 1360 by 900, under 4096 device px.
    for(const [k,w] of [[2,W],[3,1360]]){
      const {source,options}=doc.request(w,H);
      const at=(k:number,extra:Record<string,unknown>={})=>engine.compile(source,w*k,H*k,{...options,checks:false,textScalePercent:PERCENT*k,...extra});
      const one=at(1);
      // zoomUnit 100 is the answer of before, field for field.
      assert.deepEqual(boxesOf(at(1,{zoomUnit:100})),boxesOf(one),`${name}: zoomUnit 100 changes the layout`);
      boxes+=scaled(one,at(k,{zoomUnit:100*k}),k,`${name} at ${k}x`);
    }
  }
  // A fixture with the reported lengths: a 16px body margin and a 760px column are 32 and
  // 1520 device pixels at 2x, so the column is 760 CSS px wide, as at 1x.
  const html="<!doctype html><style>body{margin:16px}main{width:760px;padding:8px}p{margin:0}</style><main id=m><p>A column of text.</p></main>";
  const two=engine.compile(html,2*W,2*H,{checks:false,textScalePercent:2*PERCENT,zoomUnit:200});
  const main=boxesOf(two).find(b=>b[1]===32&&b[3]===2*(760+16));
  assert.ok(main,`no 760 CSS px column at x 16 CSS px in ${JSON.stringify(boxesOf(two).slice(0,6))}`);
  return boxes;
}
// The layout is what is compared: the pages' scripts are not started (no turn), so both frames are of the same DOM.
setScriptHost({start:()=>undefined} as unknown as Parameters<typeof setScriptHost>[0]);
const hasLibrary=(()=>{try{Deno.statSync(library);return true;}catch{return false;}})();
Deno.test("a 2x and a 3x frame are the 1x layout scaled (Wasm)",async()=>{
  const boxes=await check();console.log(`Wasm: ${boxes} boxes scaled`);
});
Deno.test({name:"a 2x and a 3x frame are the 1x layout scaled (native library)",ignore:!hasLibrary,
  fn:async()=>{const boxes=await check(library);console.log(`native: ${boxes} boxes scaled`);}});
