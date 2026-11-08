// SVG text in HTML pages (issue 1270): `text`, `tspan` and `textPath` are drawn with the
// fonts that draw HTML text, shaped in Lean (SVGText.lean). The showcase page with text
// round a circle, on a wave, rotated, anchored and in tspans renders, and its SVG text
// gives glyph paths. Run on the Wasm engine and, when it is built, the native library.
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML} from "./native_html_document.ts";

const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const page=new URL("./pages/showcase-textpath.html",import.meta.url).pathname;
const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();

const html=(svg:string)=>`<!doctype html><html lang="en"><head><meta charset="utf-8"><title>t</title></head><body>${svg}</body></html>`;
const options={url:"https://example.test/",resources:[],checks:false};
type Frame={primitiveCount:number};

async function check(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,font,"Noto Sans");
  const count=(svg:string)=>(engine.compile(html(svg),400,200,options) as unknown as Frame).primitiveCount;
  const svg=(body:string)=>`<svg width="400" height="200" viewBox="0 0 400 200">${body}</svg>`;
  const none=count(svg(""));

  // One path for each glyph with ink; a space has none.
  assert.equal(count(svg(`<text x="10" y="50" font-size="20">Lean</text>`))-none,4,"text");
  assert.equal(count(svg(`<text x="10" y="50">Le<tspan dy="5" fill="red">an</tspan> it</text>`))-none,6,"tspan");
  // Font properties on a container are read, and do not refuse the page.
  assert.equal(count(svg(`<g font-family="Noto Sans" font-size="30" style="font-weight:400"><text x="10" y="50">ab</text></g>`))-none,2,"group");
  // A path 100 units long holds the middle of each glyph that fits; the rest is not drawn.
  const path=`<defs><path id="p" d="M10 100H110"/></defs>`;
  assert.equal(count(svg(path+`<text font-size="20"><textPath href="#p">AB</textPath></text>`))-none,2,"textPath");
  const long=count(svg(path+`<text font-size="20"><textPath href="#p">AAAAAAAAAAAAAAAAAAAA</textPath></text>`))-none;
  assert(long>0&&long<20,`glyphs past the end of the path are drawn: ${long} of 20`);
  // A missing path draws nothing and refuses nothing.
  assert.equal(count(svg(`<text><textPath href="#none">AB</textPath></text>`)),none,"missing path");

  // The showcase page renders, and its SVG text is drawn.
  const doc=await prepareHTML(engine,inputURL(page,true));
  const frame=doc.compile(900,1100) as unknown as Frame;
  const source=await Deno.readTextFile(page);
  const bare=source.replace(/<text\b[\s\S]*?<\/text>/g,"");
  const plain=(await prepareHTML(engine,inputURL(page,true),undefined,bare)).compile(900,1100) as unknown as Frame;
  const glyphs=frame.primitiveCount-plain.primitiveCount;
  assert(glyphs>=140,`showcase SVG text gives ${glyphs} glyph paths; at least 140 expected`);
}

Deno.test("SVG text, tspan and textPath are drawn with the held font (Wasm)",()=>check());
Deno.test({name:"SVG text, tspan and textPath are drawn with the held font (native library)",ignore:noLibrary,fn:()=>check(library)});
