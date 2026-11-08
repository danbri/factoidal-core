// Fallback fonts: the engine holds a list of fonts, and Lean draws each character with
// the first font that has it (SfntProfile.runsOf, wordIn). Noto Sans has no Armenian;
// Noto Sans Armenian does. Run on the Wasm engine and, when it is built, the native
// library. Run with --allow-read --allow-ffi.
//
// The native library is one process with one list of held fonts, so each check uses one
// engine and changes its fonts in order, and keeps copies of the frames it compares.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

const fonts=new URL("../../../third_party/fonts/",import.meta.url).pathname;
const sans=fonts+"noto-sans/NotoSans-Regular.ttf",armenian=fonts+"noto-sans-armenian/NotoSansArmenian-Regular.ttf";
const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();

const latin="<!doctype html><p>Fallback fonts draw what the first font lacks.</p>";
// "Hello, world" in Armenian, a word with Latin and Armenian in it, and Latin again.
const mixed="<!doctype html><p>Բարեւ աշխարհ. Latin and Հայերեն, mixed: abcԱԲԳdef.</p>";
const onlyArmenian="<!doctype html><p>Բարեւ աշխարհ</p>";

type Frame={data:Float32Array;primitives:number};
const frame=(engine:HTMLEngine,html:string):Frame=>{
  const scene:HTMLArtifact=engine.compile(html,600,120,{checks:false,url:"file:///fonts.html"});
  return {data:Float32Array.from(scene.data as Float32Array),primitives:scene.primitiveCount};
};
const same=(a:Frame,b:Frame)=>a.data.length===b.data.length&&a.data.every((v,i)=>Object.is(v,b.data[i]));
/** The same primitives, with every stored value within `tolerance` (pixels, or colour
in 0..1, which does not change here). */
const close=(a:Frame,b:Frame,tolerance:number)=>a.primitives===b.primitives&&a.data.length===b.data.length&&
  a.data.every((v,i)=>Math.abs(v-b.data[i])<=tolerance);

async function check(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  assert.deepEqual(await loadFontFile(engine,sans,"Noto Sans"),{family:"Noto Sans",glyphs:3884,fonts:1});
  const latinPlain=frame(engine,latin),mixedPlain=frame(engine,mixed);

  // The Armenian font first, alone: the reference for Armenian drawn through fallback.
  assert.equal((await loadFontFile(engine,armenian,"Noto Sans Armenian")).fonts,1);
  const armenianFirst=frame(engine,onlyArmenian);

  // Noto Sans, then Noto Sans Armenian as a fallback.
  assert.equal((await loadFontFile(engine,sans,"Noto Sans")).fonts,1);
  const added=await loadFontFile(engine,armenian,"Noto Sans Armenian","bytes",true);
  assert.equal(added.family,"Noto Sans Armenian");
  assert.equal(added.fonts,2);
  // A page the first font draws alone is the same with a fallback font held.
  assert(same(latinPlain,frame(engine,latin)),"a Latin page changed when a fallback font was added");
  // Armenian is .notdef boxes in Noto Sans alone, and Armenian glyphs with the fallback.
  const mixedFallback=frame(engine,mixed);
  assert(!same(mixedPlain,mixedFallback),"the fallback font did not change an Armenian page");
  // Armenian through the fallback font is Armenian in that font. The two fonts have
  // 1000 units to the em and ascents of 1069 and 1068, so the baseline can differ by
  // a small part of a pixel, and the space comes from Noto Sans.
  const armenianFallback=frame(engine,onlyArmenian);
  assert(close(armenianFallback,armenianFirst,0.5),"Armenian through the fallback font is not Armenian in that font");

  // The same fallback font again is held once; a load without fallback replaces the list.
  assert.equal((await loadFontFile(engine,armenian,"Noto Sans Armenian","bytes",true)).fonts,2);
  assert.equal((await loadFontFile(engine,sans,"Noto Sans")).fonts,1);
  assert(same(mixedPlain,frame(engine,mixed)),"replacing the list did not drop the fallback font");

  // The text path (Base64 in JSON) holds the same list and draws the same frames.
  const text=await loadHTML(nativeEngine,"text");
  assert.equal((await loadFontFile(text,sans,"Noto Sans","text")).fonts,1);
  assert.equal((await loadFontFile(text,armenian,"Noto Sans Armenian","text",true)).fonts,2);
  assert(same(mixedFallback,frame(text,mixed)),"bytes and text font loads give different frames");
}

Deno.test("fallback fonts draw what the first font lacks (Wasm)",()=>check());
Deno.test({name:"fallback fonts draw what the first font lacks (native library)",ignore:noLibrary,fn:()=>check(library)});

// The writing-systems page with its thirteen fallback fonts, as a 390 CSS px phone at 3
// device pixels to the CSS pixel opens it: text zoom 450 (150 times the pixel ratio).
// The page is mostly tables, whose cells and rows the layout puts in translated groups.
// Each frame and each band must hold only the glyphs near the view
// (WebDocument.nearNodes), not every glyph of the page: before, both passed the storage
// budget (NativeSVG.maxDataFloats) at zoom 300 and 450.
const page="showcase-scripts.html";
async function scriptsAtPhoneZoom(nativeEngine?:string){
  // @ts-ignore plain JavaScript module of the Hub
  const {fontsFor}=await import("../../../docs/web/hub/foafnaut/font-coverage.mjs");
  const engine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  const source=await Deno.readTextFile(new URL("pages/"+page,import.meta.url));
  const wanted=await fontsFor(source,async(path:string)=>JSON.parse(await Deno.readTextFile(fonts+path.replace("./fonts/",""))));
  assert.equal(wanted.length,13);
  for(const font of wanted)await loadFontFile(engine,fonts+font.path.replace("./fonts/",""),font.family,"bytes",true);
  const width=390*3,height=844*3;
  const shell={tabs:[{title:""}],active:0,address:"",cursor:0,anchor:0,focused:false,canBack:false,canForward:false,
    loading:false,scale:3,theme:"next",pages:1,scroll:0,collapsible:true,collapse:0};
  const options={url:"file:///"+page,textScalePercent:450,checks:false};
  const first=engine.compile(source,width,height,{...options,shell});
  const bottom=Math.max(...first.webRender.boxes.map(b=>b[2]+b[4]));
  assert(bottom>4*height,`the page at zoom 450 is ${bottom} rows, expected a tall page`);
  // Every frame and band down the page draws; none holds more than a band's share.
  let most=first.data.length;
  for(let scroll=0;scroll<bottom;scroll+=height){
    const frame=engine.compile(source,width,height,{...options,shell:{...shell,scroll}});
    const band=engine.compileLayers(source,width,height,{...options,shell:{...shell,scroll}});
    assert(frame.primitiveCount>0&&band.page.primitiveCount>0,`nothing drawn at scroll ${scroll}`);
    most=Math.max(most,frame.data.length,band.page.data.length);
  }
  assert(most<=1048576,`a frame or band of ${most} floats`);
}
Deno.test("the writing-systems page draws at text zoom 450 on a 390 px phone (Wasm)",()=>scriptsAtPhoneZoom());
Deno.test({name:"the writing-systems page draws at text zoom 450 on a 390 px phone (native library)",ignore:noLibrary,fn:()=>scriptsAtPhoneZoom(library)});
