// The serif face given before the first page (serif_font.ts, run_html.ts): a serif page is
// laid out once with its final face, and a page with no serif text lays out as with no face
// held. Run on the Wasm engine and, when it is built, the native library. Run with
// --allow-read --allow-ffi.
//
// What the Lean theorems say (WebDocument.serifWanted_held, renderWithStyles_made,
// familyFontsWith_noSerif) is checked here on whole frames: the theorems are about the
// parts, this is about the engine as a host calls it.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {SERIF_FAMILY,serifFontPath,wantsSerif} from "./serif_font.ts";

const sans=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();

// No author font-family: the initial value, serif.
const unstyled="<!doctype html><h1>Serif by default</h1><p>An unstyled page draws its text with a serif face, as browsers do.</p>";
// Every text node sans-serif; the root keeps the initial family.
const sansPage="<!doctype html><style>body{font-family:sans-serif}</style><h1>Sans</h1><p>A page that names sans-serif for all of its text.</p>";
// Monospace and sans text only (pre is monospace in the UA sheet).
const monoPage="<!doctype html><style>p{font-family:Arial}</style><pre>code</pre><p>Arial is an installed sans family.</p>";

type Frame={data:Float32Array;primitives:number;wantsSerif:boolean};
let width=600;
const frame=(engine:HTMLEngine,html:string,w=width):Frame=>{
  const scene:HTMLArtifact=engine.compile(html,w,160,{checks:false,url:"file:///serif.html"});
  return {data:Float32Array.from(scene.data as Float32Array),primitives:scene.primitiveCount,wantsSerif:wantsSerif(scene)};
};
const same=(a:Frame,b:Frame)=>a.primitives===b.primitives&&a.data.length===b.data.length&&a.data.every((v,i)=>Object.is(v,b.data[i]));

async function check(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  // A new width for each layout below, so that no kept layout is given again.
  // No serif face held: the unstyled page asks for it, the sans pages do not.
  const plainUnstyled=frame(engine,unstyled,width++),plainSans=frame(engine,sansPage,width++),plainMono=frame(engine,monoPage,width++);
  assert.equal(plainUnstyled.wantsSerif,true,"an unstyled page asks for the serif face");
  assert.equal(plainSans.wantsSerif,false,"a sans page does not ask for the serif face");
  assert.equal(plainMono.wantsSerif,false,"a monospace and Arial page does not ask for the serif face");

  // The face given (as run_html.ts gives it before the first page).
  const answer=await loadFontFile(engine,serifFontPath(),SERIF_FAMILY,"bytes","serif") as {serif?:string};
  assert.equal(answer.serif,SERIF_FAMILY);
  // Pages with no serif text: the same frames as with no face held, bit for bit.
  width-=3;
  const heldUnstyled=frame(engine,unstyled,width++),heldSans=frame(engine,sansPage,width++),heldMono=frame(engine,monoPage,width++);
  assert.ok(same(heldSans,plainSans),"a sans page draws the same frame with the serif face held");
  assert.ok(same(heldMono,plainMono),"a monospace and Arial page draws the same frame with the serif face held");
  // The serif page: no second ask, and its text in the serif face (a different frame).
  assert.equal(heldUnstyled.wantsSerif,false,"with the face held, a serif page does not ask again: its first layout is final");
  assert.ok(!same(heldUnstyled,plainUnstyled),"the serif page is drawn in the serif face");

  // The first layout with the face given first is the layout a host got before on its second
  // render (the face given after a wantsSerif answer): a fresh engine, face first.
  const first=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(first,sans,"Noto Sans");
  await loadFontFile(first,serifFontPath(),SERIF_FAMILY,"bytes","serif");
  const once=frame(first,unstyled,width-3);
  assert.equal(once.wantsSerif,false);
  assert.ok(same(once,heldUnstyled),"the face given first: the first layout is the final one");
}

Deno.test("serif face given first: one layout for serif pages, no change for others (Wasm)",async()=>{await check();});
Deno.test({name:"serif face given first: one layout for serif pages, no change for others (native)",ignore:noLibrary,fn:async()=>{await check(library);}});
