// The monospace face (serif_font.ts): text whose family resolves to `monospace`
// (FontFaceRule.genericOf; the UA sheet gives it to pre, code, kbd, samp, tt) draws with
// Liberation Mono once a host gives it (fontLoad mode 4, WebDocument.loadMonoFont); a page with
// no monospace text lays out as with no face held; and a render whose text wants the face while
// the engine holds none answers wantsMono. Run on the Wasm engine and, when it is built, the
// native library, which also draws CPU pixels so that the advances can be measured.
// Run with --allow-read --allow-ffi.
//
// What the Lean theorems say (WebDocument.familyFontsWith_mono, familyFontsWith_noSerif,
// familyFontsWith_monoOnly, serifWanted_held) is checked here on whole frames.
import {strict as assert} from "node:assert";
import {loadHTML,nativeBackends,unpackAnswer,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {MONO_FAMILY,SERIF_FAMILY,monoFontPath,serifFontPath,wantsMono,wantsSerif} from "./serif_font.ts";

const sans=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const libraries=["libweb-render.dylib","libweb-render.so"].map(n=>new URL(`./.build/web-render/engines/${n}`,import.meta.url).pathname);
const library=libraries.find(p=>{try{Deno.statSync(p);return true;}catch{return false;}});

// pre is monospace in the UA sheet; code too.
const monoPage="<!doctype html><style>body{font-family:sans-serif}</style><p>Some <code>code()</code> in a line.</p><pre>for (let i = 0; i &lt; n; i++) {}\n  WWWW iiii</pre>";
// Only sans-serif text: no monospace, no serif.
const sansPage="<!doctype html><style>body{font-family:sans-serif}</style><h1>Sans</h1><p>A page that names sans-serif for all of its text.</p>";
// Serif text only (the initial family), no monospace.
const serifPage="<!doctype html><h1>Serif by default</h1><p>An unstyled page draws its text with a serif face.</p>";
// Installed monospace families resolve to the face too.
const courierPage="<!doctype html><p style='font-family:\"Courier New\", Courier, monospace'>Courier New text</p>";

type Frame={data:Float32Array;primitives:number;wantsMono:boolean;wantsSerif:boolean};
let width=600;
const frame=(engine:HTMLEngine,html:string,w=width):Frame=>{
  const scene:HTMLArtifact=engine.compile(html,w,200,{checks:false,url:"file:///mono.html"});
  return {data:Float32Array.from(scene.data as Float32Array),primitives:scene.primitiveCount,wantsMono:wantsMono(scene),wantsSerif:wantsSerif(scene)};
};
const same=(a:Frame,b:Frame)=>a.primitives===b.primitives&&a.data.length===b.data.length&&a.data.every((v,i)=>Object.is(v,b.data[i]));

async function check(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  await loadFontFile(engine,serifFontPath(),SERIF_FAMILY,"bytes","serif");
  // No monospace face held: a page of code asks for it, the others do not.
  const plainMono=frame(engine,monoPage,width++),plainSans=frame(engine,sansPage,width++),plainSerif=frame(engine,serifPage,width++),plainCourier=frame(engine,courierPage,width++);
  assert.equal(plainMono.wantsMono,true,"a page with pre and code asks for the monospace face");
  assert.equal(plainCourier.wantsMono,true,"Courier New resolves to the monospace face");
  assert.equal(plainSans.wantsMono,false,"a sans page does not ask for the monospace face");
  assert.equal(plainSerif.wantsMono,false,"a serif page does not ask for the monospace face");
  assert.equal(plainSerif.wantsSerif,false,"the serif face is held: a serif page does not ask for it");

  const answer=await loadFontFile(engine,monoFontPath(),MONO_FAMILY,"bytes","mono") as {mono?:string;glyphs?:number};
  assert.equal(answer.mono,MONO_FAMILY);
  assert.ok((answer.glyphs??0)>600,"Liberation Mono has its glyphs");
  // Pages with no monospace text: the same frames as with no face held, bit for bit.
  width-=4;
  const heldMono=frame(engine,monoPage,width++),heldSans=frame(engine,sansPage,width++),heldSerif=frame(engine,serifPage,width++),heldCourier=frame(engine,courierPage,width++);
  assert.ok(same(heldSans,plainSans),"a sans page draws the same frame with the monospace face held");
  assert.ok(same(heldSerif,plainSerif),"a serif page draws the same frame with the monospace face held");
  // The page of code: no second ask, and its code in the monospace face.
  assert.equal(heldMono.wantsMono,false,"with the face held, a page of code does not ask again");
  assert.ok(!same(heldMono,plainMono),"the page of code is drawn in the monospace face");
  assert.ok(!same(heldCourier,plainCourier),"Courier New text is drawn in the monospace face");
}

/** The widths of the blue and the red span backgrounds on a CPU picture of `html`. */
function spanWidths(lib:string,html:string):{blue:number;red:number} {
  const w=800,h=200;
  const buffer=nativeBackends(lib).bytes(html,JSON.stringify({op:"render",checks:false,cpu:true,url:"file:///mono.html"}),w,h);
  const {head,sections}=unpackAnswer(buffer);
  const scene=(head.page??head) as Record<string,unknown>;
  const [offset,length]=sections[scene.pixelsSection as number];
  const rgba=new Uint8Array(buffer,offset,length);
  const run=(match:(r:number,g:number,b:number)=>boolean)=>{
    let best=0;
    for(let y=0;y<h;y++){let n=0;for(let x=0;x<w;x++){const p=(y*w+x)*4;if(match(rgba[p],rgba[p+1],rgba[p+2]))n++;}best=Math.max(best,n);}
    return best;
  };
  return {blue:run((r,g,b)=>r<40&&g<40&&b>200),red:run((r,g,b)=>r>200&&g<40&&b<40)};
}

const widthPage="<!doctype html><body style='margin:0'><div><span style='font:20px/30px monospace;background:#0000ff;color:#0000ff'>iiiiiiiiii</span></div>"+
  "<div><span style='font:20px/30px monospace;background:#ff0000;color:#ff0000'>WWWWWWWWWW</span></div></body>";

// The native library is one process with one set of held fonts, so this check gives the face
// and measures; the frames of check() show that the face changes the drawing.
async function advances(lib:string){
  const engine=await loadHTML(lib,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  await loadFontFile(engine,monoFontPath(),MONO_FAMILY,"bytes","mono");
  const after=spanWidths(lib,widthPage);
  // Liberation Mono: 1,229 units of 2,048 to the em, 0.6 em; ten letters at 20 px are 120 px.
  assert.ok(Math.abs(after.blue-120)<=1,`ten i at 20px are 120 px wide, got ${after.blue}`);
  assert.ok(Math.abs(after.red-120)<=1,`ten W at 20px are 120 px wide, got ${after.red}`);
}

/** The height of the blue background on a CPU picture of `html` (its tallest column). */
function blueHeight(lib:string,html:string):number {
  const w=400,h=120;
  const buffer=nativeBackends(lib).bytes(html,JSON.stringify({op:"render",checks:false,cpu:true,url:"file:///mono.html"}),w,h);
  const {head,sections}=unpackAnswer(buffer);
  const scene=(head.page??head) as Record<string,unknown>;
  const [offset,length]=sections[scene.pixelsSection as number];
  const rgba=new Uint8Array(buffer,offset,length);
  let best=0;
  for(let x=0;x<w;x++){let n=0;for(let y=0;y<h;y++){const p=(y*w+x)*4;if(rgba[p]<40&&rgba[p+1]<40&&rgba[p+2]>200)n++;}best=Math.max(best,n);}
  return best;
}

// CSS 2.1 §10.6.1: the background of inline text covers the content area of its own font.
// Liberation Mono's hhea ascent and descent are 1,705 and 615 of 2,048 units (1.1328 em, 22.66 px
// at 20 px); before 2026-11-22 every line used Noto Sans's (1.362 em, 27.24 px:
// Layout.FontProfile.metricsOf).
async function contentArea(lib:string){
  const engine=await loadHTML(lib,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  await loadFontFile(engine,monoFontPath(),MONO_FAMILY,"bytes","mono");
  const height=blueHeight(lib,"<!doctype html><body style='margin:0'><p style='margin:20px 0'><span style='font:20px/60px monospace;background:#0000ff;color:#0000ff'>iii</span></p></body>");
  assert.ok(height>=22&&height<=23,`the content area of 20px Liberation Mono is 22.66 px, got ${height}`);
}

// Expected failure, https://github.com/danbri/factoidal-core/issues/750 (generic monospace at 13 px): browsers draw text whose family is the generic `monospace` alone,
// and whose size comes from a keyword (the initial `medium`), at 13 px, not 16 px (Blink, Gecko
// and WebKit; `pre`, `code`, `kbd`, `samp` in an unstyled page). This engine draws it at 16 px.
// When this test fails because the ten letters are 78 px wide (13 px x 0.6 em), assert that and
// close the issue in the same landing.
const stillGap=`expected failure of https://github.com/danbri/factoidal-core/issues/750 no longer fails: pre text is not 16 px; make this test assert 13 px (78 px for ten letters) and close the issue`;
async function monoSize(lib:string){
  const engine=await loadHTML(lib,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  await loadFontFile(engine,monoFontPath(),MONO_FAMILY,"bytes","mono");
  const page="<!doctype html><body style='margin:0'><pre style='margin:0'><span style='background:#0000ff;color:#0000ff'>iiiiiiiiii</span></pre></body>";
  const {blue}=spanWidths(lib,page);
  assert.ok(Math.abs(blue-96)<=1,stillGap+` (width ${blue})`);
}

Deno.test("monospace face: pre and code draw with Liberation Mono, other pages unchanged (Wasm)",async()=>{await check();});
Deno.test({name:"monospace face: pre and code draw with Liberation Mono, other pages unchanged (native)",ignore:!library,fn:async()=>{await check(library);}});
Deno.test({name:"monospace face: every letter is 0.6 em wide (native CPU pixels)",ignore:!library,fn:async()=>{await advances(library!);}});
Deno.test({name:"monospace face: an inline background is the content area of Liberation Mono (native CPU pixels)",ignore:!library,fn:async()=>{await contentArea(library!);}});
Deno.test({name:"expected failure, https://github.com/danbri/factoidal-core/issues/750: pre text at 16 px where browsers use 13 px (native CPU pixels)",ignore:!library,fn:async()=>{await monoSize(library!);}});
