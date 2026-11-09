// Engine features of the web font and animation work (2026-11-09), on the Wasm engine and,
// when it is built, the native library:
//
// * @font-face (CSS Fonts 4 §4): Lean says which faces the rendered text uses; the host
//   fetches only those; a file that is not a font is refused and its text falls back.
//   HTML and SVG text draw with the face.
// * A combining mark from one font on a base from another (SfntProfile.wordWith): the
//   mark is centred on its base's advance box (SfntMarkTheorems.positionMark_centre).
// * Paint-only transforms (WebPaint, FrameCost.paint_never_layouts): a script's
//   `transform` of an SVG group and an SVG animateTransform lay the page out once; each
//   frame is the frame of the page with that transform written in it.
// * Hostile text: 10,000 combining marks on one base cost time in proportion to their
//   number (Stream-Safe Text Format, InkBound), and their ink stays within 31 em.
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type HTMLArtifact} from "./native_html_engine.ts";
import {prepareHTML,loadFontFile} from "./native_html_document.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const pageURL=new URL("./pages/webfont-test.html",import.meta.url).href;
const sans=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const frakturURL="../fonts/fruktur/Fruktur-Regular.ttf";

type Run={source:number;font:string;size:number;text:string;glyphs:number[][]};
const runs=(a:HTMLArtifact)=>(a.webRender as unknown as {glyphRuns:Run[]}).glyphRuns;
const glyphIds=(a:HTMLArtifact,text:string)=>runs(a).filter(r=>r.text===text).flatMap(r=>r.glyphs.map(g=>g[0]));

async function engineWithFont(path?:string){const e=await loadHTML(path);await loadFontFile(e,sans,"Noto Sans");return e;}

const webFontPage=`<!doctype html><html><head><style>
@font-face{font-family:"Spinal";src:url(${frakturURL}) format("truetype")}
@font-face{font-family:Broken;src:url(../fonts/fruktur/OFL.txt) format("truetype")}
@font-face{font-family:Unused;src:url(../fonts/does-not-exist.ttf)}
h1{font-family:Spinal,serif;font-size:40px;margin:0}
p.b{font-family:Broken,sans-serif}
</style></head><body><h1>Spinal Tap</h1><p class="b">Broken</p>
<svg width="300" height="80"><text x="10" y="50" font-family="Spinal" font-size="40">Tap</text></svg></body></html>`;

async function webFonts(engine:HTMLEngine){
  const faces=engine.fontFaces(webFontPage,{url:pageURL});
  // Lazy (§4.8): the used faces only; the unused face is never fetched.
  assert.deepEqual(faces.faces.map(f=>f.family).sort(),["Broken","Spinal"]);
  assert.equal(faces.rules,3);
  const doc=await prepareHTML(engine,pageURL,undefined,webFontPage);
  const options=doc.request(600,300).options as {webFonts?:{url:string;sha256:string}[]};
  // The broken face is refused by the font policy: only the font is held.
  assert.equal(options.webFonts?.length,1,JSON.stringify(options.webFonts));
  assert(options.webFonts![0].url.endsWith("Fruktur-Regular.ttf"));
  const withFont=engine.compile(doc.source,600,300,options);
  const without=engine.compile(doc.source,600,300,{...options,webFonts:undefined});
  // HTML text: other glyphs (the face's), SVG text too; the broken face's text is as before.
  assert.notDeepEqual(glyphIds(withFont,"Spinal"),glyphIds(without,"Spinal"),"the h1 draws with the web font");
  assert.deepEqual(glyphIds(withFont,"Broken"),glyphIds(without,"Broken"),"refused: the text falls back");
  assert.notDeepEqual(Array.from(withFont.data),Array.from(without.data),"the SVG and HTML text differ");
  return {webFonts:options.webFonts!.length,faces:faces.faces.length};
}

// A base in a web font (U+25CA, which Noto Sans lacks) and U+0308 from Noto Sans: the
// face's unicode-range leaves the mark out, so no font has both.
const markPage=`<!doctype html><style>@font-face{font-family:Pua;src:url(${frakturURL});unicode-range:U+25CA}
p{font-family:Pua;font-size:48px;margin:0}</style><p>&#x25CA;&#x308;</p>`;
async function crossFontMark(engine:HTMLEngine){
  const doc=await prepareHTML(engine,pageURL,undefined,markPage);
  const a=engine.compile(doc.source,400,200,doc.request(400,200).options);
  const run=runs(a).find(r=>r.text.startsWith(""))!;
  assert(run&&run.glyphs.length===2,JSON.stringify(runs(a)));
  const [base,mark]=run.glyphs;
  assert.equal(mark[3],0,"the mark takes no advance");
  // The mark's origin is placed so that its ink is centred on the base's advance box:
  // its origin lies within the base's box widened by one em.
  assert(mark[1]>=base[1]-48&&mark[1]<=base[1]+base[3]+48,`base ${base} mark ${mark}`);
  return {base,mark};
}

// Paint-only transforms.
const svgPage=(t:string,extra="")=>`<!doctype html><style>body{margin:0}</style><svg width="400" height="200" viewBox="0 0 400 200">
<g id="zoom" transform="${t}"><text x="20" y="100" font-size="40">Spinal Tap</text></g>${extra}</svg>`;
function nodeIdOf(engine:HTMLEngine,html:string,id:string){
  const nodes=(engine.inspect(html,{url:pageURL}) as unknown as {nodes:{id:number;attributes:Record<string,string>}[]}).nodes;
  return nodes.find(n=>n.attributes.id===id)!.id;
}
function transformCounts(engine:HTMLEngine){
  const html=svgPage("scale(1)");
  const node=nodeIdOf(engine,html,"zoom");
  const shell={tabs:[{title:"t"}],active:0,address:pageURL,focused:false,canBack:false,canForward:false,loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};
  const at=(k:number)=>({url:pageURL,shell,checks:false,commands:[{op:"setAttribute",nodeId:node,name:"transform",value:`translate(200 100) scale(${k}) translate(-200 -100)`}]});
  engine.compileLayers(html,400,260,at(1));
  engine.frameWork(true);
  const times:number[]=[];let last;
  for(let k=1;k<=40;k++){const t=performance.now();last=engine.compileLayers(html,400,260,at(k));times.push(performance.now()-t);}
  const work=engine.frameWork(true)!;
  assert.equal(work.layouts,0,`a transform frame laid out: ${JSON.stringify(work)}`);
  assert((work as {paintOnly?:number}).paintOnly!>=39,`paint-only frames: ${JSON.stringify(work)}`);
  // The frame is the page with that transform in its source.
  const written=engine.compileLayers(svgPage("translate(200 100) scale(40) translate(-200 -100)"),400,260,{url:pageURL,shell,checks:false});
  assert.deepEqual(Array.from(last!.page.data),Array.from(written.page.data),"the painted frame is the laid-out one");
  return {work,frameMs:stats(times)};
}

const animated=svgPage("",`<animateTransform href="#zoom" attributeName="transform" type="scale" values="1;40;1" dur="2s" repeatCount="indefinite"/>`);
function animationCounts(engine:HTMLEngine){
  const shell={tabs:[{title:"t"}],active:0,address:pageURL,focused:false,canBack:false,canForward:false,loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};
  const at=(ms:number)=>({url:pageURL,shell,checks:false,animationTime:ms});
  const first=engine.compileLayers(animated,400,260,at(0));
  assert.equal(first.layers.animating,true);assert.equal(first.layers.animations,true);
  engine.frameWork(true);
  const times:number[]=[];let mid;
  for(let ms=16;ms<=2000;ms+=16){const t=performance.now();const f=engine.compileLayers(animated,400,260,at(ms));times.push(performance.now()-t);if(ms===1008)mid=f;}
  const work=engine.frameWork(true)!;
  assert.equal(work.layouts,0,`an animation frame laid out: ${JSON.stringify(work)}`);
  const peak=engine.compileLayers(animated,400,260,at(1000));
  const written=engine.compileLayers(svgPage("scale(40)"),400,260,{url:pageURL,shell,checks:false});
  assert.deepEqual(Array.from(peak.page.data),Array.from(written.page.data),"at 1 s the scale is 40");
  assert(mid);
  return {work,frameMs:stats(times)};
}

function stats(xs:number[]){const s=[...xs].sort((a,b)=>a-b);const q=(p:number)=>Math.round(s[Math.min(s.length-1,Math.floor(p*s.length))]*100)/100;return {p50:q(0.5),p95:q(0.95),max:q(1),n:s.length};}

// Hostile text: 10,000 marks on one base.
function zalgo(engine:HTMLEngine){
  const page=(n:number)=>`<!doctype html><p style="font-size:20px">a${"́".repeat(n)} b</p>`;
  const time=(n:number)=>{const t=performance.now();const a=engine.compile(page(n),400,300,{url:pageURL});return {ms:performance.now()-t,a};};
  time(10);
  const small=time(100),big=time(10000);
  // Linear: 100 times the marks cost at most 300 times the time (the base cost included).
  assert(big.ms<Math.max(50,small.ms*300),`10,000 marks ${big.ms} ms, 100 marks ${small.ms} ms`);
  // The ink of each mark stays within 31 em of its line (InkBound.clusterBound).
  for(const run of runs(big.a))for(const g of run.glyphs)assert(Math.abs(g[2])<=31*20+40,`glyph at y ${g[2]}`);
  const fixture=Deno.readTextFileSync(new URL("./fixtures/showoff/zalgo.html",import.meta.url));
  engine.compile(fixture,800,1000,{url:pageURL});
  return {marks100Ms:Math.round(small.ms),marks10000Ms:Math.round(big.ms)};
}

for(const [name,path] of [["Wasm engine",undefined],["native library",library]] as const){
  const ignore=path!==undefined&&noLibrary;
  Deno.test({name:`web fonts: used faces only, refused face falls back, HTML and SVG text, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(await webFonts(await engineWithFont(path))));}});
  Deno.test({name:`combining mark of one font on a base of another, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(await crossFontMark(await engineWithFont(path))));}});
  Deno.test({name:`paint-only: a script's transform lays out once, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(transformCounts(await engineWithFont(path))));}});
  Deno.test({name:`paint-only: animateTransform lays out once, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(animationCounts(await engineWithFont(path))));}});
  Deno.test({name:`hostile text: 10,000 marks, ${name}`,ignore,fn:async()=>{console.log(JSON.stringify(zalgo(await engineWithFont(path))));}});
}
