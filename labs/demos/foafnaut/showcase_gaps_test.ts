// Expected failures of the showcase pages (owner request of 2026-11-07, issue 1268).
// Each test states a gap as it is today, through the Wasm engine with the window's font
// (Noto Sans). When an engine change closes a gap, its test fails: change the assertion
// to the correct behaviour and close the issue in the same landing.
// Run with --allow-read; needs .build/native-html/runtime/web-render.{mjs,wasm}.
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML} from "./native_html_document.ts";

const ISSUE="https://github.com/danbri/factoidal/issues/";
const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const pages=new URL("./pages/",import.meta.url).pathname;
const engine=await loadHTML();
await loadFontFile(engine,font,"Noto Sans");

type Run={text:string;glyphs:number[][]};
const html=(body:string)=>`<!doctype html><html lang="en"><head><meta charset="utf-8"><title>gap</title></head><body>${body}</body></html>`;
const options={url:"https://example.test/",resources:[]};
const frame=(body:string)=>engine.compile(html(body),800,400,options) as unknown as {primitiveCount:number;webRender:{glyphRuns:Run[]}};
const runs=(body:string)=>frame(body).webRender.glyphRuns;
const run=(body:string,text:string)=>{const r=runs(body).find(r=>r.text===text);assert(r,`no glyph run for ${text}`);return r;};
// A glyph row is [glyph id, x, y, ...]; glyph id 0 is .notdef.
const ids=(r:Run)=>r.glyphs.map(g=>g[0]);
const left=(r:Run)=>r.glyphs[0][1];
const stillGap=(issue:string)=>`expected failure of ${ISSUE}${issue} no longer fails: make this test assert the correct result and close the issue`;

// Issue 1270 is closed: SVG text, tspan and textPath are drawn (svg_text_test.ts).
const svgFrame=(svg:string)=>frame(`<svg width="400" height="200" viewBox="0 0 400 200">${svg}</svg>`);
Deno.test("issue 1270: the showcase textPath and lettering pages render, with SVG text",async()=>{
  for(const name of ["showcase-textpath.html","showcase-lettering.html","showcase-dataviz.html","showcase-tables-svg.html"]){
    const doc=await prepareHTML(engine,inputURL(pages+name,true));
    const f=await doc.compile(900,700) as unknown as {primitiveCount:number};
    assert.ok(f.primitiveCount>0,name);
  }
});
Deno.test("issue 1270: SVG text draws glyphs; anchors, tspan and textPath add paint",()=>{
  const empty=svgFrame("").primitiveCount;
  const one=svgFrame("<text x='10' y='50' font-size='20'>Hello</text>").primitiveCount;
  assert.ok(one>empty,"a text adds paint");
  assert.equal(svgFrame("<text x='200' y='50' font-size='20' text-anchor='middle'>Hello</text>").primitiveCount,one,"an anchor moves the same glyphs");
  assert.ok(svgFrame("<text x='10' y='50' font-size='20'>Hel<tspan fill='red'>lo</tspan></text>").primitiveCount>one,"a tspan of another colour is its own paint");
  assert.ok(svgFrame("<defs><path id='p' d='M10 100 C 100 0 300 0 390 100'/></defs><text font-size='20'><textPath href='#p'>Hello</textPath></text>").primitiveCount>empty,"textPath draws");
});
Deno.test("expected failure, issue 1285: vertical writing-mode is laid out horizontally",()=>{
  // The same frame with and without writing-mode: vertical text would place the glyphs differently.
  const text=(mode:string)=>engine.compile(`<!doctype html><html><body><svg width="200" height="200"><text x="100" y="20" font-size="20"${mode}>ABC</text></svg></body></html>`,400,300,options) as unknown as {data:ArrayLike<number>};
  const a=Array.from(text("").data),b=Array.from(text(" writing-mode='vertical-rl'").data);
  assert.deepEqual(a,b,stillGap("1285"));
});
Deno.test("expected failure, issue 1286: SVG text gives no glyph runs, so it can not be selected",()=>{
  assert.equal(runs("<svg width='200' height='100'><text x='10' y='50'>Selectable</text></svg>").filter(r=>r.text==="Selectable").length,0,stillGap("1286"));
});

Deno.test("expected failure, issue 1271: the window refuses the showcase script page",async()=>{
  await assert.rejects(()=>prepareHTML(engine,inputURL(pages+"showcase-dataviz-script.html",true)),
    /does not execute scripts/,stillGap("1271"));
});

Deno.test("issue 1272: table cells are side by side, and colspan widens a cell",()=>{
  const body="<table><tr><td>alpha</td><td>beta</td></tr></table>";
  assert.ok(left(run(body,"beta"))>left(run(body,"alpha")),"cells of one row are in one line");
  assert.equal(run(body,"beta").glyphs[0][2],run(body,"alpha").glyphs[0][2],"cells of one row share a top");
  const span="<table><tr><td>one</td><td>two</td></tr><tr><td colspan=2>wide</td></tr></table>";
  assert.equal(left(run(span,"wide")),left(run(span,"one")),"a spanning cell starts in its first column");
  assert.ok(run(span,"wide").glyphs[0][2]>run(span,"two").glyphs[0][2],"the second row is below the first");
});

Deno.test("expected failure, issue 1272: a baseline cell is placed as a top cell",()=>{
  // CSS 2.1 §17.5.3: baseline cells of a row share a baseline, so the small text moves down.
  const body="<table><tr><td style='vertical-align:baseline;font-size:40px'>big</td><td style='vertical-align:baseline'>small</td></tr></table>";
  // Shared baseline: the 16px text's top is about 20px below the 40px text's top. Placed at the top: within a few pixels.
  assert.ok(run(body,"small").glyphs[0][2]-run(body,"big").glyphs[0][2]<10,stillGap("1272"));
});

Deno.test("expected failure, issue 1272: inline-table is laid out as a block-level table",()=>{
  const body="<p>before <span style='display:inline-table'><span style='display:table-cell'>cell</span></span> after</p>";
  assert.ok(run(body,"after").glyphs[0][2]>run(body,"before").glyphs[0][2],stillGap("1272"));
});

// Closed by branch wip/1268-press-feedback: an inline-block is one atomic box (its width
// holds), and borders are drawn. The rest of issue 1272 (table layout, above) and of
// issue 1273 (text-align and the other properties) stays an expected failure.
Deno.test("an inline-block keeps its width (CSS 2.2 10.3.9)",()=>{
  const body="<p><span style='display:inline-block;width:200px'>one</span><span>two</span></p>";
  assert.ok(left(run(body,"two"))>=200);
});

Deno.test("a border is drawn (CSS Backgrounds 3)",()=>{
  const plain=frame("<div>boxed</div>").primitiveCount;
  assert.equal(frame("<div style='border:4px solid #c00'>boxed</div>").primitiveCount,plain+4);
});

Deno.test("expected failure, issue 1273: text-align is dropped",()=>{
  assert.ok(left(run("<p style='text-align:right'>right</p>","right"))<100,stillGap("1273"));
});

Deno.test("expected failure, issue 1274: Hebrew, Arabic, Devanagari, Thai and CJK draw as .notdef",()=>{
  for(const text of ["שלום","مرحبا","नमस्ते","สวัสดี","你好","안녕"])
    assert.ok(ids(run(`<p>${text}</p>`,text)).every(id=>id===0),stillGap("1274")+` (${text})`);
  // Latin, Greek and Cyrillic are in the font.
  for(const text of ["Ångström","Καλημέρα","Привет"])
    assert.ok(ids(run(`<p>${text}</p>`,text)).every(id=>id!==0),text);
});

Deno.test("expected failure, issue 1275: dir=rtl is ignored",()=>{
  // Latin, so the font has the glyphs: a right-to-left paragraph should start at the right edge.
  const body="<p dir='rtl'>first second</p>";
  assert.ok(left(run(body,"first"))<left(run(body,"second")),stillGap("1275"));
  assert.ok(left(run(body,"first"))<100,stillGap("1275"));
});

Deno.test("expected failure, issue 1276: emoji draw as .notdef",()=>{
  for(const text of ["😀","🌍"])
    assert.deepEqual(ids(run(`<p>${text}</p>`,text)),[0],stillGap("1276")+` (${text})`);
});

// Owner report (issues 1268, 1270): the data visualisation and lettering pages did not
// scroll to the end. Lean's scroll limit with the layers: at the limit, the view ends at
// the last row of the layout, and the band made there holds that view.
Deno.test("the scroll limit reaches the last row of long SVG pages",async()=>{
  const W=1600,H=1000,scale=2;
  for(const name of ["showcase-dataviz.html","showcase-lettering.html","solving-showcase.html","showcase.html"]){
    const doc=await prepareHTML(engine,inputURL(pages+name,true));
    const shell=(scroll:number)=>({tabs:[{title:doc.title??""}],active:0,address:doc.url,cursor:0,focused:false,canBack:false,canForward:false,
      loading:false,scale,theme:"next",pages:1,scroll});
    const at=(scroll:number)=>engine.compileLayers(doc.source,W,H,{...doc.request(W,H).options,textScalePercent:150,shell:shell(scroll),checks:false});
    const first=at(0),place=first.layers;
    const bottom=Math.max(...(first.page.webRender.boxes as number[][]).map(b=>b[2]+b[4]));
    assert.equal(typeof place.scrollLimit,"number",name);
    assert.equal(place.scrollLimit!+place.view,Math.max(Math.ceil(bottom),place.view),`${name}: the view at the limit ends at the last row`);
    const end=at(place.scrollLimit!).layers;
    assert.ok(end.bandTop<=place.scrollLimit! && place.scrollLimit!+place.view<=end.bandTop+end.bandHeight,`${name}: the band at the limit holds the view`);
  }
});

// Images, icons and keys (issue 1268, owner requests of 2026-11-07).
Deno.test("issue 1268: an img draws its PNG, JPEG or GIF",async()=>{
  const doc=await prepareHTML(engine,inputURL(pages+"showcase-image-formats.html",true));
  const frame=doc.compile(900,1400) as unknown as {error?:string;webRender:{glyphRuns:Run[]}};
  assert.equal(frame.error,undefined);
  // No image stands as its description: each one decoded and has a box.
  assert.ok(!frame.webRender.glyphRuns.some(r=>r.text.startsWith("[")),"an image fell back to its alt text");
  assert.ok(doc.iconBase64,"the page's SVG icon was fetched");
  assert.equal(engine.iconPrepare(doc.iconBase64!,2).kind,"svg");
});

Deno.test("issue 1268: Lean's key table answers the cross-browser keys",()=>{
  assert.equal(engine.keyCommand("mac","command","r"),8);
  assert.equal(engine.keyCommand("other","","F5"),8);
  assert.equal(engine.keyCommand("mac","shift+command","t"),20);
  assert.equal(engine.pageKey(49,0),33);
  assert.equal(engine.command(29,100,undefined,false,{tabs:5,active:0}).tab,4);
  assert.equal(engine.command(36,100,undefined,false,{scroll:0,view:500,scrollLimit:1200,scale:1}).scrollTo,1200);
});

Deno.test("expected failure, issue 1280: find in page is refused",()=>{
  assert.match(engine.command(32,100).refused??"",/issues\/1280/,stillGap("1280"));
});

Deno.test("expected failure, issue 1282: an ICO icon link gives no icon",()=>{
  const facts=engine.inspect("<link rel=icon href='/favicon.ico'><p>x</p>",{url:"https://example.test/"});
  assert.equal(facts.icon,null,stillGap("1282"));
});

Deno.test("expected failure, issue 1283: WebP and AVIF are refused",()=>{
  // A 1 by 1 lossless WebP, and a 64 by 64 AVIF from SVT-AV1 through FFmpeg.
  const webp="UklGRhoAAABXRUJQVlA4TA0AAAAvAAAAEAcQERGIiP4HAA==";
  const avif="AAAAIGZ0eXBhdmlmAAAAAGF2aWZtaWYxbWlhZk1BMUIAAAD5bWV0YQAAAAAAAAAvaGRscgAAAAAAAAAAcGljdAAAAAAAAAAAAAAAAFBpY3R1cmVIYW5kbGVyAAAAAA5waXRtAAAAAAABAAAAHmlsb2MAAAAARAAAAQABAAAAAQAAASEAAAAlAAAAKGlpbmYAAAAAAAEAAAAaaW5mZQIAAAAAAQAAYXYwMUNvbG9yAAAAAGppcHJwAAAAS2lwY28AAAAUaXNwZQAAAAAAAABAAAAAQAAAABBwaXhpAAAAAAMICAgAAAAMYXYxQ4EADAAAAAATY29scm5jbHgAAgACAAIAAAAAF2lwbWEAAAAAAAAAAQABBAECgwQAAAAtbWRhdAoLAgAABVV//Gr5gEAyFhAAugIIIEEBAAAIAJXR4n6sTwStpHA=";
  for(const bytes of [webp,avif])
    assert.throws(()=>engine.iconPrepare(bytes,1),/not PNG, JPEG or GIF/,stillGap("1283"));
});

Deno.test("expected failure, issue 1284: an animated GIF shows its first frame only",()=>{
  // Two frames of 500 ms (ImageGIFTests.lean decodes both); a frame of the page names no next frame time.
  const anim="R0lGODlhBAACAPcfAAAAAAAA/wD/AAD///8AAP8A////AP///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////yH/C05FVFNDQVBFMi4wAwEAAAAh+QQEMgAfACwAAAAABAACAAAIDAAJCAhwAICBAQUCAgAh+QQFMgABACwAAAAAAgACAAAIBwABBAhwICAAOw==";
  const frame=engine.compile("<p><img src='a.gif'></p>",200,60,{url:"https://example.test/",resources:[],
    images:[{key:"https://example.test/a.gif",base64:anim}]}) as unknown as Record<string,unknown>;
  assert.equal(frame.error,undefined);
  assert.equal(frame.nextFrameMs,undefined,stillGap("1284"));
});
