// Fallback fonts: the engine holds a list of fonts, and Lean draws each character with
// the first font that has it (SfntProfile.runsOf, wordIn). Noto Sans has no Armenian;
// Noto Sans Armenian does. Run on the Wasm engine and, when it is built, the native
// library. Run with --allow-read --allow-ffi.
//
// The native library is one process with one list of held fonts, so each check uses one
// engine and changes its fonts in order, and keeps copies of the frames it compares.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {loadFontFile,prepareHTML,setFontHost,type PageEngine} from "./native_html_document.ts";
import {startCompileWorker} from "./native_html_compile.ts";
import {fallbackFontHost,fontFilePath,type FallbackFont,type PageFonts} from "./native_html_fonts.ts";

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
// device pixels to the CSS pixel opens it: text zoom 600 (the default text size, 200%, times
// the pixel ratio; it was 450), and at 1200 (the settings page's 400%).
// The page is mostly tables, whose cells and rows the layout puts in translated groups.
// Each frame and each band must hold only the glyphs near the view
// (WebDocument.nearNodes), not every glyph of the page: before, both passed the storage
// budget (NativeSVG.maxDataFloats) at zoom 300 and 450.
const page="showcase-scripts.html";
async function scriptsAtPhoneZoom(nativeEngine?:string,zoom=600){
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
  const options={url:"file:///"+page,textScalePercent:zoom,checks:false};
  const first=engine.compile(source,width,height,{...options,shell});
  const bottom=Math.max(...first.webRender.boxes.map(b=>b[2]+b[4]));
  assert(bottom>4*height,`the page at zoom ${zoom} is ${bottom} rows, expected a tall page`);
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
Deno.test("the writing-systems page draws at text zoom 600 on a 390 px phone (Wasm)",()=>scriptsAtPhoneZoom());
Deno.test("the writing-systems page draws at text zoom 1200 on a 390 px phone (Wasm)",()=>scriptsAtPhoneZoom(undefined,1200));
Deno.test({name:"the writing-systems page draws at text zoom 600 on a 390 px phone (native library)",ignore:noLibrary,fn:()=>scriptsAtPhoneZoom(library)});

// Emoji (issue 1276): the colour slices of Noto Color Emoji and Noto Emoji (outlines), after
// Noto Sans, as the Hub's table orders them and fetches them for these sequences. Each sequence
// is one glyph through the font's ligatures, with any U+FE0F hidden at no width: a ZWJ family, a
// ZWJ sequence with U+FE0F inside it (GSUB passes over the selector), a skin tone, a flag, a tag
// sequence, and keycaps whose digit Noto Sans also has (SfntProfile.runsOf keeps an emoji
// cluster in one font). An emoji with emoji presentation draws as an image of its colour glyph
// (ColrRaster): one rectangle whose pixels go in the scene's paint table; with U+FE0E it draws
// from Noto Emoji as an outline.
const emojiSequences=["\u{1F600}","❤️","♥️","\u{1F44D}\u{1F3FD}","\u{1F468}‍\u{1F469}‍\u{1F467}‍\u{1F466}",
  "\u{1F3F3}️‍\u{1F308}","\u{1F1EC}\u{1F1E7}","\u{1F3F4}\u{E0067}\u{E0062}\u{E0073}\u{E0063}\u{E0074}\u{E007F}","1️⃣","#️⃣",
  "\u{1F9D1}\u{1F3FD}‍\u{1F4BB}","\u{1F1EF}\u{1F1F5}","❤︎"];
async function emoji(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  const digits="<!doctype html><p>Call 1, 2 or # and * \u00a9 \u2122</p>";
  const plain=frame(engine,digits);
  // @ts-ignore plain JavaScript module of the Hub
  const {fontsFor}=await import("../../../docs/web/hub/foafnaut/font-coverage.mjs");
  const wanted=await fontsFor(`<p>${emojiSequences.join(" ")}</p>`,async(path:string)=>JSON.parse(await Deno.readTextFile(fonts+path.replace("./fonts/",""))));
  assert(wanted.some((f:{family:string})=>f.family==="Noto Emoji")&&wanted.length>6,`fonts ${wanted.map((f:{family:string})=>f.family)}`);
  for(const font of wanted)await loadFontFile(engine,fontFilePath(font.path),font.family,"bytes",true);
  for(const text of emojiSequences){
    const scene:HTMLArtifact=engine.compile(`<!doctype html><p>${text}</p>`,600,120,{checks:false,url:"file:///emoji.html"});
    const run=(scene.webRender.glyphRuns as {text:string;glyphs:number[][]}[]).find(r=>r.text===text);
    assert(run,`no glyph run for ${JSON.stringify(text)}`);
    // A glyph row is [id, x, y, advance, ...]; .notdef is id 0.
    const drawn=run.glyphs.filter(g=>g[3]>0);
    assert.equal(drawn.length,1,`${JSON.stringify(text)}: ${drawn.length} glyphs with width`);
    assert.notEqual(drawn[0][0],0,`${JSON.stringify(text)} is .notdef`);
  }
  // Colour: a 64 px emoji is one rectangle filled with an image of some 70 by 68 pixels, whose
  // pixels go in the paint table at the end of the tile lists; the same character with U+FE0E
  // is an outline of Noto Emoji, with no image.
  const big=(text:string)=>{
    const scene:HTMLArtifact=engine.compile(`<!doctype html><p style="font-size:64px;line-height:80px">${text}</p>`,600,120,{checks:false,url:"file:///emoji.html"});
    return {primitives:scene.primitiveCount,table:scene.tiles.length};
  };
  const empty=big("").table;
  for(const text of ["\u{1F600}","❤️","\u{1F1EC}\u{1F1E7}","\u{1F44D}\u{1F3FD}"]){
    const b=big(text);
    assert(b.primitives===1&&b.table-empty>3000,`${JSON.stringify(text)} is not one colour image: ${JSON.stringify(b)}`);
  }
  assert(big("❤︎").table-empty<3000,"❤ with U+FE0E is not an outline");
  // Digits, # and * with no selector stay in Noto Sans: the page is as it was.
  assert(same(plain,frame(engine,digits)),"plain digits and symbols changed with the emoji fonts");
}
// SVG text and canvas text (issue 1276): SVG text draws outlines, so an emoji there comes
// from Noto Emoji (the Hub fetches it for a page with emoji and an SVG text element); canvas
// fillText draws the colour glyph's image. Neither is blank.
async function emojiInSvgAndCanvas(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  // @ts-ignore plain JavaScript module of the Hub
  const {fontsFor}=await import("../../../docs/web/hub/foafnaut/font-coverage.mjs");
  const svg=(text:string)=>`<!doctype html><svg width="200" height="60"><text x="10" y="45" font-size="32">${text}</text></svg>`;
  const wanted=await fontsFor(svg("\u{1F600}"),async(path:string)=>JSON.parse(await Deno.readTextFile(fonts+path.replace("./fonts/",""))));
  assert.deepEqual(wanted.map((f:{family:string})=>f.family),["Noto Color Emoji Smileys","Noto Emoji"]);
  for(const font of wanted)await loadFontFile(engine,fontFilePath(font.path),font.family,"bytes",true);
  const count=(html:string)=>engine.compile(html,300,80,{checks:false,url:"file:///svg.html"}).primitiveCount;
  assert(count(svg("\u{1F600}"))>count(svg("")),"an emoji in SVG text draws nothing");
  if(!nativeEngine)return;
  const turn=engine.scriptSession(`<!doctype html><canvas id=c width=60 height=60></canvas><script>
const c=document.getElementById('c').getContext('2d');c.font='40px sans-serif';c.fillText('\u{1F600}',5,45);
const d=c.getImageData(27,25,1,1).data;console.log('emoji '+d[0]+' '+d[1]+' '+d[2]+' '+d[3]);</script>`,
    {action:"start",url:"file:///c.html",resources:[],instructionsPerMs:1e12,full:true,engine:"bubblepop"}) as {logs:string[];errors:string[]};
  engine.scriptSession("",{action:"close"});
  const line=turn.logs.find(l=>l.startsWith("emoji "));
  assert(line,`no pixel: ${JSON.stringify(turn)}`);
  const [r,g,b,a]=line.split(" ").slice(1).map(Number);
  assert(a===255&&r>200&&g>140&&b<120,`the canvas emoji is not the yellow face: ${line}`);
}
Deno.test("emoji in SVG text draw from Noto Emoji (Wasm)",()=>emojiInSvgAndCanvas());
Deno.test({name:"emoji in SVG text draw from Noto Emoji, and canvas fillText draws colour emoji (native library)",ignore:noLibrary,fn:()=>emojiInSvgAndCanvas(library)});
Deno.test("emoji and emoji sequences draw in colour from Noto Color Emoji (Wasm)",()=>emoji());
Deno.test({name:"emoji and emoji sequences draw in colour from Noto Color Emoji (native library)",ignore:noLibrary,fn:()=>emoji(library)});

// The native window's fallback fonts (native_html_fonts.ts): for each page, the fonts of the
// Hub's table that its characters need go into the engine worker before the first layout,
// read as bytes, and stay held. Arabic, Hebrew, Devanagari, Thai and Han then draw with no
// .notdef glyph (id 0), where Noto Sans alone draws them as .notdef.

const scriptSamples={Arabic:"مرحبا بالعالم",Hebrew:"שלום עולם",Devanagari:"नमस्ते दुनिया",Thai:"สวัสดีชาวโลก",Han:"你好世界"};
const scriptsPage="<!doctype html><title>Scripts</title>"+Object.entries(scriptSamples).map(([name,text])=>`<p>${name}: ${text}</p>`).join("");
/** The .notdef glyphs (id 0) drawn in each sample's line. */
function notdefs(scene:HTMLArtifact){
  const runs=scene.webRender.glyphRuns as {text:string;glyphs:number[][]}[];
  return Object.fromEntries(Object.entries(scriptSamples).map(([name,text])=>{
    const mine=runs.filter(run=>[...run.text].some(ch=>ch.codePointAt(0)!>0x7f&&text.includes(ch)));
    assert(mine.length,`no glyph run for the ${name} sample`);
    return [name,mine.reduce((n,run)=>n+run.glyphs.filter(g=>g[0]===0).length,0)];
  }));
}
async function nativeHostDraws(nativeEngine?:string){
  const client=await startCompileWorker({path:sans,family:"Noto Sans"},nativeEngine);
  try{
    const answers:PageFonts[]=[];
    const open=async(html:string,name:string)=>{
      const page=await prepareHTML(client.engine as unknown as PageEngine,`file:///${name}.html`,undefined,html);
      return await page.compile(900,600,{checks:false} as Record<string,unknown>) as unknown as HTMLArtifact;
    };
    // With Noto Sans alone (no font host), every sample is .notdef.
    setFontHost(undefined);
    const plain=notdefs(await open(scriptsPage,"plain"));
    for(const [name,count] of Object.entries(plain))assert(count>0,`${name} drew with Noto Sans alone`);
    // As run_html.ts: the worker chooses the page's fonts and reads them beside its engine.
    setFontHost(async source=>{answers.push(await client.pageFonts(source));});
    // A page of Latin text with a character Noto Sans has loads no font.
    await open("<!doctype html><p>Caf\u00e9 \u2014 plain text.</p>","latin");
    assert.deepEqual(answers.map(a=>[a.loaded,a.held]),[[[],[]]]);
    // The page with the samples: its fonts, in table order, then not one .notdef.
    const drawn=notdefs(await open(scriptsPage,"scripts"));
    assert.deepEqual(drawn,{Arabic:0,Hebrew:0,Devanagari:0,Thai:0,Han:0});
    const families=["Noto Sans Hebrew","Noto Sans Arabic","Noto Sans Devanagari","Noto Sans Thai","Noto Sans JP Han"];
    assert.deepEqual(answers[1].loaded,families);
    assert.deepEqual(answers[1].held.map(font=>font.family),families);
    // The fonts stay held: the same page again loads nothing and draws the same.
    assert.deepEqual(notdefs(await open(scriptsPage,"again")),drawn);
    assert.deepEqual(answers[2].loaded,[]);
    assert.equal(answers[2].held.length,5);
  }finally{setFontHost(undefined);client.terminate();}
}
Deno.test("the native host draws Arabic, Hebrew, Devanagari, Thai and Han with no .notdef (Wasm worker)",()=>nativeHostDraws());
Deno.test({name:"the native host draws Arabic, Hebrew, Devanagari, Thai and Han with no .notdef (native library worker)",ignore:noLibrary,fn:()=>nativeHostDraws(library)});

// Arabic joining on the writing page (pages/showcase-scripts.html): each word's glyphs are the
// joined forms HarfBuzz chooses with the same font (hb-shape 15.0.0, NotoSansArabic-Regular.ttf,
// left to right as drawn): .init, .medi and .fina forms, the rlig lam-alef, the dots as marks.
// A change in GSUB coverage, joining or bidi shows here as other glyph ids.
const arabicJoined:Record<string,number[]>={
  "مرحبا":[9,316,16,27,31,79],     // uni0627.fina dotbelowar uni066E.medi uni062D.init uni0631.fina uni0645.init
  "بالعالم":[77,72,9,48,72,9,316,19],
  "سلام":[74,11,71,37],              // uni0645 uni0627.fina.rlig.2 uni0644.medi.rlig uni0633.init
  "السعر":[31,48,36,72,8],
  "دينار":[30,9,282,16,318,21,28],
};
async function arabicJoins(nativeEngine?:string){
  const client=await startCompileWorker({path:sans,family:"Noto Sans"},nativeEngine);
  try{
    setFontHost(async source=>{await client.pageFonts(source);});
    const file=new URL("./pages/showcase-scripts.html",import.meta.url);
    const page=await prepareHTML(client.engine as unknown as PageEngine,file.href,undefined,await Deno.readTextFile(file));
    const scene=await page.compile(900,1200,{checks:false} as Record<string,unknown>) as unknown as HTMLArtifact;
    const runs=scene.webRender.glyphRuns as {text:string;glyphs:number[][]}[];
    const drawn:Record<string,number[]>={};
    for(const run of runs)if(run.text in arabicJoined)drawn[run.text]=run.glyphs.map(g=>g[0]);
    assert.deepEqual(drawn,arabicJoined);
  }finally{setFontHost(undefined);client.terminate();}
}
Deno.test("Arabic on the writing page draws HarfBuzz's joined forms (Wasm worker)",()=>arabicJoins());
Deno.test({name:"Arabic on the writing page draws HarfBuzz's joined forms (native library worker)",ignore:noLibrary,fn:()=>arabicJoins(library)});

// What each page costs: a Latin page reads nothing, not even the table module; a page with
// a character Noto Sans has reads the table only; a script outside CJK loads its font with
// no coverage file; Han reads the coverage file once; held fonts are not asked for again.
Deno.test("fallback fonts per page: a Latin page loads none and reads no file",async()=>{
  const loads:string[][]=[],reads:string[]=[];
  const host=fallbackFontHost(async(fonts:FallbackFont[])=>{
    for(const font of fonts)Deno.statSync(font.path);
    loads.push(fonts.map(font=>font.family));return fonts.map(font=>({family:font.family,fonts:2}));
  },{readText:path=>{reads.push(path);return Deno.readTextFile(path);}});
  assert.deepEqual(await host.page("<!doctype html><p>Plain text, &amp; an entity.</p>"),{loaded:[],failed:[],held:[]});
  assert.equal(host.stats.tableLoaded,false);
  assert.deepEqual(await host.page("<p>Café © 2026 — €5</p>"),{loaded:[],failed:[],held:[]});
  assert.equal(host.stats.tableLoaded,true);
  assert.deepEqual([loads,reads],[[],[]]);
  assert.deepEqual((await host.page("<p>Hebrew by reference: &#x5d0;&#1489;</p>")).loaded,["Noto Sans Hebrew"]);
  assert.deepEqual((await host.page("<p>Բարեւ ש</p>")).loaded,["Noto Sans Armenian"]);
  assert.deepEqual(reads,[]);
  assert.deepEqual((await host.page("<p>你好，世界</p>")).loaded,["Noto Sans JP Kana","Noto Sans JP Han"]);
  // At most once in a process: another test may have had font-coverage.mjs read it already.
  assert(reads.length<=1&&reads.every(path=>path===fontFilePath("./fonts/noto-sans-cjk/coverage.json")));
  assert.deepEqual((await host.page("<p>世界 ש</p>")).loaded,[]);
  assert(reads.length<=1);
  assert.equal(loads.length,3);
  // A font that fails is not held, so a later page asks for it again.
  const failing=fallbackFontHost(async fonts=>fonts.map(font=>({family:font.family,error:"no"})));
  assert.deepEqual(await failing.page("<p>ส</p>"),{loaded:[],failed:["Noto Sans Thai"],held:[]});
  assert.deepEqual(failing.held(),[]);
});
// Every font and coverage file of the Hub's table is in third_party/fonts, where the app holds them.
Deno.test("every file of the fallback font table is in third_party/fonts",async()=>{
  // @ts-ignore plain JavaScript module of the Hub
  const {fallbackFonts}=await import("../../../docs/web/hub/foafnaut/fallback-fonts.mjs");
  for(const font of fallbackFonts as {path:string;bytes:number;coverage?:string}[]){
    assert.equal(Deno.statSync(fontFilePath(font.path)).size,font.bytes,font.path);
    if(font.coverage)assert(Deno.statSync(fontFilePath(font.coverage)).isFile,font.coverage);
  }
});
