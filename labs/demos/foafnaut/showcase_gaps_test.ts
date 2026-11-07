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

Deno.test("expected failure, issue 1270: SVG text refuses the showcase textPath page",async()=>{
  const doc=await prepareHTML(engine,inputURL(pages+"showcase-textpath.html",true));
  assert.throws(()=>doc.compile(900,700),/unsupported (attribute on text|SVG element: text)/,stillGap("1270"));
});

Deno.test("expected failure, issue 1271: the window refuses the showcase script page",async()=>{
  await assert.rejects(()=>prepareHTML(engine,inputURL(pages+"showcase-dataviz-script.html",true)),
    /does not execute scripts/,stillGap("1271"));
});

Deno.test("expected failure, issue 1272: table cells stack as blocks",()=>{
  const body="<table><tr><td>alpha</td><td>beta</td></tr></table>";
  assert.ok(left(run(body,"beta"))<=left(run(body,"alpha")),stillGap("1272"));
});

Deno.test("expected failure, issue 1272: an inline-block width is ignored",()=>{
  const body="<p><span style='display:inline-block;width:200px'>one</span><span>two</span></p>";
  assert.ok(left(run(body,"two"))<100,stillGap("1272"));
});

Deno.test("expected failure, issue 1273: border and text-align are dropped",()=>{
  const plain=frame("<div>boxed</div>").primitiveCount;
  assert.equal(frame("<div style='border:4px solid #c00'>boxed</div>").primitiveCount,plain,stillGap("1273"));
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
