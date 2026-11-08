// Expected failures of foafnaut printing, https://github.com/danbri/factoidal/issues/1279.
// Each test states a gap as it is today. When a change closes a gap, its test fails: change
// the assertion to the correct behaviour and update the issue in the same landing.
// Gap 3 of the issue (tables) is closed by TableLayout (issue 1272 tests in showcase_gaps_test.ts).
// Run with --allow-read; needs .build/native-html/runtime/web-render.{mjs,wasm}.
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";

const stillGap=(gap:number)=>`expected failure of https://github.com/danbri/factoidal/issues/1279 gap ${gap} no longer fails: make this test assert the correct result and update the issue`;
const engine=await loadHTML();
const w=1046,h=1540;
const html=(head:string,body:string)=>`<!doctype html><html lang="en"><head><meta charset="utf-8"><title>print gap</title><style>body{margin:0}${head}</style></head><body>${body}</body></html>`;
const print={url:"https://example.test/",resources:[],media:"print"};
const layout=(source:string)=>engine.printLayout(source,w,h,print);
const printed=(source:string)=>engine.selectedText(source,w,h,{...print,selection:[0,0,w,layout(source).contentHeight]});
const tall=Array.from({length:60},(_,i)=>`<p>Line ${i}</p>`).join("");
const lab=new URL("./",import.meta.url).pathname;

Deno.test("expected failure, issue 1279 gap 1: the print layout gives row ranges only, no vector page content",()=>{
  // A vector path would give each page's scene (paths, glyph outlines) or a PDF/SVG writer.
  assert.deepEqual(Object.keys(layout(html("",tall))).sort(),["contentHeight","pages"],stillGap(1));
});

Deno.test("expected failure, issue 1279 gap 2: pages are images made before the print panel opens",()=>{
  // A paper or scale change in the panel would need Lean to lay the page out again from the view.
  const source=Deno.readTextFileSync(lab+"native_window.m");
  assert.match(source,/int32_t ng_print\(const uint8_t \*rgba/,stillGap(2));
});

Deno.test("expected failure, issue 1279 gap 4: the Hub page does not print through Lean",()=>{
  const hub=Deno.readTextFileSync(new URL("../../../docs/web/hub/foafnaut/browser.mjs",import.meta.url).pathname);
  assert.ok(!hub.includes("printLayout"),stillGap(4));
});

Deno.test("issue 1279 gap 5, closed for width features: @media print and (min-width: 1px) holds in print",()=>{
  // MediaQuery.lean evaluates width features against the paper width (2026-11-08), so the
  // paragraph is not printed. @page (below) stays a gap.
  const text=printed(html("@media print and (min-width: 1px){.gone{display:none}}","<p>Kept</p><p class='gone'>Hidden in print</p>"));
  assert.ok(text.includes("Kept")&&!text.includes("Hidden in print"),text);
});

Deno.test("expected failure, issue 1279 gap 5: @page size is not read",()=>{
  const plain=layout(html("",tall)).pages;
  const small=layout(html("@page{size:100px 100px;margin:0}",tall)).pages;
  assert.deepEqual(small,plain,stillGap(5));
});

Deno.test("expected failure, issue 1279 gap 6: no page numbers in print",()=>{
  // The page text has no digit, so any digit in the printed text would be a page number.
  const plainTall=Array.from({length:60},()=>"<p>Line</p>").join("");
  const source=html("@page{@bottom-center{content:counter(page)}}",plainTall);
  assert.ok(layout(source).pages.length>1,"the test page needs more than one page");
  assert.ok(!/[0-9]/.test(printed(source)),stillGap(6));
});
