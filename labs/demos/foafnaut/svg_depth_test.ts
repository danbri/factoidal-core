// Inline SVG deep in an HTML document (SVGReferences.lean maxIndexDepth, WebDocument.liberalSvg).
// The SVG reader indexes the identifiers of the whole HTML document, and until 2026-11-15 it
// refused the document when the HTML was nested more than 32 deep, so a page with an icon at
// depth 40 (a GitHub repository page) ended the browser with "SVG identifier nesting exceeds
// 32". Original constructs: an icon inside 40 nested elements is drawn, in strict mode, and an
// icon inside 300 is dropped by liberal mode while the rest of the page is drawn.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env --allow-write svg_depth_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {prepareHTML} from "./native_html_document.ts";
import {consoleOf} from "./native_console.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

const icon=`<svg width="16" height="16" viewBox="0 0 16 16"><defs><path id="sq" d="M0 0h16v16H0z"/></defs><use href="#sq" fill="green"/></svg>`;
const deep=(depth:number,withIcon:boolean)=>`<!doctype html><html><head><title>Deep icon</title></head><body><p>Before the icon.</p>`+
  "<div>".repeat(depth)+(withIcon?icon:"")+"</div>".repeat(depth)+`<p>After the icon.</p></body></html>`;

async function compileOf(engine:HTMLEngine,source:string,liberal:boolean){
  const dir=await Deno.makeTempDir();
  try{
    const file=`${dir}/page.html`;await Deno.writeTextFile(file,source);
    const doc=await prepareHTML(engine,new URL(`file://${file}`).href,undefined,undefined,liberal?{liberal:true}:undefined);
    const frame=await doc.compile(800,600,{textScalePercent:100});
    return {frame,system:consoleOf(doc).filter(e=>e.source==="System")};
  }finally{await Deno.remove(dir,{recursive:true});}
}

Deno.test({name:"Inline SVG inside 40 nested elements is drawn; inside 300 it is dropped and the page drawn (native library)",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const withIcon=await compileOf(engine,deep(40,true),false),without=await compileOf(engine,deep(40,false),false);
  assert.ok(withIcon.frame.primitiveCount>without.frame.primitiveCount,`depth 40: the icon is not drawn (${withIcon.frame.primitiveCount} primitives, ${without.frame.primitiveCount} without it)`);
  const deeper=await compileOf(engine,deep(300,true),true);
  assert.ok(deeper.frame.primitiveCount>2,"depth 300: the page is not drawn");
  assert.ok(deeper.system.length>0,"depth 300: liberal mode lists nothing it skipped");
  console.log(`depth 40: ${withIcon.frame.primitiveCount} primitives (${without.frame.primitiveCount} without the icon); depth 300: ${deeper.frame.primitiveCount} primitives, skipped ${deeper.system.map(e=>e.feature).join(", ")}`);
}});
