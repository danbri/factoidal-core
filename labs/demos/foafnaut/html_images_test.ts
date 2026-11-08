// HTML `img` as a replaced element drawn by Lean (Layout.lean `Picture`, `replacedSize`):
// the Images demo page on the Wasm engine and, when it is built, the native library.
// Lean lists the images it wants (`inspect`), the host fetches those of the page's own
// origin (`fetchImages`), and Lean decodes and lays them out. The two engines must give
// the same boxes. Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {imageAllowed,prepareHTML} from "./native_html_document.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const page=new URL("./pages/showcase-images.html",import.meta.url).href;

type Box=[number,number,number,number,number];
const boxesOf=(scene:HTMLArtifact)=>scene.webRender.boxes as Box[];
const textsOf=(scene:HTMLArtifact)=>(scene.webRender.glyphRuns as {text:string}[]).map(run=>run.text);
const sized=(boxes:Box[],w:number,h:number)=>boxes.filter(b=>Math.abs(b[3]-w)<0.001&&Math.abs(b[4]-h)<0.001).length;

async function images(engine:HTMLEngine) {
  const wanted=engine.inspect(Deno.readTextFileSync(new URL(page)),{url:page}).images??[];
  assert.deepEqual(wanted.map(i=>i.key.split("/").pop()),["images-badge.png","images-landscape.png","images-missing.png"]);
  const document=await prepareHTML(engine,page);
  const scene=await document.compile(900,1500,{}) as HTMLArtifact;
  const boxes=boxesOf(scene),texts=textsOf(scene);
  // Intrinsic size, block and inline; the badge twice in the text and once with object-fit:none.
  assert.equal(sized(boxes,160,96),1,"block landscape at 160 by 96");
  assert.equal(sized(boxes,48,48),2,"two badges in the text");
  // width="320": the height follows the ratio.
  assert.equal(sized(boxes,320,192),1,"width only");
  // max-width:100% in a box 120 wide; and width="120" with a 2 px border and 4 px padding.
  assert.equal(sized(boxes,120,72),1,"max-width in a narrow box");
  assert.equal(sized(boxes,132,84),1,"border and padding");
  // Four object-fit boxes, 96 by 96 with a 1 px border.
  assert.equal(sized(boxes,98,98),4,"object-fit boxes");
  // Alt text only for the missing image.
  assert(texts.includes("[the")&&texts.includes("image]"),"alt text of the missing image");
  assert(!texts.includes("[A")&&!texts.includes("[badge]"),"no alt text for a drawn image");
  // pre keeps its spaces: "width" starts 10 columns after "name".
  const pre=(scene.webRender.glyphRuns as {text:string;glyphs:number[][]}[]).filter(r=>r.text==="name"||r.text==="width");
  assert.equal(pre.length,2);
  const [name,width]=pre;
  assert(Math.abs(width.glyphs[0][1]-name.glyphs[0][1]-10*name.glyphs[0][3])<0.001,"pre spaces kept");
  // A host that sends no images (or an engine that wants none) gets the alt text, as before.
  const bare=engine.compile(document.source,900,1500,{url:document.url}) as HTMLArtifact;
  assert(textsOf(bare).includes("[A"),"alt text with no image bytes");
  assert.equal(sized(boxesOf(bare),320,192),0);
  return boxes;
}

Deno.test("img: only the page's own origin, with no proxy",()=>{
  assert(imageAllowed("https://a.example/x.png","https://a.example/page.html"));
  assert(!imageAllowed("https://b.example/x.png","https://a.example/page.html"));
  assert(!imageAllowed("http://a.example/x.png","https://a.example/page.html"));
  assert(!imageAllowed("file:///etc/x.png","https://a.example/page.html"));
  assert(imageAllowed("file:///tmp/x.png","file:///tmp/page.html"));
  assert(!imageAllowed("https://a.example/x.png","file:///tmp/page.html"));
});
Deno.test("img: the Images page, Wasm engine",async()=>{await images(await loadHTML());});
Deno.test({name:"img: the Images page, native library, the same boxes as Wasm",ignore:noLibrary,fn:async()=>{
  assert.deepEqual(await images(await loadHTML(library)),await images(await loadHTML()));
}});
