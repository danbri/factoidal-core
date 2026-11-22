// Background images (CSS Backgrounds 3 §3.3, issue https://github.com/danbri/factoidal-core/issues/704):
// `background-image: url(...)` and the `background` shorthand paint the image over the colour,
// at its natural size, repeated from the padding box's top left corner and clipped to the border
// box (the initial background-origin, -position, -repeat and -clip). Before 2026-11-22 only a
// linear gradient was painted. Checked on CPU pixels of the native library, with a data: URL so
// that no host fetch is needed (Layout.backgroundTiles, WebDocument.attachBackgrounds).
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,nativeBackends,unpackAnswer} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";

const sans=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const libraries=["libweb-render.dylib","libweb-render.so"].map(n=>new URL(`./.build/web-render/engines/${n}`,import.meta.url).pathname);
const library=libraries.find(p=>{try{Deno.statSync(p);return true;}catch{return false;}});

// A 2 by 2 PNG: green and blue on the first row, blue and green on the second.
const checker="data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAIAAAACCAYAAABytg0kAAAAFUlEQVR4nGNgaGD4z8DwH4hBBJADADhjBvtG/ELoAAAAAElFTkSuQmCC";
const W=200,H=100;

function pixels(lib:string,html:string):Uint8Array {
  const buffer=nativeBackends(lib).bytes(html,JSON.stringify({op:"render",checks:false,cpu:true,url:"https://example.test/page.html"}),W,H);
  const {head,sections}=unpackAnswer(buffer);
  const scene=(head.page??head) as Record<string,unknown>;
  const [offset,length]=sections[scene.pixelsSection as number];
  return new Uint8Array(buffer,offset,length);
}
const at=(p:Uint8Array,x:number,y:number)=>{const i=(y*W+x)*4;return [p[i],p[i+1],p[i+2]];};
const green=(c:number[])=>c[0]<30&&c[1]>100&&c[1]<160&&c[2]<30;
const blue=(c:number[])=>c[0]<30&&c[1]<30&&c[2]>220;
const red=(c:number[])=>c[0]>220&&c[1]<30&&c[2]<30;

async function check(lib:string){
  const engine=await loadHTML(lib,"bytes");
  await loadFontFile(engine,sans,"Noto Sans");
  // A 40 by 20 box at (10,10) with a 5 px border: the tiles start at the padding box (15,15),
  // so (15,15) is green, (16,15) blue, (15,16) blue, (16,16) green; the white border covers the rest.
  const page=`<!doctype html><body style="margin:0"><div style="position:absolute;left:10px;top:10px;width:30px;height:10px;border:5px solid #ffffff;background:red url(${checker})"></div></body>`;
  const p=pixels(lib,page);
  assert.ok(green(at(p,15,15)),`(15,15) green, got ${at(p,15,15)}`);
  assert.ok(blue(at(p,16,15)),`(16,15) blue, got ${at(p,16,15)}`);
  assert.ok(blue(at(p,15,16)),`(15,16) blue, got ${at(p,15,16)}`);
  assert.ok(green(at(p,16,16)),`(16,16) green, got ${at(p,16,16)}`);
  // the border paints over the tiles; nothing past the border box
  const border=at(p,11,11);
  assert.ok(border[0]>240&&border[1]>240&&border[2]>240,`the border is over the image, got ${border}`);
  assert.ok(!red(at(p,30,20)),"the image is over the colour");
  const outside=at(p,55,20);
  assert.ok(outside[0]>240&&outside[1]>240&&outside[2]>240,`nothing past the border box, got ${outside}`);
  // background-image alone, and none: the colour only
  const q=pixels(lib,`<!doctype html><body style="margin:0"><div style="width:40px;height:20px;background-color:red;background-image:url(${checker})"></div></body>`);
  assert.ok(green(at(q,0,0))&&blue(at(q,1,0)),`background-image paints, got ${at(q,0,0)} ${at(q,1,0)}`);
  const r=pixels(lib,`<!doctype html><body style="margin:0"><div style="width:40px;height:20px;background-color:red;background-image:none"></div></body>`);
  assert.ok(red(at(r,5,5)),"background-image: none paints the colour");
}

Deno.test({name:"background images: tiled from the padding box, clipped to the border box (native CPU pixels)",ignore:!library,fn:async()=>{await check(library!);}});
