// Bytes answers (issue 1268): `web_document_call_bin` gives the storage floats and tile
// words as raw sections beside a JSON head, with no Base64. The JSON text answer with
// Base64 stays the reference. For every demo page and four requests (one frame, one
// frame scrolled, layers, the CPU probes), the two give the same storage bytes, the same
// tile words and the same other fields, from the Wasm engine and, when it is built, the
// native library. The bytes engine also takes its font as bytes (`web_document_font_call_bin`)
// and the text engine as Base64, so the same frames also show the same held font.
// Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {inputURL,loadFontData,loadFontFile,prepareHTML} from "./native_html_document.ts";

const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const pagesDir=new URL("./pages/",import.meta.url).pathname;
// A page that is an expected refusal (manifest "refused" or "appRefused", with its issue) has no scene.
const refusedPages=new Set((JSON.parse(Deno.readTextFileSync(pagesDir+"manifest.json")).pages as {page:string;refused?:string;appRefused?:string}[])
  .filter(p=>p.refused||p.appRefused).map(p=>p.page));
const pages=[...Deno.readDirSync(pagesDir)].map(e=>e.name).filter(n=>n.endsWith(".html")&&!refusedPages.has(n)).sort();

const bytesOf=(part:unknown)=>{
  if(part instanceof Float32Array||part instanceof Uint32Array)return new Uint8Array(part.buffer,part.byteOffset,part.byteLength);
  if(Array.isArray(part))return new Uint8Array(new Uint32Array(part).buffer);
  throw new Error("scene part is not an array");
};
const rest=(scene:Partial<HTMLArtifact>)=>{const {data:_d,tiles:_t,...other}=scene;return JSON.stringify(other);};
function sameScene(bytes:Partial<HTMLArtifact>,text:Partial<HTMLArtifact>,label:string){
  assert(bytes.data instanceof Float32Array&&bytes.tiles instanceof Uint32Array,`${label}: bytes answer has no sections`);
  assert.deepEqual(bytesOf(bytes.data),bytesOf(text.data),`${label}: storage bytes differ`);
  assert.deepEqual(bytesOf(bytes.tiles),bytesOf(text.tiles),`${label}: tile words differ`);
  assert.equal(rest(bytes),rest(text),`${label}: other fields differ`);
}
async function pair(nativeEngine?:string):Promise<[HTMLEngine,HTMLEngine]> {
  const bytes=await loadHTML(nativeEngine,"bytes"),text=await loadHTML(nativeEngine,"text");
  const held=[await loadFontFile(bytes,font,"Noto Sans","bytes"),await loadFontFile(text,font,"Noto Sans","text")];
  assert.deepEqual(held[0],held[1],"font answers differ");
  assert.deepEqual(held[0],{family:"Noto Sans",glyphs:3884,fonts:1});
  return [bytes,text];
}
async function compare(nativeEngine?:string){
  const [bytes,text]=await pair(nativeEngine);
  let scenes=0;
  for(const name of pages){
    const doc=await prepareHTML(text,inputURL(pagesDir+name,true));
    const shell=(scroll:number)=>({tabs:[{title:doc.title??""}],active:0,address:doc.url,cursor:0,focused:false,canBack:false,
      canForward:false,loading:false,scale:2,theme:"next",pages:1,scroll});
    const {source,options}=doc.request(1600,1200);
    for(const [kind,extra] of [["frame",{checks:false,shell:shell(0)}],["scroll",{checks:false,shell:shell(400)}],
      ["probes",{shell:shell(0)}],["layers",{checks:false,shell:shell(400)}]] as const){
      const o={...options,textScalePercent:150,...extra};
      if(kind==="layers"){
        const b=bytes.compileLayers(source,1600,1200,o),t=text.compileLayers(source,1600,1200,o);
        assert.equal(JSON.stringify(b.layers),JSON.stringify(t.layers));
        sameScene(b.page,t.page,`${name} ${kind} page`);sameScene(b.chrome,t.chrome,`${name} ${kind} chrome`);
        scenes+=2;
      }else{sameScene(bytes.compile(source,1600,1200,o),text.compile(source,1600,1200,o),`${name} ${kind}`);scenes++;}
    }
  }
  // A Lean error comes back as an error from both.
  assert.throws(()=>bytes.compile("",0,0,{}));
  assert.throws(()=>bytes.compile("<p>a</p>",10,10,{images:3}),/document images must be an array/);
  return scenes;
}
Deno.test("bytes answers give the bytes of the Base64 answers on every demo page (Wasm)",async()=>{
  const scenes=await compare();
  console.log(`Wasm: ${scenes} scenes equal (${pages.length} pages)`);
});
Deno.test({name:"bytes answers give the bytes of the Base64 answers on every demo page (native library)",
  ignore:(()=>{try{Deno.statSync(library);return false;}catch{return true;}})(),
  fn:async()=>{const scenes=await compare(library);console.log(`native: ${scenes} scenes equal (${pages.length} pages)`);}});

// A font above about 3 MB can not go as Base64 in a JSON string: Wasm copies string
// arguments onto its 4 MB stack. As bytes it goes into the heap. The file here is Noto Sans
// with zero bytes after it, to 6 MiB; the tables are where the directory says.
async function largeFont(nativeEngine?:string){
  const engine=await loadHTML(nativeEngine,"bytes");
  const file=await Deno.readFile(font),big=new Uint8Array(6*1048576);
  big.set(file);
  assert.deepEqual(await loadFontData(engine,big,"Noto Sans 6 MiB"),{family:"Noto Sans 6 MiB",glyphs:3884,fonts:1});
  const scene=engine.compile("<p>A large font file</p>",200,80,{checks:false});
  assert(scene.data.length>0);
  // Not a font: a Lean refusal, and the engine still answers after it.
  assert.throws(()=>engine.fontLoadBytes(new Uint8Array([1,2,3]),"x","y"),/font\.file|font file/);
  assert.throws(()=>engine.fontLoadBytes(new Uint8Array(0),"x","y"),/font\.file|font file/);
  assert(engine.compile("<p>still here</p>",200,80,{checks:false}).data.length>0);
}
Deno.test("a 6 MiB font file loads as bytes (Wasm)",()=>largeFont());
Deno.test({name:"a 6 MiB font file loads as bytes (native library)",
  ignore:(()=>{try{Deno.statSync(library);return false;}catch{return true;}})(),fn:()=>largeFont(library)});
