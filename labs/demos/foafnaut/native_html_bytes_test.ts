// Bytes answers (issue 1268): `web_document_call_bin` gives the storage floats and tile
// words as raw sections beside a JSON head, with no Base64. The JSON text answer with
// Base64 stays the reference. For every demo page and four requests (one frame, one
// frame scrolled, layers, the CPU probes), the two give the same storage bytes, the same
// tile words and the same other fields, from the Wasm engine and, when it is built, the
// native library. Run with --allow-read --allow-ffi.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {inputURL,loadFontFile,prepareHTML} from "./native_html_document.ts";

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
  for(const e of [bytes,text])await loadFontFile(e,font,"Noto Sans");
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
