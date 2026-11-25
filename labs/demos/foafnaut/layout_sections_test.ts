// Layout sections (issue 1124 stage B): a layers answer with `layoutSections:true` carries the
// boxes, glyph runs and link regions as float64 and UTF-8 sections; the host decodes them into the
// arrays a JSON answer has. This test compares the two forms on the native engine, directly and
// through the engine worker (postMessage sends the bytes; the getters are made again on receipt),
// and checks that the pixel data and tile words are the same.
// Run with --allow-read --allow-ffi --allow-env --allow-net (the worker reads its module).
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";
import {prepareHTML,loadFontFile} from "./native_html_document.ts";
import {startCompileWorker} from "./native_html_compile.ts";

const suffix=Deno.build.os==="darwin"?"dylib":"so";
const library=new URL(`./.build/web-render/engines/libweb-render.${suffix}`,import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const font=new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname;
const shell={tabs:[{title:"t"}],active:0,address:"https://example.invalid/",cursor:0,focused:false,canBack:false,canForward:false,
  loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};
const near=(a:unknown,b:unknown):boolean=>{
  if(typeof a==="number"&&typeof b==="number")return a===b||Math.abs(a-b)<=1e-9*Math.max(1,Math.abs(a));
  if(Array.isArray(a)&&Array.isArray(b))return a.length===b.length&&a.every((x,i)=>near(x,b[i]));
  if(a&&b&&typeof a==="object"&&typeof b==="object"){
    const ka=Object.keys(a).sort(),kb=Object.keys(b).sort();
    return near(ka,kb)&&ka.every(k=>near((a as Record<string,unknown>)[k],(b as Record<string,unknown>)[k]));
  }
  return a===b;
};
type Web={boxes:unknown[];glyphRuns:unknown[];links:unknown[];layoutSections?:boolean};
function same(json:Web,sections:Web,label:string){
  assert.equal(sections.layoutSections,true,`${label}: the answer has layout sections`);
  for(const key of ["boxes","glyphRuns","links"] as const)
    assert(near(json[key],sections[key]),`${label}: ${key} differ`);
}
Deno.test({name:"layout sections decode to the JSON boxes, glyph runs and links",ignore:noLibrary,async fn(){
  const engine=await loadHTML(library);
  await loadFontFile(engine,font,"Noto Sans");
  for(const page of ["pages/index.html","pages/status.html"]){
    const doc=await prepareHTML(engine,new URL(page,import.meta.url).href);
    for(const scroll of [0,900]){
      const options={...doc.request(1600,1000).options,shell:{...shell,scroll},checks:false};
      const json=engine.compileLayers(doc.source,1600,1000,{...options,layoutSections:false});
      const bin=engine.compileLayers(doc.source,1600,1000,options);
      same(json.page.webRender as unknown as Web,bin.page.webRender as unknown as Web,`${page} scroll ${scroll}`);
      assert.deepEqual([...bin.page.data as Float32Array],[...json.page.data as Float32Array],"pixel data");
      assert.deepEqual([...(bin.page.tiles??[]) as Uint32Array],[...(json.page.tiles??[]) as Uint32Array],"tile words");
      assert(!Object.keys(bin.page.webRender).includes("glyphRuns"),"decoded arrays are not enumerable");
    }
  }
}});
Deno.test({name:"layout sections through the engine worker",ignore:noLibrary,sanitizeResources:false,sanitizeOps:false,async fn(){
  const engine=await loadHTML(library);
  await loadFontFile(engine,font,"Noto Sans");
  const worker=await startCompileWorker({path:font,family:"Noto Sans"},library);
  try{
    const doc=await prepareHTML(engine,new URL("pages/index.html",import.meta.url).href);
    const options={...doc.request(1600,1000).options,shell,checks:false};
    const json=engine.compileLayers(doc.source,1600,1000,{...options,layoutSections:false});
    const {layers}=await worker.compileLayers(doc.source,1600,1000,options);
    same(json.page.webRender as unknown as Web,layers.page.webRender as unknown as Web,"worker");
  }finally{worker.terminate();}
}});
