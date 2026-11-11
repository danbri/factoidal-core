// Many images on one engine, call after call (issue 390: the decoded image stores are kept
// in the engine's state, `WebDocument.Engine.kept`, not in a cell). A page of 40 images,
// a second page that reuses some keys, the first again, and the first with one image
// replaced under its key: each render must have every image at its own size, no image
// of an earlier call, and the same boxes on the native library as on the Wasm engine.
// `MANY_IMAGES_DUMP=FILE` writes the boxes of each step, to compare with another engine
// (`WEB_RENDER_LIB=` another libweb-render.dylib).
// Run: deno test --allow-read --allow-ffi --allow-env --allow-write many_images_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLArtifact,type HTMLEngine} from "./native_html_engine.ts";
import {pngOf} from "./png_write.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Box=[number,number,number,number,number];
const origin="http://example.test";

async function sha256(bytes:Uint8Array){
  return [...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("");
}
/** Image `i` at version `v`: a size of its own, so a box says which bytes were drawn. */
const sizeOf=(i:number,v=0):[number,number]=>[10+i+50*v,5+((i*7)%31)+50*v];
async function image(i:number,v=0){
  const [w,h]=sizeOf(i,v);const px=new Uint8Array(w*h*4);
  for(let p=0;p<w*h;p++){px[p*4]=(i*37)&255;px[p*4+1]=(v*90+p)&255;px[p*4+2]=128;px[p*4+3]=255;}
  const bytes=await pngOf(w,h,px);
  return {key:`${origin}/i${i}.png`,bytes,sha256:await sha256(bytes),size:[w,h] as [number,number]};
}
const pageOf=(ids:number[])=>`<!doctype html><body style="margin:0">${ids.map(i=>`<img src="i${i}.png" alt="[missing ${i}]">`).join("")}`;

async function steps(engine:HTMLEngine){
  const v0=await Promise.all(Array.from({length:40},(_,i)=>image(i)));
  const v1=await image(3,1);
  // The engine holds one image a key: replacing i3 is a new imageLoad under its key.
  const hold=(set:typeof v0)=>{for(const im of set)engine.imageLoad!(im.bytes,im.key,im.sha256);};
  const all=Array.from({length:40},(_,i)=>i);
  const b=[0,1,2,3,4,5,6,7,8,9,30,31,32,33,34,35,36,37,38,39].reverse();
  const plan:[string,number[],typeof v0][]=[
    ["A",all,v0],["B",b,v0],["A again",all,v0],
    ["A with i3 replaced",all,v0.map((im,i)=>i===3?v1:im)],["A once more",all,v0],["B again",b,v0],
  ];
  const out:Record<string,Box[]>={};
  for(let round=0;round<2;round++)for(const [name,ids,set] of plan){
    if(name==="A with i3 replaced")hold([v1]);else hold(set===v0&&round+name!=="0A"?[v0[3]]:v0);
    const scene=engine.compile(pageOf(ids),900,4000,{url:`${origin}/p.html`,heldImages:ids.map(i=>({key:set[i].key,sha256:set[i].sha256}))}) as HTMLArtifact;
    const boxes=scene.webRender.boxes as Box[];
    const texts=(scene.webRender.glyphRuns as {text:string}[]).map(r=>r.text);
    assert(!texts.some(t=>t.includes("[missing")),`${name}: alt text drawn, an image is missing`);
    // Each image at the size of the bytes this request named.
    const want=new Map<string,number>();for(const i of ids){const k=set[i].size.join("x");want.set(k,(want.get(k)??0)+1);}
    for(const [k,n] of want){const [w,h]=k.split("x").map(Number);
      assert.equal(boxes.filter(x=>Math.abs(x[3]-w)<0.001&&Math.abs(x[4]-h)<0.001).length,n,`${name}: ${n} box(es) ${k}`);}
    // No image of another version: i3's two sizes never both in one frame.
    const [w0,h0]=sizeOf(3,0),[w1,h1]=sizeOf(3,1);
    const has=(w:number,h:number)=>boxes.some(x=>Math.abs(x[3]-w)<0.001&&Math.abs(x[4]-h)<0.001);
    if(ids.includes(3))assert(has(w0,h0)!==has(w1,h1),`${name}: i3 drawn once, at one version`);
    if(round===0)out[name]=boxes;else assert.deepEqual(boxes,out[name],`${name}: the same on the second round`);
  }
  return out;
}

Deno.test({name:"many images: native library, call after call on one engine",ignore:!exists(library),fn:async()=>{
  const native=await steps(await loadHTML(library));
  const dump=Deno.env.get("MANY_IMAGES_DUMP");if(dump)Deno.writeTextFileSync(dump,JSON.stringify(native));
}});
Deno.test("many images: Wasm engine, the same boxes as native",async()=>{
  const wasm=await steps(await loadHTML());
  if(exists(library)&&!Deno.env.get("WEB_RENDER_LIB"))assert.deepEqual(await steps(await loadHTML(library)),wasm);
});
