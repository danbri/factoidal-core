// Partial compile of a layer (NativeSVG.compileRetained, WebPaint.retainedAnswer), counted by
// the engine: a frame in which one shape moved compiles that primitive and keeps the others,
// and the bytes are those of the plain compile; a frame with no change does no work. The
// number compiled does not depend on the size of the page. Native library only (the counts
// need the engine that has them); Wasm is covered by the same Lean code.
// Run: deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi --allow-read --allow-ffi partial_frame_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLLayers} from "./native_html_engine.ts";
import {prepareHTML,loadFontFile} from "./native_html_document.ts";

const library=Deno.env.get("WEB_RENDER_DYLIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const url=new URL("./pages/partial-frame.html",import.meta.url).href;

const page=(n:number)=>`<!doctype html><body style="margin:0">
<svg width="800" height="${Math.max(600,Math.ceil(n/20)*40+60)}" viewBox="0 0 800 ${Math.max(600,Math.ceil(n/20)*40+60)}">
<g id="mover"><rect x="10" y="10" width="20" height="20" fill="#336699"/></g>
<g id="group"><path d="M40 12 q 8 -8 16 0 t 16 0 v 10 h -32 z" fill="#884400"/><path d="M90 12 q 8 -8 16 0 t 16 0 v 10 h -32 z" fill="#448800"/><path d="M140 12 c 8 -8 16 8 24 0 v 10 h -24 z" fill="#004488"/></g>
${Array.from({length:n},(_,i)=>`<circle cx="${20+(i%20)*40}" cy="${60+Math.floor(i/20)*40}" r="14" fill="#cc6600"/>`).join("")}
</svg></body>`;
const shell={tabs:[{title:"t"}],active:0,address:url,focused:false,canBack:false,canForward:false,loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};

const sameBytes=(a:ArrayLike<number>,b:ArrayLike<number>,what:string)=>{
  assert.equal(a.length,b.length,`${what}: length`);
  for(let i=0;i<a.length;i++)if(!(a[i]===b[i]||(Number.isNaN(a[i])&&Number.isNaN(b[i]))))assert.fail(`${what}: differs at ${i}: ${a[i]} vs ${b[i]}`);
};

Deno.test({name:"partial compile counts and bytes",ignore:noLibrary,sanitizeResources:false,sanitizeOps:false,fn:async()=>{
  const engine=await loadHTML(library);
  await loadFontFile(engine,new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname,"Noto Sans");
  for(const n of [40,800]){
    const html=page(n);
    const doc=await prepareHTML(engine as never,url,undefined,html);
    const nodes=(engine.inspect(doc.source,{url}) as unknown as {nodes:{id:number;attributes:Record<string,string>}[]}).nodes;
    const mover=nodes.find(x=>x.attributes.id==="mover")!.id;
    const base=doc.request(800,600).options;
    const at=(x:number,extra:Record<string,unknown>={})=>({...base,shell,checks:false,commands:[{op:"setAttribute",nodeId:mover,name:"transform",value:`translate(${x} 0)`}],...extra});
    const damageOf=(l:HTMLLayers)=>(l.page as unknown as {damage?:{id:number;base:number|null;rects:number[][]|null}}).damage;
    engine.compileLayers(doc.source,800,600,at(0));
    engine.compileLayers(doc.source,800,600,at(5));
    engine.frameWork(true);
    const frame=engine.compileLayers(doc.source,800,600,at(90));
    const work=engine.frameWork(true)!;
    const d=damageOf(frame);
    assert(d,"the answer has a damage record");
    assert(d.base!==null&&d.rects,"damage against the last frame");
    assert.equal(work.layouts,0,"no layout");
    // One primitive moved: it is compiled, and the others are kept.
    assert.equal(work.recompiled,1,`recompiled at n=${n}: ${JSON.stringify(work)}`);
    assert(work.reused!>=n,`reused at n=${n}: ${JSON.stringify(work)}`);
    // The rectangles cover only the rows of the moved rect (its row of tiles, and a little).
    const damagedRows=new Set(d.rects.flatMap(([, y,,h])=>Array.from({length:h},(_,i)=>y+i)));
    assert(damagedRows.size<=4*32,`few damaged rows, got ${damagedRows.size}`);
    // The move of a group of curved paths: no curve is flattened again, all three keep their
    // geometry, and the bytes are those of the plain compile (below).
    const group=nodes.find(x=>x.attributes.id==="group")!.id;
    const both=(x:number,g:number,extra:Record<string,unknown>={})=>({...base,shell,checks:false,commands:[{op:"setAttribute",nodeId:mover,name:"transform",value:`translate(${x} 0)`},{op:"setAttribute",nodeId:group,name:"transform",value:`translate(${g} 3)`}],...extra});
    engine.compileLayers(doc.source,800,600,both(90,0));
    engine.compileLayers(doc.source,800,600,both(90,7));
    engine.frameWork(true);
    const shifted=engine.compileLayers(doc.source,800,600,both(90,31));
    const groupWork=engine.frameWork(true)!;
    assert.equal(groupWork.recompiled,0,`group move flattens nothing: ${JSON.stringify(groupWork)}`);
    assert.equal(groupWork.moved,3,`group move: ${JSON.stringify(groupWork)}`);
    const groupPlain=engine.compileLayers(doc.source,800,600,both(90,31,{retained:false}));
    sameBytes(shifted.page.data,groupPlain.page.data,`group move data n=${n}`);
    sameBytes(shifted.page.tiles as ArrayLike<number>,groupPlain.page.tiles as ArrayLike<number>,`group move tiles n=${n}`);
    // The same frame again: the kept answer, nothing to draw.
    engine.frameWork(true);
    const again=engine.compileLayers(doc.source,800,600,at(90));
    assert.equal(damageOf(again)!.id,d.id,"a frame with no change answers the same id");
    assert.equal(engine.frameWork(true)!.recompiled,0,"a frame with no change compiles nothing");
    // The bytes are those of the plain compile of the same frame.
    const plain=engine.compileLayers(doc.source,800,600,at(90,{retained:false}));
    assert(damageOf(plain)===undefined,"the plain path answers no damage");
    assert.equal(frame.page.primitiveCount,plain.page.primitiveCount);
    sameBytes(frame.page.data,plain.page.data,`data n=${n}`);
    sameBytes(frame.page.tiles as ArrayLike<number>,plain.page.tiles as ArrayLike<number>,`tiles n=${n}`);
  }
}});
