// Layout sections of a layers answer, decoded on first read (issue 1124 stage B), and page
// answers kept or patched against the one the host holds (stage C).
import {allFinite} from "./finite_floats.ts";
/** The boxes, glyph runs and link regions of a layers answer sent as sections
(WebRender.layoutSections, request field `layoutSections`, issue 1124 stage B): `layoutData` holds
the float64 numbers and the UTF-8 strings as views of the answer's buffer, and `boxes`,
`glyphRuns` and `links` are getters that decode them on first read into the arrays a JSON answer
has. The getters are not enumerable, so a worker's postMessage sends the bytes, not decoded
arrays; the receiver calls this again (native_html_compile.ts). */
export function attachLayout(web:Record<string,unknown>|undefined):void {
  const raw=web?.layoutData as {nums:Uint8Array;text:Uint8Array}|undefined;
  if(!web||!raw||Object.getOwnPropertyDescriptor(web,"links"))return;
  const view=new DataView(raw.nums.buffer,raw.nums.byteOffset,raw.nums.byteLength);
  const f=(i:number)=>view.getFloat64(8*i,true);
  const boxCount=f(0),runCount=f(1),glyphCount=f(2),linkCount=f(3);
  if(view.byteLength!==8*(4+5*boxCount+7*runCount+6*glyphCount+7*linkCount))throw new Error("Unexpected Lean layout section");
  const runsAt=4+5*boxCount,glyphsAt=runsAt+7*runCount,linksAt=glyphsAt+6*glyphCount;
  const utf8=new TextDecoder();
  const text=(start:number,bytes:number)=>utf8.decode(raw.text.subarray(start,start+bytes));
  const lazy=(key:string,make:()=>unknown[])=>{
    let value:unknown;
    Object.defineProperty(web,key,{enumerable:false,configurable:true,get(){return value??=make();},set(x){value=x;}});
  };
  lazy("boxes",()=>{
    const out=new Array(boxCount);
    for(let k=0,i=4;k<boxCount;k++,i+=5)out[k]=[f(i),f(i+1),f(i+2),f(i+3),f(i+4)];
    return out;
  });
  lazy("glyphRuns",()=>{
    const out=new Array(runCount);
    for(let k=0,i=runsAt,g=glyphsAt;k<runCount;k++,i+=7){
      const glyphs=new Array(f(i+6));
      for(let j=0;j<glyphs.length;j++,g+=6)glyphs[j]=[f(g),f(g+1),f(g+2),f(g+3),f(g+4),f(g+5)];
      out[k]={source:f(i),font:text(f(i+2),f(i+3)),size:f(i+1),text:text(f(i+4),f(i+5)),glyphs};
    }
    return out;
  });
  lazy("links",()=>{
    const out=new Array(linkCount);
    for(let k=0,i=linksAt;k<linkCount;k++,i+=7)out[k]=[f(i),text(f(i+1),f(i+2)),f(i+3),f(i+4),f(i+5),f(i+6)];
    return out;
  });
}

/** A patch of one section (issue 1124 stage C): the section holds only the changed bytes, in
order; `ranges` are [byteOffset, byteLength] of the full section, and `size` its byte length. */
export type SectionPatch = {base:number;ranges:[number,number][];size:number};
type PatchedArtifact = {data:Float32Array;tiles?:Uint32Array;damage?:{id:number};dataPatch?:SectionPatch;tilesPatch?:SectionPatch;kept?:number};

/** The `damage.id` of a page answer the host holds, for the request field `have`
(WebDocument.layersJSON); undefined when it has none. */
export function heldPageId(page:unknown):number|undefined {
  const id=(page as {damage?:{id?:unknown}}|undefined)?.damage?.id;
  return typeof id==="number"&&Number.isSafeInteger(id)?id:undefined;
}

function applyPatch<T extends Float32Array|Uint32Array>(base:T,patch:SectionPatch,bytes:T,make:(b:ArrayBuffer)=>T):T {
  if(base.byteLength!==patch.size)throw new Error("Lean page patch: base size differs");
  const out=make(base.buffer.slice(base.byteOffset,base.byteOffset+base.byteLength) as ArrayBuffer);
  const dst=new Uint8Array(out.buffer),src=new Uint8Array(bytes.buffer,bytes.byteOffset,bytes.byteLength);
  let at=0;
  for(const [offset,length] of patch.ranges){
    if(offset<0||length<0||offset+length>patch.size||at+length>src.length)throw new Error("Lean page patch: range out of bounds");
    dst.set(src.subarray(at,at+length),offset);at+=length;
  }
  if(at!==src.length)throw new Error("Lean page patch: unused bytes");
  return out;
}

/** The page layer of a layers answer, made whole from the page answer the host holds (`held`,
whose `damage.id` the request named in `have`): `{kept:id}` is `held` itself; a page with
`dataPatch` (and `tilesPatch`) is `held`'s storage floats and tile words with the changed bytes
written in. The new page keeps `dataPatch`, so the layer compositor can upload only those ranges
when its buffer holds `base`. The answer was made by Lean against the bytes it last gave with
that id, so the result is the full answer (WebDocument.pagePatch). */
export function resolvePage<L extends {page:unknown}>(layers:L,held:unknown):L {
  const page=layers.page as PatchedArtifact,base=held as PatchedArtifact|undefined;
  if(typeof page?.kept==="number"){
    if(!base||heldPageId(base)!==page.kept)throw new Error("Lean answered a kept page the host does not hold");
    return {...layers,page:base};
  }
  if(!page?.dataPatch&&!page?.tilesPatch)return layers;
  const id=page.dataPatch?.base??page.tilesPatch!.base;
  if(!base||heldPageId(base)!==id)throw new Error("Lean answered a page patch against a page the host does not hold");
  // The changed storage floats are checked as a whole answer's are (sceneOf); the rest is `held`'s.
  if(page.dataPatch&&!allFinite(page.data))throw new Error("Unexpected published Lean HTML scene ABI");
  if(page.dataPatch)page.data=applyPatch(base.data,page.dataPatch,page.data,b=>new Float32Array(b));
  if(page.tilesPatch&&page.tiles&&base.tiles)page.tiles=applyPatch(base.tiles,page.tilesPatch,page.tiles,b=>new Uint32Array(b));
  return layers;
}
