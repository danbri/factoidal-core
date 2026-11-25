// Layout sections of a layers answer, decoded on first read (issue 1124 stage B).
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
