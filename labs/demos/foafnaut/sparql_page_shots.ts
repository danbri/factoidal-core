// Pictures of the SPARQL planner page (WebSparql.lean), drawn by Lean on this machine's GPU,
// as PNG files: each example query, run in full, and one step of the BGP join example.
//
// deno run --unstable-webgpu --unstable-ffi --allow-read --allow-write --allow-ffi \
//   sparql_page_shots.ts OUT_DIR [--native-engine DYLIB]
import {deflateSync} from "node:zlib";
import {loadHTML} from "./native_html_engine.ts";
import {loadFontFile,prepareHTML} from "./native_html_document.ts";
import {render} from "./gpu_transport.ts";

const args=[...Deno.args];
const out=args.shift();
if(!out)throw new Error("usage: sparql_page_shots.ts OUT_DIR [--native-engine DYLIB]");
const nativeEngine=args[0]==="--native-engine"?args[1]:undefined;
if(!await navigator.gpu?.requestAdapter()){console.log("NOT RUN: sparql_page_shots.ts needs a GPU adapter");Deno.exit(0);}
const engine=await loadHTML(nativeEngine);
await loadFontFile(engine,new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname,"Noto Sans");

const table=new Uint32Array(256).map((_,n)=>{let c=n;for(let k=0;k<8;k++)c=c&1?0xedb88320^(c>>>1):c>>>1;return c>>>0;});
const crc=(bytes:Uint8Array)=>{let c=0xffffffff;for(const b of bytes)c=table[(c^b)&255]^(c>>>8);return (c^0xffffffff)>>>0;};
function png(rgba:Uint8Array,width:number,height:number):Uint8Array{
  const raw=new Uint8Array((width*4+1)*height);
  for(let y=0;y<height;y++){raw[y*(width*4+1)]=0;raw.set(rgba.subarray(y*width*4,(y+1)*width*4),y*(width*4+1)+1);}
  const chunk=(type:string,data:Uint8Array)=>{
    const body=new Uint8Array(4+data.length);body.set(new TextEncoder().encode(type));body.set(data,4);
    const c=new Uint8Array(12+data.length),v=new DataView(c.buffer);
    v.setUint32(0,data.length);c.set(body,4);v.setUint32(8+data.length,crc(body));return c;
  };
  const head=new Uint8Array(13),hv=new DataView(head.buffer);
  hv.setUint32(0,width);hv.setUint32(4,height);head.set([8,6,0,0,0],8);
  const parts=[new Uint8Array([137,80,78,71,13,10,26,10]),chunk("IHDR",head),chunk("IDAT",new Uint8Array(deflateSync(raw))),chunk("IEND",new Uint8Array())];
  const all=new Uint8Array(parts.reduce((n,p)=>n+p.length,0));let at=0;for(const p of parts){all.set(p,at);at+=p.length;}
  return all;
}

const encode=(q:string)=>encodeURIComponent(q).replace(/%20/g,"+");
const W=1000,H=1500;
await Deno.mkdir(out,{recursive:true});
const shots:[string,string][]=engine.sparqlInfo().examples.map(e=>[e.name.toLowerCase().replace(/[^a-z]+/g,"-"),"q="+encode(e.query)]);
shots.push(["bgp-join-step-3","q="+encode(engine.sparqlInfo().examples[0].query)+"&step=3"]);
for(const [name,argument] of shots){
  const page=engine.sparqlPage(argument);
  const doc=await prepareHTML(engine,"foafnaut:sparql/"+argument,undefined,page.source);
  const frame=engine.compile(page.source,W,H,doc.request(W,H).options);
  // The storage-buffer mode: a whole page is more than a uniform buffer holds.
  const rgba=await render(frame as unknown as Parameters<typeof render>[0],"svg-offscreen");
  if(!rgba)throw new Error("no GPU frame");
  const file=`${out}/sparql-${name}.png`;
  await Deno.writeFile(file,png(rgba,frame.width,frame.height));
  console.log(`${file}: ${frame.primitiveCount} paint items`);
}
