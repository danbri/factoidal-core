// Engine time of an SVG zoom: a group holding "Spın̈al Tap" in Fruktur, scaled
// 1 → 40 → 1 over 2 s at 60 frames a second (120 frames), as the page layer of a window.
// Two drivers: a script's setAttribute('transform') each frame (the commands of the page's
// script session), and <animateTransform> on the page clock. Prints p50, p95 and max of the
// engine's time per frame (compileLayers: layout or paint, then the band compile).
// Usage: deno run --allow-read --allow-ffi zoom_bench.ts [--engine PATH-to-dylib] [--frames N]
import {loadHTML} from "./native_html_engine.ts";
import {prepareHTML,loadFontFile} from "./native_html_document.ts";

const args=Deno.args;
const engineArg=args.includes("--engine")?args[args.indexOf("--engine")+1]:undefined;
const frames=args.includes("--frames")?Number(args[args.indexOf("--frames")+1]):120;
const engine=await loadHTML(engineArg);
// Fruktur is the engine's font here, so that an engine from before @font-face draws the same glyphs.
await loadFontFile(engine,new URL("../../../third_party/fonts/fruktur/Fruktur-Regular.ttf",import.meta.url).pathname,"Fruktur");
const pageURL=new URL("./pages/zoom-bench.html",import.meta.url).href;
const head=`<!doctype html><html><head><style>@font-face{font-family:Fruktur;src:url(../fonts/fruktur/Fruktur-Regular.ttf) format("truetype")}
body{margin:0}</style></head><body>`;
const svg=(inner:string)=>`${head}<svg width="728" height="150" viewBox="0 0 728 150"><g id="zoom" transform="">
<text x="364" y="100" font-family="Fruktur" font-size="80" text-anchor="middle">Spın̈al Tap</text></g>${inner}</svg></body></html>`;
const shell={tabs:[{title:"zoom"}],active:0,address:pageURL,focused:false,canBack:false,canForward:false,loading:false,scale:1,theme:"light",pages:1,scroll:0,pressed:""};
const scaleAt=(i:number)=>{const f=i/frames;return 1+39*(f<0.5?2*f:2-2*f);};
const zoom=(k:number)=>`translate(364 75) scale(${k.toFixed(4)}) translate(-364 -75)`;
const stats=(xs:number[])=>{const s=[...xs].sort((a,b)=>a-b);const q=(p:number)=>Math.round(s[Math.min(s.length-1,Math.floor(p*s.length))]*100)/100;return {p50:q(0.5),p95:q(0.95),max:q(1),frames:s.length};};
const work=()=>{try{return engine.frameWork(true);}catch{return undefined;}};

async function scriptZoom(){
  const html=svg("");
  const doc=await prepareHTML(engine,pageURL,undefined,html);
  const nodes=(engine.inspect(doc.source,{url:pageURL}) as unknown as {nodes:{id:number;attributes:Record<string,string>}[]}).nodes;
  const node=nodes.find(n=>n.attributes.id==="zoom")!.id;
  const base=doc.request(728,250).options;
  const at=(i:number)=>({...base,shell,checks:false,commands:[{op:"setAttribute",nodeId:node,name:"transform",value:zoom(scaleAt(i))}]});
  engine.compileLayers(doc.source,728,250,at(0));work();
  const times:number[]=[];
  for(let i=1;i<=frames;i++){const t=performance.now();engine.compileLayers(doc.source,728,250,at(i));times.push(performance.now()-t);}
  return {...stats(times),work:work()};
}
async function smilZoom(){
  // The animation is a child of the group it scales (its target is its parent).
  const html=svg("")
    .replace('<g id="zoom" transform="">','<g transform="translate(364 75)"><g id="zoom"><animateTransform attributeName="transform" type="scale" values="1;40;1" dur="2s" repeatCount="indefinite"/><g transform="translate(-364 -75)">').replace("</g>","</g></g></g>");
  const doc=await prepareHTML(engine,pageURL,undefined,html);
  const base=doc.request(728,250).options;
  const at=(ms:number)=>({...base,shell,checks:false,animationTime:Math.round(ms)});
  try{engine.compileLayers(doc.source,728,250,at(0));}catch(error){return {refused:String(error).slice(0,120)};}
  work();
  const times:number[]=[];
  for(let i=1;i<=frames;i++){const t=performance.now();engine.compileLayers(doc.source,728,250,at(i*2000/frames));times.push(performance.now()-t);}
  return {...stats(times),work:work()};
}
console.log(JSON.stringify({engine:engineArg??"wasm",script:await scriptZoom(),animateTransform:await smilZoom()}));
