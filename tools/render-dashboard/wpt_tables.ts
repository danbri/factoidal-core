// WPT css/css-tables reftests through the browser's own document path, with
// pixels from the real GPU. For each reftest the test and its reference are
// rendered by the same engine at the same size (WPT's 800x600), drawn by Lean's
// render plan, read back, and compared pixel by pixel. rel=mismatch inverts the
// verdict. WPT's fuzzy meta is used when the test has one.
//
// The tests come from third_party/testing/wpt-css-tables (a copy of WPT, unchanged)
// and the list of tests and kinds from wpt-tables-classes.json, which
// wpt_tables_classify.py writes. The vendored tree is served over HTTP on
// 127.0.0.1 so that WPT's root-relative links (/fonts/ahem.css,
// /css/reference/...) resolve as they do in WPT.
//
// usage:
//   deno run --no-check --unstable-webgpu --unstable-ffi --allow-read --allow-write \
//     --allow-net=127.0.0.1 --allow-ffi tools/render-dashboard/wpt_tables.ts \
//     [--output FILE] [--native-engine DYLIB] [--width 800] [--height 600]
//     [--only REGEX] [--limit N] [--font noto|bitmap] [--recycle N] [--images DIR]
//     [--root DIR] [--classes FILE] [--answers bytes|text]
//
// --answers text takes Lean's JSON text answers (Base64 floats) instead of the bytes
// answer; engines built before web_document_call_bin need it.
//
// Status of a test, one of:
//   pass      the relation holds (match: equal within fuzzy; mismatch: not equal)
//   fail      the relation does not hold; differentPixels and maxDifference say by how much
//   refused   the test or its reference was refused. source "lean" is the Lean engine's
//             error text, which names the missing feature; source "host" is the host's
//             own refusal before Lean lays out (scripts, resource limits)
//   error     anything else: the engine aborted, a resource did not load, the GPU draw or
//             readback failed, or Lean's own pixel checks on the read back frame did not hold
//   not-run   not a screen reftest (testharness, crashtest, print), or no GPU; the reason says
// A pass where both images are one flat colour is counted apart as uniformPass: such a
// pass says little (a test whose content is all dropped can still equal a blank reference).
// Shared references with a known picture (css/reference/ref-filled-green-*) are checked
// for their green square: referenceControl "broken" means the engine did not draw the
// reference as WPT means it, and a pass against it is counted apart as well.
//
// Not done: reference chains (a reference with its own reference; none in this pin),
// fuzzy meta on references, reftest-wait (scripts are refused), and a time limit per
// render (the Lean call is synchronous; run.py's whole-run timeout is the guard).
import {loadHTML,type HTMLEngine,type HTMLArtifact} from "../../labs/demos/foafnaut/native_html_engine.ts";
import {prepareHTML,loadFontFile} from "../../labs/demos/foafnaut/native_html_document.ts";
import {createLayerRenderer} from "../../labs/demos/foafnaut/layer_compositor.ts";
import {encodePPM} from "../../labs/demos/foafnaut/gpu_transport.ts";

type Reference={relation:"match"|"mismatch";href:string;path:string|null;missing?:boolean};
type Row={test:string;kind:string;tentative:boolean;references?:Reference[];
  fuzzy?:{reference:string|null;value:[[number,number],[number,number]]}|null;features?:string[];tier?:string};
type Side={status:"rendered"|"refused"|"error";source?:"lean"|"host";reason?:string;ms:number;pixels?:Uint8Array;primitives?:number};
type Case={test:string;kind:string;tentative:boolean;tier?:string;status:string;reason?:string;source?:"lean"|"host";
  refusedSide?:"test"|"reference";reference?:string;relation?:string;font?:string;
  differentPixels?:number;maxDifference?:number;referenceControl?:"ok"|"broken";fuzzy?:[[number,number],[number,number]];uniformPass?:boolean;
  primitives?:{test?:number;reference?:number};ms?:number};

const here=new URL(".",import.meta.url);
const args=[...Deno.args];
let output:string|undefined,nativeEngine:string|undefined,width=800,height=600,only:RegExp|undefined,limit=Infinity;
let font:"noto"|"bitmap"="noto",recycle=10,images:string|undefined,answers:"bytes"|"text"="bytes";
let root=new URL("../../third_party/testing/wpt-css-tables/",here).pathname,classes=new URL("wpt-tables-classes.json",here).pathname;
while(args.length){
  const arg=args.shift()!,value=()=>{const v=args.shift();if(v===undefined)throw new Error(`${arg} needs a value`);return v;};
  if(arg==="--output")output=value();
  else if(arg==="--native-engine")nativeEngine=value();
  else if(arg==="--width")width=Number(value());
  else if(arg==="--height")height=Number(value());
  else if(arg==="--only")only=new RegExp(value());
  else if(arg==="--limit")limit=Number(value());
  else if(arg==="--font"){const v=value();if(v!=="noto"&&v!=="bitmap")throw new Error("--font is noto or bitmap");font=v;}
  else if(arg==="--recycle")recycle=Number(value());
  else if(arg==="--images")images=value();
  else if(arg==="--root")root=value();
  else if(arg==="--classes")classes=value();
  else if(arg==="--answers"){const v=value();if(v!=="bytes"&&v!=="text")throw new Error("--answers is bytes or text");answers=v;}
  else throw new Error(`unknown argument ${arg}`);
}
if(!root.endsWith("/"))root+="/";
if(![width,height].every(n=>Number.isInteger(n)&&n>0&&n<=4096))throw new Error("--width and --height are 1..4096");
const NOTO=new URL("../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",here).pathname;
const AHEM=root+"fonts/Ahem.ttf";

const sha256=async(bytes:Uint8Array<ArrayBuffer>)=>[...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes))].map(b=>b.toString(16).padStart(2,"0")).join("");
const listing=JSON.parse(await Deno.readTextFile(classes)) as {tests:Row[]};
const rows=listing.tests.filter(row=>!only||only.test(row.test));

// The vendored tree over HTTP, read only, nothing outside it.
const TYPES:Record<string,string>={html:"text/html; charset=utf-8",htm:"text/html; charset=utf-8",xht:"application/xhtml+xml",xhtml:"application/xhtml+xml",
  css:"text/css",js:"text/javascript",svg:"image/svg+xml",png:"image/png",ico:"image/x-icon",ttf:"font/ttf",json:"application/json",md:"text/markdown"};
const server=Deno.serve({hostname:"127.0.0.1",port:0,onListen:()=>{}},async request=>{
  const path=decodeURIComponent(new URL(request.url).pathname);
  if(request.method!=="GET"||path.split("/").some(part=>part===".."||part.includes("\0")))return new Response("forbidden",{status:403});
  try{
    const bytes=await Deno.readFile(root+path.replace(/^\/+/,""));
    return new Response(bytes,{headers:{"content-type":TYPES[path.split(".").pop()!.toLowerCase()]??"application/octet-stream"}});
  }catch{return new Response("not found",{status:404});}
});
const origin=`http://127.0.0.1:${server.addr.port}/`;

// Engines. Lean holds one font per engine and uses it for all text, so tests that
// use Ahem get an engine with Ahem, the others an engine with Noto Sans (or the
// Lean bitmap face with --font bitmap). Both sides of a test use the same engine.
// A new engine every `recycle` renders: one engine runs out of memory on a long set
// (the known render leak, see old_web.ts).
type Slot={engine:HTMLEngine;uses:number;via:string};
const slots=new Map<string,Slot>();
async function engineFor(face:"ahem"|"noto"|"bitmap"):Promise<Slot> {
  let slot=slots.get(face);
  if(slot&&slot.uses<recycle)return slot;
  const engine=await loadHTML(nativeEngine,answers);
  let via="none";
  if(face!=="bitmap"){
    const path=face==="ahem"?AHEM:NOTO,family=face==="ahem"?"Ahem":"Noto Sans";
    // The bytes call is newer than some built engines; the Base64 call is the same font.
    // An engine older than both draws in the Lean bitmap face; via says why.
    try{await loadFontFile(engine,path,family,"bytes");via="bytes";}
    catch{
      try{await loadFontFile(engine,path,family,"text");via="text";}
      catch(error){via="unavailable: "+String((error as Error)?.message??error).slice(0,200);}
    }
  }
  slot={engine,uses:0,via};slots.set(face,slot);return slot;
}

const adapter=await navigator.gpu?.requestAdapter();
const device=adapter?await adapter.requestDevice():undefined;
const renderer=device?createLayerRenderer(device,"rgba8unorm"):undefined;
const target=device?.createTexture({size:[width,height],format:"rgba8unorm",usage:GPUTextureUsage.RENDER_ATTACHMENT|GPUTextureUsage.COPY_SRC});

async function side(slot:Slot,path:string):Promise<Side> {
  const start=performance.now();
  let frame:HTMLArtifact;
  try{
    slot.uses++;
    // compile is synchronous on the engine; await also takes a worker engine.
    frame=await (await prepareHTML(slot.engine,origin+path)).compile(width,height);
  }catch(error){
    const text=String((error as Error)?.message??error),ms=Math.round(performance.now()-start);
    // Lean's errors name a missing feature. The host refuses some pages before Lean
    // lays out (prepareHTML: scripts, resource limits). Anything else is an error.
    if(text.startsWith("Lean HTML: "))return {status:"refused",source:"lean",reason:text.slice(11).slice(0,400),ms};
    if(/^Native HTML (milestone|exceeds|stylesheets|resource exceeds)/.test(text))return {status:"refused",source:"host",reason:text.slice(0,400),ms};
    return {status:"error",reason:text.slice(0,400),ms};
  }
  // Lean's own probes are checked on the read back pixels (checkPixels in drawSingle).
  const drawn=await renderer!.drawSingle(frame,target!,true);
  return {status:"rendered",ms:Math.round(performance.now()-start),pixels:drawn.pixels!.slice(),primitives:frame.primitiveCount};
}

function compare(a:Uint8Array,b:Uint8Array) {
  let different=0,maximum=0;
  for(let i=0;i<a.length;i+=4){
    let d=0;for(let c=0;c<4;c++)d=Math.max(d,Math.abs(a[i+c]-b[i+c]));
    if(d){different++;if(d>maximum)maximum=d;}
  }
  return {different,maximum};
}
// Shared references whose picture is known: the side of their green (0,128,0) square.
// A square at a fractional position blends its edge rows, so the check asks for the
// inside of the square (side-2 squared) within 8 of the colour.
const KNOWN_GREEN:Record<string,number>={"css/reference/ref-filled-green-100px-square.xht":100,
  "css/reference/ref-filled-green-100px-square-only.html":100,"css/reference/ref-filled-green-200px-square.html":200};
const green=(p:Uint8Array)=>{let n=0;for(let i=0;i<p.length;i+=4)if(p[i]<=8&&Math.abs(p[i+1]-128)<=8&&p[i+2]<=8)n++;return n;};
const uniform=(p:Uint8Array)=>{const w=new Uint32Array(p.buffer,p.byteOffset,p.byteLength>>>2);return w.every(x=>x===w[0]);};
// WPT: equal when nothing differs, or when both counts are inside the fuzzy ranges.
const withinFuzzy=(d:{different:number;maximum:number},f?:[[number,number],[number,number]])=>
  d.different===0||(!!f&&f[0][0]<=d.maximum&&d.maximum<=f[0][1]&&f[1][0]<=d.different&&d.different<=f[1][1]);

const NOT_RUN:Record<string,string>={testharness:"testharness.js test: needs script execution",
  crashtest:"crashtest: not scored by this runner","print-reftest":"print reftest: paged media is not in this runner",
  manual:"manual test",other:"not a reftest"};
const cases:Case[]=[];
let rendered=0;
for(const row of rows){
  const item:Case={test:row.test,kind:row.kind,tentative:row.tentative,...(row.tier?{tier:row.tier}:{}),status:"not-run"};
  cases.push(item);
  if(row.kind!=="reftest"){item.reason=NOT_RUN[row.kind]??"not a reftest";continue;}
  if(rendered>=limit){item.reason="over --limit";continue;}
  if(!renderer){item.reason="no WebGPU adapter";continue;}
  const refs=(row.references??[]).filter(r=>r.path&&!r.missing);
  if(!refs.length){item.reason="reference not in the vendored tree";continue;}
  rendered++;
  const face=row.features?.includes("ahem")?"ahem":font;
  item.font=face;
  try{
    const slot=await engineFor(face);
    if(slot.via.startsWith("unavailable")){
      // Ahem tests measure Ahem boxes; in another face they say nothing.
      if(face==="ahem"){item.reason="engine can not load Ahem: "+slot.via.slice(13);rendered--;continue;}
      item.font="bitmap (Noto Sans not loaded: "+slot.via.slice(13)+")";
    }
    const test=await side(slot,row.test);
    item.primitives={test:test.primitives};
    if(test.status!=="rendered"){Object.assign(item,{status:test.status,source:test.source,reason:test.reason,refusedSide:"test",ms:test.ms});continue;}
    // More than one reference: WPT passes the test if it holds against any of them.
    let best:Case|undefined;
    for(const ref of refs){
      const other=await side(slot,ref.path!);
      const result:Case={...item,reference:ref.path!,relation:ref.relation,ms:test.ms+other.ms,primitives:{test:test.primitives,reference:other.primitives}};
      if(other.status!=="rendered"){Object.assign(result,{status:other.status,source:other.source,reason:other.reason,refusedSide:"reference"});}
      else{
        const fuzzy=row.fuzzy&&(!row.fuzzy.reference||ref.path!.endsWith(row.fuzzy.reference.replace(/^.*\//,"")))?row.fuzzy.value:undefined;
        const d=compare(test.pixels!,other.pixels!),equal=withinFuzzy(d,fuzzy);
        const holds=ref.relation==="match"?equal:!equal;
        Object.assign(result,{status:holds?"pass":"fail",differentPixels:d.different,maxDifference:d.maximum,...(fuzzy?{fuzzy}:{})});
        if(holds&&uniform(test.pixels!)&&uniform(other.pixels!))result.uniformPass=true;
        const known=KNOWN_GREEN[ref.path!];
        if(known)result.referenceControl=green(other.pixels!)>=(known-2)**2?"ok":"broken";
        if(images&&!holds){
          const stem=row.test.replace(/[^\w.-]+/g,"_");
          await Deno.mkdir(images,{recursive:true});
          await Deno.writeFile(`${images}/${stem}.test.ppm`,encodePPM(test.pixels!,width,height));
          await Deno.writeFile(`${images}/${stem}.ref.ppm`,encodePPM(other.pixels!,width,height));
        }
      }
      if(!best||result.status==="pass"||(best.status!=="pass"&&result.status==="fail"))best=result;
      if(best.status==="pass")break;
    }
    Object.assign(item,best);
  }catch(error){
    Object.assign(item,{status:"error",reason:String((error as Error)?.message??error).slice(0,400)});
  }
}
await server.shutdown();
target?.destroy();renderer?.dispose();

const counts:Record<string,number>={};
for(const c of cases)counts[c.status]=(counts[c.status]??0)+1;
const reftests=cases.filter(c=>c.kind==="reftest");
const reftestCounts:Record<string,number>={pass:0,fail:0,refused:0,error:0,"not-run":0};
for(const c of reftests)reftestCounts[c.status]=(reftestCounts[c.status]??0)+1;
const uniformPasses=reftests.filter(c=>c.uniformPass).length;
const brokenReferencePasses=reftests.filter(c=>c.status==="pass"&&c.referenceControl==="broken").length;
const brokenReferences=[...new Set(reftests.filter(c=>c.referenceControl==="broken").map(c=>c.reference!))].sort();
// Refusals grouped by their text, largest first.
const groups=new Map<string,string[]>();
for(const c of reftests.filter(c=>c.status==="refused"||c.status==="error")){
  const key=`${c.status}${c.source?" ("+c.source+")":""}: ${c.reason}`;groups.set(key,[...(groups.get(key)??[]),c.test]);
}
const refusals=[...groups].sort((a,b)=>b[1].length-a[1].length||a[0].localeCompare(b[0]))
  .map(([reason,tests])=>({reason,count:tests.length,examples:tests.slice(0,3)}));
const engineFile=nativeEngine??new URL("../../labs/demos/foafnaut/.build/native-html/runtime/web-render.wasm",here).pathname;
let engineSha:string|null=null;
try{engineSha=await sha256(await Deno.readFile(engineFile));}catch{/* the report says null */}
const report={format:"factoidal-wpt-tables-v1",runner:"tools/render-dashboard/wpt_tables.ts",
  input:{name:"WPT css/css-tables",root:"third_party/testing/wpt-css-tables",commit:"28c152b74f8679534e558745fe83312c8dcca8c8"},
  engine:{kind:nativeEngine?"native":"wasm",answers,path:engineFile,sha256:engineSha,fontCall:[...new Set([...slots.values()].map(s=>s.via))]},
  gpu:adapter?{vendor:adapter.info.vendor,architecture:adapter.info.architecture,device:adapter.info.device,description:adapter.info.description}:null,width,height,font,
  total:cases.length,counts,reftests:{total:reftests.length,counts:reftestCounts,uniformPasses,brokenReferencePasses,brokenReferences},refusals,cases};
const text=JSON.stringify(report);
if(output)await Deno.writeTextFile(output,text+"\n");else console.log(text);
console.log(`wpt css-tables reftests: ${reftestCounts.pass} pass (${uniformPasses} flat images, ${brokenReferencePasses} against a reference drawn wrong), ${reftestCounts.fail} fail, `+
  `${reftestCounts.refused} refused, ${reftestCounts.error} error, ${reftestCounts["not-run"]} not run (out of ${reftests.length}; ${cases.length} tests in all)`);
device?.destroy();
