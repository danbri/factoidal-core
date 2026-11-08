// Real-site probe for liberal mode (docs/designissues/2026-11-08-liberal-mode-and-console.md).
// For each URL and each mode (strict, liberal) it prepares the page as the native browser
// does (prepareHTML: Lean inspects, this host fetches, Lean lays out and draws one frame)
// and reports whether the page renders, the refusal if not, and what Lean skipped.
// The pages are fetched live; nothing is stored. Page scripts are off, as with --no-scripts.
//
//   deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-net \
//     --allow-ffi --allow-env labs/demos/foafnaut/real_sites_probe.ts \
//     [--engine libweb-render.dylib] [--font FILE | --bitmap-font] [--json] [--frames N] [--modes strict,liberal] [URL...]
// Times: `start` is prepare (fetches included) and the first frame; `frame` is the median of
// N more frames of the same page (a kept layout, as a scroll or repaint is), `relayout` one
// frame at another width (a new layout). A URL may be a file: URL or a path.
import {loadHTML} from "./native_html_engine.ts";
import {loadFontFile,prepareHTML} from "./native_html_document.ts";
import {consoleOf} from "./native_console.ts";

const DEFAULT_SITES=["https://en.wikipedia.org/wiki/FOAF","https://www.gov.uk/","https://www.bbc.co.uk/news"];
const args=[...Deno.args];
let enginePath:string|undefined,font:string|undefined,bitmap=false,json=false,frames=0,modes=["strict","liberal"];
const urls:string[]=[];
while(args.length){
  const arg=args.shift()!;
  if(arg==="--engine")enginePath=args.shift();
  else if(arg==="--font")font=args.shift();
  else if(arg==="--bitmap-font")bitmap=true;
  else if(arg==="--json")json=true;
  else if(arg==="--frames")frames=Number(args.shift());
  else if(arg==="--modes")modes=args.shift()!.split(",");
  else if(arg.startsWith("--"))throw new Error(`Unknown option ${arg}`);
  else urls.push(/^[a-z]+:/.test(arg)?arg:new URL(arg,`file://${Deno.cwd()}/`).href);
}
const lab=new URL("./",import.meta.url);
enginePath??=decodeURIComponent(new URL(".build/web-render/engines/libweb-render.dylib",lab).pathname);
const engine=await loadHTML(enginePath);
if(!bitmap){
  const noto=decodeURIComponent(new URL("../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",lab).pathname);
  await loadFontFile(engine,font??noto,font?"font":"Noto Sans");
}
type Row={url:string;mode:string;renders:boolean;ms:number;frameMs?:number;relayoutMs?:number;refusal?:string;primitives?:number;links?:number;
  skips?:{feature?:string;where?:string;action?:string;message:string}[];fetchFailures?:number};
const rows:Row[]=[];
for(const url of urls.length?urls:DEFAULT_SITES){
  for(const mode of modes){
    const start=performance.now();
    const row:Row={url,mode,renders:false,ms:0};
    try{
      const page=await prepareHTML(engine,url,AbortSignal.timeout(60000),undefined,{liberal:mode==="liberal"});
      const frame=await page.compile(1600,1000,{textScalePercent:200});
      row.renders=true;row.primitives=frame.primitiveCount;row.links=frame.webRender.links.length;
      row.ms=Math.round(performance.now()-start);
      if(frames>0){
        const times:number[]=[];
        for(let i=0;i<frames;i++){const t=performance.now();await page.compile(1600,1000,{textScalePercent:200});times.push(performance.now()-t);}
        times.sort((a,b)=>a-b);row.frameMs=Math.round(times[Math.floor(times.length/2)]*10)/10;
        const t=performance.now();await page.compile(1500,1000,{textScalePercent:200});row.relayoutMs=Math.round((performance.now()-t)*10)/10;
      }
      const entries=consoleOf(page).filter(e=>e.source==="System");
      row.skips=entries.filter(e=>e.feature!=="image"&&e.feature!=="tab icon").map(({feature,where,action,message})=>({feature,where,action,message}));
      row.fetchFailures=entries.length-row.skips.length;
    }catch(error){row.refusal=String(error instanceof Error?error.message:error);}
    if(!row.renders)row.ms=Math.round(performance.now()-start);
    rows.push(row);
    if(json)console.log(JSON.stringify(row));
  }
}
if(!json){
  for(const row of rows){
    console.log(`${row.mode.padEnd(8)} ${row.url}`);
    if(!row.renders){console.log(`  REFUSED (${row.ms} ms): ${row.refusal}`);continue;}
    console.log(`  renders (start ${row.ms} ms${row.frameMs!==undefined?`, frame ${row.frameMs} ms, relayout ${row.relayoutMs} ms`:""}): ${row.primitives} paint items, ${row.links} links, ${row.skips!.length} skips, ${row.fetchFailures} image or icon fetches failed`);
    const counts=new Map<string,number>();
    for(const skip of row.skips!)counts.set(`${skip.feature}: ${skip.action}`,(counts.get(`${skip.feature}: ${skip.action}`)??0)+1);
    for(const [what,n] of counts)console.log(`    ${n} x ${what}`);
  }
}
