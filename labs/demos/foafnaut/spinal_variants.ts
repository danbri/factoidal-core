// Variants of the Spinal Tap page (pages/spinal-tap-sparql.html, our own demo page; its data is
// the CC0 Wikidata snapshot in third_party/data/wikidata-spinal-tap) that take it apart one
// feature at a time, down to an empty page (core issue 450). Each variant is made here, at test
// time, from the page in the repository: none is committed. spinal_bisect.ts measures them.
//
// Most variants start from the page's DOM as its scripts leave it after load ("static"): the
// page is run once on the engine with one more script that writes the DOM to the console, and
// that DOM, with its scripts taken out, is the starting point. Each variant then removes or adds
// one thing, and names the variant it is compared with, so that the difference between the two
// is the cost of that one feature.
//
//   deno run -A --unstable-ffi spinal_variants.ts [--engine LIB] [--out DIR] [--only a,b]
import {dirname,join,relative,resolve} from "node:path";
import {fileURLToPath} from "node:url";
import {loadHTML} from "./native_html_engine.ts";
import {prepareHTML,setScriptHost} from "./native_html_document.ts";

const here=dirname(fileURLToPath(import.meta.url));
export const root=resolve(here,"../../..");
export const PAGE="labs/demos/foafnaut/pages/spinal-tap-sparql.html";
export const defaultOut=join(here,".build/spinal-bisect/variants");
export const defaultLibrary=Deno.env.get("WEB_RENDER_DYLIB")??join(here,".build/web-render/engines/libweb-render"+(Deno.build.os==="darwin"?".dylib":".so"));
const FONT="third_party/fonts/noto-sans-math/NotoSansMath-Regular.ttf";

/** One variant: how it is made, and the variant it is compared with. `adds` is true when the
variant adds the feature to its base (its cost is variant minus base); else it takes the feature
away (the cost is base minus variant). */
export type Variant={name:string;feature:string;base?:string;adds?:boolean;from:"page"|"static"|"none";make:(html:string)=>string};

// ---- Small helpers on the page text. Each one checks that it changed something, so that a
// change to the page that breaks a variant fails loudly instead of measuring the same page twice.
const must=(name:string,before:string,after:string)=>{if(before===after)throw new Error(`variant ${name}: the edit changed nothing`);return after;};
const replace=(name:string,html:string,from:string|RegExp,to:string)=>must(name,html,html.replace(from,to));
const replaceAll=(name:string,html:string,from:RegExp,to:string)=>must(name,html,html.replace(from,to));
const addStyle=(name:string,html:string,css:string)=>replace(name,html,"</style>",css+"\n</style>");
const addBody=(name:string,html:string,markup:string)=>replace(name,html,/<\/main>/,markup+"</main>");
const dropScripts=(html:string)=>html.replace(/<script\b[^>]*>[\s\S]*?<\/script>/g,"");
const dropSmil=(html:string)=>html.replace(/<animate(Transform)?\b[^>]*?(\/>|><\/animate(Transform)?>)/g,"");
const dropSvg=(html:string)=>html.replace(/<svg\b[\s\S]*?<\/svg>/g,"");
const VOID=new Set(["area","base","br","col","embed","hr","img","input","link","meta","source","track","wbr"]);

/** The children of <main> as source ranges (the serialised DOM is well formed). */
function mainChildren(html:string):{start:number;end:number}[] {
  const open=html.indexOf("<main"),start=html.indexOf(">",open)+1,stop=html.lastIndexOf("</main>");
  const out:{start:number;end:number}[]=[];
  const tag=/<(\/?)([a-zA-Z][a-zA-Z0-9-]*)\b[^>]*?(\/?)>|<!--[\s\S]*?-->/g;
  tag.lastIndex=start;let depth=0,from=start,m:RegExpExecArray|null;
  while((m=tag.exec(html))&&m.index<stop){
    if(!m[2])continue;
    const name=m[2].toLowerCase(),closing=m[1]==="/",self=m[3]==="/"||VOID.has(name);
    if(!closing&&(name==="script"||name==="style"||name==="textarea")){
      const end=html.indexOf(`</${name}>`,tag.lastIndex);tag.lastIndex=end+name.length+3;
      if(depth===0){out.push({start:from,end:tag.lastIndex});from=tag.lastIndex;}
      continue;
    }
    if(closing)depth--;else if(!self)depth++;
    if(depth===0){out.push({start:from,end:tag.lastIndex});from=tag.lastIndex;}
  }
  return out;
}
/** The page with only the first `fraction` of <main>'s children, by bytes. */
function keepFraction(name:string,html:string,fraction:number):string {
  const kids=mainChildren(html);if(kids.length<2)throw new Error(`variant ${name}: <main> has no children to drop`);
  const total=kids.at(-1)!.end-kids[0].start;let cut=kids.length;
  while(cut>1&&kids[cut-1].end-kids[0].start>total*fraction)cut--;
  return html.slice(0,kids[cut-1].end)+html.slice(kids.at(-1)!.end);
}
/** Plain words of the page's own text, for a page of the same size with nothing but text. */
function words(html:string):string[] {
  return dropSvg(dropScripts(html)).replace(/<style[\s\S]*?<\/style>/g,"").replace(/<[^>]*>/g," ").replace(/&[a-z]+;/g," ")
    .split(/\s+/).filter(w=>/^[A-Za-z][A-Za-z,.]*$/.test(w));
}

export const VARIANTS:Variant[]=[
  {name:"full",feature:"the page as it is",from:"page",make:h=>h},
  {name:"no-zoom",feature:"the zoom animation (SMIL scale 1 to 40 and a cross-fade, 8.4 s)",base:"full",from:"page",
    make:h=>replace("no-zoom",h,"else if (!slowZoom) setTimeout(startZoom, 600);","")},
  {name:"zoom-held",feature:"the zoomed SVG text held at scale 40 (no animation) instead of scale 1",base:"no-zoom",adds:true,from:"page",
    make:h=>replace("zoom-held",h,"else if (!slowZoom) setTimeout(startZoom, 600);","holdAt(3500);")},
  {name:"more-cards",feature:"the film query's 23 cards instead of the band's one (a bigger DOM, scripts on)",base:"no-zoom",adds:true,from:"page",
    make:h=>replace("more-cards",replace("more-cards",h,"else if (!slowZoom) setTimeout(startZoom, 600);",""),
      "choose((queries.find(q => '#' + q.id === location.hash) || queries[0]).id);","choose('film');")},
  {name:"static",feature:"page scripts (BubblePopJS start: the cards built in one batch, timers)",base:"no-zoom",from:"static",make:h=>h},
  {name:"no-clip",feature:"overflow:clip on the zoom stage",base:"static",from:"static",make:h=>replace("no-clip",h,' style="overflow:clip"',"")},
  {name:"no-web-font",feature:"the web font (Noto Sans Math, 657 KB, @font-face)",base:"static",from:"static",
    make:h=>replace("no-web-font",h,/@font-face\s*\{[\s\S]*?\}/,"")},
  {name:"latin-text",feature:"Fraktur letters with combining marks (math font) instead of plain Latin in the same SVG text",base:"no-web-font",from:"static",
    make:h=>replaceAll("latin-text",replace("latin-text",h,/@font-face\s*\{[\s\S]*?\}/,""),/(\u{1D504}|\u{1D505}|[\u{1D506}-\u{1D537}]|\u0308|\u0131)/gu,"x")},
  {name:"no-stroke",feature:"strokes on SVG text (wordmark outline uses, stage text)",base:"static",from:"static",
    make:h=>replaceAll("no-stroke",replaceAll("no-stroke",h,/<use\b[^>]*fill="none"[^>]*>(<\/use>)?/g,""),/ stroke="#ff[0-9a-f]{4}" stroke-width="1\.2"/g,"")},
  {name:"no-gradient",feature:"SVG linear gradients (wordmark chrome and flame)",base:"static",from:"static",
    make:h=>replaceAll("no-gradient",h,/url\(#(chrome|flame)\)/g,"#cfd6df")},
  {name:"no-wordmark",feature:"the wordmark SVG (one 150 px text, used three times)",base:"static",from:"static",
    make:h=>replace("no-wordmark",h,/<div class="mark"[\s\S]*?<\/div>/,"")},
  {name:"no-stage",feature:"the zoom stage SVG (80 px stroked text, two texts)",base:"static",from:"static",
    make:h=>replace("no-stage",h,/<svg id="zoomsvg"[\s\S]*?<\/svg>/,"")},
  {name:"no-svg",feature:"all inline SVG",base:"static",from:"static",make:h=>must("no-svg",h,dropSvg(h))},
  {name:"no-borders",feature:"CSS borders and backgrounds",base:"no-svg",from:"static",
    make:h=>replaceAll("no-borders",dropSvg(h),/(border(-[a-z]+)?|background):[^;}]*;?/g,"")},
  {name:"half",feature:"the second half of the DOM (by bytes of <main>'s children)",base:"static",from:"static",make:h=>keepFraction("half",h,0.5)},
  {name:"quarter",feature:"the second quarter of the DOM",base:"half",from:"static",make:h=>keepFraction("quarter",h,0.25)},
  {name:"text-only",feature:"CSS (the style sheet and classes) on the page's text with no SVG",base:"no-svg",from:"static",
    make:h=>dropSvg(h).replace(/<style[\s\S]*?<\/style>/g,"").replace(/ (class|style)="[^"]*"/g,"")},
  {name:"plain-text",feature:"markup: text-only's elements against one <pre> of the same bytes",base:"text-only",from:"none",
    make:h=>{const w=words(h),size=new TextEncoder().encode(h).length;let s="";for(let i=0;s.length<size-120;i++)s+=w[i%w.length]+(i%12===11?"\n":" ");
      return `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>plain</title></head><body><pre>${s}</pre></body></html>`;}},
  {name:"empty",feature:"an empty page against plain text of the page's size",base:"plain-text",from:"none",
    make:()=>`<!doctype html><html lang="en"><head><meta charset="utf-8"><title>empty</title></head><body></body></html>`},
  {name:"plus-shadow",feature:"box-shadow and border-radius on the cards, stage and buttons",base:"static",adds:true,from:"static",
    make:h=>addStyle("plus-shadow",h,".card,.stage,.picker,button,pre{border-radius:8px;box-shadow:0 4px 14px rgba(0,0,0,.6),0 0 0 1px rgba(226,184,90,.25)}")},
  {name:"plus-fixed",feature:"a position:fixed bar and a position:sticky picker",base:"static",adds:true,from:"static",
    make:h=>addBody("plus-fixed",addStyle("plus-fixed",h,".fixedbar{position:fixed;top:0;left:0;right:0;height:28px;background:#1b1b22;color:#e2b85a;border-bottom:1px solid #4a4a55}.picker{position:sticky;top:28px}"),
      '<div class="fixedbar">fixed bar</div>')},
  {name:"plus-css-anim",feature:"an infinite CSS animation (a 24 px spinner) and transitions on buttons",base:"static",adds:true,from:"static",
    make:h=>addBody("plus-css-anim",addStyle("plus-css-anim",h,"@keyframes spin{from{transform:rotate(0deg)}to{transform:rotate(360deg)}}.spin{width:24px;height:24px;border:3px solid #e2b85a;border-right-color:transparent;animation:spin 1s linear infinite}button{transition:background-color .3s,color .3s}"),
      '<div class="spin"></div>')},
  {name:"plus-effects",feature:"opacity, a transform and a blur filter on every card",base:"static",adds:true,from:"static",
    make:h=>addStyle("plus-effects",h,".card,.stage,pre{opacity:.94;transform:rotate(.4deg);filter:blur(.4px)}")},
  {name:"plus-timer",feature:"a 16 ms setInterval that changes one text node (DOM churn, no layout change of size)",base:"static",adds:true,from:"static",
    make:h=>addBody("plus-timer",h,'<p id="tick">0</p><script>let n=0;const t=document.getElementById("tick").firstChild;setInterval(()=>{t.nodeValue=String(++n%10)},16);</script>')},
  {name:"plus-images",feature:"eight <img> elements (SVG data: URLs, 160 by 90)",base:"static",adds:true,from:"static",
    make:h=>{const svg=encodeURIComponent('<svg xmlns="http://www.w3.org/2000/svg" width="160" height="90"><rect width="160" height="90" fill="#1b1b22"/><circle cx="80" cy="45" r="30" fill="#e2b85a"/></svg>');
      return addBody("plus-images",h,"<p>"+Array.from({length:8},()=>`<img width="160" height="90" alt="" src="data:image/svg+xml,${svg}">`).join(" ")+"</p>");}},
];

/** The page's DOM after load, with its scripts and SMIL elements removed: run the page on the
engine with one script more, which writes document.documentElement.outerHTML to the console. */
export async function captureStatic(library:string,pageHTML:string,baseURL:string):Promise<string> {
  const engine=await loadHTML(library) as unknown as {scriptSession:(s:string,r:Record<string,unknown>)=>{logs:string[];errors:string[]}};
  const logs:string[]=[],errors:string[]=[];
  setScriptHost({start:(source:string,u:string,resources:unknown,encoding?:string,mode?:Record<string,unknown>)=>{
    const t=engine.scriptSession(source,{action:"start",url:u,resources,width:1280,height:800,zoomUnit:100,
      layout:{url:u,textScalePercent:100,zoomUnit:100,...(mode??{})},engine:"bubblepop",...(encoding?{encoding}:{})});
    logs.push(...t.logs);errors.push(...t.errors);return t;
  }} as never);
  // A console line has a size limit: the DOM goes out in pieces.
  const probe='<script>{const h=document.documentElement.outerHTML;for(let i=0;i<h.length;i+=2000)console.log("\\u0002DOM"+h.slice(i,i+2000));}</script>';
  const html=replace("capture",pageHTML,/<\/main><\/body><\/html>\s*$/,probe+"</main></body></html>");
  try{await prepareHTML(engine as never,baseURL,undefined,html,{liberal:true});}finally{setScriptHost(undefined);}
  if(errors.length)throw new Error(`capture: page script errors: ${errors[0].slice(0,200)}`);
  const dom=logs.filter(l=>l.startsWith("\u0002DOM")).map(l=>l.slice(4)).join("");
  if(!dom.startsWith("<html"))throw new Error(`capture: no DOM from the page (${logs.length} console lines)`);
  return "<!doctype html>\n"+dropSmil(dropScripts(dom));
}

/** Write every variant (or `only`) to `out`, with the web font's URL made relative to it. */
export async function generate({library=defaultLibrary,out=defaultOut,only}:{library?:string;out?:string;only?:string[]}={}) {
  const page=Deno.readTextFileSync(join(root,PAGE));
  const fontURL=relative(out,join(root,FONT));
  const fixFont=(h:string)=>h.replace(/src:url\('\.\.\/fonts\/noto-sans-math\/NotoSansMath-Regular\.ttf'\) format\('truetype'\),\s*url\('[^']*'\) format\('truetype'\)/,
    `src:url('${fontURL}') format('truetype')`);
  if(fixFont(page)===page)throw new Error("generate: the page's @font-face is not as expected");
  const wanted=only?VARIANTS.filter(v=>only.includes(v.name)||VARIANTS.some(w=>only.includes(w.name)&&w.base===v.name)):VARIANTS;
  const needStatic=wanted.some(v=>v.from==="static"||v.from==="none");
  const staticDOM=needStatic?await captureStatic(library,page,"file://"+join(root,PAGE)):"";
  Deno.mkdirSync(out,{recursive:true});
  const made:Record<string,{file:string;bytes:number;feature:string;base?:string;adds?:boolean}>={};
  const textOnly=VARIANTS.find(v=>v.name==="text-only")!.make(staticDOM);
  for(const v of wanted){
    const src=v.from==="page"?page:v.from==="static"?staticDOM:v.name==="plain-text"?textOnly:"";
    const html=fixFont(v.make(src));
    const file=join(out,v.name+".html");
    Deno.writeTextFileSync(file,html);
    made[v.name]={file,bytes:new TextEncoder().encode(html).length,feature:v.feature,...(v.base?{base:v.base}:{}),...(v.adds?{adds:true}:{})};
  }
  Deno.writeTextFileSync(join(out,"manifest.json"),JSON.stringify(made,null,1)+"\n");
  return made;
}

if(import.meta.main){
  const args=Deno.args,opt=(n:string)=>{const i=args.indexOf(n);return i>=0?args[i+1]:undefined;};
  const made=await generate({library:opt("--engine")??defaultLibrary,out:opt("--out")??defaultOut,only:opt("--only")?.split(",")});
  for(const [name,v] of Object.entries(made))console.log(`${name.padEnd(14)} ${String(v.bytes).padStart(7)} bytes  ${v.feature}`);
}
