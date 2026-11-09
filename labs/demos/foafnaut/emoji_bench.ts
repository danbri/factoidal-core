// Cost of emoji (issue 1276): the first frame of showcase-emoji.html and of pages of 1,000
// emoji, and of pages with none, on the Wasm engine (what the Hub runs) or the native library.
//   deno run --no-check --no-config --allow-read --allow-ffi labs/demos/foafnaut/emoji_bench.ts \
//     [--native DYLIB] [--fonts colour|mono]
// `--fonts colour` loads the fonts the Hub's table fetches for each page (the colour slices of
// Noto Color Emoji, and Noto Emoji for U+FE0E); `--fonts mono` loads Noto Emoji alone, as the
// engine did before colour. Times are of `compile` (parse, style, layout, shaping, colour
// glyphs, scene): the first frame of a page, then the same page again (kept layout), in ms.
import {loadHTML} from "./native_html_engine.ts";
import {loadFontFile} from "./native_html_document.ts";
import {fontFilePath} from "./native_html_fonts.ts";

const args=Deno.args,opt=(name:string)=>{const i=args.indexOf(name);return i<0?undefined:args[i+1];};
const native=opt("--native"),mode=opt("--fonts")??"colour";
const fonts=new URL("../../../third_party/fonts/",import.meta.url).pathname;
const pages=new URL("./pages/",import.meta.url).pathname;
// @ts-ignore plain JavaScript module of the Hub
const {fontsFor}=await import("../../../docs/web/hub/foafnaut/font-coverage.mjs");

// 1,000 emoji: ten of each of 100 emoji, and 1,000 emoji of which about 700 differ.
const smileys=[...Array(80).keys()].map(i=>String.fromCodePoint(0x1F600+i));
const animals=[...Array(64).keys()].map(i=>String.fromCodePoint(0x1F400+i));
const food=[...Array(64).keys()].map(i=>String.fromCodePoint(0x1F345+i));
const objects=[...Array(256).keys()].map(i=>String.fromCodePoint(0x1F4A0+i)).filter(c=>c!=="\u{1F4FF}");
const page=(emoji:string[],size=20)=>`<!doctype html><html><head><meta charset="utf-8"><title>emoji</title></head><body style="font-size:${size}px">`+
  Array.from({length:Math.ceil(emoji.length/40)},(_,k)=>`<p style="margin:0">${emoji.slice(40*k,40*k+40).join(" ")}</p>`).join("")+"</body></html>";
const hundred=[...smileys,...animals.slice(0,20)];
const repeated=Array.from({length:1000},(_,i)=>hundred[i%100]);
const distinct=Array.from({length:1000},(_,i)=>[...smileys,...animals,...food,...objects][i%(smileys.length+animals.length+food.length+objects.length)]);
const cases:[string,string][]=[
  ["index.html (no emoji)",await Deno.readTextFile(pages+"index.html")],
  ["showcase.html (no emoji)",await Deno.readTextFile(pages+"showcase.html")],
  ["showcase-emoji.html",await Deno.readTextFile(pages+"showcase-emoji.html")],
  ["1,000 emoji, 100 kinds",page(repeated)],
  ["1,000 emoji, ~460 kinds",page(distinct)],
];

const engine=await loadHTML(native,"bytes");
await loadFontFile(engine,fonts+"noto-sans/NotoSans-Regular.ttf","Noto Sans");
const held=new Set<string>();
const coverage=async(path:string)=>JSON.parse(await Deno.readTextFile(fonts+path.replace("./fonts/","")));
console.log(`engine: ${native??"Wasm"}; fonts: ${mode}`);
for(const [name,html] of cases){
  let loadMs=0,loaded=0,bytes=0;
  const wanted=mode==="mono"?(/[\u{1F000}-\u{1FAFF}☀-➿]/u.test(html)?[{path:"./fonts/noto-emoji/NotoEmoji-Regular.ttf",family:"Noto Emoji"}]:[])
    :await fontsFor(html,coverage);
  for(const font of wanted){
    if(held.has(font.family))continue;
    held.add(font.family);
    const path=fontFilePath(font.path),at=performance.now();
    await loadFontFile(engine,path,font.family,"bytes",true);
    loadMs+=performance.now()-at;loaded++;bytes+=(await Deno.stat(path)).size;
  }
  const options={checks:false,url:"file:///bench.html"};
  let at=performance.now();
  const first=engine.compile(html,1200,900,options);
  const firstMs=performance.now()-at;
  at=performance.now();
  engine.compile(html,1200,900,options);
  const againMs=performance.now()-at;
  // Another width lays out again: words are shaped and colour glyphs drawn already.
  at=performance.now();
  engine.compile(html,1100,900,options);
  const relayoutMs=performance.now()-at;
  console.log(`${name.padEnd(26)} fonts ${String(loaded).padStart(2)} (${(bytes/1e6).toFixed(2)} MB, ${loadMs.toFixed(0)} ms)  first ${firstMs.toFixed(0).padStart(5)} ms  again ${againMs.toFixed(0).padStart(4)} ms  relayout ${relayoutMs.toFixed(0).padStart(5)} ms  primitives ${first.primitiveCount}, data ${first.data.length}`);
}
