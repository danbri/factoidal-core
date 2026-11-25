// First layout and frame build of a real-page snapshot on the native engine, for the thread
// comparison of issue 1031 (FOAFNAUT_LEAN_THREADS=0 against the default pool; the switch is in
// web_render_shim.c). One page and one run per process, so every run starts with a fresh engine.
//
//   REALPAGES_REPLAY=SNAPSHOT.zip FOAFNAUT_LEAN_THREADS=0 deno run -A --unstable-ffi \
//     --preload realpages/replay.ts realpages/engine_par_bench.ts --engine LIB --url URL [--again N]
//
// The page is read as the window reads it with --no-scripts (prepareHTML in liberal mode: sheets,
// web fonts, images waited for; no scripts), with Noto Sans loaded first. Then one compile at 1280x800 (first layout and frame
// build, `firstMs`), then N compiles at widths 1281 and 1280 in turn (each a new layout and frame,
// `againMs`). `hash` is the SHA-256 of the first frame's scene words, tiles and shader text: two
// runs with the same hash drew the same scene. One JSON line on standard output.
import {loadHTML} from "../native_html_engine.ts";
import {prepareHTML,loadFontFile} from "../native_html_document.ts";

const argv=Deno.args;
const opt=(name:string,fallback?:string)=>{const i=argv.indexOf(name);return i>=0?argv[i+1]:fallback;};
const url=opt("--url");
if(!url)throw new Error("--url is required");
const again=Number(opt("--again","4"));
const engine=await loadHTML(opt("--engine"));
await loadFontFile(engine,new URL("../../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf",import.meta.url).pathname,"Noto Sans");
const t0=performance.now();
const page=await prepareHTML(engine,url,undefined,undefined,{liberal:true});
const prepareMs=performance.now()-t0;
const t1=performance.now();
const first=await Promise.resolve(page.compile(1280,800,{checks:false} as never));
const firstMs=performance.now()-t1;
const againMs:number[]=[];
for(let i=0;i<again;i++){
  const t=performance.now();
  await Promise.resolve(page.compile(i%2===0?1281:1280,800,{checks:false} as never));
  againMs.push(performance.now()-t);
}
const parts=[new Uint8Array(Float32Array.from(first.data as ArrayLike<number>).buffer),
  new Uint8Array(Uint32Array.from(first.tiles as ArrayLike<number>).buffer),new TextEncoder().encode(first.wgsl)];
const all=new Uint8Array(parts.reduce((n,p)=>n+p.length,0));
let at=0;for(const p of parts){all.set(p,at);at+=p.length;}
const hash=[...new Uint8Array(await crypto.subtle.digest("SHA-256",all))].map(b=>b.toString(16).padStart(2,"0")).join("");
console.log(JSON.stringify({url,threads:Deno.env.get("FOAFNAUT_LEAN_THREADS")??"pool",prepareMs:Math.round(prepareMs),
  firstMs:Math.round(firstMs*10)/10,againMs:againMs.map(x=>Math.round(x*10)/10),primitives:first.primitiveCount,hash}));
