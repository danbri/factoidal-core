// The real-page survey's pure parts (realpages/): reading run_html.ts and textnaut output, the
// verdict, the layout similarity of two pictures, the comparison with the previous survey, and
// the System-entry report behind run_html.ts --liberal-report json. The logs here are made up
// for the test (no page content). The survey itself runs live pages: realpages_check.ts and
// factoidal-builds' realpages.yml.
import {strict as assert} from "node:assert";
import {cpuShare,FETCH_FAILURE,overBudget,parseScroll,parseTextnaut,parseWatch,psSeconds,verdictOf} from "./realpages/metrics.ts";
import {crop,decodePNG,ssim} from "./realpages/visual.ts";
import {findings,markdown,trendRows,TREND_COLUMNS,type Summary} from "./realpages/compare.ts";
import {pngOf} from "./png_write.ts";
import {crc32,readZip,writeZip} from "./realpages/zip.ts";
import {addEntries,reportSystemEntries,type ConsoleEntry} from "./native_console.ts";

const frame=(n:number,layoutMs:number,prims:number)=>JSON.stringify({type:"native-html-frame",t:1000+n,frame:n,primitives:prims,layoutMs,totalMs:layoutMs+5,layers:{top:65,bandTop:0}});
const WATCH=[
  "engine: native /x/libweb-render.dylib",
  JSON.stringify({type:"native-html-script",cause:"start",leanMs:120}),
  frame(1,224,2661),frame(2,268,2661),
  JSON.stringify({type:"native-html-presented",url:"https://example.test/",frames:1}),
  JSON.stringify({type:"native-html-script",cause:"timers",leanMs:6202}),
  JSON.stringify({type:"native-html-skip",source:"System",feature:"page scripts",message:"Lean HTML: scriptSession: document HTML exceeds 1MiB"}),
  JSON.stringify({type:"native-html-skip",source:"System",feature:"page scripts",message:"Lean HTML: scriptSession: document HTML exceeds 1MiB"}),
  "page: Uncaught TypeError: x is undefined",
  JSON.stringify({type:"native-html-shot",file:"/tmp/a.png",width:1280,height:800}),
  JSON.stringify({type:"native-html-log-flood",t:9000,lines:60,top:[["scriptSession: no session",60]]}),
  "gpu: 1 in flight, submit to done p50 52 ms, p95 74.3 ms, max in flight 3, 14 submits",
].join("\n");

Deno.test("parseWatch reads frames, GPU, script turns and skips", ()=>{
  const w=parseWatch(WATCH);
  assert.equal(w.first_layout_ms,224);assert.equal(w.prims,2661);assert.equal(w.frames,2);assert.equal(w.chrome_top,65);
  assert.equal(w.gpu_p50_ms,52);assert.equal(w.gpu_p95_ms,74.3);
  assert.equal(w.script_turns,2);assert.equal(w.script_turn_max_ms,6202);assert.equal(w.script_ms_total,6322);
  assert.equal(w.skips.length,1,"a skip seen twice is listed once");assert.equal(w.scripts_off,"document HTML over 1 MiB");
  assert.equal(w.page_errors,1);assert.equal(w.shot,true);
  assert.equal(w.log_floods,1);assert.match(w.log_flood_top!,/scriptSession: no session/);
  const empty=parseWatch("Error: Lean HTML: a bound\n");
  assert.equal(empty.prims,null);assert.equal(empty.gpu_p50_ms,null);assert.equal(empty.script_turn_max_ms,null);assert.equal(empty.shot,false);
});

Deno.test("parseScroll and parseTextnaut", ()=>{
  const s=parseScroll("offscreen input latency: 20 events, p50 554.4 ms, p95 713.8 ms, max 731.2 ms\nframes: 3 presented (0 checked)\nscroll presents with no Lean call: 11, totalMs p50 1.7, p95 80.5, max 80.5\n");
  assert.deepEqual(s,{events:20,latency_p50_ms:554.4,latency_p95_ms:713.8,composite_p50_ms:1.7,composite_p95_ms:80.5,lean_frames:3,ratchet:false});
  assert.equal(parseScroll("Native HTML frame cost ratchet: 4 Lean frames").ratchet,true);
  const t=parseTextnaut("timing: engine native; start 42 ms; load 1796 ms; layout 502 ms; cells 22 ms; rows 99; links 199; scripts bubblepop\n");
  assert.deepEqual(t,{load_ms:1796,layout_ms:502,rows:99,links:199,scripts:"bubblepop",refused:null});
  assert.equal(parseTextnaut("textnaut: page refused: https://a.test/: fetch failed\n").refused,"fetch failed");
  assert(FETCH_FAILURE.test("TypeError: fetch failed")&&!FETCH_FAILURE.test("Error: Lean HTML: SVG identifier nesting exceeds 32"));
});

Deno.test("CPU share after the first frame and ps times", ()=>{
  assert.equal(psSeconds("0:04.35"),4.35);assert.equal(psSeconds("1:02:03"),3723);assert.equal(psSeconds("1-00:00:01"),86401);
  // 1 s of CPU in 2 s of wall after the first frame at 1 s; the early smaller sample is dropped.
  assert.deepEqual(cpuShare([[0,0.5],[0.5,0.2],[1,1],[2,1.5],[3,2]],1),{pct:50,window_s:2});
  assert.equal(cpuShare([[0,0]],0),null);
});

Deno.test("the verdict and budgets", ()=>{
  const ok={crashed:false,unreachable:false,first_frame_s:3,prims:3000,scroll_latency_p95_ms:12,cpu_idle_pct:5,script_turn_max_ms:200};
  assert.equal(verdictOf(ok),"usable");
  assert.equal(verdictOf({...ok,first_frame_s:11.5}),"slow");
  assert.equal(verdictOf({...ok,cpu_idle_pct:101}),"slow");
  assert.equal(verdictOf({...ok,scroll_latency_p95_ms:65573}),"unusable");
  assert.equal(verdictOf({...ok,prims:1}),"blank");
  assert.equal(verdictOf({...ok,first_frame_s:null}),"timeout");
  assert.equal(verdictOf({...ok,crashed:true}),"crash");
  assert.equal(verdictOf({...ok,crashed:true,unreachable:true}),"unreachable");
  assert.deepEqual(overBudget({first_frame_s:7,rss_peak_mb:900,prims:5},{first_frame_s:5,rss_peak_mb:1500}),["first_frame_s 7 > 5"]);
});

Deno.test("PNG decoding and layout similarity", async ()=>{
  const W=320,H=256;
  const picture=(f:(x:number,y:number)=>number)=>{const px=new Uint8Array(W*H*4);
    for(let y=0;y<H;y++)for(let x=0;x<W;x++){const v=f(x,y),i=4*(y*W+x);px[i]=px[i+1]=px[i+2]=v;px[i+3]=255;}return pngOf(W,H,px);};
  // Grey "text lines" in two columns, the same lines one column wide, and a blank page.
  const lines=(x:number,y:number,cols:boolean)=>y%32<12&&x>16&&x<300&&!(cols&&x>=150&&x<=170)?40:255;
  const two=await decodePNG(await picture((x,y)=>lines(x,y,true)));
  const one=await decodePNG(await picture((x,y)=>lines(x,y,false)));
  const blank=await decodePNG(await picture(()=>255));
  assert.equal(two.width,W);assert.equal(two.height,H);assert.equal(two.data[0],255);assert.equal(two.data[20],40);
  assert.equal(ssim(two,two),1);
  const near=ssim(two,one),none=ssim(two,blank);
  assert(none<0.1,`blank against text ${none}`);
  assert(near>none,`similar layout ${near} above blank ${none}`);
  assert.equal(crop(two,64,100).height,100);
});

const summary=(pages:Record<string,unknown>[]):Summary=>({platform:"macos",release:"build-x",engine:{sha256:"ab".repeat(32)},
  host:{commit:"c".repeat(40),shot_at_end:true,liberal_report:true},started:"2026-11-15T00:00:00Z",
  totals:{pages:pages.length,usable:0,slow:0,unusable:0,blank:0,timeout:0,crash:0,unreachable:0},pages:pages as Summary["pages"]});

Deno.test("comparison with the previous survey", ()=>{
  const prev=summary([
    {id:"a",state:"ok",verdict:"usable",first_frame_s:3,first_layout_ms:80,gpu_p50_ms:20,layout_similarity:0.5},
    {id:"b",state:"ok",verdict:"usable",first_frame_s:3,first_layout_ms:10},
    {id:"c",state:"unreachable",verdict:"unreachable"},
    {id:"d",state:"ok",verdict:"usable"},
    {id:"e",state:"ok",verdict:"usable"},
  ]);
  const cur=summary([
    {id:"a",state:"ok",verdict:"slow",first_frame_s:12,first_layout_ms:100,gpu_p50_ms:25,layout_similarity:0.4},
    {id:"b",state:"ok",verdict:"usable",first_frame_s:3,first_layout_ms:40},
    {id:"c",state:"ok",verdict:"usable",first_frame_s:2},
    {id:"d",state:"crash",verdict:"crash",crash_reason:"Error: Lean HTML: a bound"},
    {id:"e",state:"ok",verdict:"usable",log_floods:2,log_flood_top:'[["x #",60]]'},
  ]);
  const fs=findings(cur,prev).map(f=>`${f.level} ${f.page} ${f.text}`);
  assert(fs.includes("warning a verdict usable -> slow"),fs.join("\n"));
  assert(fs.includes("warning a First frame s: 3 -> 12"),"1.5 times and over the floor");
  assert(!fs.some(f=>f.includes("First layout")),"100 against 80 is under 1.5 times; 40 against 10 is under the 50 ms floor");
  assert(fs.includes("warning a layout similarity 0.5 -> 0.4"));
  assert(!fs.some(f=>f.includes(" c ")),"unreachable before, fine now: no finding");
  assert(fs.some(f=>f.startsWith("error d crash")));
  assert(fs.some(f=>f.startsWith("error e log gate tripped 2 time(s)")),"a log flood fails as a crash does");
  const md=markdown(cur,prev);
  assert.match(md,/\| a \| slow \(was usable\) \| 12 \(\+300%\)/);
  const rows=trendRows(cur,"1","u");
  assert.equal(rows.length,5);assert.equal(rows[0].split(",").length,TREND_COLUMNS.length);
});

Deno.test("--liberal-report: each System entry once, page entries never, nothing when off", ()=>{
  const heard:ConsoleEntry[]=[];
  const page={};
  addEntries(page,[{source:"System",severity:"warning",feature:"f",where:"w",message:"m"}]);
  assert.equal(heard.length,0);
  reportSystemEntries(e=>heard.push(e));
  try{
    addEntries(page,[{source:"System",severity:"warning",feature:"f",where:"w",message:"m"},
      {source:"System",severity:"warning",feature:"g",where:"w",message:"n"},{source:"page",severity:"log",message:"hello"}]);
    addEntries(page,[{source:"System",severity:"warning",feature:"g",where:"w",message:"n"}]);
  } finally {reportSystemEntries(undefined);}
  assert.deepEqual(heard.map(e=>e.feature),["g"],"f was kept before the report was on; g once");
});

Deno.test("snapshot ZIP: written, read back, the same bytes for the same files", async ()=>{
  assert.equal(crc32(new TextEncoder().encode("123456789")),0xcbf43926);
  const big=new TextEncoder().encode("abc ".repeat(5000)),odd=crypto.getRandomValues(new Uint8Array(300));
  const files=[{name:"manifest.json",data:new TextEncoder().encode("{}")},{name:"bodies/0001",data:big},{name:"bodies/0002",data:odd},{name:"empty",data:new Uint8Array()}];
  const zip=await writeZip(files),back=await readZip(zip);
  assert(zip.length<big.length/10,"text is deflated");
  for(const f of files)assert.deepEqual(back.get(f.name),f.data,f.name);
  assert.deepEqual(await writeZip(files),zip,"deterministic");
});
