// Page script costs with no window (issue 1271): click turn, animation frame turn, and the
// Lean render that follows each, on pages/showcase-script.html. One JSON line per figure.
// Run: deno run --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-ffi page_scripts_bench.ts [DYLIB]
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,prepareHTML} from "./native_html_document.ts";
import {scriptHook,type PageScripts} from "./native_html_scripts.ts";

const engine=await loadHTML(Deno.args[0]);
const ms=(a:number,b:number)=>Math.round((b-a)*10)/10;
const pct=(v:number[],q:number)=>{const s=[...v].sort((a,b)=>a-b);return s.length?s[Math.min(s.length-1,Math.ceil(q*s.length)-1)]:null;};
const frameRenders:number[]=[];
const hook=scriptHook(()=>"quickjs",{plan:r=>engine.scriptPlan(r),
  compact:(s,u,c)=>Promise.resolve(engine.compactCommands(s,{url:u,commands:c})),
  changed:(_p,_b,kind)=>{
    if(kind!=="frame")return Promise.resolve();
    // The render a window makes for this frame, on this thread, timed.
    const start=performance.now();doc.compile(900,1200);frameRenders.push(performance.now()-start);
    return Promise.resolve();
  },stopped:()=>{},trace:()=>{}});
const t0=performance.now();
const doc=await prepareHTML(engine,inputURL(new URL("./pages/showcase-script.html",import.meta.url).pathname,true),undefined,undefined,hook);
const runtime=doc.script.runtime as unknown as PageScripts;
console.log(JSON.stringify({figure:"load with scripts",ms:ms(t0,performance.now())}));
// The animation runs until it ends (six seconds).
while(runtime.animating&&performance.now()-t0<12000)await new Promise(r=>setTimeout(r,16));
const animationMs=ms(t0,performance.now());
console.log(JSON.stringify({figure:"animation",frames:runtime.stats.frames,framesPerSecond:Math.round(runtime.stats.frames/(animationMs/1000)),renderMsP50:pct(frameRenders,0.5),renderMsP95:pct(frameRenders,0.95),commands:runtime.commands.length,compactions:runtime.stats.compactions}));
// Clicks: the turn, then the render that shows it.
const counter=(engine.inspect(doc.source,{url:doc.url}).nodes as unknown as {id:number;attributes:Record<string,string>}[]).find(n=>n.attributes.id==="counter")!.id;
const turns:number[]=[],renders:number[]=[];
for(let i=0;i<20;i++){
  const a=performance.now();await runtime.dispatch({type:"click",nodeId:counter});const b=performance.now();
  await doc.compile(900,1200);const c=performance.now();turns.push(b-a);renders.push(c-b);
}
console.log(JSON.stringify({figure:"click",turnMsP50:pct(turns,0.5),turnMsMax:Math.max(...turns),renderMsP50:pct(renders,0.5),renderMsMax:Math.max(...renders),
  clickToFrameMsP50:pct(turns.map((t,i)=>t+renders[i]),0.5)}));
runtime.stop("bench end");
Deno.exit(0);
