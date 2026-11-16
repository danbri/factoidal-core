// A start that waits for sync answers goes on from the script that waited (WebScripts
// StartPoint, LeanJS.startUntil; theorems LeanJS.startUntil_some, start_eq_from). Before
// 2026-11-15 each answer made the whole start again: a page whose classic scripts made n sync
// requests ran its scripts about n times (a news page made 130 requests: 29 s of the engine's
// time). An original page: a script that does some work, then n scripts each with one sync
// XMLHttpRequest. The logs are those of one run, in order, and the engine's time for 4n
// scripts is less than 8 times that for n (a rerun of the start per answer is n², 16 times).
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env start_resume_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};
type Turn=ScriptTurn&{logs:string[];errors:string[]};

function page(n:number){
  const sync=Array.from({length:n},(_,i)=>`<script>{const x=new XMLHttpRequest();x.open('GET','/d${i}',false);x.send();console.log('${i}:'+x.status+':'+x.responseText);}</script>`).join("\n");
  return `<!doctype html><html><body><p id="p">x</p><script>let w=0;for(let i=0;i<40000;i++)w=(w*7+i)%9973;console.log('work '+w);</script>
${sync}
<script>console.log('end');</script></body></html>`;
}

const b64=(t:string)=>btoa(t);
function run(engine:HTMLEngine,n:number){
  const t0=performance.now();
  let turn=engine.scriptSession(page(n),{action:"start",url:"http://example.test/p.html",resources:[],engine:"bubblepop",network:true,
    pageAddress:"93.184.216.34",width:800,height:600}) as Turn;
  let answers=0;
  for(;turn.netSync&&answers<4*n+16;answers++){
    const w=turn.netSync;
    const answer=w.resolve?{id:w.id,addresses:["93.184.216.34"]}
      :{id:w.id,status:200,headers:[["content-type","text/plain"]] as [string,string][],bodyBase64:b64("v"+new URL(w.url).pathname.slice(2))};
    turn=engine.scriptSession("",{action:"syncAnswer",session:turn.session,answer}) as Turn;
  }
  const ms=performance.now()-t0;
  engine.scriptSession("",{action:"close"});
  return {ms,turn,answers};
}

Deno.test({name:"a start goes on from the script that waited: one run's logs, linear time",ignore:!exists(library),fn:async()=>{
  const engine=await loadHTML(library);
  const small=run(engine,6);
  assert.deepEqual(small.turn.errors,[],"page errors");
  const want=["work "+(()=>{let w=0;for(let i=0;i<40000;i++)w=(w*7+i)%9973;return w;})(),
    ...Array.from({length:6},(_,i)=>`${i}:200:v${i}`),"end"];
  assert.deepEqual(small.turn.logs.map(l=>l.replace(/^\u0001\w+\u0001/,"")),want);
  const a=run(engine,8),b=run(engine,32);
  console.log(`8 sync scripts: ${a.ms.toFixed(0)} ms (${a.answers} answers); 32: ${b.ms.toFixed(0)} ms (${b.answers} answers); x${(b.ms/a.ms).toFixed(1)}`);
  assert.ok(b.ms<8*a.ms,`32 sync scripts took ${(b.ms/a.ms).toFixed(1)} times as long as 8`);
}});
