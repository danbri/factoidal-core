// The cost of adding rules to a style sheet one at a time (CSSStyleSheet.insertRule at the end
// of the list, with cssRules.length read before each: what CSS-in-JS libraries do when a page
// hydrates). Until 2026-11-16 each insert gave the sheet's whole text to Lean twice
// (CssSheet.sheetOp "rules" and "insert"), which parsed every rule again, and the page-side
// holder made its rule list again: n inserts cost n² (a news article's 800 inserts were about
// a third of its 15 s start). Now Lean reads only the new rule and the kinds of the rules
// there (CssSheet.insertAt; theorem insertRule_eq_insertAt) and the holder keeps its rules.
// This page is an original construct: a style element with some rules, and a script that
// inserts `n` rules, deletes one, and reads the result back. The rules, their order, the
// sheet's text and the cascade must be what the inserts say, and the steps of 800 inserts
// (the script clock's count, the same on every machine) must stay under 1.2 M: they were
// 2,568,585 before and are about 600,000 now. What is still paid per insert is the sheet's
// text written back to its style element (the sheet's state is that text): bytes at memory
// speed, a step for each 64. The time is printed and bounded loosely (800 inserts took 25 s
// before and take about half a second), since a busy machine stretches it.
// Needs the native library (build-web-render.sh --native).
// Run: deno test --allow-read --allow-ffi --allow-env cssom_insert_cost_test.ts
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine,type ScriptTurn} from "./native_html_engine.ts";

const library=Deno.env.get("WEB_RENDER_LIB")??new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const exists=(p:string)=>{try{return Deno.statSync(p).isFile;}catch{return false;}};

/** The page: 40 rules in a style element, and a script that inserts `n` more at the end. */
export function page(n:number){
  const base=Array.from({length:40},(_,i)=>`.b${i}{margin:${i}px;color:#${(i*37%4096).toString(16).padStart(3,"0")}}`).join("\n");
  return `<!doctype html><html><head><style id="s">${base}</style></head><body><p id="p" class="c7">text</p><script>
const sheet=document.getElementById('s').sheet;
const first=sheet.cssRules[0];
for(let i=0;i<${n};i++)sheet.insertRule('.c'+i+'{padding:'+(i%9)+'px;color:rgb('+(i%256)+', 0, 0)}',sheet.cssRules.length);
sheet.insertRule('@media (min-width: 10px){.m{left:1px}}',1);
sheet.deleteRule(2);
const rules=sheet.cssRules;
console.log('OUT '+JSON.stringify({
  length:rules.length,same:rules[0]===first,second:rules[1].cssText,third:rules[2].cssText,
  last:rules[rules.length-1].cssText,lastSelector:rules[rules.length-1].selectorText,
  parent:rules[5].parentStyleSheet===sheet,color:getComputedStyle(document.getElementById('p')).color,
  lines:document.getElementById('s').textContent.split('\\n').length}));
</script></body></html>`;
}

type Turn=ScriptTurn&{logs:string[];errors:string[]};
function start(engine:HTMLEngine,n:number){
  const url="http://example.test/cssom.html";
  const t0=performance.now();
  const turn=engine.scriptSession(page(n),{action:"start",url,resources:[],instructionsPerMs:1e12,engine:"bubblepop",layout:{url},width:800,height:600}) as Turn;
  const ms=performance.now()-t0;
  engine.scriptSession("",{action:"close"});
  assert.deepEqual(turn.errors,[],"page errors at start");
  const out=turn.logs.find(l=>l.includes("OUT "));
  return {ms,turn,out:out?JSON.parse(out.slice(out.indexOf("OUT ")+4)):undefined};
}

async function check(engine:HTMLEngine,label:string){
  const info=engine.scriptInfo();
  if(!(info.engines??[]).includes("bubblepop")){console.log(`NOT RUN (${label}): this engine has no BubblePopJS`);return;}
  start(engine,10); // warm the engine
  const small=start(engine,200),large=start(engine,800);
  console.log(`${label}: 200 inserts ${small.ms.toFixed(0)} ms, ${small.turn.instructions} steps; 800 inserts ${large.ms.toFixed(0)} ms, ${large.turn.instructions} steps`);
  assert.deepEqual(large.out,{length:840,same:true,second:"@media (min-width: 10px) {\n  .m { left: 1px; }\n}",third:".b2 { margin: 2px; color: rgb(0, 68, 170); }",
    last:".c799 { padding: 7px; color: rgb(31, 0, 0); }",lastSelector:".c799",parent:true,color:"rgb(7, 0, 0)",lines:842},`${label}: the sheet after the inserts`);
  assert.ok(large.turn.instructions<1200000,`${label}: 800 inserts took ${large.turn.instructions} steps (the sheet is read again at each insert?)`);
  assert.ok(large.ms<8000,`${label}: 800 inserts took ${large.ms.toFixed(0)} ms`);
}

Deno.test({name:"Inserting rules into a style sheet one at a time does not read the sheet again at each insert (native library)",ignore:!exists(library),fn:async()=>{
  await check(await loadHTML(library),"native");
}});
