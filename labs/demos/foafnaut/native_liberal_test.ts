// Liberal mode and the console (WebAccept.lean, WebConsole.lean; docs/designissues/
// 2026-11-08-liberal-mode-and-console.md) through the host path of the native browser
// (prepareHTML: Lean inspects, the host fetches, Lean lays out and draws), on the original
// fixtures of fixtures/liberal/. For each fixture: strict mode refuses it, liberal mode draws
// it with the System entries Lean gave and the note that links to foafnaut:console; on the
// demo pages, which strict mode accepts, liberal mode draws the same frame with no entries.
// Run on the Wasm engine and, when it is built, the native library. --allow-read --allow-ffi --allow-env.
import {strict as assert} from "node:assert";
import {loadHTML,type HTMLEngine} from "./native_html_engine.ts";
import {prepareHTML} from "./native_html_document.ts";
import {consoleOf,consoleRequest} from "./native_console.ts";

const library=new URL("./.build/web-render/engines/libweb-render.dylib",import.meta.url).pathname;
const noLibrary=(()=>{try{Deno.statSync(library);return false;}catch{return true;}})();
const fixture=(name:string)=>new URL(`./fixtures/liberal/${name}`,import.meta.url).href;
const page=(name:string)=>new URL(`./pages/${name}`,import.meta.url).href;

const cases:{name:string;refusal:RegExp;features:string[]}[]=[
  {name:"media.html",refusal:/unsupported stylesheet media condition/,features:["stylesheet media condition"]},
  {name:"missing-css.html",refusal:/No such file|not found|os error 2/i,features:["external stylesheet"]},
  {name:"svg.html",refusal:/unsupported/,features:["inline SVG"]},
  {name:"sample.html",refusal:/./,features:["stylesheet media condition","external stylesheet"]},
];

async function runs(engine:HTMLEngine){
  const out:unknown[]=[];
  for(const c of cases){
    await assert.rejects(async()=>{const doc=await prepareHTML(engine,fixture(c.name));engine.compile(doc.source,800,600,doc.request(800,600).options);},c.refusal,`strict ${c.name}`);
    const doc=await prepareHTML(engine,fixture(c.name),undefined,undefined,{liberal:true});
    const frame=await doc.compile(800,600,{textScalePercent:100});
    const system=consoleOf(doc).filter(e=>e.source==="System");
    for(const feature of c.features)assert(system.some(e=>e.feature===feature),`${c.name}: no System entry for ${feature}: ${JSON.stringify(system)}`);
    assert(system.every(e=>e.action&&e.message),`${c.name}: an entry without action or message`);
    assert(frame.webRender.links.some(link=>link[1]==="foafnaut:console"),`${c.name}: no note linking to foafnaut:console`);
    // The console page: Lean writes it from the entries and draws it.
    const consolePage=engine.consolePage(consoleRequest(doc,0,[doc]));
    assert.match(consolePage.title,new RegExp(`Console \\(${system.length} System`));
    for(const feature of c.features)assert(consolePage.source.includes(feature),`${c.name}: console page lacks ${feature}`);
    const shown=await prepareHTML(engine,"foafnaut:console",undefined,consolePage.source);
    assert(engine.compile(shown.source,800,600,shown.request(800,600).options).primitiveCount>20);
    out.push({name:c.name,features:system.map(e=>e.feature),primitives:frame.primitiveCount});
  }
  // A media condition this engine reads, in both modes: the sheet applies at 800 CSS px and
  // not at 400 (the viewport in CSS px is the width over the text scale).
  const bottom=(frame:{webRender:Record<string,unknown>})=>Math.max(0,...((frame.webRender.boxes as number[][]|undefined)??[]).map(b=>b[2]+b[4]));
  const tall='<!doctype html><title>T</title><style media="screen and (min-width: 500px)">div{height:300px}</style><div>x</div>';
  for(const liberal of [false,true]){
    const doc=await prepareHTML(engine,fixture("tall.html"),undefined,tall,{liberal});
    const wide=await doc.compile(800,600,{textScalePercent:100}),narrow=await doc.compile(400,600,{textScalePercent:100});
    assert(bottom(wide)>=300&&bottom(narrow)<300,`min-width: ${bottom(wide)} at 800, ${bottom(narrow)} at 400`);
    const zoomed=await doc.compile(800,600,{textScalePercent:200});
    assert(bottom(zoomed)<300,`min-width at 200%: ${bottom(zoomed)} (400 CSS px)`);
  }
  // Pages that strict mode accepts: the same frame in liberal mode, and no System entry.
  for(const name of ["index.html","showcase-tables.html","settings.html","print-showcase.html"]){
    const strict=await prepareHTML(engine,page(name));
    const liberal=await prepareHTML(engine,page(name),undefined,undefined,{liberal:true});
    const a=await strict.compile(900,1200,{textScalePercent:150}),b=await liberal.compile(900,1200,{textScalePercent:150});
    assert.equal(b.primitiveCount,a.primitiveCount,name);
    assert.deepEqual(Array.from(b.data),Array.from(a.data),`${name}: liberal frame differs`);
    assert.equal(b.diagnostics,undefined,name);
    assert.equal(consoleOf(liberal).filter(e=>e.source==="System").length,0,name);
  }
  return out;
}

Deno.test("liberal mode skips, reports and draws the note; strict refuses (Wasm)",async()=>{await runs(await loadHTML());});
Deno.test({name:"liberal mode (native library), as the Wasm engine",ignore:noLibrary,fn:async()=>{
  assert.equal(JSON.stringify(await runs(await loadHTML(library))),JSON.stringify(await runs(await loadHTML())));
}});

// Console levels (prelude.js console, WebConsole.level): warn, error, info and debug reach the
// console tab with their level, on BubblePopJS and on QuickJS-NG (when its guest module, built
// from this prelude, is given in QUICKJS_WASM). Native library.
const levelsPage='<!doctype html><title>L</title><p>x</p><script>console.log("plain");console.warn("careful",1);console.error("bad");'+
  'console.info("note");console.debug("detail");console.table([1]);console.group("g");console.groupEnd();console.assert(false,"assert")</script>';
Deno.test({name:"console levels reach the console tab (BubblePopJS, and QuickJS-NG with QUICKJS_WASM)",ignore:noLibrary,fn:async()=>{
  const engine=await loadHTML(library);
  const engines=(engine.scriptInfo().engines??[]) as string[];
  const guest=Deno.env.get("QUICKJS_WASM");
  const runs:[string,Record<string,unknown>][]=[];
  if(engines.includes("bubblepop"))runs.push(["bubblepop",{engine:"bubblepop"}]);
  if(guest){engine.scriptLoad(await Deno.readFile(guest));runs.push(["quickjs",{}]);}
  for(const [name,extra] of runs){
    const turn=engine.scriptSession(levelsPage,{action:"start",url:"file:///levels.html",resources:[],...extra}) as {logs:string[];errors:string[]};
    engine.scriptSession("",{action:"close"});
    assert.deepEqual(turn.errors,[],`${name}: page errors`);
    assert.deepEqual(turn.logs,["plain","\u0001warn\u0001careful 1","\u0001error\u0001bad","\u0001info\u0001note","\u0001debug\u0001detail","[1]","g","\u0001error\u0001Assertion failed: assert"],name);
    const page={url:"file:///levels.html",title:"L"};
    const shown=engine.consolePage({tab:1,title:"L",url:page.url,entries:turn.logs.map(message=>({source:"page",severity:"log",message})),tabs:[page]});
    for(const want of ["page warn","page error","page info","page debug","page log"])assert(shown.source.includes(want),`${name}: console page lacks ${want}`);
    assert(!shown.source.includes("\u0001"),`${name}: a level mark is shown`);
  }
}});
