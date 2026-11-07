// Page scripts in the desktop host (issue 1271): the setting, QuickJS-NG on the demo page,
// and VerifiedJS refusing visibly (issue 1252). Needs the Lean engine with the script
// operations in .build/native-html/runtime (test.sh copies the local build there) and the
// QuickJS-NG reactor (web-render/script-engine/fetch-reactor.mjs).
// Run: deno test --no-check --no-config --no-npm --node-modules-dir=none --allow-read --allow-write --allow-run page_scripts_test.ts
import {strict as assert} from "node:assert";
import {loadHTML} from "./native_html_engine.ts";
import {inputURL,prepareHTML} from "./native_html_document.ts";
import {scriptHook,type Batch,type PageScripts} from "./native_html_scripts.ts";
import {createVerifiedJSSession,moduleInterface} from "./web-render/script-engine/verifiedjs/adapter.mjs";

const engine=await loadHTML();
const page=inputURL(new URL("./pages/showcase-script.html",import.meta.url).pathname,true);
const quiet={sanitizeOps:false,sanitizeResources:false};
type Node={id:number;parent?:number|null;attributes:Record<string,string>;textContent:string};

async function open(setting:string,url=page){
  const batches:{kind:string;batch:Batch}[]=[],stops:string[]=[];
  const hook=scriptHook(()=>setting,{plan:request=>engine.scriptPlan(request),
    compact:(source,url,commands)=>Promise.resolve(engine.compactCommands(source,{url,commands})),
    changed:(_page,batch,kind)=>{batches.push({kind,batch});return Promise.resolve();},
    stopped:(_page,reason)=>{stops.push(reason);},trace:()=>{}});
  const doc=await prepareHTML(engine,url,undefined,undefined,hook);
  const nodes=()=>engine.inspect(doc.source,{url:doc.url,commands:doc.script.commands}).nodes as unknown as Node[];
  const byId=(id:string)=>nodes().find(n=>n.attributes.id===id);
  return {doc,batches,stops,nodes,byId,runtime:doc.script.runtime as unknown as PageScripts|undefined};
}

Deno.test("the page script setting: QuickJS-NG is the default, and a link names each engine",()=>{
  assert.equal(engine.scriptPlan({setting:"",scripts:1}).engine,"quickjs");
  assert.equal(engine.scriptSetting("VerifiedJS").setting,"verifiedjs");
  assert.equal(engine.scriptSetting("none").setting,"none");
  assert.throws(()=>engine.scriptSetting("rhino"),/unknown page script engine/);
});

Deno.test({name:"QuickJS-NG runs the demo page: counter, growing list, sorted table and keys change Lean's DOM",...quiet,fn:async()=>{
  const {doc,runtime,byId,nodes}=await open("quickjs");
  assert.ok(runtime,"a runtime started");
  try{
    assert.equal(doc.script.marker,"JS QUICKJS-NG");
    assert.equal(doc.script.notice,"");
    const id=(name:string)=>byId(name)!.id;
    await runtime.dispatch({type:"click",nodeId:id("counter")});
    assert.equal(byId("count")?.textContent,"Clicks: 1");
    assert.equal(byId("counter")?.attributes.class,"button even","classList.toggle went through Lean");
    assert.match(byId("counter")?.attributes.style??"",/border-color: #c4455a/,"style.borderColor went through Lean");
    await runtime.dispatch({type:"click",nodeId:id("grow")});
    const list=id("list");
    assert.equal(nodes().filter(n=>n.parent===list).length,4,"createElement and appendChild added an item");
    assert.equal(byId("list")?.textContent.endsWith("Item 4"),true);
    await runtime.dispatch({type:"click",nodeId:id("sort")});
    assert.equal(byId("people-body")?.textContent,"Ada1815Grace1906Tim1955","appendChild moved the rows into order");
    for(const key of "xyz")await runtime.dispatch({type:"keydown",key});
    assert.equal(byId("typed")?.textContent,"xyz");
    // The page renders with the script's DOM.
    assert.ok((await doc.compile(900,1200)).primitiveCount>0);
  }finally{runtime.stop("test end");}
}});

Deno.test({name:"the None setting runs no script and the chrome says so",...quiet,fn:async()=>{
  const {doc,runtime}=await open("none");
  assert.equal(runtime,undefined);
  assert.equal(doc.script.marker,"JS OFF");
  assert.equal(doc.script.commands.length,0);
}});

// Expected failure of https://github.com/danbri/factoidal/issues/1252: VerifiedJS can not run a
// page script. When it can, this test fails: make it assert the page runs, and close the issue.
Deno.test({name:"expected failure, issue 1252: VerifiedJS refuses the demo page visibly, and the page still renders",...quiet,fn:async()=>{
  const {doc,runtime,stops}=await open("verifiedjs");
  assert.equal(doc.script.marker,"JS REFUSED");
  assert.match(doc.script.notice,/^Page scripts refused \(VerifiedJS\): .*issues\/1252/);
  assert.equal(doc.script.commands.length,0);
  assert.ok(!runtime||runtime.stopped,`no VerifiedJS runtime runs (stops: ${stops.join("; ")})`);
  // The notice is on the page: the render with it differs from the render with no notice.
  const shown=await doc.compile(900,1200),plain=engine.compile(doc.source,900,1200,{url:doc.url,resources:[]});
  assert.notEqual(shown.primitiveCount,plain.primitiveCount);
}});

// A minimal module with the host interface of a VerifiedJS module at the pin: it imports
// wasi_snapshot_preview1.fd_write and exports memory, _start and main.
function pinShapedModule():Uint8Array<ArrayBuffer>{
  const text=(s:string)=>[s.length,...new TextEncoder().encode(s)];
  const section=(id:number,body:number[])=>[id,body.length,...body];
  const types=section(1,[2,0x60,4,0x7f,0x7f,0x7f,0x7f,1,0x7f,0x60,0,0]);
  const imports=section(2,[1,...text("wasi_snapshot_preview1"),...text("fd_write"),0,0]);
  const functions=section(3,[1,1]);
  const memory=section(5,[1,0,1]);
  const exports=section(7,[3,...text("memory"),2,0,...text("_start"),0,1,...text("main"),0,1]);
  const code=section(10,[1,2,0,0x0b]);
  return new Uint8Array([0,0x61,0x73,0x6d,1,0,0,0,...types,...imports,...functions,...memory,...exports,...code]);
}

Deno.test({name:"expected failure, issue 1252: a VerifiedJS module with the pin's interface is refused, with the interface named",...quiet,fn:async()=>{
  const bytes=pinShapedModule();
  assert.deepEqual(moduleInterface(bytes),{imports:["wasi_snapshot_preview1.fd_write"],exports:["memory","_start","main"]});
  // A stand-in compiler: it writes that module to the -o path, as the VerifiedJS compiler does.
  const dir=await Deno.makeTempDir({prefix:"fake-verifiedjs-"});
  try{
    await Deno.writeFile(`${dir}/module.wasm`,bytes);
    await Deno.writeTextFile(`${dir}/verifiedjs`,`#!/bin/sh\ncp "${dir}/module.wasm" "$3"\n`);
    await Deno.chmod(`${dir}/verifiedjs`,0o755);
    const session=createVerifiedJSSession({binary:`${dir}/verifiedjs`});
    await assert.rejects(session.start({nodes:[],sources:["document.title"]}),
      /no DOM host interface \(imports: wasi_snapshot_preview1\.fd_write; exports: memory, _start, main\).*issues\/1252/);
    // A compiler that fails says why.
    await Deno.writeTextFile(`${dir}/verifiedjs`,`#!/bin/sh\necho "parse error at 1:1" >&2\nexit 3\n`);
    await assert.rejects(session.start({nodes:[],sources:["("]}),/did not compile script 1: parse error at 1:1/);
  }finally{await Deno.remove(dir,{recursive:true});}
}});
