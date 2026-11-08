// testharness-run.ts: run WPT testharness.js tests with page scripts run by Lean
// (record: docs/designissues/2026-11-08-page-scripts.md).
//
// Each test page runs in the Foafnaut engine's script session (`scriptSession`,
// labs/demos/foafnaut/WebScripts.lean): QuickJS-NG in WasmVM on the page's Lean DOM
// arena, with the Lean event loop deciding every callback. The virtual clock moves
// until nothing waits (a budget of 70 s of virtual time). testharness.js and our
// testharnessreport.js (tests/browser-wpt/testharnessreport.js, in place of WPT's) are
// classic scripts; results leave the page as console lines.
//
// Tests: the pinned WPT files in third_party/testing/wpt-scripting (wpt ce5ca396; see
// third_party/testing/wpt-scripting-PROVENANCE.md). `.any.js` and `.window.js` files
// get the window wrapper that wptserve gives them.
//
//   deno run -A tests/browser-wpt/testharness-run.ts [--engine native|wasm|bench]
//     [--native-engine DYLIB] [--quickjs-wasm FILE] [--dirs a,b] [--only SUBSTRING]
//     [--out FILE] [--baseline FILE] [--bench EXE] [--instructions-per-ms N]
//
// --engine native (default): the engine library labs/demos/foafnaut/.build/web-render/
// engines/libweb-render.dylib. wasm: the engine's Wasm build. bench: the same session
// through `lake exe wasmvm-bench page` (formal/lean4), for work on the guest without an
// engine build. With --baseline, the run fails when a subtest that passed there fails.
import {dirname,join,resolve} from "node:path";
import {fileURLToPath as fromFileUrl} from "node:url";

const here=dirname(fromFileUrl(import.meta.url)),root=resolve(here,"../.."),
  wpt=join(root,"third_party/testing/wpt-scripting");
const args=Deno.args,opt=(name:string,fallback="")=>{const i=args.indexOf(name);return i>=0?args[i+1]:fallback;};
const engineKind=opt("--engine","native");
const quickjs=opt("--quickjs-wasm",join(Deno.env.get("HOME")??"","working/qjs-wasm/qjs-wasmvm.wasm"));
export const directories=["html/webappapis/timers","html/webappapis/microtask-queuing","dom/events","dom/nodes",
  "html/webappapis/scripting/event-loops"];
const dirs=opt("--dirs")?opt("--dirs").split(","):directories;
const only=opt("--only");
const origin="http://web-platform.test";
// The script clock's rate (Hosts.Page.ScriptClock). A test's own timeouts (testharness.js
// gives each file 10 s) assume a browser's speed; this engine runs many more instructions
// for the same work, so at the engine's rate (100 000 a ms) script time alone would time
// out heavy files. The runner measures conformance, so script time is as good as off
// (a trillion instructions a ms) unless --instructions-per-ms says otherwise. An engine
// from before the clock ignores the field; a bench from before it takes the flag for a
// file name, so run this runner with a bench built from the same tree.
const scriptRate=Number(opt("--instructions-per-ms","1000000000000"));
const statusNames=["PASS","FAIL","TIMEOUT","NOTRUN","PRECONDITION_FAILED"];
const harnessNames=["OK","ERROR","TIMEOUT","PRECONDITION_FAILED"];

type Subtest={name:string;status:string;message?:string|null};
export type Case={file:string;harness:string;message?:string|null;subtests:Subtest[];ms?:number;instructions?:number;
  clock?:number;errors?:string[]};

/** The tests of a directory: its own files that are testharness tests a window runs. */
export function testsOf(dir:string):{file:string;skip?:string}[] {
  const out:{file:string;skip?:string}[]=[];
  for(const e of [...Deno.readDirSync(join(wpt,dir))].sort((a,b)=>a.name<b.name?-1:1)) {
    if(!e.isFile)continue;
    const n=e.name,file=`${dir}/${n}`;
    if(n.endsWith(".any.js")||n.endsWith(".window.js")) {
      const meta=metaOf(Deno.readTextFileSync(join(wpt,file)));
      const globals=meta.filter(([k])=>k==="global").map(([,v])=>v).join(",");
      if(globals&&!/(^|,)\s*(window|default)\b/.test(globals)&&n.endsWith(".any.js"))out.push({file,skip:"no window global"});
      else out.push({file});
    } else if(n.endsWith(".worker.js"))out.push({file,skip:"worker"});
    else if(n.endsWith(".html")||n.endsWith(".xhtml")) {
      const text=Deno.readTextFileSync(join(wpt,file));
      if(!text.includes("/resources/testharness.js"))continue;
      if(n.includes("-manual"))out.push({file,skip:"manual"});
      else if(n.includes(".sub."))out.push({file,skip:"needs wptserve substitution"});
      else if(n.endsWith(".xhtml")&&engineKind==="bench")out.push({file,skip:"XML (engine only)"});
      else out.push({file});
    }
  }
  return out;
}
function metaOf(text:string):[string,string][] {
  const out:[string,string][]=[];
  for(const line of text.split("\n")) {
    const m=/^\/\/\s*META:\s*([a-z_]+)=(.*)$/.exec(line.trim());
    if(m)out.push([m[1],m[2].trim()]);else if(line.trim()!==""&&!line.startsWith("//"))break;
  }
  return out;
}
const escapeHTML=(s:string)=>s.replace(/&/g,"&amp;").replace(/</g,"&lt;").replace(/"/g,"&quot;");
/** The page wptserve makes for a .any.js (window variant) or .window.js test. */
export function wrapper(file:string):string {
  const meta=metaOf(Deno.readTextFileSync(join(wpt,file)));
  const title=meta.find(([k])=>k==="title")?.[1];
  const long=meta.some(([k,v])=>k==="timeout"&&v==="long");
  const scripts=meta.filter(([k])=>k==="script").map(([,v])=>v);
  return `<!doctype html>\n<meta charset=utf-8>\n${long?'<meta name="timeout" content="long">\n':""}${title?`<title>${escapeHTML(title)}</title>\n`:""}`+
    `<script>\nself.GLOBAL = {isWindow: function() { return true; }, isWorker: function() { return false; }, isShadowRealm: function() { return false; }};\n</script>\n`+
    `<script src="/resources/testharness.js"></script>\n<script src="/resources/testharnessreport.js"></script>\n`+
    scripts.map(s=>`<script src="${escapeHTML(s)}"></script>\n`).join("")+
    `<div id=log></div>\n<script src="/${file}"></script>\n`;
}
const pageOf=(file:string)=>file.endsWith(".js")?file.replace(/\.js$/,".html"):file;
/** A script URL of the test origin as a file: our testharnessreport.js, else the pinned WPT file. */
function scriptFile(url:string):string|undefined {
  const u=new URL(url);
  if(u.origin!==origin)return undefined;
  if(u.pathname==="/resources/testharnessreport.js")return join(here,"testharnessreport.js");
  const path=join(wpt,decodeURIComponent(u.pathname));
  return path.startsWith(wpt)?path:undefined;
}

function resultOf(file:string,logs:string[]):Case {
  const subtests:Subtest[]=[];let harness="CRASH",message:string|null|undefined;
  for(const line of logs) {
    if(line.startsWith("__wpt_result ")){const r=JSON.parse(line.slice(13));subtests.push({name:r.name,status:statusNames[r.status]??String(r.status),...(r.status?{message:r.message}:{})});}
    else if(line.startsWith("__wpt_done ")){const d=JSON.parse(line.slice(11));harness=harnessNames[d.status]??String(d.status);message=d.message;}
  }
  if(harness==="CRASH"&&subtests.length===0)harness="NO_RESULT";
  return {file,harness,...(message?{message}:{}),subtests};
}

// ---- the engine backend -------------------------------------------------------------
async function engineBackend():Promise<{run:(file:string)=>Promise<Case>;info:Record<string,unknown>}> {
  const {loadHTML}=await import("../../labs/demos/foafnaut/native_html_engine.ts");
  const engine=await loadHTML(engineKind==="wasm"?undefined:opt("--native-engine",join(root,"labs/demos/foafnaut/.build/web-render/engines/libweb-render.dylib")));
  const info=engine.scriptInfo();
  engine.scriptLoad(await Deno.readFile(quickjs));
  return {info,run:async(file)=>{
    const html=file.endsWith(".js")?wrapper(file):await Deno.readTextFile(join(wpt,file));
    const url=`${origin}/${pageOf(file)}`;
    const t0=performance.now();
    const facts=engine.inspect(html,{url}) as unknown as {scripts:{nodeId:number;src:string;url:string}[]};
    const resources=[];
    for(const s of facts.scripts) {
      if(!s.src)continue;
      const path=scriptFile(s.url);
      if(path)try{resources.push({nodeId:s.nodeId,source:await Deno.readTextFile(path)});}catch{/* not vendored: the page reports it */}
    }
    let turn=engine.scriptSession(html,{action:"start",url,resources,commandLimit:200000,logLimit:100000,instructionsPerMs:scriptRate});
    const logs=[...turn.logs],errors=[...turn.errors];
    let instructions=turn.instructions;
    turn=engine.scriptSession("",{action:"settle",session:turn.session,budgetMs:70000});
    logs.push(...turn.logs);errors.push(...turn.errors);instructions+=turn.instructions;
    engine.scriptSession("",{action:"close"});
    return {...resultOf(file,logs),ms:Math.round(performance.now()-t0),instructions,clock:turn.clock,...(errors.length?{errors:errors.slice(0,5)}:{})};
  }};
}

// ---- the bench backend (lake exe wasmvm-bench page) -----------------------------------
async function benchBackend():Promise<{run:(file:string)=>Promise<Case>;info:Record<string,unknown>}> {
  const exe=opt("--bench",join(root,"formal/lean4/.lake/build/bin/wasmvm-bench"));
  const served=await Deno.makeTempDir({prefix:"wpt-served-"});
  for(const d of ["dom","html","common"])await Deno.symlink(join(wpt,d),join(served,d));
  await Deno.mkdir(join(served,"resources"));
  for(const e of Deno.readDirSync(join(wpt,"resources")))await Deno.symlink(join(wpt,"resources",e.name),join(served,"resources",e.name));
  await Deno.symlink(join(here,"testharnessreport.js"),join(served,"resources/testharnessreport.js"));
  const gen=join(served,"generated");
  return {info:{engine:"wasmvm-bench page"},run:async(file:string)=>{
    let page=file;
    if(file.endsWith(".js")){page=`generated/${pageOf(file)}`;await Deno.mkdir(dirname(join(served,page)),{recursive:true});
      await Deno.writeTextFile(join(served,page),wrapper(file));}
    const t0=performance.now();
    const out=await new Deno.Command(exe,{args:["page",quickjs,served,page,"--settle","70000","--commands","200000",
      "--instructions-per-ms",String(scriptRate)],stdout:"piped",stderr:"null"}).output();
    const line=new TextDecoder().decode(out.stdout).trim().split("\n").pop()??"{}";
    const r=JSON.parse(line||"{}");
    if(r.error)return {file,harness:"ERROR",message:r.error,subtests:[]};
    return {...resultOf(file,r.logs??[]),ms:Math.round(performance.now()-t0),instructions:r.instructions,clock:r.clock,...(r.errors?.length?{errors:r.errors.slice(0,5)}:{})};
  },cleanup:()=>Deno.remove(served,{recursive:true})} as never;
}

if(import.meta.main) {
  const backend=engineKind==="bench"?await benchBackend():await engineBackend();
  const cases:Case[]=[];
  const started=new Date().toISOString();
  for(const dir of dirs) for(const t of testsOf(dir)) {
    if(only&&!t.file.includes(only))continue;
    if(t.skip){cases.push({file:t.file,harness:"SKIP",message:t.skip,subtests:[]});continue;}
    let c:Case;
    try{c=await backend.run(t.file);}catch(e){c={file:t.file,harness:"ERROR",message:String((e as Error).message??e).slice(0,300),subtests:[]};}
    cases.push(c);
    const pass=c.subtests.filter(s=>s.status==="PASS").length;
    console.error(`${c.harness.padEnd(9)} ${String(pass).padStart(3)}/${String(c.subtests.length).padEnd(3)} ${c.file} ${c.ms??""}ms`);
  }
  const byDir:Record<string,{files:number;run:number;skipped:number;harnessOK:number;subtests:number;pass:number}>={};
  for(const dir of dirs) {
    const cs=cases.filter(c=>c.file.startsWith(dir+"/"));
    byDir[dir]={files:cs.length,run:cs.filter(c=>c.harness!=="SKIP").length,skipped:cs.filter(c=>c.harness==="SKIP").length,
      harnessOK:cs.filter(c=>c.harness==="OK").length,subtests:cs.reduce((n,c)=>n+c.subtests.length,0),
      pass:cs.reduce((n,c)=>n+c.subtests.filter(s=>s.status==="PASS").length,0)};
  }
  const hash=async(path:string)=>{try{return [...new Uint8Array(await crypto.subtle.digest("SHA-256",await Deno.readFile(path)))].map(b=>b.toString(16).padStart(2,"0")).join("");}catch{return null;}};
  const report={format:"factoidal-wpt-testharness-v1",measuredAt:started,
    scope:"WPT testharness.js tests, window variant, in the engine's script session (QuickJS-NG in WasmVM, Lean DOM arena, Lean event loop, virtual clock). Subtest counts are of the subtests a page reported; a page that reported none counts 0 of 0.",
    wptCommit:"ce5ca39646886a9349fc42913f843ec6e1c8a36f",engine:engineKind,info:backend.info,
    quickjsWasmSha256:await hash(quickjs),runnerSha256:await hash(fromFileUrl(import.meta.url)),
    reportSha256:await hash(join(here,"testharnessreport.js")),
    directories:byDir,
    totals:{files:cases.length,run:cases.filter(c=>c.harness!=="SKIP").length,subtests:cases.reduce((n,c)=>n+c.subtests.length,0),
      pass:cases.reduce((n,c)=>n+c.subtests.filter(s=>s.status==="PASS").length,0)},
    cases};
  for(const [d,v] of Object.entries(byDir))console.log(`${d}: ${v.pass}/${v.subtests} subtests pass; ${v.harnessOK}/${v.run} pages OK; ${v.skipped} skipped`);
  console.log(`total: ${report.totals.pass}/${report.totals.subtests} subtests pass`);
  if(opt("--out"))await Deno.writeTextFile(opt("--out"),JSON.stringify(report,null,1)+"\n");
  // @ts-ignore bench backend only
  await backend.cleanup?.();
  if(opt("--baseline")) {
    const base=JSON.parse(await Deno.readTextFile(opt("--baseline"))) as {cases:Case[]};
    const now=new Map(cases.map(c=>[c.file,c]));
    const lost:string[]=[];
    for(const c of base.cases) {
      const n=now.get(c.file);if(!n)continue;
      for(const s of c.subtests)if(s.status==="PASS"&&n.subtests.find(x=>x.name===s.name)?.status!=="PASS")lost.push(`${c.file}: ${s.name}`);
    }
    if(lost.length){console.log(`${lost.length} subtests passed in the baseline and do not now:`);for(const l of lost.slice(0,40))console.log("  "+l);Deno.exit(1);}
    console.log("no subtest that passed in the baseline fails now");
  }
}
