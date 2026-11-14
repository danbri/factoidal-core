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
//   deno run -A tests/browser-wpt/testharness-run.ts [--engine native|wasm|bench] [--script-engine bubblepop|quickjs] [--exclude a,b] [--wpt-root DIR]
//     [--native-engine DYLIB] [--quickjs-wasm FILE] [--dirs a,b] [--only SUBSTRING]
//     [--out FILE] [--baseline FILE] [--bench EXE] [--instructions-per-ms N]
//     [--encoding-fallback detect|locale|LABEL] [--locale TAG]
//     [--wpt-root DIR --list FILE [--wptserve] [--jsonl FILE] [--wpt-commit SHA] [--test262-inline]]
//
// --wpt-root and --list run any WPT checkout's tests by their wpt.fyi names, one a line
// (`/dom/nodes/Node-cloneNode.html`, `/url/a.any.html?include=x`, `/x/y.window.html`,
// `/third_party/test262/test/.../z.test262.html`). Each name is mapped to its file the
// way wptserve maps it: `.any.html` and `.window.html` get their wrappers, the query
// stays in the page's URL (`?include=`, `?1-1000` variants), `.sub.` pages get the
// common wptserve substitutions. Names this engine cannot run are counted, not run:
// the variants this engine lacks the API for (worker, shared worker, service worker,
// ShadowRealm, module: SKIP "not supported by engine", kind "engine", found by a probe of
// the engine once a process); pages without testharness.js (reftests, crashtests, visual
// and manual tests). Test262 pages are
// wptserve's: an outer testharness page whose test runs in an iframe; --test262-inline
// instead runs the iframe's page itself as the top-level page (a diagnostic, not a WPT
// result). --jsonl appends each case as it ends and skips names already there, so a
// killed run resumes; with `--list`, only `--dirs` is ignored.
//
// --wptserve (with --wpt-root and --list): WPT test mode. Every page is loaded from a
// local wptserve (wpt-score.py serve; started here if none answers) at
// http://web-platform.test:8000/<name> (https://web-platform.test:8443/ for `.https.`
// names, www. for `.www.`), and the host fetches the page and its scripts over HTTP, so
// wptserve's wrappers, `.sub.` substitution, .headers files, pipes, handlers and other
// origins (www1, not-web-platform.test, port 8001, ...) behave as in a browser run.
// WPT's hostnames reach 127.0.0.1 only through wpt-hosts.ts, in this mode only; HTTPS
// trusts WPT's test CA for this process only; any other host is refused. The one file
// the runner still supplies itself is /resources/testharnessreport.js (ours: results as
// console lines), as wptrunner does for each browser. Variants run when the engine has
// their API (a worker variant once Worker exists).
//
// --engine native (default): the engine library labs/demos/foafnaut/.build/web-render/
// engines/libweb-render.dylib. wasm: the engine's Wasm build. bench: the same session
// through `lake exe wasmvm-bench page` (formal/lean4), for work on the guest without an
// engine build. With --baseline, the run fails when a subtest that passed there fails.
// --script-engine bubblepop (the default since 2026-11-13) runs the pages' scripts on BubblePopJS, the JavaScript engine
// written in Lean (engine:"bubblepop" in the start request, WasmVM/Hosts/LeanJS.lean): the engine Foafnaut uses, so the one
// WPT scores are quoted for. --script-engine quickjs runs QuickJS-NG in WasmVM instead, kept for differential testing.
// QuickJS's guest (--quickjs-wasm) has tools/wasmvm/quickjs/prelude.js compiled in, so it must be built from the same
// commit as the engine (tools/wasmvm/build-quickjs.sh); an older guest silently lacks newer page APIs. On 2026-11-13 a
// whole-WPT run on the default guest of 11-09 reported ~800k subtests failing that pass on BubblePopJS.
import {dirname,join,resolve} from "node:path";
import {fileURLToPath as fromFileUrl} from "node:url";
import {wptDomains,wptFetcher,wptPorts,wptRoute,wptSubdomains,type WptServe} from "./wpt-hosts.ts";

const args=Deno.args,opt=(name:string,fallback="")=>{const i=args.indexOf(name);return i>=0?args[i+1]:fallback;};
const here=dirname(fromFileUrl(import.meta.url)),root=resolve(here,"../.."),
  wpt=resolve(opt("--wpt-root",join(root,"third_party/testing/wpt-scripting")));
// The pinned WPT copies, one tree to the tests: a path is in the first copy that has it
// (the --wpt-root checkout, or wpt-scripting, first).
const roots=[...new Set([wpt,...["wpt-scripting","wpt-encoding","wpt-url","wpt-webapis","wpt-wasm"].map(r=>join(root,"third_party/testing",r))])];
const exists=(p:string)=>{try{Deno.statSync(p);return true;}catch{return false;}};
const wptFile=(path:string)=>join(roots.find(r=>exists(join(r,path)))??wpt,path);
const engineKind=opt("--engine","native");
const scriptEngine=opt("--script-engine","bubblepop");
const quickjs=opt("--quickjs-wasm",join(Deno.env.get("HOME")??"","working/qjs-wasm/qjs-wasmvm.wasm"));
export const directories=["html/webappapis/timers","html/webappapis/microtask-queuing","dom/events","dom/nodes",
  "html/webappapis/scripting/event-loops"];
const dirs=opt("--dirs")?opt("--dirs").split(","):directories;
const only=opt("--only");
// --encoding-fallback detect|locale|LABEL and --locale TAG: the browser's setting for pages that
// declare no encoding and the system's language (WHATWG.Encoding.Sniff; default detect, en).
const pageFallback=opt("--encoding-fallback",""),pageLocale=opt("--locale","en");
// --exclude a,b: files whose path holds one of these are counted SKIP ("excluded").
const excluded=opt("--exclude")?opt("--exclude").split(","):[];
const origin="http://web-platform.test",secureOrigin="https://web-platform.test";
// --wptserve: WPT test mode. Pages, scripts and data come from a local wptserve over HTTP
// (and HTTPS with WPT's test CA) by WPT's own hostnames, mapped to 127.0.0.1 by
// wpt-hosts.ts for this process only. Without it, the runner reads the files of the
// checkout and makes wptserve's wrappers itself (the older path).
const wptserveMode=args.includes("--wptserve");
const serveSpec:WptServe={domains:wptDomains,subdomains:wptSubdomains,ports:wptPorts};
const serveOrigin=`http://web-platform.test:${wptPorts.http[0]}`,serveSecureOrigin=`https://web-platform.test:${wptPorts.https[0]}`;
let serve:{fetcher:ReturnType<typeof wptFetcher>;stop?:()=>Promise<void>}|undefined;
const isWptHost=(url:string)=>wptserveMode?!("refused" in wptRoute(url,serveSpec)):[origin,secureOrigin].includes(new URL(url).origin);
/** Reach the local wptserve, or start one (wpt-score.py serve) that stops with this process. */
async function startServe() {
  try{serveSpec.caPEM=await Deno.readTextFile(join(wpt,"tools/certs/cacert.pem"));}catch{/* HTTPS pages then fail: no CA */}
  const fetcher=wptFetcher(serveSpec);
  const up=async()=>{try{const r=await fetcher.fetch(`${serveOrigin}/resources/testharness.js`,{signal:AbortSignal.timeout(3000)});await r.body?.cancel();return r.ok;}catch{return false;}};
  if(await up()){serve={fetcher};return;}
  const child=new Deno.Command("python3",{args:[join(here,"wpt-score.py"),"serve","--wpt-root",wpt],stdout:"null",stderr:"null"}).spawn();
  for(let i=0;i<120&&!(await up());i++)await new Promise(r=>setTimeout(r,500));
  if(!(await up())){try{child.kill();}catch{/* gone */}throw new Error(`wptserve did not start for ${wpt} (python3 tests/browser-wpt/wpt-score.py serve --wpt-root ${wpt})`);}
  serve={fetcher,stop:async()=>{try{child.kill("SIGINT");}catch{/* gone */}await child.status.catch(()=>{});}};
}
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
export type Case={file:string;harness:string;kind?:string;message?:string|null;subtests:Subtest[];ms?:number;instructions?:number;
  clock?:number;errors?:string[]};

/** The tests of a directory: its own files that are testharness tests a window runs. */
export function testsOf(dir:string):{file:string;skip?:string}[] {
  const out:{file:string;skip?:string}[]=[];
  for(const e of [...Deno.readDirSync(wptFile(dir))].sort((a,b)=>a.name<b.name?-1:1)) {
    if(!e.isFile)continue;
    const n=e.name,file=`${dir}/${n}`;
    if(n.endsWith(".any.js")||n.endsWith(".window.js")) {
      const meta=metaOf(Deno.readTextFileSync(wptFile(file)));
      const globals=meta.filter(([k])=>k==="global").map(([,v])=>v).join(",");
      if(globals&&!/(^|,)\s*(window|default)\b/.test(globals)&&n.endsWith(".any.js"))out.push({file,skip:"no window global"});
      else out.push({file});
      // workers: the dedicated worker variant (wptserve's default globals are window and
      // dedicatedworker), on an engine with Worker (BubblePopJS)
      if(n.endsWith(".any.js")&&(!globals||/(^|,)\s*(default|worker|dedicatedworker)\b/.test(globals)))
        out.push(scriptEngine==="bubblepop"?{file:file.replace(/\.js$/,".worker.html")}:{file:file.replace(/\.js$/,".worker.html"),skip:"worker (BubblePopJS only)"});
    } else if(n.endsWith(".worker.js"))out.push(scriptEngine==="bubblepop"?{file:file.replace(/\.js$/,".html")}:{file,skip:"worker"});
    else if(n.endsWith(".html")||n.endsWith(".xhtml")) {
      const text=Deno.readTextFileSync(wptFile(file));
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
  const meta=metaOf(Deno.readTextFileSync(wptFile(file)));
  const title=meta.find(([k])=>k==="title")?.[1];
  const long=meta.some(([k,v])=>k==="timeout"&&v==="long");
  // A relative META script is relative to the test file (the generated page may live elsewhere).
  const scripts=meta.filter(([k])=>k==="script").map(([,v])=>v.startsWith("/")?v:new URL(v,`${origin}/${file}`).pathname);
  return `<!doctype html>\n<meta charset=utf-8>\n${long?'<meta name="timeout" content="long">\n':""}${title?`<title>${escapeHTML(title)}</title>\n`:""}`+
    `<script>\nself.GLOBAL = {isWindow: function() { return true; }, isWorker: function() { return false; }, isShadowRealm: function() { return false; }};\n</script>\n`+
    `<script src="/resources/testharness.js"></script>\n<script src="/resources/testharnessreport.js"></script>\n`+
    scripts.map(s=>`<script src="${escapeHTML(s)}"></script>\n`).join("")+dataShim(file)+
    `<div id=log></div>\n<script src="/${file}"></script>\n`;
}
// ==== workers: wptserve's dedicated worker variant of a .any.js test (tools/serve/serve.py
// WorkersHandler and AnyWorkerHandler), and the engine's script fetches ====
/** The `.any.worker.html` page: testharness.js takes the worker's results. */
export function workerWrapper(file:string,query=""):string {
  const meta=metaOf(Deno.readTextFileSync(wptFile(file)));
  const long=meta.some(([k,v])=>k==="timeout"&&v==="long");
  // x.any.js runs as x.any.worker.js; a x.worker.js test is its own worker script
  const script=file.endsWith(".any.js")?file.replace(/\.js$/,".worker.js"):file;
  return `<!doctype html>\n<meta charset=utf-8>\n${long?'<meta name="timeout" content="long">\n':""}`+
    `<script src="/resources/testharness.js"></script>\n<script src="/resources/testharnessreport.js"></script>\n<div id=log></div>\n`+
    `<script>\nfetch_tests_from_worker(new Worker("/${script}${query}"));\n</script>\n`;
}
/** The `.any.worker.js` script: the worker's globals, testharness.js, the META scripts, the test, done(). */
export function workerScript(file:string):string {
  const meta=metaOf(Deno.readTextFileSync(wptFile(file)));
  const quote=(v:string)=>v.replace(/\\/g,"\\\\").replace(/"/g,'\\"');
  const title=meta.find(([k])=>k==="title")?.[1];
  return (title?`self.META_TITLE = "${quote(title)}";\n`:"")+
    `self.GLOBAL = {\n  isWindow: function() { return false; },\n  isWorker: function() { return true; },\n  isShadowRealm: function() { return false; },\n};\n`+
    `importScripts("/resources/testharness.js");\n`+
    meta.filter(([k])=>k==="script").map(([,v])=>`importScripts("${quote(v)}")\n`).join("")+
    `importScripts("/${file}");\ndone();\n`;
}
// ==== end workers ====

// A test that loads its own JSON data with fetch("resources/x.json") (url/) gets that data
// from a runner shim, since page scripts have no fetch: the shim answers only those files.
function dataShim(file:string):string {
  const text=Deno.readTextFileSync(wptFile(file));
  const names=[...new Set([...text.matchAll(/fetch\("(resources\/[\w.-]+\.json)"\)/g)].map(m=>m[1]))];
  if(!names.length)return "";
  const dir=file.slice(0,file.lastIndexOf("/")+1);
  return shimScript(Object.fromEntries(names.map(n=>[n,Deno.readTextFileSync(wptFile(dir+n))])));
}
/** The shim: a `fetch` that answers only the test's own data files (by their relative URL). */
function shimScript(data:Record<string,string>):string {
  return `<script>/* runner shim: the test's own data files */(()=>{const data=${JSON.stringify(data).replace(/<\//g,"<\\/")};`+
    `self.fetch=u=>data[u]===undefined?Promise.reject(new TypeError("runner shim: no "+u)):Promise.resolve({ok:true,json:()=>Promise.resolve(JSON.parse(data[u]))});})();</script>\n`;
}
const pageOf=(file:string)=>file.endsWith(".js")?file.replace(/\.js$/,".html"):file;
/** A script URL of the test origin as a file: our testharnessreport.js, else the pinned WPT file. */
function scriptFile(url:string):string|undefined {
  const u=new URL(url);
  if(u.origin!==origin&&u.origin!==secureOrigin)return undefined;
  if(u.pathname==="/resources/testharnessreport.js")return join(here,"testharnessreport.js");
  // test_driver's vendor file is the runner's too (key input of the user: scriptSession action `key`).
  if(u.pathname==="/resources/testdriver-vendor.js")return join(here,"testdriver-vendor.js");
  // wptserve's one rewrite (tools/serve/serve.py `rewrites`).
  const pathname=u.pathname==="/resources/WebIDLParser.js"?"/resources/webidl2/lib/webidl2.js":u.pathname;
  const path=wptFile(decodeURIComponent(pathname));
  return roots.some(r=>path.startsWith(r+"/"))?path:undefined;
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

// ---- tests named as wpt.fyi names them (--list) ---------------------------------------
/** A wpt.fyi test name as this runner runs it: the page and its URL, or why it is not run. */
export type Named={file:string;html?:string;url?:string;skip?:string;kind:string};
/** The variants wpt.fyi runs of a test (wptserve's `.any.js` variants and the rest), with
 * the engine features each one needs beyond a window with classic scripts. */
export const variants:[RegExp,string,string[]][]=[
  [/\.any\.worker\.html$/,"dedicated worker variant",["Worker"]],[/\.any\.sharedworker\.html$/,"shared worker variant",["SharedWorker"]],
  [/\.any\.serviceworker\.html$/,"service worker variant",["serviceWorker"]],[/\.any\.worker-module\.html$/,"module worker variant",["Worker","module scripts"]],
  [/\.any\.sharedworker-module\.html$/,"module shared worker variant",["SharedWorker","module scripts"]],
  [/\.any\.serviceworker-module\.html$/,"module service worker variant",["serviceWorker","module scripts"]],
  [/\.any\.shadowrealm[a-z-]*\.html$/,"ShadowRealm variant",["ShadowRealm"]],[/\.any\.window-module\.html$/,"module script variant",["module scripts"]],
  [/\.worker\.html$/,"worker test",["Worker"]],[/\.test262-module\.html$/,"Test262 module test",["module scripts"]],
  [/\.extension\.html$/,"browser extension test",["browser extensions"]]];
/** The engine features a test name needs that this engine lacks (`features`: the probe's answer). */
export function missingFeatures(path:string,features:Record<string,boolean>):{why:string;missing:string[]}|undefined {
  for(const [re,why,needs] of variants)if(re.test(path))return {why,missing:needs.filter(f=>!features[f])};
  return undefined;
}
/** What the engine has, probed once a process: the APIs a variant needs. */
export let engineFeatures:Record<string,boolean>={};
const testharnessPage=/\.(html?|xhtml|xht|svg|xml)$/;
/** wptserve's common `.sub.` substitutions, with the runner's one origin on ports 80 and 443. */
export function substitute(text:string,query:string):string {
  const get=new URLSearchParams(query);
  return text.replace(/\{\{([^}]*)\}\}/g,(whole,expr:string)=>{
    const e=expr.trim().replace(/^[a-z_]+:/,"");
    if(/^(host|domains\[[^\]]*\]|hosts\[[^\]]*\]\[[^\]]*\])$/.test(e))return "web-platform.test";
    if(/^ports\[http\]\[\d\]$/.test(e))return "80";
    if(/^ports\[https\]\[\d\]$/.test(e))return "443";
    if(/^ports\[(ws|wss|h2|webtransport-h3)\]\[\d\]$/.test(e))return "0";
    let m=/^GET\[([^\]]*)\]$/.exec(e);if(m)return get.get(m[1])??"";
    if(e==="location[host]"||e==="location[hostname]")return "web-platform.test";
    if(e==="location[scheme]")return "http";
    if(e==="uuid()")return crypto.randomUUID();
    m=/^header_or_default\([^,]*,\s*(.*)\)$/.exec(e);if(m)return m[1].replace(/^["']|["']$/g,"");
    return whole;
  });
}
/** Test262's frontmatter: includes, flags and negative, as WPT's manifest parses them. */
export function test262Record(text:string){
  const fm=/\/\*---([\s\S]*?)---\*\//.exec(text)?.[1]??"";
  const list=(key:string)=>{const m=new RegExp(`^${key}:\\s*\\[([^\\]]*)\\]`,"m").exec(fm);
    if(m)return m[1].split(",").map(x=>x.trim()).filter(Boolean);
    const b=new RegExp(`^${key}:\\s*\\n((?:\\s+-\\s*.*\\n?)*)`,"m").exec(fm);
    return b?b[1].split("\n").map(x=>x.replace(/^\s*-\s*/,"").trim()).filter(Boolean):[];};
  const neg=/^negative:\s*\n((?:\s+.*\n?)*)/m.exec(fm)?.[1]??"";
  const negative=neg?{phase:/phase:\s*(\S+)/.exec(neg)?.[1]??"",type:/type:\s*(\S+)/.exec(neg)?.[1]??""}:null;
  const flags=list("flags");
  return {includes:list("includes"),flags,negative,isAsync:flags.includes("async")};
}
/** wptserve's Test262 test page (Test262WindowTestBaseHandler), the page its iframe loads. */
function test262Inner(source:string,strict:boolean):string {
  const r=test262Record(Deno.readTextFileSync(join(wpt,source)));
  const meta=(r.negative?`<script>test262Negative('${r.negative.type}', '${r.negative.phase}')</script>\n`:"")+
    (r.isAsync?"<script>test262IsAsync(true)</script>\n":"");
  const scripts=r.includes.map(f=>`<script src="/third_party/test262/harness/${escapeHTML(f)}"></script>\n`).join("")+
    (r.isAsync?'<script src="/third_party/test262/harness/doneprintHandle.js"></script>\n':"");
  return `<!doctype html>\n<meta charset=utf-8>\n<title>Test</title>\n<script src="/resources/test262/test262-reporter.js"></script>\n`+
    `<script src="/third_party/test262/harness/assert.js"></script>\n<script src="/third_party/test262/harness/sta.js"></script>\n`+
    `<script src="/resources/test262/test262-provider.js"></script>\n${meta}${scripts}`+
    `<body><script>test262Setup()</script>\n<script src="/${source}${strict?"?strict":""}" onerror="test262ScriptError()"></script></body>`;
}
const test262Outer=(inner:string)=>`<!doctype html>\n<meta charset=utf-8>\n<title>Test</title>\n`+
  `<script src="/resources/testharness.js"></script>\n<script src="/resources/testharnessreport.js"></script>\n<script>\n`+
  `const t = async_test(document.title);\nwindow.test262HarnessDone = t.step_func_done(function(status, message) {\n`+
  `    if (status === 1) {\n        throw new Error(message || "Test failed");\n    } else if (status === 2) {\n`+
  `        throw new Error(message || "Harness Error");\n    }\n});\n</script>\n`;
/** The outer page as wptserve serves it (its iframe, `inner`, needs a document of its own),
 * or with --test262-inline the inner page run at top level under the outer page's test. */
function test262Page(source:string,id:string,strict:boolean):string {
  const inner=test262Inner(source,strict);
  if(!args.includes("--test262-inline"))
    return test262Outer(inner)+`<div id=log></div>\n<iframe id="test262-iframe" src="/${escapeHTML(id.replace(/\.test262(\.strict)?\.html$/,strict?".test262-test.strict.html":".test262-test.html"))}"></iframe>`;
  return test262Outer(inner)+inner.replace(/^<!doctype html>\n<meta charset=utf-8>\n<title>Test<\/title>\n/,"");
}
/** A wpt.fyi name in --wptserve mode: the URL wptserve serves it at (it makes the wrappers,
 * substitutions and headers itself), once the checkout says it is a testharness test. */
function servedName(id:string,path:string,url:string,exists:(f:string)=>boolean):Named {
  const source=/\.any(\.[a-z-]+)?\.html$/.test(path)?path.replace(/\.any(\.[a-z-]+)?\.html$/,".any.js"):
    /\.(window|worker)\.html$/.test(path)?path.replace(/\.html$/,".js"):path.replace(/\.test262(-module)?(\.strict)?\.html$/,".js");
  if(!exists(source))return {file:id,kind:"missing",skip:`not in the checkout: ${source}`};
  if(/\.h2\./.test(path))return {file:id,kind:"runner",skip:"needs wptserve's HTTP/2 server (not started)"};
  const kind=/\.test262/.test(path)?"test262":/\.any\.html$/.test(path)?"any":/\.any\.[a-z-]+\.html$/.test(path)?path.replace(/^.*\.any\.([a-z-]+)\.html$/,"any-$1"):
    /\.(window|worker)\.html$/.test(path)?path.replace(/^.*\.(window|worker)\.html$/,"$1"):"testharness";
  // wpt.fyi's .py names are wdspec tests: pytest drives a browser over WebDriver (webdriver/)
  // or reads its accessibility tree (aria/, core-aam/, mathml-aam/). wptserve has no page for them.
  if(kind==="testharness"&&path.endsWith(".py"))return {file:id,kind:"wdspec",skip:"wdspec (pytest over WebDriver or an accessibility API), not a page"};
  if(kind==="testharness"){
    if(!testharnessPage.test(path))return {file:id,kind:"other",skip:"not a testharness page"};
    // NULs out: a UTF-16 page (html/infrastructure/urls/.../utf-16le.html) names the harness too.
    const text=Deno.readTextFileSync(join(wpt,path)).replace(/\0/g,"");
    if(!text.includes("/resources/testharness.js"))
      return {file:id,kind:"reftest",skip:/(-crash|crashtests\/)/.test(path)?"crashtest":/-manual\./.test(path)?"manual":"not testharness.js (reftest or visual)"};
    if(/-manual\./.test(path))return {file:id,kind:"manual",skip:"manual"};
  }
  if(kind==="test262"&&args.includes("--test262-inline")){
    const m=/^(.*)\.test262(\.strict)?\.html$/.exec(path)!;
    return {file:id,kind,url,html:test262Page(`${m[1]}.js`,id,!!m[2])};
  }
  return {file:id,kind,url};
}
/** A wpt.fyi test name (with or without its leading slash) as a page to run, or why not. */
export function named(name:string):Named {
  const id=name.replace(/^\//,""),q=id.indexOf("?"),path=q>=0?id.slice(0,q):id,query=q>=0?id.slice(q):"";
  const secure=/\.https\./.test(path)||path.includes("/https/");
  // wptrunner's name flags: `.https.` loads over HTTPS, `.www.` from the www subdomain.
  const url=wptserveMode?`${(secure?serveSecureOrigin:serveOrigin).replace("//web-platform",/\.www\./.test(path)?"//www.web-platform":"//web-platform")}/${id}`:
    `${secure?secureOrigin:origin}/${id}`;
  const variant=missingFeatures(path,engineFeatures);
  if(variant?.missing.length)return {file:id,kind:"engine",skip:`not supported by engine: ${variant.missing.join(", ")} (${variant.why})`};
  // workers: without --wptserve, a dedicated worker variant on an engine with Worker
  // (BubblePopJS) runs from the wrapper wptserve would generate (workerWrapper, workerScript)
  if(variant&&!wptserveMode&&engineFeatures.Worker){
    const has=(f:string)=>{try{return Deno.statSync(join(wpt,f)).isFile;}catch{return false;}};
    let w=/^(.*)\.any\.worker\.html$/.exec(path);
    if(w){const source=`${w[1]}.any.js`;
      if(!has(source))return {file:id,kind:"missing",skip:`not in the checkout: ${source}`};
      return {file:id,kind:"worker",url,html:workerWrapper(source,query)};}
    w=/^(.*)\.worker\.html$/.exec(path);
    if(w&&!/\.(shared|service)worker\.html$/.test(path)&&has(`${w[1]}.worker.js`))
      return {file:id,kind:"worker",url,html:workerWrapper(`${w[1]}.worker.js`,query)};
  }
  if(variant&&!wptserveMode)return {file:id,kind:"runner",skip:`${variant.why}: run with --wptserve`};
  const exists=(f:string)=>{try{return Deno.statSync(join(wpt,f)).isFile;}catch{return false;}};
  if(wptserveMode)return servedName(id,path,url,exists);
  let m=/^(.*)\.(any|window)\.html$/.exec(path);
  if(m){const source=`${m[1]}.${m[2]}.js`;
    if(!exists(source))return {file:id,kind:"missing",skip:`not in the checkout: ${source}`};
    return {file:id,kind:m[2],url,html:wrapper(source)};}
  m=/^(.*)\.test262(\.strict)?\.html$/.exec(path);
  if(m){const source=`${m[1]}.js`;
    if(!exists(source))return {file:id,kind:"missing",skip:`not in the checkout: ${source}`};
    return {file:id,kind:"test262",url,html:test262Page(source,id,!!m[2])};}
  if(!exists(path))return {file:id,kind:"missing",skip:`not in the checkout: ${path}`};
  if(!testharnessPage.test(path))return {file:id,kind:"other",skip:"not a testharness page"};
  let text=Deno.readTextFileSync(join(wpt,path));
  if(!text.includes("/resources/testharness.js"))
    return {file:id,kind:"reftest",skip:/(-crash|crashtests\/)/.test(path)?"crashtest":/-manual\./.test(path)?"manual":"not testharness.js (reftest or visual)"};
  if(/-manual\./.test(path))return {file:id,kind:"manual",skip:"manual"};
  if(path.includes(".sub."))text=substitute(text,query);
  return {file:id,kind:"testharness",url,html:text};
}

// ---- the engine backend -------------------------------------------------------------
type Run=(file:string,page?:{html?:string;url:string})=>Promise<Case>;
/** A script turn, with the worker script fetches it waits for (an engine with Workers). */
type ScriptTurnWithFetches={session:number;logs:string[];errors:string[];instructions:number;fetches?:{id:number;url:string;kind?:string}[]};
async function engineBackend():Promise<{run:Run;info:Record<string,unknown>;engine?:unknown}> {
  const {loadHTML}=await import("../../labs/demos/foafnaut/native_html_engine.ts");
  const engine=await loadHTML(engineKind==="wasm"?undefined:opt("--native-engine",join(root,"labs/demos/foafnaut/.build/web-render/engines/libweb-render.dylib")));
  const info={...engine.scriptInfo(),scriptEngine};
  if(scriptEngine==="bubblepop"&&!(info.engines??[]).includes("bubblepop"))throw new Error("this engine has no BubblePopJS");
  if(scriptEngine!=="bubblepop"&&!args.includes("--quickjs-wasm"))
    console.error(`warning: QuickJS guest ${quickjs} (modified ${(await Deno.stat(quickjs)).mtime?.toISOString()}); `+
      "its prelude must come from the same commit as the engine, or pass --quickjs-wasm FILE built from it");
  const guest=scriptEngine==="bubblepop"?undefined:await Deno.readFile(quickjs);
  if(guest)engine.scriptLoad(guest);
  // A page the engine refuses (a script over its size bound) can leave the session without
  // its guest; load it again then, so one refused page does not fail every later one.
  const start=(html:string,request:Record<string,unknown>)=>{
    try{return engine.scriptSession(html,request);}
    catch(e){if(!guest||!/no guest module/.test(String(e)))throw e;engine.scriptLoad(guest);return engine.scriptSession(html,request);}
  };
  // The probe: which of the APIs that WPT's variants need this engine defines.
  try{
    const probe=start(`<!doctype html><script>console.log("__probe "+JSON.stringify({Worker:typeof Worker!=="undefined",SharedWorker:typeof SharedWorker!=="undefined",`+
      `serviceWorker:typeof navigator!=="undefined"&&!!navigator.serviceWorker,ShadowRealm:typeof ShadowRealm!=="undefined",fetch:typeof fetch!=="undefined",`+
      `XMLHttpRequest:typeof XMLHttpRequest!=="undefined",postMessage:typeof postMessage!=="undefined"}))</script>`+
      `<script type=module>console.log("__probe_module")</script>`,{action:"start",url:`${origin}/probe.html`,resources:[],
      ...(scriptEngine==="bubblepop"?{engine:"bubblepop"}:{})});
    const logs=[...probe.logs,...engine.scriptSession("",{action:"settle",session:probe.session,budgetMs:1000}).logs];
    engine.scriptSession("",{action:"close"});
    const line=logs.find(l=>l.startsWith("__probe {"));
    engineFeatures={...(line?JSON.parse(line.slice(8)):{}),"module scripts":logs.includes("__probe_module")};
  }catch{engineFeatures={};}
  (info as Record<string,unknown>).features=engineFeatures;
  let heldCanvasFont=false;
  // Web fonts given to the engine in this process, by URL: the SHA-256 it holds them by ("" when refused).
  const fontShas=new Map<string,string>();
  // What the host reads: files of the pinned copies (the default), or, with --wptserve,
  // the local wptserve over HTTP by WPT's own hostnames (wpt-hosts.ts), as a browser run does.
  const http=serve?.fetcher;
  const readText=async(url:string):Promise<string|undefined>=>{
    if(new URL(url).pathname==="/resources/testharnessreport.js"&&isWptHost(url))return await Deno.readTextFile(join(here,"testharnessreport.js"));
    // test_driver's vendor file is the runner's too (testdriver-vendor.js of this directory).
    if(new URL(url).pathname==="/resources/testdriver-vendor.js"&&isWptHost(url))return await Deno.readTextFile(join(here,"testdriver-vendor.js"));
    if(http){try{const r=await http.fetch(url);if(!r.ok){await r.body?.cancel();return undefined;}return await r.text();}catch{return undefined;}}
    const path=scriptFile(url);if(!path)return undefined;
    try{let source=await Deno.readTextFile(path);
      if(path.includes(".sub."))source=substitute(source,new URL(url).search);
      else if(/\/test262\/test\/.*\.js$/.test(path)&&new URL(url).search==="?strict")source='"use strict";\n'+source;
      return source;}catch{return undefined;}
  };
  const readBytes=async(url:string):Promise<Uint8Array|undefined>=>{
    if(http){try{const r=await http.fetch(url);if(!r.ok){await r.body?.cancel();return undefined;}return new Uint8Array(await r.arrayBuffer());}catch{return undefined;}}
    const path=scriptFile(url);if(!path)return undefined;
    try{return await Deno.readFile(path);}catch{return undefined;}
  };
  /** The host's answer to one script fetch of a worker: status 0 is a network error. */
  const hostFetch=async(f:{id:number;url:string}):Promise<{id:number;status:number;url:string;contentType:string;contentTypeOptions?:string;source:string}>=>{
    const failed={id:f.id,status:0,url:f.url,contentType:"",source:""};
    if(http&&new URL(f.url).pathname!=="/resources/testharnessreport.js"){
      try{const r=await http.fetch(f.url);
        // The type and X-Content-Type-Options as the server sent them: Lean decides (nosniff, LeanJSWorkers.scriptAccepted).
        return {id:f.id,status:r.status,url:(r as Response&{finalURL?:string}).finalURL??f.url,contentType:r.headers.get("content-type")??"",
          contentTypeOptions:r.headers.get("x-content-type-options")??"",source:await r.text()};}
      catch{return failed;}
    }
    // workers: the .any.worker.js that wptserve generates, made here from the pinned .any.js
    const u=new URL(f.url);
    let source:string|undefined;
    if(/\.any\.worker\.js$/.test(u.pathname)&&isWptHost(f.url)){try{source=workerScript(decodeURIComponent(u.pathname).slice(1).replace(/\.worker\.js$/,".js"));}catch{/* not in the checkout */}}
    else source=await readText(f.url);
    return source===undefined?failed:{id:f.id,status:200,url:f.url,contentType:"text/javascript",source};
  };
  const decode=(bytes:Uint8Array,contentType:string)=>{
    const decoded=(engine as {decodeDocument?:(b:Uint8Array,c:string,f?:string,l?:string)=>{encoding:string;source:string}|undefined}).decodeDocument?.(bytes,contentType,pageFallback,pageLocale);
    return {html:decoded?decoded.source:new TextDecoder().decode(bytes),encoding:decoded?.encoding};
  };
  // A frame's `src` scripts, read as the page's are.
  const resourcesOf=async(html:string,url:string)=>{
    const facts=engine.inspect(html,{url}) as unknown as {scripts:{nodeId:number;src:string;url:string}[]};
    const out:{nodeId:number;source:string}[]=[];
    for(const s of facts.scripts){if(!s.src)continue;const source=await readText(s.url);if(source!==undefined)out.push({nodeId:s.nodeId,source});}
    return out;
  };
  // A frame's document: from wptserve; else as wptserve serves it (Test262's inner page, a
  // .any/.window wrapper, or a file of the copy decoded as a page is); undefined when absent.
  // The encoding name of the frame document frameSource last decoded (the `frame` action's `encoding`).
  let frameEncoding:string|undefined;
  // the URL the last frame document came from (after redirects), when wptserve served it
  let frameFinal:string|undefined;
  const frameSource=async(url:string):Promise<string|undefined>=>{
    frameEncoding=undefined;frameFinal=undefined;
    let u:URL;try{u=new URL(url);}catch{return undefined;}
    if(http){try{const r=await http.fetch(url);if(!r.ok){await r.body?.cancel();return undefined;}frameFinal=(r as Response&{finalURL?:string}).finalURL;const d=decode(new Uint8Array(await r.arrayBuffer()),r.headers.get("content-type")??"");frameEncoding=d.encoding;return d.html;}catch{return undefined;}}
    if(!isWptHost(url))return undefined;
    const path=decodeURIComponent(u.pathname).replace(/^\//,"");
    const m=/^(.*)\.test262-test(\.strict)?\.html$/.exec(path);
    if(m)try{return test262Inner(`${m[1]}.js`,!!m[2]);}catch{return undefined;}
    const w=/^(.*)\.(any|window)\.html$/.exec(path);
    if(w)try{return wrapper(`${w[1]}.${w[2]}.js`);}catch{return undefined;}
    try{
      const file=wptFile(path),bytes=await Deno.readFile(file);
      let contentType="";
      try{contentType=/^content-type:\s*(.*)$/im.exec(await Deno.readTextFile(file+".headers"))?.[1]?.trim()??"";}catch{/* no headers file */}
      const d=decode(bytes,contentType),text=d.html;frameEncoding=d.encoding;
      return path.includes(".sub.")?substitute(text,u.search):text;
    }catch{return undefined;}
  };
  return {info,engine,run:async(file,page)=>{
    // A page's bytes become text in Lean (decodeDocument: the BOM, the charset of its .headers
    // file as wptserve sends it, the meta prescan); an engine without the op reads UTF-8.
    let html:string,encoding:string|undefined,url:string;
    if(page&&page.html!==undefined){html=page.html;url=page.url;}
    else if(page&&http){
      // The page as wptserve serves it: its wrappers, substitutions, headers and redirects.
      const r=await http.fetch(page.url);
      if(!r.ok){await r.body?.cancel();return {file,harness:"ERROR",message:`wptserve: HTTP ${r.status} for ${page.url}`,subtests:[]};}
      ({html,encoding}=decode(new Uint8Array(await r.arrayBuffer()),r.headers.get("content-type")??""));
      url=(r as Response&{finalURL?:string}).finalURL??page.url;
    }
    else if(file.endsWith(".any.worker.html")){html=workerWrapper(file.replace(/\.worker\.html$/,".js"));url=`${origin}/${file}`;}
    else if(file.endsWith(".worker.html")&&exists(wptFile(file.replace(/\.html$/,".js")))){html=workerWrapper(file.replace(/\.html$/,".js"));url=`${origin}/${file}`;}
    else if(file.endsWith(".js")){html=wrapper(file);url=`${origin}/${pageOf(file)}`;}
    else {
      const bytes=await Deno.readFile(wptFile(file));
      let contentType="";
      try{contentType=/^content-type:\s*(.*)$/im.exec(await Deno.readTextFile(wptFile(file)+".headers"))?.[1]?.trim()??"";}catch{/* no headers file */}
      ({html,encoding}=decode(bytes,contentType));url=`${origin}/${pageOf(file)}`;
    }
    const t0=performance.now();
    type Facts={scripts:{nodeId:number;src:string;url:string;kind?:string}[];stylesheets?:{nodeId:number;url:string}[]};
    let facts=engine.inspect(html,{url}) as unknown as Facts;
    const sources=new Map<string,string|undefined>();
    for(const s of facts.scripts)if(s.src&&!sources.has(s.url))sources.set(s.url,await readText(s.url));
    // The url/ tests' own JSON data (fetch("resources/x.json")): page scripts have no fetch,
    // so the runner's shim answers those files, read from wptserve as the page would.
    if(http){
      const names=[...new Set([...sources.values()].flatMap(t=>t?[...t.matchAll(/fetch\("(resources\/[\w.-]+\.json)"\)/g)].map(m=>m[1]):[]))];
      const data:Record<string,string>={};
      for(const n of names){const t=await readText(new URL(n,url).href);if(t!==undefined)data[n]=t;}
      if(names.length){
        // An XML page (.xhtml) parses the script as XML: its text goes in a CDATA section.
        const xml=/\.(xhtml|xht|xml|svg)$/.test(new URL(url).pathname),shim=shimScript(data);
        const at=html.search(/<script/i);
        html=html.slice(0,at<0?html.length:at)+(xml?shim.replace(/^<script>([\s\S]*)<\/script>\n$/,(_,body:string)=>`<script>//<![CDATA[\n${body.replace(/\]\]>/g,"]]]]><![CDATA[>")}\n//]]></script>\n`):shim)+html.slice(at<0?html.length:at);
        facts=engine.inspect(html,{url}) as unknown as Facts;
      }
    }
    const resources=[];
    for(const s of facts.scripts) {
      if(!s.src)continue;
      const source=sources.has(s.url)?sources.get(s.url):await readText(s.url);
      if(source!==undefined)resources.push({nodeId:s.nodeId,source});/* else not served: the page reports it */
    }
    // The page's stylesheet links, fetched as a browser host fetches them (native_html_document.ts),
    // for the layout reads of its scripts (the session's `layout` request): with a sheet missing,
    // a strict layout refuses the page and every read answers zero. At most 64 (the engine's bound).
    const sheetResources:{nodeId:number;source:string;url:string}[]=[],sheetFailures:{nodeId:number;reason:string}[]=[];
    for(const sh of (facts.stylesheets??[]).slice(0,64)){
      const source=await readText(sh.url);
      if(source===undefined)sheetFailures.push({nodeId:sh.nodeId,reason:"not fetched"});
      else sheetResources.push({nodeId:sh.nodeId,source,url:sh.url});
    }
    // The page's web fonts (@font-face), loaded as a browser host loads them
    // (native_html_document.ts loadWebFonts): Lean names the faces the page's text uses
    // (fontFaces), the host fetches the first URL of each that it can and gives the bytes to
    // Lean (webFontLoad: the font policy checks and holds them), and the layout request names
    // them. Without this a page's own fonts (Ahem in most layout tests) are never used, and
    // SVG text, which is drawn and hit only with a held font, is not there at all.
    const webFonts:{url:string;sha256:string}[]=[];
    const hasFace=(t:string)=>/@font-face/i.test(t);
    const fontEngine=engine as unknown as {fontFaces?:(s:string,o:Record<string,unknown>)=>{faces?:{family:string;sources:string[]}[]};webFontLoad?:(b:Uint8Array,sha:string)=>unknown};
    if((hasFace(html)||sheetResources.some(r=>hasFace(r.source)))&&typeof fontEngine.fontFaces==="function"&&typeof fontEngine.webFontLoad==="function"){
      try{
        const faces=fontEngine.fontFaces(html,{url,resources:sheetResources}).faces??[];
        for(const face of faces.slice(0,16))for(const src of face.sources){
          let sha=fontShas.get(src);
          if(sha===undefined){
            sha="";
            const bytes=await readBytes(src);
            if(bytes&&bytes.length<=8*1048576){
              try{const h=[...new Uint8Array(await crypto.subtle.digest("SHA-256",bytes as BufferSource))].map(b=>b.toString(16).padStart(2,"0")).join("");
                fontEngine.webFontLoad(bytes,h);sha=h;}catch{/* the font policy refused it */}
            }
            fontShas.set(src,sha);
          }
          if(sha){webFonts.push({url:src,sha256:sha});break;}
        }
      }catch{/* an engine without the op, or a page it refuses */}
    }
    const layout=sheetResources.length||sheetFailures.length||webFonts.length?{layout:{url,resources:sheetResources,resourceFailures:sheetFailures,...(webFonts.length?{webFonts}:{})}}:{};
    // The images of a canvas test (<img src>), held by the engine by their URL, as a host
    // holds the images it fetched: Canvas 2D draws them (docs/designissues/2026-11-08-canvas-2d.md).
    // The font of the canvas text tests (an @font-face the engine does not load for
    // scripts), held once as the engine's font, as a host holds the fonts it fetched.
    if(file.includes("/canvas/")&&html.includes("CanvasTest")&&!heldCanvasFont){
      const bytes=await readBytes(new URL("/fonts/CanvasTest.ttf",url).href);
      if(bytes)try{engine.fontLoadBytes(bytes,"CanvasTest","canvastest");heldCanvasFont=true;}catch{/* refused */}
    }
    if(file.includes("/canvas/")&&engine.imageLoad)
      for(const m of html.matchAll(/<img[^>]*\ssrc=["']?([^"' >]+)/g)){
        const key=new URL(m[1],url).href,bytes=await readBytes(key);
        if(bytes)try{engine.imageLoad(bytes,key,key);}catch{/* refused */}
      }
    // navigations:true: this runner loads frames' URLs (scriptSession action `frame`).
    let turn=start(html,{action:"start",url,resources,...layout,commandLimit:200000,logLimit:100000,instructionsPerMs:scriptRate,...(encoding?{encoding}:{}),
      navigations:true,...(http?{network:true,pageAddress:"127.0.0.1"}:{}),...(scriptEngine==="bubblepop"?{engine:"bubblepop"}:{})});
    // The engine's page requests in flight (each from one turn): http.fetch to wptserve.
    type NetWire={id:number;method:string;url:string;headers:[string,string][];bodyBase64?:string};
    const inflight=new Map<number,Promise<{id:number;answer:Record<string,unknown>}>>();
    const b64=(u:Uint8Array)=>{let s="";for(let i=0;i<u.length;i+=32768)s+=String.fromCharCode(...u.subarray(i,i+32768));return btoa(s);};
    // pageAddress: wptserve serves every WPT page from 127.0.0.1, so the page is local and the
    // engine asks for no name resolution (Net.PageFetch); a resolve-only wire gets no address.
    const netFetch=async(w:NetWire):Promise<{id:number;answer:Record<string,unknown>}>=>{
      const failed={id:w.id,answer:{id:w.id,status:0}};
      if((w as {resolve?:boolean}).resolve)return {id:w.id,answer:{id:w.id,addresses:[]}};
      if(!http)return failed;
      try{
        const headers=new Headers();for(const [n,v] of w.headers)headers.append(n,v);
        // The host's part of a request, as a browser host's HTTP client has: a User-Agent
        // (navigator.userAgent's value) when the page's script set none.
        if(!headers.has("user-agent"))headers.set("user-agent","Foafnaut");
        const body=w.bodyBase64!==undefined?Uint8Array.from(atob(w.bodyBase64),c=>c.charCodeAt(0)):undefined;
        const r=await http.fetch(w.url,{method:w.method,headers,body,noFollow:true,signal:AbortSignal.timeout(30000)} as RequestInit);
        const bytes=new Uint8Array(await r.arrayBuffer());
        return {id:w.id,answer:{id:w.id,status:r.status,statusText:r.statusText,headers:[...r.headers],bodyBase64:b64(bytes)}};
      }catch{return failed;}
    };
    // A sync XMLHttpRequest (netSync in a turn): the run was undone; answer and it runs again.
    const resolveSync=async(t:ScriptTurnWithFetches):Promise<ScriptTurnWithFetches>=>{
      let r:ScriptTurnWithFetches=t;
      for(let i=0;(r as {netSync?:NetWire}).netSync&&i<4096;i++){
        const answer=(await netFetch((r as unknown as {netSync:NetWire}).netSync)).answer;
        r=engine.scriptSession("",{action:"syncAnswer",session:r.session,answer}) as ScriptTurnWithFetches;
      }
      return r;
    };
    turn=await resolveSync(turn as ScriptTurnWithFetches) as typeof turn;
    const logs=[...turn.logs],errors=[...turn.errors];
    let instructions=turn.instructions;
    // A worker's script and its importScripts: a turn lists what it waits for (fetches, each
    // id once), the host fetches them and answers with action "fetched"; the turn then runs
    // what is due, and the page settles again (the workers record).
    type Fetch={id:number;url:string;kind?:string};
    const answered=new Set<number>();
    const collectNet=(t:{netRequests?:NetWire[]})=>{for(const w of t.netRequests??[])inflight.set(w.id,netFetch(w));};
    const ss=(req:Record<string,unknown>)=>resolveSync(engine.scriptSession("",req) as ScriptTurnWithFetches) as Promise<typeof turn>;
    const take=(t:ScriptTurnWithFetches)=>{logs.push(...t.logs);errors.push(...t.errors);instructions+=t.instructions;collectNet(t as {netRequests?:NetWire[]});};
    collectNet(turn as {netRequests?:NetWire[]});
    const startFetches=(turn as ScriptTurnWithFetches).fetches??[];
    // test_driver (testdriver-vendor.js of this directory): a request of the page leaves it as a
    // console line; it is run as input of the user (scriptSession action `key`). The page then
    // settles in short slices of virtual time, so a request is seen before the test's own
    // timeout runs. Pages without testdriver.js settle in one call, as before.
    const driver=scriptEngine==="bubblepop"&&html.includes("testdriver.js");
    let driverSeen=0;
    const drive=async():Promise<boolean>=>{
      let did=false;
      for(;driverSeen<logs.length;driverSeen++){
        const line=logs[driverSeen];
        if(!line.startsWith("__wpt_driver "))continue;
        let req:{keys?:Record<string,unknown>[]};
        try{req=JSON.parse(line.slice(13));}catch{continue;}
        for(const k of req.keys??[]){take(turn=await ss({...k,action:"key",session:turn.session}));did=true;}
      }
      return did;
    };
    const settleTo=async(budgetMs:number)=>{
      if(!driver){take(turn=await ss({action:"settle",session:turn.session,budgetMs}));return;}
      const stop=turn.clock+budgetMs;
      for(let i=0;i<200000;i++){
        take(turn=await ss({action:"settle",session:turn.session,budgetMs:Math.max(1,Math.min(16,stop-turn.clock))}));
        const did=await drive();
        if(turn.clock>=stop||(!did&&(turn as {quiet?:boolean}).quiet))break;
      }
    };
    await settleTo(70000);
    let pending:Fetch[]=[...startFetches,...((turn as ScriptTurnWithFetches).fetches??[])].filter(f=>!answered.has(f.id));
    for(let round=0;pending.length&&round<1000;round++){
      for(const f of pending)answered.add(f.id);
      const results=await Promise.all(pending.map(hostFetch));
      const given=engine.scriptSession("",{action:"fetched",session:turn.session,results}) as ScriptTurnWithFetches;
      take(given);
      await settleTo(70000);
      pending=[...(given.fetches??[]),...((turn as ScriptTurnWithFetches).fetches??[])].filter((f,i,all)=>!answered.has(f.id)&&all.findIndex(g=>g.id===f.id)===i);
    }
    // Frames and page requests (XMLHttpRequest: `network:true`): answer each navigation with
    // its document and each request from wptserve; the engine decides all (redirect "manual").
    // `elapsedMs` moves the virtual clock by the real time waited, so timers and `timeout` still fire.
    const answerFrames=async()=>{
      for(let round=0;round<256&&turn.clock<70000&&((turn.navigations?.length??0)>0||(turn.frameLoads??0)>0);round++){
        const session=turn.session;
        for(const nav of turn.navigations??[]){
          const source=await frameSource(nav.url);
          // responseUrl: where the document came from after redirects; the engine takes the
          // frame's origin from it (a redirect to another origin is a document of that origin).
          const from=frameFinal&&frameFinal!==nav.url?frameFinal:undefined;
          take(turn=await ss({action:"frame",session,node:nav.nodeId,url:nav.url,source:source??"",...(frameEncoding?{encoding:frameEncoding}:{}),
            ...(from?{responseUrl:from}:{}),
            ...(source===undefined?{failed:true}:{resources:await resourcesOf(source,from??nav.url)})}));
        }
        await settleTo(Math.max(1,70000-turn.clock));
      }
    };
    await answerFrames();
    let lastNet=performance.now();
    for(let round=0;inflight.size&&round<5000&&turn.clock<70000;round++){
      const {id,answer}=await Promise.race(inflight.values());
      inflight.delete(id);
      const now=performance.now(),elapsedMs=Math.round(now-lastNet);lastNet=now;
      take(turn=await ss({action:"net",session:turn.session,results:[answer],elapsedMs}));
      await settleTo(Math.max(1,70000-turn.clock));
      await answerFrames();
    }
    engine.scriptSession("",{action:"close"});
    return {...resultOf(file,logs),ms:Math.round(performance.now()-t0),instructions,clock:turn.clock,...(errors.length?{errors:errors.slice(0,5)}:{})};
  }};
}

// ---- the bench backend (lake exe wasmvm-bench page) -----------------------------------
async function benchBackend():Promise<{run:Run;info:Record<string,unknown>}> {
  const exe=opt("--bench",join(root,"formal/lean4/.lake/build/bin/wasmvm-bench"));
  const served=await Deno.makeTempDir({prefix:"wpt-served-"});
  // The union of the pinned copies: a directory in several copies is made, its entries linked.
  const merge=async(rel:string)=>{
    const dirs=roots.map(r=>join(r,rel)).filter(d=>exists(d)&&Deno.statSync(d).isDirectory);
    await Deno.mkdir(join(served,rel),{recursive:true});
    const names=new Set<string>();for(const d of dirs)for(const e of Deno.readDirSync(d))names.add(e.name);
    for(const name of names){
      const r=rel?`${rel}/${name}`:name,has=dirs.filter(d=>exists(join(d,name)));
      if((has.length>1||r==="resources")&&Deno.statSync(join(has[0],name)).isDirectory)await merge(r);
      else if(!exists(join(served,r)))await Deno.symlink(join(has[0],name),join(served,r));
    }
  };
  await merge("");
  await Deno.symlink(join(here,"testharnessreport.js"),join(served,"resources/testharnessreport.js"));
  const gen=join(served,"generated");
  return {info:{engine:"wasmvm-bench page"},run:async(file:string)=>{
    let page=file;
    if(file.endsWith(".js")){page=`generated/${pageOf(file)}`;await Deno.mkdir(dirname(join(served,page)),{recursive:true});
      await Deno.writeTextFile(join(served,page),wrapper(file));}
    const t0=performance.now();
    const out=await new Deno.Command(exe,{args:["page",quickjs,served,page,"--settle","70000","--commands","200000",
      "--instructions-per-ms",String(scriptRate),...(scriptEngine==="bubblepop"?["--bubblepop"]:[])],stdout:"piped",stderr:"null"}).output();
    const line=new TextDecoder().decode(out.stdout).trim().split("\n").pop()??"{}";
    const r=JSON.parse(line||"{}");
    if(r.error)return {file,harness:"ERROR",message:r.error,subtests:[]};
    return {...resultOf(file,r.logs??[]),ms:Math.round(performance.now()-t0),instructions:r.instructions,clock:r.clock,...(r.errors?.length?{errors:r.errors.slice(0,5)}:{})};
  },cleanup:()=>Deno.remove(served,{recursive:true})} as never;
}

/** --list: run wpt.fyi-named tests from any checkout, one JSON line a case to --jsonl. */
async function runList(listFile:string) {
  if(engineKind==="bench")throw new Error("--list runs on the engine (native or wasm), not the bench");
  const names=(await Deno.readTextFile(listFile)).split("\n").map(l=>l.trim()).filter(l=>l&&!l.startsWith("#"));
  const jsonl=opt("--jsonl"),done=new Set<string>(),cases:Case[]=[];
  if(jsonl)try{for(const l of (await Deno.readTextFile(jsonl)).split("\n"))if(l.trim()){const c=JSON.parse(l) as Case;done.add(c.file);cases.push(c);}}catch{/* a new file */}
  // The engine first: its probe decides which variants it can run.
  if(wptserveMode)await startServe();
  const backend=await engineBackend();
  for(const name of names) {
    const id=name.replace(/^\//,"");
    if(done.has(id)||(only&&!id.includes(only)))continue;
    console.error(`START ${id}`);
    let c:Case;
    try{
      const t=named(id);
      if(t.skip)c={file:id,harness:"SKIP",message:t.skip,kind:t.kind,subtests:[]};
      else if(excluded.some(x=>id.includes(x)))c={file:id,harness:"SKIP",message:"excluded",kind:t.kind,subtests:[]};
      else {c={...await backend.run(id,{html:t.html,url:t.url!}),kind:t.kind};}
    }catch(e){c={file:id,harness:"ERROR",message:String((e as Error).message??e).slice(0,300),subtests:[]};}
    cases.push(c);done.add(id);
    if(jsonl)await Deno.writeTextFile(jsonl,JSON.stringify(c)+"\n",{append:true});
    const pass=c.subtests.filter(s=>s.status==="PASS").length;
    console.error(`${c.harness.padEnd(9)} ${String(pass).padStart(3)}/${String(c.subtests.length).padEnd(3)} ${id} ${c.ms??""}ms`);
  }
  const totals={files:cases.length,run:cases.filter(c=>c.harness!=="SKIP").length,subtests:cases.reduce((n,c)=>n+c.subtests.length,0),
    pass:cases.reduce((n,c)=>n+c.subtests.filter(s=>s.status==="PASS").length,0)};
  console.log(`total: ${totals.pass}/${totals.subtests} subtests pass in ${totals.run} pages run of ${totals.files}`);
  if(opt("--out"))await Deno.writeTextFile(opt("--out"),JSON.stringify({format:"factoidal-wpt-testharness-v1",
    measuredAt:new Date().toISOString(),wptRoot:wpt,wptCommit:opt("--wpt-commit")||null,engine:engineKind,scriptEngine,
    info:backend.info,wptserve:wptserveMode?{origin:serveOrigin,secureOrigin:serveSecureOrigin}:null,totals,cases},null,1)+"\n");
  serve?.fetcher.close();await serve?.stop?.();
}

if(import.meta.main&&opt("--list"))await runList(opt("--list"));
else if(import.meta.main&&wptserveMode)throw new Error("--wptserve runs a --list of wpt.fyi names from a --wpt-root checkout (wpt-score.py tree)");
else if(import.meta.main) {
  const backend=engineKind==="bench"?await benchBackend():await engineBackend();
  const cases:Case[]=[];
  const started=new Date().toISOString();
  for(const dir of dirs) for(const t of testsOf(dir)) {
    if(only&&!t.file.includes(only))continue;
    if(t.skip){cases.push({file:t.file,harness:"SKIP",message:t.skip,subtests:[]});continue;}
    if(excluded.some(x=>t.file.includes(x))){cases.push({file:t.file,harness:"SKIP",message:"excluded",subtests:[]});continue;}
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
    scope:`WPT testharness.js tests, window variant, in the engine's script session (${scriptEngine==="bubblepop"?"BubblePopJS (the JavaScript engine written in Lean)":"QuickJS-NG in WasmVM"}, Lean DOM arena, Lean event loop, virtual clock). Subtest counts are of the subtests a page reported; a page that reported none counts 0 of 0.`,scriptEngine,
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
