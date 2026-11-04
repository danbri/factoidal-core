#!/usr/bin/env node
// Original WPT scripts execute only inside the pinned QuickJS WASM instance.
// This is a synchronous shell transport, not a complete Window/event-loop runner.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { createQuickJS, QUICKJS_SHA256 } from '../../labs/demos/foafnaut/web-render/script-engine/quickjs.mjs';
import { bootstrap } from '../../labs/demos/foafnaut/web-render/script-engine/guest.mjs';
import { createLeanDOM } from '../../labs/demos/foafnaut/web-render/script-engine/lean-dom.mjs';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const argv = process.argv.slice(2);
const option = name => argv[argv.indexOf(name) + 1];
for (const name of ['--corpus', '--native', '--output']) if (!argv.includes(name)) throw Error(`Missing ${name}`);
const corpus = resolve(option('--corpus')), native = resolve(option('--native')), output = resolve(option('--output'));
mkdirSync(output, { recursive: true });
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
const manifest = JSON.parse(readFileSync(resolve(corpus, 'source.json')));
const inventory = JSON.parse(readFileSync(resolve(corpus, 'inventory.json')));
const files = new Map(manifest.files.map(f => [f.path, f]));
const fixture = path => {
  if (!files.has(path)) throw Error(`Uninventoried dependency: ${path}`);
  const bytes = readFileSync(resolve(corpus, 'upstream', path));
  if (hash(bytes) !== files.get(path).sha256) throw Error(`Fixture integrity failure: ${path}`);
  return bytes.toString('utf8');
};
const harness = fixture('resources/testharness.js');
const reactor = readFileSync(resolve(root, 'labs/demos/foafnaut/.build/script-engine/qjs-wasi-reactor.wasm'));
const optionsFile = resolve(output, 'inspect-options.json');
const leanModulePath = resolve(root, 'labs/demos/foafnaut/.build/web-render/engines/web-render.mjs');
const leanWasmPath = resolve(dirname(leanModulePath), 'web-render.wasm');
const leanModuleURL = pathToFileURL(leanModulePath).href;
const { default: createLeanModule } = await import(leanModuleURL);
// The document ABI is stateless. Reuse this separate Lean instance between
// cases; each document gets its own bounded command history and QuickJS heap.
const leanEngine = await createLeanModule();
const report = {
  format: 'factoidal-wpt-quickjs-shell-v1', startedAt: new Date().toISOString(),
  scope: 'All script-test documents in supplied inventory; synchronous assertions only. No browser event-loop or full Window claim.',
  revision: manifest.revision, sourceManifestSha256: hash(readFileSync(resolve(corpus, 'source.json'))),
  native: { path: native, sha256: hash(readFileSync(native)) },
  leanWasm: { path: leanWasmPath, sha256: hash(readFileSync(leanWasmPath)), moduleSha256: hash(readFileSync(leanModulePath)) },
  quickjs: { version: '0.18.0', sha256: QUICKJS_SHA256 },
  harnessSha256: hash(harness), runnerSha256: hash(readFileSync(fileURLToPath(import.meta.url))),
  guestSha256: hash(readFileSync(resolve(root, 'labs/demos/foafnaut/web-render/script-engine/guest.mjs'))),
  transport: 'Lean native inspect supplies nodes and scripts. QuickJS executes pinned testharness.js in shell mode and the production guest binding. The production synchronous DOM capability calls a separate Lean WASM instance, reused between documents with separate command histories. JSON callbacks replace testharnessreport.js.',
  controls: {}, cases: []
};
// Forbid accidental evaluation of page/harness source in the Node host realm.
globalThis.eval = () => { throw Error('Host eval forbidden'); };
globalThis.Function = new Proxy(globalThis.Function, {
  apply() { throw Error('Host Function forbidden'); }, construct() { throw Error('Host Function forbidden'); }
});
const collector = `setup({explicit_done:true,output:false});
globalThis.__wptResults=[];globalThis.__wptRegistered=0;globalThis.__wptAsync=0;globalThis.__wptCompletion=null;
add_result_callback(t=>__wptResults.push({name:t.name,status:t.status,message:t.message}));
add_completion_callback((tests,s)=>globalThis.__wptCompletion={status:s.status,message:s.message});
for(const name of ['test','async_test','promise_test']){const original=globalThis[name];
globalThis[name]=function(...args){__wptRegistered++;if(name!=='test')__wptAsync++;return original(...args);};}`;
function collect(vm) {
  return JSON.parse(vm.evaluate('JSON.stringify({results:__wptResults,registered:__wptRegistered,async:__wptAsync,completion:__wptCompletion})', { stringResult: true }));
}
async function vmWithHarness() {
  const vm = await createQuickJS(reactor);
  vm.evaluate('globalThis.self=globalThis;');
  vm.evaluate(harness); vm.evaluate(collector);
  return vm;
}
{
  const vm = await vmWithHarness();
  try {
    vm.evaluate('test(()=>assert_equals(2+2,4),"expected pass");test(()=>assert_equals(2+2,5),"intentional failure");');
    report.controls.assertions = collect(vm).results;
    report.controls.guestGlobals = JSON.parse(vm.evaluate('JSON.stringify({process:typeof process,fetch:typeof fetch,document:typeof document,WebAssembly:typeof WebAssembly})', { stringResult: true }));
    if (JSON.stringify(report.controls.assertions.map(t => t.status)) !== '[0,1]') throw Error('WPT assertion controls failed');
    if (Object.values(report.controls.guestGlobals).some(x => x !== 'undefined')) throw Error('Unexpected guest host API');
  } finally { vm.dispose(); }
}
const candidates = inventory.documents.filter(d => d.kind === 'script-test');
for (const doc of candidates) {
  const row = { path: doc.path, sourceSha256: files.get(doc.path)?.sha256, requirements: doc.requirements, status: 'UNAVAILABLE', results: [] };
  report.cases.push(row);
  if (!doc.path.endsWith('.html')) { row.reason = 'SVG/XML script document loading is not wired in the current HTML guest'; continue; }
  if (doc.variants?.length) { row.reason = 'URL variants are not implemented by this shell transport'; continue; }
  let vm;
  try {
    const html = fixture(doc.path);
    writeFileSync(optionsFile, JSON.stringify({ op: 'inspect', url: 'https://web-platform.test/' + doc.path }));
    const inspected = spawnSync(native, [resolve(corpus, 'upstream', doc.path), '800', '600', '--document', optionsFile],
      { encoding: 'utf8', timeout: 2500, maxBuffer: 8 * 1024 * 1024 });
    if (inspected.error) { row.status = inspected.error.code === 'ETIMEDOUT' ? 'TIMEOUT' : 'HARNESS_ERROR'; row.reason = String(inspected.error); continue; }
    if (inspected.status !== 0) { row.status = 'CRASH'; row.reason = `${inspected.status}/${inspected.signal}: ${inspected.stderr.slice(0,1000)}`; continue; }
    const snapshot = JSON.parse(inspected.stdout);
    if (snapshot.error) { row.status = 'UNSUPPORTED'; row.reason = snapshot.error; continue; }
    row.snapshotSha256 = hash(inspected.stdout);
    row.scriptCount = snapshot.scripts.length;
    let deadline = Infinity;
    vm = await createQuickJS(reactor, { shouldInterrupt: () => performance.now() > deadline });
    await vm.bind('__factoidalDOM', await createLeanDOM({source:html,url:'https://web-platform.test/'+doc.path,moduleURL:leanModuleURL},leanEngine));
    vm.evaluate('globalThis.self=globalThis;'); vm.evaluate(harness); vm.evaluate(collector);
    vm.evaluate(bootstrap(snapshot.nodes)); vm.evaluate('globalThis.window=globalThis;');
    for (const script of snapshot.scripts) {
      let source = script.source;
      if (script.src) {
        const url = new URL(script.url);
        if (url.origin !== 'https://web-platform.test') throw Error('External dependency not supplied: ' + script.url);
        const path = decodeURIComponent(url.pathname).replace(/^\//, '');
        if (path === 'resources/testharness.js' || path === 'resources/testharnessreport.js') continue;
        source = fixture(path);
      }
      deadline = performance.now() + 100;
      try { vm.evaluate(source); }
      catch (error) { row.scriptError = String(error); break; }
      finally { deadline = Infinity; }
    }
    if (!collect(vm).async) vm.evaluate('done();');
    const actual = collect(vm); Object.assign(row, actual);
    row.status = row.scriptError ? (row.scriptError.includes('interrupted') ? 'TIMEOUT' : 'ERROR')
      : actual.completion?.status ? 'HARNESS_ERROR'
      : actual.results.some(t => t.status !== 0) ? 'FAIL'
      : actual.async || !actual.completion || actual.results.length !== actual.registered ? 'INCOMPLETE'
      : actual.results.length ? 'PASS' : 'NO_ASSERTIONS';
  } catch (error) { row.status = 'HARNESS_ERROR'; row.reason = String(error); }
  finally { vm?.dispose(); }
  if (report.cases.length % 50 === 0) console.log(JSON.stringify({ completed: report.cases.length, total: candidates.length }));
}
report.finishedAt = new Date().toISOString();
report.counts = report.cases.reduce((r,c) => (r[c.status]=(r[c.status]??0)+1,r),{});
report.assertions = report.cases.flatMap(c=>c.results).reduce((r,t)=>(r[t.status===0?'pass':'fail']++,r),{pass:0,fail:0});
if (hash(readFileSync(native)) !== report.native.sha256) throw Error('Native engine changed during run');
if (hash(readFileSync(leanWasmPath)) !== report.leanWasm.sha256 || hash(readFileSync(leanModulePath)) !== report.leanWasm.moduleSha256) throw Error('Lean WASM changed during run');
writeFileSync(resolve(output, 'quickjs-wpt.json'), JSON.stringify(report, null, 2)+'\n');
console.log(JSON.stringify({total:report.cases.length,counts:report.counts,assertions:report.assertions,report:resolve(output,'quickjs-wpt.json')}));
process.exitCode = report.cases.every(c=>c.status==='PASS') ? 0 : 1;
