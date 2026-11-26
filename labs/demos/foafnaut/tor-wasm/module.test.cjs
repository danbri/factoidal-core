// Checks of the Arti wasm module in Node (no host transport): it fails closed, the opt-in needs
// the exact string, state can be read out and loaded back, no debug lines by default. Expected
// failures of the Deno worker path are in deno/tor.test.ts.
// Run after build.sh: node --test labs/demos/foafnaut/tor-wasm/xfail.test.cjs
const test = require('node:test');
const assert = require('node:assert');
const fs = require('fs'), path = require('path'), dir = path.join(__dirname, '.build');
global.self = global;
require('vm').runInThisContext(fs.readFileSync(path.join(dir, 'foafnaut_tor_wasm.js'), 'utf8') + ';globalThis.wasm_bindgen=wasm_bindgen;');
// Arti's retry timers keep the event loop alive; end the process once the tests are done.
test.after(() => setTimeout(() => process.exit(process.exitCode ?? 0), 50));
const ready = wasm_bindgen({ module_or_path: fs.readFileSync(path.join(dir, 'foafnaut_tor_wasm_bg.wasm')) });

test('without a host transport the client never bootstraps (fails closed)', async () => {
  await ready;
  const out = await wasm_bindgen.bootstrap(3000);
  assert.ok(!/"step":"bootstrap","ok":true/.test(out));
  assert.equal(wasm_bindgen.isolated_context(), false, 'Node main thread is not a worker');
});




test('refused connections are counted and nothing else is tried', async () => {
  await ready;
  const out = await wasm_bindgen.bootstrap(3000);
  const end = JSON.parse(out.trim().split('\n').pop());
  assert.ok(end.refusedConnections > 0, 'Arti tried to connect and every attempt was refused');
  assert.equal(end.fraction, 0, 'no directory progress without a transport');
});

test('the transport stays off without the exact acknowledgement', async () => {
  await ready;
  assert.equal(wasm_bindgen.enable_unreviewed_transport(''), false);
  assert.equal(wasm_bindgen.enable_unreviewed_transport('yes'), false);
  assert.equal(wasm_bindgen.enable_unreviewed_transport('dangerously-use-unreviewed-tor-transport '), false);
});

test('no debug lines by default (they can carry relay addresses)', async () => {
  await ready;
  const seen = [];
  const orig = console.log;
  console.log = (...a) => { seen.push(a.join(' ')); };
  try { await wasm_bindgen.bootstrap(2000); } finally { console.log = orig; }
  const debug = seen.filter((l) => /^arti\s+(DEBUG|TRACE)/.test(l));
  assert.equal(debug.length, 0, `debug lines printed: ${debug.slice(0, 2).join(' | ')}`);
  assert.ok(seen.some((l) => l.startsWith('tor ')), 'the console capture saw the module');
  // Control: with debug on, the same capture must see debug lines (else this test sees nothing).
  const seen2 = [];
  console.log = (...a) => { seen2.push(a.join(' ')); };
  wasm_bindgen.log_debug(true);
  try { await wasm_bindgen.bootstrap(2000); } finally { console.log = orig; wasm_bindgen.log_debug(false); }
  assert.ok(seen2.some((l) => /^arti\s+DEBUG/.test(l)), 'control: debug lines visible when switched on');
});

test('state can be read out and loaded back', async () => {
  await ready;
  const before = JSON.parse(wasm_bindgen.state_snapshot());
  assert.equal(typeof before, 'object');
  assert.equal(wasm_bindgen.state_load('{"foafnaut_test":"{\\"x\\":1}"}'), 1);
  assert.equal(JSON.parse(wasm_bindgen.state_snapshot()).foafnaut_test, '{"x":1}');
  assert.equal(wasm_bindgen.state_load('not json'), -1);
  assert.equal(wasm_bindgen.set_state_store('file'), false, 'only a sealed LWS store is accepted');
});
