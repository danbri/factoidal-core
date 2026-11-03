import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { Worker } from 'node:worker_threads';
import { createQuickJS, QUICKJS_SHA256 } from './quickjs.mjs';
import { createScriptSession, validateBatch } from './session.mjs';
const wasmBytes = await readFile(new URL('../../.build/script-engine/qjs-wasi-reactor.wasm', import.meta.url));
const nodes = [
  { id: 4, tagName: 'p', attributes: { id: 'message' }, textContent: 'before' },
  { id: 5, tagName: 'a', attributes: { id: 'change', href: '#change' }, textContent: 'Change' }
];
const options = { wasmBytes, workerFactory: () => new Worker(new URL('./worker.mjs', import.meta.url)) };
const create = extra => createScriptSession({ ...options, ...extra });

test('unmodified pinned QuickJS reactor executes code with its own heap', async () => {
  const vm = await createQuickJS(wasmBytes);
  try {
    assert.equal(vm.evaluate('JSON.stringify({n:6*7,b:typeof process,f:typeof fetch,p:typeof postMessage})', { stringResult: true }), '{"n":42,"b":"undefined","f":"undefined","p":"undefined"}');
    assert.equal(QUICKJS_SHA256.length, 64);
  } finally { vm.dispose(); }
  await assert.rejects(createQuickJS(new Uint8Array([0, 97, 115, 109])), /checksum mismatch/);
});

test('classic scripts share VM bindings; callback produces typed commands', async () => {
  const session = create();
  try {
    const first = await session.start({ nodes, sources: [
      'let count = 1; document.getElementById("message").textContent = "loaded";',
      'document.querySelector("#change").addEventListener("click", function(event) { document.getElementById("message").textContent = "click " + count++; this.setAttribute("data-clicked", event.type); });'
    ] });
    assert.deepEqual(first.commands, [{ op: 'setTextContent', nodeId: 4, value: 'loaded' }]);
    assert.deepEqual(first.listeners, [{ nodeId: 5, type: 'click' }]);
    assert.deepEqual((await session.dispatch({ type: 'click', nodeId: 5 })).commands, [
      { op: 'setTextContent', nodeId: 4, value: 'click 1' },
      { op: 'setAttribute', nodeId: 5, name: 'data-clicked', value: 'click' }
    ]);
    assert.equal((await session.dispatch({ type: 'click', nodeId: 5 })).commands[0].value, 'click 2');
    await assert.rejects(session.dispatch({ type: 'click', nodeId: 999 }), /Unknown script click target/);
  } finally { session.reset(); }
});

test('infinite loop is interrupted and the session can restart', async () => {
  const session = create();
  try {
    const start = performance.now();
    await assert.rejects(session.start({ nodes, source: 'while(true){}', budgetMs: 20 }), /interrupted|timeout/);
    assert.ok(performance.now() - start < 3000);
    assert.deepEqual((await session.start({ nodes, source: 'console.log("restarted")' })).logs, ['restarted']);
  } finally { session.reset(); }
});

test('host watchdog terminates a busy actual worker before cooperative deadline', async () => {
  const session = create({ watchdogMs: 100 });
  try {
    await assert.rejects(session.start({ nodes, source: 'while(true){}', budgetMs: 1000 }), /worker timeout; engine terminated/);
    await assert.rejects(session.dispatch({ type: 'click', nodeId: 5 }), /not running/);
    // Reset and new worker also work after hard termination.
    assert.equal((await session.start({ nodes, source: 'document.getElementById("message").textContent="fresh"' })).commands[0].value, 'fresh');
  } finally { session.reset(); }
});

test('allocation exhaustion and guest exception do not commit pending commands', async () => {
  const session = create();
  try {
    await assert.rejects(session.start({ nodes, source: 'document.getElementById("message").textContent="discard";throw Error("stop");' }), /stop/);
    await assert.rejects(session.start({ nodes, source: 'new Array(100000000).fill("x")' }), /memory|allocation|out of bounds|timeout/i);
    assert.deepEqual((await session.start({ nodes, source: '' })).commands, []);
  } finally { session.reset(); }
});

test('message validator refuses unknown handles and command forms', () => {
  const allowed = new Set([4, 5]), base = { listeners: [], logs: [] };
  assert.throws(() => validateBatch({ ...base, commands: [{ op: 'setTextContent', nodeId: 999, value: 'bad' }] }, allowed), /Invalid/);
  assert.throws(() => validateBatch({ ...base, commands: [{ op: 'innerHTML', nodeId: 4, value: '<p>bad</p>' }] }, allowed), /Unsupported/);
  assert.throws(() => validateBatch({ ...base, commands: [{ op: 'setTextContent', nodeId: 4, value: 'a'.repeat(65537) }] }, allowed), /Invalid/);
});

test('reset cancels an outstanding turn', async () => {
  const session = create();
  const pending = session.start({ nodes, source: '' });
  session.reset();
  await assert.rejects(pending, /session reset/);
});
