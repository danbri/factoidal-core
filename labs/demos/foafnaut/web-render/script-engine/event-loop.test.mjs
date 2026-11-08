// The HTML event loop of a page, decided by Lean (L4Factoidal.EventLoop, op
// `eventLoop`) and run by QuickJS. Drives fixtures/timers.html with the virtual
// clock and checks the Lean DOM text after each step.
// Run: node --test event-loop.test.mjs (needs .build/web-render/engines/web-render.mjs
// and .build/script-engine/qjs-wasi-reactor.wasm; see build-web-render.sh --wasm).
import test from 'node:test';
import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import { Worker } from 'node:worker_threads';
import { createScriptSession } from './session.mjs';

const leanModuleURL = new URL('../../.build/web-render/engines/web-render.mjs', import.meta.url).href;
const wasmBytes = await readFile(new URL('../../.build/script-engine/qjs-wasi-reactor.wasm', import.meta.url));
const source = await readFile(new URL('../fixtures/timers.html', import.meta.url), 'utf8');
const url = 'https://example.test/timers.html';
const { default: createModule } = await import(leanModuleURL);
const engine = await createModule();
const call = (html, request) => {
  const pointer = engine.ccall('web_document_call', 'number', ['string','string','number','number'], [html, JSON.stringify(request), 1, 1]);
  try { return JSON.parse(engine.UTF8ToString(pointer)); }
  finally { engine.ccall('web_render_free', null, ['number'], [pointer]); }
};
const supported = !call('', { op: 'eventLoop', action: 'init' }).error;
const skip = supported ? false : 'this web-render engine has no eventLoop operation; rebuild with build-web-render.sh --wasm';

const inspect = commands => {
  const result = call(source, { op: 'inspect', url, commands });
  assert.equal(result.error, undefined);
  return result;
};
const text = (snapshot, id) => snapshot.nodes.find(node => node.attributes.id === id).textContent;

test('Lean eventLoop operation: setTimer ids, step order, clamp, dispatch plan', { skip }, () => {
  let state = call('', { op: 'eventLoop', action: 'init' }).state;
  const act = (action, fields = {}) => { const answer = call('', { op: 'eventLoop', action, state, ...fields }); assert.equal(answer.error, undefined); state = answer.state; return answer; };
  assert.equal(act('setTimer', { callback: 5, timeout: 10, periodic: false }).id, 1);
  assert.equal(act('setTimer', { callback: 6, timeout: 10, periodic: false }).id, 2);
  act('queueMicrotask', { callback: 7 });
  assert.deepEqual(act('step').run, { kind: 'microtask', callback: 7, source: null, timer: null, event: null, now: 0 });
  assert.equal(act('step').run, null);
  // advance stops the clock at the first due timer (10), so the target (100) is not reached yet.
  assert.deepEqual(act('advance', { target: 100 }), { fired: 2, settled: false, state });
  assert.deepEqual([act('step').run.callback, act('step').run.callback], [5, 6]);
  const plan = call('', { op: 'eventLoop', action: 'dispatch', path: [1, 2], bubbles: true,
    listeners: [{ node: 2, capture: false, callback: 1 }, { node: 1, capture: true, callback: 2 }, { node: 1, capture: false, callback: 3 }] });
  assert.deepEqual(plan.visits.map(visit => [visit.callback, visit.phase]), [[2, 1], [1, 2], [3, 3]]);
  // A state whose timers are out of order is refused.
  const bad = { ...state, timers: [[1,1,9,0,9,false,1],[2,2,5,1,5,false,1]], nextSeq: 2 };
  assert.match(call('', { op: 'eventLoop', action: 'step', state: bad }).error, /out of order/);
});

test('timers.html: order, interval, timeout chain, listeners, frames', { skip }, async () => {
  const initial = inspect([]);
  const sources = initial.scripts.map(script => script.source);
  const session = createScriptSession({ wasmBytes, leanModuleURL, workerFactory: () => new Worker(new URL('./worker.mjs', import.meta.url)) });
  const commands = [];
  const apply = batch => { commands.push(...batch.commands); return inspect(commands); };
  try {
    let batch = await session.start({ nodes: initial.nodes, sources, budgetMs: 1000, document: { source, url, commands: [] } });
    assert.equal(session.eventLoop, true);
    let dom = apply(batch);
    // Script, microtask checkpoint (queueMicrotask, then the Promise job), then the 0 ms timeout.
    assert.equal(text(dom, 'order'), 'sync micro promise timeout');
    assert.equal(text(dom, 'count'), '0');
    assert.equal(batch.loop.clock, 0);
    assert.equal(batch.loop.nextDue, 20);

    batch = await session.advance(350, { budgetMs: 1000 });
    dom = apply(batch);
    assert.equal(text(dom, 'count'), '3');
    assert.equal(text(dom, 'chain'), 'a b c');
    assert.equal(batch.loop.clock, 350);

    batch = await session.advance(1000, { budgetMs: 1000 });
    dom = apply(batch);
    assert.equal(text(dom, 'count'), '5', 'clearInterval at 5 stops the counter');
    assert.equal(batch.loop.nextDue, null);

    const id = name => initial.nodes.find(node => node.attributes.id === name).id;
    batch = await session.dispatch({ type: 'click', nodeId: id('inner') }, { budgetMs: 1000 });
    dom = apply(batch);
    assert.equal(text(dom, 'events'), 'capture inner, target inner phase 2, micro after inner, bubble inner phase 3');

    batch = await session.dispatch({ type: 'click', nodeId: id('stopper') }, { budgetMs: 1000 });
    dom = apply(batch);
    assert.equal(text(dom, 'events'),
      'capture inner, target inner phase 2, micro after inner, bubble inner phase 3, capture stopper, stop, same node still runs');

    for (let frame = 1; frame <= 4; frame++) {
      if (frame === 2) dom = apply(await session.advance(16, { budgetMs: 1000 }));
      batch = await session.frame({ budgetMs: 1000 });
      dom = apply(batch);
    }
    assert.equal(text(dom, 'frames'), '3 at 1366', 'three frames, then no more requests');
    assert.equal(batch.loop.frames, false);
  } finally { session.reset(); }
});
