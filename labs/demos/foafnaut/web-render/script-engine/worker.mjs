import { createQuickJS } from './quickjs.mjs';
import { bootstrap } from './guest.mjs';
import { createLeanDOM, createLeanLoop } from './lean-dom.mjs';

let send, listen;
if (typeof globalThis.postMessage === 'function') {
  send = value => globalThis.postMessage(value);
  listen = callback => globalThis.addEventListener('message', event => callback(event.data));
} else {
  const { parentPort } = await import('node:worker_threads');
  send = value => parentPort.postMessage(value);
  listen = callback => parentPort.on('message', callback);
}
// The most callbacks one operation runs; a page that queues work forever stops here.
const RUN_BUDGET = 10000;
let vm, loop, deadline = Infinity, initialized = false;

// Promise reactions are QuickJS jobs. They run after each callback, as part of
// the microtask checkpoint that follows it (HTML "clean up after running script").
const jobs = () => vm.runJobs();
const run = item => {
  vm.evaluate(`__factoidalRun(${JSON.stringify(JSON.stringify(item))});`);
  jobs();
};
// HTML §8.1.7.3: run tasks and microtasks in the order Lean gives, moving the
// virtual clock up to `target`. Lean moves the clock to each due timer in turn.
const pump = target => {
  let count = 0;
  for (;;) {
    const { run: next } = loop.act('step');
    if (next) {
      if (++count > RUN_BUDGET) throw Error('Event loop budget exceeded');
      run(next);
      continue;
    }
    const { settled, fired } = loop.act('advance', { target: target ?? loop.clock });
    if (settled && fired === 0) return;
  }
};
// HTML "update the rendering": the animation frame callbacks of this frame, each
// followed by a microtask checkpoint; then the tasks due now.
const frame = () => {
  loop.act('render');
  let count = 0;
  for (let next; (next = loop.act('frameStep').run);) {
    if (++count > RUN_BUDGET) throw Error('Event loop budget exceeded');
    run(next);
    vm.evaluate('__factoidalCheckpoint()');
    jobs();
  }
  pump();
};
const loopSummary = () => loop ? { clock: loop.clock, nextDue: loop.nextDue, frames: loop.framesWaiting } : null;

listen(async message => {
  const { id, operation, payload } = message;
  try {
    if (operation === 'initialize') {
      if (initialized) throw Error('Script worker already initialized');
      initialized = true;
      let bytes = payload.wasmBytes;
      if (!bytes) {
        const response = await fetch(payload.wasmURL);
        if (!response.ok) throw Error(`QuickJS download HTTP ${response.status}`);
        bytes = await response.arrayBuffer();
      }
      vm = await createQuickJS(bytes, { shouldInterrupt: () => performance.now() >= deadline });
      // The Lean engine serves the DOM and, by default with it, the event loop.
      // An engine built before the `eventLoop` operation refuses it; then the page
      // runs without the loop unless the host asked for it.
      const wantLoop = payload.eventLoop ?? Boolean(payload.document);
      let engine;
      if (wantLoop) {
        const { default: createModule } = await import(payload.leanModuleURL);
        engine = await createModule();
        try { loop = await createLeanLoop({ engine }); }
        catch (error) { if (payload.eventLoop === true) throw error; }
        if (loop) await vm.bind('__factoidalLoop', loop.capability);
      }
      if (payload.document) {
        const mutate = await createLeanDOM({ ...payload.document, moduleURL: payload.leanModuleURL }, engine);
        await vm.bind('__factoidalDOM', mutate);
      }
      send({ id, ok: true, result: { engine: 'quickjs-ng-v0.18.0-wasi-reactor', eventLoop: Boolean(loop) } });
      return;
    }
    if (!vm) throw Error('Script engine is not initialized');
    deadline = performance.now() + payload.budgetMs;
    if (operation === 'start') {
      vm.evaluate(bootstrap(payload.nodes));
      for (const source of payload.sources) {
        vm.evaluate(source);
        // Each classic script is followed by a microtask checkpoint.
        if (loop) vm.evaluate('__factoidalCheckpoint()');
        jobs();
      }
      if (loop) pump();
    } else if (operation === 'dispatch') {
      if (loop) {
        // A user interaction task (HTML §8.1.7.4); Lean orders it with the others.
        loop.act('queueTask', { source: 'userInteraction', callback: 0, event: { type: payload.event.type, target: payload.event.nodeId } });
        pump();
      } else {
        vm.evaluate(`__factoidalDispatch(${JSON.stringify(JSON.stringify(payload.event))});`);
        jobs();
      }
    } else if (operation === 'advance') {
      if (!loop) throw Error('The event loop needs the Lean engine');
      pump(loop.clock + payload.ms);
    } else if (operation === 'frame') {
      if (!loop) throw Error('The event loop needs the Lean engine');
      frame();
    } else throw Error('Unknown script worker operation');
    const result = JSON.parse(vm.evaluate('__factoidalDrain()', { stringResult: true }));
    result.loop = loopSummary();
    send({ id, ok: true, result });
  } catch (error) {
    send({ id, ok: false, error: String(error.message ?? error).slice(0, 4096) });
  } finally { deadline = Infinity; }
});
