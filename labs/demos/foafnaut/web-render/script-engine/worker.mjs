import { createQuickJS } from './quickjs.mjs';
import { bootstrap } from './guest.mjs';
import { createLeanDOM } from './lean-dom.mjs';

let send, listen;
if (typeof globalThis.postMessage === 'function') {
  send = value => globalThis.postMessage(value);
  listen = callback => globalThis.addEventListener('message', event => callback(event.data));
} else {
  const { parentPort } = await import('node:worker_threads');
  send = value => parentPort.postMessage(value);
  listen = callback => parentPort.on('message', callback);
}
let vm, deadline = Infinity, initialized = false;
const interrupted = () => performance.now() >= deadline;
// Run the guest's Promise jobs (HTML §8.1.4.4 "perform a microtask checkpoint"),
// bounded; an error in a job is reported, as an uncaught error in a callback is.
const microtasks = errors => {
  for (const error of vm.runJobs(1000)) if (errors.length < 8) errors.push(String(error).slice(0, 512));
};
const turnFailed = error => interrupted() || /InternalError|interrupted|out of memory|stack overflow/.test(String(error?.message ?? error));
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
      vm = await createQuickJS(bytes, { shouldInterrupt: interrupted });
      if (payload.document) {
        const mutate = await createLeanDOM({ ...payload.document, moduleURL: payload.leanModuleURL });
        await vm.bind('__factoidalDOM', mutate);
        await vm.bind('__factoidalQuery', mutate.query);
      }
      send({ id, ok: true, result: { engine: 'quickjs-ng-v0.18.0-wasi-reactor' } });
      return;
    }
    if (!vm) throw Error('Script engine is not initialized');
    deadline = performance.now() + payload.budgetMs;
    const errors = [];
    const clock = JSON.stringify(Number(payload.now) || 0);
    if (operation === 'start') {
      vm.evaluate(bootstrap(payload.snapshot ?? payload.nodes));
      vm.evaluate(`__factoidalClock(${clock});`);
      // Each classic script runs in turn; an error ends that script only and is
      // reported (HTML §8.1.4.3 "report an exception"). A budget end stops the turn.
      for (const source of payload.sources) {
        try { vm.evaluate(source); }
        catch (error) { if (turnFailed(error)) throw error; if (errors.length < 8) errors.push(String(error.message ?? error).slice(0, 512)); }
        microtasks(errors);
      }
    } else if (operation === 'dispatch') {
      vm.evaluate(`__factoidalClock(${clock});`);
      vm.evaluate(`__factoidalDispatch(${JSON.stringify(JSON.stringify(payload.event))});`);
    } else if (operation === 'timers') {
      vm.evaluate(`__factoidalTick(${clock});`);
    } else if (operation === 'frame') {
      vm.evaluate(`__factoidalFrame(${clock});`);
    } else throw Error('Unknown script worker operation');
    microtasks(errors);
    const result = JSON.parse(vm.evaluate('__factoidalDrain()', { stringResult: true }));
    result.errors = [...errors, ...result.errors].slice(0, 8);
    send({ id, ok: true, result });
  } catch (error) {
    send({ id, ok: false, error: String(error.message ?? error).slice(0, 4096) });
  } finally { deadline = Infinity; }
});
