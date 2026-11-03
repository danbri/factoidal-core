import { createQuickJS } from './quickjs.mjs';
import { bootstrap } from './guest.mjs';

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
      send({ id, ok: true, result: { engine: 'quickjs-ng-v0.18.0-wasi-reactor' } });
      return;
    }
    if (!vm) throw Error('Script engine is not initialized');
    deadline = performance.now() + payload.budgetMs;
    if (operation === 'start') {
      vm.evaluate(bootstrap(payload.nodes));
      for (const source of payload.sources) vm.evaluate(source);
    } else if (operation === 'dispatch') {
      vm.evaluate(`__factoidalDispatch(${JSON.stringify(JSON.stringify(payload.event))});`);
    } else throw Error('Unknown script worker operation');
    // No Promise job loop in this MVP. Each classic script/click turn is sync.
    const result = JSON.parse(vm.evaluate('__factoidalDrain()', { stringResult: true }));
    send({ id, ok: true, result });
  } catch (error) {
    send({ id, ok: false, error: String(error.message ?? error).slice(0, 4096) });
  } finally { deadline = Infinity; }
});
