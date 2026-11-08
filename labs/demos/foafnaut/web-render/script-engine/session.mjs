const workerURL = new URL('./worker.mjs', import.meta.url);
const defaultWasmURL = new URL('/lab/.build/script-engine/qjs-wasi-reactor.wasm', import.meta.url);
const defaultLeanURL = new URL('/lab/.build/web-render/engines/web-render.mjs', import.meta.url);
const encoder = new TextEncoder();
const validId = id => Number.isSafeInteger(id) && id >= 0 && id <= 1048576;
const boundedString = (value, maximum = 65536) => typeof value === 'string' && encoder.encode(value).length <= maximum;

// Validation is repeated in Lean. This layer protects the host message boundary;
// it does not choose DOM, CSS, layout or event-target semantics.
export function validateBatch(batch, allowedIds) {
  if (!batch || !Array.isArray(batch.commands) || batch.commands.length > 256 ||
      !Array.isArray(batch.listeners) || batch.listeners.length > 16384 ||
      !Array.isArray(batch.logs) || batch.logs.length > 32 ||
      typeof batch.defaultPrevented !== 'boolean') throw Error('Invalid script result envelope');
  for (const command of batch.commands) {
    if (!command || !validId(command.nodeId) || !allowedIds.has(command.nodeId) || !boundedString(command.value)) throw Error('Invalid script DOM command');
    if (command.op === 'setTextContent' && Object.keys(command).length === 3) continue;
    if (command.op === 'setAttribute' && Object.keys(command).length === 4 && boundedString(command.name, 256)) continue;
    throw Error('Unsupported script DOM command');
  }
  for (const listener of batch.listeners) if (!listener || listener.type !== 'click' || !validId(listener.nodeId) || !allowedIds.has(listener.nodeId) || Object.keys(listener).length !== 2) throw Error('Invalid script event listener');
  if (!batch.logs.every(log => boundedString(log))) throw Error('Invalid script console result');
  return batch;
}

export function createScriptSession({ workerFactory = () => new Worker(workerURL, { type: 'module' }), wasmURL = defaultWasmURL.href, wasmBytes, watchdogMs, leanModuleURL = defaultLeanURL.href } = {}) {
  let worker, pending, nextId = 0, started = false, ids = new Set(), listenerIds = new Set(), eventLoop = false;
  const reset = () => {
    const old = worker; worker = undefined; started = false; ids = new Set(); listenerIds = new Set(); eventLoop = false;
    if (pending) { clearTimeout(pending.timer); pending.reject(Error('Script session reset')); pending = undefined; }
    old?.terminate();
  };
  const fail = error => {
    const request = pending; pending = undefined;
    if (request) { clearTimeout(request.timer); request.reject(error); }
    reset();
  };
  const receive = message => {
    if (!pending || message.id !== pending.id) return;
    if (!message.ok) { fail(Error(`QuickJS: ${message.error}`)); return; }
    const request = pending; pending = undefined; clearTimeout(request.timer); request.resolve(message.result);
  };
  const call = (operation, payload, timeout) => new Promise((resolve, reject) => {
    if (!worker) { reject(Error('Script session is not running')); return; }
    if (pending) { reject(Error('Concurrent script turns are not supported')); return; }
    const id = ++nextId;
    const timer = setTimeout(() => fail(Error('Script worker timeout; engine terminated')), timeout);
    pending = { id, resolve, reject, timer };
    worker.postMessage({ id, operation, payload });
  });
  const budget = value => {
    const result = value ?? 100;
    if (!Number.isInteger(result) || result < 1 || result > 1000) throw Error('Script budget must be 1 to 1000ms');
    return result;
  };
  const accept = batch => {
    try {
      validateBatch(batch, ids);
      listenerIds = new Set(batch.listeners.map(listener => listener.nodeId));
      return batch;
    } catch (error) { reset(); throw error; }
  };
  return {
    // `eventLoop`: timers, microtasks, frames and listener order from Lean
    // (default: on when a Lean `document` is given; it needs the Lean engine).
    async start({ nodes, source, sources = source === undefined ? [] : [source], budgetMs, document, eventLoop: wantLoop } = {}) {
      reset();
      if (!Array.isArray(nodes) || nodes.length > 16384 || !boundedString(JSON.stringify(nodes), 2097152)) throw Error('Script DOM snapshot exceeds budget');
      ids = new Set();
      for (const node of nodes) {
        if (!node || !validId(node.id) || ids.has(node.id) || !boundedString(node.tagName, 256) || !boundedString(node.textContent, 1048576) || !node.attributes || Array.isArray(node.attributes) || typeof node.attributes !== 'object') throw Error('Invalid script DOM snapshot');
        ids.add(node.id);
      }
      if (!Array.isArray(sources) || sources.length > 64 || !sources.every(item => boundedString(item, 1048576)) || encoder.encode(sources.join('')).length > 1048576) throw Error('Script source exceeds budget');
      budgetMs = budget(budgetMs);
      worker = workerFactory();
      const activeWorker = worker;
      if (typeof worker.addEventListener === 'function') {
        worker.addEventListener('message', event => { if (worker === activeWorker) receive(event.data); });
        worker.addEventListener('error', event => { if (worker === activeWorker) fail(Error(event.message ?? 'Script worker failed')); });
      } else {
        worker.on('message', message => { if (worker === activeWorker) receive(message); });
        worker.on('error', error => { if (worker === activeWorker) fail(error); });
      }
      try {
        eventLoop = (await call('initialize', { wasmURL, wasmBytes, document, leanModuleURL, eventLoop: wantLoop }, 5000)).eventLoop === true;
        const batch = accept(await call('start', { nodes, sources, budgetMs }, watchdogMs ?? budgetMs + 500));
        started = true;
        return batch;
      } catch (error) { reset(); throw error; }
    },
    async dispatch(event, { budgetMs } = {}) {
      if (!started) throw Error('Script session is not running');
      // With the event loop the event goes to its target and bubbles; any element may be the target.
      if (!event || event.type !== 'click' || !validId(event.nodeId) || !(eventLoop ? ids : listenerIds).has(event.nodeId)) throw Error('Unknown script click target');
      budgetMs = budget(budgetMs);
      return accept(await call('dispatch', { event: { type: 'click', nodeId: event.nodeId }, budgetMs }, watchdogMs ?? budgetMs + 500));
    },
    // Move the page's virtual clock on by `ms` milliseconds; Lean runs the due timers in order.
    async advance(ms, { budgetMs } = {}) {
      if (!started || !eventLoop) throw Error('Script event loop is not running');
      if (!Number.isInteger(ms) || ms < 0 || ms > 86400000) throw Error('Clock step must be 0 to 86400000 ms');
      budgetMs = budget(budgetMs);
      return accept(await call('advance', { ms, budgetMs }, watchdogMs ?? budgetMs + 500));
    },
    // One rendering opportunity: the animation frame callbacks (HTML "update the rendering").
    async frame({ budgetMs } = {}) {
      if (!started || !eventLoop) throw Error('Script event loop is not running');
      budgetMs = budget(budgetMs);
      return accept(await call('frame', { budgetMs }, watchdogMs ?? budgetMs + 500));
    },
    get eventLoop() { return eventLoop; },
    reset
  };
}
