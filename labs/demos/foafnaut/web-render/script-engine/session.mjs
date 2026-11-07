const workerURL = new URL('./worker.mjs', import.meta.url);
const defaultWasmURL = new URL('/lab/.build/script-engine/qjs-wasi-reactor.wasm', import.meta.url);
const defaultLeanURL = new URL('/lab/.build/web-render/engines/web-render.mjs', import.meta.url);
const encoder = new TextEncoder();
const validId = id => Number.isSafeInteger(id) && id >= 0 && id <= 1048576;
const boundedString = (value, maximum = 65536) => typeof value === 'string' && encoder.encode(value).length <= maximum;
export const EVENT_TYPES = ['click', 'input', 'keydown', 'keyup'];
// The fields of each DOM command; WebRenderScript.applyCommand checks the same in Lean.
const SHAPES = {
  setTextContent: ['value'], setAttribute: ['name', 'value'], removeAttribute: ['name'],
  createElement: ['tagName', 'namespace'], appendChild: ['child'], removeChild: ['child'],
  classList: ['action', 'token'], setStyleProperty: ['property', 'value']
};

// Validation is repeated in Lean. This layer protects the host message boundary;
// it does not choose DOM, CSS, layout or event-target semantics. `allowedIds` gets
// the ids of created elements.
export function validateBatch(batch, allowedIds) {
  if (!batch || !Array.isArray(batch.commands) || batch.commands.length > 1024 ||
      !Array.isArray(batch.listeners) || batch.listeners.length > 16384 ||
      !Array.isArray(batch.logs) || batch.logs.length > 32 ||
      typeof batch.defaultPrevented !== 'boolean') throw Error('Invalid script result envelope');
  batch.errors ??= []; batch.documentListeners ??= []; batch.timer ??= null; batch.frame ??= false;
  if (!Array.isArray(batch.errors) || batch.errors.length > 8 || !batch.errors.every(e => boundedString(e, 4096)) ||
      !Array.isArray(batch.documentListeners) || !batch.documentListeners.every(t => EVENT_TYPES.includes(t)) ||
      !(batch.timer === null || (typeof batch.timer === 'number' && batch.timer >= 0 && Number.isFinite(batch.timer))) ||
      typeof batch.frame !== 'boolean') throw Error('Invalid script result envelope');
  const ids = new Set(allowedIds);
  for (const command of batch.commands) {
    const fields = SHAPES[command?.op];
    if (!fields) throw Error('Unsupported script DOM command');
    if (!validId(command.nodeId) || Object.keys(command).length !== fields.length + 2 || !fields.every(f => Object.hasOwn(command, f)))
      throw Error('Invalid script DOM command');
    if (command.op === 'createElement') {
      if (ids.has(command.nodeId) || !boundedString(command.tagName, 256) || !['html', 'svg'].includes(command.namespace)) throw Error('Invalid script DOM command');
      ids.add(command.nodeId);
      continue;
    }
    if (!ids.has(command.nodeId)) throw Error('Invalid script DOM command');
    if ('child' in command && (!validId(command.child) || !ids.has(command.child))) throw Error('Invalid script DOM command');
    for (const field of fields) if (field !== 'child' && !boundedString(command[field], field === 'name' ? 256 : 65536)) throw Error('Invalid script DOM command');
  }
  for (const listener of batch.listeners) if (!listener || !['click', 'input'].includes(listener.type) || !validId(listener.nodeId) || !ids.has(listener.nodeId) || Object.keys(listener).length !== 2) throw Error('Invalid script event listener');
  if (!batch.logs.every(log => boundedString(log))) throw Error('Invalid script console result');
  if (allowedIds instanceof Set) for (const id of ids) allowedIds.add(id);
  return batch;
}

export function createScriptSession({ workerFactory = () => new Worker(workerURL, { type: 'module' }), wasmURL = defaultWasmURL.href, wasmBytes, watchdogMs, leanModuleURL = defaultLeanURL.href, now = () => performance.now() } = {}) {
  let worker, pending, nextId = 0, started = false, ids = new Set(), listeners = [], documentListeners = [];
  // Turns run one at a time, in the order asked: input, timers and frames keep their order.
  let queue = Promise.resolve(), generation = 0;
  const stop = () => {
    const old = worker; worker = undefined; started = false; ids = new Set(); listeners = []; documentListeners = [];
    if (pending) { clearTimeout(pending.timer); pending.reject(Error('Script session reset')); pending = undefined; }
    old?.terminate();
  };
  // reset() also cancels the turns that wait in the queue.
  const reset = () => { generation++; stop(); };
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
  const serial = work => {
    const asked = generation;
    const begin = () => { if (asked !== generation) throw Error('Script session reset'); return work(); };
    const run = queue.then(begin, begin); queue = run.catch(() => {}); return run;
  };
  const budget = value => {
    const result = value ?? 100;
    if (!Number.isInteger(result) || result < 1 || result > 1000) throw Error('Script budget must be 1 to 1000ms');
    return result;
  };
  const accept = batch => {
    try {
      validateBatch(batch, ids);
      listeners = batch.listeners; documentListeners = batch.documentListeners;
      return batch;
    } catch (error) { reset(); throw error; }
  };
  const turn = (operation, payload, budgetMs) => serial(async () => {
    if (!started) throw Error('Script session is not running');
    budgetMs = budget(budgetMs);
    return accept(await call(operation, { ...payload, budgetMs, now: now() }, watchdogMs ?? budgetMs + 500));
  });
  return {
    get listeners() { return listeners; },
    get documentListeners() { return documentListeners; },
    get running() { return started; },
    start({ nodes, next, source, sources = source === undefined ? [] : [source], budgetMs, document } = {}) {
      return serial(async () => {
        stop();
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
          worker.addEventListener('error', event => { event.preventDefault?.(); if (worker === activeWorker) fail(Error(event.message ?? 'Script worker failed')); });
        } else {
          worker.on('message', message => { if (worker === activeWorker) receive(message); });
          worker.on('error', error => { if (worker === activeWorker) fail(error); });
        }
        try {
          await call('initialize', { wasmURL, wasmBytes, document, leanModuleURL }, 10000);
          const snapshot = Number.isInteger(next) ? { nodes, next } : nodes;
          const batch = accept(await call('start', { snapshot, sources, budgetMs, now: now() }, watchdogMs ?? budgetMs + 500));
          started = true;
          return batch;
        } catch (error) { stop(); throw error; }
      });
    },
    dispatch(event, { budgetMs } = {}) {
      if (!started) return Promise.reject(Error('Script session is not running'));
      if (!event || !EVENT_TYPES.includes(event.type)) return Promise.reject(Error('Unknown script event type'));
      let wire;
      if (event.type === 'click' || event.type === 'input') {
        const onNode = validId(event.nodeId) && listeners.some(l => l.nodeId === event.nodeId && l.type === event.type);
        const onDocument = documentListeners.includes(event.type) && (event.nodeId === undefined || event.nodeId === null || (validId(event.nodeId) && ids.has(event.nodeId)));
        if (!onNode && !onDocument) return Promise.reject(Error(`Unknown script ${event.type} target`));
        wire = { type: event.type, ...(validId(event.nodeId) ? { nodeId: event.nodeId } : {}) };
      } else {
        if (!boundedString(event.key ?? '', 64) || !boundedString(event.code ?? '', 64)) return Promise.reject(Error('Invalid key event'));
        wire = { type: event.type, key: event.key ?? '', code: event.code ?? '', shiftKey: !!event.shiftKey, metaKey: !!event.metaKey, altKey: !!event.altKey, ctrlKey: !!event.ctrlKey };
      }
      return turn('dispatch', { event: wire }, budgetMs);
    },
    // Run the timers that are due now (HTML §8.6), at most 64 callbacks.
    timers({ budgetMs } = {}) { return turn('timers', {}, budgetMs); },
    // Run the animation frame callbacks (HTML §8.10 "run the animation frame callbacks").
    frame({ budgetMs } = {}) { return turn('frame', {}, budgetMs); },
    reset
  };
}
