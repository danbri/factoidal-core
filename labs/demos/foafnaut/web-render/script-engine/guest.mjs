// This function is serialized as source and runs INSIDE QuickJS, never in the
// browser's JS realm. It exposes only a bounded projection of Lean node handles.
//
// Timers, microtasks, animation frames and event listener order are decided by
// Lean (`L4Factoidal.EventLoop`, op `eventLoop`) through `__factoidalLoop`.
// This code keeps the callbacks under opaque handles and runs the one Lean
// names. It never uses a host timer. Without the Lean engine those APIs are
// absent and a click runs the target's listeners only, as before.
export function installGuest(snapshot) {
  const stringify = JSON.stringify.bind(JSON), parse = JSON.parse.bind(JSON);
  const freeze = Object.freeze.bind(Object);
  const own = Object.hasOwn;
  const nodes = new Map(), callbacks = new Map();
  const records = new Map(snapshot.map(item => [item.id, { ...item, attributes: { ...item.attributes } }]));
  let connected = new Set(records.keys());
  const mutate = typeof globalThis.__factoidalDOM === 'function' ? globalThis.__factoidalDOM : null;
  if (mutate) delete globalThis.__factoidalDOM;
  const loopCall = typeof globalThis.__factoidalLoop === 'function' ? globalThis.__factoidalLoop : null;
  if (loopCall) delete globalThis.__factoidalLoop;
  let commands = [], logs = [], lastDefaultPrevented = false;
  const emit = command => {
    if (commands.length >= 256) throw new RangeError('DOM command budget exceeded');
    if (mutate) {
      const updated = parse(mutate(stringify(command)));
      if (!Array.isArray(updated.nodes)) throw new TypeError('Invalid Lean DOM response');
      connected = new Set(updated.nodes.map(item => item.id));
      for (const item of updated.nodes) records.set(item.id, item);
    }
    commands.push(command);
  };
  const text = value => {
    value = String(value ?? '');
    if (value.length > 65536) throw new RangeError('DOM string budget exceeded');
    return value;
  };
  const log = value => { if (logs.length < 32) logs.push(text(value)); };
  // HTML "report the exception": the error goes to the console; the loop goes on.
  const report = error => log(`Uncaught ${error?.name ?? 'Error'}: ${error?.message ?? error}`);

  // ---- The event loop, decided by Lean ----
  const lean = (action, fields = {}) => {
    if (!loopCall) throw new TypeError('The event loop needs the Lean engine');
    return parse(loopCall(stringify({ action, ...fields })));
  };
  const handles = new Map(), timerHandles = new Map();
  let nextHandle = 1, currentEvent = null;
  const handleOf = entry => {
    if (handles.size >= 65536) throw new RangeError('Callback budget exceeded');
    const handle = nextHandle++;
    handles.set(handle, entry);
    return handle;
  };
  // WebIDL `long` (ToInt32), then HTML §8.6 step "If timeout is less than 0, then set timeout to 0".
  const timeoutOf = value => Math.max(0, Number(value) | 0);
  const timer = (handler, timeout, args, periodic) => {
    // A string handler is compiled as a classic script (HTML §8.6 step 9.2).
    const fn = typeof handler === 'function' ? handler : (source => () => (0, eval)(source))(String(handler));
    const handle = handleOf({ fn, args, periodic });
    const { id } = lean('setTimer', { callback: handle, timeout: timeoutOf(timeout), periodic });
    timerHandles.set(id, handle);
    return id;
  };
  const clearTimer = id => {
    id = Number(id) | 0;
    if (id <= 0) return;
    lean('clearTimer', { id });
    handles.delete(timerHandles.get(id));
    timerHandles.delete(id);
  };
  const checkpoint = () => {
    for (let count = 0; count < 10000; count++) {
      const { callback } = lean('microtaskStep');
      if (callback === null) return;
      const entry = handles.get(callback);
      handles.delete(callback);
      if (entry) try { entry.fn.call(globalThis); } catch (error) { report(error); }
    }
    throw new RangeError('Microtask budget exceeded');
  };
  if (loopCall) {
    const define = (name, value) => Object.defineProperty(globalThis, name, { value, writable: true, configurable: true });
    define('setTimeout', (handler, timeout = 0, ...args) => timer(handler, timeout, args, false));
    define('setInterval', (handler, timeout = 0, ...args) => timer(handler, timeout, args, true));
    define('clearTimeout', clearTimer);
    define('clearInterval', clearTimer);
    define('queueMicrotask', callback => {
      if (typeof callback !== 'function') throw new TypeError('queueMicrotask requires a function');
      lean('queueMicrotask', { callback: handleOf({ fn: callback }) });
    });
    define('requestAnimationFrame', callback => {
      if (typeof callback !== 'function') throw new TypeError('requestAnimationFrame requires a function');
      const handle = handleOf({ fn: callback, frame: true });
      const { id } = lean('requestFrame', { callback: handle });
      timerHandles.set(-id, handle);
      return id;
    });
    define('cancelAnimationFrame', id => {
      id = Number(id) | 0;
      if (id <= 0) return;
      lean('cancelFrame', { id });
      handles.delete(timerHandles.get(-id));
      timerHandles.delete(-id);
    });
  }

  // ---- Event listeners (DOM §2.7), in the order they were added ----
  const listenerList = [];
  const BUBBLES = new Set(['click', 'dblclick', 'mousedown', 'mouseup', 'pointerdown', 'pointerup', 'keydown', 'keyup', 'input', 'change', 'submit']);
  const captureOf = options => typeof options === 'boolean' ? options : Boolean(options?.capture);
  const addListener = (nodeId, type, callback, options) => {
    if (callback === null || callback === undefined) return;
    if (typeof callback !== 'function' && typeof callback?.handleEvent !== 'function') throw new TypeError('Listener must be a function or have handleEvent');
    type = text(type);
    const capture = captureOf(options);
    if (listenerList.some(entry => !entry.removed && entry.node === nodeId && entry.type === type && entry.callback === callback && entry.capture === capture)) return;
    if (listenerList.length >= 4096) throw new RangeError('Listener budget exceeded');
    const entry = { node: nodeId, type, callback, capture, once: Boolean(options?.once), removed: false };
    entry.handle = handleOf({ listener: entry });
    listenerList.push(entry);
  };
  const removeListener = (nodeId, type, callback, options) => {
    const capture = captureOf(options);
    const index = listenerList.findIndex(entry => !entry.removed && entry.node === nodeId && entry.type === String(type) && entry.callback === callback && entry.capture === capture);
    if (index < 0) return;
    const [entry] = listenerList.splice(index, 1);
    entry.removed = true;
    handles.delete(entry.handle);
  };

  for (const item of snapshot) {
    const record = () => records.get(item.id);
    const listeners = [];
    const node = Object.freeze({
      nodeId: item.id, tagName: item.tagName,
      get isConnected() { return connected.has(item.id); },
      get parentElement() { const parent = record().parent; return parent === null || parent === undefined ? null : nodes.get(parent) ?? null; },
      get textContent() { return record().textContent; },
      set textContent(value) {
        value = text(value);
        emit({ op: 'setTextContent', nodeId: item.id, value });
        // A detached handle remains usable; Lean's connected snapshot omits it.
        record().textContent = value;
      },
      getAttribute(name) {
        const attributes = record().attributes, key = String(name);
        return own(attributes, key) ? attributes[key] : null;
      },
      setAttribute(name, value) {
        name = text(name); value = text(value);
        emit({ op: 'setAttribute', nodeId: item.id, name, value });
        record().attributes[name] = value;
      },
      addEventListener(type, callback, options) {
        if (!loopCall) {
          if (type !== 'click' || typeof callback !== 'function') throw new TypeError('Only click listeners are supported');
          if (listeners.length >= 32) throw new RangeError('Listener budget exceeded');
          if (!listeners.includes(callback)) listeners.push(callback);
          return;
        }
        addListener(item.id, type, callback, options);
      },
      removeEventListener(type, callback, options) {
        if (!loopCall) { const index = listeners.indexOf(callback); if (type === 'click' && index >= 0) listeners.splice(index, 1); return; }
        removeListener(item.id, type, callback, options);
      },
      get onclick() { return callbacks.get(item.id)?.onclick ?? null; },
      set onclick(callback) {
        if (callback !== null && typeof callback !== 'function') throw new TypeError('onclick requires a function');
        const state = callbacks.get(item.id);
        // HTML §8.1.8.1: the event handler's listener is added when it is first set.
        if (loopCall && callback && !state.handlerAdded) {
          state.handlerAdded = true;
          addListener(item.id, 'click', state.handler, false);
        }
        state.onclick = callback;
      }
    });
    const state = { node, listeners, onclick: null, handlerAdded: false };
    state.handler = function (event) {
      if (state.onclick && state.onclick.call(this, event) === false) event.preventDefault();
    };
    callbacks.set(item.id, state);
    nodes.set(item.id, node);
  }

  // DOM §2.9 "dispatch" for an event at `target`, with the plan from Lean.
  const dispatch = (type, target) => {
    const path = [];
    for (let id = target; id !== null && id !== undefined && path.length < 4096; id = records.get(id)?.parent) path.unshift(id);
    const entries = listenerList.filter(entry => entry.type === type && path.includes(entry.node));
    const bubbles = BUBBLES.has(type);
    let visits = lean('dispatch', { path, bubbles, listeners: entries.map(entry => ({ node: entry.node, capture: entry.capture, callback: entry.handle })) }).visits;
    let stop = false, immediate = false, defaultPrevented = false, current = null;
    const event = freeze({
      type, bubbles, cancelable: true, isTrusted: true,
      target: nodes.get(target) ?? null,
      get currentTarget() { return current ? nodes.get(current.node) : null; },
      get eventPhase() { return current ? current.phase : 0; },
      get defaultPrevented() { return defaultPrevented; },
      get timeStamp() { return clock; },
      NONE: 0, CAPTURING_PHASE: 1, AT_TARGET: 2, BUBBLING_PHASE: 3,
      preventDefault() { defaultPrevented = true; },
      stopPropagation() { stop = true; },
      stopImmediatePropagation() { stop = true; immediate = true; }
    });
    const previous = currentEvent;
    currentEvent = event;
    try {
      for (let index = 0; index < visits.length;) {
        const visit = visits[index], entry = handles.get(visit.callback)?.listener;
        if (entry && !entry.removed) {
          current = visit;
          if (entry.once) removeListener(entry.node, entry.type, entry.callback, entry.capture);
          try {
            const callback = entry.callback;
            if (typeof callback === 'function') callback.call(nodes.get(visit.node), event);
            else callback.handleEvent(event);
          } catch (error) { report(error); }
          // HTML "clean up after running script": a microtask checkpoint after each listener.
          checkpoint();
        }
        if (stop) {
          // Lean gives the visits that still run: the rest of this invoke, or none.
          visits = lean('afterStop', { visits, index, immediate }).visits;
          stop = false;
          if (immediate) break;
          index = 0;
          continue;
        }
        index++;
      }
    } finally { current = null; currentEvent = previous; }
    lastDefaultPrevented = defaultPrevented;
    return !defaultPrevented;
  };
  let clock = 0;
  // The worker passes each callback Lean names here.
  Object.defineProperty(globalThis, '__factoidalRun', { value: wire => {
    const run = parse(wire);
    clock = run.now ?? clock;
    if (run.kind === 'task' && run.event) { dispatch(run.event.type, run.event.target); return; }
    const entry = handles.get(run.callback);
    if (!entry) return;
    if (!entry.periodic) handles.delete(run.callback);
    try {
      if (run.kind === 'frame') entry.fn.call(globalThis, run.now);
      else entry.fn.apply(globalThis, entry.args ?? []);
    } catch (error) { report(error); }
  } });
  Object.defineProperty(globalThis, '__factoidalCheckpoint', { value: () => { if (loopCall) checkpoint(); } });
  const getElementById = id => [...connected].map(key => nodes.get(key)).find(node => node && node.getAttribute('id') === String(id)) ?? null;
  Object.defineProperty(globalThis, 'document', { value: Object.freeze({
    getElementById,
    querySelector(selector) {
      if (typeof selector !== 'string' || !/^#[A-Za-z_][A-Za-z0-9_-]*$/.test(selector)) throw new TypeError('Only simple #id selectors are supported');
      return getElementById(selector.slice(1));
    }
  }) });
  Object.defineProperty(globalThis, 'console', { value: Object.freeze({ log(...values) {
    log(values.map(String).join(' '));
  } }) });
  // Without the Lean engine: the earlier synchronous click at the target only.
  Object.defineProperty(globalThis, '__factoidalDispatch', { value: wire => {
    const event = parse(wire), state = callbacks.get(event.nodeId);
    if (event.type !== 'click' || !state) throw new TypeError('Unknown click target');
    // Each event owns its flag. A saved event cannot cancel a later click.
    let defaultPrevented = false;
    const delivered = freeze({ type: 'click', target: state.node, currentTarget: state.node,
      cancelable: true,
      get defaultPrevented() { return defaultPrevented; },
      preventDefault() { defaultPrevented = true; }
    });
    if (state.onclick && state.onclick.call(state.node, delivered) === false) delivered.preventDefault();
    for (const callback of state.listeners.slice()) callback.call(state.node, delivered);
    lastDefaultPrevented = defaultPrevented;
  } });
  Object.defineProperty(globalThis, '__factoidalDrain', { value: () => {
    const listeners = [];
    if (loopCall) {
      const seen = new Set();
      for (const entry of listenerList) if (entry.type === 'click' && connected.has(entry.node) && !seen.has(entry.node)) { seen.add(entry.node); listeners.push({ nodeId: entry.node, type: 'click' }); }
    } else {
      for (const [nodeId, state] of callbacks) if (connected.has(nodeId) && (state.onclick || state.listeners.length)) listeners.push({ nodeId, type: 'click' });
    }
    const wire = stringify({ commands, listeners, logs, defaultPrevented: lastDefaultPrevented });
    commands = []; logs = []; lastDefaultPrevented = false;
    return wire;
  } });
}

// Parse data as JSON: embedding it as an object literal changes the meaning
// of a real "__proto__" attribute before the binding can inspect it.
export const bootstrap = nodes => `(${installGuest.toString()})(JSON.parse(${JSON.stringify(JSON.stringify(nodes))}));`;
