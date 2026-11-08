// prelude.js: the page objects that scripts see, for QuickJS-NG in the Lean WasmVM engine
// (record: docs/designissues/2026-11-08-page-scripts.md). build-quickjs.sh puts this file
// into the module as a C string; qjs_new evaluates it once and calls it with `n`, the
// native functions of qjs_wasmvm_entry.c. `n` is never a global.
//
// The DOM is not here. Each node is a number of the Lean DOM arena; each read and each
// change is one `foafnaut_dom` import, which Lean serves on the arena (changes are typed
// commands). Lean also keeps the event listeners, the timers and the animation frame
// callbacks, and decides their order: `n.plan` gives the listener order of one dispatch
// (L4Factoidal.EventLoop.Dispatch.plan), and timers and frames are tasks of
// L4Factoidal.EventLoop. This file only keeps the JavaScript functions, by number.
//
// Negative numbers from `n` are errors: -1 none, -2 not a node of the right type,
// -3 InvalidCharacterError, -4 HierarchyRequestError, -5 over a budget, -9 NotFoundError,
// -10 NotSupportedError.
(function (n0) {
  'use strict';
  // The natives, with every change of the tree also queued as a mutation record (DOM §4.3)
  // for MutationObserver. The change itself is Lean's; this only reports it.
  const n = Object.assign({}, n0);
  const WINDOW = 0x0FFFFFFF;
  let nextTarget = 0x10000000;
  const define = (o, name, value) => Object.defineProperty(o, name, { value, writable: true, configurable: true });
  const consts = (o, table) => { for (const k in table) Object.defineProperty(o, k, { value: table[k], enumerable: true }); };

  // ---- DOMException -------------------------------------------------------------
  const codes = { IndexSizeError: 1, HierarchyRequestError: 3, WrongDocumentError: 4, InvalidCharacterError: 5,
    NoModificationAllowedError: 7, NotFoundError: 8, NotSupportedError: 9, InvalidStateError: 11, SyntaxError: 12,
    InvalidModificationError: 13, NamespaceError: 14, InvalidAccessError: 15, TypeMismatchError: 17,
    SecurityError: 18, NetworkError: 19, AbortError: 20, TimeoutError: 23, DataCloneError: 25 };
  class DOMException extends Error {
    constructor(message = '', name = 'Error') {
      super(String(message));
      define(this, 'name', String(name));
    }
    get code() { return codes[this.name] ?? 0; }
  }
  Object.defineProperty(DOMException.prototype, 'name', { value: 'Error', writable: true, configurable: true });
  const legacy = { INDEX_SIZE_ERR: 1, DOMSTRING_SIZE_ERR: 2, HIERARCHY_REQUEST_ERR: 3, WRONG_DOCUMENT_ERR: 4,
    INVALID_CHARACTER_ERR: 5, NO_DATA_ALLOWED_ERR: 6, NO_MODIFICATION_ALLOWED_ERR: 7, NOT_FOUND_ERR: 8,
    NOT_SUPPORTED_ERR: 9, INUSE_ATTRIBUTE_ERR: 10, INVALID_STATE_ERR: 11, SYNTAX_ERR: 12,
    INVALID_MODIFICATION_ERR: 13, NAMESPACE_ERR: 14, INVALID_ACCESS_ERR: 15, VALIDATION_ERR: 16,
    TYPE_MISMATCH_ERR: 17, SECURITY_ERR: 18, NETWORK_ERR: 19, ABORT_ERR: 20, URL_MISMATCH_ERR: 21,
    QUOTA_EXCEEDED_ERR: 22, TIMEOUT_ERR: 23, INVALID_NODE_TYPE_ERR: 24, DATA_CLONE_ERR: 25 };
  consts(DOMException, legacy); consts(DOMException.prototype, legacy);
  const fail = code => {
    switch (code) {
      case -2: throw new TypeError('not a node of the right type');
      case -3: throw new DOMException('The string contains invalid characters.', 'InvalidCharacterError');
      case -4: throw new DOMException('The operation would yield an incorrect node tree.', 'HierarchyRequestError');
      case -5: throw new RangeError('DOM budget exceeded');
      case -9: throw new DOMException('The object can not be found here.', 'NotFoundError');
      case -10: throw new DOMException('The operation is not supported.', 'NotSupportedError');
      default: throw new TypeError('DOM error ' + code);
    }
  };
  const chk = r => (typeof r === 'number' && r < -1) ? fail(r) : r;

  // ---- callbacks, by number ------------------------------------------------------
  const callbacks = new Map(); let nextCallback = 1;
  const register = f => { const id = nextCallback++; callbacks.set(id, f); return id; };

  // ---- nodes ---------------------------------------------------------------------
  const wrappers = new Map();
  const ids = new WeakMap();
  const idOf = x => { const id = ids.get(x); if (id === undefined) throw new TypeError('not a node'); return id; };
  const nodeId = x => { const id = ids.get(x); if (id === undefined || id >= WINDOW) throw new TypeError("parameter is not of type 'Node'"); return id; };
  const wrap = id => (id < 0 ? null : (wrappers.get(id) ?? make(id)));
  const info = (id, which) => n.info(id, which);
  const kids = id => n.kids(id);
  let EventTargetProto, protoOf;
  const make = id => {
    const t = info(id, 0);
    if (t < 0) return null;
    const o = Object.create(protoOf(id, t));
    ids.set(o, id); wrappers.set(id, o);
    return o;
  };
  const isElement = x => x instanceof Element;
  const str = (id, which) => { const s = n.str(id, which); return typeof s === 'number' ? (s === -1 ? null : fail(s)) : s; };

  // ---- events --------------------------------------------------------------------
  const ev = new WeakMap();
  const state = e => { const s = ev.get(e); if (!s) throw new TypeError('not an Event'); return s; };
  const now = () => performance.now();
  class Event {
    constructor(type, init = undefined) {
      if (arguments.length < 1) throw new TypeError("Failed to construct 'Event': 1 argument required");
      const d = init == null ? {} : init;
      if (typeof d !== 'object' && typeof d !== 'function') throw new TypeError('EventInit must be an object');
      ev.set(this, { type: String(type), bubbles: !!d.bubbles, cancelable: !!d.cancelable, composed: !!d.composed,
        initialized: true, dispatching: false, stop: false, stopImmediate: false, canceled: false, passive: false,
        target: null, currentTarget: null, phase: 0, trusted: false, timeStamp: now(), path: [] });
    }
    get type() { return state(this).type; }
    get target() { return state(this).target; }
    get srcElement() { return state(this).target; }
    get currentTarget() { return state(this).currentTarget; }
    get eventPhase() { return state(this).phase; }
    get bubbles() { return state(this).bubbles; }
    get cancelable() { return state(this).cancelable; }
    get composed() { return state(this).composed; }
    get defaultPrevented() { return state(this).canceled; }
    get returnValue() { return !state(this).canceled; }
    set returnValue(v) { if (!v) this.preventDefault(); }
    get cancelBubble() { return state(this).stop; }
    set cancelBubble(v) { if (v) state(this).stop = true; }
    get timeStamp() { return state(this).timeStamp; }
    get isTrusted() { return state(this).trusted; }
    composedPath() { const s = state(this); return s.dispatching ? s.path.slice() : []; }
    stopPropagation() { state(this).stop = true; }
    stopImmediatePropagation() { const s = state(this); s.stop = true; s.stopImmediate = true; }
    preventDefault() { const s = state(this); if (s.cancelable && !s.passive) s.canceled = true; }
    initEvent(type, bubbles = false, cancelable = false) {
      if (arguments.length < 1) throw new TypeError('initEvent: 1 argument required');
      const s = state(this);
      if (s.dispatching) return;
      Object.assign(s, { type: String(type), bubbles: !!bubbles, cancelable: !!cancelable, initialized: true,
        stop: false, stopImmediate: false, canceled: false, target: null });
    }
  }
  const phases = { NONE: 0, CAPTURING_PHASE: 1, AT_TARGET: 2, BUBBLING_PHASE: 3 };
  consts(Event, phases); consts(Event.prototype, phases);
  class CustomEvent extends Event {
    constructor(type, init = undefined) { super(type, init); state(this).detail = init?.detail ?? null; }
    get detail() { return state(this).detail ?? null; }
    initCustomEvent(type, bubbles = false, cancelable = false, detail = null) {
      if (state(this).dispatching) return;
      this.initEvent(type, bubbles, cancelable); state(this).detail = detail;
    }
  }
  class UIEvent extends Event {
    constructor(type, init = undefined) { super(type, init); const s = state(this); s.view = init?.view ?? null; s.detail = init?.detail ?? 0; }
    get view() { return state(this).view ?? null; }
    get detail() { return state(this).detail ?? 0; }
  }
  class MouseEvent extends UIEvent {
    constructor(type, init = undefined) {
      super(type, init);
      const s = state(this), d = init ?? {};
      for (const k of ['screenX', 'screenY', 'clientX', 'clientY', 'button', 'buttons']) s[k] = Number(d[k] ?? 0);
      for (const k of ['ctrlKey', 'shiftKey', 'altKey', 'metaKey']) s[k] = !!d[k];
      s.relatedTarget = d.relatedTarget ?? null;
    }
  }
  for (const k of ['screenX', 'screenY', 'clientX', 'clientY', 'button', 'buttons', 'ctrlKey', 'shiftKey', 'altKey', 'metaKey', 'relatedTarget'])
    Object.defineProperty(MouseEvent.prototype, k, { get() { return state(this)[k]; }, configurable: true });
  class KeyboardEvent extends UIEvent {
    constructor(type, init = undefined) { super(type, init); const s = state(this); s.key = String(init?.key ?? ''); s.code = String(init?.code ?? ''); }
    get key() { return state(this).key; }
    get code() { return state(this).code; }
  }
  class FocusEvent extends UIEvent {}
  class ErrorEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init);
      const s = state(this), d = init ?? {};
      s.message = String(d.message ?? ''); s.filename = String(d.filename ?? ''); s.lineno = d.lineno >>> 0; s.colno = d.colno >>> 0; s.error = d.error;
    }
    get message() { return state(this).message; }
    get filename() { return state(this).filename; }
    get lineno() { return state(this).lineno; }
    get colno() { return state(this).colno; }
    get error() { return state(this).error; }
  }
  class PromiseRejectionEvent extends Event {
    constructor(type, init) { super(type, init); state(this).promise = init?.promise; state(this).reason = init?.reason; }
    get promise() { return state(this).promise; }
    get reason() { return state(this).reason; }
  }

  // ---- listeners -----------------------------------------------------------------
  // Each listener is one callback number. Lean keeps (target, type, capture, number) and
  // gives the order of a dispatch; this map keeps the function and the flags.
  const records = new Map();          // callback number -> record
  const byTarget = new Map();         // target id -> array of records, in the order added
  const flatten = o => (o !== null && typeof o === 'object') ? { capture: !!o.capture, once: !!o.once, passive: o.passive === undefined ? undefined : !!o.passive, signal: o.signal } : { capture: !!o };
  const addListener = (target, type, callback, options) => {
    const id = idOf(target);
    const o = flatten(options);
    if (callback === null || callback === undefined) return;
    if (o.signal !== undefined && !(o.signal instanceof AbortSignal)) throw new TypeError("member signal is not of type 'AbortSignal'");
    if (o.signal?.aborted) return;
    type = String(type);
    const list = byTarget.get(id) ?? [];
    if (list.some(r => r.type === type && r.callback === callback && r.capture === o.capture)) return;
    const passive = o.passive ?? ((id === WINDOW || id === 0 || id === docElement() || id === docBody()) &&
      ['touchstart', 'touchmove', 'wheel', 'mousewheel'].includes(type));
    const r = { target, type, callback, capture: o.capture, once: o.once, passive, removed: false, cb: 0 };
    r.cb = register(r);
    list.push(r); byTarget.set(id, list); records.set(r.cb, r);
    chk(n.listen(id, type, r.cb, o.capture ? 1 : 0));
    if (o.signal) o.signal.addEventListener('abort', () => removeRecord(r));
  };
  const removeRecord = r => {
    if (r.removed) return;
    r.removed = true;
    const id = ids.get(r.target);
    const list = byTarget.get(id);
    if (list) { const i = list.indexOf(r); if (i >= 0) list.splice(i, 1); }
    records.delete(r.cb); callbacks.delete(r.cb);
    n.unlisten(r.cb);
  };
  const removeListener = (target, type, callback, options) => {
    const id = idOf(target), capture = flatten(options).capture;
    const list = byTarget.get(id) ?? [];
    const r = list.find(r => r.type === String(type) && r.callback === callback && r.capture === capture);
    if (r) removeRecord(r);
  };

  // ---- reporting an exception (HTML "report an exception") -------------------------
  let reporting = false;
  const report = e => {
    const message = e instanceof Error ? `${e.name}: ${e.message}` : 'Uncaught ' + String(e);
    if (reporting) { n.log('Uncaught (in error handler) ' + message); return; }
    const stack = e instanceof Error && typeof e.stack === 'string' ? e.stack.split('\n').slice(0, 3).join(' | ') : '';
    reporting = true;
    try {
      const event = new ErrorEvent('error', { message, error: e, cancelable: true, filename: '', lineno: 0, colno: 0 });
      state(event).trusted = true;
      const notCanceled = dispatch(window, event);
      if (notCanceled) n.log('Uncaught ' + message + (stack ? ' at ' + stack : ''));
    } finally { reporting = false; }
  };

  // ---- dispatch (DOM §2.9), with the order from Lean -------------------------------
  const invokeListener = (r, event, s) => {
    if (r.removed) return;
    if (r.once) removeRecord(r);
    s.passive = !!r.passive;
    const saved = globalEvent;
    globalEvent = event;
    try {
      const f = r.callback;
      if (typeof f === 'function') f.call(s.currentTarget, event);
      else {
        const h = f.handleEvent;
        if (typeof h !== 'function') throw new TypeError('handleEvent is not a function');
        h.call(f, event);
      }
    } catch (e) { report(e); }
    finally { globalEvent = saved; s.passive = false; }
  };
  const dispatch = (target, event) => {
    const s = state(event);
    if (s.dispatching || !s.initialized) throw new DOMException('The event is already being dispatched.', 'InvalidStateError');
    const tid = idOf(target);
    s.dispatching = true; s.target = target;
    // Lean answers [path length, path (target first)..., then per listener call:
    // callback, node, phase + 8 * capture, depth]: L4Factoidal.EventLoop.Dispatch.plan.
    const plan = chk(n.plan(tid, s.type, s.bubbles ? 1 : 0));
    const k = plan[0];
    s.path = []; for (let i = k; i >= 1; i--) s.path.push(wrapTarget(plan[i]));
    let stopAt = null;
    for (let i = k + 1; i + 3 < plan.length; i += 4) {
      const cb = plan[i], node = plan[i + 1], phase = plan[i + 2] & 7, capture = (plan[i + 2] & 8) !== 0, depth = plan[i + 3];
      // After stopPropagation the rest of the same invoke still runs: the same node and
      // the same pass (EventLoop.Dispatch.afterStop); after stopImmediatePropagation, none.
      if (s.stopImmediate) break;
      if (s.stop) {
        if (stopAt === null) break;
        if (stopAt.depth !== depth || stopAt.capture !== capture) break;
      }
      const r = records.get(cb);
      if (!r) continue;
      s.currentTarget = wrapTarget(node); s.phase = phase;
      invokeListener(r, event, s);
      if (s.stop && stopAt === null) stopAt = { depth, capture };
    }
    s.phase = 0; s.currentTarget = null; s.dispatching = false; s.stop = false; s.stopImmediate = false;
    return !s.canceled;
  };
  const wrapTarget = id => id === WINDOW ? window : (id >= 0x10000000 ? targets.get(id) ?? null : wrap(id));
  const targets = new Map();
  let globalEvent = undefined;

  class EventTarget {
    constructor() { const id = nextTarget++; ids.set(this, id); targets.set(id, this); }
    addEventListener(type, callback, options = {}) {
      if (arguments.length < 2) throw new TypeError("addEventListener: 2 arguments required");
      addListener(this === undefined || this === null ? window : this, type, callback, options);
    }
    removeEventListener(type, callback, options = {}) {
      if (arguments.length < 2) throw new TypeError("removeEventListener: 2 arguments required");
      removeListener(this === undefined || this === null ? window : this, type, callback, options);
    }
    dispatchEvent(event) {
      if (!(event instanceof Event)) throw new TypeError("parameter 1 is not of type 'Event'");
      state(event).trusted = false;
      return dispatch(this === undefined || this === null ? window : this, event);
    }
  }
  EventTargetProto = EventTarget.prototype;

  // Event handler IDL attributes (HTML §8.1.8.1).
  const handlerNames = ['abort', 'blur', 'cancel', 'change', 'click', 'close', 'contextmenu', 'dblclick', 'error', 'focus',
    'input', 'keydown', 'keypress', 'keyup', 'load', 'mousedown', 'mouseenter', 'mouseleave', 'mousemove', 'mouseout',
    'mouseover', 'mouseup', 'reset', 'resize', 'scroll', 'select', 'submit', 'toggle', 'wheel', 'animationend',
    'transitionend', 'pointerdown', 'pointerup', 'pointermove', 'message', 'unhandledrejection', 'rejectionhandled',
    'beforeunload', 'unload', 'hashchange', 'popstate', 'pageshow', 'pagehide', 'storage', 'online', 'offline'];
  const handlers = new WeakMap();
  const handlerOf = (t, name) => handlers.get(t)?.get(name)?.value ?? null;
  const setHandler = (t, name, f) => {
    let m = handlers.get(t); if (!m) handlers.set(t, m = new Map());
    let h = m.get(name);
    const value = (typeof f === 'function' || (typeof f === 'object' && f !== null)) ? f : null;
    if (!h) {
      if (value === null) return;
      h = { value };
      m.set(name, h);
      const special = name === 'error' && t === window;
      addListener(t, name, function (event) {
        const v = h.value;
        if (typeof v !== 'function') return;
        const r = special && event instanceof ErrorEvent
          ? v.call(this, event.message, event.filename, event.lineno, event.colno, event.error)
          : v.call(this, event);
        if (special ? r === true : r === false) event.preventDefault();
      }, false);
    } else h.value = value;
  };
  const addHandlers = proto => {
    for (const name of handlerNames)
      Object.defineProperty(proto, 'on' + name, { get() { return handlerOf(this, name); },
        set(f) { setHandler(this, name, f); }, configurable: true, enumerable: true });
  };

  // ---- Node and the node types -----------------------------------------------------
  const types = { ELEMENT_NODE: 1, ATTRIBUTE_NODE: 2, TEXT_NODE: 3, CDATA_SECTION_NODE: 4, ENTITY_REFERENCE_NODE: 5,
    ENTITY_NODE: 6, PROCESSING_INSTRUCTION_NODE: 7, COMMENT_NODE: 8, DOCUMENT_NODE: 9, DOCUMENT_TYPE_NODE: 10,
    DOCUMENT_FRAGMENT_NODE: 11, NOTATION_NODE: 12 };
  const positions = { DOCUMENT_POSITION_DISCONNECTED: 1, DOCUMENT_POSITION_PRECEDING: 2, DOCUMENT_POSITION_FOLLOWING: 4,
    DOCUMENT_POSITION_CONTAINS: 8, DOCUMENT_POSITION_CONTAINED_BY: 16, DOCUMENT_POSITION_IMPLEMENTATION_SPECIFIC: 32 };
  const listCache = new WeakMap();
  const liveList = (ids, proto) => {
    const target = Object.create(proto ?? NodeList.prototype);
    return new Proxy(target, {
      get(t, p, recv) {
        if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return wrap(ids()[Number(p)] ?? -1);
        if (p === 'length') return ids().length;
        if (p === Symbol.iterator) return function* () { for (const i of ids()) yield wrap(i); };
        return Reflect.get(t, p, recv);
      },
      has(t, p) { if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return Number(p) < ids().length; return Reflect.has(t, p); },
      ownKeys() { return [...ids().keys()].map(String); },
      getOwnPropertyDescriptor(t, p) {
        if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p) && Number(p) < ids().length)
          return { value: wrap(ids()[Number(p)]), enumerable: true, configurable: true, writable: false };
        return undefined;
      },
    });
  };
  class NodeList {
    constructor() { throw new TypeError('Illegal constructor'); }
    item(i) { return this[i >>> 0] ?? null; }
    forEach(f, thisArg) { const xs = [...this]; for (let i = 0; i < xs.length; i++) f.call(thisArg, xs[i], i, this); }
    entries() { return [...this].entries(); }
    keys() { return [...this].keys(); }
    values() { return [...this].values(); }
  }
  class HTMLCollection {
    constructor() { throw new TypeError('Illegal constructor'); }
    item(i) { return this[i >>> 0] ?? null; }
    namedItem(name) { for (const e of this) if (e.id === name || e.getAttribute('name') === name) return e; return null; }
  }
  const liveCollection = ids => liveList(ids, HTMLCollection.prototype);
  const staticList = xs => {
    const o = Object.create(NodeList.prototype);
    xs.forEach((x, i) => Object.defineProperty(o, i, { value: x, enumerable: true }));
    Object.defineProperty(o, 'length', { value: xs.length });
    o[Symbol.iterator] = function* () { yield* xs; };
    return o;
  };
  const collection = xs => {
    const o = Object.create(HTMLCollection.prototype);
    xs.forEach((x, i) => Object.defineProperty(o, i, { value: x, enumerable: true }));
    Object.defineProperty(o, 'length', { value: xs.length });
    o[Symbol.iterator] = function* () { yield* xs; };
    return o;
  };
  const descendants = id => {
    const out = [];
    const walk = k => { for (const c of kids(k)) { out.push(c); walk(c); } };
    walk(id);
    return out;
  };
  const elementsOf = id => descendants(id).filter(k => info(k, 0) === 1);
  const toNode = x => (x instanceof Node) ? nodeId(x) : chk(n.create(0, String(x)));
  const convertNodes = xs => {
    if (xs.length === 1) return toNode(xs[0]);
    const f = chk(n.create(2, ''));
    for (const x of xs) chk(n.insert(f, toNode(x), -1));
    return f;
  };
  class Node extends EventTarget {
    constructor() { throw new TypeError('Illegal constructor'); }
    get nodeType() { return info(nodeId(this), 0); }
    get nodeName() { return str(nodeId(this), 1); }
    get baseURI() { return document.URL; }
    get isConnected() { let k = nodeId(this); for (let i = 0; i < 1 << 20; i++) { const p = info(k, 1); if (p < 0) return k === 0; k = p; } return false; }
    get ownerDocument() { const id = nodeId(this); return info(id, 0) === 9 ? null : wrap(info(id, 7)); }
    getRootNode() { let k = nodeId(this); for (;;) { const p = info(k, 1); if (p < 0) return wrap(k); k = p; } }
    get parentNode() { return wrap(info(nodeId(this), 1)); }
    get parentElement() { const p = info(nodeId(this), 1); return p >= 0 && info(p, 0) === 1 ? wrap(p) : null; }
    hasChildNodes() { return info(nodeId(this), 6) > 0; }
    get childNodes() {
      let l = listCache.get(this);
      if (!l) { const id = nodeId(this); l = liveList(() => kids(id)); listCache.set(this, l); }
      return l;
    }
    get firstChild() { return wrap(info(nodeId(this), 2)); }
    get lastChild() { return wrap(info(nodeId(this), 3)); }
    get previousSibling() { return wrap(info(nodeId(this), 4)); }
    get nextSibling() { return wrap(info(nodeId(this), 5)); }
    get nodeValue() { const t = this.nodeType; return (t === 3 || t === 4 || t === 7 || t === 8) ? str(nodeId(this), 3) : null; }
    set nodeValue(v) { const t = this.nodeType; if (t === 3 || t === 4 || t === 7 || t === 8) chk(n.setText(nodeId(this), v === null ? '' : String(v))); }
    get textContent() { return str(nodeId(this), 4); }
    set textContent(v) { chk(n.setText(nodeId(this), v === null ? '' : String(v))); }
    normalize() { chk(n.treeOp(nodeId(this), 0, 2)); }
    cloneNode(deep = false) { return wrap(chk(n.clone(nodeId(this), deep ? 1 : 0))); }
    isEqualNode(other) { return other === null || other === undefined ? false : chk(n.treeOp(nodeId(this), nodeId(other), 1)) === 1; }
    isSameNode(other) { return this === other; }
    compareDocumentPosition(other) {
      const a = nodeId(other), b = nodeId(this);
      if (a === b) return 0;
      const chain = k => { const c = [k]; for (;;) { const p = info(k, 1); if (p < 0) return c; c.push(p); k = p; } };
      const ca = chain(a), cb = chain(b);
      if (ca[ca.length - 1] !== cb[cb.length - 1]) return 1 | 32 | (a < b ? 2 : 4);
      if (ca.includes(b)) return 16 | 4;
      if (cb.includes(a)) return 8 | 2;
      let i = ca.length - 1, j = cb.length - 1;
      while (ca[i - 1] === cb[j - 1]) { i--; j--; }
      const p = ca[i], xs = kids(p);
      return xs.indexOf(ca[i - 1]) < xs.indexOf(cb[j - 1]) ? 2 : 4;
    }
    contains(other) {
      if (other === null || other === undefined) return false;
      const a = nodeId(this); let k = nodeId(other);
      for (;;) { if (k === a) return true; k = info(k, 1); if (k < 0) return false; }
    }
    lookupNamespaceURI(prefix) { return (prefix === null || prefix === '') && isElement(this) ? this.namespaceURI : null; }
    isDefaultNamespace(ns) { return (ns === '' ? null : ns) === this.lookupNamespaceURI(null); }
    insertBefore(node, child) {
      if (arguments.length < 2) throw new TypeError('insertBefore: 2 arguments required');
      const c = child === null || child === undefined ? -1 : nodeId(child);
      chk(n.insert(nodeId(this), nodeId(node), c)); return node;
    }
    appendChild(node) { chk(n.insert(nodeId(this), nodeId(node), -1)); return node; }
    replaceChild(node, child) { chk(n.replace(nodeId(this), nodeId(node), nodeId(child))); return child; }
    removeChild(child) { chk(n.remove(nodeId(this), nodeId(child))); return child; }
  }
  consts(Node, types); consts(Node.prototype, types); consts(Node, positions); consts(Node.prototype, positions);
  // ParentNode and ChildNode mixins (DOM §4.2.6, §4.2.8).
  const parentNode = {
    get children() { const id = nodeId(this); return liveCollection(() => kids(id).filter(k => info(k, 0) === 1)); },
    get firstElementChild() { return wrap(kids(nodeId(this)).find(k => info(k, 0) === 1) ?? -1); },
    get lastElementChild() { return wrap(kids(nodeId(this)).findLast(k => info(k, 0) === 1) ?? -1); },
    get childElementCount() { return kids(nodeId(this)).filter(k => info(k, 0) === 1).length; },
    prepend(...xs) { chk(n.insert(nodeId(this), convertNodes(xs), info(nodeId(this), 2))); },
    append(...xs) { chk(n.insert(nodeId(this), convertNodes(xs), -1)); },
    replaceChildren(...xs) { const node = convertNodes(xs); const id = nodeId(this); for (const k of kids(id)) chk(n.remove(id, k)); chk(n.insert(id, node, -1)); },
    querySelector(sel) { return select(this, sel, true)[0] ?? null; },
    querySelectorAll(sel) { return staticList(select(this, sel, false)); },
    getElementsByTagName(name) { const id = nodeId(this); name = String(name);
      return liveCollection(() => elementsOf(id).filter(k => name === '*' || str(k, 0) === (info(k, 8) === 1 ? name.toLowerCase() : name) || str(k, 1) === name)); },
    getElementsByClassName(names) { const id = nodeId(this); const want = String(names).split(/[ \t\n\f\r]+/).filter(Boolean);
      return liveCollection(() => want.length === 0 ? [] : elementsOf(id).filter(k => { const c = (n.attr(k, 'class') ?? '').split(/[ \t\n\f\r]+/); return want.every(w => c.includes(w)); })); },
  };
  const childNode = {
    remove() { const id = nodeId(this), p = info(id, 1); if (p >= 0) chk(n.remove(p, id)); },
    before(...xs) { const id = nodeId(this), p = info(id, 1); if (p < 0) return;
      let prev = info(id, 4); while (prev >= 0 && xs.some(x => x instanceof Node && ids.get(x) === prev)) prev = info(prev, 4);
      const node = convertNodes(xs); chk(n.insert(p, node, prev < 0 ? info(p, 2) : info(prev, 5))); },
    after(...xs) { const id = nodeId(this), p = info(id, 1); if (p < 0) return;
      let next = info(id, 5); while (next >= 0 && xs.some(x => x instanceof Node && ids.get(x) === next)) next = info(next, 5);
      const node = convertNodes(xs); chk(n.insert(p, node, next)); },
    replaceWith(...xs) { const id = nodeId(this), p = info(id, 1); if (p < 0) return;
      let next = info(id, 5); while (next >= 0 && xs.some(x => x instanceof Node && ids.get(x) === next)) next = info(next, 5);
      const node = convertNodes(xs);
      if (info(id, 1) === p) chk(n.replace(p, node, id)); else chk(n.insert(p, node, next)); },
    get previousElementSibling() { let k = info(nodeId(this), 4); while (k >= 0 && info(k, 0) !== 1) k = info(k, 4); return wrap(k); },
    get nextElementSibling() { let k = info(nodeId(this), 5); while (k >= 0 && info(k, 0) !== 1) k = info(k, 5); return wrap(k); },
  };
  const mix = (cls, obj, names) => { for (const k of names ?? Object.keys(Object.getOwnPropertyDescriptors(obj)))
    Object.defineProperty(cls.prototype, k, Object.getOwnPropertyDescriptor(obj, k)); };

  class DOMTokenList {
    constructor() { throw new TypeError('Illegal constructor'); }
  }
  const tokenList = (el, attr) => {
    const o = Object.create(DOMTokenList.prototype);
    const get = () => (el.getAttribute(attr) ?? '').split(/[ \t\n\f\r]+/).filter(Boolean).filter((x, i, a) => a.indexOf(x) === i);
    const set = xs => el.setAttribute(attr, xs.join(' '));
    const check = t => { t = String(t); if (t === '') throw new DOMException('empty token', 'SyntaxError');
      if (/[ \t\n\f\r]/.test(t)) throw new DOMException('token has white space', 'InvalidCharacterError'); return t; };
    Object.defineProperties(o, {
      length: { get: () => get().length },
      value: { get: () => el.getAttribute(attr) ?? '', set: v => el.setAttribute(attr, String(v)) },
      item: { value: i => get()[i >>> 0] ?? null },
      contains: { value: t => get().includes(String(t)) },
      add: { value: (...ts) => { ts = ts.map(check); const xs = get(); for (const t of ts) if (!xs.includes(t)) xs.push(t); set(xs); } },
      remove: { value: (...ts) => { ts = ts.map(check); set(get().filter(x => !ts.includes(x))); } },
      toggle: { value: (t, force) => { t = check(t); const xs = get(); const has = xs.includes(t);
        if (has && force !== true) { set(xs.filter(x => x !== t)); return false; }
        if (!has && force !== false) { xs.push(t); set(xs); return true; } return has; } },
      replace: { value: (a, b) => { a = check(a); b = check(b); const xs = get(); const i = xs.indexOf(a); if (i < 0) return false; xs[i] = b; set(xs.filter((x, j, all) => all.indexOf(x) === j)); return true; } },
      toString: { value: () => el.getAttribute(attr) ?? '' },
      [Symbol.iterator]: { value: function* () { yield* get(); } },
    });
    return new Proxy(o, { get(t, p, r) { if (typeof p === 'string' && /^[0-9]+$/.test(p)) return get()[Number(p)]; return Reflect.get(t, p, r); } });
  };
  const tokenLists = new WeakMap();

  class Element extends Node {
    get tagName() { return str(nodeId(this), 1); }
    get localName() { return str(nodeId(this), 0); }
    get namespaceURI() { return str(nodeId(this), 2); }
    get prefix() { return str(nodeId(this), 5); }
    get id() { return n.attr(nodeId(this), 'id') ?? ''; }
    set id(v) { chk(n.setAttr(nodeId(this), 'id', String(v))); }
    get className() { return n.attr(nodeId(this), 'class') ?? ''; }
    set className(v) { chk(n.setAttr(nodeId(this), 'class', String(v))); }
    get classList() { let l = tokenLists.get(this); if (!l) tokenLists.set(this, l = tokenList(this, 'class')); return l; }
    getAttribute(name) { const r = n.attr(nodeId(this), String(name)); return typeof r === 'number' ? fail(r) : r; }
    getAttributeNS(ns, name) { return ns === null || ns === '' ? this.getAttribute(name) : null; }
    hasAttribute(name) { return this.getAttribute(name) !== null; }
    hasAttributes() { return this.getAttributeNames().length > 0; }
    setAttribute(name, value) {
      if (arguments.length < 2) throw new TypeError('setAttribute: 2 arguments required');
      chk(n.setAttr(nodeId(this), String(name), String(value)));
      if (/^on/i.test(String(name))) contentHandler(this, String(name).toLowerCase().slice(2), String(value));
    }
    setAttributeNS(ns, name, value) { this.setAttribute(name, value); }
    removeAttribute(name) { chk(n.removeAttr(nodeId(this), String(name))); }
    removeAttributeNS(ns, name) { this.removeAttribute(name); }
    toggleAttribute(name, force) {
      const has = this.hasAttribute(name);
      if (has && force !== true) { this.removeAttribute(name); return false; }
      if (!has && force !== false) { this.setAttribute(name, ''); return true; }
      return has;
    }
    getAttributeNames() { const s = str(nodeId(this), 6) ?? ''; const xs = s === '' ? [] : s.split('\u0000'); return xs.filter((x, i) => i % 2 === 0 && i + 1 < xs.length); }
    get attributes() {
      const s = str(nodeId(this), 6) ?? ''; const xs = s === '' ? [] : s.split('\u0000'); const out = [];
      for (let i = 0; i + 1 < xs.length; i += 2) out.push({ name: xs[i], localName: xs[i], value: xs[i + 1], namespaceURI: null, prefix: null, specified: true });
      const o = Object.create(NamedNodeMap.prototype);
      out.forEach((a, i) => { o[i] = a; });
      Object.defineProperty(o, 'length', { value: out.length });
      o.getNamedItem = name => out.find(a => a.name === String(name)) ?? null;
      o.item = i => out[i >>> 0] ?? null;
      o[Symbol.iterator] = function* () { yield* out; };
      return o;
    }
    matches(sel) { return matches(nodeId(this), parse(String(sel))); }
    webkitMatchesSelector(sel) { return this.matches(sel); }
    closest(sel) { const p = parse(String(sel)); let k = nodeId(this); while (k >= 0 && info(k, 0) === 1) { if (matches(k, p)) return wrap(k); k = info(k, 1); } return null; }
    insertAdjacentElement(where, el) { return insertAdjacent(this, where, el); }
    insertAdjacentText(where, text) { insertAdjacent(this, where, document.createTextNode(text)); }
    get innerHTML() { return kids(nodeId(this)).map(serialize).join(''); }
    get outerHTML() { return serialize(nodeId(this)); }
  }
  class NamedNodeMap { constructor() { throw new TypeError('Illegal constructor'); } }
  const insertAdjacent = (el, where, node) => {
    switch (String(where).toLowerCase()) {
      case 'beforebegin': if (!el.parentNode) return null; el.parentNode.insertBefore(node, el); return node;
      case 'afterbegin': el.insertBefore(node, el.firstChild); return node;
      case 'beforeend': el.appendChild(node); return node;
      case 'afterend': if (!el.parentNode) return null; el.parentNode.insertBefore(node, el.nextSibling); return node;
      default: throw new DOMException('bad position', 'SyntaxError');
    }
  };
  const voids = new Set(['area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'source', 'track', 'wbr']);
  const escapeText = s => s.replace(/&/g, '&amp;').replace(/ /g, '&nbsp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
  const serialize = k => {
    const t = info(k, 0);
    if (t === 3) { const p = info(k, 1); const raw = p >= 0 && ['style', 'script', 'xmp', 'iframe', 'noembed', 'noframes', 'plaintext'].includes(str(p, 0)); return raw ? str(k, 3) : escapeText(str(k, 3)); }
    if (t === 8) return '<!--' + str(k, 3) + '-->';
    if (t !== 1) return '';
    const name = str(k, 0), a = str(k, 6) ?? '', xs = a === '' ? [] : a.split('\u0000');
    let out = '<' + name;
    for (let i = 0; i + 1 < xs.length; i += 2) out += ' ' + xs[i] + '="' + xs[i + 1].replace(/&/g, '&amp;').replace(/ /g, '&nbsp;').replace(/"/g, '&quot;') + '"';
    out += '>';
    if (voids.has(name)) return out;
    return out + kids(k).map(serialize).join('') + '</' + name + '>';
  };
  class HTMLElement extends Element {
    get title() { return this.getAttribute('title') ?? ''; }
    set title(v) { this.setAttribute('title', v); }
    get lang() { return this.getAttribute('lang') ?? ''; }
    set lang(v) { this.setAttribute('lang', v); }
    get dir() { return this.getAttribute('dir') ?? ''; }
    set dir(v) { this.setAttribute('dir', v); }
    get hidden() { return this.hasAttribute('hidden'); }
    set hidden(v) { this.toggleAttribute('hidden', !!v); }
    get dataset() {
      const el = this;
      return new Proxy({}, {
        get: (t, p) => typeof p === 'string' ? el.getAttribute('data-' + p.replace(/[A-Z]/g, c => '-' + c.toLowerCase())) ?? undefined : undefined,
        set: (t, p, v) => { el.setAttribute('data-' + String(p).replace(/[A-Z]/g, c => '-' + c.toLowerCase()), String(v)); return true; },
      });
    }
    get style() { let s = styles.get(this); if (!s) styles.set(this, s = styleOf(this)); return s; }
    click() {
      if (clicking.has(this)) return;
      clicking.add(this);
      try {
        const e = new MouseEvent('click', { bubbles: true, cancelable: true, composed: true, view: window });
        dispatch(this, e);
      } finally { clicking.delete(this); }
    }
    focus() {}
    blur() {}
    get offsetWidth() { return 0; }
    get offsetHeight() { return 0; }
    getBoundingClientRect() { return { x: 0, y: 0, width: 0, height: 0, top: 0, left: 0, right: 0, bottom: 0 }; }
  }
  const clicking = new WeakSet();
  const styles = new WeakMap();
  const styleOf = el => new Proxy({}, {
    get(t, p) {
      if (p === 'cssText') return el.getAttribute('style') ?? '';
      if (p === 'getPropertyValue') return name => decls(el).get(String(name)) ?? '';
      if (p === 'setProperty') return (name, value) => { const d = decls(el); if (value === null || value === '') d.delete(String(name)); else d.set(String(name), String(value)); write(el, d); };
      if (p === 'removeProperty') return name => { const d = decls(el); const v = d.get(String(name)) ?? ''; d.delete(String(name)); write(el, d); return v; };
      if (typeof p !== 'string') return undefined;
      return decls(el).get(p.replace(/[A-Z]/g, c => '-' + c.toLowerCase())) ?? '';
    },
    set(t, p, v) {
      if (p === 'cssText') { el.setAttribute('style', String(v)); return true; }
      const d = decls(el), name = String(p).replace(/[A-Z]/g, c => '-' + c.toLowerCase());
      if (v === null || v === '') d.delete(name); else d.set(name, String(v));
      write(el, d); return true;
    },
  });
  const decls = el => { const m = new Map(); for (const part of (el.getAttribute('style') ?? '').split(';')) { const i = part.indexOf(':'); if (i > 0) m.set(part.slice(0, i).trim().toLowerCase(), part.slice(i + 1).trim()); } return m; };
  const write = (el, d) => el.setAttribute('style', [...d].map(([k, v]) => `${k}: ${v}`).join('; '));
  class HTMLUnknownElement extends HTMLElement {}
  const htmlClasses = {};
  const htmlClass = (name, tags) => { const c = ({ [name]: class extends HTMLElement {} })[name]; for (const t of tags) htmlClasses[t] = c; return c; };
  const elementClasses = [
    ['HTMLHtmlElement', ['html']], ['HTMLHeadElement', ['head']], ['HTMLBodyElement', ['body']], ['HTMLTitleElement', ['title']],
    ['HTMLMetaElement', ['meta']], ['HTMLLinkElement', ['link']], ['HTMLStyleElement', ['style']], ['HTMLScriptElement', ['script']],
    ['HTMLDivElement', ['div']], ['HTMLSpanElement', ['span']], ['HTMLParagraphElement', ['p']], ['HTMLAnchorElement', ['a']],
    ['HTMLButtonElement', ['button']], ['HTMLInputElement', ['input']], ['HTMLFormElement', ['form']], ['HTMLImageElement', ['img']],
    ['HTMLUListElement', ['ul']], ['HTMLOListElement', ['ol']], ['HTMLLIElement', ['li']], ['HTMLTableElement', ['table']],
    ['HTMLTableRowElement', ['tr']], ['HTMLTableCellElement', ['td', 'th']], ['HTMLHeadingElement', ['h1', 'h2', 'h3', 'h4', 'h5', 'h6']],
    ['HTMLPreElement', ['pre']], ['HTMLBRElement', ['br']], ['HTMLHRElement', ['hr']], ['HTMLLabelElement', ['label']],
    ['HTMLSelectElement', ['select']], ['HTMLOptionElement', ['option']], ['HTMLTextAreaElement', ['textarea']],
    ['HTMLIFrameElement', ['iframe']], ['HTMLCanvasElement', ['canvas']], ['HTMLTemplateElement', ['template']],
    ['HTMLDetailsElement', ['details']], ['HTMLFieldSetElement', ['fieldset']], ['HTMLDialogElement', ['dialog']],
    ['HTMLVideoElement', ['video']], ['HTMLAudioElement', ['audio']], ['HTMLSlotElement', ['slot']]];
  const named = {};
  for (const [name, tags] of elementClasses) named[name] = htmlClass(name, tags);
  Object.defineProperty(named.HTMLTemplateElement.prototype, 'content', { get() { return wrap(info(nodeId(this), 9)); }, configurable: true });
  for (const t of ['address', 'article', 'aside', 'footer', 'header', 'hgroup', 'main', 'nav', 'section', 'b', 'i', 'em', 'strong',
    'small', 'code', 'abbr', 'cite', 'dfn', 'kbd', 'mark', 'q', 's', 'samp', 'sub', 'sup', 'u', 'var', 'bdi', 'bdo', 'dd', 'dt',
    'figcaption', 'figure', 'noscript', 'ruby', 'rt', 'rp', 'summary', 'wbr', 'center', 'tt', 'big', 'nobr', 'acronym']) htmlClasses[t] = HTMLElement;
  class SVGElement extends Element {}
  class CharacterData extends Node {
    get data() { return str(nodeId(this), 3); }
    set data(v) { chk(n.setText(nodeId(this), v === null ? '' : String(v))); }
    get length() { return this.data.length; }
    substringData(offset, count) { const d = this.data; offset >>>= 0; if (offset > d.length) throw new DOMException('offset', 'IndexSizeError'); return d.substring(offset, offset + (count >>> 0)); }
    appendData(s) { this.data = this.data + String(s); }
    insertData(offset, s) { this.replaceData(offset, 0, s); }
    deleteData(offset, count) { this.replaceData(offset, count, ''); }
    replaceData(offset, count, s) {
      const d = this.data; offset >>>= 0; count >>>= 0;
      if (offset > d.length) throw new DOMException('offset', 'IndexSizeError');
      this.data = d.slice(0, offset) + String(s) + d.slice(Math.min(d.length, offset + count));
    }
  }
  class Text extends CharacterData {
    constructor(data = '') { return wrap(chk(n.create(0, String(data)))); }
    get wholeText() {
      const id = nodeId(this), p = info(id, 1);
      if (p < 0) return this.data;
      const xs = kids(p); let i = xs.indexOf(id), j = i;
      while (i > 0 && info(xs[i - 1], 0) === 3) i--;
      while (j + 1 < xs.length && info(xs[j + 1], 0) === 3) j++;
      return xs.slice(i, j + 1).map(k => str(k, 3)).join('');
    }
    splitText(offset) {
      const d = this.data; offset >>>= 0;
      if (offset > d.length) throw new DOMException('offset', 'IndexSizeError');
      const rest = d.slice(offset);
      const t = document.createTextNode(rest);
      const p = this.parentNode;
      if (p) p.insertBefore(t, this.nextSibling);
      this.data = d.slice(0, offset);
      return t;
    }
  }
  class CDATASection extends Text {}
  class Comment extends CharacterData {
    constructor(data = '') { return wrap(chk(n.create(1, String(data)))); }
  }
  class ProcessingInstruction extends CharacterData { get target() { return str(nodeId(this), 0); } }
  class DocumentType extends Node {
    get name() { return str(nodeId(this), 0); }
    get publicId() { return ''; }
    get systemId() { return ''; }
  }
  class DocumentFragment extends Node {
    constructor() { return wrap(chk(n.create(2, ''))); }
    getElementById(id) { return elementsOf(nodeId(this)).map(wrap).find(e => e.id === String(id)) ?? null; }
  }
  let readyState = 'loading';
  class Document extends Node {
    constructor() { throw new TypeError('Illegal constructor'); }
    get URL() { return location.href; }
    get documentURI() { return location.href; }
    get compatMode() { return 'CSS1Compat'; }
    get characterSet() { return 'UTF-8'; }
    get charset() { return 'UTF-8'; }
    get inputEncoding() { return 'UTF-8'; }
    get contentType() { return 'text/html'; }
    get readyState() { return readyState; }
    get defaultView() { return this === document ? window : null; }
    get location() { return this === document ? location : null; }
    get doctype() { return wrap(kids(nodeId(this)).find(k => info(k, 0) === 10) ?? -1); }
    get documentElement() { return wrap(kids(nodeId(this)).find(k => info(k, 0) === 1) ?? -1); }
    get head() { const h = this.documentElement; return h ? (h.children[0]?.localName === 'head' ? h.children[0] : [...h.children].find(e => e.localName === 'head') ?? null) : null; }
    get body() { const h = this.documentElement; return h ? [...h.children].find(e => e.localName === 'body' || e.localName === 'frameset') ?? null : null; }
    get title() { const t = elementsOf(nodeId(this)).find(k => str(k, 0) === 'title'); return t === undefined ? '' : (str(t, 4) ?? '').replace(/[ \t\n\f\r]+/g, ' ').trim(); }
    set title(v) { const t = elementsOf(nodeId(this)).find(k => str(k, 0) === 'title'); if (t !== undefined) chk(n.setText(t, String(v))); }
    get activeElement() { return this.body; }
    hasFocus() { return true; }
    get scripts() { return this.getElementsByTagName('script'); }
    get forms() { return this.getElementsByTagName('form'); }
    get images() { return this.getElementsByTagName('img'); }
    get links() { const id = nodeId(this); return liveCollection(() => elementsOf(id).filter(k => ['a', 'area'].includes(str(k, 0)) && n.attr(k, 'href') !== null)); }
    get currentScript() { return currentScript; }
    getElementById(id) { return wrap(n.byId(String(id))); }
    getElementsByName(name) { return staticList(elementsOf(nodeId(this)).filter(k => n.attr(k, 'name') === String(name)).map(wrap)); }
    createElement(name, options) { return wrap(chk(n.create(3, String(name)))); }
    createElementNS(ns, qname) {
      if (ns === 'http://www.w3.org/1999/xhtml') return this.createElement(String(qname).split(':').pop());
      return wrap(chk(n.create(4, (ns ?? '') + '\u0000' + String(qname))));
    }
    createTextNode(data) { return wrap(chk(n.create(0, String(data)))); }
    createComment(data) { return wrap(chk(n.create(1, String(data)))); }
    createDocumentFragment() { return wrap(chk(n.create(2, ''))); }
    createProcessingInstruction(target, data) { return wrap(chk(n.create(5, String(target) + '\u0000' + String(data)))); }
    createCDATASection(data) { return wrap(chk(n.create(6, String(data)))); }
    createEvent(name) {
      const map = { event: Event, events: Event, htmlevents: Event, customevent: CustomEvent, mouseevent: MouseEvent,
        mouseevents: MouseEvent, uievent: UIEvent, uievents: UIEvent, keyboardevent: KeyboardEvent, focusevent: FocusEvent,
        errorevent: ErrorEvent };
      const C = map[String(name).toLowerCase()];
      if (!C) throw new DOMException('The provided event type is not supported.', 'NotSupportedError');
      const e = new C('');
      state(e).initialized = false;
      return e;
    }
    importNode(node, deep = false) { return node.cloneNode(deep); }
    adoptNode(node) { if (node.parentNode) node.parentNode.removeChild(node); return node; }
    elementFromPoint() { return null; }
    get implementation() { return implementation; }
  }
  const implementation = Object.freeze({ hasFeature: () => true });
  class HTMLDocument extends Document {}
  mix(Element, parentNode); mix(Document, parentNode); mix(DocumentFragment, parentNode);
  mix(Element, childNode); mix(CharacterData, childNode, ['remove', 'before', 'after', 'replaceWith', 'previousElementSibling', 'nextElementSibling']);
  mix(DocumentType, childNode, ['remove', 'before', 'after', 'replaceWith']);
  addHandlers(HTMLElement.prototype); addHandlers(Document.prototype); addHandlers(SVGElement.prototype);
  protoOf = (id, t) => {
    switch (t) {
      case 1: {
        if (info(id, 8) !== 1) return (str(id, 2) === 'http://www.w3.org/2000/svg' ? SVGElement : Element).prototype;
        return (htmlClasses[str(id, 0)] ?? HTMLUnknownElement).prototype;
      }
      case 3: return Text.prototype;
      case 4: return CDATASection.prototype;
      case 7: return ProcessingInstruction.prototype;
      case 8: return Comment.prototype;
      case 9: return HTMLDocument.prototype;
      case 10: return DocumentType.prototype;
      case 11: return DocumentFragment.prototype;
      default: return Node.prototype;
    }
  };
  const docBody = () => { const b = document.body; return b ? nodeId(b) : -1; };
  const docElement = () => kids(0).find(k => info(k, 0) === 1) ?? -1;

  // ---- selectors: type, #id, .class, [attr], [attr=v], *, :first-child, :last-child,
  // :not(simple), with descendant, child, next-sibling and subsequent-sibling combinators --
  const parse = sel => {
    const groups = [];
    for (const g of splitTop(sel, ',')) {
      const src = g.trim();
      if (src === '') throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
      const parts = []; let comb = null; let i = 0;
      const re = /\s*([>+~])\s*|\s+/y;
      while (i < src.length) {
        re.lastIndex = i;
        const m = re.exec(src);
        if (m && m.index === i) { comb = m[1] ?? ' '; i = re.lastIndex; continue; }
        const [compound, next] = readCompound(src, i, sel);
        parts.push({ comb: parts.length === 0 ? null : (comb ?? ' '), compound }); comb = null; i = next;
      }
      if (comb && comb !== ' ') throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
      groups.push(parts);
    }
    return groups;
  };
  const splitTop = (s, c) => { const out = []; let depth = 0, cur = '', q = null;
    for (const ch of s) { if (q) { cur += ch; if (ch === q) q = null; continue; }
      if (ch === '"' || ch === "'") q = ch; if (ch === '(' || ch === '[') depth++; if (ch === ')' || ch === ']') depth--;
      if (ch === c && depth === 0) { out.push(cur); cur = ''; } else cur += ch; }
    out.push(cur); return out; };
  const ident = /-?(?:[A-Za-z_ -￿]|\\.)(?:[A-Za-z0-9_\- -￿]|\\.)*/y;
  const readIdent = (s, i, sel) => { ident.lastIndex = i; const m = ident.exec(s); if (!m || m.index !== i) throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError'); return [m[0].replace(/\\(.)/g, '$1'), ident.lastIndex]; };
  const readCompound = (s, i, sel) => {
    const tests = []; const start = i;
    if (s[i] === '*') { i++; } else if (/[A-Za-z_\\]/.test(s[i] ?? '')) { const [t, j] = readIdent(s, i, sel); tests.push({ kind: 'tag', name: t.toLowerCase() }); i = j; }
    for (;;) {
      const c = s[i];
      if (c === '#') { const [t, j] = readIdent(s, i + 1, sel); tests.push({ kind: 'id', name: t }); i = j; }
      else if (c === '.') { const [t, j] = readIdent(s, i + 1, sel); tests.push({ kind: 'class', name: t }); i = j; }
      else if (c === '[') {
        const end = s.indexOf(']', i); if (end < 0) throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
        const body = s.slice(i + 1, end).trim(); const m = /^([A-Za-z_][\w-]*)\s*(?:([~|^$*]?=)\s*(?:"([^"]*)"|'([^']*)'|([^\s"']+)))?\s*(i)?$/.exec(body);
        if (!m) throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
        tests.push({ kind: 'attr', name: m[1].toLowerCase(), op: m[2] ?? null, value: m[3] ?? m[4] ?? m[5] ?? '' }); i = end + 1;
      } else if (c === ':') {
        const m = /:(first-child|last-child|only-child|root|empty|checked|disabled|enabled|not)(\()?/y; m.lastIndex = i; const r = m.exec(s);
        if (!r || r.index !== i) throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
        if (r[1] === 'not') {
          let depth = 1, j = m.lastIndex; while (j < s.length && depth > 0) { if (s[j] === '(') depth++; if (s[j] === ')') depth--; j++; }
          tests.push({ kind: 'not', inner: parse(s.slice(m.lastIndex, j - 1)) }); i = j;
        } else { tests.push({ kind: 'pseudo', name: r[1] }); i = m.lastIndex; }
      } else break;
    }
    if (i === start) throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
    return [tests, i];
  };
  const testOne = (k, t) => {
    switch (t.kind) {
      case 'tag': return (info(k, 8) === 1 ? str(k, 0) : str(k, 0).toLowerCase()) === t.name;
      case 'id': return n.attr(k, 'id') === t.name;
      case 'class': return (n.attr(k, 'class') ?? '').split(/[ \t\n\f\r]+/).includes(t.name);
      case 'attr': {
        const v = n.attr(k, t.name); if (v === null || typeof v === 'number') return false;
        switch (t.op) { case null: return true; case '=': return v === t.value; case '~=': return v.split(/\s+/).includes(t.value);
          case '|=': return v === t.value || v.startsWith(t.value + '-'); case '^=': return t.value !== '' && v.startsWith(t.value);
          case '$=': return t.value !== '' && v.endsWith(t.value); case '*=': return t.value !== '' && v.includes(t.value); }
        return false;
      }
      case 'pseudo': {
        const p = info(k, 1); const sibs = p >= 0 ? kids(p).filter(x => info(x, 0) === 1) : [k];
        switch (t.name) { case 'first-child': return sibs[0] === k; case 'last-child': return sibs[sibs.length - 1] === k;
          case 'only-child': return sibs.length === 1; case 'root': return p >= 0 && info(p, 0) === 9;
          case 'empty': return kids(k).every(c => { const ct = info(c, 0); return ct !== 1 && !(ct === 3 && str(c, 3) !== ''); });
          case 'checked': return n.attr(k, 'checked') !== null; case 'disabled': return n.attr(k, 'disabled') !== null;
          case 'enabled': return n.attr(k, 'disabled') === null; }
        return false;
      }
      case 'not': return !matches(k, t.inner);
    }
    return false;
  };
  const matchParts = (k, parts, idx) => {
    if (!parts[idx].compound.every(t => testOne(k, t))) return false;
    if (idx === 0) return true;
    const comb = parts[idx].comb;
    if (comb === '>') { const p = info(k, 1); return p >= 0 && info(p, 0) === 1 && matchParts(p, parts, idx - 1); }
    if (comb === ' ') { let p = info(k, 1); while (p >= 0 && info(p, 0) === 1) { if (matchParts(p, parts, idx - 1)) return true; p = info(p, 1); } return false; }
    const prevEl = x => { let s = info(x, 4); while (s >= 0 && info(s, 0) !== 1) s = info(s, 4); return s; };
    if (comb === '+') { const s = prevEl(k); return s >= 0 && matchParts(s, parts, idx - 1); }
    if (comb === '~') { let s = prevEl(k); while (s >= 0) { if (matchParts(s, parts, idx - 1)) return true; s = prevEl(s); } return false; }
    return false;
  };
  const matches = (k, groups) => groups.some(parts => matchParts(k, parts, parts.length - 1));
  const select = (root, sel, first) => {
    const groups = parse(String(sel)); const out = [];
    for (const k of elementsOf(nodeId(root))) if (matches(k, groups)) { out.push(wrap(k)); if (first) break; }
    return out;
  };

  // ---- AbortController and AbortSignal (DOM §3) --------------------------------------
  class AbortSignal extends EventTarget {
    constructor(key) { if (key !== abortKey) throw new TypeError('Illegal constructor'); super(); this._aborted = false; this._reason = undefined; }
    get aborted() { return this._aborted; }
    get reason() { return this._reason; }
    throwIfAborted() { if (this._aborted) throw this._reason; }
    static abort(reason) { const s = new AbortSignal(abortKey); signalAbort(s, reason); return s; }
    static timeout(ms) { const s = new AbortSignal(abortKey); setTimeout(() => signalAbort(s, new DOMException('signal timed out', 'TimeoutError')), ms); return s; }
  }
  addHandlers(AbortSignal.prototype);
  const abortKey = {};
  const signalAbort = (s, reason) => {
    if (s._aborted) return;
    s._aborted = true; s._reason = reason === undefined ? new DOMException('signal is aborted without reason', 'AbortError') : reason;
    dispatch(s, new Event('abort'));
  };
  class AbortController {
    constructor() { this._signal = new AbortSignal(abortKey); }
    get signal() { return this._signal; }
    abort(reason) { signalAbort(this._signal, reason); }
  }

  // ---- MutationObserver (DOM §4.3), on the tree changes the natives make ----------------
  const observed = new Map();          // node -> [{ observer, options }]
  let pendingObservers = [], notifyQueued = false;
  const observerState = new WeakMap();
  class MutationRecord { constructor() { throw new TypeError('Illegal constructor'); } }
  const record = (fields) => {
    const r = Object.create(MutationRecord.prototype);
    for (const [k, v] of Object.entries({ type: '', target: null, addedNodes: staticList([]), removedNodes: staticList([]),
      previousSibling: null, nextSibling: null, attributeName: null, attributeNamespace: null, oldValue: null, ...fields }))
      Object.defineProperty(r, k, { value: v, enumerable: true });
    return r;
  };
  const queueRecord = (type, target, fields, name) => {
    if (observed.size === 0) return;
    const interested = new Map();
    for (let k = target, first = true; k >= 0; k = info(k, 1), first = false) {
      for (const { observer, options } of observed.get(k) ?? []) {
        if (!first && !options.subtree) continue;
        if (type === 'attributes' && (!options.attributes || (options.attributeFilter && !options.attributeFilter.includes(name)))) continue;
        if (type === 'characterData' && !options.characterData) continue;
        if (type === 'childList' && !options.childList) continue;
        const keepOld = (type === 'attributes' && options.attributeOldValue) || (type === 'characterData' && options.characterDataOldValue);
        if (!interested.has(observer) || keepOld) interested.set(observer, keepOld);
      }
    }
    for (const [observer, keepOld] of interested) {
      observerState.get(observer).records.push(record({ type, target: wrap(target), ...fields, oldValue: keepOld ? fields.oldValue ?? null : null }));
      if (!pendingObservers.includes(observer)) pendingObservers.push(observer);
    }
    if (interested.size && !notifyQueued) {
      notifyQueued = true;
      Promise.resolve().then(() => {
        notifyQueued = false;
        const list = pendingObservers; pendingObservers = [];
        for (const o of list) {
          const st = observerState.get(o), rs = st.records; st.records = [];
          if (rs.length) try { st.callback.call(o, rs, o); } catch (e) { report(e); }
        }
      });
    }
  };
  const nodes = ids => staticList(ids.map(wrap));
  const childList = (parent, added, removed, prev, next) => {
    if (added.length || removed.length)
      queueRecord('childList', parent, { addedNodes: nodes(added), removedNodes: nodes(removed), previousSibling: wrap(prev), nextSibling: wrap(next) });
  };
  const attrName = (id, name) => info(id, 8) === 1 ? name.toLowerCase() : name;
  n.setAttr = (id, name, value) => {
    const old = observed.size ? n0.attr(id, name) : null, r = n0.setAttr(id, name, value);
    if (r === 0 && observed.size) queueRecord('attributes', id, { attributeName: attrName(id, name), oldValue: typeof old === 'string' ? old : null }, attrName(id, name));
    return r;
  };
  n.removeAttr = (id, name) => {
    const old = observed.size ? n0.attr(id, name) : null, r = n0.removeAttr(id, name);
    if (r === 0 && typeof old === 'string') queueRecord('attributes', id, { attributeName: attrName(id, name), oldValue: old }, attrName(id, name));
    return r;
  };
  n.setText = (id, value) => {
    if (!observed.size) return n0.setText(id, value);
    const t = info(id, 0);
    if (t === 3 || t === 4 || t === 7 || t === 8) {
      const old = str(id, 3), r = n0.setText(id, value);
      if (r === 0) queueRecord('characterData', id, { oldValue: old });
      return r;
    }
    const before = kids(id), r = n0.setText(id, value);
    if (r === 0) childList(id, kids(id), before, -1, -1);
    return r;
  };
  n.insert = (p, node, child) => {
    if (!observed.size) return n0.insert(p, node, child);
    const fragment = info(node, 0) === 11, moved = fragment ? kids(node) : [node];
    const oldParent = fragment ? -1 : info(node, 1), oldPrev = info(node, 4), oldNext = info(node, 5);
    const r = n0.insert(p, node, child);
    if (r !== 0) return r;
    if (fragment) childList(node, [], moved, -1, -1);
    else if (oldParent >= 0) childList(oldParent, [], [node], oldPrev, oldNext);
    if (moved.length) childList(p, moved, [], info(moved[0], 4), info(moved[moved.length - 1], 5));
    return r;
  };
  n.remove = (p, child) => {
    const prev = info(child, 4), next = info(child, 5), r = n0.remove(p, child);
    if (r === 0 && observed.size) childList(p, [], [child], prev, next);
    return r;
  };
  n.replace = (p, node, child) => {
    if (!observed.size) return n0.replace(p, node, child);
    const fragment = info(node, 0) === 11, moved = fragment ? kids(node) : [node];
    const oldParent = fragment ? -1 : info(node, 1), oldPrev = info(node, 4), oldNext = info(node, 5);
    const prev = info(child, 4) === node ? info(node, 4) : info(child, 4), next = info(child, 5) === node ? info(node, 5) : info(child, 5);
    const r = n0.replace(p, node, child);
    if (r !== 0) return r;
    if (fragment) childList(node, [], moved, -1, -1);
    else if (oldParent >= 0 && !(oldParent === p && (oldPrev === child || oldNext === child) && false)) {
      if (oldParent !== p || node !== child) childList(oldParent, [], [node], oldPrev, oldNext);
    }
    childList(p, moved, [child], prev, next);
    return r;
  };
  class MutationObserver {
    constructor(callback) {
      if (typeof callback !== 'function') throw new TypeError("parameter 1 is not of type 'MutationCallback'");
      observerState.set(this, { callback, records: [], nodes: new Set() });
    }
    observe(target, init = {}) {
      const id = nodeId(target), o = { ...init };
      if ((o.attributeOldValue !== undefined || o.attributeFilter !== undefined) && o.attributes === undefined) o.attributes = true;
      if (o.characterDataOldValue !== undefined && o.characterData === undefined) o.characterData = true;
      if (!o.childList && !o.attributes && !o.characterData) throw new TypeError('The options object must set at least one of attributes, characterData or childList to true.');
      if (o.attributeOldValue && !o.attributes) throw new TypeError('attributeOldValue needs attributes');
      if (o.attributeFilter !== undefined && !o.attributes) throw new TypeError('attributeFilter needs attributes');
      if (o.characterDataOldValue && !o.characterData) throw new TypeError('characterDataOldValue needs characterData');
      const options = { childList: !!o.childList, attributes: !!o.attributes, characterData: !!o.characterData, subtree: !!o.subtree,
        attributeOldValue: !!o.attributeOldValue, characterDataOldValue: !!o.characterDataOldValue,
        attributeFilter: o.attributeFilter === undefined ? null : [...o.attributeFilter].map(String) };
      const list = observed.get(id) ?? [];
      const existing = list.find(x => x.observer === this);
      if (existing) existing.options = options; else list.push({ observer: this, options });
      observed.set(id, list); observerState.get(this).nodes.add(id);
    }
    disconnect() {
      const st = observerState.get(this);
      for (const id of st.nodes) { const list = (observed.get(id) ?? []).filter(x => x.observer !== this); if (list.length) observed.set(id, list); else observed.delete(id); }
      st.nodes.clear(); st.records = [];
    }
    takeRecords() { const st = observerState.get(this), rs = st.records; st.records = []; return rs; }
  }

  // ---- Window -----------------------------------------------------------------------
  class Window extends EventTarget { constructor() { throw new TypeError('Illegal constructor'); } }
  addHandlers(Window.prototype);
  Object.setPrototypeOf(globalThis, Window.prototype);
  const window = globalThis;
  ids.set(window, WINDOW);
  const document = wrap(0);
  let href = 'about:blank';
  const location = {
    get href() { return href; }, toString() { return href; },
    get protocol() { return /^[a-z][a-z0-9+.-]*:/i.exec(href)?.[0] ?? ''; },
    get pathname() { const m = /^[a-z][a-z0-9+.-]*:\/\/[^/?#]*([^?#]*)/i.exec(href); return m ? m[1] || '/' : ''; },
    get search() { const i = href.indexOf('?'); if (i < 0) return ''; const j = href.indexOf('#', i); return href.slice(i, j < 0 ? undefined : j); },
    get hash() { const i = href.indexOf('#'); return i < 0 ? '' : href.slice(i); },
    get host() { return /^[a-z][a-z0-9+.-]*:\/\/([^/?#]*)/i.exec(href)?.[1] ?? ''; },
    get hostname() { return this.host.replace(/:\d+$/, ''); },
    get origin() { const m = /^([a-z][a-z0-9+.-]*:\/\/[^/?#]*)/i.exec(href); return m ? m[1] : 'null'; },
    reload() {}, assign() {}, replace() {},
  };
  let currentScript = null;
  // HTML §8.6: a handler that is not a function is converted to a string at once; the
  // timeout is a WebIDL `long` (ToInt32), and a negative one is 0.
  const timer = (repeat, f, delay, args) => {
    let run;
    if (typeof f === 'function') run = () => f.apply(window, args);
    else { const code = String(f); run = () => (0, eval)(code); }
    const t = Number(delay) | 0;
    return chk(n.timer(register(run), t < 0 ? 0 : t, repeat));
  };
  const def = (name, value) => define(globalThis, name, value);
  def('window', window); def('self', window); def('globalThis', window); def('frames', window);
  Object.defineProperty(globalThis, 'parent', { get: () => window, configurable: true });
  Object.defineProperty(globalThis, 'top', { get: () => window, configurable: true });
  Object.defineProperty(globalThis, 'event', { get: () => globalEvent, set(v) {}, configurable: true });
  def('opener', null); def('frameElement', null); def('name', '');
  def('document', document); def('location', location);
  def('navigator', Object.freeze({ userAgent: 'Foafnaut', language: 'en', languages: ['en'], platform: '', onLine: true,
    cookieEnabled: false, hardwareConcurrency: 1 }));
  def('history', Object.freeze({ length: 1, state: null, pushState() {}, replaceState() {}, back() {}, forward() {}, go() {} }));
  def('screen', Object.freeze({ width: 800, height: 600, availWidth: 800, availHeight: 600, colorDepth: 24, pixelDepth: 24 }));
  def('innerWidth', 800); def('innerHeight', 600); def('devicePixelRatio', 1); def('scrollX', 0); def('scrollY', 0);
  def('pageXOffset', 0); def('pageYOffset', 0);
  const log = (...xs) => n.log(xs.map(x => typeof x === 'string' ? x : (() => { try { return typeof x === 'object' && x !== null && !(x instanceof Error) ? JSON.stringify(x) : String(x); } catch { return String(x); } })()).join(' '));
  def('console', Object.freeze({ log, info: log, debug: log, warn: log, error: log, trace: log, assert: (c, ...xs) => { if (!c) log('Assertion failed:', ...xs); },
    group: log, groupEnd() {}, time() {}, timeEnd() {}, dir: log, table: log }));
  def('setTimeout', (f, delay = 0, ...args) => timer(0, f, delay, args));
  def('setInterval', (f, delay = 0, ...args) => timer(1, f, delay, args));
  def('clearTimeout', (id = 0) => { n.clearTimer(Number(id) | 0); });
  def('clearInterval', (id = 0) => { n.clearTimer(Number(id) | 0); });
  def('queueMicrotask', f => {
    if (typeof f !== 'function') throw new TypeError("Failed to execute 'queueMicrotask': parameter 1 is not of type 'Function'.");
    Promise.resolve().then(() => { try { f(); } catch (e) { report(e); } });
  });
  def('requestAnimationFrame', f => { if (typeof f !== 'function') throw new TypeError('requestAnimationFrame needs a function'); return chk(n.frame(register(f))); });
  def('cancelAnimationFrame', id => { n.cancelFrame(Number(id) | 0); });
  def('reportError', e => report(e));
  def('structuredClone', v => JSON.parse(JSON.stringify(v)));
  def('getComputedStyle', el => el.style);
  def('matchMedia', q => ({ matches: false, media: String(q), addListener() {}, removeListener() {}, addEventListener() {}, removeEventListener() {} }));
  def('postMessage', () => {});
  def('focus', () => {}); def('blur', () => {}); def('close', () => {}); def('stop', () => {}); def('scrollTo', () => {}); def('scrollBy', () => {});
  def('alert', () => {}); def('confirm', () => false); def('prompt', () => null);
  def('open', () => null);
  for (const [k, v] of Object.entries({ EventTarget, Event, CustomEvent, UIEvent, MouseEvent, KeyboardEvent, FocusEvent, ErrorEvent,
    PromiseRejectionEvent, Node, Element, HTMLElement, HTMLUnknownElement, SVGElement, CharacterData, Text, CDATASection, Comment,
    ProcessingInstruction, DocumentType, DocumentFragment, Document, HTMLDocument, NodeList, HTMLCollection, NamedNodeMap,
    DOMTokenList, DOMException, AbortController, AbortSignal, Window, MutationObserver, MutationRecord, ...named })) def(k, v);

  // Content event handler attributes (HTML §8.1.8.1): onclick="..." and <body onload>.
  const bodyWindowHandlers = new Set(['load', 'error', 'resize', 'scroll', 'message', 'unload', 'beforeunload', 'hashchange', 'popstate', 'pageshow', 'pagehide', 'online', 'offline']);
  const contentHandler = (el, name, source) => {
    if (!handlerNames.includes(name)) return;
    const onBody = el.localName === 'body' && bodyWindowHandlers.has(name);
    let f;
    try { f = new Function('event', source); } catch (e) { report(e); return; }
    const t = onBody ? window : el;
    setHandler(t, name, onBody && name === 'error' ? function (m, s, l, c, e) { return f.call(this, m); } : f);
  };

  return {
    // Lean runs a timer (target -1) or an animation frame callback (target -2, `arg` the time).
    call(id, target, arg) {
      const f = callbacks.get(id);
      if (!f) return '';
      try { if (target === -2) f(arg); else f(); } catch (e) { report(e); }
      return '';
    },
    // Lean dispatches an event of the user agent at a node, the document (0) or the window.
    dispatch(target, type, flags) {
      const C = type === 'click' || type.startsWith('mouse') ? MouseEvent : Event;
      const e = new C(type, { bubbles: (flags & 1) !== 0, cancelable: (flags & 2) !== 0, composed: (flags & 4) !== 0, view: window });
      state(e).trusted = true;
      if (type === 'DOMContentLoaded') readyState = 'interactive';
      if (type === 'load' && target === WINDOW) readyState = 'complete';
      return dispatch(wrapTarget(target), e) ? '' : 'prevented';
    },
    report(e) { report(e); },
    // A page starts: the content event handler attributes of its elements. The host may
    // run the prelude once on an empty document and copy that state for each page.
    start() {
      for (const k of elementsOf(0)) {
        const a = str(k, 6) ?? ''; const xs = a === '' ? [] : a.split('\u0000');
        for (let i = 0; i + 1 < xs.length; i += 2) if (/^on[a-z]+$/.test(xs[i])) contentHandler(wrap(k), xs[i].slice(2), xs[i + 1]);
      }
    },
    script(id) { currentScript = id < 0 ? null : wrap(id); },
    url(u) { href = String(u); },
    release(id) { callbacks.delete(id); },
  };
})
