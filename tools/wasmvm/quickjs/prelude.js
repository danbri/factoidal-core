// prelude.js: the page objects that scripts see, for QuickJS-NG in the Lean WasmVM engine
// (record: docs/designissues/2026-11-08-page-scripts.md). build-quickjs.sh compiles this
// file to QuickJS-NG bytecode (prelude_bytecode.c) that the module holds; qjs_new runs it once and calls it with `n`, the
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
  const n = Object.create(n0); // the natives are not enumerable: inherit them
  const WINDOW = 0x0FFFFFFF;
  let nextTarget = 0x10000000;
  const define = (o, name, value) => Object.defineProperty(o, name, { value, writable: true, configurable: true });
  const consts = (o, table) => { for (const k in table) Object.defineProperty(o, k, { value: table[k], enumerable: true }); };

  // ---- DOMException -------------------------------------------------------------
  const codes = { IndexSizeError: 1, HierarchyRequestError: 3, WrongDocumentError: 4, InvalidCharacterError: 5,
    NoModificationAllowedError: 7, NotFoundError: 8, NotSupportedError: 9, InvalidStateError: 11, SyntaxError: 12,
    InvalidModificationError: 13, NamespaceError: 14, InvalidAccessError: 15, TypeMismatchError: 17,
    SecurityError: 18, NetworkError: 19, AbortError: 20, URLMismatchError: 21, QuotaExceededError: 22, TimeoutError: 23,
    InvalidNodeTypeError: 24, DataCloneError: 25 };
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
      case -11: throw new DOMException('The operation is not allowed by Namespaces in XML.', 'NamespaceError');
      case -12: throw new DOMException('The string is not a valid selector.', 'SyntaxError');
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

  // ---- what Lean's layout answers (node_query ops 16 to 19) ------------------------
  // 16: the init of the event of the user agent being dispatched (JSON); 17: the layout
  // of a node: border box x y w h in the page, client box left top w h; 18: an SVG
  // element's bounding box in its user space; 19: the viewport in CSS pixels. An engine
  // without them answers an error: then zeros, and a viewport of 800 by 600.
  const query = (id, op, count) => {
    const s = n.query(id, op, '');
    const xs = typeof s === 'string' && s !== '' ? s.split(' ').map(Number) : [];
    return xs.length >= count ? xs : new Array(count).fill(0);
  };
  const layoutOf = el => query(nodeId(el), 17, 8);
  const viewport = () => { const v = query(0, 19, 2); return v[0] > 0 ? v : [800, 600]; };
  class DOMRectReadOnly {
    constructor(x = 0, y = 0, width = 0, height = 0) { Object.assign(this, { x: +x, y: +y, width: +width, height: +height }); }
    get top() { return Math.min(this.y, this.y + this.height); }
    get bottom() { return Math.max(this.y, this.y + this.height); }
    get left() { return Math.min(this.x, this.x + this.width); }
    get right() { return Math.max(this.x, this.x + this.width); }
    toJSON() { return { x: this.x, y: this.y, width: this.width, height: this.height, top: this.top, right: this.right, bottom: this.bottom, left: this.left }; }
  }
  class DOMRect extends DOMRectReadOnly {}

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
  // UI Events §3-§7 and HTML: the event interfaces and their init dictionaries. A member
  // getter reads the state; `legacyOnly` makes an interface that createEvent can make but
  // `new` can not (BeforeUnloadEvent, TextEvent).
  let legacyMaking = false;
  const getters = (C, names) => { for (const k of names) Object.defineProperty(C.prototype, k, { get() { return state(this)[k]; }, configurable: true, enumerable: true }); };
  const initOf = init => init == null ? {} : init;
  class UIEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      if (d.view !== undefined && d.view !== null && d.view !== window) throw new TypeError("member view is not of type 'Window'");
      s.view = d.view ?? null; s.detail = d.detail === undefined ? 0 : (d.detail | 0); s.which = d.which === undefined ? 0 : d.which >>> 0;
    }
    get view() { return state(this).view ?? null; }
    get detail() { return state(this).detail ?? 0; }
    get which() { return state(this).which ?? 0; }
    initUIEvent(type, bubbles = false, cancelable = false, view = null, detail = 0) {
      if (state(this).dispatching) return;
      this.initEvent(type, bubbles, cancelable); Object.assign(state(this), { view, detail: detail | 0 });
    }
  }
  const modifiers = (s, d) => { for (const k of ['ctrlKey', 'shiftKey', 'altKey', 'metaKey']) s[k] = !!d[k]; };
  class MouseEvent extends UIEvent {
    constructor(type, init = undefined) {
      super(type, init);
      const s = state(this), d = initOf(init);
      for (const k of ['screenX', 'screenY', 'clientX', 'clientY', 'button', 'buttons']) s[k] = Number(d[k] ?? 0);
      for (const k of ['ctrlKey', 'shiftKey', 'altKey', 'metaKey']) s[k] = !!d[k];
      s.relatedTarget = d.relatedTarget ?? null;
    }
  }
  for (const k of ['screenX', 'screenY', 'clientX', 'clientY', 'button', 'buttons', 'ctrlKey', 'shiftKey', 'altKey', 'metaKey', 'relatedTarget'])
    Object.defineProperty(MouseEvent.prototype, k, { get() { return state(this)[k]; }, configurable: true });
  // CSSOM View §10: page and offset coordinates. An event of the user agent has them from
  // Lean's layout (the nodeAt answer); for a script's own event, page = client (no scroll),
  // and offset is from the padding edge of the target's box in Lean's layout.
  for (const [k, c] of [['pageX', 'clientX'], ['pageY', 'clientY'], ['x', 'clientX'], ['y', 'clientY']])
    Object.defineProperty(MouseEvent.prototype, k, { get() { const s = state(this); return s[k] ?? s[c]; }, configurable: true });
  for (const [k, c, i] of [['offsetX', 'clientX', 0], ['offsetY', 'clientY', 1]])
    Object.defineProperty(MouseEvent.prototype, k, { get() {
      const s = state(this);
      if (s[k] !== undefined) return s[k];
      if (!(s.target instanceof Element)) return s[c];
      const b = layoutOf(s.target);
      return s[c] - b[i] - b[i + 4];
    }, configurable: true });
  for (const k of ['movementX', 'movementY']) Object.defineProperty(MouseEvent.prototype, k, { get() { return state(this)[k] ?? 0; }, configurable: true });
  // Pointer Events 3 §4.1.
  class PointerEvent extends MouseEvent {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      s.pointerId = (d.pointerId ?? 0) | 0; s.width = Number(d.width ?? 1); s.height = Number(d.height ?? 1);
      s.pressure = Number(d.pressure ?? 0); s.tangentialPressure = Number(d.tangentialPressure ?? 0);
      s.tiltX = (d.tiltX ?? 0) | 0; s.tiltY = (d.tiltY ?? 0) | 0; s.twist = (d.twist ?? 0) | 0;
      s.altitudeAngle = Number(d.altitudeAngle ?? Math.PI / 2); s.azimuthAngle = Number(d.azimuthAngle ?? 0);
      s.pointerType = String(d.pointerType ?? ''); s.isPrimary = !!d.isPrimary;
    }
    getCoalescedEvents() { return []; }
    getPredictedEvents() { return []; }
  }
  getters(PointerEvent, ['pointerId', 'width', 'height', 'pressure', 'tangentialPressure', 'tiltX', 'tiltY', 'twist',
    'altitudeAngle', 'azimuthAngle', 'pointerType', 'isPrimary']);
  class WheelEvent extends MouseEvent {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      for (const k of ['deltaX', 'deltaY', 'deltaZ']) s[k] = Number(d[k] ?? 0);
      s.deltaMode = (d.deltaMode ?? 0) >>> 0;
    }
  }
  getters(WheelEvent, ['deltaX', 'deltaY', 'deltaZ', 'deltaMode']);
  consts(WheelEvent, { DOM_DELTA_PIXEL: 0, DOM_DELTA_LINE: 1, DOM_DELTA_PAGE: 2 });
  consts(WheelEvent.prototype, { DOM_DELTA_PIXEL: 0, DOM_DELTA_LINE: 1, DOM_DELTA_PAGE: 2 });
  class KeyboardEvent extends UIEvent {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      modifiers(s, d);
      s.key = String(d.key ?? ''); s.code = String(d.code ?? ''); s.location = (d.location ?? 0) >>> 0;
      s.repeat = !!d.repeat; s.isComposing = !!d.isComposing; s.charCode = (d.charCode ?? 0) >>> 0; s.keyCode = (d.keyCode ?? 0) >>> 0;
    }
    getModifierState(k) { const s = state(this); return { Control: s.ctrlKey, Shift: s.shiftKey, Alt: s.altKey, Meta: s.metaKey }[String(k)] ?? false; }
  }
  getters(KeyboardEvent, ['key', 'code', 'location', 'repeat', 'isComposing', 'charCode', 'keyCode', 'ctrlKey', 'shiftKey', 'altKey', 'metaKey']);
  const keyLocations = { DOM_KEY_LOCATION_STANDARD: 0, DOM_KEY_LOCATION_LEFT: 1, DOM_KEY_LOCATION_RIGHT: 2, DOM_KEY_LOCATION_NUMPAD: 3 };
  consts(KeyboardEvent, keyLocations); consts(KeyboardEvent.prototype, keyLocations);
  class FocusEvent extends UIEvent {
    constructor(type, init = undefined) {
      super(type, init); const r = initOf(init).relatedTarget;
      if (r !== undefined && r !== null && !(r instanceof EventTarget)) throw new TypeError("member relatedTarget is not of type 'EventTarget'");
      state(this).relatedTarget = r ?? null;
    }
  }
  getters(FocusEvent, ['relatedTarget']);
  class CompositionEvent extends UIEvent {
    constructor(type, init = undefined) { super(type, init); state(this).data = String(initOf(init).data ?? ''); }
  }
  getters(CompositionEvent, ['data']);
  class InputEvent extends UIEvent {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      s.data = d.data === undefined || d.data === null ? null : String(d.data); s.isComposing = !!d.isComposing; s.inputType = String(d.inputType ?? '');
    }
  }
  getters(InputEvent, ['data', 'isComposing', 'inputType']);
  class DragEvent extends MouseEvent {
    constructor(type, init = undefined) { super(type, init); state(this).dataTransfer = initOf(init).dataTransfer ?? null; }
  }
  getters(DragEvent, ['dataTransfer']);
  class HashChangeEvent extends Event {
    constructor(type, init = undefined) { super(type, init); const d = initOf(init); state(this).oldURL = String(d.oldURL ?? ''); state(this).newURL = String(d.newURL ?? ''); }
  }
  getters(HashChangeEvent, ['oldURL', 'newURL']);
  class MessageEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      s.data = d.data === undefined ? null : d.data; s.origin = String(d.origin ?? ''); s.lastEventId = String(d.lastEventId ?? '');
      s.source = d.source ?? null; s.ports = Object.freeze([...(d.ports ?? [])]);
    }
    initMessageEvent(type, bubbles = false, cancelable = false, data = null, origin = '', lastEventId = '', source = null, ports = []) {
      if (state(this).dispatching) return;
      this.initEvent(type, bubbles, cancelable);
      Object.assign(state(this), { data, origin: String(origin), lastEventId: String(lastEventId), source, ports: Object.freeze([...ports]) });
    }
  }
  getters(MessageEvent, ['data', 'origin', 'lastEventId', 'source', 'ports']);
  class StorageEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      for (const k of ['key', 'oldValue', 'newValue']) s[k] = d[k] === undefined || d[k] === null ? null : String(d[k]);
      s.url = String(d.url ?? ''); s.storageArea = d.storageArea ?? null;
    }
  }
  getters(StorageEvent, ['key', 'oldValue', 'newValue', 'url', 'storageArea']);
  class DeviceMotionEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      s.acceleration = d.acceleration ?? null; s.accelerationIncludingGravity = d.accelerationIncludingGravity ?? null;
      s.rotationRate = d.rotationRate ?? null; s.interval = Number(d.interval ?? 0);
    }
  }
  getters(DeviceMotionEvent, ['acceleration', 'accelerationIncludingGravity', 'rotationRate', 'interval']);
  class DeviceOrientationEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init); const s = state(this), d = initOf(init);
      for (const k of ['alpha', 'beta', 'gamma']) s[k] = d[k] === undefined || d[k] === null ? null : Number(d[k]);
      s.absolute = !!d.absolute;
    }
  }
  getters(DeviceOrientationEvent, ['alpha', 'beta', 'gamma', 'absolute']);
  class BeforeUnloadEvent extends Event {
    constructor(type) { if (!legacyMaking) throw new TypeError('Illegal constructor'); super(type); state(this).returnValue = ''; }
    get returnValue() { return state(this).returnValue; }
    set returnValue(v) { state(this).returnValue = String(v); }
  }
  class TextEvent extends UIEvent {
    constructor(type) { if (!legacyMaking) throw new TypeError('Illegal constructor'); super(type); state(this).data = ''; }
    get data() { return state(this).data; }
    initTextEvent(type, bubbles = false, cancelable = false, view = null, data = 'undefined') {
      if (state(this).dispatching) return;
      this.initUIEvent(type, bubbles, cancelable, view, 0); state(this).data = String(data);
    }
  }
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
    // DOM §2.9 steps 5.4 and 5.9.3: the activation target of a click (Lean's choice), and its
    // legacy-pre-activation behaviour before any listener runs.
    let act = null, actState = null;
    if (event instanceof MouseEvent && s.type === 'click' && tid < WINDOW) {
      const r = chk(n.query(tid, 10, s.bubbles ? '1' : '0'));
      if (r !== null) { act = Number(r); actState = preActivation(act); }
    }
    // Lean answers [path length, path (target first)..., then per listener call:
    // callback, node, phase + 8 * capture, depth]: L4Factoidal.EventLoop.Dispatch.plan.
    const plan = chk(n.plan(tid, s.type, s.bubbles ? 1 : 0));
    const k = plan[0];
    s.path = []; for (let i = 1; i <= k; i++) s.path.push(wrapTarget(plan[i]));
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
    if (act !== null) { if (s.canceled) canceledActivation(act, actState); else activation(act, tid); }
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
    'beforeunload', 'unload', 'hashchange', 'popstate', 'pageshow', 'pagehide', 'storage', 'online', 'offline',
    'afterprint', 'beforeprint', 'languagechange', 'messageerror'];
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
  // HTML §8.1.8.2: on body and frameset elements, the window-reflecting body element event
  // handlers and the WindowEventHandlers are the window's.
  const bodyWindowHandlers = new Set(['blur', 'error', 'focus', 'load', 'resize', 'scroll', 'afterprint', 'beforeprint',
    'beforeunload', 'hashchange', 'languagechange', 'message', 'messageerror', 'offline', 'online', 'pagehide', 'pageshow',
    'popstate', 'rejectionhandled', 'storage', 'unhandledrejection', 'unload']);
  const windowReflecting = el => el instanceof HTMLElement && (el.localName === 'body' || el.localName === 'frameset');
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
        if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) { const k = ids()[Number(p)]; return k === undefined ? undefined : wrap(k); }
        if (p === 'length') return ids().length;
        return Reflect.get(t, p, recv);
      },
      // Indexed properties have no setter (WebIDL §3.9): an assignment fails.
      set(t, p, v, recv) { if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return false; return Reflect.set(t, p, v, recv); },
      defineProperty(t, p, desc) { if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return false; return Reflect.defineProperty(t, p, desc); },
      has(t, p) { if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return Number(p) < ids().length; return p === 'length' || Reflect.has(t, p); },
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
  }
  // An interface with an indexed getter and `iterable` (WebIDL §3.7.10) takes the Array ones.
  for (const k of ['forEach', 'entries', 'keys', 'values']) define(NodeList.prototype, k, Array.prototype[k]);
  define(NodeList.prototype, Symbol.iterator, Array.prototype.values);
  class HTMLCollection {
    constructor() { throw new TypeError('Illegal constructor'); }
    item(i) { return this[i >>> 0] ?? null; }
    namedItem(name) { for (const e of this) if (e.id === name || e.getAttribute('name') === name) return e; return null; }
  }
  define(HTMLCollection.prototype, Symbol.iterator, Array.prototype.values);
  const liveCollection = ids => liveList(ids, HTMLCollection.prototype);
  const staticList = xs => {
    const o = Object.create(NodeList.prototype);
    xs.forEach((x, i) => Object.defineProperty(o, i, { value: x, enumerable: true }));
    Object.defineProperty(o, 'length', { value: xs.length });
    return o;
  };
  const collection = xs => {
    const o = Object.create(HTMLCollection.prototype);
    xs.forEach((x, i) => Object.defineProperty(o, i, { value: x, enumerable: true }));
    Object.defineProperty(o, 'length', { value: xs.length });
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
    // nodeValue and textContent are DOMString?: null and undefined are the empty string.
    set nodeValue(v) { const t = this.nodeType; if (t === 3 || t === 4 || t === 7 || t === 8) chk(n.setText(nodeId(this), v == null ? '' : String(v))); }
    get textContent() { return str(nodeId(this), 4); }
    set textContent(v) { chk(n.setText(nodeId(this), v == null ? '' : String(v))); }
    normalize() { chk(n.treeOp(nodeId(this), 0, 2)); }
    cloneNode(deep = false) { const c = chk(n.clone(nodeId(this), deep ? 1 : 0)); scanHandlers(c, true); return wrap(c); }
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
    // Locate a namespace and a namespace prefix (DOM §4.4) are Lean's (Dom.lookupNamespaceURI).
    lookupNamespaceURI(prefix) { return chk(n.query(nodeId(this), 0, prefix === null || prefix === undefined || prefix === '' ? '\u0000' : String(prefix))); }
    lookupPrefix(ns) { return ns === null || ns === undefined || ns === '' ? null : chk(n.query(nodeId(this), 1, String(ns))); }
    isDefaultNamespace(ns) { return (ns === '' || ns === undefined ? null : ns) === this.lookupNamespaceURI(null); }
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
    querySelector(sel) { if (arguments.length < 1) throw new TypeError('querySelector: 1 argument required'); return select(this, sel, true)[0] ?? null; },
    querySelectorAll(sel) { if (arguments.length < 1) throw new TypeError('querySelectorAll: 1 argument required'); return staticList(select(this, sel, false)); },
    // DOM §4.2.6.2 "list of elements with qualified name": in an HTML document, an HTML element
    // matches the ASCII lower case of the name.
    getElementsByTagName(name) { const id = nodeId(this); name = String(name); const lower = name.replace(/[A-Z]/g, c => c.toLowerCase());
      return liveCollection(() => elementsOf(id).filter(k => { if (name === '*') return true;
        const p = str(k, 5), q = p === null ? str(k, 0) : p + ':' + str(k, 0); return q === (info(k, 8) === 1 ? lower : name); })); },
    getElementsByTagNameNS(ns, localName) { const id = nodeId(this); ns = ns === null || ns === undefined || ns === '' ? null : String(ns); localName = String(localName);
      return liveCollection(() => elementsOf(id).filter(k => (ns === '*' || str(k, 2) === ns) && (localName === '*' || str(k, 0) === localName))); },
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
    // The update steps (DOM §7.1): no attribute and no tokens leaves the attribute absent.
    const set = xs => { if (xs.length === 0 && !el.hasAttribute(attr)) return; el.setAttribute(attr, xs.join(' ')); };
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
      replace: { value: (a, b) => { a = String(a); b = String(b);
        if (a === '' || b === '') throw new DOMException('empty token', 'SyntaxError'); a = check(a); b = check(b); const xs = get(); const i = xs.indexOf(a); if (i < 0) return false; xs[i] = b; set(xs.filter((x, j, all) => all.indexOf(x) === j)); return true; } },
      toString: { value: () => el.getAttribute(attr) ?? '' },
      [Symbol.iterator]: { value: function* () { yield* get(); } },
    });
    return new Proxy(o, { get(t, p, r) { if (typeof p === 'string' && /^[0-9]+$/.test(p)) return get()[Number(p)]; return Reflect.get(t, p, r); } });
  };
  const tokenLists = new WeakMap();

  class Element extends Node {
    // CSSOM View §6 and §7, from Lean's layout of the current DOM (laid out when a script
    // reads, once until the DOM or the viewport changes). The root element's client box
    // is the viewport.
    getBoundingClientRect() { const b = layoutOf(this); return new DOMRect(b[0], b[1], b[2], b[3]); }
    getClientRects() { const b = layoutOf(this); return b[2] === 0 && b[3] === 0 && !this.isConnected ? [] : [new DOMRect(b[0], b[1], b[2], b[3])]; }
    get clientWidth() { return this === document.documentElement ? viewport()[0] : Math.round(layoutOf(this)[6]); }
    get clientHeight() { return this === document.documentElement ? viewport()[1] : Math.round(layoutOf(this)[7]); }
    get clientLeft() { return Math.round(layoutOf(this)[4]); }
    get clientTop() { return Math.round(layoutOf(this)[5]); }
    get scrollWidth() { return this.clientWidth; }
    get scrollHeight() { return this.clientHeight; }
    get scrollTop() { return 0; } set scrollTop(v) {}
    get scrollLeft() { return 0; } set scrollLeft(v) {}
    get tagName() { return str(nodeId(this), 1); }
    get localName() { return str(nodeId(this), 0); }
    get namespaceURI() { return str(nodeId(this), 2); }
    get prefix() { return str(nodeId(this), 5); }
    get id() { return n.attr(nodeId(this), 'id') ?? ''; }
    set id(v) { chk(n.setAttr(nodeId(this), 'id', String(v))); }
    get className() { return n.attr(nodeId(this), 'class') ?? ''; }
    set className(v) { chk(n.setAttr(nodeId(this), 'class', String(v))); }
    get classList() { let l = tokenLists.get(this); if (!l) tokenLists.set(this, l = tokenList(this, 'class')); return l; }
    set classList(v) { this.classList.value = v; }
    getAttribute(name) { const r = n.attr(nodeId(this), String(name)); return typeof r === 'number' ? fail(r) : r; }
    // The namespaced forms pass "namespace U+0000 name" (Hosts.Dom.nsName?).
    getAttributeNS(ns, name) { const r = n.attr(nodeId(this), nsArg(ns) + '\u0000' + String(name)); return typeof r === 'number' ? fail(r) : r; }
    hasAttribute(name) { return this.getAttribute(name) !== null; }
    hasAttributeNS(ns, name) { return this.getAttributeNS(ns, name) !== null; }
    hasAttributes() { return this.getAttributeNames().length > 0; }
    setAttribute(name, value) {
      if (arguments.length < 2) throw new TypeError('setAttribute: 2 arguments required');
      const k = String(name), v = String(value);
      chk(n.setAttr(nodeId(this), k, v));
      // An event handler content attribute: a name that starts with "on", in any case.
      if (k.length >= 2 && (k.charCodeAt(0) | 32) === 111 && (k.charCodeAt(1) | 32) === 110)
        contentHandler(this, k.toLowerCase().slice(2), v);
    }
    setAttributeNS(ns, name, value) {
      if (arguments.length < 3) throw new TypeError('setAttributeNS: 3 arguments required');
      chk(n.setAttr(nodeId(this), nsArg(ns) + '\u0000' + String(name), String(value)));
    }
    removeAttribute(name) {
      const k = lowerIfHtml(this, String(name)), a = attrNodes(this).find(x => x.name === k);
      if (a) detachAttr(a);
      chk(n.removeAttr(nodeId(this), String(name)));
      // Removing an event handler content attribute deactivates the handler (HTML §8.1.8.1).
      if (a && k.startsWith('on') && handlerNames.includes(k.slice(2)) && this instanceof HTMLElement)
        setHandler(windowReflecting(this) && bodyWindowHandlers.has(k.slice(2)) ? window : this, k.slice(2), null);
    }
    removeAttributeNS(ns, name) { const a = attrNode(this, nsArg(ns) || null, String(name)); if (a) detachAttr(a); chk(n.removeAttr(nodeId(this), nsArg(ns) + '\u0000' + String(name))); }
    toggleAttribute(name, force) {
      name = String(name);
      chk(n.query(0, 3, name));
      const has = this.hasAttribute(name);
      if (has && force !== true) { this.removeAttribute(name); return false; }
      if (!has && (force === undefined || force === true)) { this.setAttribute(name, ''); return true; }
      return has;
    }
    getAttributeNode(name) { name = lowerIfHtml(this, String(name)); return attrNodes(this).find(a => a.name === name) ?? null; }
    getAttributeNodeNS(ns, name) { return attrNode(this, nsArg(ns) || null, String(name)); }
    setAttributeNode(attr) { return setAttrNode(this, attr); }
    setAttributeNodeNS(attr) { return setAttrNode(this, attr); }
    removeAttributeNode(attr) {
      if (!(attr instanceof Attr) || attrState.get(attr).el !== this) throw new DOMException('The attribute is not on this element.', 'NotFoundError');
      const a = attrState.get(attr);
      detachAttr(attr); chk(n.removeAttr(nodeId(this), (a.ns ?? '') + '\u0000' + a.lname)); return attr;
    }
    getAttributeNames() { const s = str(nodeId(this), 6) ?? ''; const xs = s === '' ? [] : s.split('\u0000'); return xs.filter((x, i) => i % 2 === 0 && i + 1 < xs.length); }
    get attributes() { let m = attrMaps.get(this); if (!m) attrMaps.set(this, m = namedNodeMap(this)); return m; }
    matches(sel) { if (arguments.length < 1) throw new TypeError('matches: 1 argument required'); return selectorQuery(nodeId(this), 8, sel) === '1'; }
    webkitMatchesSelector(sel) { if (arguments.length < 1) throw new TypeError('webkitMatchesSelector: 1 argument required'); return this.matches(sel); }
    closest(sel) { if (arguments.length < 1) throw new TypeError('closest: 1 argument required'); const k = selectorQuery(nodeId(this), 9, sel); return k === null ? null : wrap(Number(k)); }
    insertAdjacentElement(where, el) { return insertAdjacent(this, where, el); }
    insertAdjacentText(where, text) { insertAdjacent(this, where, document.createTextNode(text)); }
  }
  // ---- Attr and NamedNodeMap (DOM §4.9.1, §4.9.2) ----------------------------------------
  // The attributes are Lean's, on their element (Hosts.Dom node_query 2 lists them). An Attr
  // names one of them (element, namespace, local name); a removed or new Attr keeps its own
  // value until it is set on an element. One Attr object per attribute.
  const nsArg = ns => ns === null || ns === undefined ? '' : String(ns);
  const lowerIfHtml = (el, name) => info(nodeId(el), 8) === 1 ? name.replace(/[A-Z]/g, c => c.toLowerCase()) : name;
  const attrState = new WeakMap(), attrObjects = new Map(), attrMaps = new WeakMap();
  const attrKey = (id, ns, lname) => id + '\u0000' + (ns ?? '') + '\u0000' + lname;
  const newAttr = (fields) => { const o = Object.create(Attr.prototype); attrState.set(o, fields); return o; };
  const attrList = id => {
    const s = chk(n.query(id, 2, '')) ?? '', xs = s === '' ? [] : s.split('\u0000'), out = [];
    for (let i = 0; i + 3 < xs.length; i += 4) out.push({ ns: xs[i] || null, pfx: xs[i + 1] || null, lname: xs[i + 2], value: xs[i + 3] });
    return out;
  };
  const attrNodes = el => {
    const id = nodeId(el);
    return attrList(id).map(a => {
      const key = attrKey(id, a.ns, a.lname);
      let o = attrObjects.get(key);
      if (!o) { o = newAttr({ el, ns: a.ns, pfx: a.pfx, lname: a.lname, value: a.value, doc: info(id, 7) }); attrObjects.set(key, o); }
      return o;
    });
  };
  const attrNode = (el, ns, lname) => attrNodes(el).find(a => { const s = attrState.get(a); return s.ns === ns && s.lname === lname; }) ?? null;
  const detachAttr = attr => {
    const a = attrState.get(attr);
    if (!a.el) return;
    const id = nodeId(a.el), v = n.attr(id, (a.ns ?? '') + '\u0000' + a.lname);
    if (typeof v === 'string') a.value = v;
    attrObjects.delete(attrKey(id, a.ns, a.lname)); a.el = null;
  };
  const setAttrNode = (el, attr) => {
    if (!(attr instanceof Attr)) throw new TypeError("parameter is not of type 'Attr'");
    const a = attrState.get(attr);
    if (a.el !== null && a.el !== el) throw new DOMException('The attribute is in use by another element.', 'InUseAttributeError');
    const old = attrNode(el, a.ns, a.lname);
    if (old === attr) return attr;
    const value = a.value;
    if (old) detachAttr(old);
    const id = nodeId(el);
    chk(n.setAttr(id, a.ns === null && a.pfx === null ? a.lname : (a.ns ?? '') + '\u0000' + (a.pfx === null ? '' : a.pfx + ':') + a.lname, value));
    a.el = el; a.doc = info(id, 7); attrObjects.set(attrKey(id, a.ns, a.lname), attr);
    return old;
  };
  class Attr extends Node {
    get nodeType() { return 2; }
    get nodeName() { return this.name; }
    get name() { const a = attrState.get(this); return a.pfx === null ? a.lname : a.pfx + ':' + a.lname; }
    get localName() { return attrState.get(this).lname; }
    get namespaceURI() { return attrState.get(this).ns; }
    get prefix() { return attrState.get(this).pfx; }
    get ownerElement() { return attrState.get(this).el; }
    get specified() { return true; }
    get value() {
      const a = attrState.get(this);
      if (a.el) { const v = n.attr(nodeId(a.el), (a.ns ?? '') + '\u0000' + a.lname); if (typeof v === 'string') return a.value = v; }
      return a.value;
    }
    set value(v) {
      const a = attrState.get(this); v = String(v);
      if (a.el) chk(n.setAttr(nodeId(a.el), (a.ns ?? '') + '\u0000' + (a.pfx === null ? '' : a.pfx + ':') + a.lname, v));
      else a.value = v;
    }
    get nodeValue() { return this.value; }
    set nodeValue(v) { this.value = v == null ? '' : v; }
    get textContent() { return this.value; }
    set textContent(v) { this.value = v == null ? '' : v; }
    get ownerDocument() { return wrap(attrState.get(this).doc); }
    get parentNode() { return null; }
    get parentElement() { return null; }
    get firstChild() { return null; }
    get lastChild() { return null; }
    get previousSibling() { return null; }
    get nextSibling() { return null; }
    get childNodes() { return staticList([]); }
    hasChildNodes() { return false; }
    get isConnected() { return false; }
    getRootNode() { return this; }
    cloneNode() { const a = attrState.get(this); return newAttr({ el: null, ns: a.ns, pfx: a.pfx, lname: a.lname, value: this.value, doc: a.doc }); }
    isEqualNode(o) { return o instanceof Attr && o.namespaceURI === this.namespaceURI && o.localName === this.localName && o.value === this.value; }
    contains(o) { return o === this; }
    lookupNamespaceURI(prefix) { const el = this.ownerElement; return el ? el.lookupNamespaceURI(prefix) : null; }
    lookupPrefix(ns) { const el = this.ownerElement; return el ? el.lookupPrefix(ns) : null; }
    appendChild() { throw new DOMException('An Attr has no children.', 'HierarchyRequestError'); }
    insertBefore() { throw new DOMException('An Attr has no children.', 'HierarchyRequestError'); }
  }
  class NamedNodeMap { constructor() { throw new TypeError('Illegal constructor'); } }
  const namedNodeMap = el => {
    const target = Object.create(NamedNodeMap.prototype);
    const names = () => { const xs = attrNodes(el), out = [];
      for (const a of xs) { const q = a.name; if (out.includes(q)) continue; if (info(nodeId(el), 8) === 1 && /[A-Z]/.test(q)) continue; out.push(q); } return out; };
    const index = p => typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p);
    const proxy = new Proxy(target, {
      get(t, p, r) {
        if (index(p)) return attrNodes(el)[Number(p)];
        if (p === Symbol.iterator) return function* () { yield* attrNodes(el); };
        if (p === 'length') return attrNodes(el).length;
        if (typeof p === 'string' && !(p in t) && names().includes(p)) return el.getAttributeNode(p);
        return Reflect.get(t, p, r);
      },
      has(t, p) { if (index(p)) return Number(p) < attrNodes(el).length; if (typeof p === 'string' && names().includes(p)) return true; return Reflect.has(t, p); },
      ownKeys(t) { return [...attrNodes(el).keys()].map(String).concat(names()); },
      getOwnPropertyDescriptor(t, p) {
        if (index(p) && Number(p) < attrNodes(el).length) return { value: attrNodes(el)[Number(p)], enumerable: true, configurable: true, writable: false };
        if (typeof p === 'string' && !(p in t) && names().includes(p)) return { value: el.getAttributeNode(p), enumerable: false, configurable: true, writable: false };
        return undefined;
      },
    });
    mapOwners.set(proxy, el);
    return proxy;
  };
  const mapOwners = new WeakMap();
  const attrMapOwner = m => { const el = mapOwners.get(m); if (!el) throw new TypeError('Illegal invocation'); return el; };
  for (const [k, f] of Object.entries({
    item(i) { return attrNodes(attrMapOwner(this))[i >>> 0] ?? null; },
    getNamedItem(name) { return attrMapOwner(this).getAttributeNode(name); },
    getNamedItemNS(ns, name) { return attrMapOwner(this).getAttributeNodeNS(ns, name); },
    setNamedItem(a) { return attrMapOwner(this).setAttributeNode(a); },
    setNamedItemNS(a) { return attrMapOwner(this).setAttributeNodeNS(a); },
    removeNamedItem(name) { const el = attrMapOwner(this), a = el.getAttributeNode(name); if (!a) throw new DOMException('No such attribute.', 'NotFoundError'); return el.removeAttributeNode(a); },
    removeNamedItemNS(ns, name) { const el = attrMapOwner(this), a = el.getAttributeNodeNS(ns, name); if (!a) throw new DOMException('No such attribute.', 'NotFoundError'); return el.removeAttributeNode(a); },
  })) define(NamedNodeMap.prototype, k, f);
  Object.defineProperty(NamedNodeMap.prototype, 'length', { get() { return attrNodes(attrMapOwner(this)).length; }, configurable: true });
  const insertAdjacent = (el, where, node) => {
    switch (String(where).toLowerCase()) {
      case 'beforebegin': if (!el.parentNode) return null; el.parentNode.insertBefore(node, el); return node;
      case 'afterbegin': el.insertBefore(node, el.firstChild); return node;
      case 'beforeend': el.appendChild(node); return node;
      case 'afterend': if (!el.parentNode) return null; el.parentNode.insertBefore(node, el.nextSibling); return node;
      default: throw new DOMException('bad position', 'SyntaxError');
    }
  };
  class HTMLElement extends Element {
    // title, lang, dir, hidden and the other reflected attributes: DOM.Reflect (dombreadth section).
    get dataset() {
      const el = this;
      return new Proxy({}, {
        get: (t, p) => typeof p === 'string' ? el.getAttribute('data-' + p.replace(/[A-Z]/g, c => '-' + c.toLowerCase())) ?? undefined : undefined,
        set: (t, p, v) => { el.setAttribute('data-' + String(p).replace(/[A-Z]/g, c => '-' + c.toLowerCase()), String(v)); return true; },
      });
    }
    get style() { let s = styles.get(this); if (!s) styles.set(this, s = styleOf(this)); return s; }
    click() {
      if (chk(n.query(nodeId(this), 11, '')) === '1') return;
      if (clicking.has(this)) return;
      clicking.add(this);
      try {
        const e = new MouseEvent('click', { bubbles: true, cancelable: true, composed: true, view: window });
        dispatch(this, e);
      } finally { clicking.delete(this); }
    }
    focus() {}
    blur() {}
    get offsetWidth() { return Math.round(layoutOf(this)[2]); }
    get offsetHeight() { return Math.round(layoutOf(this)[3]); }
    get offsetLeft() { return Math.round(layoutOf(this)[0]); }
    get offsetTop() { return Math.round(layoutOf(this)[1]); }
    get offsetParent() { return this.isConnected && this.localName !== 'body' && this.localName !== 'html' ? document.body : null; }
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
    ['HTMLVideoElement', ['video']], ['HTMLAudioElement', ['audio']], ['HTMLSlotElement', ['slot']],
    ['HTMLAreaElement', ['area']], ['HTMLBaseElement', ['base']], ['HTMLTableCaptionElement', ['caption']],
    ['HTMLTableColElement', ['col', 'colgroup']], ['HTMLDataElement', ['data']], ['HTMLDataListElement', ['datalist']],
    ['HTMLModElement', ['del', 'ins']], ['HTMLDirectoryElement', ['dir']], ['HTMLDListElement', ['dl']],
    ['HTMLEmbedElement', ['embed']], ['HTMLFontElement', ['font']], ['HTMLFrameElement', ['frame']],
    ['HTMLFrameSetElement', ['frameset']], ['HTMLLegendElement', ['legend']], ['HTMLMapElement', ['map']],
    ['HTMLMeterElement', ['meter']], ['HTMLObjectElement', ['object']], ['HTMLOptGroupElement', ['optgroup']],
    ['HTMLOutputElement', ['output']], ['HTMLParamElement', ['param']], ['HTMLProgressElement', ['progress']],
    ['HTMLQuoteElement', ['q', 'blockquote']], ['HTMLSourceElement', ['source']],
    ['HTMLTableSectionElement', ['tbody', 'thead', 'tfoot']], ['HTMLTimeElement', ['time']], ['HTMLTrackElement', ['track']],
    ['HTMLMenuElement', ['menu']], ['HTMLPictureElement', ['picture']], ['HTMLMarqueeElement', ['marquee']]];
  const named = {};
  for (const [name, tags] of elementClasses) named[name] = htmlClass(name, tags);
  Object.defineProperty(named.HTMLTemplateElement.prototype, 'content', { get() { return wrap(info(nodeId(this), 9)); }, configurable: true });
  // An iframe's document is Lean's (Hosts.Page.start `frames`, node_info 11). The frames share
  // this realm: a frame's window is a view of this window with its own document.
  // Reflected content attributes (HTML §2.6.1): strings, and URLs resolved against the
  // document's URL.
  const reflectString = (C, names) => { for (const k of names) Object.defineProperty(C.prototype, k, {
    get() { return this.getAttribute(k.toLowerCase()) ?? ''; }, set(v) { this.setAttribute(k.toLowerCase(), String(v)); }, configurable: true, enumerable: true }); };
  const reflectURL = (C, names) => { for (const k of names) Object.defineProperty(C.prototype, k, {
    get() { const v = this.getAttribute(k); if (v === null) return ''; return resolveURL(v) ?? v; },
    set(v) { this.setAttribute(k, String(v)); }, configurable: true, enumerable: true }); };
  // Form controls, links, labels and details (HTML §4.10, §4.6, §4.11): the state and the
  // decisions are Lean's (DOM.Forms: node_query 10-14, tree_op 6-9).
  const reflectBool = (C, names) => { for (const k of names) Object.defineProperty(C.prototype, k, {
    get() { return this.hasAttribute(k.toLowerCase()); }, set(v) { this.toggleAttribute(k.toLowerCase(), !!v); }, configurable: true, enumerable: true }); };
  const typeState = el => chk(n.query(nodeId(el), 14, ''));
  Object.defineProperties(named.HTMLInputElement.prototype, {
    checked: { get() { return chk(n.treeOp(nodeId(this), 0, 7)) === 1; }, set(v) { chk(n.treeOp(nodeId(this), v ? 1 : 0, 6)); }, configurable: true, enumerable: true },
    defaultChecked: { get() { return this.hasAttribute('checked'); }, set(v) { this.toggleAttribute('checked', !!v); }, configurable: true, enumerable: true },
    type: { get() { return typeState(this); }, set(v) { this.setAttribute('type', String(v)); }, configurable: true, enumerable: true },
    value: { get() { return this.getAttribute('value') ?? (['checkbox', 'radio'].includes(typeState(this)) ? 'on' : ''); }, set(v) { this.setAttribute('value', String(v)); }, configurable: true, enumerable: true },
    form: { get() { return formOf(this); }, configurable: true, enumerable: true },
  });
  Object.defineProperties(named.HTMLButtonElement.prototype, {
    type: { get() { return typeState(this); }, set(v) { this.setAttribute('type', String(v)); }, configurable: true, enumerable: true },
    form: { get() { return formOf(this); }, configurable: true, enumerable: true },
  });
  reflectString(named.HTMLInputElement, ['name']); reflectBool(named.HTMLInputElement, ['disabled', 'required', 'readOnly', 'multiple']);
  reflectString(named.HTMLButtonElement, ['name', 'value']); reflectBool(named.HTMLButtonElement, ['disabled']);
  reflectBool(named.HTMLSelectElement, ['disabled']); reflectBool(named.HTMLTextAreaElement, ['disabled']);
  reflectBool(named.HTMLFieldSetElement, ['disabled']); reflectBool(named.HTMLDetailsElement, ['open']);
  reflectString(named.HTMLFormElement, ['name', 'method', 'action']);
  reflectURL(named.HTMLAnchorElement, ['href']); reflectString(named.HTMLAnchorElement, ['target', 'download', 'rel']);
  reflectURL(named.HTMLAreaElement, ['href']);
  Object.defineProperty(named.HTMLLabelElement.prototype, 'htmlFor', { get() { return this.getAttribute('for') ?? ''; }, set(v) { this.setAttribute('for', String(v)); }, configurable: true });
  const formOf = el => { let k = info(nodeId(el), 1); while (k >= 0) { if (info(k, 0) === 1 && info(k, 8) === 1 && str(k, 0) === 'form') return wrap(k); k = info(k, 1); } return null; };
  class SubmitEvent extends Event {
    constructor(type, init = undefined) { super(type, init); state(this).submitter = initOf(init).submitter ?? null; }
    get submitter() { return state(this).submitter; }
  }
  // The form submission algorithm up to navigation (HTML §4.10.21.3 steps 6.5-6.7): the
  // submit event; a navigation would follow, but nothing loads here.
  const submitForm = (form, submitter) => {
    if (!form.isConnected) return; // a form that is not connected does not submit (§4.10.21.3 step 1)
    const e = new SubmitEvent('submit', { bubbles: true, cancelable: true, submitter: submitter === form ? null : submitter });
    state(e).trusted = true;
    dispatch(form, e);
  };
  const resetForm = form => {
    const e = new Event('reset', { bubbles: true, cancelable: true });
    state(e).trusted = true;
    if (dispatch(form, e)) chk(n.treeOp(nodeId(form), 0, 9));
  };
  Object.defineProperties(named.HTMLFormElement.prototype, {
    submit: { value() {}, writable: true, configurable: true },
    requestSubmit: { value(submitter) { submitForm(this, submitter ?? this); }, writable: true, configurable: true },
    reset: { value() { resetForm(this); }, writable: true, configurable: true },
  });
  const fire = (target, type, init) => { const e = new Event(type, init); state(e).trusted = true; return dispatch(target, e); };
  // DOM §2.9: legacy-pre-activation, legacy-canceled-activation and activation behaviours.
  const preActivation = k => {
    if (!(info(k, 8) === 1 && str(k, 0) === 'input')) return null;
    const t = chk(n.query(k, 14, ''));
    if (t === 'checkbox') { const old = chk(n.treeOp(k, 0, 7)); chk(n.treeOp(k, old ? 0 : 1, 6)); return { old }; }
    if (t === 'radio') { const prev = chk(n.treeOp(k, 0, 8)), old = chk(n.treeOp(k, 0, 7)); chk(n.treeOp(k, 1, 6)); return { prev, old }; }
    return null;
  };
  const canceledActivation = (k, st) => {
    if (!st) return;
    if (st.prev === undefined) chk(n.treeOp(k, st.old, 6));
    else if (st.prev >= 0) chk(n.treeOp(st.prev, 1, 6));
    else chk(n.treeOp(k, st.old, 6));
  };
  const activation = (k, targetId) => {
    if (info(k, 8) !== 1) return;
    const el = wrap(k), name = str(k, 0);
    if (name === 'input' || name === 'button') {
      const t = chk(n.query(k, 14, ''));
      if (t === 'checkbox' || t === 'radio') {
        if (!el.isConnected) return;
        fire(el, 'input', { bubbles: true, composed: true }); fire(el, 'change', { bubbles: true });
        return;
      }
      if (chk(n.query(k, 11, '')) === '1') return;
      const form = formOf(el);
      if (!form) return;
      if (t === 'submit' || t === 'image') submitForm(form, el);
      else if (t === 'reset') resetForm(form);
    } else if (name === 'a' || name === 'area') {
      followHyperlink(el.href);
    } else if (name === 'label') {
      const c = chk(n.query(k, 13, String(targetId)));
      if (c !== null) wrap(Number(c)).click();
    } else if (name === 'summary') {
      const details = el.parentNode;
      details.toggleAttribute('open');
      setTimeout(() => fire(details, 'toggle', {}), 0);
    }
  };
  for (const C of [named.HTMLBodyElement, named.HTMLFrameSetElement])
    for (const name of bodyWindowHandlers) {
      Object.defineProperty(C.prototype, 'on' + name, { get() { return handlerOf(window, name); },
        set(f) { setHandler(window, name, f); }, configurable: true, enumerable: true });
    }
  reflectURL(named.HTMLIFrameElement, ['src']); reflectString(named.HTMLIFrameElement, ['srcdoc', 'name', 'width', 'height', 'allow']);
  reflectURL(named.HTMLImageElement, ['src']); reflectString(named.HTMLImageElement, ['alt']);
  reflectURL(named.HTMLScriptElement, ['src']);
  reflectURL(named.HTMLLinkElement, ['href']); reflectString(named.HTMLLinkElement, ['rel', 'type', 'media']);
  Object.defineProperties(named.HTMLIFrameElement.prototype, {
    contentDocument: { get() { return wrap(info(nodeId(this), 11)); }, configurable: true },
    contentWindow: { get() { const d = info(nodeId(this), 11); return d < 0 ? null : frameWindow(d); }, configurable: true },
  });
  // ---- WebGPU subset (docs/designissues/2026-11-08-page-gpu.md) ------------------------
  // Page-facing objects only. Each method packs its arguments into one `gpu_command` import
  // (`n.gpu(op, header, payload)`); Lean (L4Factoidal.PageGpu) decodes, validates and turns
  // it into host commands, or refuses it. A refusal comes back as text and becomes a
  // GPUValidationError of the device (error scopes, `onuncapturederror`), as in WebGPU.
  // Nothing here decides what is allowed.
  const gpuNames = { float32: 1, float32x2: 2, float32x3: 3, float32x4: 4 };
  const gpuTopology = { 'triangle-list': 0, 'triangle-strip': 1, 'line-list': 2, 'point-list': 3 };
  const GPUBufferUsage = Object.freeze({ MAP_READ: 1, MAP_WRITE: 2, COPY_SRC: 4, COPY_DST: 8, INDEX: 16, VERTEX: 32,
    UNIFORM: 64, STORAGE: 128, INDIRECT: 256, QUERY_RESOLVE: 512 });
  const GPUTextureUsage = Object.freeze({ COPY_SRC: 1, COPY_DST: 2, TEXTURE_BINDING: 4, STORAGE_BINDING: 8, RENDER_ATTACHMENT: 16 });
  const GPUShaderStage = Object.freeze({ VERTEX: 1, FRAGMENT: 2, COMPUTE: 4 });
  const GPUColorWrite = Object.freeze({ RED: 1, GREEN: 2, BLUE: 4, ALPHA: 8, ALL: 15 });
  class GPUError { constructor(message) { this.message = String(message); } }
  class GPUValidationError extends GPUError {}
  class GPUOutOfMemoryError extends GPUError {}
  let gpuNext = 1;
  // A view over all of its buffer is sent as the buffer (n.gpu copies it); only a part is sliced.
  const gpuBytes = data => {
    if (data instanceof ArrayBuffer) return data;
    if (ArrayBuffer.isView(data)) return data.byteOffset === 0 && data.byteLength === data.buffer.byteLength ? data.buffer
      : data.buffer.slice(data.byteOffset, data.byteOffset + data.byteLength);
    throw new TypeError('GPU data must be an ArrayBuffer or a typed array');
  };
  // The frame path (shaders, 2026-11-09): a pass goes to Lean with a binary header (op + 64,
  // PageGpu.Wire.binaryOp: a u32 count, then u32 numbers), so no number becomes text here;
  // in a script engine in WasmVM that conversion cost more than the rest of a frame. A write
  // sends its two numbers as text, which is cheaper than a typed array for two. Numbers are
  // not clamped here: Lean refuses one that is not a whole number in range. Whether the
  // engine reads binary headers is asked once, with a binary destroy of no object (an engine
  // from before the binary op answers otherwise); if not, passes go with text headers.
  let gpuBinary;
  const gpuPass = (header, payload) => {
    if (gpuBinary === undefined) {
      const probe = n.gpu(72, new Uint32Array([1, 0]).buffer, '');
      gpuBinary = typeof probe === 'string' && probe.startsWith('gpu: destroy');
    }
    if (gpuBinary) return n.gpu(71, header.buffer, payload ?? '');
    return n.gpu(7, Array.prototype.join.call(header.subarray(1), ' '), payload ?? '');
  };
  // One pass's binary header: the count of numbers, then canvas, clear r g b a, the draws
  // (each pipeline bind nVb vb* count instances first firstInstance), from the encoder's words.
  const passHeader = (canvas, clear, count, words) => {
    const h = new Uint32Array(7 + words.length);
    h[0] = 6 + words.length; h[1] = canvas; h[2] = clear[0]; h[3] = clear[1]; h[4] = clear[2]; h[5] = clear[3]; h[6] = count;
    h.set(words, 7);
    return h;
  };
  // A colour channel 0..1 as 0..255 (NaN as 0); the comparisons convert x to a number.
  const unorm = x => x >= 1 ? 255 : x > 0 ? Math.round(x * 255) : 0;
  class GPUDevice extends EventTarget {}
  const gpuDevice = (() => {
    const device = new GPUDevice();
    const scopes = [];
    let lostResolve;
    const report = message => {
      const error = new GPUValidationError(message);
      for (let i = scopes.length - 1; i >= 0; i--) if (scopes[i].filter === 'validation') { scopes[i].error ??= error; return; }
      console.warn('WebGPU: ' + message);
      const ev = new Event('uncapturederror'); ev.error = error;
      if (typeof device.onuncapturederror === 'function') device.onuncapturederror.call(device, ev);
      device.dispatchEvent(ev);
    };
    const send = (op, header, payload) => {
      const r = n.gpu(op, header.map(x => String(Math.max(0, Math.floor(Number(x) || 0)))).join(' '), payload ?? '');
      const message = typeof r === 'number' ? 'gpu: import error ' + r : r;
      if (message) report(message);
      return !message;
    };
    class GPUBuffer {
      constructor(d) {
        this.id = gpuNext++; this.size = Number(d.size) || 0; this.usage = Number(d.usage) | 0;
        this.mapState = d.mappedAtCreation ? 'mapped' : 'unmapped';
        // mappedAtCreation: the page fills a local copy; unmap writes it (so COPY_DST is added).
        this.ok = send(2, [this.id, this.size, this.usage | (d.mappedAtCreation ? 8 : 0)]);
        if (d.mappedAtCreation) this.mapped = new ArrayBuffer(this.size);
      }
      getMappedRange(offset = 0, size) {
        if (!this.mapped) throw new DOMException('buffer is not mapped', 'OperationError');
        if (offset !== 0) throw new DOMException('getMappedRange at an offset is not in the page GPU subset', 'OperationError');
        return this.mapped;
      }
      unmap() {
        if (!this.mapped) return;
        send(3, [this.id, 0], this.mapped); this.mapped = undefined; this.mapState = 'unmapped';
      }
      mapAsync() { return Promise.reject(new DOMException('mapAsync is not in the page GPU subset', 'OperationError')); }
      destroy() { send(8, [this.id]); }
    }
    class GPUShaderModule {
      constructor(d) {
        this.id = gpuNext++; this.code = String(d.code);
        const r = n.gpu(4, String(this.id), this.code), got = typeof r === 'number' ? 'gpu: import error ' + r : r;
        this.error = got || null;
        if (got) report(got);
      }
      getCompilationInfo() { return Promise.resolve({ messages: this.error ? [{ type: 'error', message: this.error, lineNum: 0, linePos: 0, offset: 0, length: 0 }] : [] }); }
    }
    class GPUBindGroupLayout { constructor(pipeline) { this.pipeline = pipeline; } }
    class GPURenderPipeline {
      constructor(d) {
        this.id = gpuNext++;
        const v = d.vertex ?? {}, f = d.fragment ?? {};
        if (f.module && v.module && f.module !== v.module) { report('gpu: vertex and fragment must be one shader module'); this.ok = false; return; }
        const buffers = (v.buffers ?? []).filter(Boolean);
        const header = [this.id, v.module?.id ?? 0, gpuTopology[d.primitive?.topology ?? 'triangle-list'] ?? 99, buffers.length];
        for (const b of buffers) {
          const attrs = b.attributes ?? [];
          header.push(b.arrayStride, attrs.length);
          for (const a of attrs) header.push(gpuNames[a.format] ?? 0, a.offset, a.shaderLocation);
        }
        this.ok = send(5, header, (v.entryPoint ?? '') + '\n' + (f.entryPoint ?? ''));
      }
      getBindGroupLayout() { return new GPUBindGroupLayout(this); }
    }
    class GPUBindGroup {
      constructor(d) {
        this.id = gpuNext++;
        const e = (d.entries ?? []).find(x => x.binding === 0);
        this.ok = send(6, [this.id, d.layout?.pipeline?.id ?? 0, e?.resource?.buffer?.id ?? e?.resource?.id ?? 0]);
      }
    }
    // A pass keeps its draws as the words of its binary header (passHeader).
    class GPURenderPassEncoder {
      constructor(target, clear) { this.target = target; this.clear = clear; this.count = 0; this.words = []; this.pipeline = 0; this.bind = 0; this.vbufs = []; }
      setPipeline(p) { this.pipeline = p ? p.id : 0; }
      setBindGroup(index, g) { if (index === 0) this.bind = g ? g.id : 0; }
      setVertexBuffer(slot, b) { this.vbufs[slot] = b ? b.id : 0; }
      setViewport() {} setScissorRect() {} setBlendConstant() {} setStencilReference() {}
      draw(count, instances = 1, first = 0, firstInstance = 0) {
        const w = this.words, v = this.vbufs;
        w.push(this.pipeline, this.bind, v.length);
        for (let i = 0; i < v.length; i++) w.push(v[i] ?? 0);
        w.push(+count, +instances, +first, +firstInstance);
        this.count++;
      }
      end() {}
    }
    // The last clear colour and its bytes: a page clears to the same colour frame after frame.
    let lastR = 0, lastG = 0, lastB = 0, lastA = 0, lastClear = [0, 0, 0, 0];
    class GPUCommandEncoder {
      constructor() { this.passes = []; }
      beginRenderPass(d) {
        const a = (d.colorAttachments ?? [])[0] ?? {}, c = a.clearValue ?? { r: 0, g: 0, b: 0, a: 0 };
        const list = Array.isArray(c), r = list ? c[0] : c.r, g = list ? c[1] : c.g, b = list ? c[2] : c.b, al = list ? c[3] : c.a;
        if (r !== lastR || g !== lastG || b !== lastB || al !== lastA) {
          lastR = r; lastG = g; lastB = b; lastA = al; lastClear = [unorm(r), unorm(g), unorm(b), unorm(al)];
        }
        const pass = new GPURenderPassEncoder(a.view?.canvas ?? 0, lastClear);
        this.passes.push(pass); return pass;
      }
      finish() { return { passes: this.passes }; }
    }
    const queue = Object.freeze({
      writeBuffer(buffer, offset, data, dataOffset = 0, size) {
        let bytes;
        if (dataOffset || size !== undefined) {
          const unit = ArrayBuffer.isView(data) && data.BYTES_PER_ELEMENT ? data.BYTES_PER_ELEMENT : 1;
          const from = (ArrayBuffer.isView(data) ? data.byteOffset : 0) + dataOffset * unit;
          const all = ArrayBuffer.isView(data) ? data.buffer : gpuBytes(data);
          bytes = all.slice(from, size === undefined ? (ArrayBuffer.isView(data) ? data.byteOffset + data.byteLength : undefined) : from + size * unit);
        } else bytes = gpuBytes(data);
        const r = n.gpu(3, buffer.id + ' ' + +offset, bytes);
        if (r) report(typeof r === 'number' ? 'gpu: import error ' + r : r);
      },
      submit(buffers) {
        if (!buffers) return;
        for (let i = 0; i < buffers.length; i++) {
          const passes = buffers[i].passes;
          if (passes) for (let j = 0; j < passes.length; j++) {
            const p = passes[j], r = gpuPass(passHeader(p.target, p.clear, p.count, p.words));
            if (r) report(typeof r === 'number' ? 'gpu: import error ' + r : r);
          }
        }
      },
      onSubmittedWorkDone() { return Promise.resolve(); },
    });
    Object.assign(device, {
      queue, features: new Set(), limits: Object.freeze({ maxBufferSize: 16777216, maxVertexBuffers: 8, maxVertexAttributes: 16,
        maxTextureDimension2D: 2048, maxBindGroups: 1, maxUniformBufferBindingSize: 65536 }),
      lost: new Promise(r => { lostResolve = r; }), onuncapturederror: null, label: '',
      createBuffer: d => new GPUBuffer(d ?? {}),
      createShaderModule: d => new GPUShaderModule(d ?? {}),
      createRenderPipeline: d => new GPURenderPipeline(d ?? {}),
      createRenderPipelineAsync: d => Promise.resolve(new GPURenderPipeline(d ?? {})),
      createBindGroup: d => new GPUBindGroup(d ?? {}),
      createCommandEncoder: () => new GPUCommandEncoder(),
      createPipelineLayout: () => 'auto',
      createBindGroupLayout: () => new GPUBindGroupLayout(null),
      pushErrorScope: filter => { scopes.push({ filter, error: null }); },
      popErrorScope: () => scopes.length ? Promise.resolve(scopes.pop().error) : Promise.reject(new DOMException('no error scope', 'OperationError')),
      destroy() {},
    });
    return device;
  })();
  const gpuAdapter = Object.freeze({ features: new Set(), limits: gpuDevice.limits, isFallbackAdapter: false,
    info: Object.freeze({ vendor: 'foafnaut', architecture: 'lean-validated', device: '', description: 'WebGPU subset validated by Lean' }),
    requestDevice: () => Promise.resolve(gpuDevice), requestAdapterInfo: () => Promise.resolve(gpuAdapter.info) });
  const gpu = Object.freeze({ requestAdapter: () => Promise.resolve(gpuAdapter), getPreferredCanvasFormat: () => 'rgba8unorm',
    wgslLanguageFeatures: new Set() });
  const canvasSize = (el, name, fallback) => { const v = parseInt(el.getAttribute(name), 10); return v > 0 ? v : fallback; };
  const gpuContexts = new Map();
  class GPUCanvasContext {
    constructor(canvas) { this.canvas = canvas; this.id = 0; this.texture = null; }
    configure(d) {
      if (this.id) return;
      this.id = gpuNext++;
      if (d?.device !== gpuDevice) throw new TypeError('configure needs the device');
      const node = nodeId(this.canvas);
      const width = canvasSize(this.canvas, 'width', 300), height = canvasSize(this.canvas, 'height', 150);
      if (!(n.gpu(1, [this.id, node, width, height].join(' '), '') === '')) {
        console.warn('WebGPU: the canvas could not be configured'); this.id = 0;
      }
      // The canvas texture Lean made has the size of the canvas at configure; each frame's
      // texture is that one (no attribute read in a frame).
      const view = { canvas: this.id };
      this.texture = { width, height, format: 'rgba8unorm', createView: () => view, destroy() {} };
    }
    unconfigure() {}
    getCurrentTexture() {
      return this.texture ?? { width: 0, height: 0, format: 'rgba8unorm', createView: () => ({ canvas: 0 }), destroy() {} };
    }
  }
  // ---- WebGL 1 and 2 on the same Lean-validated layer (record, sections 6 and 6b) ----------
  // Page-facing state only (bound buffer, current program, attribute pointers, uniform values,
  // the clear colour); every object and every draw is a gpu_command that Lean validates. A
  // program is linked by Lean (op 9: GLSL ES 3.00 or 1.00 to the WGSL subset), which answers
  // the attribute locations and uniform offsets. The draws of a task are one render pass on
  // the canvas, sent after the task (as a WebGL drawing buffer is presented after it).
  const GL = {
    DEPTH_BUFFER_BIT: 0x100, STENCIL_BUFFER_BIT: 0x400, COLOR_BUFFER_BIT: 0x4000,
    POINTS: 0, LINES: 1, LINE_LOOP: 2, LINE_STRIP: 3, TRIANGLES: 4, TRIANGLE_STRIP: 5, TRIANGLE_FAN: 6,
    ARRAY_BUFFER: 0x8892, ELEMENT_ARRAY_BUFFER: 0x8893, STREAM_DRAW: 0x88E0, STATIC_DRAW: 0x88E4, DYNAMIC_DRAW: 0x88E8,
    BYTE: 0x1400, UNSIGNED_BYTE: 0x1401, SHORT: 0x1402, UNSIGNED_SHORT: 0x1403, INT: 0x1404, UNSIGNED_INT: 0x1405, FLOAT: 0x1406,
    FRAGMENT_SHADER: 0x8B30, VERTEX_SHADER: 0x8B31, COMPILE_STATUS: 0x8B81, LINK_STATUS: 0x8B82, DELETE_STATUS: 0x8B80,
    NO_ERROR: 0, INVALID_ENUM: 0x500, INVALID_VALUE: 0x501, INVALID_OPERATION: 0x502, OUT_OF_MEMORY: 0x505,
    DEPTH_TEST: 0x0B71, BLEND: 0x0BE2, CULL_FACE: 0x0B44, SCISSOR_TEST: 0x0C11,
    SRC_ALPHA: 0x0302, ONE_MINUS_SRC_ALPHA: 0x0303, ONE: 1, ZERO: 0, VERSION: 0x1F02, RENDERER: 0x1F01, VENDOR: 0x1F00,
    SHADING_LANGUAGE_VERSION: 0x8B8C, MAX_VERTEX_ATTRIBS: 0x8869, MAX_TEXTURE_SIZE: 0x0D33,
  };
  const glModes = { 0: 3, 1: 2, 4: 0, 5: 1 };
  class WebGLObject {}
  class WebGLBuffer extends WebGLObject {}
  class WebGLShader extends WebGLObject {}
  class WebGLProgram extends WebGLObject {}
  class WebGLUniformLocation { constructor(program, offset, type) { this.program = program; this.offset = offset; this.type = type; } }
  const glContextFor = (canvas, version) => {
    const gpuSend = (op, header, payload) => {
      const r = n.gpu(op, header.map(x => String(Math.max(0, Math.floor(Number(x) || 0)))).join(' '), payload ?? '');
      return typeof r === 'number' ? 'gpu: import error ' + r : r;
    };
    let error = 0, canvasId = 0, arrayBuffer = null, program = null, clear = [0, 0, 0, 0], draws = [], flushQueued = false;
    const attribs = [];
    let attribVersion = 0;
    const fail = (message, code = GL.INVALID_OPERATION) => { if (!error) error = code; console.warn('WebGL: ' + message); };
    const send = (op, header, payload) => { const m = gpuSend(op, header, payload); if (m && !m.startsWith('{')) { fail(m); return null; } return m; };
    const ensureCanvas = () => {
      if (canvasId) return canvasId;
      const id = gpuNext++;
      if (send(1, [id, nodeId(canvas), canvasSize(canvas, 'width', 300), canvasSize(canvas, 'height', 150)]) !== null) canvasId = id;
      return canvasId;
    };
    let drawCount = 0;
    const flush = () => {
      flushQueued = false;
      if (!drawCount || !ensureCanvas()) { draws = []; drawCount = 0; return; }
      const header = passHeader(canvasId, [unorm(clear[0]), unorm(clear[1]), unorm(clear[2]), unorm(clear[3])], drawCount, draws);
      draws = []; drawCount = 0;
      const m = gpuPass(header);
      if (m) fail(typeof m === 'number' ? 'gpu: import error ' + m : m);
    };
    const pipelineFor = (p, layouts, mode, key) => {
      let entry = p.pipelines.get(key);
      if (entry) return entry;
      const id = gpuNext++, header = [id, p.id, mode, layouts.length];
      for (const l of layouts) header.push(l.stride, 1, l.format, l.offset, l.location);
      if (send(5, header, 'vs\nfs') === null) return null;
      entry = { id, bind: 0 };
      if (p.uniformBuffer) {
        const bind = gpuNext++;
        if (send(6, [bind, id, p.uniformBuffer]) !== null) entry.bind = bind;
      }
      p.pipelines.set(key, entry);
      return entry;
    };
    // Uniform values go into the program's copy of its uniform buffer (views made at link),
    // sent once before a draw that follows a change.
    const up = loc => {
      if (!loc) return null;
      if (loc.program !== program) { fail('uniform location of another program'); return null; }
      program.uniformDirty = true;
      return program;
    };
    const setUniform = (loc, values, ints) => {
      const p = up(loc);
      if (!p) return;
      const view = ints ? p.i32 : p.f32, o = loc.offset >> 2;
      for (let i = 0; i < values.length; i++) view[o + i] = values[i];
    };
    const ctx = {
      canvas, drawingBufferWidth: canvasSize(canvas, 'width', 300), drawingBufferHeight: canvasSize(canvas, 'height', 150),
      getError() { const e = error; error = 0; return e; },
      getContextAttributes: () => ({ alpha: true, antialias: false, depth: false, stencil: false, premultipliedAlpha: true, preserveDrawingBuffer: false }),
      getExtension: () => null, getSupportedExtensions: () => [], isContextLost: () => false,
      getParameter(p) {
        if (p === GL.VERSION) return version === 2 ? 'WebGL 2.0 (Foafnaut, Lean-validated)' : 'WebGL 1.0 (Foafnaut, Lean-validated)';
        if (p === GL.SHADING_LANGUAGE_VERSION) return version === 2 ? 'WebGL GLSL ES 3.00' : 'WebGL GLSL ES 1.0';
        if (p === GL.VENDOR || p === GL.RENDERER) return 'Foafnaut';
        if (p === GL.MAX_VERTEX_ATTRIBS) return 16;
        if (p === GL.MAX_TEXTURE_SIZE) return 2048;
        return null;
      },
      viewport() {}, scissor() {}, enable() {}, disable() {}, blendFunc() {}, depthFunc() {}, cullFace() {}, frontFace() {},
      lineWidth() {}, pixelStorei() {}, colorMask() {}, depthMask() {}, flush() {}, finish() {},
      clearColor(r, g, b, a) { clear = [r, g, b, a]; },
      clear(mask) { /* every frame of a page canvas starts cleared to the clear colour (loadOp: clear) */ },
      createBuffer() { const b = new WebGLBuffer(); b.gpu = 0; b.size = 0; return b; },
      deleteBuffer(b) { if (b?.gpu) send(8, [b.gpu]); if (b) b.gpu = 0; },
      bindBuffer(target, b) { if (target === GL.ARRAY_BUFFER) arrayBuffer = b; else if (b) fail('only ARRAY_BUFFER in this slice', GL.INVALID_ENUM); },
      bufferData(target, data, usage) {
        if (target !== GL.ARRAY_BUFFER || !arrayBuffer) { fail('bufferData needs a bound ARRAY_BUFFER'); return; }
        const bytes = typeof data === 'number' ? new ArrayBuffer(data) : gpuBytes(data);
        const b = arrayBuffer, size = bytes.byteLength;
        if (b.gpu && b.size !== size) { send(8, [b.gpu]); b.gpu = 0; }
        if (!b.gpu) { const id = gpuNext++; if (send(2, [id, size, 32 | 8]) === null) return; b.gpu = id; b.size = size; attribVersion++; }
        if (size) send(3, [b.gpu, 0], bytes);
      },
      bufferSubData(target, offset, data) {
        if (target !== GL.ARRAY_BUFFER || !arrayBuffer?.gpu) { fail('bufferSubData needs a bound ARRAY_BUFFER with data'); return; }
        send(3, [arrayBuffer.gpu, offset], gpuBytes(data));
      },
      createShader(type) { const s = new WebGLShader(); s.type = type; s.source = ''; return s; },
      shaderSource(s, src) { s.source = String(src); },
      compileShader() {},
      getShaderParameter(s, p) { return p === GL.COMPILE_STATUS ? true : null; },
      getShaderInfoLog: () => '', deleteShader() {},
      createProgram() { const p = new WebGLProgram(); p.shaders = []; p.pipelines = new Map(); return p; },
      attachShader(p, s) { p.shaders.push(s); }, detachShader() {}, deleteProgram() {},
      bindAttribLocation() { fail('bindAttribLocation: use layout(location = n); Lean assigns locations'); },
      linkProgram(p) {
        const vs = p.shaders.find(s => s.type === GL.VERTEX_SHADER), fs = p.shaders.find(s => s.type === GL.FRAGMENT_SHADER);
        if (!vs || !fs) { p.log = 'a program needs a vertex and a fragment shader'; return; }
        p.id = gpuNext++;
        const answer = gpuSend(9, [p.id], vs.source + '\u0000' + fs.source);
        if (!answer.startsWith('{')) { p.log = answer; p.linked = false; console.warn('WebGL: ' + answer); return; }
        p.info = JSON.parse(answer); p.linked = true; p.log = '';
        p.attrList = Object.entries(p.info.attributes);
        if (p.info.uniformSize) {
          const id = gpuNext++;
          if (send(2, [id, p.info.uniformSize, 64 | 8]) !== null) p.uniformBuffer = id;
          p.uniformData = new ArrayBuffer(p.info.uniformSize); p.uniformDirty = true;
          p.f32 = new Float32Array(p.uniformData); p.i32 = new Int32Array(p.uniformData);
          // gl_FragCoord counts y from the bottom: Lean's translation reads the drawing
          // buffer's height from this uniform (PageGpu.Glsl, gl_FragHeight).
          const h = p.info.uniforms.gl_FragHeight;
          p.fragHeight = h ? h[0] >> 2 : -1;
        }
      },
      getProgramParameter(p, q) { return q === GL.LINK_STATUS ? !!p.linked : null; },
      getProgramInfoLog: p => p.log ?? '',
      useProgram(p) { program = p; },
      getAttribLocation(p, name) { const l = p.info?.attributes[name]; return l === undefined ? -1 : l; },
      getUniformLocation(p, name) {
        const u = String(name).startsWith('gl_') ? undefined : p.info?.uniforms[name];
        return u ? new WebGLUniformLocation(p, u[0], u[1]) : null;
      },
      // attribVersion moves only when an attribute changes, so a draw with the attributes of
      // the draw before reuses its pipeline and buffers (pages set them again each frame).
      enableVertexAttribArray(i) { const a = attribs[i] ??= {}; if (a.enabled !== true) { a.enabled = true; attribVersion++; } },
      disableVertexAttribArray(i) { const a = attribs[i] ??= {}; if (a.enabled !== false) { a.enabled = false; attribVersion++; } },
      vertexAttribPointer(i, size, type, normalized, stride, offset) {
        if (type !== GL.FLOAT || size < 1 || size > 4) { fail('only FLOAT attributes of 1 to 4 components', GL.INVALID_ENUM); return; }
        const a = attribs[i] ??= {}, st = stride || size * 4;
        if (a.buffer !== arrayBuffer || a.size !== size || a.stride !== st || a.offset !== offset) {
          a.buffer = arrayBuffer; a.size = size; a.stride = st; a.offset = offset; attribVersion++;
        }
      },
      uniform1f(l, x) { const p = up(l); if (p) p.f32[l.offset >> 2] = x; },
      uniform2f(l, x, y) { const p = up(l); if (p) { const o = l.offset >> 2; p.f32[o] = x; p.f32[o + 1] = y; } },
      uniform3f(l, x, y, z) { const p = up(l); if (p) { const o = l.offset >> 2; p.f32[o] = x; p.f32[o + 1] = y; p.f32[o + 2] = z; } },
      uniform4f(l, x, y, z, w) { const p = up(l); if (p) { const o = l.offset >> 2; p.f32[o] = x; p.f32[o + 1] = y; p.f32[o + 2] = z; p.f32[o + 3] = w; } },
      uniform1i(l, x) { const p = up(l); if (p) p.i32[l.offset >> 2] = x; },
      uniform2i(l, x, y) { const p = up(l); if (p) { const o = l.offset >> 2; p.i32[o] = x; p.i32[o + 1] = y; } },
      uniform1fv(l, v) { setUniform(l, v); }, uniform2fv(l, v) { setUniform(l, v); }, uniform3fv(l, v) { setUniform(l, v); },
      uniform4fv(l, v) { setUniform(l, v); },
      uniformMatrix4fv(l, transpose, v) { setUniform(l, v); }, uniformMatrix2fv(l, transpose, v) { setUniform(l, v); },
      uniformMatrix3fv(l, transpose, v) {
        // mat3 columns are 16 bytes apart in the uniform buffer.
        const out = []; for (let c = 0; c < 3; c++) out.push(v[3 * c], v[3 * c + 1], v[3 * c + 2], 0);
        setUniform(l, out);
      },
      drawArrays(mode, first, count) {
        const p = program;
        if (!p?.linked) { fail('drawArrays with no linked program'); return; }
        let pipeline, vbufs;
        if (p.drawVersion === attribVersion && p.drawMode === mode) { pipeline = p.drawPipeline; vbufs = p.drawVbufs; }
        else {
          const layouts = [], list = p.attrList, glMode = glModes[mode] ?? 99;
          vbufs = [];
          let key = '' + glMode;
          for (let i = 0; i < list.length; i++) {
            const location = list[i][1], a = attribs[location];
            if (!a?.enabled || !a.buffer?.gpu) { fail(`attribute ${list[i][0]} has no buffer`); return; }
            layouts.push({ stride: a.stride, format: a.size, offset: a.offset, location }); vbufs.push(a.buffer.gpu);
            key += ' ' + a.stride + ' ' + a.size + ' ' + a.offset + ' ' + location;
          }
          pipeline = pipelineFor(p, layouts, glMode, key);
          if (!pipeline) return;
          p.drawVersion = attribVersion; p.drawMode = mode; p.drawPipeline = pipeline; p.drawVbufs = vbufs;
        }
        if (p.fragHeight >= 0 && p.f32[p.fragHeight] !== ctx.drawingBufferHeight) { p.f32[p.fragHeight] = ctx.drawingBufferHeight; p.uniformDirty = true; }
        if (p.uniformBuffer && p.uniformDirty) {
          // n.gpu copies the bytes at once, so the program's own buffer is sent as it is.
          const m = n.gpu(3, p.uniformBuffer + ' 0', p.uniformData);
          if (m) fail(typeof m === 'number' ? 'gpu: import error ' + m : m);
          p.uniformDirty = false;
        }
        draws.push(pipeline.id, pipeline.bind, vbufs.length);
        for (let i = 0; i < vbufs.length; i++) draws.push(vbufs[i]);
        draws.push(+count, 1, +first, 0);
        drawCount++;
        if (!flushQueued) { flushQueued = true; Promise.resolve().then(flush); }
      },
    };
    Object.assign(ctx, GL);
    ensureCanvas();
    return ctx;
  };
  // ==== Canvas 2D (docs/designissues/2026-11-08-canvas-2d.md) ===== begin canvas2d section ====
  // Page-facing objects only. Each call is recorded as numbers (an opcode and its
  // arguments) and strings; at the end of the task, or before a call that needs an answer,
  // the whole batch goes to Lean in one `gpu_command` import (op 200; queries op 201).
  // Lean (L4Factoidal.PageCanvas) parses colours and fonts, keeps the drawing state, builds
  // paths, shapes text and rasterises every draw into the canvas bitmap. Nothing here
  // decides what is drawn: this converts arguments (WebIDL) and makes objects. Made on first
  // use, so a page with no 2D canvas pays nothing.
  let c2dMade = null;
  const c2d = () => c2dMade ??= make2d();
  // The section's code is text until a page first uses Canvas 2D: compiled then, so pages
  // without a 2D canvas carry no more JavaScript (QuickJS's collector walks every function's
  // code on each cycle). It sees the prelude only through these parameters.
  const make2d = () => new Function('n', 'define', 'named', 'nodeId', 'canvasSize', 'gpuContexts', 'DOMException', 'EventTarget',
    make2dSource)(n, define, named, nodeId, canvasSize, gpuContexts, DOMException, EventTarget);
  const make2dSource = `'use strict';
    const K = Symbol('canvas2d');
    let q = [], strs = [], strIx = new Map(), tails = [], tailLen = 0, queued = false, selected = -1;
    let nextObj = 1, nextOffscreen = 0x20000000;
    const objs = new Map(); // Lean's object ids, for the fillStyle and strokeStyle getters
    const str = s => { s = String(s); let i = strIx.get(s); if (i === undefined) { i = strs.length; strs.push(s); strIx.set(s, i); } return i; };
    const pack = (nums, ts, tl) => {
      const k = nums.length, buf = new ArrayBuffer(8 + 8 * k + tl);
      new Uint32Array(buf, 0, 2)[0] = k;
      if (k) new Float64Array(buf, 8, k).set(nums);
      if (tl) { const u8 = new Uint8Array(buf); let o = 8 + 8 * k; for (const t of ts) { u8.set(t, o); o += t.length; } }
      return buf;
    };
    const flush = () => {
      queued = false;
      if (q.length === 0) return;
      // Numbers as text (op 203) unless the batch carries bytes (op 200): filling a typed
      // array costs more than joining in BubblePopJS, and Lean reads both exactly.
      const text = tailLen === 0, payload = text ? q.join(',') : pack(q, tails, tailLen), header = JSON.stringify(strs);
      q = []; strs = []; strIx = new Map(); tails = []; tailLen = 0; selected = -1;
      const r = n.gpu(text ? 203 : 200, header, payload);
      if (typeof r === 'number') console.warn('Canvas 2D: import error ' + r);
      else if (r.charCodeAt(0) === 2) console.warn('Canvas 2D:', r.slice(1));
    };
    const later = () => { if (!queued) { queued = true; Promise.resolve().then(flush); } };
    const on = id => { if (selected !== id) { q.push(1, id); selected = id; } later(); };
    const tail = bytes => { const off = tailLen; tails.push(bytes); tailLen += bytes.length; return off; };
    const ask = (nums, ss = []) => {
      flush();
      const r = n.gpu(201, JSON.stringify(ss), pack(nums, [], 0));
      if (typeof r !== 'string') throw new DOMException('Canvas 2D: import error ' + r, 'InvalidStateError');
      if (r.charCodeAt(0) === 2) throw new DOMException(r.slice(1), 'InvalidStateError');
      return r.slice(1);
    };
    const nums = r => r === '' ? [] : r.split(' ').map(Number);
    const need = (got, k, name) => { if (got < k) throw new TypeError("Failed to execute '" + (name) + "': " + (k) + ' arguments required, but only ' + (got) + ' present.'); };
    const dbl = (x, name) => { x = +x; if (!Number.isFinite(x)) throw new TypeError("Failed to execute '" + (name) + "': the provided double value is non-finite."); return x; };
    const self = o => { const s = o?.[K]; if (!s || s.kind !== 'ctx') throw new TypeError('Illegal invocation'); return s; };
    const ruleOf = (r, name) => { if (r === undefined || r === 'nonzero') return 0; if (r === 'evenodd') return 1;
      throw new TypeError("Failed to execute '" + (name) + "': The provided value '" + (r) + "' is not a valid enum value of type CanvasFillRule."); };

    // ---- Objects ------------------------------------------------------------------------
    class CanvasGradient {
      constructor() { throw new TypeError('Illegal constructor'); }
      addColorStop(offset, color) {
        need(arguments.length, 2, 'addColorStop');
        const r = ask([9, this[K].id, dbl(offset, 'addColorStop'), 0], [String(color)]);
        if (r === 'IndexSizeError') throw new DOMException('The provided offset is outside the range [0, 1].', 'IndexSizeError');
        if (r === 'SyntaxError') throw new DOMException("The value provided ('" + (color) + "') could not be parsed as a color.", 'SyntaxError');
      }
    }
    class CanvasPattern {
      constructor() { throw new TypeError('Illegal constructor'); }
      setTransform(m = {}) { const t = matrixOf(m); q.push(92, this[K].id, ...t); later(); }
    }
    const made = (C, kind, id) => { const o = Object.create(C.prototype); define(o, K, { kind, id }); objs.set(id, o); return o; };
    class DOMMatrixReadOnly {
      constructor(init) {
        const v = init === undefined ? [1, 0, 0, 1, 0, 0] : Array.from(init, Number);
        if (v.length === 6) { [this.a, this.b, this.c, this.d, this.e, this.f] = v; this.is2D = true; }
        else if (v.length === 16) { [this.a, this.b, , , this.c, this.d, , , , , , , this.e, this.f] = v; this.is2D = false; }
        else throw new TypeError('DOMMatrix needs 6 or 16 numbers');
      }
      get m11() { return this.a; } get m12() { return this.b; } get m21() { return this.c; } get m22() { return this.d; }
      get m41() { return this.e; } get m42() { return this.f; }
      get m13() { return 0; } get m14() { return 0; } get m23() { return 0; } get m24() { return 0; } get m31() { return 0; }
      get m32() { return 0; } get m33() { return 1; } get m34() { return 0; } get m43() { return 0; } get m44() { return 1; }
      get isIdentity() { return this.a === 1 && this.b === 0 && this.c === 0 && this.d === 1 && this.e === 0 && this.f === 0; }
    }
    class DOMMatrix extends DOMMatrixReadOnly {}
    class DOMPointReadOnly {
      constructor(x = 0, y = 0, z = 0, w = 1) { this.x = +x; this.y = +y; this.z = +z; this.w = +w; }
      static fromPoint(p = {}) { return new this(p.x ?? 0, p.y ?? 0, p.z ?? 0, p.w ?? 1); }
      toJSON() { return { x: this.x, y: this.y, z: this.z, w: this.w }; }
    }
    class DOMPoint extends DOMPointReadOnly {}
    const matrixOf = m => {
      if (m === null || typeof m !== 'object') throw new TypeError('The matrix is not an object');
      const g = (x, y, d) => m[x] !== undefined ? +m[x] : m[y] !== undefined ? +m[y] : d;
      return [g('a', 'm11', 1), g('b', 'm12', 0), g('c', 'm21', 0), g('d', 'm22', 1), g('e', 'm41', 0), g('f', 'm42', 0)];
    };
    class ImageData {
      constructor(a, b, c, settings) {
        need(arguments.length, 2, 'ImageData');
        let data, w, h;
        if (a instanceof Uint8ClampedArray) {
          data = a; w = b >>> 0; const len = data.length;
          if (len === 0 || len % 4 !== 0) throw new DOMException('The input data has zero elements, or a length that is not a multiple of 4.', 'InvalidStateError');
          if (w === 0) throw new DOMException('The source width is zero or not a number.', 'IndexSizeError');
          if ((len / 4) % w !== 0) throw new DOMException('The input data length is not a multiple of (4 * width).', 'IndexSizeError');
          h = len / 4 / w;
          if (c !== undefined && (c >>> 0) !== h) throw new DOMException('The input data length is not equal to (4 * width * height).', 'IndexSizeError');
        } else {
          w = +a; h = +b;
          if (!Number.isFinite(w) || !Number.isFinite(h)) throw new TypeError('ImageData sizes must be finite');
          w = Math.trunc(w) >>> 0; h = Math.trunc(h) >>> 0;
          if (w === 0 || h === 0) throw new DOMException('The source width or height is zero.', 'IndexSizeError');
          if (w * h > 268435456) throw new RangeError('Out of memory at ImageData creation');
          data = new Uint8ClampedArray(w * h * 4);
        }
        define(this, K, { kind: 'data' });
        Object.defineProperty(this, 'data', { value: data, enumerable: true });
        Object.defineProperty(this, 'width', { value: w, enumerable: true });
        Object.defineProperty(this, 'height', { value: h, enumerable: true });
        Object.defineProperty(this, 'colorSpace', { value: 'srgb', enumerable: true });
        Object.defineProperty(this, 'pixelFormat', { value: 'rgba-unorm8', enumerable: true });
      }
    }
    class ImageBitmap {
      constructor() { throw new TypeError('Illegal constructor'); }
      get width() { return this[K].closed ? 0 : this[K].w; }
      get height() { return this[K].closed ? 0 : this[K].h; }
      close() { if (!this[K].closed) { this[K].closed = true; q.push(94, 4, this[K].id); later(); } }
    }
    class TextMetrics { constructor() { throw new TypeError('Illegal constructor'); } }
    const metricNames = ['width', 'actualBoundingBoxLeft', 'actualBoundingBoxRight', 'fontBoundingBoxAscent',
      'fontBoundingBoxDescent', 'actualBoundingBoxAscent', 'actualBoundingBoxDescent', 'emHeightAscent',
      'emHeightDescent', 'hangingBaseline', 'alphabeticBaseline', 'ideographicBaseline'];

    // An image source as Lean names it: [kind, number or string]. 1 a canvas, 2 an
    // ImageBitmap, 3 an image of the page by URL.
    const sourceOf = (img, name) => {
      if (img instanceof named.HTMLCanvasElement) { const id = nodeId(img); ensure(img, id); return [1, id]; }
      if (img instanceof OffscreenCanvas) { const s = img[K]; if (!s.ctx) blankOffscreen(img); return [1, s.id]; }
      if (img instanceof ImageBitmap) {
        if (img[K].closed) throw new DOMException('The image source is detached.', 'InvalidStateError');
        return [2, img[K].id];
      }
      if (img instanceof named.HTMLImageElement) return [3, img.src];
      throw new TypeError("Failed to execute '" + (name) + "': The provided value is not of a supported image source type.");
    };
    // A canvas element read as an image before it has a 2D context: a blank bitmap of its size in Lean.
    const ensure = (canvas, id) => {
      const held = gpuContexts.get(id);
      if (!held) { q.push(2, id, canvasSize(canvas, 'width', 300), canvasSize(canvas, 'height', 150), 0); selected = id; later(); gpuContexts.set(id, { kind: 'blank' }); }
    };
    const blankOffscreen = oc => { const s = oc[K]; q.push(2, s.id, s.w, s.h, 0); selected = s.id; later(); };

    // ---- The context --------------------------------------------------------------------
    class CanvasRenderingContext2D { constructor() { throw new TypeError('Illegal constructor'); } }
    const P = CanvasRenderingContext2D.prototype;
    const attrs = { globalAlpha: [20, 'n'], globalCompositeOperation: [21, 's'], lineWidth: [26, 'n'], lineCap: [27, 's'],
      lineJoin: [28, 's'], miterLimit: [29, 'n'], lineDashOffset: [31, 'n'], shadowColor: [32, 's'], shadowBlur: [33, 'n'],
      shadowOffsetX: [34, 'n'], shadowOffsetY: [35, 'n'], font: [36, 's'], textAlign: [37, 's'], textBaseline: [38, 's'],
      direction: [39, 's'], imageSmoothingEnabled: [40, 'b'], imageSmoothingQuality: [41, 's'], filter: [42, 's'],
      letterSpacing: [43, 's'], wordSpacing: [44, 's'], fontKerning: [45, 's'], fontStretch: [46, 's'],
      fontVariantCaps: [47, 's'], textRendering: [48, 's'], lang: [49, 's'] };
    for (const [name, [op, t]] of Object.entries(attrs)) {
      Object.defineProperty(P, name, { configurable: true, enumerable: true,
        get() { const s = self(this); const r = ask([1, s.id, 0], [name]); return t === 'n' ? Number(r) : t === 'b' ? r === '1' : r; },
        set(v) {
          const s = this?.[K];
          if (s === undefined || s.kind !== 'ctx') throw new TypeError('Illegal invocation');
          if (selected !== s.id) { q.push(1, s.id); selected = s.id; }
          if (!queued) { queued = true; Promise.resolve().then(flush); }
          q.push(op, t === 'n' ? +v : t === 'b' ? (v ? 1 : 0) : str(v));
        } });
    }
    for (const [name, ops] of [['fillStyle', [22, 24]], ['strokeStyle', [23, 25]]]) {
      Object.defineProperty(P, name, { configurable: true, enumerable: true,
        get() { const s = self(this); const r = ask([1, s.id, 0], [name]);
          return r.charCodeAt(0) === 1 ? objs.get(Number(r.slice(2))) ?? null : r; },
        set(v) {
          const s = this?.[K];
          if (s === undefined || s.kind !== 'ctx') throw new TypeError('Illegal invocation');
          if (selected !== s.id) { q.push(1, s.id); selected = s.id; }
          if (!queued) { queued = true; Promise.resolve().then(flush); }
          if (typeof v === 'string') q.push(ops[0], str(v));
          else if (v instanceof CanvasGradient) q.push(ops[1], 1, v[K].id);
          else if (v instanceof CanvasPattern) q.push(ops[1], 2, v[K].id);
          else q.push(ops[0], str(v));
        } });
    }
    // The calls a frame makes most are written out (no helper calls): BubblePopJS pays for each call.
    const simple = { save: [3, 0], restore: [4, 0], reset: [5, 0], resetTransform: [15, 0], beginPath: [51, 0],
      scale: [13, 2], rotate: [14, 1], translate: [12, 2], transform: [11, 6] };
    for (const [name, [op, k]] of Object.entries(simple))
      define(P, name, function (a, b, c, d, e, f) {
        const s = self(this); need(arguments.length, k, name); on(s.id);
        if (k === 0) q.push(op); else if (k === 1) q.push(op, +a); else if (k === 2) q.push(op, +a, +b);
        else q.push(op, +a, +b, +c, +d, +e, +f);
      });
    const rectOp = (op, name) => function (x, y, w, h) {
      const s = this?.[K];
      if (s === undefined || s.kind !== 'ctx') throw new TypeError('Illegal invocation');
      if (arguments.length < 4) need(arguments.length, 4, name);
      if (selected !== s.id) { q.push(1, s.id); selected = s.id; }
      if (!queued) { queued = true; Promise.resolve().then(flush); }
      q.push(op, +x, +y, +w, +h);
    };
    define(P, 'fillRect', rectOp(73, 'fillRect'));
    define(P, 'strokeRect', rectOp(74, 'strokeRect'));
    define(P, 'clearRect', rectOp(75, 'clearRect'));
    // CanvasPath: the context's path (target 0) or a Path2D's (target its id).
    const pathOps = { moveTo: [52, 2], lineTo: [53, 2], quadraticCurveTo: [54, 4], bezierCurveTo: [55, 6], rect: [59, 4], closePath: [61, 0] };
    const pathMethods = (proto, start, end) => {
      for (const [name, [op, k]] of Object.entries(pathOps))
        define(proto, name, function (...a) {
          need(a.length, k, name); start(this); q.push(op); for (let i = 0; i < k; i++) q.push(+a[i]); end(this);
        });
      define(proto, 'arc', function (x, y, r, a0, a1, ccw = false) {
        need(arguments.length, 5, 'arc');
        if (+r < 0) throw new DOMException('The radius provided (' + (r) + ') is negative.', 'IndexSizeError');
        start(this); q.push(56, +x, +y, +r, +a0, +a1, ccw ? 1 : 0); end(this);
      });
      define(proto, 'arcTo', function (x1, y1, x2, y2, r) {
        need(arguments.length, 5, 'arcTo');
        if (+r < 0) throw new DOMException('The radius provided (' + (r) + ') is negative.', 'IndexSizeError');
        start(this); q.push(57, +x1, +y1, +x2, +y2, +r); end(this);
      });
      define(proto, 'ellipse', function (x, y, rx, ry, rot, a0, a1, ccw = false) {
        need(arguments.length, 7, 'ellipse');
        if (+rx < 0 || +ry < 0) throw new DOMException('The major-axis or minor-axis radius provided is negative.', 'IndexSizeError');
        start(this); q.push(58, +x, +y, +rx, +ry, +rot, +a0, +a1, ccw ? 1 : 0); end(this);
      });
      // roundRect radii (WebIDL conversion and the list of 1 to 4 radii, HTML §4.12.5.1.9).
      define(proto, 'roundRect', function (x, y, w, h, radii = 0) {
        need(arguments.length, 4, 'roundRect');
        const list = (typeof radii === 'object' && radii !== null && typeof radii[Symbol.iterator] === 'function') ? [...radii] : [radii];
        if (list.length < 1 || list.length > 4) throw new RangeError((list.length) + ' radii provided. Between one and four radii are necessary.');
        const pts = list.map(r => (typeof r === 'object' && r !== null) ? [+(r.x ?? 0), +(r.y ?? 0)] : [+r, +r]);
        if (![x, y, w, h].every(v => Number.isFinite(+v)) || pts.some(p => !Number.isFinite(p[0]) || !Number.isFinite(p[1]))) return;
        if (pts.some(p => p[0] < 0 || p[1] < 0)) throw new RangeError('A radius provided is negative.');
        const [tl, tr, br, bl] = pts.length === 1 ? [pts[0], pts[0], pts[0], pts[0]] : pts.length === 2 ? [pts[0], pts[1], pts[0], pts[1]]
          : pts.length === 3 ? [pts[0], pts[1], pts[2], pts[1]] : pts;
        start(this); q.push(60, +x, +y, +w, +h, 4, ...tl, ...tr, ...br, ...bl); end(this);
      });
    };
    pathMethods(P, c => on(self(c).id), () => {});
    // moveTo and lineTo, written out for the same reason.
    for (const [name, op] of [['moveTo', 52], ['lineTo', 53]])
      define(P, name, function (x, y) {
        const s = this?.[K];
        if (s === undefined || s.kind !== 'ctx') throw new TypeError('Illegal invocation');
        if (arguments.length < 2) need(arguments.length, 2, name);
        if (selected !== s.id) { q.push(1, s.id); selected = s.id; }
        if (!queued) { queued = true; Promise.resolve().then(flush); }
        q.push(op, +x, +y);
      });
    const pathId = (p, name) => { if (!(p instanceof Path2D)) throw new TypeError("Failed to execute '" + (name) + "': parameter 1 is not of type 'Path2D'."); return p[K].id; };
    const drawPath = (op, hasRule) => function (a, b) {
      const s = self(this); let path = 0, rule = a;
      if (a instanceof Path2D) { path = a[K].id; rule = b; } else if (typeof a === 'object' && a !== null) pathId(a, 'fill');
      const r = hasRule ? ruleOf(rule, 'fill') : 0;
      on(s.id); if (hasRule) q.push(op, path, r); else q.push(op, path);
    };
    define(P, 'fill', drawPath(70, true));
    define(P, 'stroke', drawPath(71, false));
    define(P, 'clip', drawPath(72, true));
    define(P, 'isPointInPath', function (...a) {
      const s = self(this); let path = 0;
      if (a[0] instanceof Path2D) { path = a[0][K].id; a = a.slice(1); }
      need(a.length, 2, 'isPointInPath');
      return ask([4, s.id, path, +a[0], +a[1], ruleOf(a[2], 'isPointInPath')]) === '1';
    });
    define(P, 'isPointInStroke', function (...a) {
      const s = self(this); let path = 0;
      if (a[0] instanceof Path2D) { path = a[0][K].id; a = a.slice(1); }
      need(a.length, 2, 'isPointInStroke');
      return ask([5, s.id, path, +a[0], +a[1]]) === '1';
    });
    define(P, 'setTransform', function (...a) {
      const s = self(this);
      const m = a.length === 0 ? [1, 0, 0, 1, 0, 0] : a.length === 1 ? matrixOf(a[0]) : (need(a.length, 6, 'setTransform'), a.slice(0, 6).map(Number));
      on(s.id); q.push(10, ...m);
    });
    define(P, 'getTransform', function () { const s = self(this); return new DOMMatrix(nums(ask([6, s.id]))); });
    define(P, 'setLineDash', function (segments) {
      const s = self(this); need(arguments.length, 1, 'setLineDash');
      const v = Array.from(segments, Number); on(s.id); q.push(30, v.length, ...v);
    });
    define(P, 'getLineDash', function () { return nums(ask([8, self(this).id])); });
    const text = op => function (t, x, y, maxWidth) {
      const s = self(this); need(arguments.length, 3, op === 76 ? 'fillText' : 'strokeText'); on(s.id);
      q.push(op, str(t), +x, +y, maxWidth === undefined ? NaN : +maxWidth);
    };
    define(P, 'fillText', text(76));
    define(P, 'strokeText', text(77));
    define(P, 'measureText', function (t) {
      const s = self(this); need(arguments.length, 1, 'measureText');
      const v = nums(ask([3, s.id, 0], [String(t)]));
      const m = Object.create(TextMetrics.prototype);
      metricNames.forEach((k, i) => Object.defineProperty(m, k, { value: v[i] ?? 0, enumerable: true }));
      return m;
    });
    define(P, 'drawImage', function (img, ...a) {
      const s = self(this);
      if (a.length !== 2 && a.length !== 4 && a.length !== 8) throw new TypeError("Failed to execute 'drawImage': Valid arities are: [3, 5, 9], but " + (a.length + 1) + ' arguments provided.');
      const [kind, src] = sourceOf(img, 'drawImage');
      if (kind === 3 && src === '') return;
      const v = a.map(Number);
      const r = a.length === 2 ? [NaN, NaN, NaN, NaN, v[0], v[1], NaN, NaN] : a.length === 4 ? [NaN, NaN, NaN, NaN, ...v] : v;
      on(s.id); q.push(80, kind, kind === 3 ? str(src) : src, ...r);
    });
    define(P, 'createImageData', function (a, b) {
      self(this); need(arguments.length, 1, 'createImageData');
      if (a instanceof ImageData) return new ImageData(a.width, a.height);
      need(arguments.length, 2, 'createImageData');
      let w = Math.trunc(+a), h = Math.trunc(+b);
      if (!Number.isFinite(+a) || !Number.isFinite(+b)) throw new TypeError('createImageData sizes must be finite');
      if (w === 0 || h === 0) throw new DOMException('The source width or height is 0.', 'IndexSizeError');
      return new ImageData(Math.abs(w), Math.abs(h));
    });
    define(P, 'getImageData', function (sx, sy, sw, sh) {
      const s = self(this); need(arguments.length, 4, 'getImageData');
      if (![sx, sy, sw, sh].every(v => Number.isFinite(+v))) throw new TypeError("Failed to execute 'getImageData': The provided value is non-finite.");
      sx = Math.trunc(+sx); sy = Math.trunc(+sy); sw = Math.trunc(+sw); sh = Math.trunc(+sh);
      if (sw === 0 || sh === 0) throw new DOMException('The source ' + (sw === 0 ? 'width' : 'height') + ' is 0.', 'IndexSizeError');
      if (sw < 0) { sx += sw; sw = -sw; }
      if (sh < 0) { sy += sh; sh = -sh; }
      const img = new ImageData(sw, sh);
      flush();
      // The pixels as bytes (op 202, an ArrayBuffer), copied into the data at once.
      const bytes = n.gpuBytes(202, '[]', pack([2, s.id, sx, sy, sw, sh], [], 0));
      if (!(bytes instanceof ArrayBuffer)) throw new DOMException('Canvas 2D: getImageData failed', 'InvalidStateError');
      img.data.set(new Uint8Array(bytes));
      return img;
    });
    define(P, 'putImageData', function (img, dx, dy, x, y, w, h) {
      const s = self(this);
      if (arguments.length !== 3 && arguments.length !== 7) need(arguments.length, arguments.length < 3 ? 3 : 7, 'putImageData');
      if (!(img instanceof ImageData)) throw new TypeError("Failed to execute 'putImageData': parameter 1 is not of type 'ImageData'.");
      const all = arguments.length === 3, v = all ? [dx, dy, 0, 0, img.width, img.height] : [dx, dy, x, y, w, h];
      if (!v.every(t => Number.isFinite(+t))) return;
      const bytes = new Uint8Array(img.data.length); bytes.set(img.data);
      on(s.id); q.push(81, tail(bytes), img.width, img.height, ...v.map(t => Math.trunc(+t)));
    });
    const gradient = (kind, args, name, k) => {
      need(args.length, k, name);
      const v = Array.from(args).slice(0, k).map(x => dbl(x, name));
      if (kind === 2 && (v[2] < 0 || v[5] < 0)) throw new DOMException('The ' + (v[2] < 0 ? 'r0' : 'r1') + ' provided is less than 0.', 'IndexSizeError');
      const id = nextObj++; q.push(90, id, kind, ...v, ...Array(6 - k).fill(0)); later();
      return made(CanvasGradient, 'gradient', id);
    };
    define(P, 'createLinearGradient', function () { self(this); return gradient(1, arguments, 'createLinearGradient', 4); });
    define(P, 'createRadialGradient', function () { self(this); return gradient(2, arguments, 'createRadialGradient', 6); });
    define(P, 'createConicGradient', function () { self(this); return gradient(3, arguments, 'createConicGradient', 3); });
    define(P, 'createPattern', function (img, repetition) {
      self(this); need(arguments.length, 2, 'createPattern');
      const [kind, src] = sourceOf(img, 'createPattern');
      const id = nextObj++, rep = repetition === null ? '' : String(repetition);
      const r = ask([10, id, kind, kind === 3 ? 0 : src, kind === 3 ? 1 : 0], kind === 3 ? [src, rep] : [rep]);
      if (r === 'SyntaxError') throw new DOMException("The provided type ('" + (rep) + "') is not one of 'repeat', 'no-repeat', 'repeat-x', or 'repeat-y'.", 'SyntaxError');
      if (r === 'InvalidStateError') throw new DOMException('The image argument is a canvas element with a width or height of 0.', 'InvalidStateError');
      return r === 'null' ? null : made(CanvasPattern, 'pattern', id);
    });
    Object.defineProperty(P, 'canvas', { get() { return self(this).canvas; }, configurable: true, enumerable: true });
    define(P, 'getContextAttributes', function () { self(this); return { alpha: true, colorSpace: 'srgb', desynchronized: false, willReadFrequently: false }; });
    define(P, 'isContextLost', function () { self(this); return false; });
    define(P, 'drawFocusIfNeeded', function () { self(this); });

    class Path2D {
      constructor(path) {
        const id = nextObj++;
        define(this, K, { kind: 'path', id });
        if (path instanceof Path2D) q.push(62, id, path[K].id);
        else if (path !== undefined) q.push(63, id, str(path));
        else q.push(62, id, 0);
        later();
      }
      addPath(path, transform = {}) {
        need(arguments.length, 1, 'addPath'); const src = pathId(path, 'addPath');
        q.push(64, this[K].id, src, ...matrixOf(transform)); later();
      }
    }
    pathMethods(Path2D.prototype, p => q.push(50, p[K].id), () => { q.push(50, 0); later(); });

    class OffscreenCanvasRenderingContext2D { constructor() { throw new TypeError('Illegal constructor'); } }
    for (const k of Reflect.ownKeys(P)) if (k !== 'constructor') Object.defineProperty(OffscreenCanvasRenderingContext2D.prototype, k, Object.getOwnPropertyDescriptor(P, k));
    const contextFor = (C, canvas, id, w, h, element) => {
      const ctx = Object.create(C.prototype);
      define(ctx, K, { kind: 'ctx', id, canvas });
      q.push(2, id, w, h, element ? 1 : 0); selected = id; later();
      return ctx;
    };
    class OffscreenCanvas extends EventTarget {
      constructor(w, h) {
        super(); need(arguments.length, 2, 'OffscreenCanvas');
        define(this, K, { id: nextOffscreen++, w: Math.trunc(+w) >>> 0, h: Math.trunc(+h) >>> 0, ctx: null, kind: null });
      }
      get width() { return this[K].w; }
      set width(v) { const s = this[K]; s.w = Math.trunc(+v) >>> 0; if (s.ctx) { q.push(2, s.id, s.w, s.h, 0); selected = s.id; later(); } }
      get height() { return this[K].h; }
      set height(v) { const s = this[K]; s.h = Math.trunc(+v) >>> 0; if (s.ctx) { q.push(2, s.id, s.w, s.h, 0); selected = s.id; later(); } }
      getContext(kind) {
        need(arguments.length, 1, 'getContext');
        const s = this[K]; kind = String(kind);
        if (!['2d', 'webgl', 'webgl2', 'webgpu', 'bitmaprenderer'].includes(kind)) throw new TypeError("The provided value '" + (kind) + "' is not a valid enum value of type OffscreenRenderingContextType.");
        if (s.kind) return s.kind === kind ? s.ctx : null;
        if (kind !== '2d') return null;
        s.kind = kind; s.ctx = contextFor(OffscreenCanvasRenderingContext2D, this, s.id, s.w, s.h, false);
        return s.ctx;
      }
      transferToImageBitmap() {
        const s = this[K];
        if (!s.ctx) blankOffscreen(this);
        const b = bitmapOf(1, s.id, NaN, NaN, NaN, NaN, s.w, s.h);
        q.push(2, s.id, s.w, s.h, 0); selected = s.id; later();
        return b;
      }
    }
    const bitmapOf = (kind, src, sx, sy, sw, sh, w, h) => {
      const id = nextObj++;
      q.push(93, id, kind, src, sx, sy, sw, sh, w, h); later();
      const b = Object.create(ImageBitmap.prototype); define(b, K, { id, w, h, closed: false });
      return b;
    };
    const createImageBitmap = (img, ...a) => new Promise((resolve, reject) => {
      try {
        let sx = NaN, sy = NaN, sw = NaN, sh = NaN;
        if (a.length >= 4) {
          [sx, sy, sw, sh] = a.slice(0, 4).map(Number);
          if (sw === 0 || sh === 0) throw new RangeError('The crop rect width or height is 0.');
          if (sw < 0) { sx += sw; sw = -sw; }
          if (sh < 0) { sy += sh; sh = -sh; }
        }
        if (img instanceof ImageData) {
          const bytes = new Uint8Array(img.data.length); bytes.set(img.data);
          resolve(bitmapOf(4, tail(bytes), 0, 0, img.width, img.height, img.width, img.height));
          return;
        }
        const [kind, src] = sourceOf(img, 'createImageBitmap');
        const size = nums(ask([11, kind, kind === 3 ? 0 : src], kind === 3 ? [src] : []));
        if (size.length < 2) throw new DOMException('The source image could not be decoded.', 'InvalidStateError');
        resolve(bitmapOf(kind, kind === 3 ? str(src) : src, sx, sy, sw, sh, Number.isNaN(sw) ? size[0] : sw, Number.isNaN(sh) ? size[1] : sh));
      } catch (e) { reject(e); }
    });
    return { CanvasRenderingContext2D, OffscreenCanvasRenderingContext2D, OffscreenCanvas, Path2D, ImageData,
      ImageBitmap, CanvasGradient, CanvasPattern, TextMetrics, DOMMatrix, DOMMatrixReadOnly, DOMPoint, DOMPointReadOnly, createImageBitmap,
      context: canvas => contextFor(CanvasRenderingContext2D, canvas, nodeId(canvas), canvasSize(canvas, 'width', 300), canvasSize(canvas, 'height', 150), true),
      resized: canvas => { const id = nodeId(canvas); q.push(2, id, canvasSize(canvas, 'width', 300), canvasSize(canvas, 'height', 150), 1); selected = id; later(); },
      dataURL: (canvas, type) => { const id = nodeId(canvas); ensure(canvas, id); return ask([7, id, 0], [type === undefined ? 'image/png' : String(type)]); } };
`;
  // ==== end canvas2d section ====
  // A 2D canvas whose width or height is set starts again (HTML §4.12.5: the bitmap and the context's state are reset).
  const sized = (el, name, v) => { el.setAttribute(name, String(v >>> 0)); if (gpuContexts.get(nodeId(el))?.kind === '2d') c2d().resized(el); };
  Object.defineProperties(named.HTMLCanvasElement.prototype, {
    width: { get() { return canvasSize(this, 'width', 300); }, set(v) { sized(this, 'width', v); }, configurable: true },
    height: { get() { return canvasSize(this, 'height', 150); }, set(v) { sized(this, 'height', v); }, configurable: true },
    toDataURL: { value(type) { return c2d().dataURL(this, type); }, writable: true, configurable: true },
    getContext: { value(kind) {
      // One context kind per canvas, as in HTML.
      const id = nodeId(this), held = gpuContexts.get(id);
      if (held && held.kind !== 'blank') return held.kind === kind ? held.context : null;
      let context = null;
      if (kind === '2d') context = c2d().context(this);
      else if (kind === 'webgpu') context = new GPUCanvasContext(this);
      else if (kind === 'webgl2') context = glContextFor(this, 2);
      else if (kind === 'webgl' || kind === 'experimental-webgl') context = glContextFor(this, 1);
      if (context) gpuContexts.set(id, { kind, context });
      return context;
    }, writable: true, configurable: true },
  });
  for (const t of ['address', 'article', 'aside', 'footer', 'header', 'hgroup', 'main', 'nav', 'section', 'b', 'i', 'em', 'strong',
    'small', 'code', 'abbr', 'cite', 'dfn', 'kbd', 'mark', 's', 'samp', 'sub', 'sup', 'u', 'var', 'bdi', 'bdo', 'dd', 'dt',
    'figcaption', 'figure', 'noscript', 'ruby', 'rt', 'rp', 'summary', 'wbr', 'center', 'tt', 'big', 'nobr', 'acronym',
    'basefont', 'noframes', 'noembed', 'plaintext', 'search', 'strike']) htmlClasses[t] = HTMLElement;
  for (const t of ['listing', 'xmp']) htmlClasses[t] = named.HTMLPreElement;
  class SVGElement extends Element {
    // SVG 2 §8.10 getBBox: the bounds of the element's geometry in its own user space.
    getBBox() { const b = query(nodeId(this), 18, 4); return new DOMRect(b[0], b[1], b[2], b[3]); }
  }
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
    get publicId() { return str(nodeId(this), 7) ?? ''; }
    get systemId() { return str(nodeId(this), 8) ?? ''; }
  }
  class DocumentFragment extends Node {
    constructor() { return wrap(chk(n.create(2, ''))); }
    getElementById(id) { id = String(id); if (id === '') return null; const k = chk(n.query(nodeId(this), 5, id)); return k === null ? null : wrap(Number(k)); }
  }
  let readyState = 'loading';
  class Document extends Node {
    constructor() { return wrap(chk(n.create(8, ''))); }
    get URL() { return this === document ? location.href : 'about:blank'; }
    get documentURI() { return this.URL; }
    get compatMode() { return 'CSS1Compat'; }
    get characterSet() { return this === document ? docEncoding() : 'UTF-8'; }
    get charset() { return this.characterSet; }
    get inputEncoding() { return 'UTF-8'; }
    get contentType() { return str(nodeId(this), 9); }
    get readyState() { return readyState; }
    get defaultView() { return this === document ? window : (info(nodeId(this), 12) >= 0 ? frameWindow(nodeId(this)) : null); }
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
    getElementById(id) { id = String(id); if (id === '') return null; const k = chk(n.query(nodeId(this), 5, id)); return k === null ? null : wrap(Number(k)); }
    getElementsByName(name) { return staticList(elementsOf(nodeId(this)).filter(k => n.attr(k, 'name') === String(name)).map(wrap)); }
    // Each node is made in this document: kind + 16 × its node number (Hosts.Dom.createKind).
    createElement(name, options) { return wrap(chk(n.create(3 + 16 * nodeId(this), String(name)))); }
    createElementNS(ns, qname) {
      if (arguments.length < 2) throw new TypeError('createElementNS: 2 arguments required');
      return wrap(chk(n.create(4 + 16 * nodeId(this), nsArg(ns) + '\u0000' + String(qname))));
    }
    createAttribute(name) {
      if (arguments.length < 1) throw new TypeError('createAttribute: 1 argument required');
      name = String(name); chk(n.query(0, 3, name));
      if (info(nodeId(this), 10) === 1) name = name.replace(/[A-Z]/g, c => c.toLowerCase());
      return newAttr({ el: null, ns: null, pfx: null, lname: name, value: '', doc: nodeId(this) });
    }
    createAttributeNS(ns, qname) {
      if (arguments.length < 2) throw new TypeError('createAttributeNS: 2 arguments required');
      const [ns2, pfx, lname] = chk(n.query(0, 4, nsArg(ns) + '\u0000' + String(qname))).split('\u0000');
      return newAttr({ el: null, ns: ns2 || null, pfx: pfx || null, lname, value: '', doc: nodeId(this) });
    }
    createTextNode(data) { return wrap(chk(n.create(0 + 16 * nodeId(this), String(data)))); }
    createComment(data) { return wrap(chk(n.create(1 + 16 * nodeId(this), String(data)))); }
    createDocumentFragment() { return wrap(chk(n.create(2 + 16 * nodeId(this), ''))); }
    createProcessingInstruction(target, data) { return wrap(chk(n.create(5 + 16 * nodeId(this), String(target) + '\u0000' + String(data)))); }
    createCDATASection(data) { return wrap(chk(n.create(6 + 16 * nodeId(this), String(data)))); }
    createEvent(name) {
      const map = { event: Event, events: Event, htmlevents: Event, customevent: CustomEvent, mouseevent: MouseEvent,
        mouseevents: MouseEvent, uievent: UIEvent, uievents: UIEvent, keyboardevent: KeyboardEvent, focusevent: FocusEvent,
        svgevents: Event, messageevent: MessageEvent, hashchangeevent: HashChangeEvent, storageevent: StorageEvent,
        beforeunloadevent: BeforeUnloadEvent, compositionevent: CompositionEvent, devicemotionevent: DeviceMotionEvent,
        deviceorientationevent: DeviceOrientationEvent, dragevent: DragEvent, textevent: TextEvent };
      const C = Object.prototype.hasOwnProperty.call(map, String(name).toLowerCase()) ? map[String(name).toLowerCase()] : undefined;
      if (!C) throw new DOMException('The provided event type is not supported.', 'NotSupportedError');
      legacyMaking = true;
      let e; try { e = new C(''); } finally { legacyMaking = false; }
      state(e).initialized = false;
      return e;
    }
    // DOM §4.5: importNode clones into this document; adoptNode moves a node here (Lean's
    // Dom.cloneNode with a document, Dom.adopt).
    importNode(node, options = false) {
      const deep = typeof options === 'object' && options !== null ? !options.selfOnly : !!options;
      if (node instanceof Attr) { const c = node.cloneNode(); attrState.get(c).doc = nodeId(this); return c; }
      const c = chk(n.treeOp(nodeId(node), nodeId(this), deep ? 5 : 4)); scanHandlers(c, true); return wrap(c);
    }
    adoptNode(node) {
      if (node instanceof Attr) { const a = attrState.get(node); if (a.el) node.ownerElement.removeAttributeNode(node); a.doc = nodeId(this); return node; }
      const id = nodeId(node);
      if (info(id, 0) === 9) throw new DOMException('A document can not be adopted.', 'NotSupportedError');
      if (info(id, 0) !== 11 && info(id, 1) >= 0) node.parentNode.removeChild(node);
      chk(n.treeOp(id, nodeId(this), 3)); return node;
    }
    elementFromPoint() { return null; }
    get implementation() { let i = implementations.get(this); if (!i) { i = Object.create(DOMImplementation.prototype); implDoc.set(i, nodeId(this)); implementations.set(this, i); } return i; }
  }
  // DOMImplementation (DOM §4.5.1): documents and doctypes made in the arena by Lean.
  const implementations = new WeakMap(), implDoc = new WeakMap();
  class DOMImplementation {
    constructor() { throw new TypeError('Illegal constructor'); }
    createHTMLDocument(title) { return wrap(chk(n.create(title === undefined ? 10 : 7, title === undefined ? '' : String(title)))); }
    createDocument(ns, qname, doctype = null) {
      if (arguments.length < 2) throw new TypeError('createDocument: 2 arguments required');
      if (doctype !== null && doctype !== undefined && !(doctype instanceof DocumentType)) throw new TypeError("parameter 3 is not of type 'DocumentType'");
      qname = qname === null ? '' : String(qname);
      const d = wrap(chk(n.create(8, nsArg(ns))));
      const el = qname === '' ? null : d.createElementNS(ns, qname);
      if (doctype) d.appendChild(doctype);
      if (el) d.appendChild(el);
      return d;
    }
    createDocumentType(name, publicId, systemId) {
      return wrap(chk(n.create(9 + 16 * implDoc.get(this), String(name) + '\u0000' + String(publicId) + '\u0000' + String(systemId))));
    }
    hasFeature() { return true; }
  }
  // DOMParser (HTML §8.5.1): the document is parsed by Lean (Hosts.Dom.createKind 11, 12).
  const xmlTypes = ['text/xml', 'application/xml', 'application/xhtml+xml', 'image/svg+xml'];
  class DOMParser {
    parseFromString(source, type) {
      if (arguments.length < 2) throw new TypeError('parseFromString: 2 arguments required');
      source = String(source); type = String(type);
      if (type === 'text/html') return wrap(chk(n.create(11, source)));
      if (xmlTypes.includes(type)) return wrap(chk(n.create(12, type + '\u0000' + source)));
      throw new TypeError(`'${type}' is not a valid value for DOMParserSupportedType`);
    }
  }
  class HTMLDocument extends Document {}
  class XMLDocument extends Document {}
  mix(Element, parentNode); mix(Document, parentNode); mix(DocumentFragment, parentNode);
  mix(Element, childNode); mix(CharacterData, childNode, ['remove', 'before', 'after', 'replaceWith', 'previousElementSibling', 'nextElementSibling']);
  mix(DocumentType, childNode, ['remove', 'before', 'after', 'replaceWith']);
  // [Unscopable] (DOM §4.2.6, §4.2.8).
  const unscopable = (C, names) => {
    const u = Object.assign(Object.create(null), C.prototype[Symbol.unscopables] ?? {});
    for (const k of names) u[k] = true;
    Object.defineProperty(C.prototype, Symbol.unscopables, { value: u, configurable: true });
  };
  for (const C of [Element, Document, DocumentFragment]) unscopable(C, ['prepend', 'append', 'replaceChildren']);
  for (const C of [Element, CharacterData, DocumentType]) unscopable(C, ['before', 'after', 'replaceWith', 'remove']);
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
      case 9: return info(id, 10) === 1 ? HTMLDocument.prototype : XMLDocument.prototype;
      case 10: return DocumentType.prototype;
      case 11: return DocumentFragment.prototype;
      default: return Node.prototype;
    }
  };
  const docBody = () => { const b = document.body; return b ? nodeId(b) : -1; };
  const docElement = () => kids(0).find(k => info(k, 0) === 1) ?? -1;

  // ---- selectors: Lean's (DOM.Selectors, node_query 6-9); a SyntaxError is -12 ------------
  const selectorQuery = (id, op, sel) => {
    sel = String(sel);
    const r = n.query(id, op, sel);
    if (r === -12) throw new DOMException(`'${sel}' is not a valid selector`, 'SyntaxError');
    return chk(r);
  };
  const select = (root, sel, first) => {
    const r = selectorQuery(nodeId(root), first ? 7 : 6, sel);
    return r === null || r === '' ? [] : r.split(' ').map(k => wrap(Number(k)));
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
  let nextObserver = 0;
  const withTransients = new Set();
  // DOM §4.2.3 "remove" step 15: each subtree registration on an inclusive ancestor of the
  // parent also watches the removed node, until the observer is next notified.
  const addTransients = (parent, removed) => {
    if (!observed.size) return;
    for (let k = parent; k >= 0; k = info(k, 1)) {
      for (const r of observed.get(k) ?? []) {
        if (!r.options.subtree) continue;
        for (const node of removed) {
          const list = observed.get(node) ?? [];
          list.push({ observer: r.observer, options: r.options, source: r });
          observed.set(node, list); observerState.get(r.observer).nodes.add(node); withTransients.add(r.observer); scheduleNotify();
        }
      }
    }
  };
  class MutationRecord { constructor() { throw new TypeError('Illegal constructor'); } }
  const record = (fields) => {
    const r = Object.create(MutationRecord.prototype);
    for (const [k, v] of Object.entries({ type: '', target: null, addedNodes: staticList([]), removedNodes: staticList([]),
      previousSibling: null, nextSibling: null, attributeName: null, attributeNamespace: null, oldValue: null, ...fields }))
      Object.defineProperty(r, k, { value: v, enumerable: true });
    return r;
  };
  // Queue a mutation observer microtask (DOM §4.3.1), once.
  const scheduleNotify = () => {
    if (notifyQueued) return;
    notifyQueued = true;
    Promise.resolve().then(() => {
      notifyQueued = false;
      // DOM §4.3.2 "notify mutation observers": in the order the observers were made; the
      // transient registrations of each go before its callback runs.
      const list = [...new Set([...pendingObservers, ...withTransients])].sort((a, b) => observerState.get(a).order - observerState.get(b).order);
      pendingObservers = []; withTransients.clear();
      for (const o of list) {
        const st = observerState.get(o), rs = st.records; st.records = [];
        for (const k of st.nodes) { const l = observed.get(k); if (l && l.some(x => x.source && x.observer === o)) { const kept = l.filter(x => !(x.source && x.observer === o)); if (kept.length) observed.set(k, kept); else observed.delete(k); } }
        if (rs.length) try { st.callback.call(o, rs, o); } catch (e) { report(e); }
      }
    });
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
    if (interested.size) scheduleNotify();
  };
  const nodes = ids => staticList(ids.map(wrap));
  const childList = (parent, added, removed, prev, next) => {
    if (removed.length) addTransients(parent, removed);
    if (added.length || removed.length)
      queueRecord('childList', parent, { addedNodes: nodes(added), removedNodes: nodes(removed), previousSibling: wrap(prev), nextSibling: wrap(next) });
  };
  const attrName = (id, name) => info(id, 8) === 1 ? name.toLowerCase() : name;
  // A namespaced name is "namespace U+0000 qualified name" (set) or "namespace U+0000 local
  // name" (remove): the record names the local name and the namespace.
  const recordName = (id, name) => {
    const i = name.indexOf('\u0000');
    if (i < 0) return { key: name, attributeName: attrName(id, name), attributeNamespace: null };
    const ns = name.slice(0, i), q = name.slice(i + 1), c = q.indexOf(':'), l = c < 0 ? q : q.slice(c + 1);
    return { key: ns + '\u0000' + l, attributeName: l, attributeNamespace: ns === '' ? null : ns };
  };
  n.setAttr = (id, name, value) => {
    if (!observed.size) return n0.setAttr(id, name, value);
    const rn = recordName(id, name), old = n0.attr(id, rn.key), r = n0.setAttr(id, name, value);
    if (r === 0) queueRecord('attributes', id, { attributeName: rn.attributeName, attributeNamespace: rn.attributeNamespace, oldValue: typeof old === 'string' ? old : null }, rn.attributeName);
    return r;
  };
  n.removeAttr = (id, name) => {
    if (!observed.size) return n0.removeAttr(id, name);
    const rn = recordName(id, name), old = n0.attr(id, rn.key), r = n0.removeAttr(id, name);
    if (r === 0 && typeof old === 'string') queueRecord('attributes', id, { attributeName: rn.attributeName, attributeNamespace: rn.attributeNamespace, oldValue: old }, rn.attributeName);
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
      observerState.set(this, { callback, records: [], nodes: new Set(), order: nextObserver++ });
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
      const existing = list.find(x => x.observer === this && !x.source);
      if (existing) {
        // DOM §4.3.3 observe() step 7.1: the transient registrations made from this one go.
        for (const k of observerState.get(this).nodes) { const l = observed.get(k); if (l) { const kept = l.filter(x => x.source !== existing); if (kept.length) observed.set(k, kept); else observed.delete(k); } }
        existing.options = options;
      } else list.push({ observer: this, options });
      observed.set(id, list); observerState.get(this).nodes.add(id);
    }
    disconnect() {
      const st = observerState.get(this);
      for (const id of st.nodes) { const list = (observed.get(id) ?? []).filter(x => x.observer !== this); if (list.length) observed.set(id, list); else observed.delete(id); }
      st.nodes.clear(); st.records = [];
    }
    takeRecords() { const st = observerState.get(this), rs = st.records; st.records = []; return rs; }
  }

  // ---- WebAssembly (pagewasm) -------------------------------------------------------------
  // The WebAssembly JavaScript API is tools/wasmvm/quickjs/webassembly.js, run on the first
  // read of `WebAssembly`, so a page without WebAssembly never loads it. Lean serves it (L4Factoidal.WasmVM.Hosts.PageWasm). An engine that
  // does not serve wasm_call leaves WebAssembly undefined.
  const wasmServed = typeof n.wasm === 'function' && typeof n.wasmGlue === 'function' && typeof n.wasm(0, 0) !== 'number';
  // ---- end of WebAssembly (pagewasm) ------------------------------------------------------

  // ---- Window -----------------------------------------------------------------------
  class Window extends EventTarget { constructor() { throw new TypeError('Illegal constructor'); } }
  addHandlers(Window.prototype);
  Object.setPrototypeOf(globalThis, Window.prototype);
  const window = globalThis;
  ids.set(window, WINDOW);
  const document = wrap(0);
  const frameWindows = new Map();
  const frameWindow = doc => {
    let w = frameWindows.get(doc);
    if (w) return w;
    const own = { document: () => wrap(doc), window: () => w, self: () => w, frames: () => w, globalThis: () => w,
      parent: () => window, top: () => window, frameElement: () => wrap(info(doc, 12)), length: () => 0 };
    w = new Proxy(window, {
      get(t, p) { return Object.prototype.hasOwnProperty.call(own, p) ? own[p]() : Reflect.get(t, p, t); },
      has(t, p) { return Object.prototype.hasOwnProperty.call(own, p) || Reflect.has(t, p); },
    });
    frameWindows.set(doc, w);
    return w;
  };
  let href = 'about:blank';
  const location = {
    get href() { return href; }, toString() { return href; },
    get protocol() { return /^[a-z][a-z0-9+.-]*:/i.exec(href)?.[0] ?? ''; },
    get pathname() { const m = /^[a-z][a-z0-9+.-]*:\/\/[^/?#]*([^?#]*)/i.exec(href); return m ? m[1] || '/' : ''; },
    get search() { const i = href.indexOf('?'); if (i < 0) return ''; const j = href.indexOf('#', i); return href.slice(i, j < 0 ? undefined : j); },
    get hash() { const i = href.indexOf('#'); return i < 0 || i === href.length - 1 ? '' : href.slice(i); },
    set hash(v) { v = String(v); const base = href.split('#')[0]; followHyperlink(v === '' ? base + '#' : base + (v.startsWith('#') ? v : '#' + v)); },
    set href(v) { const u = resolveURL(String(v)); if (u !== null) followHyperlink(u); },
    get host() { return /^[a-z][a-z0-9+.-]*:\/\/([^/?#]*)/i.exec(href)?.[1] ?? ''; },
    get hostname() { return this.host.replace(/:\d+$/, ''); },
    get origin() { const m = /^([a-z][a-z0-9+.-]*:\/\/[^/?#]*)/i.exec(href); return m ? m[1] : 'null'; },
    reload() {}, assign() {}, replace() {},
  };
  // URLs are parsed by Lean (WHATWG URL, node_query 12).
  const resolveURL = (input, base = href) => { const r = n.query(0, 12, base + '\u0000' + String(input)); return typeof r === 'string' ? r : null; };
  // Navigate to a fragment of this document (HTML §7.4.2.3.3): the URL changes and a
  // hashchange event is queued; any other navigation loads nothing here.
  const followHyperlink = url => {
    if (url === null || url === undefined) return;
    const oldURL = href, strip = u => u.split('#')[0];
    if (strip(url) !== strip(oldURL) || !url.includes('#') || url === oldURL) return;
    href = url;
    setTimeout(() => { const e = new HashChangeEvent('hashchange', { oldURL, newURL: url }); state(e).trusted = true; dispatch(window, e); }, 0);
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
  // [Replaceable] (WebIDL §3.7.4): an assignment replaces the attribute with a data property.
  Object.defineProperty(globalThis, 'event', { get: () => globalEvent,
    set(v) { Object.defineProperty(globalThis, 'event', { value: v, writable: true, configurable: true, enumerable: true }); }, configurable: true, enumerable: true });
  def('opener', null); def('frameElement', null); def('name', '');
  def('document', document); def('location', location);
  def('navigator', Object.freeze({ userAgent: 'Foafnaut', language: 'en', languages: ['en'], platform: '', onLine: true,
    cookieEnabled: false, hardwareConcurrency: 1, gpu,
    // Foafnaut's own (not a web API), for a page that shows what the engine does: the script
    // engine and the host's wall time of this page's last script turn, read when asked
    // (node_query op 20). Undefined in an engine without the op.
    get foafnaut() {
      const r = n.query(0, 20, '');
      if (typeof r !== 'string') return undefined;
      const k = r.lastIndexOf(' ');
      return { engine: r.slice(0, k), lastTurnMs: Number(r.slice(k + 1)) / 1e6 };
    } }));
  def('GPUBufferUsage', GPUBufferUsage); def('GPUTextureUsage', GPUTextureUsage); def('GPUShaderStage', GPUShaderStage);
  def('GPUColorWrite', GPUColorWrite); def('GPUValidationError', GPUValidationError); def('GPUOutOfMemoryError', GPUOutOfMemoryError);
  def('GPUCanvasContext', GPUCanvasContext); def('GPUDevice', GPUDevice);
  // document.fonts: a FontFaceSet (section dombreadth).
  // Canvas 2D globals, made on first use (the canvas2d section above).
  for (const name of ['CanvasRenderingContext2D', 'OffscreenCanvasRenderingContext2D', 'OffscreenCanvas', 'Path2D', 'ImageData',
    'ImageBitmap', 'CanvasGradient', 'CanvasPattern', 'TextMetrics', 'DOMMatrix', 'DOMMatrixReadOnly', 'DOMPoint', 'DOMPointReadOnly',
    'createImageBitmap'])
    if (!(name in globalThis)) Object.defineProperty(globalThis, name, { get: () => c2d()[name], configurable: true,
      set(v) { Object.defineProperty(globalThis, name, { value: v, writable: true, configurable: true }); } });
  def('WebGLRenderingContext', Object.freeze({ ...GL })); def('WebGL2RenderingContext', Object.freeze({ ...GL }));
  def('WebGLBuffer', WebGLBuffer); def('WebGLShader', WebGLShader); def('WebGLProgram', WebGLProgram);
  def('WebGLUniformLocation', WebGLUniformLocation);
  // pagewasm: a data property once read (WebIDL); before that an accessor that compiles the glue.
  if (wasmServed) Object.defineProperty(globalThis, 'WebAssembly', { configurable: true, enumerable: false,
    // QuickJS-NG hands the glue's function (bytecode); BubblePopJS hands its source.
    get() { const g = n.wasmGlue(), W = (typeof g === 'function' ? g : (0, eval)(g))(n, define); def('WebAssembly', W); return W; },
    set(v) { def('WebAssembly', v); } });
  def('history', Object.freeze({ length: 1, state: null, pushState() {}, replaceState() {}, back() {}, forward() {}, go() {} }));
  def('screen', Object.freeze({ width: 800, height: 600, availWidth: 800, availHeight: 600, colorDepth: 24, pixelDepth: 24 }));
  for (const [k, i] of [['innerWidth', 0], ['innerHeight', 1], ['outerWidth', 0], ['outerHeight', 1]])
    Object.defineProperty(globalThis, k, { get: () => viewport()[i], set(v) {}, configurable: true, enumerable: true });
  def('devicePixelRatio', 1); def('scrollX', 0); def('scrollY', 0);
  def('pageXOffset', 0); def('pageYOffset', 0);
  const text = xs => xs.map(x => typeof x === 'string' ? x : (() => { try { return typeof x === 'object' && x !== null && !(x instanceof Error) ? JSON.stringify(x) : String(x); } catch { return String(x); } })()).join(' ');
  const log = (...xs) => n.log(text(xs));
  // A line of another level starts with the level between two U+0001 marks; the console tab
  // (WebConsole.lean) reads it. One host import (console_log) carries every level.
  const at = level => (...xs) => n.log('\u0001' + level + '\u0001' + text(xs));
  const warn = at('warn'), error = at('error');
  def('console', Object.freeze({ log, info: at('info'), debug: at('debug'), warn, error, trace: log,
    assert: (c, ...xs) => { if (!c) error('Assertion failed:', ...xs); },
    group: log, groupCollapsed: log, groupEnd() {}, time() {}, timeEnd() {}, timeLog() {}, count() {}, countReset() {},
    dir: log, dirxml: log, table: log }));
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
  // ==== basics: web APIs over Lean (Encoding, URL, base64, crypto, structuredClone, performance) ====
  // Record: docs/designissues/2026-11-08-page-scripts.md, "Web APIs over Lean". The algorithms
  // are Lean's (L4Factoidal.WasmVM.Hosts.WebApi: WHATWG.Encoding, WHATWG.URL, WHATWG.Base64,
  // Crypto.WebCrypto); one `n.api` call is one whole operation (bytes as bytes). This section
  // only converts arguments (WebIDL), shapes objects and makes promises. Each API is installed
  // lazily: a getter on the global object that, on first use, probes `n.api` once and either
  // defines the API or leaves it undefined (an engine without the op). Nothing here runs at
  // page start.
  // `call(op, args, flags, bytes)`: the native `n.api(op, flags, bytes, ...args)`.
  const apiCall = (op, args, flags = 0, bytes = false) => n0.api(op, flags, bytes, ...args);
  const apiOn = (() => { let on; return () => on ??= (typeof n0.api === 'function' && apiCall(1, []) === '1'); })();
  const lazy = (name, make) => Object.defineProperty(globalThis, name, { configurable: true, enumerable: false,
    get() {
      const v = apiOn() ? make() : undefined;
      if (v === undefined) { delete globalThis[name]; return undefined; }
      define(globalThis, name, v); return v;
    },
    set(v) { define(globalThis, name, v); } });
  const apiError = (r, what) => {
    switch (r) {
      case -3: throw new DOMException(what, 'InvalidCharacterError');
      case -5: throw new RangeError(what + ': over a budget');
      case -21: throw new RangeError(what);
      case -22: throw new DOMException(what, 'OperationError');
      case -23: throw new DOMException(what, 'NotSupportedError');
      default: throw new TypeError(what);
    }
  };
  const api = (op, args, flags, bytes, what) => { const r = apiCall(op, args, flags, bytes); return typeof r === 'number' ? apiError(r, what) : r; };
  // WebIDL conversions.
  // USVString: a lone surrogate becomes U+FFFD. BubblePopJS strings are code points, never
  // lone surrogates, and need nothing.
  const usv = x => { const s = String(x); return typeof s.toWellFormed === 'function' ? s.toWellFormed() : s; };
  const dict = (x, what) => { if (x === undefined || x === null) return {}; if (typeof x !== 'object' && typeof x !== 'function') throw new TypeError(what + ': the options are not an object'); return x; };
  const isShared = x => typeof SharedArrayBuffer === 'function' && x instanceof SharedArrayBuffer;
  // A detached buffer holds no bytes (WebIDL "get a copy of the buffer source").
  const bufferSource = (x, what) => {
    if (x instanceof ArrayBuffer || isShared(x)) return x.detached ? new Uint8Array(0) : new Uint8Array(x);
    if (ArrayBuffer.isView(x)) return x.buffer.detached ? new Uint8Array(0) : new Uint8Array(x.buffer, x.byteOffset, x.byteLength);
    throw new TypeError(what + ": parameter is not of type 'BufferSource'");
  };
  const copyBytes = v => new Uint8Array(v);
  const brand = (map, o, what) => { const s = map.get(o); if (!s) throw new TypeError('Illegal invocation: ' + what); return s; };
  const setTag = (C, tag) => Object.defineProperty(C.prototype, Symbol.toStringTag, { value: tag, configurable: true });

  // ---- Encoding Standard §7: TextDecoder, TextEncoder ----------------------------------
  lazy('TextDecoder', () => {
    const decoders = new WeakMap();
    let nextHandle = 1;
    // A decoder dropped in the middle of a stream: Lean forgets its state.
    const finished = typeof FinalizationRegistry === 'function'
      ? new FinalizationRegistry(h => { apiCall(3, ['utf-8', String(h), ''], 0, false); }) : null;
    class TextDecoder {
      constructor(label = 'utf-8', options = undefined) {
        const l = String(label), o = dict(options, "Failed to construct 'TextDecoder'");
        const fatal = !!o.fatal, ignoreBOM = !!o.ignoreBOM;
        const name = apiCall(2, [l], 0, false);
        if (typeof name !== 'string') throw new RangeError(`Failed to construct 'TextDecoder': The encoding label provided ('${l}') is invalid.`);
        decoders.set(this, { name, fatal, ignoreBOM, handle: 0 });
      }
      get encoding() { return brand(decoders, this, 'TextDecoder').name; }
      get fatal() { return brand(decoders, this, 'TextDecoder').fatal; }
      get ignoreBOM() { return brand(decoders, this, 'TextDecoder').ignoreBOM; }
      decode(input = undefined, options = undefined) {
        const s = brand(decoders, this, 'TextDecoder');
        const bytes = input === undefined ? '' : bufferSource(input, "Failed to execute 'decode' on 'TextDecoder'");
        const stream = !!dict(options, "Failed to execute 'decode' on 'TextDecoder'").stream;
        if (stream && s.handle === 0) { s.handle = nextHandle++; finished?.register(this, s.handle, s); }
        const h = s.handle;
        if (!stream && h !== 0) { s.handle = 0; finished?.unregister(s); }
        const r = apiCall(3, [s.name, String(h), bytes], (s.fatal ? 1 : 0) | (s.ignoreBOM ? 2 : 0) | (stream ? 4 : 0), false);
        if (typeof r === 'number') apiError(r, r === -20 ? "Failed to execute 'decode' on 'TextDecoder': The encoded data was not valid." : 'TextDecoder');
        return r;
      }
    }
    setTag(TextDecoder, 'TextDecoder');
    return TextDecoder;
  });
  lazy('TextEncoder', () => {
    const encoders = new WeakSet();
    class TextEncoder {
      constructor() { encoders.add(this); }
      get encoding() { if (!encoders.has(this)) throw new TypeError('Illegal invocation'); return 'utf-8'; }
      encode(input = '') {
        if (!encoders.has(this)) throw new TypeError('Illegal invocation');
        return new Uint8Array(api(4, [usv(input)], 0, true, 'TextEncoder'));
      }
      encodeInto(source, destination) {
        if (!encoders.has(this)) throw new TypeError('Illegal invocation');
        if (!(destination instanceof Uint8Array)) throw new TypeError("Failed to execute 'encodeInto' on 'TextEncoder': parameter 2 is not of type 'Uint8Array'.");
        const r = api(5, [usv(source), String(destination.length)], 0, true, 'TextEncoder');
        const h = new Uint8Array(r, 0, 8), u32 = k => (h[k] | h[k + 1] << 8 | h[k + 2] << 16 | h[k + 3] << 24) >>> 0;
        const read = u32(0), written = u32(4);
        destination.set(new Uint8Array(r, 8, written));
        return { read, written };
      }
    }
    setTag(TextEncoder, 'TextEncoder');
    return TextEncoder;
  });

  // ---- URL Standard §6: URL, URLSearchParams ----------------------------------------------
  // A URL's state is its attributes as Lean answers them (op 10 parse, op 11 a setter); the
  // URL record is its href, which the URL parser gives back (the standard's serializer
  // round trip). URLSearchParams keeps its list; parsing and serializing are Lean's.
  const urlParts = new WeakMap(), paramState = new WeakMap();
  const PARTS = ['href', 'origin', 'protocol', 'username', 'password', 'host', 'hostname', 'port', 'pathname', 'search', 'hash'];
  const splitPrefixed = s => { const out = []; let i = 0; while (i < s.length) { const j = s.indexOf(':', i), k = Number(s.slice(i, j)); out.push(s.slice(j + 1, j + 1 + k)); i = j + 1 + k; } return out; };
  const parseQuery = (q, strip = false) => { const xs = splitPrefixed(api(12, [q], strip ? 1 : 0, false, 'URLSearchParams')); const list = []; for (let i = 0; i + 1 < xs.length; i += 2) list.push([xs[i], xs[i + 1]]); return list; };
  let URLSearchParamsC;
  const makeURLSearchParams = () => {
    if (URLSearchParamsC) return URLSearchParamsC;
    const serialize = list => api(13, list.flat(), 0, false, 'URLSearchParams');
    const update = s => {
      if (!s.url) return;
      const u = urlParts.get(s.url);
      const r = apiCall(11, [u.parts[0], 'search', serialize(s.list)], 0, false);
      if (typeof r === 'string') u.parts = r.split('\0');
    };
    const st = o => brand(paramState, o, 'URLSearchParams');
    const iterProto = Object.create(Object.getPrototypeOf(Object.getPrototypeOf([][Symbol.iterator]())), {
      next: { value() { const it = this; if (!it || !it.target) throw new TypeError('Illegal invocation'); const list = st(it.target).list;
        if (it.index >= list.length) return { value: undefined, done: true };
        const [k, v] = list[it.index++]; return { value: it.kind === 'key' ? k : it.kind === 'value' ? v : [k, v], done: false }; }, writable: true, configurable: true },
      [Symbol.toStringTag]: { value: 'URLSearchParams Iterator', configurable: true } });
    const iterate = (o, kind) => { st(o); const it = Object.create(iterProto); it.target = o; it.kind = kind; it.index = 0; return it; };
    class URLSearchParams {
      constructor(init = '') {
        const list = [];
        if (init !== null && (typeof init === 'object' || typeof init === 'function')) {
          if (init[Symbol.iterator] !== undefined) {
            for (const pair of init) {
              if (pair === null || (typeof pair !== 'object' && typeof pair !== 'function')) throw new TypeError("Failed to construct 'URLSearchParams': The provided value cannot be converted to a sequence.");
              const p = [...pair];
              if (p.length !== 2) throw new TypeError("Failed to construct 'URLSearchParams': Sequence initializer must only contain pair elements");
              list.push([usv(p[0]), usv(p[1])]);
            }
          } else {
            for (const k of Reflect.ownKeys(init)) {
              const d = Reflect.getOwnPropertyDescriptor(init, k);
              if (d === undefined || !d.enumerable) continue;
              if (typeof k === 'symbol') throw new TypeError("Failed to construct 'URLSearchParams': a key is a symbol");
              list.push([usv(k), usv(init[k])]);
            }
          }
        } else list.push(...parseQuery(usv(init), true));
        paramState.set(this, { list, url: null });
      }
      get size() { return st(this).list.length; }
      append(name, value) { if (arguments.length < 2) throw new TypeError("Failed to execute 'append' on 'URLSearchParams': 2 arguments required"); const s = st(this); s.list.push([usv(name), usv(value)]); update(s); }
      delete(name, value = undefined) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'delete' on 'URLSearchParams': 1 argument required");
        const s = st(this), k = usv(name), v = value === undefined ? undefined : usv(value);
        s.list = s.list.filter(p => !(p[0] === k && (v === undefined || p[1] === v))); update(s);
      }
      get(name) { if (arguments.length < 1) throw new TypeError("Failed to execute 'get' on 'URLSearchParams': 1 argument required"); const k = usv(name), p = st(this).list.find(p => p[0] === k); return p ? p[1] : null; }
      getAll(name) { if (arguments.length < 1) throw new TypeError("Failed to execute 'getAll' on 'URLSearchParams': 1 argument required"); const k = usv(name); return st(this).list.filter(p => p[0] === k).map(p => p[1]); }
      has(name, value = undefined) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'has' on 'URLSearchParams': 1 argument required");
        const k = usv(name), v = value === undefined ? undefined : usv(value);
        return st(this).list.some(p => p[0] === k && (v === undefined || p[1] === v));
      }
      set(name, value) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'set' on 'URLSearchParams': 2 arguments required");
        const s = st(this), k = usv(name), v = usv(value);
        const i = s.list.findIndex(p => p[0] === k);
        if (i < 0) s.list.push([k, v]); else { s.list[i] = [k, v]; s.list = s.list.filter((p, j) => j <= i || p[0] !== k); }
        update(s);
      }
      // Stable, by the code units of the names (URL §6.2): JavaScript compares strings so.
      sort() { const s = st(this); s.list.sort((a, b) => a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0); update(s); }
      toString() { return serialize(st(this).list); }
      forEach(f, thisArg = undefined) {
        if (typeof f !== 'function') throw new TypeError("Failed to execute 'forEach' on 'URLSearchParams': parameter 1 is not of type 'Function'.");
        const s = st(this);
        for (let i = 0; i < s.list.length; i++) { const [k, v] = s.list[i]; f.call(thisArg, v, k, this); }
      }
      entries() { return iterate(this, 'key+value'); }
      keys() { return iterate(this, 'key'); }
      values() { return iterate(this, 'value'); }
    }
    Object.defineProperty(URLSearchParams.prototype, Symbol.iterator, { value: URLSearchParams.prototype.entries, writable: true, configurable: true });
    setTag(URLSearchParams, 'URLSearchParams');
    URLSearchParamsC = URLSearchParams;
    return URLSearchParams;
  };
  lazy('URLSearchParams', makeURLSearchParams);
  lazy('URL', () => {
    const parse = (url, base) => {
      const r = base === undefined ? apiCall(10, [usv(url)], 0, false) : apiCall(10, [usv(url), usv(base)], 1, false);
      return typeof r === 'string' ? r.split('\0') : null;
    };
    const parts = o => brand(urlParts, o, 'URL');
    const queryOf = u => u.parts[9].startsWith('?') ? u.parts[9].slice(1) : '';
    const reparams = u => { if (u.params) paramState.get(u.params).list = parseQuery(queryOf(u)); };
    const setter = (o, attr, v) => {
      const u = parts(o);
      const r = apiCall(11, [u.parts[0], attr, usv(v)], 0, false);
      if (typeof r !== 'string') { if (attr === 'href') throw new TypeError(`Failed to set the 'href' property on 'URL': Invalid URL`); return; }
      u.parts = r.split('\0');
      if (attr === 'href' || attr === 'search') reparams(u);
    };
    class URL {
      constructor(url, base = undefined) {
        if (arguments.length < 1) throw new TypeError("Failed to construct 'URL': 1 argument required, but only 0 present.");
        const p = parse(url, base);
        if (p === null) throw new TypeError(`Failed to construct 'URL': Invalid URL`);
        urlParts.set(this, { parts: p, params: null });
      }
      static canParse(url, base = undefined) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'canParse' on 'URL': 1 argument required");
        return parse(url, base) !== null;
      }
      static parse(url, base = undefined) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'parse' on 'URL': 1 argument required");
        const p = parse(url, base);
        if (p === null) return null;
        const o = Object.create(URL.prototype); urlParts.set(o, { parts: p, params: null }); return o;
      }
      get searchParams() {
        const u = parts(this);
        if (!u.params) { const P = makeURLSearchParams(); u.params = new P(''); const s = paramState.get(u.params); s.list = parseQuery(queryOf(u)); s.url = this; }
        return u.params;
      }
      toString() { return parts(this).parts[0]; }
      toJSON() { return parts(this).parts[0]; }
    }
    PARTS.forEach((k, i) => {
      const d = { get() { return parts(this).parts[i]; }, enumerable: true, configurable: true };
      if (k !== 'origin') d.set = function (v) { setter(this, k, v); };
      Object.defineProperty(URL.prototype, k, d);
    });
    setTag(URL, 'URL');
    return URL;
  });
  // The webkitURL alias (URL §6.1).
  lazy('webkitURL', () => globalThis.URL);

  // ---- HTML §8.3: atob, btoa (forgiving-base64 of Infra, in Lean) ---------------------------
  lazy('atob', () => function atob(data) {
    if (arguments.length < 1) throw new TypeError("Failed to execute 'atob' on 'Window': 1 argument required, but only 0 present.");
    return api(20, [String(data)], 0, false, "Failed to execute 'atob' on 'Window': The string to be decoded is not correctly encoded.");
  });
  lazy('btoa', () => function btoa(data) {
    if (arguments.length < 1) throw new TypeError("Failed to execute 'btoa' on 'Window': 1 argument required, but only 0 present.");
    return api(21, [String(data)], 0, false, "Failed to execute 'btoa' on 'Window': The string to be encoded contains characters outside of the Latin1 range.");
  });

  // ---- Web Cryptography: crypto, SubtleCrypto, CryptoKey ------------------------------------
  // ==== haclweb: crypto.subtle over Lean and HACL* ====
  // Record: docs/designissues/2026-11-09-hacl-web-crypto.md. Lean decides everything
  // (Crypto.WebCryptoKeys: the registry, usages, extractability, key formats, the error of
  // each refusal) and HACL* computes (Crypto.WebHacl). Keys live in Lean: a CryptoKey here
  // holds a handle and its public attributes, never key bytes. This section only converts
  // arguments (WebIDL), shapes objects and settles promises; each operation runs as a task
  // of Lean's event loop (`later`), never inside the caller's turn or a frame.
  //   n.api 40 normalize(op, name) -> "Registered\nmember:type[!]..." (the dictionary to read)
  //   n.api 41 subtle(method, k1, v1, ...) -> packed fields (`unpack`)
  //   n.api 42 drop(handle): the page's CryptoKey was collected; Lean zeroes the key bytes.
  let CryptoKeyC, cryptoKeys, cloneCryptoKey;
  lazy('crypto', () => {
    const random = typeof apiCall(30, ['0'], 0, true) !== 'number';
    const subtleOn = typeof apiCall(40, ['digest', 'SHA-256'], 0, false) === 'string';
    const intArrays = [Int8Array, Uint8Array, Uint8ClampedArray, Int16Array, Uint16Array, Int32Array, Uint32Array,
      ...(typeof BigInt64Array === 'function' ? [BigInt64Array, BigUint64Array] : [])];
    cryptoKeys = new WeakMap();
    const keyOf = k => brand(cryptoKeys, k, 'CryptoKey');
    class CryptoKey {
      constructor() { throw new TypeError('Illegal constructor'); }
      get type() { return keyOf(this).type; }
      get extractable() { return keyOf(this).extractable; }
      get algorithm() { return keyOf(this).algorithm; }
      get usages() { return keyOf(this).usages; }
    }
    setTag(CryptoKey, 'CryptoKey');
    CryptoKeyC = CryptoKey;
    const dropped = typeof FinalizationRegistry === 'function' ? new FinalizationRegistry(h => { apiCall(42, [String(h)], 0, false); }) : null;
    const errNames = { [-20]: 'TypeError', [-22]: 'OperationError', [-23]: 'NotSupportedError', [-24]: 'SyntaxError',
      [-25]: 'InvalidAccessError', [-26]: 'DataError', [-27]: 'QuotaExceededError' };
    const raise = (code, what) => {
      const name = errNames[code] || 'OperationError';
      if (name === 'TypeError') throw new TypeError(what);
      throw new DOMException(what, name);
    };
    // A task of the event loop (HTML "queue a global task") settles the promise. `keep`
    // holds the operation's CryptoKeys until the task has run: a key the page dropped in
    // the meantime must not be collected (and its bytes wiped in Lean) before its use.
    const later = (f, keep) => new Promise((resolve, reject) => { timer(0, () => { try { resolve(f(keep)); } catch (e) { reject(e); } }, 0, []); });
    const start = f => { try { return f(); } catch (e) { return Promise.reject(e); } };
    // WebIDL conversions.
    const domString = v => { if (typeof v === 'symbol') throw new TypeError('Cannot convert a Symbol to a string'); return String(v); };
    const enforceRange = (v, max, what) => {
      const x = Number(v);
      if (!Number.isFinite(x)) throw new TypeError(`${what} is not a finite number`);
      const t = Math.trunc(x);
      if (t < 0 || t > max) throw new TypeError(`${what} is outside the accepted range`);
      return t;
    };
    const usageNames = ['encrypt', 'decrypt', 'sign', 'verify', 'deriveKey', 'deriveBits', 'wrapKey', 'unwrapKey',
      'encapsulateKey', 'encapsulateBits', 'decapsulateKey', 'decapsulateBits'];
    const formatNames = ['raw', 'pkcs8', 'spki', 'jwk', 'raw-public', 'raw-private', 'raw-seed', 'raw-secret'];
    const usagesOf = us => {
      if (us === null || typeof us !== 'object' || typeof us[Symbol.iterator] !== 'function') throw new TypeError('keyUsages: not a sequence');
      const out = [];
      for (const u of us) { const x = domString(u); if (!usageNames.includes(x)) throw new TypeError(`KeyUsage: '${x}' is not a valid enum value`); out.push(x); }
      return out;
    };
    const formatOf = f => { const x = domString(f); if (!formatNames.includes(x)) throw new TypeError(`KeyFormat: '${x}' is not a valid enum value`); return x; };
    // JsonWebKey (WebIDL dictionary, members in lexicographic order).
    const jwkMembers = ['alg', 'crv', 'd', 'dp', 'dq', 'e', 'ext', 'k', 'key_ops', 'kty', 'n', 'oth', 'p', 'q', 'qi', 'use', 'x', 'y'];
    const jwkPairs = o => {
      const out = [];
      if (o === null || o === undefined) return out;
      for (const m of jwkMembers) {
        const v = o[m];
        if (v === undefined) continue;
        if (m === 'ext') out.push('j:ext', v ? 'true' : 'false');
        else if (m === 'key_ops') {
          if (v === null || typeof v !== 'object' || typeof v[Symbol.iterator] !== 'function') throw new TypeError('JsonWebKey: key_ops is not a sequence');
          out.push('j:key_ops', '');
          for (const x of v) out.push('j:key_ops[]', domString(x));
        } else if (m === 'oth') {
          if (v === null || typeof v !== 'object') throw new TypeError('JsonWebKey: oth is not a sequence');
        } else out.push('j:' + m, domString(v));
      }
      return out;
    };
    // Lean's answers: a u32 count, then each field as a u32 length and its bytes.
    const unpack = ab => {
      const u = new Uint8Array(ab), u32 = i => u[i] | u[i + 1] << 8 | u[i + 2] << 16 | (u[i + 3] << 24 >>> 0);
      const out = [];
      for (let i = 0, at = 4, n = u32(0); i < n; i++) { const len = u32(at); out.push(u.subarray(at + 4, at + 4 + len)); at += 4 + len; }
      return out;
    };
    const ascii = b => { let s = ''; for (let i = 0; i < b.length; i++) s += String.fromCharCode(b[i]); return s; };
    const buffer = b => { const r = new ArrayBuffer(b.length); new Uint8Array(r).set(b); return r; };
    // "normalize an algorithm" (§18.4): Lean names the registered algorithm and the members
    // of its dictionary; here they are read and converted, in WebIDL order.
    const normalize = (op, alg, prefix = 'a:') => {
      if (alg === null || (typeof alg !== 'object' && typeof alg !== 'function')) alg = { name: domString(alg) };
      const nm = alg.name;
      if (nm === undefined) throw new TypeError("Algorithm: Missing or not an AlgorithmIdentifier: name");
      const r = apiCall(40, [op, domString(nm)], 0, false);
      if (typeof r === 'number') raise(r, `Algorithm: Unrecognized name or not supported for ${op}`);
      const [reg, ...ms] = r.split('\n');
      const pairs = [prefix + 'name', reg], keys = [];
      for (const m of ms) {
        const i = m.indexOf(':'), k = m.slice(0, i), req = m.endsWith('!'), t = m.slice(i + 1, req ? -1 : undefined);
        const v = alg[k];
        if (v === undefined) { if (req) throw new TypeError(`Algorithm: Missing required member '${k}'`); continue; }
        let x;
        if (t === 'h') x = normalize('digest', v).name;
        else if (t === 'b') x = copyBytes(bufferSource(v, 'Algorithm'));
        else if (t === 'l') x = String(enforceRange(v, 4294967295, k));
        else if (t === 'o') x = String(enforceRange(v, 255, k));
        else if (t === 'k') { x = String(keyOf(v).handle); keys.push(v); }
        else x = domString(v);
        pairs.push(prefix + k, x);
      }
      return { name: reg, pairs, keys };
    };
    const call = (args, what) => {
      const r = apiCall(41, args, 0, true);
      if (typeof r === 'number') raise(r, what);
      return unpack(r);
    };
    // A CryptoKey from Lean's fields at `i` ("key", handle, type, extractable, usages, name, n, pairs).
    const makeKey = (f, i) => {
      const handle = +ascii(f[i + 1]), us = ascii(f[i + 4]), np = +ascii(f[i + 6]);
      const algorithm = { name: ascii(f[i + 5]) };
      for (let j = 0; j < np; j++) {
        const k = ascii(f[i + 7 + 2 * j]), v = ascii(f[i + 8 + 2 * j]);
        algorithm[k] = k === 'hash' ? { name: v } : k === 'length' ? +v : v;
      }
      const key = Object.create(CryptoKey.prototype);
      cryptoKeys.set(key, { handle, type: ascii(f[i + 2]), extractable: ascii(f[i + 3]) === '1', algorithm, usages: us ? us.split(',') : [] });
      if (dropped) dropped.register(key, handle);
      return [key, i + 7 + 2 * np];
    };
    const keyAnswer = f => {
      if (ascii(f[0]) === 'pair') { const [publicKey, j] = makeKey(f, 1); const [privateKey] = makeKey(f, j); return { publicKey, privateKey }; }
      return makeKey(f, 0)[0];
    };
    const bytesAnswer = f => buffer(f[1]);
    const jwkAnswer = f => {
      const o = {};
      for (let i = 0, n = +ascii(f[1]); i < n; i++) {
        const name = ascii(f[2 + 3 * i]), kind = ascii(f[3 + 3 * i]), v = ascii(f[4 + 3 * i]);
        o[name] = kind === 'b' ? v === 'true' : kind === 'a' ? (v ? v.split(',') : []) : v;
      }
      return o;
    };
    const usagePairs = us => us.flatMap(u => ['usage', u]);
    // wrapKey and unwrapKey normalize for "wrapKey" ("unwrapKey") and, failing that, for
    // "encrypt" ("decrypt") (§14.3.11 step 3, §14.3.12 step 3).
    const normalizeEither = (op, fallback, alg) => {
      try { return normalize(op, alg); } catch (e) { if (e instanceof DOMException && e.name === 'NotSupportedError') return normalize(fallback, alg); throw e; }
    };
    const subtleMethods = {
      digest(algorithm, data) {
        return start(() => { const a = normalize('digest', algorithm); const d = copyBytes(bufferSource(data, 'digest'));
          return later(() => { const r = apiCall(32, [a.name, d], 0, true); if (typeof r === 'number') raise(r, 'digest'); return r; }); });
      },
      generateKey(algorithm, extractable, keyUsages) {
        return start(() => {
          const us = usagesOf(keyUsages), a = normalize('generateKey', algorithm);
          const args = ['generateKey', 'extractable', extractable ? '1' : '0', ...usagePairs(us), ...a.pairs];
          return later(() => keyAnswer(call(args, 'generateKey')));
        });
      },
      importKey(format, keyData, algorithm, extractable, keyUsages) {
        return start(() => {
          const f = formatOf(format);
          const isBuffer = keyData instanceof ArrayBuffer || ArrayBuffer.isView(keyData) || isShared(keyData);
          const jwk = isBuffer ? null : jwkPairs(keyData);
          const us = usagesOf(keyUsages);
          if (f === 'jwk' && isBuffer) throw new TypeError('importKey: keyData is not a JsonWebKey');
          if (f !== 'jwk' && !isBuffer) throw new TypeError("importKey: keyData is not of type 'BufferSource'");
          const a = normalize('importKey', algorithm);
          const data = isBuffer ? copyBytes(bufferSource(keyData, 'importKey')) : null;
          const args = ['importKey', 'format', f, 'extractable', extractable ? '1' : '0', ...usagePairs(us), ...a.pairs,
            ...(data ? ['data', data] : jwk)];
          return later(() => { try { return keyAnswer(call(args, 'importKey')); } finally { if (data) data.fill(0); } });
        });
      },
      exportKey(format, key) {
        return start(() => {
          const f = formatOf(format), k = keyOf(key);
          return later(() => { const r = call(['exportKey', 'format', f, 'key', String(k.handle)], 'exportKey'); return ascii(r[0]) === 'jwk' ? jwkAnswer(r) : bytesAnswer(r); }, [key]);
        });
      },
      sign(algorithm, key, data) {
        return start(() => { const a = normalize('sign', algorithm), k = keyOf(key), d = copyBytes(bufferSource(data, 'sign'));
          return later(() => bytesAnswer(call(['sign', 'key', String(k.handle), 'data', d, ...a.pairs], 'sign')), [key]); });
      },
      verify(algorithm, key, signature, data) {
        return start(() => { const a = normalize('verify', algorithm), k = keyOf(key);
          const sig = copyBytes(bufferSource(signature, 'verify')), d = copyBytes(bufferSource(data, 'verify'));
          return later(() => ascii(call(['verify', 'key', String(k.handle), 'signature', sig, 'data', d, ...a.pairs], 'verify')[1]) === '1', [key]); });
      },
      deriveBits(algorithm, baseKey, length = null) {
        return start(() => {
          const len = length === null || length === undefined ? 'null' : String(enforceRange(length, 4294967295, 'length'));
          const a = normalize('deriveBits', algorithm), k = keyOf(baseKey);
          return later(() => bytesAnswer(call(['deriveBits', 'baseKey', String(k.handle), 'length', len, ...a.pairs], 'deriveBits')), [baseKey, ...a.keys]);
        });
      },
      deriveKey(algorithm, baseKey, derivedKeyType, extractable, keyUsages) {
        return start(() => {
          const us = usagesOf(keyUsages), a = normalize('deriveBits', algorithm), k = keyOf(baseKey);
          const t = normalize('importKey', derivedKeyType, 't:');
          normalize('get key length', derivedKeyType, 't:');
          const args = ['deriveKey', 'baseKey', String(k.handle), 'extractable', extractable ? '1' : '0', ...usagePairs(us), ...a.pairs, ...t.pairs];
          return later(() => keyAnswer(call(args, 'deriveKey')), [baseKey, ...a.keys]);
        });
      },
      encrypt(algorithm, key, data) {
        return start(() => { const a = normalize('encrypt', algorithm), k = keyOf(key), d = copyBytes(bufferSource(data, 'encrypt'));
          return later(() => bytesAnswer(call(['encrypt', 'key', String(k.handle), 'data', d, ...a.pairs], 'encrypt')), [key]); });
      },
      decrypt(algorithm, key, data) {
        return start(() => { const a = normalize('decrypt', algorithm), k = keyOf(key), d = copyBytes(bufferSource(data, 'decrypt'));
          return later(() => bytesAnswer(call(['decrypt', 'key', String(k.handle), 'data', d, ...a.pairs], 'decrypt')), [key]); });
      },
      wrapKey(format, key, wrappingKey, wrapAlgorithm) {
        return start(() => {
          const f = formatOf(format), a = normalizeEither('wrapKey', 'encrypt', wrapAlgorithm), k = keyOf(key), w = keyOf(wrappingKey);
          return later(() => bytesAnswer(call(['wrapKey', 'format', f, 'key', String(k.handle), 'wrappingKey', String(w.handle), ...a.pairs], 'wrapKey')), [key, wrappingKey]);
        });
      },
      unwrapKey(format, wrappedKey, unwrappingKey, unwrapAlgorithm, unwrappedKeyAlgorithm, extractable, keyUsages) {
        return start(() => {
          const f = formatOf(format), us = usagesOf(keyUsages);
          const a = normalizeEither('unwrapKey', 'decrypt', unwrapAlgorithm), t = normalize('importKey', unwrappedKeyAlgorithm, 't:');
          const w = keyOf(unwrappingKey), d = copyBytes(bufferSource(wrappedKey, 'unwrapKey'));
          const args = ['unwrapKey', 'format', f, 'unwrappingKey', String(w.handle), 'data', d, 'extractable', extractable ? '1' : '0',
            ...usagePairs(us), ...a.pairs, ...t.pairs];
          return later(() => keyAnswer(call(args, 'unwrapKey')), [unwrappingKey]);
        });
      },
    };
    class SubtleCrypto { constructor() { throw new TypeError('Illegal constructor'); } }
    if (subtleOn) for (const [k, f] of Object.entries(subtleMethods)) define(SubtleCrypto.prototype, k, f);
    setTag(SubtleCrypto, 'SubtleCrypto');
    const subtle = Object.create(SubtleCrypto.prototype);
    class Crypto { constructor() { throw new TypeError('Illegal constructor'); } get subtle() { return subtleOn ? subtle : undefined; } }
    if (random) {
      define(Crypto.prototype, 'getRandomValues', function getRandomValues(array) {
        if (!(intArrays.some(C => array instanceof C))) throw new DOMException("Failed to execute 'getRandomValues' on 'Crypto': The provided ArrayBufferView is of type that is not an integer array.", 'TypeMismatchError');
        if (array.byteLength > 65536) throw new DOMException(`Failed to execute 'getRandomValues' on 'Crypto': The ArrayBufferView's byte length (${array.byteLength}) exceeds the number of bytes of entropy available via this API (65536).`, 'QuotaExceededError');
        new Uint8Array(array.buffer, array.byteOffset, array.byteLength).set(new Uint8Array(api(30, [String(array.byteLength)], 0, true, 'getRandomValues')));
        return array;
      });
      define(Crypto.prototype, 'randomUUID', function randomUUID() { return api(31, [], 0, false, 'randomUUID'); });
    }
    // StructuredSerialize of a CryptoKey (§15.4 "serializable"): the copy has its own handle
    // to the same key in Lean, so the page's dropping one does not wipe the other's.
    cloneCryptoKey = key => { keyOf(key); return keyAnswer(call(['cloneKey', 'key', String(keyOf(key).handle)], 'structuredClone')); };
    setTag(Crypto, 'Crypto');
    define(globalThis, 'Crypto', Crypto); define(globalThis, 'SubtleCrypto', SubtleCrypto); define(globalThis, 'CryptoKey', CryptoKey);
    return Object.create(Crypto.prototype);
  });
  // ==== end haclweb ====
  for (const k of ['Crypto', 'SubtleCrypto', 'CryptoKey'])
    Object.defineProperty(globalThis, k, { configurable: true, enumerable: false, get() { void globalThis.crypto; const d = Object.getOwnPropertyDescriptor(globalThis, k); return d && 'value' in d ? d.value : undefined; } });

  // ---- HTML §2.7: structuredClone ------------------------------------------------------
  // StructuredSerializeInternal and StructuredDeserialize in one walk (the two halves meet
  // in the same realm, so the record between them is not built). The memory map keeps
  // repeated and cyclic references. Platform objects other than DOMException are not
  // serializable.
  const cloneError = what => new DOMException(`Failed to execute 'structuredClone' on 'Window': ${what} could not be cloned.`, 'DataCloneError');
  const errorNames = ['Error', 'EvalError', 'RangeError', 'ReferenceError', 'SyntaxError', 'TypeError', 'URIError'];
  const typedArrays = [Int8Array, Uint8Array, Uint8ClampedArray, Int16Array, Uint16Array, Int32Array, Uint32Array, Float32Array, Float64Array,
    ...(typeof BigInt64Array === 'function' ? [BigInt64Array, BigUint64Array] : []), ...(typeof Float16Array === 'function' ? [Float16Array] : [])];
  const isPlatform = v => v instanceof EventTarget || ev.has(v) || v instanceof DOMRectReadOnly || (cryptoKeys !== undefined && cryptoKeys.has(v)) ||
    urlParts.has(v) || paramState.has(v);
  const has = (o, p) => Object.prototype.hasOwnProperty.call(o, p);
  const slotted = [Promise, WeakMap, WeakSet, globalThis.WeakRef, globalThis.FinalizationRegistry, Symbol];
  const structuredCloneOf = (value, memory) => {
    if (typeof value === 'symbol') throw cloneError('Symbol()');
    if (value === null || (typeof value !== 'object' && typeof value !== 'function')) return value;
    if (memory.has(value)) return memory.get(value);
    if (typeof value === 'function') throw cloneError(String(value).slice(0, 40));
    let out;
    const keep = o => { memory.set(value, o); return o; };
    const tag = Object.prototype.toString.call(value);
    // Boolean, Number, BigInt and String objects: each valueOf throws for any other object.
    for (const P of [Boolean, Number, BigInt, String]) {
      let x, ok = true;
      try { x = P.prototype.valueOf.call(value); } catch { ok = false; }
      if (ok) return keep(Object(x));
    }
    if (value instanceof Date) return keep(new Date(Date.prototype.getTime.call(value)));
    if (value instanceof RegExp) return keep(new RegExp(value.source, value.flags));
    if (isShared(value)) throw cloneError('SharedArrayBuffer');
    if (value instanceof ArrayBuffer) {
      if (value.detached) throw cloneError('An ArrayBuffer is detached and');
      return keep(value.resizable ? (() => { const b = new ArrayBuffer(value.byteLength, { maxByteLength: value.maxByteLength }); new Uint8Array(b).set(new Uint8Array(value)); return b; })() : value.slice(0));
    }
    if (ArrayBuffer.isView(value)) {
      if (value.buffer.detached) throw cloneError('An ArrayBufferView is detached and');
      const buffer = structuredCloneOf(value.buffer, memory);
      if (typeof DataView === 'function' && value instanceof DataView) return keep(new DataView(buffer, value.byteOffset, value.byteLength));
      const C = typedArrays.find(T => value instanceof T);
      return keep(new C(buffer, value.byteOffset, value.length));
    }
    if (value instanceof Map) {
      out = keep(new Map());
      const entries = [...Map.prototype.entries.call(value)];
      for (const [k, v] of entries) out.set(structuredCloneOf(k, memory), structuredCloneOf(v, memory));
      return out;
    }
    if (value instanceof Set) {
      out = keep(new Set());
      const entries = [...Set.prototype.values.call(value)];
      for (const v of entries) out.add(structuredCloneOf(v, memory));
      return out;
    }
    if (value instanceof DOMException) {
      return keep(new DOMException(String(value.message), String(value.name)));
    }
    if (cryptoKeys !== undefined && cryptoKeys.has(value)) return keep(cloneCryptoKey(value)); // haclweb
    if (isPlatform(value)) throw cloneError(Object.prototype.toString.call(value));
    if (value instanceof Error) {
      const nameProp = value.name;
      const name = errorNames.includes(nameProp) ? nameProp : 'Error';
      const d = Object.getOwnPropertyDescriptor(value, 'message');
      const C = globalThis[name];
      out = keep(d && 'value' in d ? new C(String(d.value)) : new C());
      const sd = Object.getOwnPropertyDescriptor(value, 'stack');
      if (sd && 'value' in sd && typeof sd.value === 'string') define(out, 'stack', sd.value);
      if (has(value, 'cause')) define(out, 'cause', structuredCloneOf(value.cause, memory));
      return out;
    }
    if (Array.isArray(value)) out = keep(new Array(value.length));
    else {
      // An object with internal slots of its own, or an exotic one, is not serializable.
      if (tag === '[object Arguments]' || slotted.some(C => typeof C === 'function' && value instanceof C)) throw cloneError(tag);
      out = keep({});
    }
    for (const k of Object.keys(value)) {
      if (!has(value, k)) continue;
      out[k] = structuredCloneOf(value[k], memory);
    }
    return out;
  };
  def('structuredClone', function structuredClone(value, options = undefined) {
    if (arguments.length < 1) throw new TypeError("Failed to execute 'structuredClone' on 'Window': 1 argument required, but only 0 present.");
    const o = dict(options, "Failed to execute 'structuredClone' on 'Window'");
    const transfer = o.transfer === undefined ? [] : [...o.transfer];
    const memory = new Map();
    for (const t of transfer) {
      if (!(t instanceof ArrayBuffer) || isShared(t)) throw cloneError('A value in the transfer list');
      if (memory.has(t)) throw new DOMException("Failed to execute 'structuredClone' on 'Window': ArrayBuffer at index is a duplicate of an earlier ArrayBuffer.", 'DataCloneError');
      if (t.detached) throw cloneError('An ArrayBuffer is detached and');
      memory.set(t, null);
    }
    // The transferred buffers move: their new objects are made now, and the old ones are
    // detached after the walk (HTML StructuredSerializeWithTransfer step 5).
    for (const t of transfer) memory.set(t, t.slice(0));
    const out = structuredCloneOf(value, memory);
    for (const t of transfer) t.transfer();
    return out;
  });

  // ---- User Timing: performance.mark, measure ---------------------------------------------
  // performance.now and timeOrigin are QuickJS-NG's, on the WASI clock, which is Lean's script
  // clock (Hosts.Page.ScriptClock). The entries are this list.
  if (typeof performance === 'object' && performance !== null && typeof performance.mark !== 'function') {
    const entries = [];
    class PerformanceEntry {
      constructor() { throw new TypeError('Illegal constructor'); }
      toJSON() { return { name: this.name, entryType: this.entryType, startTime: this.startTime, duration: this.duration }; }
    }
    const entry = (C, name, entryType, startTime, duration, detail) => {
      const e = Object.create(C.prototype);
      for (const [k, v] of Object.entries({ name, entryType, startTime, duration, detail })) Object.defineProperty(e, k, { value: v, enumerable: true });
      return e;
    };
    const time = (x, what) => { const t = Number(x); if (!(t >= 0)) throw new TypeError(`${what}: the time is negative or not a number`); return t; };
    class PerformanceMark extends PerformanceEntry {
      constructor(name, options = undefined) {
        const o = dict(options, "Failed to construct 'PerformanceMark'");
        const e = entry(new.target, String(name), 'mark', o.startTime === undefined ? performance.now() : time(o.startTime, 'PerformanceMark'), 0,
          o.detail === undefined ? null : structuredClone(o.detail));
        return e;
      }
    }
    class PerformanceMeasure extends PerformanceEntry {}
    const markTime = (m, what) => {
      if (typeof m === 'number') return time(m, what);
      const name = String(m);
      for (let i = entries.length - 1; i >= 0; i--) if (entries[i].entryType === 'mark' && entries[i].name === name) return entries[i].startTime;
      throw new DOMException(`Failed to execute 'measure' on 'Performance': The mark '${name}' does not exist.`, 'SyntaxError');
    };
    const methods = {
      mark(name, options = undefined) { const e = new PerformanceMark(name, options); entries.push(e); return e; },
      measure(name, startOrOptions = undefined, endMark = undefined) {
        let start, end, detail = null, duration;
        if (startOrOptions !== null && typeof startOrOptions === 'object' && !Array.isArray(startOrOptions)) {
          const o = startOrOptions;
          if (endMark !== undefined) throw new TypeError("Failed to execute 'measure' on 'Performance': end must not be given with options");
          if (o.start === undefined && o.end === undefined && o.duration === undefined && o.detail === undefined) { start = 0; end = performance.now(); }
          else {
            if (o.start !== undefined && o.end !== undefined && o.duration !== undefined) throw new TypeError("Failed to execute 'measure' on 'Performance': start, end and duration together");
            if (o.start === undefined && o.end === undefined) throw new TypeError("Failed to execute 'measure' on 'Performance': no start nor end");
            if (o.duration !== undefined) duration = time(o.duration, 'measure');
            end = o.end !== undefined ? markTime(o.end, 'measure') : (o.start !== undefined && duration !== undefined ? markTime(o.start, 'measure') + duration : performance.now());
            start = o.start !== undefined ? markTime(o.start, 'measure') : (duration !== undefined ? end - duration : 0);
            detail = o.detail === undefined ? null : structuredClone(o.detail);
          }
        } else {
          start = startOrOptions === undefined ? 0 : markTime(startOrOptions, 'measure');
          end = endMark === undefined ? performance.now() : markTime(endMark, 'measure');
        }
        const e = entry(PerformanceMeasure, String(name), 'measure', start, end - start, detail);
        entries.push(e); return e;
      },
      getEntries() { return entries.slice().sort((a, b) => a.startTime - b.startTime); },
      getEntriesByType(type) { const t = String(type); return this.getEntries().filter(e => e.entryType === t); },
      getEntriesByName(name, type = undefined) { const x = String(name); return this.getEntries().filter(e => e.name === x && (type === undefined || e.entryType === String(type))); },
      clearMarks(name = undefined) { for (let i = entries.length - 1; i >= 0; i--) if (entries[i].entryType === 'mark' && (name === undefined || entries[i].name === String(name))) entries.splice(i, 1); },
      clearMeasures(name = undefined) { for (let i = entries.length - 1; i >= 0; i--) if (entries[i].entryType === 'measure' && (name === undefined || entries[i].name === String(name))) entries.splice(i, 1); },
      toJSON() { return { timeOrigin: performance.timeOrigin }; },
    };
    for (const [k, f] of Object.entries(methods)) define(performance, k, f);
    for (const [k, C] of Object.entries({ PerformanceEntry, PerformanceMark, PerformanceMeasure })) { setTag(C, k); def(k, C); }
  }
  // ---- The document's encoding; HTMLHyperlinkElementUtils (HTML §4.6.6) on a and area -----
  // The encoding is Lean's (op 9: the page's meta charset declaration), and is fixed once
  // read, as a document's encoding is. An element's URL is parsed with it (op 10, flag 2),
  // so a query is percent-encoded in the document's encoding.
  const docEncoding = (() => { let e; return () => e ??= (apiOn() ? apiCall(9, []) : 'UTF-8'); })();
  for (const C of [named.HTMLAnchorElement, named.HTMLAreaElement]) {
    const urlOf = el => {
      const v = el.getAttribute('href');
      if (v === null || !apiOn()) return null;
      // The element's node document's encoding: the page's, or UTF-8 for a document a
      // script made (createHTMLDocument, DOMParser).
      const r = apiCall(10, [v, document.baseURI, el.ownerDocument === document ? docEncoding() : 'UTF-8'], 3);
      return typeof r === 'string' ? r.split('\0') : null;
    };
    PARTS.forEach((k, i) => {
      const d = { get() { const u = urlOf(this); return u ? u[i] : k === 'href' ? (this.getAttribute('href') ?? '') : k === 'protocol' ? ':' : ''; },
        enumerable: true, configurable: true };
      if (k === 'href') d.set = function (v) { this.setAttribute('href', String(v)); };
      else if (k !== 'origin') d.set = function (v) {
        const u = urlOf(this);
        if (!u) return;
        const r = apiCall(11, [u[0], k, usv(v)]);
        if (typeof r === 'string') this.setAttribute('href', r.split('\0')[0]);
      };
      Object.defineProperty(C.prototype, k, d);
    });
    define(C.prototype, 'toString', function toString() { return this.href; });
  }
  // ==== end of basics ====
  def('matchMedia', q => ({ matches: false, media: String(q), addListener() {}, removeListener() {}, addEventListener() {}, removeEventListener() {} }));
  def('postMessage', () => {});
  def('focus', () => {}); def('blur', () => {}); def('close', () => {}); def('stop', () => {}); def('scrollTo', () => {}); def('scrollBy', () => {});
  def('alert', () => {}); def('confirm', () => false); def('prompt', () => null);
  def('open', () => null);
  for (const [k, v] of Object.entries({ EventTarget, Event, CustomEvent, UIEvent, MouseEvent, KeyboardEvent, FocusEvent, ErrorEvent,
    WheelEvent, PointerEvent, DOMRect, DOMRectReadOnly, CompositionEvent, InputEvent, DragEvent, HashChangeEvent, MessageEvent, StorageEvent, DeviceMotionEvent,
    DeviceOrientationEvent, BeforeUnloadEvent, TextEvent,
    PromiseRejectionEvent, Node, Element, HTMLElement, HTMLUnknownElement, SVGElement, CharacterData, Text, CDATASection, Comment,
    ProcessingInstruction, DocumentType, DocumentFragment, Document, HTMLDocument, XMLDocument, DOMImplementation, NodeList, HTMLCollection, NamedNodeMap, Attr, DOMParser, SubmitEvent,
    DOMTokenList, DOMException, AbortController, AbortSignal, Window, MutationObserver, MutationRecord, ...named })) def(k, v);

  // ==== dombreadth: markup setters, Range, StaticRange, Selection, NodeIterator, TreeWalker ====
  // The algorithms are Lean's: the HTML fragment parsing and serialization algorithms
  // (DOM.Fragment: create kind 13, node_query op 15), and the live ranges, the selection,
  // NodeIterator and TreeWalker (DOM.Range, DOM.Live, DOM.Traversal, served as node_query ops
  // from 32 by Hosts.Dom.domOp). Here: argument conversion, the objects, and the filter
  // callbacks of the page.
  const failD = code => {
    switch (code) {
      case -13: throw new DOMException('The node is of an invalid type.', 'InvalidNodeTypeError');
      case -14: throw new DOMException('The index is not in the allowed range.', 'IndexSizeError');
      case -15: throw new DOMException('The two ranges are in different documents.', 'WrongDocumentError');
      case -16: throw new DOMException('The object is in an invalid state.', 'InvalidStateError');
      default: return fail(code);
    }
  };
  const op = (id, code, s = '') => { const r = n.query(id, code, String(s)); return typeof r === 'number' ? failD(r) : r; };
  const HTML_NS = 'http://www.w3.org/1999/xhtml';
  const needArgs = (args, k, name) => { if (args.length < k) throw new TypeError(`${name}: ${k} argument${k > 1 ? 's' : ''} required`); };
  // ---- markup (DOM Parsing and Serialization; HTML §13.3, §13.4) --------------------------
  // The fragment Lean's parser makes of `markup` for a context element (namespace, local
  // name), in document `doc`; its content event handler attributes become handlers.
  const fragmentOf = (doc, ns, name, markup) => {
    const f = chk(n.create(13 + 16 * doc, (ns ?? '') + '\u0000' + name + '\u0000' + markup));
    scanHandlers(f, false);
    return f;
  };
  const contextOf = (ctx, doc) => (info(ctx, 0) !== 1 || (info(ctx, 8) === 1 && str(ctx, 0) === 'html'))
    ? [HTML_NS, 'body'] : [str(ctx, 2), str(ctx, 0)];
  const setInner = (el, v) => {
    const id = nodeId(el), f = fragmentOf(info(id, 7), str(id, 2), str(id, 0), v === null ? '' : String(v));
    const target = info(id, 8) === 1 && str(id, 0) === 'template' ? info(id, 9) : id;
    chk(n.setText(target, '')); chk(n.insert(target, f, -1));
  };
  const noModification = () => new DOMException('The node has no parent element to change.', 'NoModificationAllowedError');
  Object.defineProperties(Element.prototype, {
    innerHTML: { get() { return chk(n.query(nodeId(this), 15, '0')); }, set(v) { setInner(this, v); }, configurable: true, enumerable: true },
    outerHTML: { get() { return chk(n.query(nodeId(this), 15, '1')); }, set(v) {
      const id = nodeId(this), p = info(id, 1);
      if (p < 0) return;
      if (info(p, 0) === 9) throw noModification();
      const [ns, name] = info(p, 0) === 11 ? [HTML_NS, 'body'] : [str(p, 2), str(p, 0)];
      chk(n.replace(p, fragmentOf(info(id, 7), ns, name, v === null ? '' : String(v)), id));
    }, configurable: true, enumerable: true },
    insertAdjacentHTML: { value(position, text) {
      needArgs(arguments, 2, 'insertAdjacentHTML');
      const id = nodeId(this), pos = String(position).toLowerCase(), outside = pos === 'beforebegin' || pos === 'afterend';
      if (!outside && pos !== 'afterbegin' && pos !== 'beforeend')
        throw new DOMException(`'${position}' is not a valid position.`, 'SyntaxError');
      const ctx = outside ? info(id, 1) : id;
      if (ctx < 0 || info(ctx, 0) === 9) throw noModification();
      const [ns, name] = contextOf(ctx, info(id, 7));
      const f = fragmentOf(info(id, 7), ns, name, String(text));
      if (pos === 'beforebegin') chk(n.insert(ctx, f, id));
      else if (pos === 'afterbegin') chk(n.insert(id, f, info(id, 2)));
      else if (pos === 'beforeend') chk(n.insert(id, f, -1));
      else chk(n.insert(ctx, f, info(id, 5)));
    }, writable: true, configurable: true },
    setHTMLUnsafe: { value(html) { setInner(this, String(html)); }, writable: true, configurable: true },
    getHTML: { value() { return this.innerHTML; }, writable: true, configurable: true },
  });
  define(Document, 'parseHTMLUnsafe', html => wrap(chk(n.create(11, String(html)))));
  // ---- CharacterData changes that move live ranges (DOM §4.10, §4.11) ------------------------
  Object.defineProperties(CharacterData.prototype, {
    replaceData: { value(offset, count, data) {
      needArgs(arguments, 3, 'replaceData');
      const id = nodeId(this), old = observed.size ? str(id, 3) : null;
      op(id, 119, `${offset >>> 0} ${count >>> 0}\u0000${String(data)}`);
      if (observed.size) queueRecord('characterData', id, { oldValue: old });
    }, writable: true, configurable: true },
    appendData: { value(data) { needArgs(arguments, 1, 'appendData'); this.replaceData(this.length, 0, data); }, writable: true, configurable: true },
    insertData: { value(offset, data) { needArgs(arguments, 2, 'insertData'); this.replaceData(offset, 0, data); }, writable: true, configurable: true },
    deleteData: { value(offset, count) { needArgs(arguments, 2, 'deleteData'); this.replaceData(offset, count, ''); }, writable: true, configurable: true },
  });
  define(Text.prototype, 'splitText', function (offset) {
    const id = nodeId(this), p = info(id, 1), old = observed.size ? str(id, 3) : null;
    const k = Number(op(id, 120, String(offset >>> 0)));
    if (observed.size) { if (p >= 0) childList(p, [k], [], id, info(k, 5)); queueRecord('characterData', id, { oldValue: old }); }
    return wrap(k);
  });
  // ---- reflected IDL attributes (HTML §2.6.1): the table and the algorithms are Lean's ----
  // (DOM.Reflect). The rows of each interface are installed on its prototype when the prelude
  // runs, which the engine does once (Page.Module'.base, LeanJS.prepare) and copies for each
  // page: no page pays for it. Each get is one host call.
  const reflected = new Set();
  const finite = v => { v = Number(v); if (!Number.isFinite(v)) throw new TypeError('The provided double value is non-finite.'); return String(v); };
  const reflectConv = { s: String, n: v => v === null ? '' : String(v), u: String, b: v => (v ? '1' : '0'), i: v => String(v | 0),
    I: v => String(v | 0), U: v => String(v >>> 0), P: v => String(v >>> 0), F: v => String(v >>> 0), C: v => String(v >>> 0),
    d: finite, D: finite, e: String, E: v => (v === null || v === undefined ? '\u0001' : String(v)) };
  const reflectTokens = new WeakMap(), nonces = new WeakMap();
  const reflectInstall = C => {
    for (let P = C; P && P !== Element && !reflected.has(P); P = Object.getPrototypeOf(P)) {
      reflected.add(P);
      const rows = op(0, 162, P.name);
      for (const line of (rows ?? '').split('\u0000')) {
        if (line === '') continue;
        const [row, idl, k, content] = line.split(' ');
        if (k === 'N') {
          // nonce hiding (HTML §2.6.5): the IDL attribute is the element's internal slot, which a
          // change of the content attribute sets
          Object.defineProperty(P.prototype, idl, { get() {
            let n = nonces.get(this); const a = this.getAttribute(content);
            if (!n || n.attr !== a) nonces.set(this, n = { attr: a, value: a ?? '' });
            return n.value;
          }, set(v) { nonces.set(this, { attr: this.getAttribute(content), value: String(v) }); }, configurable: true, enumerable: true });
          continue;
        }
        if (k === 't') {
          Object.defineProperty(P.prototype, idl, { get() {
            let m = reflectTokens.get(this); if (!m) reflectTokens.set(this, m = new Map());
            let l = m.get(content); if (!l) m.set(content, l = tokenList(this, content)); return l;
          }, set(v) { this[idl].value = v; }, configurable: true, enumerable: true });
          continue;
        }
        Object.defineProperty(P.prototype, idl, {
          get() {
            const id = nodeId(this), r = op(id, 160, k === 'u' ? row + '\u0000' + (info(id, 7) === 0 ? href : 'about:blank') : row);
            switch (k) {
              case 'b': return r === '1';
              case 'i': case 'I': case 'U': case 'P': case 'F': case 'C': return Number(r);
              case 'd': case 'D': { const [lit, dflt] = r.split('\u0000'); const x = Number(lit); return Number.isFinite(x) ? x : Number(dflt); }
              case 'E': return r === '\u0001' ? null : r;
              default: return r;
            }
          },
          set(v) {
            // one host call: Lean decides and sets the content attribute (with no observer to tell
            // and no URL, whose iframe src navigates); else the decision, then setAttribute
            if (!observed.size && k !== 'u') { op(nodeId(this), 167, row + '\u0000' + reflectConv[k](v)); return; }
            const a = op(nodeId(this), 161, row + '\u0000' + reflectConv[k](v));
            if (a === 'r') this.removeAttribute(content);
            else if (a !== '') this.setAttribute(content, a.slice(1));
          },
          configurable: true, enumerable: true,
        });
      }
    }
  };
  // ---- Range and StaticRange (DOM §5) ------------------------------------------------------
  // One Range object per live range of Lean. When the engine collects a Range object, its
  // live range is released (op 118): Lean stops moving it, and a new range takes its slot.
  // An engine without WeakRef keeps every range.
  const weakRanges = typeof WeakRef === 'function' && typeof FinalizationRegistry === 'function';
  const rangeObjects = new Map(), rangeNumbers = new WeakMap();
  const rangeGone = weakRanges ? new FinalizationRegistry(k => {
    const w = rangeObjects.get(k);
    if (w && w.deref()) return;
    rangeObjects.delete(k); n.query(k, 118, '');
  }) : null;
  const rid = r => { const k = rangeNumbers.get(r); if (k === undefined) throw new TypeError("parameter is not of type 'Range'"); return k; };
  const rangeOf = k => {
    const w = rangeObjects.get(k);
    let r = weakRanges ? w?.deref() : w;
    if (!r) {
      r = Object.create(Range.prototype); rangeNumbers.set(r, k);
      if (weakRanges) { rangeObjects.set(k, new WeakRef(r)); rangeGone.register(r, k); } else rangeObjects.set(k, r);
    }
    return r;
  };
  const boundsOf = k => op(k, 101).split(' ').map(Number);
  const point = (node, offset) => nodeId(node) + ' ' + (offset >>> 0);
  class AbstractRange { constructor() { throw new TypeError('Illegal constructor'); } }
  class Range extends AbstractRange {
    constructor() { return rangeOf(Number(op(nodeId(document), 100))); }
    get startContainer() { return wrap(boundsOf(rid(this))[0]); }
    get startOffset() { return boundsOf(rid(this))[1]; }
    get endContainer() { return wrap(boundsOf(rid(this))[2]); }
    get endOffset() { return boundsOf(rid(this))[3]; }
    get collapsed() { const b = boundsOf(rid(this)); return b[0] === b[2] && b[1] === b[3]; }
    get commonAncestorContainer() { return wrap(Number(op(rid(this), 110))); }
    setStart(node, offset) { needArgs(arguments, 2, 'setStart'); op(rid(this), 102, '1 ' + point(node, offset)); }
    setEnd(node, offset) { needArgs(arguments, 2, 'setEnd'); op(rid(this), 102, '0 ' + point(node, offset)); }
    setStartBefore(node) { op(rid(this), 103, '0 ' + nodeId(node)); }
    setStartAfter(node) { op(rid(this), 103, '1 ' + nodeId(node)); }
    setEndBefore(node) { op(rid(this), 103, '2 ' + nodeId(node)); }
    setEndAfter(node) { op(rid(this), 103, '3 ' + nodeId(node)); }
    collapse(toStart = false) { op(rid(this), 104, toStart ? '1' : '0'); }
    selectNode(node) { op(rid(this), 105, '0 ' + nodeId(node)); }
    selectNodeContents(node) { op(rid(this), 105, '1 ' + nodeId(node)); }
    compareBoundaryPoints(how, sourceRange) {
      needArgs(arguments, 2, 'compareBoundaryPoints');
      const h = Number(how) & 0xFFFF;
      return Number(op(rid(this), 106, h + ' ' + rid(sourceRange)));
    }
    deleteContents() { op(rid(this), 112, '0'); }
    extractContents() { return wrap(Number(op(rid(this), 112, '1'))); }
    cloneContents() { const f = Number(op(rid(this), 112, '2')); scanHandlers(f, false); return wrap(f); }
    insertNode(node) { op(rid(this), 113, String(nodeId(node))); }
    surroundContents(newParent) { op(rid(this), 114, String(nodeId(newParent))); }
    cloneRange() { return rangeOf(Number(op(rid(this), 115))); }
    detach() {}
    isPointInRange(node, offset) { needArgs(arguments, 2, 'isPointInRange'); return op(rid(this), 108, point(node, offset)) === '1'; }
    comparePoint(node, offset) { needArgs(arguments, 2, 'comparePoint'); return Number(op(rid(this), 107, point(node, offset))); }
    intersectsNode(node) { needArgs(arguments, 1, 'intersectsNode'); return op(rid(this), 109, String(nodeId(node))) === '1'; }
    toString() { return op(rid(this), 111); }
    createContextualFragment(fragment) { needArgs(arguments, 1, 'createContextualFragment'); const f = Number(op(rid(this), 116, String(fragment))); scanHandlers(f, false); return wrap(f); }
    // CSSOM View §6.1: the boxes of the range's common ancestor element in Lean's layout.
    getBoundingClientRect() { let k = Number(op(rid(this), 110)); if (info(k, 0) !== 1) k = info(k, 1); if (k < 0 || info(k, 0) !== 1) return new DOMRect(0, 0, 0, 0); return wrap(k).getBoundingClientRect(); }
    getClientRects() { const r = this.getBoundingClientRect(); return r.width === 0 && r.height === 0 ? [] : [r]; }
  }
  const howConsts = { START_TO_START: 0, START_TO_END: 1, END_TO_END: 2, END_TO_START: 3 };
  consts(Range, howConsts); consts(Range.prototype, howConsts);
  const staticState = new WeakMap();
  class StaticRange extends AbstractRange {
    constructor(init) {
      if (init === null || init === undefined || typeof init !== 'object') throw new TypeError("Failed to construct 'StaticRange': 1 argument required");
      for (const k of ['startContainer', 'startOffset', 'endContainer', 'endOffset'])
        if (init[k] === undefined) throw new TypeError(`StaticRangeInit: required member ${k} is undefined`);
      const sc = init.startContainer, ec = init.endContainer;
      if (!(sc instanceof Node) || !(ec instanceof Node)) throw new TypeError("member startContainer is not of type 'Node'");
      if (sc.nodeType === 10 || sc.nodeType === 2 || ec.nodeType === 10 || ec.nodeType === 2) failD(-13);
      const o = Object.create(StaticRange.prototype);
      staticState.set(o, { sc, so: init.startOffset >>> 0, ec, eo: init.endOffset >>> 0 });
      return o;
    }
    get startContainer() { return staticState.get(this).sc; }
    get startOffset() { return staticState.get(this).so; }
    get endContainer() { return staticState.get(this).ec; }
    get endOffset() { return staticState.get(this).eo; }
    get collapsed() { const s = staticState.get(this); return s.sc === s.ec && s.so === s.eo; }
  }
  // ---- Selection (Selection API): one per document with a browsing context ----------------
  class Selection { constructor() { throw new TypeError('Illegal constructor'); } }
  const selection = Object.create(Selection.prototype);
  const selState = () => { const r = op(0, 140); if (r === null) return null; const [k, dir] = r.split(' ').map(Number); return { k, dir, b: boundsOf(k) }; };
  const collapsedB = b => b[0] === b[2] && b[1] === b[3];
  // Selection API §3: a change of the selection queues a task to fire selectionchange at the
  // document (one per change seen; none when the selection is as it was).
  const selKey = () => { const s = selState(); return s ? s.dir + ' ' + s.b.join(' ') : ''; };
  let selQueued = false;
  const selChanging = f => function (...args) {
    const before = selKey(), r = f.apply(this, args);
    if (!selQueued && selKey() !== before) {
      selQueued = true;
      setTimeout(() => { selQueued = false; const e = new Event('selectionchange'); state(e).trusted = true; dispatch(document, e); }, 0);
    }
    return r;
  };
  for (const [k, f] of Object.entries({
    getRangeAt(index) { needArgs(arguments, 1, 'getRangeAt'); const s = selState(); if (!s || (index >>> 0) !== 0) failD(-14); return rangeOf(s.k); },
    addRange(range) { needArgs(arguments, 1, 'addRange'); op(rid(range), 141); },
    removeRange(range) { needArgs(arguments, 1, 'removeRange'); op(rid(range), 142); },
    removeAllRanges() { op(0, 143); },
    empty() { op(0, 143); },
    collapse(node, offset = 0) { needArgs(arguments, 1, 'collapse'); if (node === null) { op(0, 143); return; } op(0, 144, point(node, offset)); },
    setPosition(node, offset = 0) { needArgs(arguments, 1, 'setPosition'); if (node === null) { op(0, 143); return; } op(0, 144, point(node, offset)); },
    collapseToStart() { op(0, 145, '1'); },
    collapseToEnd() { op(0, 145, '0'); },
    extend(node, offset = 0) { needArgs(arguments, 1, 'extend'); op(0, 146, point(node, offset)); },
    setBaseAndExtent(anchorNode, anchorOffset, focusNode, focusOffset) {
      needArgs(arguments, 4, 'setBaseAndExtent'); op(0, 147, point(anchorNode, anchorOffset) + ' ' + point(focusNode, focusOffset)); },
    selectAllChildren(node) { needArgs(arguments, 1, 'selectAllChildren'); op(0, 148, String(nodeId(node))); },
    deleteFromDocument() { op(0, 149); },
    containsNode(node, allowPartialContainment = false) { needArgs(arguments, 1, 'containsNode'); return op(0, 150, nodeId(node) + ' ' + (allowPartialContainment ? 1 : 0)) === '1'; },
    modify() {},
    getComposedRanges() { const s = selState(); return s ? [new StaticRange({ startContainer: wrap(s.b[0]), startOffset: s.b[1], endContainer: wrap(s.b[2]), endOffset: s.b[3] })] : []; },
    toString() { const s = selState(); return s ? op(s.k, 111) : ''; },
  })) define(Selection.prototype, k, ['addRange', 'removeRange', 'removeAllRanges', 'empty', 'collapse', 'setPosition', 'collapseToStart',
    'collapseToEnd', 'extend', 'setBaseAndExtent', 'selectAllChildren', 'deleteFromDocument'].includes(k) ? selChanging(f) : f);
  for (const [k, f] of Object.entries({
    anchorNode() { const s = selState(); return s ? wrap(s.dir === 2 ? s.b[2] : s.b[0]) : null; },
    anchorOffset() { const s = selState(); return s ? (s.dir === 2 ? s.b[3] : s.b[1]) : 0; },
    focusNode() { const s = selState(); return s ? wrap(s.dir === 2 ? s.b[0] : s.b[2]) : null; },
    focusOffset() { const s = selState(); return s ? (s.dir === 2 ? s.b[1] : s.b[3]) : 0; },
    isCollapsed() { const s = selState(); return !s || collapsedB(s.b); },
    rangeCount() { return selState() ? 1 : 0; },
    type() { const s = selState(); return !s ? 'None' : collapsedB(s.b) ? 'Caret' : 'Range'; },
    direction() { const s = selState(); return !s || collapsedB(s.b) || s.dir === 0 ? 'none' : s.dir === 2 ? 'backward' : 'forward'; },
  })) Object.defineProperty(Selection.prototype, k, { get: f, configurable: true, enumerable: true });
  const getSelection = function () { return this === undefined || this === window || this === document ? selection : null; };
  define(Document.prototype, 'getSelection', function () { return this === document ? selection : null; });
  // ---- NodeIterator and TreeWalker (DOM §6) -------------------------------------------------
  const NodeFilter = function NodeFilter() { throw new TypeError('Illegal constructor'); };
  consts(NodeFilter, { FILTER_ACCEPT: 1, FILTER_REJECT: 2, FILTER_SKIP: 3, SHOW_ALL: 0xFFFFFFFF, SHOW_ELEMENT: 0x1,
    SHOW_ATTRIBUTE: 0x2, SHOW_TEXT: 0x4, SHOW_CDATA_SECTION: 0x8, SHOW_ENTITY_REFERENCE: 0x10, SHOW_ENTITY: 0x20,
    SHOW_PROCESSING_INSTRUCTION: 0x40, SHOW_COMMENT: 0x80, SHOW_DOCUMENT: 0x100, SHOW_DOCUMENT_TYPE: 0x200,
    SHOW_DOCUMENT_FRAGMENT: 0x400, SHOW_NOTATION: 0x800 });
  const traversers = new WeakMap();
  const tstate = t => { const s = traversers.get(t); if (!s) throw new TypeError('Illegal invocation'); return s; };
  // "Filter" (DOM §6) for a node that whatToShow shows (Lean passed over the others).
  const filterNode = (st, node) => {
    if (st.active) failD(-16);
    const f = st.filter;
    if (f === null || f === undefined) return 1;
    st.active = true;
    try {
      let r;
      if (typeof f === 'function') r = f.call(undefined, node);
      else { const m = f.acceptNode; if (typeof m !== 'function') throw new TypeError('NodeFilter.acceptNode is not a function'); r = m.call(f, node); }
      return Number(r) & 0xFFFF;
    } finally { st.active = false; }
  };
  class NodeIterator { constructor() { throw new TypeError('Illegal constructor'); } }
  const iterate = (it, next) => {
    const st = tstate(it);
    let [node, before] = op(st.k, 133).split(' ').map(Number);
    for (;;) {
      const r = op(st.k, 131, `${next ? 1 : 0} ${node} ${before}`);
      if (r === null) return null;
      [node, before] = r.split(' ').map(Number);
      // the node being filtered moves as the reference does if the filter removes nodes
      // (Lean's pre-removing steps); accepted, it becomes the reference as moved
      op(st.k, 136, `${node} ${before}`);
      let res;
      try { res = filterNode(st, wrap(node)); } catch (e) { op(st.k, 136, ''); throw e; }
      if (res === 1) { op(st.k, 137); return wrap(node); }
      op(st.k, 136, '');
    }
  };
  for (const [k, f] of Object.entries({
    nextNode() { return iterate(this, true); },
    previousNode() { return iterate(this, false); },
    detach() {},
  })) define(NodeIterator.prototype, k, f);
  for (const [k, f] of Object.entries({
    root() { return tstate(this).root; },
    whatToShow() { return tstate(this).whatToShow; },
    filter() { return tstate(this).filter; },
    referenceNode() { return wrap(Number(op(tstate(this).k, 133).split(' ')[0])); },
    pointerBeforeReferenceNode() { return op(tstate(this).k, 133).split(' ')[1] === '1'; },
  })) Object.defineProperty(NodeIterator.prototype, k, { get: f, configurable: true, enumerable: true });
  class TreeWalker { constructor() { throw new TypeError('Illegal constructor'); } }
  // A method of the walker: Lean's machine (Traversal.run) stops at each node to filter.
  const walk = (tw, m) => {
    const st = tstate(tw);
    let a = op(st.cur, 134, `${m} ${st.rootId} ${st.whatToShow}`);
    for (;;) {
      const p = a.split(' ');
      if (p[0] === 'd') { const k = Number(p[1]); if (k < 0) return null; st.cur = k; return wrap(k); }
      const r = filterNode(st, wrap(Number(p[1])));
      a = op(0, 135, p.slice(2).join(' ') + ' ' + r);
    }
  };
  ['parentNode', 'firstChild', 'lastChild', 'previousSibling', 'nextSibling', 'previousNode', 'nextNode']
    .forEach((name, m) => define(TreeWalker.prototype, name, function () { return walk(this, m); }));
  for (const [k, f] of Object.entries({
    root() { return tstate(this).root; },
    whatToShow() { return tstate(this).whatToShow; },
    filter() { return tstate(this).filter; },
  })) Object.defineProperty(TreeWalker.prototype, k, { get: f, configurable: true, enumerable: true });
  Object.defineProperty(TreeWalker.prototype, 'currentNode', { get() { return wrap(tstate(this).cur); },
    set(node) { tstate(this).cur = nodeId(node); }, configurable: true, enumerable: true });
  Object.defineProperties(Document.prototype, {
    createRange: { value() { return rangeOf(Number(op(nodeId(this), 100))); }, writable: true, configurable: true },
    createNodeIterator: { value(root, whatToShow = 0xFFFFFFFF, filter = null) {
      needArgs(arguments, 1, 'createNodeIterator');
      const id = nodeId(root), w = whatToShow >>> 0;
      const it = Object.create(NodeIterator.prototype);
      traversers.set(it, { k: Number(op(id, 130, String(w))), root, whatToShow: w, filter, active: false });
      return it;
    }, writable: true, configurable: true },
    createTreeWalker: { value(root, whatToShow = 0xFFFFFFFF, filter = null) {
      needArgs(arguments, 1, 'createTreeWalker');
      const id = nodeId(root), tw = Object.create(TreeWalker.prototype);
      traversers.set(tw, { rootId: id, root, cur: id, whatToShow: whatToShow >>> 0, filter, active: false });
      return tw;
    }, writable: true, configurable: true },
  });
  // ---- getComputedStyle (CSSOM §9): Lean's cascade (Rendering.CSS, the cascade alone, op 20)
  // and Lean's layout for the used width and height (op 21). Live: each read asks again; the
  // engine keeps one cascade and one layout per DOM version, and a read of a style property
  // makes no layout.
  class CSSStyleDeclaration { constructor() { throw new TypeError('Illegal constructor'); } }
  // The property names of Lean's computed style, in Lean's order (op 20's answer), once.
  let computedNames = null;
  const namesOf = r => { const xs = r.split('\u0000'), out = []; for (let i = 0; i + 1 < xs.length; i += 2) out.push(xs[i]); return out; };
  const namesFor = el => {
    if (computedNames === null) { const r = n.query(nodeId(el), 20, ''); if (typeof r !== 'string' || r === '') return []; computedNames = namesOf(r); }
    return computedNames;
  };
  const camel = name => name.replace(/-([a-z])/g, (m, c) => c.toUpperCase());
  const computedValue = (el, name) => {
    const id = nodeId(el);
    if (namesFor(el).length === 0) return '';
    const k = computedNames.indexOf(name);
    if (k < 0) return '';
    if (name === 'width' || name === 'height') {
      const d = n.query(id, 200 + computedNames.indexOf('display'), '');
      const u = d !== 'none' ? n.query(id, 21, '') : '';
      if (typeof u === 'string' && u !== '') return u.split(' ')[name === 'width' ? 0 : 1] + 'px';
    }
    const r = n.query(id, 200 + k, '');
    return typeof r === 'string' ? r : '';
  };
  const computedValues = el => {
    const r = n.query(nodeId(el), 20, ''), m = new Map();
    if (typeof r !== 'string') return m;
    const xs = r.split('\u0000');
    for (let i = 0; i + 1 < xs.length; i += 2) m.set(xs[i], xs[i + 1]);
    if (m.get('display') !== 'none') {
      const u = n.query(nodeId(el), 21, '');
      if (typeof u === 'string' && u !== '') { const [w, h] = u.split(' '); m.set('width', w + 'px'); m.set('height', h + 'px'); }
    }
    return m;
  };
  const cssName = p => p.startsWith('--') ? p : p.replace(/[A-Z]/g, c => '-' + c.toLowerCase()).replace(/^webkit-/, '-webkit-');
  const readOnlyDecl = () => new DOMException('The computed style declaration is read-only.', 'NoModificationAllowedError');
  const computedStyle = el => {
    const target = Object.create(CSSStyleDeclaration.prototype);
    const methods = {
      getPropertyValue: name => computedValue(el, String(name).startsWith('--') ? String(name) : String(name).toLowerCase()),
      getPropertyPriority: () => '',
      setProperty: () => { throw readOnlyDecl(); },
      removeProperty: () => { throw readOnlyDecl(); },
      item: i => namesFor(el)[i >>> 0] ?? '',
    };
    return new Proxy(target, {
      get(t, p) {
        if (typeof p !== 'string') return Reflect.get(t, p);
        if (Object.prototype.hasOwnProperty.call(methods, p)) return methods[p];
        if (p === 'length') return namesFor(el).length;
        if (p === 'cssText') return '';
        if (p === 'parentRule') return null;
        if (/^(0|[1-9][0-9]*)$/.test(p)) return namesFor(el)[Number(p)];
        if (p === 'cssFloat') return computedValue(el, 'float');
        if (p in t) return Reflect.get(t, p);
        return computedValue(el, p.includes('-') ? p : cssName(p));
      },
      set() { throw readOnlyDecl(); },
      // every property Lean computes is a property of the declaration, dashed and camel-cased
      has(t, p) {
        if (typeof p !== 'string') return Reflect.has(t, p);
        if (p in t || p === 'length' || p === 'cssText' || p === 'cssFloat' || Object.prototype.hasOwnProperty.call(methods, p)) return true;
        const xs = namesFor(el);
        if (/^(0|[1-9][0-9]*)$/.test(p)) return Number(p) < xs.length;
        return xs.includes(p) || xs.includes(cssName(p));
      },
      ownKeys(t) { const xs = namesFor(el); return [...xs.keys()].map(String).concat(Reflect.ownKeys(t)); },
      getOwnPropertyDescriptor(t, p) {
        if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p) && Number(p) < namesFor(el).length)
          return { value: namesFor(el)[Number(p)], enumerable: true, configurable: true, writable: false };
        return Reflect.getOwnPropertyDescriptor(t, p);
      },
    });
  };
  define(CSSStyleDeclaration.prototype, Symbol.iterator, function* () { for (let i = 0; i < this.length; i++) yield this[i]; });
  // ---- the CSS namespace (CSS Conditional 3 §8.1, CSSOM §2.1): Lean's answers -------------
  const CSSns = {};
  define(CSSns, 'supports', function (a, b) {
    if (arguments.length < 1) throw new TypeError('CSS.supports: 1 argument required');
    return op(0, 165, arguments.length >= 2 ? '1\u0000' + String(a) + '\u0000' + String(b) : '0\u0000' + String(a)) === '1';
  });
  define(CSSns, 'escape', function (ident) {
    if (arguments.length < 1) throw new TypeError('CSS.escape: 1 argument required');
    return op(0, 166, String(ident));
  });
  Object.defineProperty(CSSns, Symbol.toStringTag, { value: 'CSS', configurable: true });
  def('CSS', CSSns);
  // ---- document.fonts (CSS Font Loading 3 §2): the fonts a page uses are held before its
  // scripts run, and a page can not add font faces here, so the set is empty and loaded ----
  const fontKey = {};
  class FontFaceSet extends EventTarget {
    constructor(key) { if (key !== fontKey) throw new TypeError('Illegal constructor'); super(); }
    get status() { return 'loaded'; }
    get size() { return 0; }
    get ready() { return fontsReady; }
    check(font, text = ' ') { if (arguments.length < 1) throw new TypeError('check: 1 argument required'); return true; }
    load(font, text = ' ') { if (arguments.length < 1) throw new TypeError('load: 1 argument required'); return Promise.resolve([]); }
    has() { return false; }
    add() { return this; }
    delete() { return false; }
    clear() {}
    forEach() {}
    *entries() {} *keys() {} *values() {}
  }
  define(FontFaceSet.prototype, Symbol.iterator, FontFaceSet.prototype.values);
  Object.defineProperty(FontFaceSet.prototype, Symbol.toStringTag, { value: 'FontFaceSet', configurable: true });
  addHandlers(FontFaceSet.prototype);
  const fontSet = new FontFaceSet(fontKey), fontsReady = Promise.resolve(fontSet);
  Object.defineProperty(Document.prototype, 'fonts', { get() { return fontSet; }, configurable: true, enumerable: true });
  def('FontFaceSet', FontFaceSet);
  def('getComputedStyle', (el, pseudo) => {
    if (!(el instanceof Element)) throw new TypeError("Failed to execute 'getComputedStyle': parameter 1 is not of type 'Element'.");
    return computedStyle(el);
  });
  def('getSelection', getSelection);
  for (const C of new Set([HTMLElement, HTMLUnknownElement, ...Object.values(named)])) reflectInstall(C);
  for (const [k, v] of Object.entries({ AbstractRange, Range, StaticRange, Selection, NodeFilter, NodeIterator, TreeWalker, CSSStyleDeclaration })) {
    if (k !== 'NodeFilter') Object.defineProperty(v.prototype, Symbol.toStringTag, { value: k, configurable: true });
    def(k, v);
  }
  // ==== end dombreadth ====

  // Content event handler attributes (HTML §8.1.8.1): onclick="..." and <body onload>.
  // The event handler content attributes of the elements of a subtree (a page's, or a clone's:
  // a clone's attributes are set by Lean, not through setAttribute).
  const scanHandlers = (root, inclusive) => {
    for (const k of inclusive && info(root, 0) === 1 ? [root, ...elementsOf(root)] : elementsOf(root)) {
      if (info(k, 8) !== 1) continue;
      const a = str(k, 6) ?? ''; const xs = a === '' ? [] : a.split('\u0000');
      for (let i = 0; i + 1 < xs.length; i += 2) if (/^on[a-z]+$/.test(xs[i])) contentHandler(wrap(k), xs[i].slice(2), xs[i + 1]);
    }
  };
  const contentHandler = (el, name, source) => {
    if (!handlerNames.includes(name)) return;
    const onBody = windowReflecting(el) && bodyWindowHandlers.has(name);
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
      const C = type.startsWith('pointer') ? PointerEvent : type === 'click' || type.startsWith('mouse') ? MouseEvent : Event;
      const init = { bubbles: (flags & 1) !== 0, cancelable: (flags & 2) !== 0, composed: (flags & 4) !== 0, view: window };
      // The pointer's coordinates, buttons and pointer fields, as Lean gives them.
      let data = {};
      if (C !== Event) { const s = n.query(0, 16, ''); if (typeof s === 'string' && s !== '') { try { data = JSON.parse(s); } catch {} } }
      const e = new C(type, Object.assign({}, data, init));
      for (const k of ['pageX', 'pageY', 'offsetX', 'offsetY', 'movementX', 'movementY']) if (typeof data[k] === 'number') state(e)[k] = data[k];
      state(e).trusted = true;
      if (type === 'DOMContentLoaded') readyState = 'interactive';
      if (type === 'load' && target === WINDOW) readyState = 'complete';
      return dispatch(wrapTarget(target), e) ? '' : 'prevented';
    },
    report(e) { report(e); },
    // A page starts: the content event handler attributes of its elements. The host may
    // run the prelude once on an empty document and copy that state for each page.
    start() { scanHandlers(0, false); },
    script(id) { currentScript = id < 0 ? null : wrap(id); },
    url(u) { href = String(u); },
    release(id) { callbacks.delete(id); },
  };
})
