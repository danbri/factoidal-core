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
  // The globals of the language itself, before any page object (section workers keeps
  // them in a worker's global scope).
  const esGlobals = new Set(Object.getOwnPropertyNames(globalThis));
  // The natives, with every change of the tree also queued as a mutation record (DOM §4.3)
  // for MutationObserver. The change itself is Lean's; this only reports it.
  const n = Object.create(n0); // the natives are not enumerable: inherit them
  const WINDOW = 0x0FFFFFFF;
  let nextTarget = 0x10000000;
  const define = (o, name, value) => Object.defineProperty(o, name, { value, writable: true, configurable: true });
  // Trusted Types (section trustedtypes): these stay null until the page uses Trusted Types or
  // one of its documents has a policy that asks for them, so other pages pay one comparison.
  // ttAttr(element, namespace, name, value) and ttValue(type, node id or null, value, sink)
  // answer the string that may reach the sink, or throw.
  let ttAttr = null, ttValue = null, ttMeta = null, ttStart = null, ttDoc = null;
  // `new FormData(form, submitter)`: the entry list of a form (section forms; Lean's
  // HTML.FormEntries). Null in a worker, where there are no forms.
  let formEntryList = null;
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
  // The interface of an SVG element by its local name (the SVG DOM section assigns it).
  let svgProtoOf = null;
  const make = id => {
    const t = info(id, 0);
    if (t < 0) return null;
    const o = Object.create(protoOf(id, t));
    ids.set(o, id); wrappers.set(id, o);
    return o;
  };
  const isElement = x => x instanceof Element;
  // An HTML element (DOM §4.9: an element in the HTML namespace), in a document of either
  // type. node_info 8 answers 1 only in an HTML document (where names are lower-cased), so an
  // element of an XML document is asked for its namespace.
  const XHTML_NS = 'http://www.w3.org/1999/xhtml';
  const htmlEl = k => info(k, 8) === 1 || (info(k, 0) === 1 && n.str(k, 2) === XHTML_NS);
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
  // WebIDL: two required `double` arguments (TypeError when missing or not finite).
  const pointArgs = (args, what) => {
    if (args.length < 2) throw new TypeError(`Failed to execute '${what}' on 'Document': 2 arguments required, but only ${args.length} present.`);
    if (!Number.isFinite(Number(args[0])) || !Number.isFinite(Number(args[1]))) throw new TypeError(`Failed to execute '${what}' on 'Document': The provided double value is non-finite.`);
  };
  const inViewport = (x, y) => { const [w, h] = viewport(); return x >= 0 && y >= 0 && x < w && y < h; };
  const pointHits = (x, y) => {
    const px = Math.floor(Number(x)), py = Math.floor(Number(y)), [w, h] = viewport();
    if (!(px >= 0 && py >= 0 && px < w && py < h && px < 65536 && py < 65536)) return [];
    const s = n.query(px * 65536 + py, 35, '');
    return typeof s === 'string' && s !== '' ? s.split(' ').map(k => wrap(Number(k))) : [];
  };
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
    // With shadow trees, Lean filters the path for the current target (node_query 31).
    composedPath() {
      const s = state(this);
      if (!s.dispatching) return [];
      if (!s.pathIds) return s.path.slice();
      const c = s.currentTarget === null ? 0 : idOf(s.currentTarget), r = n.query(c, 31, s.pathIds.join(' '));
      return typeof r === 'string' ? (r === '' ? [] : r.split(' ').map(x => wrapTarget(Number(x)))) : s.path.slice();
    }
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
      s.ranges = Array.isArray(d.ranges) ? d.ranges : Array.isArray(d.targetRanges) ? d.targetRanges : [];
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
  let windowOfScript = () => window, frameLoad = () => {};
  // A worker's global scope sends an error that no listener canceled to its Worker object
  // (section workers); a window logs it.
  let uncaughtHook = null;
  const report = e => {
    const message = e instanceof Error ? `${e.name}: ${e.message}` : 'Uncaught ' + String(e);
    if (reporting) { n.log('Uncaught (in error handler) ' + message); return; }
    const stack = e instanceof Error && typeof e.stack === 'string' ? e.stack.split('\n').slice(0, 3).join(' | ') : '';
    reporting = true;
    try {
      // no source positions are kept: the document's URL (right for an inline script), line 0
      let filename = '';
      try { filename = String(windowOfScript().location.href); } catch (_) {}
      const event = new ErrorEvent('error', { message, error: e, cancelable: true, filename, lineno: 0, colno: 0 });
      state(event).trusted = true;
      const notCanceled = dispatch(windowOfScript(), event);
      if (notCanceled) { if (uncaughtHook) uncaughtHook(message, e); else n.log('Uncaught ' + message + (stack ? ' at ' + stack : '')); }
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
    // With shadow trees (flag 4, an engine with DOM.Shadow): the path goes through slots
    // and shadow roots, and each call has a fifth number, the target that listener sees
    // (DOM §2.5 retargeting; Dispatch.planAt).
    const sh = shadowEngine();
    const plan = chk(n.plan(tid, s.type, (s.bubbles ? 1 : 0) | (s.composed ? 2 : 0) | (sh ? 4 : 0)));
    const k = plan[0], step = sh ? 5 : 4;
    s.path = []; for (let i = 1; i <= k; i++) s.path.push(wrapTarget(plan[i]));
    s.pathIds = sh ? plan.slice(1, k + 1) : null;
    let stopAt = null;
    for (let i = k + 1; i + step - 1 < plan.length; i += step) {
      const cb = plan[i], node = plan[i + 1], phase = plan[i + 2] & 7, capture = (plan[i + 2] & 8) !== 0, depth = plan[i + 3];
      if (sh) s.target = plan[i + 4] < 0 ? null : wrapTarget(plan[i + 4]);
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
    // DOM §2.9 steps 6 and 10: the target is the one at the target; it is cleared when it is
    // in a shadow tree.
    if (sh) s.target = tid < WINDOW && info(info(tid, 28), 22) >= 0 ? null : target;
    if (act !== null) { if (s.canceled) canceledActivation(act, actState); else activation(act, tid); }
    return !s.canceled;
  };
  const wrapTarget = id => id === WINDOW ? window : (id >= 0x10000000 ? targets.get(id) ?? null : wrap(id));
  const targets = new Map();
  let globalEvent = undefined;

  // `ceActive`: a custom element is defined (section customelements), so attribute and tree
  // changes go through the natives that tell custom elements.
  let htmlConstructing = false, ceActive = false;
  // A script element that a script made (section dynscripts): told when it is created.
  let noteFreshScript = () => {};
  // Connected (DOM §4.2.2): the shadow-including root is a document (node_info 25).
  const connectedId = id => { if (id < 0) return false; if (shadowEngine()) return info(id, 25) === 1; for (let k = id, i = 0; i < 1 << 20; i++) { const p = info(k, 1); if (p < 0) return k === 0; k = p; } return false; };
  class EventTarget {
    constructor() { if (htmlConstructing) return; const id = nextTarget++; ids.set(this, id); targets.set(id, this); }
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
    'afterprint', 'beforeprint', 'languagechange', 'messageerror', 'slotchange', 'beforetoggle', 'command', 'invalid',
    // the rest of GlobalEventHandlers and WindowEventHandlers (HTML §8.1.8.2)
    'auxclick', 'beforeinput', 'beforematch', 'canplay', 'canplaythrough', 'contextlost', 'contextrestored', 'copy',
    'cuechange', 'cut', 'drag', 'dragend', 'dragenter', 'dragleave', 'dragover', 'dragstart', 'drop', 'durationchange',
    'emptied', 'ended', 'formdata', 'loadeddata', 'loadedmetadata', 'loadstart', 'paste', 'pause', 'play', 'playing',
    'progress', 'ratechange', 'scrollend', 'securitypolicyviolation', 'seeked', 'seeking', 'stalled', 'suspend',
    'timeupdate', 'volumechange', 'waiting', 'webkitanimationend', 'webkitanimationiteration', 'webkitanimationstart',
    'webkittransitionend', 'pagereveal', 'pageswap'];
  // The event type of a handler: the attribute's name without "on", except the prefixed
  // animation events, whose types are in camel case (HTML §8.1.8.2).
  const handlerTypes = { webkitanimationend: 'webkitAnimationEnd', webkitanimationiteration: 'webkitAnimationIteration',
    webkitanimationstart: 'webkitAnimationStart', webkittransitionend: 'webkitTransitionEnd' };
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
      addListener(t, handlerTypes[name] ?? name, function (event) {
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
    'popstate', 'rejectionhandled', 'storage', 'unhandledrejection', 'unload', 'pagereveal', 'pageswap']);
  const windowReflecting = el => el instanceof HTMLElement && (el.localName === 'body' || el.localName === 'frameset');
  // The window a body or frameset element's window-reflecting handlers belong to (HTML
  // §8.1.8.1): its own document's. For a same-origin frame's document that is the frame's
  // window target, not the page's window (whose handlers a frame's `<body onload>` replaced).
  const bodyWindow = el => { const d = info(nodeId(el), 7); return d > 0 ? frameTarget(d) : window; };
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
    constructor() { if (!htmlConstructing) throw new TypeError('Illegal constructor'); super(); }
    get nodeType() { return info(nodeId(this), 0); }
    get nodeName() { return str(nodeId(this), 1); }
    // A node of a frame's document loaded from a URL has that URL as base (node_query 171
    // answers for a frame document this page may reach); an about:blank or about:srcdoc
    // frame document, and a document a script made, take the page's (HTML §2.4.1 fallback
    // base URL), as before.
    get baseURI() { const id = nodeId(this), d = info(id, 0) === 9 ? id : info(id, 7); if (d > 0) { const r = n.query(d, 171, ''); if (typeof r === 'string' && !r.startsWith('about:')) return r; } return document.URL; }
    get isConnected() { if (shadowEngine()) return info(nodeId(this), 25) === 1; let k = nodeId(this); for (let i = 0; i < 1 << 20; i++) { const p = info(k, 1); if (p < 0) return k === 0; k = p; } return false; }
    get ownerDocument() { const id = nodeId(this); return info(id, 0) === 9 ? null : wrap(info(id, 7)); }
    getRootNode(options = {}) { if (shadowEngine()) return wrap(info(nodeId(this), options?.composed ? 24 : 28)); let k = nodeId(this); for (;;) { const p = info(k, 1); if (p < 0) return wrap(k); k = p; } }
    get parentNode() { return wrap(info(nodeId(this), 1)); }
    get parentElement() { const p = info(nodeId(this), 1); return p >= 0 && info(p, 0) === 1 ? wrap(p) : null; }
    hasChildNodes() { return info(nodeId(this), 6) > 0; }
    get childNodes() {
      let l = listCache.get(this);
      // the node's number is read at each use: a frame's Document object takes the number of
      // the document that document.close() made
      if (!l) { nodeId(this); l = liveList(() => kids(nodeId(this))); listCache.set(this, l); }
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
      const k = String(name), v = ttAttr === null ? String(value) : ttAttr(this, null, k, value);
      chk(n.setAttr(nodeId(this), k, v));
      // An event handler content attribute: a name that starts with "on", in any case.
      if (k.length >= 2 && (k.charCodeAt(0) | 32) === 111 && (k.charCodeAt(1) | 32) === 110)
        contentHandler(this, k.toLowerCase().slice(2), v);
    }
    setAttributeNS(ns, name, value) {
      if (arguments.length < 3) throw new TypeError('setAttributeNS: 3 arguments required');
      const q = String(name);
      chk(n.setAttr(nodeId(this), nsArg(ns) + '\u0000' + q, ttAttr === null ? String(value) : ttAttr(this, nsArg(ns), q, value)));
    }
    removeAttribute(name) {
      const k = lowerIfHtml(this, String(name)), a = attrNodes(this).find(x => x.name === k);
      if (a) detachAttr(a);
      chk(n.removeAttr(nodeId(this), String(name)));
      // Removing an event handler content attribute deactivates the handler (HTML §8.1.8.1).
      if (a && k.startsWith('on') && handlerNames.includes(k.slice(2)) && (this instanceof HTMLElement || this instanceof SVGElement || this instanceof MathMLElement))
        setHandler(windowReflecting(this) && bodyWindowHandlers.has(k.slice(2)) ? bodyWindow(this) : this, k.slice(2), null);
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
    const value = ttAttr === null ? a.value : ttAttr(el, a.ns ?? '', a.lname, a.value);
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
      if (a.el && ttAttr !== null) v = ttAttr(a.el, a.ns ?? '', a.lname, v);
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
  // [HTMLConstructor] (HTML §3.2.3): `new` on a custom element's constructor; set by section
  // customelements. Until a custom element is defined no constructor of an element is legal.
  // While `htmlConstructing`, the constructors of Node and EventTarget let the object through:
  // the HTMLElement constructor then gives it its node.
  let htmlDefinition = () => { throw new TypeError('Illegal constructor'); }, htmlConstructed = () => {};
  class HTMLElement extends Element {
    constructor() {
      const d = htmlDefinition(new.target);
      htmlConstructing = true;
      try { super(); } finally { htmlConstructing = false; }
      htmlConstructed(this, d);
    }
    // title, lang, dir, hidden and the other reflected attributes: DOM.Reflect (dombreadth section).
    get dataset() {
      const el = this;
      return new Proxy({}, {
        get: (t, p) => typeof p === 'string' ? el.getAttribute('data-' + p.replace(/[A-Z]/g, c => '-' + c.toLowerCase())) ?? undefined : undefined,
        set: (t, p, v) => { el.setAttribute('data-' + String(p).replace(/[A-Z]/g, c => '-' + c.toLowerCase()), String(v)); return true; },
      });
    }
    get style() { let s = styles.get(this); if (!s) styles.set(this, s = styleOf(this)); return s; }
    set style(v) { this.style.cssText = v; }
    click() {
      if (chk(n.query(nodeId(this), 11, '')) === '1') return;
      if (clicking.has(this)) return;
      clicking.add(this);
      try {
        const e = new MouseEvent('click', { bubbles: true, cancelable: true, composed: true, view: window });
        dispatch(this, e);
      } finally { clicking.delete(this); }
    }
    focus() { n.query(nodeId(this), 177, 'f'); }
    blur() {}
    get offsetWidth() { return Math.round(layoutOf(this)[2]); }
    get offsetHeight() { return Math.round(layoutOf(this)[3]); }
    get offsetLeft() { return Math.round(layoutOf(this)[0]); }
    get offsetTop() { return Math.round(layoutOf(this)[1]); }
    get offsetParent() { return this.isConnected && this.localName !== 'body' && this.localName !== 'html' ? document.body : null; }
  }
  const clicking = new WeakSet();
  const styles = new WeakMap();
  // ---- element.style (CSSOM §6.6): the declaration block is the value of the style attribute.
  // Lean (CssValues.styleOp, node_query op 151) parses it, changes it and writes it as text:
  // which values a property takes, how they are written and how shorthands expand are decided
  // there. This is the WebIDL surface only. An engine without op 151 answers "" everywhere.
  const styleOp = (...parts) => { const r = n.query(0, 151, parts.join('\u0000')); return typeof r === 'string' ? r : ''; };
  const cssPropName = p => p === 'cssFloat' ? 'float' : (p.startsWith('--') || p.includes('-')) ? p
    : p.replace(/[A-Z]/g, c => '-' + c.toLowerCase()).replace(/^webkit-/, '-webkit-');
  const styleOf = el => blockStyle(() => el.getAttribute('style') ?? '', nb => el.setAttribute('style', nb));
  // A CSSStyleDeclaration over a declaration block kept as text: `block()` reads it,
  // `store(text)` keeps a changed one.
  const blockStyle = (block, store) => {
    // U+0001: the operation left the block as it was (an invalid value, a property not set)
    const write = nb => { if (nb !== '\u0001' && nb !== block()) store(nb); };
    const names = () => { const r = styleOp('names', block()); return r === '' ? [] : r.split('\u0000'); };
    const methods = {
      getPropertyValue(name) { if (arguments.length < 1) throw new TypeError('getPropertyValue: 1 argument required'); return styleOp('get', block(), String(name)); },
      getPropertyPriority(name) { if (arguments.length < 1) throw new TypeError('getPropertyPriority: 1 argument required'); return styleOp('pri', block(), String(name)); },
      setProperty(name, value, priority = '') {
        if (arguments.length < 2) throw new TypeError('setProperty: 2 arguments required');
        write(styleOp('set', block(), String(name), value === null ? '' : String(value), priority === null ? '' : String(priority)));
      },
      removeProperty(name) {
        if (arguments.length < 1) throw new TypeError('removeProperty: 1 argument required');
        const r = styleOp('rem', block(), String(name)).split('\u0000'); write(r[0]); return r[1] ?? '';
      },
      item(i) { if (arguments.length < 1) throw new TypeError('item: 1 argument required'); return names()[i >>> 0] ?? ''; },
    };
    const isIndex = p => /^(0|[1-9][0-9]*)$/.test(p);
    return new Proxy(Object.create(CSSStyleDeclaration.prototype), {
      get(t, p) {
        if (typeof p !== 'string') return Reflect.get(t, p);
        if (p === 'cssText') return styleOp('txt', block());
        if (p === 'length') return names().length;
        if (p === 'parentRule') return null;
        if (Object.prototype.hasOwnProperty.call(methods, p)) return methods[p];
        if (isIndex(p)) return names()[Number(p)];
        if (p in t) return Reflect.get(t, p);
        return styleOp('get', block(), cssPropName(p));
      },
      set(t, p, v) {
        if (typeof p !== 'string') return Reflect.set(t, p, v);
        if (p === 'cssText') { store(styleOp('txt', String(v))); return true; }
        if (p === 'length' || p === 'parentRule' || isIndex(p)) return true;
        write(styleOp('set', block(), cssPropName(p), v === null ? '' : String(v), ''));
        return true;
      },
      has(t, p) {
        if (typeof p !== 'string') return Reflect.has(t, p);
        if (p in t || p === 'cssText' || p === 'length' || p === 'parentRule' || p === 'cssFloat' || Object.prototype.hasOwnProperty.call(methods, p)) return true;
        if (isIndex(p)) return Number(p) < names().length;
        return styleOp('sup', cssPropName(p), 'initial') === '1';
      },
      ownKeys(t) { return names().map((x, i) => String(i)).concat(Reflect.ownKeys(t)); },
      getOwnPropertyDescriptor(t, p) {
        if (typeof p === 'string' && isIndex(p)) { const xs = names(); if (Number(p) < xs.length) return { value: xs[Number(p)], enumerable: true, configurable: true, writable: false }; }
        return Reflect.getOwnPropertyDescriptor(t, p);
      },
    });
  };
  class HTMLUnknownElement extends HTMLElement {}
  // The HTML element names whose interface is HTMLElement itself (HTML §3.2.2), and the valid
  // custom element names (node_query 181, DOM.CustomElements.validName; asked once a name):
  // an element of either kind is an HTMLElement, any other unknown name an HTMLUnknownElement.
  const plainHTMLElements = new Set(['abbr', 'address', 'article', 'aside', 'b', 'bdi', 'bdo', 'cite', 'code', 'dd', 'dfn', 'dt', 'em',
    'figcaption', 'figure', 'footer', 'header', 'hgroup', 'i', 'kbd', 'main', 'mark', 'nav', 'noscript', 'rp', 'rt', 'ruby', 's',
    'samp', 'search', 'section', 'small', 'strong', 'sub', 'summary', 'sup', 'u', 'var', 'wbr', 'acronym', 'basefont', 'big',
    'center', 'nobr', 'noembed', 'noframes', 'plaintext', 'rb', 'rtc', 'strike', 'tt']);
  const customNames = new Map();
  const isCustomName = l => { if (l.indexOf('-') < 0) return false; let v = customNames.get(l); if (v === undefined) customNames.set(l, v = n.query(0, 181, l) === '1'); return v; };
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
  // The form owner (HTML §4.10.18.3) is Lean's: DOM.FormControls.formOwner, node_query 186 "f".
  const formOf = el => { const r = n.query(nodeId(el), 186, 'f'); return typeof r === 'string' && r !== '' ? wrap(Number(r)) : null; };
  class SubmitEvent extends Event {
    constructor(type, init = undefined) { super(type, init); state(this).submitter = initOf(init).submitter ?? null; }
    get submitter() { return state(this).submitter; }
  }
  // The form submission algorithm up to navigation (HTML §4.10.21.3 steps 6.5-6.7): the
  // submit event; a navigation would follow, but nothing loads here.
  const submitForm = (form, submitter) => {
    if (!form.isConnected) return; // a form that is not connected does not submit (§4.10.21.3 step 1)
    if (formsSandboxed(form)) return; // nor one of a document with the sandboxed forms flag (step 3)
    const e = new SubmitEvent('submit', { bubbles: true, cancelable: true, submitter: submitter === form ? null : submitter });
    state(e).trusted = true;
    if (dispatch(form, e)) planSubmission(form, submitter === form ? null : submitter);
  };
  // ---- encoding100: the form submission algorithm after the submit event (HTML §4.10.21.3)
  // is Lean's (node_query 170, HTML.FormSubmission): the entry list, the form's encoding,
  // the URL and the target frame, whose navigation the embedder then answers. Here: which
  // form, which submitter, and the page's encoding label. An engine without op 170 answers
  // -2 and nothing navigates.
  const planSubmission = (form, submitter) => {
    if (!form.isConnected) return;
    const enc = form.ownerDocument === document ? docEncoding() : '';
    n.query(nodeId(form), 170, (submitter ? String(nodeId(submitter)) : '') + '\u0000' + enc);
  };
  // A document's URL (node_query 171): the page's, or a same-origin frame document's.
  const docURL = doc => { const r = n.query(doc, 171, ''); return typeof r === 'string' ? r : 'about:blank'; };
  // ---- end of encoding100 (forms) ----
  const resetForm = form => {
    const e = new Event('reset', { bubbles: true, cancelable: true });
    state(e).trusted = true;
    if (dispatch(form, e)) chk(n.treeOp(nodeId(form), 0, 9));
  };
  Object.defineProperties(named.HTMLFormElement.prototype, {
    submit: { value() { planSubmission(this, null); }, writable: true, configurable: true },
    requestSubmit: { value(submitter) { submitForm(this, submitter ?? this); }, writable: true, configurable: true },
    reset: { value() { resetForm(this); }, writable: true, configurable: true },
  });
  const fire = (target, type, init) => { const e = new Event(type, init); state(e).trusted = true; return dispatch(target, e); };
  // DOM §2.9: legacy-pre-activation, legacy-canceled-activation and activation behaviours.
  const preActivation = k => {
    if (!(htmlEl(k) && str(k, 0) === 'input')) return null;
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
  let invokerActivation = () => {};
  const activation = (k, targetId) => {
    if (!htmlEl(k)) {
      // An SVG a element that is a link (SVG 2 §16.2; Lean names it the activation target):
      // its link navigates a frame as an HTML a's does (node_query 190).
      if (str(k, 0) === 'a' && str(k, 2) === 'http://www.w3.org/2000/svg') {
        const raw = n.attr(k, 'href') ?? wrap(k).getAttributeNS('http://www.w3.org/1999/xlink', 'href'), target = n.attr(k, 'target');
        const url = typeof raw === 'string' ? resolveURL(raw, wrap(k).baseURI || href) : null;
        if (url !== null && /^(https?|data|blob|about):/i.test(url) && (typeof target === 'string' && target !== '' || info(k, 7) > 0))
          n.query(k, 190, (typeof target === 'string' ? target : '') + '\u0000' + url);
      }
      return;
    }
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
      if (form && (t === 'submit' || t === 'image')) { submitForm(form, el); return; }
      if (form && t === 'reset') { resetForm(form); return; }
      // a button with `commandfor` or `popovertarget` (section popover)
      invokerActivation(el, t);
    } else if (name === 'a' || name === 'area') {
      // A link in a frame's document, or one whose target names a frame, navigates that
      // frame: Lean chooses it and queues the navigation (node_query 190). A link of the
      // page's own document with no target is the fragment navigation below.
      const url = el.href, target = n.attr(k, 'target');
      if (/^(https?|data|blob|about):/i.test(url) && (typeof target === 'string' && target !== '' || info(k, 7) > 0)) {
        const own = info(k, 7) > 0 ? docURL(info(k, 7)) : href;
        if (url.split('#')[0] !== own.split('#')[0] || !url.includes('#')) { if (n.query(k, 190, (typeof target === 'string' ? target : '') + '\u0000' + url) === '1') return; }
      }
      followHyperlink(url);
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
      Object.defineProperty(C.prototype, 'on' + name, { get() { return handlerOf(bodyWindow(this), name); },
        set(f) { setHandler(bodyWindow(this), name, f); }, configurable: true, enumerable: true });
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
  // The object interfaces of WebGL 1.0 §5.3 to §5.13 and WebGL 2.0 §3.1 to §3.5. None has a
  // constructor a page may call: the context makes them (`glNew`).
  class WebGLObject { constructor() { throw new TypeError('Illegal constructor'); } }
  class WebGLBuffer extends WebGLObject {}
  class WebGLFramebuffer extends WebGLObject {}
  class WebGLProgram extends WebGLObject {}
  class WebGLRenderbuffer extends WebGLObject {}
  class WebGLShader extends WebGLObject {}
  class WebGLTexture extends WebGLObject {}
  class WebGLQuery extends WebGLObject {}
  class WebGLSampler extends WebGLObject {}
  class WebGLSync extends WebGLObject {}
  class WebGLTransformFeedback extends WebGLObject {}
  class WebGLVertexArrayObject extends WebGLObject {}
  class WebGLUniformLocation { constructor() { throw new TypeError('Illegal constructor'); } }
  const glNew = C => Object.create(C.prototype);
  const glClasses = [WebGLObject, WebGLBuffer, WebGLFramebuffer, WebGLProgram, WebGLRenderbuffer, WebGLShader, WebGLTexture,
    WebGLQuery, WebGLSampler, WebGLSync, WebGLTransformFeedback, WebGLVertexArrayObject, WebGLUniformLocation];
  const glFacts = new WeakMap(); // a WebGLActiveInfo's and a WebGLShaderPrecisionFormat's values
  const glFact = (o, k) => { const f = glFacts.get(o); if (!f) throw new TypeError('Illegal invocation'); return f[k]; };
  class WebGLActiveInfo {
    constructor() { throw new TypeError('Illegal constructor'); }
    get size() { return glFact(this, 'size'); }
    get type() { return glFact(this, 'type'); }
    get name() { return glFact(this, 'name'); }
  }
  class WebGLShaderPrecisionFormat {
    constructor() { throw new TypeError('Illegal constructor'); }
    get rangeMin() { return glFact(this, 'rangeMin'); }
    get rangeMax() { return glFact(this, 'rangeMax'); }
    get precision() { return glFact(this, 'precision'); }
  }
  const glEventText = new WeakMap();
  class WebGLContextEvent extends Event {
    constructor(type, init = undefined) {
      super(type, init);
      glEventText.set(this, init === undefined || init === null || init.statusMessage === undefined ? '' : String(init.statusMessage));
    }
    get statusMessage() { const m = glEventText.get(this); if (m === undefined) throw new TypeError('Illegal invocation'); return m; }
  }
  // The rendering context interfaces. Their constants, attributes, operations and overload
  // signatures are Lean's table of the WebGL IDL (PageGl.Idl, web_api op 100), which the
  // validator reads too: the interface object is made from it on first use (`lazyGroup`,
  // below). An operation checks its receiver and argument count, converts its arguments by
  // the signatures (Web IDL), and hands the call to Lean's state machine (PageGl.State, op
  // 102) when Lean models the command, and to the drawing path below when it draws.
  const glState = new WeakMap(); // page context -> its state
  const glObjIds = new WeakMap(); // WebGL object -> { st, id }: the context that made it and Lean's number
  const glInterfaces = [];
  const glInterface = version => glInterfaces[version] ??= makeGlInterface(version);
  const glClassNamed = name => glClasses.find(C => C.name === name);
  // One overload: its argument types. A type: its letter (tools/webgl-idl-table.py), an
  // interface name after `O`, optional (`~`), nullable (`?`).
  const glOverloads = sig => sig.split('|').map(o => o === '' ? [] : o.split(',').map(t => {
    const opt = t[0] === '~'; if (opt) t = t.slice(1);
    const nullable = t.endsWith('?'); if (nullable) t = t.slice(0, -1);
    return { t: t[0], cls: t.length > 1 ? glClassNamed(t.slice(1)) : null, opt, nullable };
  }));
  const glScalar = t => 'uilfbs'.includes(t);
  const glImageSource = v => {
    for (const name of ['ImageData', 'ImageBitmap', 'HTMLImageElement', 'HTMLCanvasElement', 'HTMLVideoElement', 'OffscreenCanvas', 'VideoFrame']) {
      const d = Object.getOwnPropertyDescriptor(globalThis, name), C = d && d.value;
      if (typeof C === 'function' && v instanceof C) return true;
    }
    return false;
  };
  const glTyped = { F: Float32Array, I: Int32Array, U: Uint32Array };
  // Does a value go with an argument type? A scalar type takes any value, except an object
  // or null where another overload has an object type for that argument.
  const glFits = (ty, v, others, i) => {
    const none = v === null || v === undefined, object = !none && (typeof v === 'object' || typeof v === 'function');
    if (glScalar(ty.t)) return !((object || none) && others.some(o => o[i] && !glScalar(o[i].t) && o[i].t !== 'a'));
    if (ty.t === 'a') return true;
    if (none) return ty.nullable;
    if (ty.t === 'O') return v instanceof ty.cls;
    if (ty.t === 'B') return v instanceof ArrayBuffer || ArrayBuffer.isView(v) || (typeof SharedArrayBuffer === 'function' && v instanceof SharedArrayBuffer);
    if (ty.t === 'V') return ArrayBuffer.isView(v);
    if (ty.t === 'T') return glImageSource(v);
    return object; // a typed array or a sequence
  };
  // The argument as a field of Lean's command (PageGl.Api.argOf).
  const glField = (ty, v, st) => {
    switch (ty.t) {
      case 'u': return 'i' + (Number(v) >>> 0);
      case 'i': return 'i' + (Number(v) | 0);
      case 'l': { const x = Math.trunc(Number(v)); return 'i' + (x === x && x !== Infinity && x !== -Infinity ? x : 0); }
      case 'f': return 'f' + Number(v);
      case 'b': return 'i' + (v ? 1 : 0);
      case 's': return 's' + String(v);
      case 'O': { if (v === null || v === undefined) return 'o0'; const reg = glObjIds.get(v); return reg && reg.st === st ? 'o' + reg.id : 'o-'; }
      case 'B': case 'V': return v === null || v === undefined ? 'u' : 'b' + v.byteLength + ' ' + (v.BYTES_PER_ELEMENT || 1);
      case 'F': case 'I': case 'U': case 'Q':
        if (ArrayBuffer.isView(v)) return 'b' + v.byteLength + ' ' + (v.BYTES_PER_ELEMENT || 1);
        return 'l' + Array.from(v, x => { const y = Math.trunc(Number(x)); return y === y && y !== Infinity && y !== -Infinity ? y : 0; }).join(',');
      default: return 'u';
    }
  };
  // The overload a call takes (Web IDL §3.6, by argument count and then by which arguments
  // are objects), and its arguments as fields. No overload: a TypeError.
  const glConvert = (name, k, overloads, args, st) => {
    const longest = overloads.reduce((m, o) => Math.max(m, o.length), 0), count = Math.min(args.length, longest);
    const byCount = overloads.filter(o => o.length >= count && o.filter(t => !t.opt).length <= count);
    for (const o of byCount) {
      let ok = true;
      for (let i = 0; i < count && ok; i++) ok = glFits(o[i], args[i], byCount.filter(x => x !== o), i);
      if (ok) { const fields = []; for (let i = 0; i < count; i++) fields.push(glField(o[i], args[i], st)); return fields; }
    }
    throw new TypeError(`Failed to execute '${k}' on '${name}': the arguments match no overload.`);
  };
  const makeGlInterface = version => {
    const name = version === 2 ? 'WebGL2RenderingContext' : 'WebGLRenderingContext';
    const text = apiOn() ? apiCall(100, [String(version)]) : null;
    if (typeof text !== 'string') return undefined;
    const C = function () { throw new TypeError('Illegal constructor'); };
    const hidden = (o, k, value) => Object.defineProperty(o, k, { value, writable: false, enumerable: false, configurable: true });
    hidden(C, 'name', name);
    const P = C.prototype;
    Object.defineProperty(C, 'prototype', { writable: false });
    hidden(P, Symbol.toStringTag, name);
    const stateOf = o => { const st = glState.get(o); if (!st) throw new TypeError('Illegal invocation'); return st; };
    const modelled = new Set();
    for (const line of text.split('\n')) {
      const [kind, k, v, sig] = line.split(' ');
      if (kind === 'c') {
        const d = { value: Number(v), writable: false, enumerable: true, configurable: false };
        Object.defineProperty(C, k, d); Object.defineProperty(P, k, d);
      } else if (kind === 'a') {
        const get = function () { return stateOf(this).attr(k); };
        hidden(get, 'name', 'get ' + k);
        let set;
        if (v === '0') { set = function (x) { stateOf(this).setAttr(k, x); }; hidden(set, 'name', 'set ' + k); }
        Object.defineProperty(P, k, { get, set, enumerable: true, configurable: true });
      } else if (kind === 'o') {
        const len = Number(v), overloads = glOverloads(sig ?? '');
        const f = function (...args) {
          const st = stateOf(this);
          if (args.length < len) throw new TypeError(`Failed to execute '${k}' on '${name}': ${len} argument${len === 1 ? '' : 's'} required, but only ${args.length} present.`);
          return st.call(k, args, glConvert(name, k, overloads, args, st), modelled.has(k));
        };
        hidden(f, 'name', k); hidden(f, 'length', len);
        Object.defineProperty(P, k, { value: f, writable: true, enumerable: true, configurable: true });
      } else if (kind === 'm') modelled.add(k);
    }
    return C;
  };
  // The page's context object: Lean's state machine in front of the drawing path (`glImplFor`).
  const glContextFor = (canvas, version, attributes) => {
    const C = glInterface(version);
    if (!C) return null;
    const a = attributes !== null && typeof attributes === 'object' ? attributes : {};
    const flag = (k, dflt) => (a[k] === undefined ? dflt : !!a[k]) ? '1' : '0';
    const id = apiCall(101, [String(version), flag('alpha', true), flag('depth', true), flag('stencil', false)]);
    if (typeof id !== 'string') return null;
    const impl = glImplFor(canvas, version), page = glNew(C), objects = new Map();
    let drawingSpace = 'srgb', unpackSpace = 'srgb';
    // An error the drawing path found is recorded in Lean's flag (the first error wins there).
    const drawError = keep => { const e = impl.getError(); if (e && keep) apiCall(102, [id, '$raise', 'i' + e]); };
    const st = { impl, version,
      call(k, args, fields, modelled) {
        if (k === 'getError') { drawError(true); return Number(String(apiCall(102, [id, 'getError'])).slice(1)) || 0; }
        const draw = impl[k];
        if (!modelled) {
          if (typeof draw !== 'function') return undefined;
          const r = draw.apply(impl, args); drawError(true); return r;
        }
        const r = apiCall(102, [id, k].concat(fields));
        if (typeof r !== 'string' || r === '!') return k.startsWith('is') ? false : k.startsWith('get') || k.startsWith('create') ? null : undefined;
        switch (r[0]) {
          case 'z': return null;
          case 'i': return Number(r.slice(1));
          case 't': return true;
          case 'F': return false;
          case 'o': {
            const n = Number(r.slice(1));
            if (!k.startsWith('create')) return objects.get(n) ?? null;
            // A new object: the drawing path's when it makes that kind, else a plain one.
            const made = typeof draw === 'function' ? draw.apply(impl, args) : glNew(glClassNamed(k === 'createVertexArray' ? 'WebGLVertexArrayObject' : 'WebGL' + k.slice(6)));
            drawError(false);
            glObjIds.set(made, { st, id: n }); objects.set(n, made);
            return made;
          }
          default: {
            // Accepted by Lean ('u'), or the drawing path's to answer ('d'): the drawing path runs;
            // what it refuses of an accepted command is its own limit, not a GL error.
            if (typeof draw !== 'function') return k.startsWith('get') ? null : undefined;
            const out = draw.apply(impl, args); drawError(false);
            if (k.startsWith('delete') && args[0]) { const reg = glObjIds.get(args[0]); if (reg) objects.delete(reg.id); }
            return out;
          }
        }
      },
      attr(k) {
        if (k === 'drawingBufferFormat') return 0x8058; // RGBA8
        if (k === 'drawingBufferColorSpace') return drawingSpace;
        if (k === 'unpackColorSpace') return unpackSpace;
        return impl[k];
      },
      // PredefinedColorSpace: a value outside the enumeration is ignored (Web IDL §3.7.5).
      setAttr(k, x) {
        x = String(x);
        if (x !== 'srgb' && x !== 'display-p3') return;
        if (k === 'drawingBufferColorSpace') drawingSpace = x; else if (k === 'unpackColorSpace') unpackSpace = x;
      } };
    glState.set(page, st);
    return page;
  };
  const glImplFor = (canvas, version) => {
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
      createBuffer() { const b = glNew(WebGLBuffer); b.gpu = 0; b.size = 0; return b; },
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
      createShader(type) { const s = glNew(WebGLShader); s.type = type; s.source = ''; return s; },
      shaderSource(s, src) { s.source = String(src); },
      compileShader() {},
      getShaderParameter(s, p) { return p === GL.COMPILE_STATUS ? true : null; },
      getShaderInfoLog: () => '', deleteShader() {},
      createProgram() { const p = glNew(WebGLProgram); p.shaders = []; p.pipelines = new Map(); return p; },
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
        return u ? Object.assign(glNew(WebGLUniformLocation), { program: p, offset: u[0], type: u[1] }) : null;
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
      else if (kind === 'webgl2') context = glContextFor(this, 2, arguments[1]);
      else if (kind === 'webgl' || kind === 'experimental-webgl') context = glContextFor(this, 1, arguments[1]);
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
    get style() { let s = styles.get(this); if (!s) styles.set(this, s = styleOf(this)); return s; }
    set style(v) { this.style.cssText = v; }
    // SVG 2 §8.10 getBBox: the bounds of the element's geometry in its own user space.
    getBBox() { const b = query(nodeId(this), 18, 4); return new DOMRect(b[0], b[1], b[2], b[3]); }
  }
  // MathML Core §2.3: the interface of the elements in the MathML namespace.
  class MathMLElement extends Element {}
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
    get URL() { return this === document ? location.href : docURL(nodeId(this)); }
    get documentURI() { return this.URL; }
    get compatMode() { return 'CSS1Compat'; }
    get characterSet() { if (this === document) return docEncoding(); const r = n.query(nodeId(this), 172, ''); return typeof r === 'string' ? r : 'UTF-8'; }
    get charset() { return this.characterSet; }
    get inputEncoding() { return this.characterSet; }
    get contentType() { return str(nodeId(this), 9); }
    // xmlweb: a document that no navigation made (DOMParser, createDocument, XSLTProcessor)
    // has the readiness "complete" (HTML §3.1.3 "current document readiness")
    get readyState() { return this === document || info(nodeId(this), 12) >= 0 ? readyState : 'complete'; }
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
    // CSSOM View §5.1: the hit test is Lean's (node_query 35 on the layout of the page;
    // the point as x × 65536 + y in whole CSS pixels). Off the viewport, none.
    elementFromPoint(x, y) { pointArgs(arguments, 'elementFromPoint'); return pointHits(x, y)[0] ?? null; }
    elementsFromPoint(x, y) { pointArgs(arguments, 'elementsFromPoint'); const r = pointHits(x, y); return r.length || !this.documentElement ? r : (inViewport(x, y) ? [this.documentElement] : []); }
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
  addHandlers(MathMLElement.prototype);
  // ElementCSSInlineStyle (CSSOM §7.1) and HTMLOrSVGElement (HTML §3.2.6): an SVG element
  // and a MathML element have `style`, `dataset`, `focus` and `blur` as an HTML element has them.
  for (const C of [SVGElement, MathMLElement])
    for (const k of ['style', 'dataset', 'focus', 'blur'])
      Object.defineProperty(C.prototype, k, Object.getOwnPropertyDescriptor(HTMLElement.prototype, k));
  protoOf = (id, t) => {
    switch (t) {
      case 1: {
        if (!htmlEl(id)) {
          const ns = str(id, 2);
          if (ns === 'http://www.w3.org/2000/svg') return svgProtoOf ? svgProtoOf(str(id, 0)) : SVGElement.prototype;
          return (ns === 'http://www.w3.org/1998/Math/MathML' ? MathMLElement : Element).prototype;
        }
        const l = str(id, 0), C = htmlClasses[l];
        return (C ?? (plainHTMLElements.has(l) || isCustomName(l) ? HTMLElement : HTMLUnknownElement)).prototype;
      }
      case 3: return Text.prototype;
      case 4: return CDATASection.prototype;
      case 7: return ProcessingInstruction.prototype;
      case 8: return Comment.prototype;
      case 9: return info(id, 10) === 1 ? HTMLDocument.prototype : XMLDocument.prototype;
      case 10: return DocumentType.prototype;
      case 11: return shadowEngine() && info(id, 22) >= 0 ? (seeShadow(), ShadowRoot.prototype) : DocumentFragment.prototype;
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
  // ==== shadowframes: Shadow DOM ========================================================
  // DOM §4.2.2 (slots), §4.8 (ShadowRoot), §4.9 (attachShadow). The algorithms are Lean's
  // (L4Factoidal.DOM.Shadow): node_info 20-28, node_query 30, 31 and 33, tree_op 20, 22 and
  // 23. An engine without them answers -2 to node_info 27, which an engine with them answers
  // for any node, so the probe works before there is a document (BubblePopJS runs this
  // prelude once, with none, for its realm): then this section defines nothing and events
  // keep the old plan.
  let shadowProbe;
  function shadowEngine() { return shadowProbe ?? (shadowProbe = info(0, 27) !== -2); }
  // "Signal a slot change" (DOM §4.2.2.5): once a shadow root has been seen, a change of the
  // tree marks the slots for one Lean comparison (node_query 33) in a microtask, which
  // fires slotchange at each slot whose assigned nodes changed.
  let shadowSeen = false, slotDirty = false;
  // The tree-changing natives get the slot check only once a shadow root is seen, so a page
  // with no shadow tree pays nothing per change.
  function seeShadow() {
    if (shadowSeen) return;
    shadowSeen = true; n.query(0, 33, '');
    for (const k of ['setAttr', 'removeAttr', 'setText', 'insert', 'remove', 'replace', 'treeOp']) {
      const f = n[k];
      n[k] = (...a) => { const r = f.apply(n, a); if (!slotDirty) { slotDirty = true; Promise.resolve().then(fireSlotChanges); } return r; };
    }
  }
  const fireSlotChanges = () => {
    slotDirty = false;
    const r = n.query(0, 33, '');
    if (typeof r !== 'string' || r === '') return;
    for (const id of r.split(' ')) { const e = new Event('slotchange', { bubbles: true }); state(e).trusted = true; dispatch(wrap(Number(id)), e); }
  };
  class ShadowRoot extends DocumentFragment {
    constructor() { throw new TypeError('Illegal constructor'); }
    get mode() { return info(nodeId(this), 22) & 1 ? 'closed' : 'open'; }
    get host() { return wrap(info(nodeId(this), 21)); }
    get delegatesFocus() { return (info(nodeId(this), 22) & 2) !== 0; }
    get slotAssignment() { return info(nodeId(this), 22) & 4 ? 'manual' : 'named'; }
    get clonable() { return (info(nodeId(this), 22) & 8) !== 0; }
    get serializable() { return (info(nodeId(this), 22) & 16) !== 0; }
    get activeElement() { return focusRetarget(nodeId(this)); }
    get onslotchange() { return handlerOf(this, 'slotchange'); }
    set onslotchange(f) { setHandler(this, 'slotchange', f); }
  }
  if (shadowEngine()) {
    // ShadowRoot.innerHTML (DOM Parsing): the shadow root's children, and in the setter
    // markup parsed with the host as context (Element.prototype.innerHTML is defined later).
    Object.defineProperty(ShadowRoot.prototype, 'innerHTML', {
      get() { return chk(n.query(nodeId(this), 15, '0')); },
      set(v) {
        const id = nodeId(this), host = info(id, 21);
        const f = fragmentOf(info(id, 7), str(host, 2), str(host, 0), v === null ? '' : String(v));
        chk(n.setText(id, '')); chk(n.insert(id, f, -1));
      }, configurable: true, enumerable: true });
    // ShadowRoot.setHTMLUnsafe and getHTML (HTML §8.4): the host is the context element.
    define(ShadowRoot.prototype, 'getHTML', function getHTML(options = undefined) { return getHTMLOf(this, options); });
    define(ShadowRoot.prototype, 'setHTMLUnsafe', function setHTMLUnsafe(html) {
      const id = nodeId(this), host = info(id, 21);
      const f = fragmentOf(info(id, 7), str(host, 2), str(host, 0), String(html), true);
      chk(n.setText(id, '')); chk(n.insert(id, f, -1));
    });
    define(Element.prototype, 'attachShadow', function attachShadow(init) {
      if (arguments.length < 1) throw new TypeError("Failed to execute 'attachShadow' on 'Element': 1 argument required, but only 0 present.");
      if (init === null || (typeof init !== 'object' && typeof init !== 'function')) throw new TypeError("Failed to execute 'attachShadow' on 'Element': parameter 1 is not of type 'ShadowRootInit'.");
      // WebIDL dictionary members, read in lexicographical order.
      const clonable = !!init.clonable, delegatesFocus = !!init.delegatesFocus, modeIn = init.mode;
      const serializable = !!init.serializable, slotIn = init.slotAssignment;
      if (modeIn === undefined) throw new TypeError("Failed to read the 'mode' property from 'ShadowRootInit': Required member is undefined.");
      const mode = String(modeIn), slot = slotIn === undefined ? 'named' : String(slotIn);
      if (mode !== 'open' && mode !== 'closed') throw new TypeError(`The provided value '${mode}' is not a valid enum value of type ShadowRootMode.`);
      if (slot !== 'named' && slot !== 'manual') throw new TypeError(`The provided value '${slot}' is not a valid enum value of type SlotAssignmentMode.`);
      seeShadow();
      const flags = (mode === 'closed' ? 1 : 0) | (delegatesFocus ? 2 : 0) | (slot === 'manual' ? 4 : 0) | (clonable ? 8 : 0) | (serializable ? 16 : 0);
      return wrap(chk(n.treeOp(nodeId(this), flags, 20)));
    });
    Object.defineProperty(Element.prototype, 'shadowRoot', { get() { return wrap(info(nodeId(this), 20)); }, configurable: true, enumerable: true });
    for (const C of [Element, Text]) Object.defineProperty(C.prototype, 'assignedSlot', { get() { return wrap(info(nodeId(this), 23)); }, configurable: true, enumerable: true });
    reflectString(Element, ['slot']);
    const Slot = named.HTMLSlotElement;
    reflectString(Slot, ['name']);
    const assigned = (slot, options, elements) => {
      const r = chk(n.query(nodeId(slot), 30, options !== null && typeof options === 'object' && options.flatten ? '1' : '0'));
      const ids = typeof r === 'string' && r !== '' ? r.split(' ').map(Number) : [];
      return (elements ? ids.filter(k => info(k, 0) === 1) : ids).map(wrap);
    };
    define(Slot.prototype, 'assignedNodes', function assignedNodes(options = {}) { return assigned(this, options, false); });
    define(Slot.prototype, 'assignedElements', function assignedElements(options = {}) { return assigned(this, options, true); });
    define(Slot.prototype, 'assign', function assign(...nodes) {
      for (const x of nodes) if (!(x instanceof Element || x instanceof Text)) throw new TypeError("Failed to execute 'assign' on 'HTMLSlotElement': parameter is not of type 'Element' or 'Text'.");
      const id = nodeId(this);
      chk(n.treeOp(id, 0, 22));
      for (const x of nodes) chk(n.treeOp(id, nodeId(x), 23));
    });
    // HTML §4.12.3: the declarative shadow root attributes of `template`.
    const T = named.HTMLTemplateElement;
    Object.defineProperty(T.prototype, 'shadowRootMode', { get() { const v = (this.getAttribute('shadowrootmode') ?? '').toLowerCase(); return v === 'open' || v === 'closed' ? v : ''; },
      set(v) { this.setAttribute('shadowrootmode', String(v)); }, configurable: true, enumerable: true });
    for (const [k, a] of [['shadowRootDelegatesFocus', 'shadowrootdelegatesfocus'], ['shadowRootClonable', 'shadowrootclonable'], ['shadowRootSerializable', 'shadowrootserializable']])
      Object.defineProperty(T.prototype, k, { get() { return this.hasAttribute(a); }, set(v) { this.toggleAttribute(a, !!v); }, configurable: true, enumerable: true });
  }
  // ==== end shadowframes: Shadow DOM =====================================================

  // ---- Window -----------------------------------------------------------------------
  class Window extends EventTarget { constructor() { throw new TypeError('Illegal constructor'); } }
  addHandlers(Window.prototype);
  Object.setPrototypeOf(globalThis, Window.prototype);
  const window = globalThis;
  ids.set(window, WINDOW);
  const document = wrap(0);
  const frameWindows = new Map(), frameCells = new Map(), frameOfWindow = new WeakMap();
  // `postMessage` to the window of a frame's document (assigned where the frames' targets are).
  let postFrame = () => {};
  // The parent window of a frame's document in this realm: the window of the document that
  // holds its iframe (the page's, or another frame's).
  const parentOfDoc = doc => { const el = info(doc, 12), pd = el >= 0 ? info(el, 7) : 0; return pd > 0 ? frameWindow(pd) : window; };
  const frameWindow = doc0 => {
    let w = frameWindows.get(doc0);
    if (w) return w;
    // The frame's document now: `document.close()` gives the frame another document node
    // (document.open, write, close below) and this window stays the frame's window.
    const cell = { doc: doc0 };
    // HTML §9.3.3: a message to this window goes to this frame's window target (where the
    // frame's scripts listen), not to the page's.
    const post = function postMessage(message, targetOrigin, transfer) {
      if (arguments.length < 1) throw new TypeError("Failed to execute 'postMessage' on 'Window': 1 argument required, but only 0 present.");
      postFrame(cell.doc, message, targetOrigin, transfer);
    };
    const own = { document: () => wrap(cell.doc), window: () => w, self: () => w, frames: () => w, globalThis: () => w,
      parent: () => parentOfDoc(cell.doc), top: () => window, frameElement: () => wrap(info(cell.doc, 12)), length: () => 0,
      location: () => frameLocation(cell.doc), postMessage: () => post };
    // Frames share this realm. A function reached through a frame's window runs with that
    // frame's document as `document` for the length of the call (as the frame's own scripts
    // do: n.script below), so `iframe.contentWindow.f()` resolves URLs against the frame's
    // document. Callbacks that f leaves behind run later with the top document: one realm
    // can not tell which frame a function belongs to.
    const inFrame = new WeakMap();
    const asFrame = f => {
      let g = inFrame.get(f);
      if (g) return g;
      const enter = run => { const before = scriptDocument; scriptDocument = wrap(cell.doc); try { return run(); } finally { scriptDocument = before; } };
      // A plain function, not a Proxy of f: BubblePopJS does not call a Proxy of a function.
      g = function (...args) { return enter(() => new.target ? Reflect.construct(f, args, new.target === g ? f : new.target) : f.apply(this, args)); };
      Object.setPrototypeOf(g, f);
      if (Object.prototype.hasOwnProperty.call(f, 'prototype')) g.prototype = f.prototype;
      Object.defineProperty(g, 'name', { value: f.name, configurable: true });
      Object.defineProperty(g, 'length', { value: f.length, configurable: true });
      inFrame.set(f, g);
      return g;
    };
    // What a script sets on this window (`frame.contentWindow.x = v`) is this window's: it
    // does not replace the page's global of that name (frames share the realm, not their
    // windows' properties). A frame's own scripts' globals are the realm's and are read below.
    const vars = Object.create(null);
    const isOwn = p => Object.prototype.hasOwnProperty.call(own, p), isVar = p => Object.prototype.hasOwnProperty.call(vars, p);
    w = new Proxy(window, {
      get(t, p) {
        if (isOwn(p)) return own[p]();
        if (isVar(p)) return vars[p];
        if (typeof p === 'string' && p.startsWith('on') && handlerNames.includes(p.slice(2))) return handlerOf(frameTarget(cell.doc), p.slice(2));
        const v = Reflect.get(t, p, t);
        // Only a page's own global functions (enumerable: a function declaration or an
        // assignment). The platform's constructors and methods are not enumerable and keep
        // their identity, so `frame.contentWindow.TypeError === TypeError` as before.
        if (typeof v !== 'function' || typeof p !== 'string') return v;
        const d = Object.getOwnPropertyDescriptor(t, p);
        return d && d.enumerable && 'value' in d ? asFrame(v) : v;
      },
      has(t, p) { return isOwn(p) || isVar(p) || Reflect.has(t, p); },
      set(t, p, v) {
        // `frame.contentWindow.location = url` navigates the frame (as its `src` does)
        if (isOwn(p)) { if (p === 'location') wrap(info(cell.doc, 12)).setAttribute('src', String(v)); return true; }
        // an event handler attribute of the window (`onload`, `onmessage`) is the frame's target's
        if (typeof p === 'string' && p.startsWith('on') && handlerNames.includes(p.slice(2))) { setHandler(frameTarget(cell.doc), p.slice(2), v); return true; }
        vars[p] = v; return true;
      },
      deleteProperty(t, p) { if (isVar(p)) { delete vars[p]; return true; } return !isOwn(p); },
    });
    frameWindows.set(doc0, w); frameCells.set(doc0, cell); frameOfWindow.set(w, cell);
    return w;
  };
  // encoding100: a same-origin frame's Location: its document's URL (node_query 171) and
  // that URL's parts as the URL class (Lean's URL parser) gives them. Read only here.
  const frameLocations = new Map();
  const frameLocation = doc => {
    let l = frameLocations.get(doc);
    if (l) return l;
    const parts = () => { try { return new URL(docURL(doc)); } catch { return null; } };
    l = { get href() { return docURL(doc); }, toString() { return docURL(doc); } };
    for (const k of ['protocol', 'host', 'hostname', 'port', 'pathname', 'search', 'hash', 'origin'])
      Object.defineProperty(l, k, { get() { const u = parts(); return u ? u[k] : ''; }, enumerable: true });
    frameLocations.set(doc, l);
    return l;
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
    else { const code = ttValue === null ? String(f) : ttValue('TrustedScript', null, f, repeat ? 'Window setInterval' : 'Window setTimeout'); run = () => (0, eval)(code); }
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
  // A script of a frame's document runs in this realm with `document` its own document
  // (Hosts.Page.Session.loadFrameP sets the current script).
  let scriptDocument = null;
  Object.defineProperty(globalThis, 'document', { get: () => scriptDocument ?? document, configurable: true, enumerable: true });
  // ---- Named access on the Window object (HTML §7.3.3) ----
  // A name with no binding, or a property the global and its prototype chain lack, is asked
  // of Lean (DOM.Named, node_query 180) for the document of the running script: an element by
  // its id, an embed, form, img or object by its name, a frame's window by its name, or a
  // live collection when several elements have the name. The engine calls this function on
  // such a miss only (JS.Interp `namedGlobal`), from the global's internal slot (a private
  // name key, which no reflection lists); `undefined` means "not a named property".
  {
    let asking = false;
    const namedIds = (doc, name) => { const r = n.query(doc, 180, name); return typeof r === 'string' && (r[0] === 'c' || r[0] === 'e') ? r.slice(1).split(' ').map(Number) : []; };
    const namedProperty = name => {
      if (asking || typeof name !== 'string' || name === '') return undefined;
      asking = true;
      try {
        const doc = scriptDocument ? nodeId(scriptDocument) : 0;
        const r = n.query(doc, 180, name);
        if (typeof r !== 'string' || r === '') return undefined;
        const kind = r[0], rest = r.slice(1);
        if (kind === 'e') return wrap(Number(rest));
        if (kind === 'w') return wrap(Number(rest)).contentWindow ?? undefined;
        if (kind === 'c') return liveCollection(() => namedIds(doc, name));
        return undefined;
      } finally { asking = false; }
    };
    // BubblePopJS: the engine's slot for named properties, which no property key of a script
    // names (n.setNamedGetter). Another engine has no such slot.
    if (typeof n.setNamedGetter === 'function') n.setNamedGetter(namedProperty);
  }
  // ==== customelements: Custom elements (HTML §4.13) ====================================
  // The registry, the definitions and the callbacks are these JavaScript objects. Lean decides
  // what is a function of a name or of the tree (DOM.CustomElements): node_query 181, whether
  // a name is a valid custom element name; 182, the elements a tree change at a node reaches,
  // in shadow-including tree order. Until the first `define` the natives are not wrapped
  // (`ceActive`), so a page without custom elements does no work here.
  //
  // An element's object is the `this` of its constructor: `new C()` makes the object, and the
  // HTMLElement constructor gives it the element's node (a new node, or the node being
  // upgraded). When a script already holds an object for an element that is upgraded later,
  // that object stays the element's object: the constructor runs on a second object for the
  // same node, and its own properties and prototype are then given to the first.
  {
    const validName = name => isCustomName(name);
    const reach = id => { const r = n.query(id, 182, ''); return typeof r === 'string' && r !== '' ? r.split(' ').map(Number) : []; };
    const defsByName = new Map(), defsByCtor = new Map(), waiting = new Map(), ceState = new WeakMap(), isValues = new Map();
    let defining = false;
    // IsConstructor: a function, or a Proxy of one
    const isCtor = f => { if (f === null || (typeof f !== 'function' && typeof f !== 'object')) return false; try { Reflect.construct(String, [], f); return true; } catch { return false; } };
    const customOf = id => { const el = wrappers.get(id), st = el && ceState.get(el); return st && st.state === 'custom' ? el : undefined; };
    // "Look up a custom element definition" (HTML §4.13.3) for the element numbered `id`.
    const lookup = id => {
      if (info(id, 0) !== 1 || !htmlEl(id)) return null;
      // a document with no browsing context has no definitions (the page's document is 0; a
      // frame's document answers its iframe to node_info 12)
      const doc = info(id, 7);
      if (doc !== 0 && info(doc, 12) < 0) return null;
      const l = str(id, 0), d = defsByName.get(l);
      if (d && d.localName === l) return d;
      let is = isValues.get(id);
      if (is === undefined) { const a = n0.attr(id, 'is'); is = typeof a === 'string' ? a : undefined; }
      if (is !== undefined) { const e = defsByName.get(is); if (e && e.localName === l) return e; }
      return null;
    };
    // the element's "defined" state, for `:defined` (tree_op 30 and 31: `Node.states` bit 4)
    const markDefined = id => { const b = n.treeOp(id, 0, 31); if (typeof b === 'number' && b >= 0 && !(b & 4)) n.treeOp(id, b | 4, 30); };
    const callback = (el, name, args) => {
      const st = ceState.get(el), f = st && st.def && st.def.callbacks[name];
      if (f) try { f.apply(el, args); } catch (e) { report(e); }
    };
    // "Upgrade an element" (HTML §4.13.5), for the element numbered `id`.
    // `sync`: "create an element" with the synchronous custom elements flag (step 6.1): the
    // constructor's result is checked and is the element made, which the answer is.
    const upgrade = (id, def, sync = false) => {
      const held = wrappers.get(id);
      let st = held && ceState.get(held);
      if (st && st.state !== 'undefined' && st.state !== 'uncustomized') return;
      if (!st) st = { state: 'undefined', def: null };
      if (held) ceState.set(held, st);
      st.def = def; st.state = 'failed';
      const pending = [];
      if (def.callbacks.attributeChangedCallback) {
        const xs = (n.query(id, 2, '') || '').split('\u0000');
        for (let i = 0; i + 3 < xs.length; i += 4) if (def.observed.has(xs[i + 2])) pending.push(['attributeChangedCallback', [xs[i + 2], null, xs[i + 3], xs[i] === '' ? null : xs[i]]]);
      }
      if (connectedId(id)) pending.push(['connectedCallback', []]);
      const entry = { id, held, made: undefined, done: false, st };
      def.stack.push(entry);
      try {
        if (def.disableShadow && info(id, 26) >= 0) throw new DOMException('The element already has a shadow root.', 'NotSupportedError');
        st.state = 'precustomized';
        const r = new def.constructor();
        if (sync) {
          if (!(r instanceof HTMLElement)) throw new TypeError('The result of constructing a custom element is not an HTMLElement.');
          const k = nodeId(r);
          if (n.query(k, 2, '') !== '' || info(k, 6) > 0 || info(k, 1) >= 0 || info(k, 7) !== info(id, 7) || str(k, 0) !== def.localName)
            throw new DOMException('The result of constructing a custom element must have no attributes, children or parent, and be in the document with the local name asked for.', 'NotSupportedError');
          if (r !== entry.made) { def.stack.pop(); if (entry.done) { st.def = null; st.state = 'failed'; } return r; }
        } else if (!entry.done || r !== entry.made) throw new TypeError('The custom element constructor did not produce the element being upgraded.');
        if (held) {
          Object.setPrototypeOf(held, Object.getPrototypeOf(r));
          for (const k of Reflect.ownKeys(r)) { try { Object.defineProperty(held, k, Object.getOwnPropertyDescriptor(r, k)); } catch {} }
        }
      } catch (e) {
        def.stack.pop(); st.def = null; st.state = 'failed';
        // the object the constructor was given keeps the element's own interface
        const w = wrappers.get(id);
        if (w && !held) { Object.setPrototypeOf(w, def.localName === def.name ? HTMLElement.prototype : protoOf(id, 1)); ceState.set(w, st); }
        throw e;
      }
      def.stack.pop();
      st.state = 'custom';
      markDefined(id);
      const el = wrappers.get(id);
      for (const [name, args] of pending) callback(el, name, args);
      return el;
    };
    // "Try to upgrade an element": when a definition matches, as a reaction that reports.
    const tryUpgrade = id => {
      const el = wrappers.get(id), st = el && ceState.get(el);
      if (st && st.state !== 'undefined' && st.state !== 'uncustomized') return;
      const def = lookup(id);
      if (def) try { upgrade(id, def); } catch (e) { report(e); }
    };
    const platformClasses = new Set([HTMLUnknownElement, ...Object.values(htmlClasses)]);
    const platformOf = NT => { let C = NT; for (let i = 0; i < 1000 && C !== null && C !== undefined && C !== HTMLElement && !platformClasses.has(C); i++) C = Object.getPrototypeOf(C); return C; };
    // [HTMLConstructor] steps 1 to 5: the definition of NewTarget, or a TypeError.
    htmlDefinition = NT => {
      const def = NT === undefined ? undefined : defsByCtor.get(NT);
      if (!def) throw new TypeError('Illegal constructor');
      const active = platformOf(NT);
      if (def.localName === def.name ? active !== HTMLElement : htmlClasses[def.localName] !== active) throw new TypeError('Illegal constructor: the definition does not extend this interface');
      return def;
    };
    // Steps 6 to 12, with `self` the object that `new` made: it becomes the object of a new
    // element, or of the element being upgraded.
    htmlConstructed = (self, def) => {
      const st0 = { state: 'custom', def };
      if (def.stack.length === 0) {
        const id = chk(n0.create(3 + 16 * (scriptDocument ? nodeId(scriptDocument) : 0), def.localName));
        ids.set(self, id); wrappers.set(id, self); ceState.set(self, st0);
        if (def.localName !== def.name) isValues.set(id, def.name);
        markDefined(id);
        return;
      }
      const entry = def.stack[def.stack.length - 1];
      if (entry.done) throw new TypeError('This custom element constructor was already called for this element.');
      entry.done = true; entry.made = self;
      ids.set(self, entry.id); ceState.set(self, entry.st);
      if (!entry.held) wrappers.set(entry.id, self);
    };
    // The reactions of a tree change (HTML §4.13.6), run when the native returns.
    const connectAll = idsIn => { for (const k of idsIn) { const el = customOf(k); if (el) callback(el, 'connectedCallback', []); else tryUpgrade(k); } };
    const customIn = id => reach(id).map(customOf).filter(el => el !== undefined);
    const wrapNatives = () => {
      const insert0 = n.insert, remove0 = n.remove, replace0 = n.replace, setText0 = n.setText, setAttr0 = n.setAttr, removeAttr0 = n.removeAttr, clone0 = n.clone, treeOp0 = n.treeOp;
      const moved = (p, node, native) => {
        const fragment = info(node, 0) === 11, roots = fragment ? kids(node) : [node];
        const gone = !fragment && connectedId(node) ? customIn(node) : [], doc0 = roots.length ? info(roots[0], 7) : -1;
        const r = native();
        if (r !== 0) return r;
        for (const el of gone) callback(el, 'disconnectedCallback', []);
        const into = connectedId(p);
        for (const k of roots) {
          const doc1 = info(k, 7);
          if (doc0 >= 0 && doc1 !== doc0) for (const el of customIn(k)) callback(el, 'adoptedCallback', [wrap(doc0), wrap(doc1)]);
          if (into) connectAll(reach(k));
        }
        return r;
      };
      n.insert = (p, node, child) => moved(p, node, () => insert0(p, node, child));
      n.replace = (p, node, child) => {
        const gone = child !== node && connectedId(child) ? customIn(child) : [];
        const r = moved(p, node, () => replace0(p, node, child));
        if (r === 0) for (const el of gone) callback(el, 'disconnectedCallback', []);
        return r;
      };
      n.remove = (p, child) => {
        const gone = connectedId(child) ? customIn(child) : [];
        const r = remove0(p, child);
        if (r === 0) for (const el of gone) callback(el, 'disconnectedCallback', []);
        return r;
      };
      n.setText = (id, value) => {
        const t = info(id, 0);
        const gone = (t === 1 || t === 11) && connectedId(id) ? kids(id).flatMap(customIn) : [];
        const r = setText0(id, value);
        if (r === 0) for (const el of gone) callback(el, 'disconnectedCallback', []);
        return r;
      };
      const attrChange = (id, name, native) => {
        const el = customOf(id), st = el && ceState.get(el);
        if (!st || !st.def.callbacks.attributeChangedCallback) return native();
        const rn = recordName(id, name);
        if (!st.def.observed.has(rn.attributeName)) return native();
        const old = n0.attr(id, rn.key), r = native();
        if (r === 0) { const now = n0.attr(id, rn.key); callback(el, 'attributeChangedCallback', [rn.attributeName, typeof old === 'string' ? old : null, typeof now === 'string' ? now : null, rn.attributeNamespace]); }
        return r;
      };
      n.setAttr = (id, name, value) => attrChange(id, name, () => setAttr0(id, name, value));
      n.removeAttr = (id, name) => attrChange(id, name, () => removeAttr0(id, name));
      // a clone has the `is` value of its original (DOM §4.5 "clone a node" step 2.1.2)
      const copyIs = (from, to) => { if (isValues.size === 0) return; const a = reach(from), b = reach(to); if (a.length === b.length) a.forEach((k, i) => { const v = isValues.get(k); if (v !== undefined) isValues.set(b[i], v); }); else { const v = isValues.get(from); if (v !== undefined) isValues.set(to, v); } };
      n.clone = (id, deep) => { const c = clone0(id, deep); if (typeof c === 'number' && c >= 0) { copyIs(id, c); for (const k of reach(c)) tryUpgrade(k); } return c; };
      // tree_op 3 adopts a node; 4 and 5 import one (a clone in another document)
      n.treeOp = (id, arg, op) => {
        if (op === 3) {
          const doc0 = info(id, 7), gone = connectedId(id) ? customIn(id) : [];
          const r = treeOp0(id, arg, op);
          if (typeof r === 'number' && r < 0) return r;
          for (const el of gone) callback(el, 'disconnectedCallback', []);
          const doc1 = info(id, 7);
          if (doc1 !== doc0) for (const el of customIn(id)) callback(el, 'adoptedCallback', [wrap(doc0), wrap(doc1)]);
          return r;
        }
        const r = treeOp0(id, arg, op);
        if ((op === 4 || op === 5) && typeof r === 'number' && r >= 0) { copyIs(id, r); for (const k of reach(r)) tryUpgrade(k); }
        return r;
      };
    };
    class CustomElementRegistry {
      constructor() { throw new TypeError('Illegal constructor'); }
      define(name, constructor, options = undefined) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'define' on 'CustomElementRegistry': 2 arguments required.");
        name = String(name);
        if (!isCtor(constructor)) throw new TypeError("Failed to execute 'define' on 'CustomElementRegistry': parameter 2 is not a constructor.");
        if (options !== undefined && options !== null && typeof options !== 'object' && typeof options !== 'function') throw new TypeError("Failed to execute 'define' on 'CustomElementRegistry': parameter 3 is not an object.");
        const ext = options === undefined || options === null ? undefined : options.extends;
        if (!validName(name)) throw new DOMException(`"${name}" is not a valid custom element name`, 'SyntaxError');
        if (defsByName.has(name)) throw new DOMException(`the name "${name}" has already been used with this registry`, 'NotSupportedError');
        if (defsByCtor.has(constructor)) throw new DOMException('this constructor has already been used with this registry', 'NotSupportedError');
        let localName = name;
        if (ext !== undefined) {
          const e = String(ext);
          if (validName(e)) throw new DOMException(`"${e}" is a valid custom element name`, 'NotSupportedError');
          if (!Object.prototype.hasOwnProperty.call(htmlClasses, e) && !plainHTMLElements.has(e)) throw new DOMException(`"${e}" is not the name of an HTML element`, 'NotSupportedError');
          localName = e;
        }
        if (defining) throw new DOMException('a custom element definition is running', 'NotSupportedError');
        defining = true;
        let made;
        try {
          const prototype = constructor.prototype;
          if (prototype === null || (typeof prototype !== 'object' && typeof prototype !== 'function')) throw new TypeError('The "prototype" of the constructor is not an object.');
          const callbacks = {};
          const read = k => { const v = prototype[k]; if (v !== undefined) { if (typeof v !== 'function') throw new TypeError(`"${k}" is not a function.`); callbacks[k] = v; } };
          for (const k of ['connectedCallback', 'disconnectedCallback', 'adoptedCallback', 'attributeChangedCallback']) read(k);
          let observed = [];
          if (callbacks.attributeChangedCallback) { const oa = constructor.observedAttributes; if (oa !== undefined) observed = [...oa].map(String); }
          const df = constructor.disabledFeatures, disabled = df === undefined ? [] : [...df].map(String);
          const formAssociated = !!constructor.formAssociated;
          if (formAssociated) for (const k of ['formAssociatedCallback', 'formResetCallback', 'formDisabledCallback', 'formStateRestoreCallback']) read(k);
          made = { name, localName, constructor, observed: new Set(observed), callbacks, stack: [], formAssociated,
            disableInternals: disabled.includes('internals'), disableShadow: disabled.includes('shadow') };
        } finally { defining = false; }
        defsByName.set(name, made); defsByCtor.set(constructor, made);
        if (!ceActive) { ceActive = true; wrapNatives(); }
        // the elements of the document that the definition matches, in shadow-including tree order
        for (const k of reach(0)) if (lookup(k) === made) tryUpgrade(k);
        const w = waiting.get(name);
        if (w) { waiting.delete(name); w.resolve(constructor); }
      }
      get(name) { if (arguments.length < 1) throw new TypeError("Failed to execute 'get' on 'CustomElementRegistry': 1 argument required."); const d = defsByName.get(String(name)); return d ? d.constructor : undefined; }
      getName(constructor) {
        if (arguments.length < 1 || (typeof constructor !== 'function' && !isCtor(constructor))) throw new TypeError("Failed to execute 'getName' on 'CustomElementRegistry': parameter 1 is not a function.");
        const d = defsByCtor.get(constructor); return d ? d.name : null;
      }
      whenDefined(name) {
        if (arguments.length < 1) return Promise.reject(new TypeError("Failed to execute 'whenDefined' on 'CustomElementRegistry': 1 argument required."));
        name = String(name);
        if (!validName(name)) return Promise.reject(new DOMException(`"${name}" is not a valid custom element name`, 'SyntaxError'));
        const d = defsByName.get(name);
        if (d) return Promise.resolve(d.constructor);
        let w = waiting.get(name);
        if (!w) { w = {}; w.promise = new Promise(resolve => { w.resolve = resolve; }); waiting.set(name, w); }
        return w.promise;
      }
      upgrade(root) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'upgrade' on 'CustomElementRegistry': 1 argument required.");
        for (const k of reach(nodeId(root))) tryUpgrade(k);
      }
    }
    def('CustomElementRegistry', CustomElementRegistry);
    def('customElements', Object.create(CustomElementRegistry.prototype));
    // ElementInternals (HTML §4.13.7): the shadow root, the custom states, the form value of
    // a form-associated element, and the default ARIA semantics (ARIAMixin as plain values).
    const internalsOf = new Map(), internalsState = new WeakMap();   // internalsOf: by node number
    const inState = x => { const st = internalsState.get(x); if (!st) throw new TypeError('not an ElementInternals'); return st; };
    const formAssociated = (x, what) => { const st = inState(x); if (!st.def.formAssociated) throw new DOMException(`'${what}' needs a form-associated custom element.`, 'NotSupportedError'); return st; };
    class CustomStateSet {
      constructor() { throw new TypeError('Illegal constructor'); }
      get size() { return stateSets.get(this).size; }
      add(v) { stateSets.get(this).add(String(v)); return this; }
      delete(v) { return stateSets.get(this).delete(String(v)); }
      has(v) { return stateSets.get(this).has(String(v)); }
      clear() { stateSets.get(this).clear(); }
      forEach(f, thisArg) { for (const v of [...stateSets.get(this)]) f.call(thisArg, v, v, this); }
      keys() { return stateSets.get(this).values(); }
      values() { return stateSets.get(this).values(); }
      entries() { return stateSets.get(this).entries(); }
      [Symbol.iterator]() { return stateSets.get(this).values(); }
    }
    const stateSets = new WeakMap();
    class ElementInternals {
      constructor() { throw new TypeError('Illegal constructor'); }
      get shadowRoot() { const st = inState(this), k = info(nodeId(st.el), 26); return k >= 0 && !st.hideShadow ? wrap(k) : null; }
      get states() { const st = inState(this); if (!st.states) { st.states = Object.create(CustomStateSet.prototype); stateSets.set(st.states, new Set()); } return st.states; }
      setFormValue(value, state) { const st = formAssociated(this, 'setFormValue'); st.value = value; st.restore = arguments.length < 2 ? value : state; }
      get form() { const st = formAssociated(this, 'form'); return formOf(st.el); }
      get willValidate() { const st = formAssociated(this, 'willValidate'); return !st.el.hasAttribute('disabled') && !st.el.hasAttribute('readonly'); }
      get labels() { const st = formAssociated(this, 'labels'), el = st.el; return staticList([...(el.getRootNode()).querySelectorAll('label')].filter(l => l.control === el)); }
    }
    def('ElementInternals', ElementInternals); def('CustomStateSet', CustomStateSet);
    const ariaRows = n.query(0, 162, 'Element');
    for (const line of (typeof ariaRows === 'string' ? ariaRows : '').split('\u0000')) {
      const [, idl, k] = line.split(' ');
      if (k !== 'E') continue;
      Object.defineProperty(ElementInternals.prototype, idl, { get() { return inState(this).aria.get(idl) ?? null; },
        set(v) { const m = inState(this).aria; if (v === null || v === undefined) m.delete(idl); else m.set(idl, String(v)); }, configurable: true, enumerable: true });
    }
    define(HTMLElement.prototype, 'attachInternals', function attachInternals() {
      const id = nodeId(this), st = ceState.get(this), d = st && st.def;
      if (!d || d.localName !== d.name) throw new DOMException('attachInternals needs an autonomous custom element.', 'NotSupportedError');
      if (d.disableInternals) throw new DOMException('ElementInternals is disabled for this custom element.', 'NotSupportedError');
      if (internalsOf.has(id)) throw new DOMException('ElementInternals was already attached.', 'NotSupportedError');
      if (st.state !== 'precustomized' && st.state !== 'custom') throw new DOMException('The element is not a custom element yet.', 'NotSupportedError');
      const x = Object.create(ElementInternals.prototype);
      internalsState.set(x, { el: this, def: d, aria: new Map(), states: null, value: null, restore: null, hideShadow: false });
      internalsOf.set(id, x);
      return x;
    });
    // createElement and createElementNS make a custom element with its constructor
    // (HTML §4.13.3 "create an element", synchronously), and keep the `is` value.
    const made = (id, options) => {
      const is = options !== null && typeof options === 'object' && options.is !== undefined && options.is !== null ? String(options.is) : undefined;
      if (is !== undefined) isValues.set(id, is);
      // a constructor that throws leaves an element in the "failed" state: HTMLUnknownElement
      // for an autonomous custom element (HTML §4.13.3 "create an element" step 6.1.4)
      if (ceActive) {
        const d = lookup(id);
        if (d) try { return upgrade(id, d, d.localName === d.name) ?? wrap(id); } catch (e) { report(e); if (d.localName === d.name) Object.setPrototypeOf(wrap(id), HTMLUnknownElement.prototype); }
      }
      return wrap(id);
    };
    define(Document.prototype, 'createElement', function createElement(name, options = undefined) {
      name = String(name);
      const id = chk(n.create(3 + 16 * nodeId(this), name));
      if (name.length === 6 && name.toLowerCase() === 'script') noteFreshScript(id);
      else if (ttMeta !== null && name.length === 4 && name.toLowerCase() === 'meta') ttMeta();
      return made(id, options);
    });
    define(Document.prototype, 'createElementNS', function createElementNS(ns, qname, options = undefined) {
      if (arguments.length < 2) throw new TypeError('createElementNS: 2 arguments required');
      qname = String(qname);
      const id = chk(n.create(4 + 16 * nodeId(this), nsArg(ns) + '\u0000' + qname));
      if (qname.endsWith('script')) noteFreshScript(id);
      return made(id, options);
    });
  }
  // ==== end customelements ================================================================
  def('location', location);
  def('navigator', Object.freeze({ userAgent: 'Foafnaut', language: 'en', languages: ['en'], platform: '', onLine: true,
    cookieEnabled: false, hardwareConcurrency: 1, gpu }));
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
  for (const C of [...glClasses, WebGLActiveInfo, WebGLShaderPrecisionFormat, WebGLContextEvent]) def(C.name, C);
  // pagewasm: a data property once read (WebIDL); before that an accessor that compiles the glue.
  if (wasmServed) Object.defineProperty(globalThis, 'WebAssembly', { configurable: true, enumerable: false,
    // QuickJS-NG hands the glue's function (bytecode); BubblePopJS hands its source.
    get() { const g = n.wasmGlue(), W = (typeof g === 'function' ? g : (0, eval)(g))(n, define); def('WebAssembly', W); return W; },
    set(v) { def('WebAssembly', v); } });
  def('history', Object.freeze({ length: 1, state: null, pushState() {}, replaceState() {}, back() {}, forward() {}, go() {} }));
  def('screen', Object.freeze({ width: 800, height: 600, availWidth: 800, availHeight: 600, colorDepth: 24, pixelDepth: 24 }));
  for (const [k, i] of [['innerWidth', 0], ['innerHeight', 1], ['outerWidth', 0], ['outerHeight', 1]])
    Object.defineProperty(globalThis, k, { get: () => viewport()[i], set(v) {}, configurable: true, enumerable: true });
  // ==== dprfix ==== devicePixelRatio (CSSOM View §4): the screen's device pixels for each
  // CSS pixel, from Lean (node_query 22: the layout request's zoomUnit, no layout); 1 when
  // the engine has no answer. Layout and every length a script reads are CSS pixels.
  Object.defineProperty(globalThis, 'devicePixelRatio', { get: () => { const r = query(0, 22, 1)[0]; return r > 0 ? r : 1; },
    set(v) {}, configurable: true, enumerable: true });
  def('scrollX', 0); def('scrollY', 0);
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
  // A group of interfaces made together on first use: reading one name defines them all as
  // the data properties Web IDL asks for (writable, configurable, not enumerable).
  const lazyGroup = (names, make) => {
    for (const name of names) Object.defineProperty(globalThis, name, { configurable: true, enumerable: false,
      get() {
        const made = apiOn() ? make() : undefined;
        if (!made) { for (const k of names) delete globalThis[k]; return undefined; }
        for (const k of names) define(globalThis, k, made[k]);
        return made[name];
      },
      set(v) { define(globalThis, name, v); } });
  };
  // The WebGL rendering context interfaces (made from Lean's table when a page first names one).
  lazyGroup(['WebGLRenderingContext', 'WebGL2RenderingContext'], () => {
    const a = glInterface(1), b = glInterface(2);
    return a && b ? { WebGLRenderingContext: a, WebGL2RenderingContext: b } : undefined;
  });
  // What the section needs of the page's other objects (filled in below it).
  const codecsHost = {};
  // ==== WebCodecs (docs/designissues/2026-11-14-webgl-webcodecs.md) ==== begin webcodecs section ====
  // Page-facing objects only. What a frame is (its layout, visible rectangle, display size and
  // rotation), which rows a copy moves, and whether a codec configuration is valid or supported
  // are Lean's answers (L4Factoidal.WebCodecs, web_api ops 120 to 139): this converts arguments
  // (Web IDL), keeps the bytes and moves the rows Lean lists. The section is text until a page
  // first names one of its interfaces, so other pages carry no more JavaScript.
  let codecsMade = null;
  const codecs = () => codecsMade ??= new Function('apiCall', 'DOMException', 'EventTarget', 'DOMRectReadOnly', 'queueMicrotask',
    'reportError', 'structuredClone', 'host', codecsSource)(apiCall, DOMException, EventTarget, DOMRectReadOnly,
    f => { Promise.resolve().then(f); }, e => report(e), (v, o) => globalThis.structuredClone(v, o), codecsHost);
  const codecsSource = `'use strict';
    // Each object's state is here, never on the object: a method called on another object
    // finds none and throws (Web IDL brand check).
    const K = new WeakMap();
    const st = o => { const s = K.get(o); if (!s) throw new TypeError('Illegal invocation'); return s; };
    const need = (got, k, what) => { if (got < k) throw new TypeError("Failed to execute '" + what + "': " + k + ' argument' + (k === 1 ? '' : 's') + ' required, but only ' + got + ' present.'); };
    const bad = what => new TypeError('WebCodecs: ' + what);
    const dom = (name, what) => new DOMException(what, name);
    // One operation of Lean's (WebCodecs.Api): text, or a TypeError when Lean refuses.
    const ask = (op, args, what) => { const r = apiCall(op, args, 0, false); if (typeof r !== 'string') throw bad(what); return r; };
    const nums = line => line === '' ? [] : line.split(' ').map(Number);
    // Web IDL conversions.
    const dict = (x, what) => { if (x === undefined || x === null) return {}; if (typeof x !== 'object' && typeof x !== 'function') throw bad(what + ' is not an object'); return x; };
    const enforce = (v, max, what) => {
      let x = Number(v);
      if (x !== x || x === Infinity || x === -Infinity) throw bad(what + ' is not a finite number');
      x = Math.trunc(x);
      if (x < 0 || x > max) throw bad(what + ' is out of range');
      return x + 0;
    };
    const enforceSigned = (v, what) => {
      let x = Number(v);
      if (x !== x || x === Infinity || x === -Infinity) throw bad(what + ' is not a finite number');
      x = Math.trunc(x);
      if (x < -9007199254740991 || x > 9007199254740991) throw bad(what + ' is out of range');
      return x + 0;
    };
    const U32 = 4294967295, U64 = 9007199254740991;
    const oneOf = (v, values, what) => { const s = String(v); if (!values.includes(s)) throw bad("'" + s + "' is not a value of " + what); return s; };
    const isShared = x => typeof SharedArrayBuffer === 'function' && x instanceof SharedArrayBuffer;
    // The bytes of an AllowSharedBufferSource, as a view (no copy).
    const bytesOf = (x, what) => {
      if (x instanceof ArrayBuffer || isShared(x)) { if (x.detached) throw bad(what + ' is detached'); return new Uint8Array(x); }
      if (ArrayBuffer.isView(x)) { if (x.buffer.detached) throw bad(what + ' is detached'); return new Uint8Array(x.buffer, x.byteOffset, x.byteLength); }
      throw bad(what + ' is not a buffer source');
    };
    // transfer: each buffer is detached once the bytes are taken (a buffer listed twice is a DataCloneError).
    const transferList = (init, what) => {
      if (init.transfer === undefined) return [];
      const list = Array.from(init.transfer);
      for (const b of list) if (!(b instanceof ArrayBuffer)) throw bad(what + ': transfer holds a value that is not an ArrayBuffer');
      if (new Set(list).size !== list.length) throw dom('DataCloneError', what + ': a buffer is in transfer twice');
      for (const b of list) if (b.detached) throw dom('DataCloneError', what + ': a buffer in transfer is detached');
      return list;
    };
    const detach = list => { for (const b of list) { try { if (typeof b.transfer === 'function') b.transfer(); else structuredClone(b, { transfer: [b] }); } catch (e) {} } };
    const getters = (C, names, read) => { for (const k of names) Object.defineProperty(C.prototype, k, { get: Object.defineProperty(function () { return read(st(this), k); }, 'name', { value: 'get ' + k }), enumerable: true, configurable: true }); };
    const members = C => {
      Object.defineProperty(C.prototype, Symbol.toStringTag, { value: C.name, configurable: true });
      for (const k of Object.getOwnPropertyNames(C.prototype)) {
        if (k === 'constructor') continue;
        const d = Object.getOwnPropertyDescriptor(C.prototype, k);
        if (d.configurable && !d.enumerable) { d.enumerable = true; Object.defineProperty(C.prototype, k, d); }
      }
      for (const k of Object.getOwnPropertyNames(C)) {
        if (k === 'prototype' || k === 'length' || k === 'name') continue;
        const d = Object.getOwnPropertyDescriptor(C, k);
        if (d.configurable && !d.enumerable) { d.enumerable = true; Object.defineProperty(C, k, d); }
      }
      return C;
    };

    // ---- VideoColorSpace (WebCodecs 9.9) ----
    const PRIMARIES = ['bt709', 'bt470bg', 'smpte170m', 'bt2020', 'smpte432'];
    const TRANSFER = ['bt709', 'smpte170m', 'iec61966-2-1', 'linear', 'pq', 'hlg'];
    const MATRIX = ['rgb', 'bt709', 'bt470bg', 'smpte170m', 'bt2020-ncl'];
    const colorInit = init => {
      const d = dict(init, 'VideoColorSpaceInit'), opt = (v, values, what) => v === undefined || v === null ? null : oneOf(v, values, what);
      return { primaries: opt(d.primaries, PRIMARIES, 'VideoColorPrimaries'), transfer: opt(d.transfer, TRANSFER, 'VideoTransferCharacteristics'),
        matrix: opt(d.matrix, MATRIX, 'VideoMatrixCoefficients'), fullRange: d.fullRange === undefined || d.fullRange === null ? null : !!d.fullRange };
    };
    class VideoColorSpace {
      constructor(init = undefined) { K.set(this, colorInit(init)); }
      toJSON() { const s = st(this); return { fullRange: s.fullRange, matrix: s.matrix, primaries: s.primaries, transfer: s.transfer }; }
    }
    getters(VideoColorSpace, ['primaries', 'transfer', 'matrix', 'fullRange'], (s, k) => s[k]);
    const colorSpaceOf = v => { const c = Object.create(VideoColorSpace.prototype); K.set(c, v); return c; };

    // ---- VideoFrame (WebCodecs 9.4) ----
    // The frame's values and layout are Lean's (WebCodecs.Frame, WebCodecs.Layout): this reads
    // the init (Web IDL), keeps the resource's bytes and moves the rows Lean lists.
    const FORMATS = ['I420', 'I420P10', 'I420P12', 'I420A', 'I420AP10', 'I420AP12', 'I422', 'I422P10', 'I422P12', 'I422A', 'I422AP10',
      'I422AP12', 'I444', 'I444P10', 'I444P12', 'I444A', 'I444AP10', 'I444AP12', 'NV12', 'RGBA', 'RGBX', 'BGRA', 'BGRX'];
    const RGB = ['RGBA', 'RGBX', 'BGRA', 'BGRX'];
    const rectArg = (r, what) => {
      if (r === undefined) return '';
      const d = dict(r, what), part = k => {
        const x = d[k] === undefined ? 0 : Number(d[k]);
        if (x !== x || x === Infinity || x === -Infinity || x < 0) throw bad(what + '.' + k + ' is negative or not finite');
        return Math.trunc(x);
      };
      return [part('x'), part('y'), part('width'), part('height')].join(' ');
    };
    const layoutArg = (l, what) => {
      if (l === undefined) return '';
      const out = [];
      for (const p of Array.from(l)) {
        const d = dict(p, what);
        if (d.offset === undefined || d.stride === undefined) throw bad(what + ': a PlaneLayout needs offset and stride');
        out.push(enforce(d.offset, U32, 'offset'), enforce(d.stride, U32, 'stride'));
      }
      // An empty list has no planes: no format has none, so Lean refuses it by the count.
      return out.length ? out.join(' ') : '0';
    };
    const displayArg = d => {
      const w = d.displayWidth === undefined ? undefined : enforce(d.displayWidth, U32, 'displayWidth');
      const h = d.displayHeight === undefined ? undefined : enforce(d.displayHeight, U32, 'displayHeight');
      return w === undefined && h === undefined ? '' : w === undefined || h === undefined ? '-' : w + ' ' + h;
    };
    // The page's double, exactly: its eight bytes (Lean reads sign, mantissa and exponent).
    const rotationArg = v => {
      if (v === undefined) return '';
      const x = Number(v);
      if (x !== x || x === Infinity || x === -Infinity) throw bad('rotation is not a finite number');
      return new Uint8Array(new Float64Array([x]).buffer);
    };
    const initArgs = d => [rectArg(d.visibleRect, 'visibleRect'), displayArg(d), rotationArg(d.rotation), d.flip ? '1' : ''];
    const metaOf = line => { const m = nums(line); return { cw: m[0], ch: m[1], vx: m[2], vy: m[3], vw: m[4], vh: m[5], dw: m[6], dh: m[7], rotation: m[8], flip: m[9] === 1 }; };
    const metaLine = s => [s.cw, s.ch, s.vx, s.vy, s.vw, s.vh, s.dw, s.dh, s.rotation, s.flip ? 1 : 0].join(' ');
    // The rows Lean lists, copied (each line: source offset and stride, destination offset and stride, bytes a row, rows).
    const move = (src, dst, lines) => {
      for (const line of lines) {
        const m = nums(line);
        for (let r = 0; r < m[5]; r++) { const a = m[0] + r * m[1]; dst.set(src.subarray(a, a + m[4]), m[2] + r * m[3]); }
      }
    };
    const rectOf = (x, y, w, h) => new DOMRectReadOnly(x, y, w, h);
    const live = (s, what) => { if (s.closed) throw dom('InvalidStateError', what + ': the VideoFrame is closed'); return s; };
    const frameOf = s => { const f = Object.create(VideoFrame.prototype); K.set(f, s); return f; };
    const optionsOf = (s, options) => {
      const d = dict(options, 'VideoFrameCopyToOptions');
      const rect = rectArg(d.rect, 'rect'), layout = layoutArg(d.layout, 'layout');
      const format = d.format === undefined ? undefined : oneOf(d.format, FORMATS, 'VideoPixelFormat');
      const space = d.colorSpace === undefined ? undefined : oneOf(d.colorSpace, ['srgb', 'display-p3'], 'PredefinedColorSpace');
      if (format !== undefined && format !== s.format && !RGB.includes(format)) throw dom('NotSupportedError', 'copyTo converts to RGBA, RGBX, BGRA and BGRX only');
      return { rect: rect === '' ? [s.vx, s.vy, s.vw, s.vh].join(' ') : rect, layout, format: format === undefined ? s.format : format, space };
    };
    class VideoFrame {
      constructor(image, init = undefined) {
        need(arguments.length, 1, 'VideoFrame');
        if (image instanceof VideoFrame) {
          const b = K.get(image), d = dict(init, 'VideoFrameInit');
          if (!b || b.closed) throw dom('InvalidStateError', 'VideoFrame: the source frame is closed');
          const alpha = d.alpha === undefined ? 'keep' : oneOf(d.alpha, ['keep', 'discard'], 'AlphaOption');
          const m = metaOf(ask(121, [b.format, metaLine(b)].concat(initArgs(d)), 'the VideoFrameInit is not valid for the source frame'));
          let format = b.format, resource = b.resource;
          if (alpha === 'discard') {
            // The format without alpha; its bytes are the first bytes of the source's (Lean: dropAlpha_planes).
            const a = ask(123, [b.format, String(b.cw), String(b.ch)], 'the frame has no format').split(' ');
            format = a[0]; resource = b.resource.subarray(0, Number(a[1]));
          }
          K.set(this, Object.assign({}, b, m, { format, resource,
            duration: d.duration === undefined ? b.duration : enforce(d.duration, U64, 'duration'),
            timestamp: d.timestamp === undefined ? b.timestamp : enforceSigned(d.timestamp, 'timestamp') }));
          return;
        }
        if (image instanceof ArrayBuffer || isShared(image) || ArrayBuffer.isView(image)) {
          need(arguments.length, 2, 'VideoFrame');
          const d = dict(init, 'VideoFrameBufferInit');
          if (d.format === undefined || d.codedWidth === undefined || d.codedHeight === undefined || d.timestamp === undefined)
            throw bad('VideoFrameBufferInit needs format, codedWidth, codedHeight and timestamp');
          const format = oneOf(d.format, FORMATS, 'VideoPixelFormat');
          const cw = enforce(d.codedWidth, U32, 'codedWidth'), ch = enforce(d.codedHeight, U32, 'codedHeight');
          const timestamp = enforceSigned(d.timestamp, 'timestamp');
          const duration = d.duration === undefined ? null : enforce(d.duration, U64, 'duration');
          const layout = layoutArg(d.layout, 'layout');
          const args = initArgs(d);
          const color = d.colorSpace === undefined ? undefined : colorInit(d.colorSpace);
          const transfer = transferList(d, 'VideoFrame');
          const data = bytesOf(image, 'data');
          const lines = ask(120, [format, String(cw), String(ch), String(data.byteLength), layout].concat(args), 'the VideoFrameBufferInit is not valid for the data').split('\\n');
          const resource = new Uint8Array(Number(lines[0]));
          move(data, resource, lines.slice(3));
          detach(transfer);
          const c = lines[2].split(' ');
          // RGBX and BGRX: the fourth byte is padding, kept opaque (Lean says which formats).
          if (c[4] === '1') for (let i = 3; i < resource.length; i += 4) resource[i] = 255;
          K.set(this, Object.assign(metaOf(lines[1]), { format, timestamp, duration, resource, closed: false,
            color: color === undefined ? { primaries: c[0], transfer: c[1], matrix: c[2], fullRange: c[3] === '1' } : color }));
          return;
        }
        const s = imageFrame(image, dict(init, 'VideoFrameInit'));
        if (!s) throw bad('the image is not a CanvasImageSource or a buffer');
        K.set(this, s);
      }
      get format() { const s = st(this); return s.closed ? null : s.format; }
      get codedWidth() { const s = st(this); return s.closed ? 0 : s.cw; }
      get codedHeight() { const s = st(this); return s.closed ? 0 : s.ch; }
      get codedRect() { const s = st(this); return s.closed ? null : rectOf(0, 0, s.cw, s.ch); }
      get visibleRect() { const s = st(this); return s.closed ? null : rectOf(s.vx, s.vy, s.vw, s.vh); }
      get rotation() { const s = st(this); return s.closed ? 0 : s.rotation; }
      get flip() { const s = st(this); return s.closed ? false : s.flip; }
      get displayWidth() { const s = st(this); return s.closed ? 0 : s.dw; }
      get displayHeight() { const s = st(this); return s.closed ? 0 : s.dh; }
      get duration() { return st(this).duration; }
      get timestamp() { return st(this).timestamp; }
      get colorSpace() { const s = st(this); return colorSpaceOf(s.closed ? { primaries: null, transfer: null, matrix: null, fullRange: null } : s.color); }
      metadata() { live(st(this), 'metadata'); return {}; }
      allocationSize(options = undefined) {
        const s = live(st(this), 'allocationSize'), o = optionsOf(s, options);
        if (o.format !== s.format) return Number(ask(122, [o.format, String(nums(o.rect)[2]), String(nums(o.rect)[3]), '', o.layout, ''], 'the options are not valid for the frame').split('\\n')[0]);
        return Number(ask(122, [s.format, String(s.cw), String(s.ch), o.rect, o.layout, ''], 'the options are not valid for the frame').split('\\n')[0]);
      }
      copyTo(destination, options = undefined) {
        try {
          need(arguments.length, 1, 'copyTo');
          const s = live(st(this), 'copyTo'), o = optionsOf(s, options);
          const dst = bytesOf(destination, 'destination');
          let src = s.resource, lines;
          if (o.format !== s.format) {
            // To RGB: Lean converts the rectangle to packed pixels; the rows then go as any RGBA frame's.
            const r = nums(o.rect);
            src = convertFrame(s, o);
            lines = ask(122, [o.format, String(r[2]), String(r[3]), '', o.layout, String(dst.byteLength)], 'the destination or the options are not valid for the frame').split('\\n');
          } else lines = ask(122, [s.format, String(s.cw), String(s.ch), o.rect, o.layout, String(dst.byteLength)], 'the destination or the options are not valid for the frame').split('\\n');
          move(src, dst, lines.slice(1));
          return Promise.resolve(lines.slice(1).map(line => { const m = nums(line); return { offset: m[2], stride: m[3] }; }));
        } catch (e) { return Promise.reject(e); }
      }
      clone() { const s = live(st(this), 'clone'); return frameOf(Object.assign({}, s)); }
      close() { const s = st(this); s.closed = true; s.resource = null; }
    }
    // A frame from an image needs the image's pixels (the canvas section's): not connected yet.
    const imageFrame = (image, d) => { throw dom('NotSupportedError', 'VideoFrame from an image is not supported yet'); };
    // The rectangle as packed pixels of an RGB format: Lean's conversion (WebCodecs.Convert.toRgb).
    // It keeps the frame's primaries and transfer: a destination that is not sRGB is refused.
    const convertFrame = (s, o) => {
      if (o.space !== undefined && o.space !== 'srgb') throw dom('NotSupportedError', 'copyTo converts to sRGB only');
      const r = apiCall(124, [s.format, String(s.cw), String(s.ch), o.rect, o.format, s.color.matrix === null ? '' : s.color.matrix, s.color.fullRange ? '1' : '', s.resource], 0, true);
      if (typeof r === 'number') throw dom('NotSupportedError', 'copyTo does not convert this frame');
      return new Uint8Array(r);
    };

    // ---- EncodedVideoChunk, EncodedAudioChunk (WebCodecs 8) ----
    const chunkInit = (init, what) => {
      const d = dict(init, what);
      if (d.type === undefined || d.timestamp === undefined || d.data === undefined) throw bad(what + ' needs type, timestamp and data');
      const type = oneOf(d.type, ['key', 'delta'], 'the chunk type');
      const timestamp = enforceSigned(d.timestamp, 'timestamp');
      const duration = d.duration === undefined ? null : enforce(d.duration, U64, 'duration');
      const transfer = transferList(d, what);
      const data = bytesOf(d.data, 'data').slice();
      detach(transfer);
      return { type, timestamp, duration, data };
    };
    const chunkCopy = (s, destination) => {
      const dst = bytesOf(destination, 'destination');
      if (dst.byteLength < s.data.byteLength) throw bad('the destination is smaller than the chunk');
      dst.set(s.data);
    };
    class EncodedVideoChunk {
      constructor(init) { need(arguments.length, 1, 'EncodedVideoChunk'); K.set(this, chunkInit(init, 'EncodedVideoChunkInit')); }
      copyTo(destination) { need(arguments.length, 1, 'copyTo'); chunkCopy(st(this), destination); }
    }
    class EncodedAudioChunk {
      constructor(init) { need(arguments.length, 1, 'EncodedAudioChunk'); K.set(this, chunkInit(init, 'EncodedAudioChunkInit')); }
      copyTo(destination) { need(arguments.length, 1, 'copyTo'); chunkCopy(st(this), destination); }
    }
    for (const C of [EncodedVideoChunk, EncodedAudioChunk]) getters(C, ['type', 'timestamp', 'duration', 'byteLength'], (s, k) => k === 'byteLength' ? s.data.byteLength : s[k]);

    // ---- The four codecs (WebCodecs 3 to 6) ----
    // Whether a configuration is valid, and whether it is supported, are Lean's answers
    // (WebCodecs.Config.check). This engine has no encoder or decoder: a valid configuration
    // closes the codec with a NotSupportedError, as the standard says for an unsupported one.
    const CONFIG = {
      AudioDecoder: { required: ['sampleRate', 'numberOfChannels'], nums: [] },
      VideoDecoder: { required: [], nums: ['codedWidth', 'codedHeight', 'displayAspectWidth', 'displayAspectHeight'] },
      AudioEncoder: { required: ['sampleRate', 'numberOfChannels'], nums: ['bitrate'], sub: { opus: ['complexity', 'packetlossperc', 'frameDuration'] } },
      VideoEncoder: { required: ['width', 'height'], nums: ['displayWidth', 'displayHeight', 'bitrate'] },
    };
    // The verdict on a configuration: 'invalid', 'unsupported' or 'supported'. Reads the members (Web IDL).
    const checkConfig = (kind, config) => {
      const d = dict(config, kind + 'Config'), shape = CONFIG[kind], lines = [];
      if (d.codec === undefined) throw bad(kind + ': the configuration has no codec');
      const codec = String(d.codec);
      for (const k of shape.required) { if (d[k] === undefined) throw bad(kind + ': the configuration has no ' + k); lines.push(k + '=' + enforce(d[k], U64, k)); }
      for (const k of shape.nums) if (d[k] !== undefined) lines.push(k + '=' + enforce(d[k], U64, k));
      for (const g of Object.keys(shape.sub || {})) {
        if (d[g] === undefined) continue;
        const sub = dict(d[g], g);
        for (const k of shape.sub[g]) if (sub[k] !== undefined) lines.push(g + '.' + k + '=' + enforce(sub[k], U64, k));
      }
      let detached = '';
      if (d.description !== undefined && d.description !== null) {
        const x = d.description, b = x instanceof ArrayBuffer || isShared(x) ? x : ArrayBuffer.isView(x) ? x.buffer : null;
        if (b === null) throw bad(kind + ': the description is not a buffer source');
        if (b.detached) detached = '1';
      }
      const verdict = ask(125, [kind, codec, lines.join('\\n'), detached], 'the configuration is not valid');
      if (verdict === 'invalid') throw bad(kind + ': the configuration is not valid');
      return verdict;
    };
    const cloneConfig = config => { const out = {}; for (const k of Object.keys(config)) out[k] = config[k]; return out; };
    const codecInit = (init, what, outputType) => {
      const d = dict(init, what + 'Init');
      if (typeof d.output !== 'function' || typeof d.error !== 'function') throw bad(what + 'Init needs the output and error callbacks');
      return { state: 'unconfigured', queue: 0, output: d.output, error: d.error, ondequeue: null, flushes: [] };
    };
    const closeCodec = (s, error) => {
      // "Close codec" (WebCodecs 3.5 and its siblings): pending flushes are rejected; the error callback runs unless it is an abort.
      s.state = 'closed';
      for (const f of s.flushes.splice(0)) f.reject(error);
      if (error.name !== 'AbortError') { try { s.error.call(undefined, error); } catch (e) { reportError(e); } }
    };
    const makeCodec = (kind, inputType, work, queueName) => {
      const C = class extends EventTarget {
        constructor(init) { super(); need(arguments.length, 1, kind); K.set(this, codecInit(init, kind)); }
        get state() { return st(this).state; }
        get ondequeue() { return st(this).ondequeue; }
        set ondequeue(f) {
          const s = st(this);
          if (s.ondequeue) this.removeEventListener('dequeue', s.ondequeue);
          s.ondequeue = typeof f === 'function' ? f : null;
          if (s.ondequeue) this.addEventListener('dequeue', s.ondequeue);
        }
        configure(config) {
          need(arguments.length, 1, 'configure');
          const s = st(this), verdict = checkConfig(kind, config);
          if (s.state === 'closed') throw dom('InvalidStateError', kind + ': the codec is closed');
          s.state = 'configured';
          // Not supported: the codec closes with a NotSupportedError, as a queued control message.
          if (verdict !== 'supported') queueMicrotask(() => { if (s.state !== 'closed') closeCodec(s, dom('NotSupportedError', kind + ': the configuration is not supported')); });
        }
        flush() {
          const s = st(this);
          if (s.state !== 'configured') return Promise.reject(dom('InvalidStateError', kind + ': the codec is not configured'));
          return new Promise((resolve, reject) => { s.flushes.push({ resolve, reject }); });
        }
        reset() {
          const s = st(this);
          if (s.state === 'closed') throw dom('InvalidStateError', kind + ': the codec is closed');
          s.state = 'unconfigured'; s.queue = 0;
          for (const f of s.flushes.splice(0)) f.reject(dom('AbortError', kind + ': the codec was reset'));
        }
        close() {
          const s = st(this);
          if (s.state === 'closed') throw dom('InvalidStateError', kind + ': the codec is closed');
          closeCodec(s, dom('AbortError', kind + ': the codec was closed'));
        }
        static isConfigSupported(config) {
          try {
            need(arguments.length, 1, 'isConfigSupported');
            const verdict = checkConfig(kind, config);
            return Promise.resolve({ supported: verdict === 'supported', config: cloneConfig(config) });
          } catch (e) { return Promise.reject(e); }
        }
      };
      Object.defineProperty(C, 'name', { value: kind, configurable: true });
      const run = function (input, options) {
        need(arguments.length, 1, work);
        const s = st(this);
        if (!(input instanceof inputType())) throw bad(work + ': the argument is not of the expected interface');
        if (s.state !== 'configured') throw dom('InvalidStateError', kind + ': the codec is not configured');
        // Reached only between configure() and the close that follows an unsupported configuration.
        s.queue++;
      };
      Object.defineProperty(run, 'name', { value: work, configurable: true });
      Object.defineProperty(run, 'length', { value: 1, configurable: true });
      Object.defineProperty(C.prototype, work, { value: run, writable: true, enumerable: true, configurable: true });
      getters(C, [queueName], s => s.queue);
      return members(C);
    };
    const AudioDecoder = makeCodec('AudioDecoder', () => EncodedAudioChunk, 'decode', 'decodeQueueSize');
    const VideoDecoder = makeCodec('VideoDecoder', () => EncodedVideoChunk, 'decode', 'decodeQueueSize');
    const AudioEncoder = makeCodec('AudioEncoder', () => AudioData, 'encode', 'encodeQueueSize');
    const VideoEncoder = makeCodec('VideoEncoder', () => VideoFrame, 'encode', 'encodeQueueSize');
    // AudioData arrives with the audio layout ops; the name is held so that encode can test its argument.
    class AudioData { constructor() { throw dom('NotSupportedError', 'AudioData is not supported yet'); } }
    for (const C of [VideoColorSpace, VideoFrame, EncodedVideoChunk, EncodedAudioChunk]) members(C);
    return { VideoColorSpace, VideoFrame, EncodedVideoChunk, EncodedAudioChunk, AudioDecoder, VideoDecoder, AudioEncoder, VideoEncoder };
`;
  const codecNames = ['VideoColorSpace', 'VideoFrame', 'EncodedVideoChunk', 'EncodedAudioChunk', 'AudioDecoder', 'VideoDecoder', 'AudioEncoder', 'VideoEncoder'];
  lazyGroup(codecNames, codecs);
  // ==== end webcodecs section ====
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

  // ---- Blob, File (File API) and FormData (XHR Standard §5) ---------------------------------
  // Byte holders: a Blob keeps a copy of its bytes and its type; FormData keeps its entries.
  // The multipart/form-data body of a FormData is Lean's (web_api op 78, Net.Xhr.formDataBody).
  const blobs = new WeakMap();
  let BlobC, FileC, FormDataC;
  const utf8 = str => new TextEncoder().encode(usv(str));
  const blobType = t => { t = String(t); return /^[\x20-\x7e]*$/.test(t) ? t.toLowerCase() : ''; };
  const blobBytes = b => blobs.get(b).bytes;
  const makeBlob = () => {
    if (BlobC) return BlobC;
    class Blob {
      constructor(parts = undefined, options = undefined) {
        const d = dict(options, "Failed to construct 'Blob'");
        const native = d.endings === 'native';
        if (d.endings !== undefined && d.endings !== 'transparent' && !native) throw new TypeError("Failed to construct 'Blob': bad endings");
        const chunks = [];
        if (parts !== undefined && parts !== null) {
          if (typeof parts !== 'object' || typeof parts[Symbol.iterator] !== 'function') throw new TypeError("Failed to construct 'Blob': The provided value cannot be converted to a sequence.");
          for (const p of parts) {
            if (p instanceof Blob) chunks.push(blobBytes(p));
            else if (p instanceof ArrayBuffer || ArrayBuffer.isView(p) || isShared(p)) chunks.push(copyBytes(bufferSource(p, 'Blob')));
            else { let t = usv(p); if (native) t = t.replace(/\r\n|\r/g, '\n'); chunks.push(utf8(t)); }
          }
        }
        let size = 0; for (const c of chunks) size += c.length;
        const bytes = new Uint8Array(size); let at = 0; for (const c of chunks) { bytes.set(c, at); at += c.length; }
        blobs.set(this, { bytes, type: d.type === undefined ? '' : blobType(d.type) });
      }
      get size() { return brand(blobs, this, 'Blob.size').bytes.length; }
      get type() { return brand(blobs, this, 'Blob.type').type; }
      slice(start = undefined, end = undefined, contentType = undefined) {
        const b = brand(blobs, this, 'Blob.slice').bytes, n = b.length;
        const at = (v, dflt) => { if (v === undefined) return dflt; v = Math.trunc(Number(v)) || 0; return v < 0 ? Math.max(n + v, 0) : Math.min(v, n); };
        const from = at(start, 0), to = at(end, n);
        const r = Object.create(Blob.prototype);
        blobs.set(r, { bytes: b.slice(from, Math.max(from, to)), type: contentType === undefined ? '' : blobType(contentType) });
        return r;
      }
      text() { try { return Promise.resolve(new TextDecoder().decode(brand(blobs, this, 'Blob.text').bytes)); } catch (e) { return Promise.reject(e); } }
      arrayBuffer() { try { return Promise.resolve(brand(blobs, this, 'Blob.arrayBuffer').bytes.slice().buffer); } catch (e) { return Promise.reject(e); } }
      bytes() { try { return Promise.resolve(brand(blobs, this, 'Blob.bytes').bytes.slice()); } catch (e) { return Promise.reject(e); } }
    }
    setTag(Blob, 'Blob');
    return BlobC = Blob;
  };
  lazy('Blob', makeBlob);
  const makeFile = () => {
    if (FileC) return FileC;
    const Blob = makeBlob();
    const files = new WeakMap();
    class File extends Blob {
      constructor(bits, name, options = undefined) {
        if (arguments.length < 2) throw new TypeError("Failed to construct 'File': 2 arguments required");
        super(bits, options);
        const d = dict(options, "Failed to construct 'File'");
        files.set(this, { name: usv(name), lastModified: d.lastModified === undefined ? Date.now() : Number(d.lastModified) });
      }
      get name() { return brand(files, this, 'File.name').name; }
      get lastModified() { return brand(files, this, 'File.lastModified').lastModified; }
    }
    setTag(File, 'File');
    return FileC = File;
  };
  lazy('File', makeFile);
  const makeFormData = () => {
    if (FormDataC) return FormDataC;
    const Blob = makeBlob(), File = makeFile();
    const forms = new WeakMap();
    const E = (o, what) => brand(forms, o, 'FormData.' + what).entries;
    // "create an entry": a Blob that is not a File becomes a File named "blob"; a File gets
    // the given filename.
    const entry = (name, value, filename, args, what) => {
      name = usv(name);
      if (value instanceof Blob) {
        const isFile = value instanceof File;
        if (args < 3 && isFile) return [name, value];
        const fname = args >= 3 ? usv(filename) : 'blob';
        return [name, new File([value], fname, { type: value.type, ...(isFile ? { lastModified: value.lastModified } : {}) })];
      }
      if (args >= 3) throw new TypeError(`Failed to execute '${what}' on 'FormData': parameter 2 is not of type 'Blob'.`);
      return [name, usv(value)];
    };
    class FormData {
      constructor(form = undefined, submitter = undefined) {
        forms.set(this, { entries: [] });
        if (form === undefined) return;
        if (formEntryList === null) throw new TypeError("Failed to construct 'FormData': parameter 1 is not of type 'HTMLFormElement'.");
        // "construct the entry list": Lean's entries, then the formdata event at the form
        // with a FormData of them, which a listener may change
        forms.get(this).entries = formEntryList(form, submitter ?? null,
          entries => { const fd = new FormData(); forms.get(fd).entries = entries; return fd; }, fd => forms.get(fd).entries.slice());
      }
      append(name, value, filename = undefined) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'append' on 'FormData': 2 arguments required");
        E(this, 'append').push(entry(name, value, filename, arguments.length, 'append'));
      }
      set(name, value, filename = undefined) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'set' on 'FormData': 2 arguments required");
        const es = E(this, 'set'), e = entry(name, value, filename, arguments.length, 'set');
        const i = es.findIndex(x => x[0] === e[0]);
        if (i < 0) { es.push(e); return; }
        es[i] = e;
        for (let j = es.length - 1; j > i; j--) if (es[j][0] === e[0]) es.splice(j, 1);
      }
      delete(name) { name = usv(name); const es = E(this, 'delete'); for (let j = es.length - 1; j >= 0; j--) if (es[j][0] === name) es.splice(j, 1); }
      get(name) { name = usv(name); const e = E(this, 'get').find(x => x[0] === name); return e ? e[1] : null; }
      getAll(name) { name = usv(name); return E(this, 'getAll').filter(x => x[0] === name).map(x => x[1]); }
      has(name) { name = usv(name); return E(this, 'has').some(x => x[0] === name); }
      forEach(f, thisArg = undefined) {
        if (typeof f !== 'function') throw new TypeError("Failed to execute 'forEach' on 'FormData': parameter 1 is not a function");
        const es = E(this, 'forEach');
        for (let i = 0; i < es.length; i++) f.call(thisArg, es[i][1], es[i][0], this);
      }
      *entries() { const es = E(this, 'entries'); for (let i = 0; i < es.length; i++) yield [es[i][0], es[i][1]]; }
      *keys() { for (const [k] of this.entries()) yield k; }
      *values() { for (const [, v] of this.entries()) yield v; }
    }
    Object.defineProperty(FormData.prototype, Symbol.iterator, { value: FormData.prototype.entries, writable: true, configurable: true });
    setTag(FormData, 'FormData');
    return FormDataC = FormData;
  };
  lazy('FormData', makeFormData);
  // ---- FileReader (File API §6.2) ---------------------------------------------------------
  // A read is tasks of this realm: loadstart, progress, load and loadend at the reader, in that
  // order, with the result packaged when the read ends (§6.2.3). The text is Lean's decoding
  // (TextDecoder), the data URL Lean's base64 (btoa), the type's charset Lean's MIME parser.
  lazy('FileReader', () => {
    const PE = makeProgressEvent();
    const readers = new WeakMap();
    const R = (o, what) => brand(readers, o, 'FileReader.' + what);
    const fireAt = (reader, type, loaded, total) => {
      const e = new PE(type, { lengthComputable: total > 0, loaded, total });
      state(e).trusted = true;
      dispatch(reader, e);
    };
    const binary = bytes => { let s = ''; for (let i = 0; i < bytes.length; i += 8192) s += String.fromCharCode(...bytes.subarray(i, i + 8192)); return s; };
    const charsetOf = type => {
      const canon = type === '' ? -1 : apiCall(86, [type]);
      const m = typeof canon === 'string' ? /;charset=(?:"((?:[^"\\]|\\.)*)"|([^;]*))/.exec(canon) : null;
      return m ? (m[1] !== undefined ? m[1].replace(/\\(.)/g, '$1') : m[2]) : '';
    };
    const packaged = (kind, bytes, type, label) => {
      if (kind === 'arraybuffer') return bytes.slice().buffer;
      if (kind === 'binary') return binary(bytes);
      if (kind === 'dataurl') return 'data:' + (type === '' ? 'application/octet-stream' : type) + ';base64,' + btoa(binary(bytes));
      // Text: a byte order mark names the encoding (Encoding "decode"); else the label given,
      // else the charset of the blob's type, else UTF-8.
      if (bytes.length >= 3 && bytes[0] === 0xEF && bytes[1] === 0xBB && bytes[2] === 0xBF) return new TextDecoder('utf-8').decode(bytes);
      if (bytes.length >= 2 && bytes[0] === 0xFE && bytes[1] === 0xFF) return new TextDecoder('utf-16be').decode(bytes);
      if (bytes.length >= 2 && bytes[0] === 0xFF && bytes[1] === 0xFE) return new TextDecoder('utf-16le').decode(bytes);
      for (const l of [label, charsetOf(type)]) {
        if (l === undefined || l === null || l === '') continue;
        let decoder;
        try { decoder = new TextDecoder(l); } catch { continue; }
        return decoder.decode(bytes);
      }
      return new TextDecoder().decode(bytes);
    };
    const read = (reader, kind, blob, label, what) => {
      const s = R(reader, what), b = blobs.get(blob);
      if (!b) throw new TypeError(`Failed to execute '${what}' on 'FileReader': parameter 1 is not of type 'Blob'.`);
      if (s.state === 1) throw new DOMException(`Failed to execute '${what}' on 'FileReader': the reader is reading`, 'InvalidStateError');
      s.state = 1; s.result = null; s.error = null;
      const run = ++s.run, bytes = b.bytes, type = b.type, n = bytes.length;
      // Each event is a task of its own, so the microtasks of one event's listeners (a promise
      // that waits for it) run before the next event, as when a browser fires them from tasks.
      const task = f => setTimeout(() => { if (s.run === run) f(); }, 0);
      const finish = () => task(() => {
        if (s.state !== 1) return;
        s.state = 2;
        let event = 'load';
        try { s.result = packaged(kind, bytes, type, label); }
        catch (e) { s.result = null; s.error = new DOMException(String(e && e.message || e), 'NotReadableError'); event = 'error'; }
        fireAt(reader, event, n, n);
        task(() => { if (s.state !== 1) fireAt(reader, 'loadend', n, n); });
      });
      task(() => {
        if (s.state !== 1) return;
        fireAt(reader, 'loadstart', 0, n);
        if (n > 0) task(() => { if (s.state !== 1) return; fireAt(reader, 'progress', n, n); finish(); });
        else finish();
      });
    };
    const need = (have, what) => { if (have < 1) throw new TypeError(`Failed to execute '${what}' on 'FileReader': 1 argument required, but only 0 present.`); };
    class FileReader extends EventTarget {
      constructor() { super(); readers.set(this, { state: 0, result: null, error: null, run: 0 }); }
      get readyState() { return R(this, 'readyState').state; }
      get result() { return R(this, 'result').result; }
      get error() { return R(this, 'error').error; }
      readAsArrayBuffer(blob) { need(arguments.length, 'readAsArrayBuffer'); read(this, 'arraybuffer', blob, undefined, 'readAsArrayBuffer'); }
      readAsBinaryString(blob) { need(arguments.length, 'readAsBinaryString'); read(this, 'binary', blob, undefined, 'readAsBinaryString'); }
      readAsText(blob, encoding = undefined) { need(arguments.length, 'readAsText'); read(this, 'text', blob, encoding === undefined ? undefined : String(encoding), 'readAsText'); }
      readAsDataURL(blob) { need(arguments.length, 'readAsDataURL'); read(this, 'dataurl', blob, undefined, 'readAsDataURL'); }
      abort() {
        const s = R(this, 'abort');
        if (s.state !== 1) { s.result = null; return; }
        s.state = 2; s.result = null;
        const run = ++s.run;
        fireAt(this, 'abort', 0, 0);
        if (s.run === run && s.state !== 1) fireAt(this, 'loadend', 0, 0);
      }
    }
    const states = { EMPTY: 0, LOADING: 1, DONE: 2 };
    consts(FileReader, states); consts(FileReader.prototype, states);
    for (const name of ['loadstart', 'progress', 'load', 'abort', 'error', 'loadend'])
      Object.defineProperty(FileReader.prototype, 'on' + name, { get() { return handlerOf(this, name); },
        set(f) { setHandler(this, name, f); }, configurable: true, enumerable: true });
    setTag(FileReader, 'FileReader');
    return FileReader;
  });
  // A request body (XHR §4.5.1 and Fetch "extract a body"): [bytes, Content-Type or ''].
  // A FormData's multipart body and boundary are Lean's (op 78).
  const extractBody = (body, what) => {
    if (BlobC && body instanceof BlobC) return [blobBytes(body), blobs.get(body).type];
    if (FormDataC && body instanceof FormDataC) {
      const args = [];
      for (const [name, v] of forms_entries(body)) {
        if (typeof v === 'string') args.push(name, '0', '', '', utf8(v));
        else args.push(name, '1', v.name, v.type, blobBytes(v));
      }
      const r = apiCall(78, args, 0, true);
      if (!(r instanceof ArrayBuffer)) return apiError(r, what);
      const bytes = new Uint8Array(r);
      let i = 0; while (i + 1 < bytes.length && !(bytes[i] === 13 && bytes[i + 1] === 10)) i++;
      const boundary = String.fromCharCode(...bytes.subarray(2, i)).replace(/--$/, '');
      return [bytes, 'multipart/form-data; boundary=' + boundary];
    }
    if (typeof body === 'object' && (body instanceof ArrayBuffer || ArrayBuffer.isView(body) || isShared(body))) return [bufferSource(body, what), ''];
    if (typeof body === 'object' && URLSearchParamsC && body instanceof URLSearchParamsC) return [String(body), 'application/x-www-form-urlencoded;charset=UTF-8'];
    return [usv(body), 'text/plain;charset=UTF-8'];
  };
  const forms_entries = f => { const it = FormDataC.prototype.entries.call(f); return [...it]; };

  // ---- XMLHttpRequest (XHR Standard) -------------------------------------------------------
  // The object's state, what each method may do, the order of events and the text of a
  // response are Lean's (formal/lean4/L4Factoidal/Net/Xhr.lean, web_api ops 60 to 79; the
  // policy of what a page may reach is Net/PageFetch.lean). This class holds a handle,
  // converts WebIDL arguments, fires the events Lean lists, and arms the timeout. Off
  // (undefined) unless the embedder turned the network on: op 75 answers -2 then.
  const xhrErr = (r, what) => {
    switch (r) {
      case -31: throw new DOMException(what, 'InvalidStateError');
      case -32: throw new DOMException(what, 'SecurityError');
      case -24: throw new DOMException(what, 'SyntaxError');
      case -25: throw new DOMException(what, 'InvalidAccessError');
      case -23: throw new DOMException(what + ': sync requests are not supported in this build', 'NotSupportedError');
      case -33: throw new DOMException(what, 'NetworkError');
      case -40: throw { name: '__syncWait' };   // the run is undone and redone with the answer
      default: return apiError(r, what);
    }
  };
  let ProgressEventC;
  const makeProgressEvent = () => {
    if (ProgressEventC) return ProgressEventC;
    class ProgressEvent extends Event {
      constructor(type, init = undefined) { super(type, init); const d = initOf(init); const s = state(this);
        s.lengthComputable = !!d.lengthComputable; s.loaded = Number(d.loaded ?? 0); s.total = Number(d.total ?? 0); }
    }
    getters(ProgressEvent, ['lengthComputable', 'loaded', 'total']);
    return ProgressEventC = ProgressEvent;
  };
  lazy('ProgressEvent', makeProgressEvent);
  const makeXHR = () => {
    if (apiCall(75, []) !== '1') return undefined;
    const PE = makeProgressEvent();
    const key = {};
    const st = new WeakMap();
    const S = (o, what) => brand(st, o, 'XMLHttpRequest' + (what ? '.' + what : ''));
    const call = (op, args, what) => { const r = apiCall(op, args); return typeof r === 'number' ? xhrErr(r, what) : r; };
    class XMLHttpRequestEventTarget extends EventTarget {
      constructor(k) { if (k !== key) throw new TypeError('Illegal constructor'); super(); }
    }
    const upload = new WeakMap();
    class XMLHttpRequestUpload extends XMLHttpRequestEventTarget {
      constructor(k) { super(k); upload.set(this, { listened: false }); }
      addEventListener(type, cb, opts) { upload.get(this).listened = true; return super.addEventListener(type, cb, opts); }
    }
    const handlerAttr = (C, name) => Object.defineProperty(C.prototype, 'on' + name, { configurable: true, enumerable: true,
      get() { return handlerOf(this, name); },
      set(f) { if (this instanceof XMLHttpRequestUpload) upload.get(this).listened = true; setHandler(this, name, f); } });
    for (const name of ['loadstart', 'progress', 'abort', 'error', 'load', 'timeout', 'loadend']) handlerAttr(XMLHttpRequestEventTarget, name);
    const fireOne = (x, s, line) => {
      const [up, type, loaded, total, computable] = line.split('\u0000');
      const target = up === '1' ? s.upload : x;
      const ev = type === 'readystatechange' ? new Event(type)
        : new PE(type, { lengthComputable: computable === '1', loaded: Number(loaded), total: Number(total) });
      state(ev).trusted = true;
      dispatch(target, ev);
    };
    const drain = (x, s) => {
      for (;;) { const e = call(64, [s.h], 'XMLHttpRequest'); if (e === '') break; fireOne(x, s, e); }
      if (s.timer && call(67, [s.h, 0]) === '4') { n.clearTimer(s.timer); s.timer = 0; }
    };
    class XMLHttpRequest extends XMLHttpRequestEventTarget {
      constructor() {
        super(key);
        xhrState.set(this, st.set(this, { h: Number(call(60, [], 'XMLHttpRequest')), upload: new XMLHttpRequestUpload(key), timer: 0, ms: 0, cred: false, text: null, json: null, buf: null, doc: null }).get(this));
      }
      get upload() { return S(this).upload; }
      get readyState() { return Number(call(67, [S(this).h, 0])); }
      get status() { return Number(call(67, [S(this).h, 1])); }
      get statusText() { return call(67, [S(this).h, 2]); }
      get responseURL() { return call(67, [S(this).h, 3]); }
      get responseType() { return call(67, [S(this).h, 6]); }
      set responseType(v) { const s = S(this); call(71, [s.h, String(v)], "Failed to set 'responseType' on 'XMLHttpRequest'"); }
      get timeout() { return S(this).ms; }
      set timeout(v) { const s = S(this), ms = Number(v) >>> 0; call(72, [s.h, ms], "Failed to set 'timeout' on 'XMLHttpRequest'"); s.ms = ms; }
      get withCredentials() { return S(this).cred; }
      set withCredentials(v) { const s = S(this), b = !!v; call(73, [s.h, b ? 1 : 0], "Failed to set 'withCredentials' on 'XMLHttpRequest'"); s.cred = b; }
      get responseText() {
        const s = S(this), t = call(67, [s.h, 6]);
        if (t !== '' && t !== 'text') throw new DOMException("responseText is only for responseType '' and 'text'", 'InvalidStateError');
        if (s.text !== null) return s.text;
        const v = call(67, [s.h, 4]);
        if (call(67, [s.h, 0]) === '4') s.text = v;
        return v;
      }
      get responseXML() {
        const s = S(this), t = call(67, [s.h, 6]);
        if (t !== '' && t !== 'document') throw new DOMException('responseXML is only for responseType document', 'InvalidStateError');
        if (s.doc !== null) return s.doc.v;
        const kind = call(67, [s.h, 7]);
        let v = null;
        if (kind !== '' && typeof DOMParser === 'function') {
          try {
            const d = new DOMParser().parseFromString(call(67, [s.h, 4]), kind === 'html' ? 'text/html' : 'application/xml');
            v = kind === 'xml' && d.documentElement && d.documentElement.localName === 'parsererror' ? null : d;
          } catch { v = null; }
        }
        s.doc = { v };
        return v;
      }
      get response() {
        const s = S(this), t = call(67, [s.h, 6]);
        if (t === '' || t === 'text') return this.responseText;
        if (call(67, [s.h, 0]) !== '4') return null;
        if (t === 'json') { if (s.json === null) { try { s.json = { v: JSON.parse(call(67, [s.h, 4])) }; } catch { s.json = { v: null }; } } return s.json.v; }
        if (t === 'document') return this.responseXML;
        if (t === 'arraybuffer') { if (s.buf === null) { const b = apiCall(74, [s.h], 0, true); s.buf = b instanceof ArrayBuffer ? b : new ArrayBuffer(0); } return s.buf; }
        if (t === 'blob') {
          if (s.buf === null) { const b = apiCall(74, [s.h], 0, true); s.buf = new (makeBlob())([b instanceof ArrayBuffer ? b : new ArrayBuffer(0)], { type: call(67, [s.h, 8]) }); }
          return s.buf;
        }
        return null;
      }
      open(method, url, async = true, user = null, password = null) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'open' on 'XMLHttpRequest': 2 arguments required");
        const s = S(this), isAsync = arguments.length < 3 ? true : !!async;
        // a worker's API base URL is its script's URL (HTML §10.2.4)
        const base = scriptBase();
        call(61, [s.h, String(method), usv(url), base, isAsync ? 1 : 0], "Failed to execute 'open' on 'XMLHttpRequest'");
        s.text = s.json = s.buf = s.doc = null;
        if (s.timer) { n.clearTimer(s.timer); s.timer = 0; }
        drain(this, s);
      }
      setRequestHeader(name, value) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'setRequestHeader' on 'XMLHttpRequest': 2 arguments required");
        call(62, [S(this).h, String(name), String(value)], "Failed to execute 'setRequestHeader' on 'XMLHttpRequest'");
      }
      send(body = null) {
        const s = S(this), what = "Failed to execute 'send' on 'XMLHttpRequest'";
        let has = 0, ct = '', bytes = '';
        if (body !== null && body !== undefined) { has = 1; [bytes, ct] = extractBody(body, what); }
        const x = this, cb = register(() => drain(x, s));
        const up = upload.get(s.upload).listened;
        s.text = s.json = s.buf = s.doc = null;
        call(63, [s.h, cb, up ? 1 : 0, has, ct, bytes], what);
        drain(this, s);
        if (call(67, [s.h, 5]) === '1') chk(n.timer(register(() => { call(76, [s.h]); drain(x, s); }), 0, 0));
        if (s.ms > 0 && call(67, [s.h, 0]) !== '4') s.timer = chk(n.timer(register(() => { s.timer = 0; call(66, [s.h]); drain(x, s); }), s.ms, 0));
      }
      abort() { const s = S(this); call(65, [s.h]); s.text = s.json = s.buf = s.doc = null; drain(this, s); }
      getResponseHeader(name) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'getResponseHeader' on 'XMLHttpRequest': 1 argument required");
        const r = apiCall(68, [S(this).h, String(name)]);
        return typeof r === 'number' ? (r === -1 ? null : xhrErr(r, 'getResponseHeader')) : r;
      }
      getAllResponseHeaders() { return call(69, [S(this).h], 'getAllResponseHeaders'); }
      overrideMimeType(mime) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'overrideMimeType' on 'XMLHttpRequest': 1 argument required");
        call(70, [S(this).h, String(mime)], "Failed to execute 'overrideMimeType' on 'XMLHttpRequest'");
      }
    }
    handlerAttr(XMLHttpRequest, 'readystatechange');
    const readyStates = { UNSENT: 0, OPENED: 1, HEADERS_RECEIVED: 2, LOADING: 3, DONE: 4 };
    consts(XMLHttpRequest, readyStates); consts(XMLHttpRequest.prototype, readyStates);
    // responseXML is [Exposed=Window] (XHR §4.6.5)
    if (inWorker) delete XMLHttpRequest.prototype.responseXML;
    setTag(XMLHttpRequest, 'XMLHttpRequest'); setTag(XMLHttpRequestEventTarget, 'XMLHttpRequestEventTarget'); setTag(XMLHttpRequestUpload, 'XMLHttpRequestUpload');
    define(globalThis, 'XMLHttpRequestEventTarget', XMLHttpRequestEventTarget);
    define(globalThis, 'XMLHttpRequestUpload', XMLHttpRequestUpload);
    return XMLHttpRequest;
  };
  const xhrState = new WeakMap();
  lazy('XMLHttpRequest', makeXHR);

  // ---- fetch (Fetch Standard): Headers, Request, Response, and fetch over the XMLHttpRequest core
  // Lean decides every request (Net/PageFetch.lean, the object is Net/Xhr.lean's); this is the
  // promise surface. `no-cors` opaque responses and stream bodies are not here yet.
  // A `Headers` object's rules (what it keeps, by its guard), a `Request`'s method and the MIME
  // type of a body are Lean's (Net/FetchRules.lean, WHATWG/MimeType.lean, web_api ops 86 to 89).
  // These classes hold the objects, convert WebIDL arguments and ask there.
  const headerState = new WeakMap();   // Headers -> { list: [[lowercase name, value]], guard }
  const hState = (o, what) => brand(headerState, o, 'Headers.' + what);
  const hNeed = (n, have, what) => { if (have < n) throw new TypeError(`Failed to execute '${what}' on 'Headers': ${n} argument${n > 1 ? 's' : ''} required, but only ${have} present.`); };
  // "validate" (after "normalize") of Lean: the value to keep, or undefined for a field dropped.
  const hValidate = (s, name, value, what) => {
    const r = apiCall(87, [s.guard, name, value]);
    if (typeof r !== 'string') throw new TypeError(`${what}: not a header name or value, or the headers are immutable`);
    return r === '0' ? undefined : r.slice(1);
  };
  const hAppend = (s, name, value, what) => {
    const n = String(name), v = hValidate(s, n, String(value), what);
    if (v === undefined) return;
    const lower = n.toLowerCase();
    if (s.guard === 'request-no-cors') {
      // §5.1 append step 4: the value combined with the one held must stay safelisted.
      const held = hGet(s, lower);
      if (held !== null && apiCall(87, ['request-no-cors-combined', n, held + ', ' + v]) === '0') return;
    }
    s.list.push([lower, v]);
  };
  const hName = (name, what) => {
    const n = String(name);
    if (apiCall(88, [n]) !== '') throw new TypeError(`${what}: not a header name`);
    return n.toLowerCase();
  };
  const hFill = (s, init, what) => {
    if (init === undefined) return;
    if (init === null || (typeof init !== 'object' && typeof init !== 'function')) throw new TypeError(`${what}: the headers are not a sequence or a record`);
    const it = init[Symbol.iterator];
    if (it !== undefined && it !== null) {
      if (typeof it !== 'function') throw new TypeError(`${what}: the headers are not iterable`);
      for (const pair of init) {
        if (pair === null || (typeof pair !== 'object' && typeof pair !== 'function') || typeof pair[Symbol.iterator] !== 'function') throw new TypeError(`${what}: a header is not a sequence`);
        const p = [...pair];
        if (p.length !== 2) throw new TypeError(`${what}: a header is a name and a value`);
        hAppend(s, p[0], p[1], what);
      }
      return;
    }
    for (const k of Reflect.ownKeys(init)) {
      const d = Reflect.getOwnPropertyDescriptor(init, k);
      if (d === undefined || !d.enumerable) continue;
      if (typeof k === 'symbol' || /[^\x00-\xff]/.test(k)) throw new TypeError(`${what}: a header name is not a ByteString`);
      hAppend(s, k, init[k], what);
    }
  };
  // "Sort and combine" (Fetch §2.2.2): names in order, the values of a name joined; each
  // Set-Cookie on its own.
  const hPairs = s => {
    const names = [...new Set(s.list.map(e => e[0]))].sort(), out = [];
    for (const n of names) {
      if (n === 'set-cookie') { for (const e of s.list) if (e[0] === n) out.push([n, e[1]]); }
      else out.push([n, s.list.filter(e => e[0] === n).map(e => e[1]).join(', ')]);
    }
    return out;
  };
  const hGet = (s, n) => { const vs = s.list.filter(e => e[0] === n).map(e => e[1]); return vs.length ? vs.join(', ') : null; };
  let HeadersC, RequestC, ResponseC;
  const makeHeaders = () => {
    if (HeadersC) return HeadersC;
    const iterState = new WeakMap();
    const iterProto = Object.create(Object.getPrototypeOf(Object.getPrototypeOf([][Symbol.iterator]())));
    Object.defineProperty(iterProto, 'next', { writable: true, enumerable: true, configurable: true, value: function next() {
      const st = iterState.get(this);
      if (!st) throw new TypeError('Illegal invocation: Headers Iterator.next');
      const pairs = hPairs(st.s);
      if (st.i >= pairs.length) return { value: undefined, done: true };
      const p = pairs[st.i++];
      return { value: st.kind === 0 ? p[0] : st.kind === 1 ? p[1] : [p[0], p[1]], done: false };
    } });
    Object.defineProperty(iterProto, Symbol.toStringTag, { value: 'Headers Iterator', configurable: true });
    const iter = (o, kind, what) => { const it = Object.create(iterProto); iterState.set(it, { s: hState(o, what), kind, i: 0 }); return it; };
    class Headers {
      constructor(init = undefined) {
        const s = { list: [], guard: 'none' };
        headerState.set(this, s);
        hFill(s, init, "Failed to construct 'Headers'");
      }
      append(name, value) { hNeed(2, arguments.length, 'append'); hAppend(hState(this, 'append'), name, value, "Failed to execute 'append' on 'Headers'"); }
      delete(name) {
        hNeed(1, arguments.length, 'delete');
        const s = hState(this, 'delete'), n = String(name);
        const r = apiCall(87, [s.guard === 'request-no-cors' ? 'request-no-cors-name' : s.guard, n, '']);
        if (typeof r !== 'string') throw new TypeError("Failed to execute 'delete' on 'Headers': not a header name, or the headers are immutable");
        if (r === '0') return;
        const lower = n.toLowerCase();
        s.list = s.list.filter(e => e[0] !== lower);
      }
      get(name) { hNeed(1, arguments.length, 'get'); const s = hState(this, 'get'); return hGet(s, hName(name, "Failed to execute 'get' on 'Headers'")); }
      getSetCookie() { return hState(this, 'getSetCookie').list.filter(e => e[0] === 'set-cookie').map(e => e[1]); }
      has(name) { hNeed(1, arguments.length, 'has'); const s = hState(this, 'has'), n = hName(name, "Failed to execute 'has' on 'Headers'"); return s.list.some(e => e[0] === n); }
      set(name, value) {
        hNeed(2, arguments.length, 'set');
        const s = hState(this, 'set'), n = String(name), v = hValidate(s, n, String(value), "Failed to execute 'set' on 'Headers'");
        if (v === undefined) return;
        const lower = n.toLowerCase(), i = s.list.findIndex(e => e[0] === lower);
        if (i < 0) { s.list.push([lower, v]); return; }
        s.list[i] = [lower, v];
        s.list = s.list.filter((e, j) => j <= i || e[0] !== lower);
      }
      forEach(callback, thisArg = undefined) {
        hNeed(1, arguments.length, 'forEach');
        const s = hState(this, 'forEach');
        if (typeof callback !== 'function') throw new TypeError("Failed to execute 'forEach' on 'Headers': parameter 1 is not a function");
        for (let i = 0; ; i++) { const pairs = hPairs(s); if (i >= pairs.length) break; callback.call(thisArg, pairs[i][1], pairs[i][0], this); }
      }
      keys() { return iter(this, 0, 'keys'); }
      values() { return iter(this, 1, 'values'); }
      entries() { return iter(this, 2, 'entries'); }
    }
    for (const k of ['append', 'delete', 'get', 'getSetCookie', 'has', 'set', 'forEach', 'keys', 'values', 'entries'])
      Object.defineProperty(Headers.prototype, k, { value: Headers.prototype[k], writable: true, enumerable: true, configurable: true });
    Object.defineProperty(Headers.prototype, Symbol.iterator, { value: Headers.prototype.entries, writable: true, configurable: true });
    setTag(Headers, 'Headers');
    return HeadersC = Headers;
  };
  // A Headers object over a list, with a guard (a Request's, a Response's).
  const headersOf = (list, guard) => { const h = Object.create(makeHeaders().prototype); headerState.set(h, { list: list.map(e => [e[0], e[1]]), guard }); return h; };
  lazy('Headers', () => (apiCall(88, ['a']) !== '' ? undefined : makeHeaders()));

  // ---- Body (Fetch §5.3): the bytes of a Request or a Response -------------------------------
  const bodies = new WeakMap();   // Request or Response -> { bytes (null: no body), used, stream, headers }
  const bState = (o, what) => brand(bodies, o, what);
  const bodyTake = (o, what) => {
    let b;
    try { b = bState(o, what); } catch (e) { return Promise.reject(e); }
    if (b.used || (b.stream && b.stream.locked)) return Promise.reject(new TypeError(`Failed to execute '${what}': the body was already read`));
    if (b.signal && b.signal.aborted) return Promise.reject(b.signal.reason);
    if (b.bytes !== null) b.used = true;
    return Promise.resolve(b.bytes === null ? new Uint8Array(0) : b.bytes);
  };
  // The body's MIME type, serialized ('' for none): Fetch "extract a MIME type", Lean's.
  const bodyMime = b => { const ct = hGet(headerState.get(b.headers), 'content-type'); if (ct === null) return ''; const r = apiCall(86, [ct]); return typeof r === 'string' ? r : ''; };
  const bodyInit = (body, what) => {
    if (typeof body === 'object' && body !== null && typeof body.getReader === 'function') throw new TypeError(`${what}: a stream body is not supported in this build`);
    const [raw, ct] = extractBody(body, what);
    return [typeof raw === 'string' ? utf8(raw) : copyBytes(raw), ct];
  };
  const bodyMixin = C => {
    const name = C.name;
    const methods = {
      arrayBuffer() { return bodyTake(this, name + '.arrayBuffer').then(b => b.slice().buffer); },
      blob() {
        return bodyTake(this, name + '.blob').then(b => {
          const blob = new (makeBlob())([b]);
          blobs.get(blob).type = bodyMime(bodies.get(this));
          return blob;
        });
      },
      bytes() { return bodyTake(this, name + '.bytes').then(b => b.slice()); },
      formData() {
        return bodyTake(this, name + '.formData').then(b => {
          const type = bodyMime(bodies.get(this));
          if (!/^application\/x-www-form-urlencoded(;|$)/.test(type)) throw new TypeError(`Failed to execute 'formData' on '${name}': only application/x-www-form-urlencoded bodies are read in this build`);
          const form = new (makeFormData())();
          for (const [k, v] of new URLSearchParams(new TextDecoder().decode(b))) form.append(k, v);
          return form;
        });
      },
      json() { return bodyTake(this, name + '.json').then(b => JSON.parse(new TextDecoder().decode(b))); },
      text() { return bodyTake(this, name + '.text').then(b => new TextDecoder().decode(b)); },
    };
    for (const k in methods) Object.defineProperty(C.prototype, k, { value: methods[k], writable: true, enumerable: true, configurable: true });
    Object.defineProperty(C.prototype, 'bodyUsed', { enumerable: true, configurable: true, get() { return bState(this, name + '.bodyUsed').used; } });
    Object.defineProperty(C.prototype, 'body', { enumerable: true, configurable: true, get() {
      const b = bState(this, name + '.body');
      if (b.bytes === null) return null;
      if (b.stream === undefined) {
        const RS = globalThis.ReadableStream;
        b.stream = null;
        if (typeof RS === 'function') {
          try { b.stream = new RS({ pull(c) { b.used = true; c.enqueue(b.bytes.slice()); c.close(); } }, { highWaterMark: 0 }); } catch { b.stream = null; }
        }
      }
      return b.stream;
    } });
  };
  const urlFields = (url, base) => { const r = base === undefined ? apiCall(10, [url], 0, false) : apiCall(10, [url, base], 1, false); return typeof r === 'string' ? r.split('\0') : null; };
  const pageOrigin = () => { const p = urlFields(scriptBase()); return p === null ? 'null' : p[1]; };
  // A signal that aborts when `source` does (DOM §3.1 "create a dependent abort signal").
  const followSignal = source => {
    const s = new AbortSignal(abortKey);
    if (source) {
      if (source.aborted) signalAbort(s, source.reason);
      else source.addEventListener('abort', () => signalAbort(s, source.reason));
    }
    return s;
  };

  // ---- document.cookie (HTML §3.1.5; RFC 6265bis for a "non-HTTP" API) -----------------------
  // The jar, what a script may set and what it reads are Lean's (Net/Cookies.lean, web_api
  // ops 96 and 97): cookies are in memory and each is its host's; none is sent on the network.
  // The host is the engine's; this passes the document's path and the time.
  const cookieClock = Date.now;
  const cookieArgs = doc => {
    const p = urlFields(doc === document ? href : docURL(nodeId(doc)));
    return [p === null ? '/' : p[8], Math.floor(cookieClock() / 1000)];
  };
  Object.defineProperty(Document.prototype, 'cookie', { configurable: true, enumerable: true,
    get() { const r = apiCall(96, cookieArgs(this)); return typeof r === 'string' ? r : ''; },
    set(v) { apiCall(97, [...cookieArgs(this), String(v)]); } });

  // ---- Request (Fetch §5.4) ------------------------------------------------------------------
  const requests = new WeakMap();
  const makeRequest = () => {
    if (RequestC) return RequestC;
    const what = "Failed to construct 'Request'";
    const R = (o, attr) => brand(requests, o, 'Request.' + attr);
    const enumOf = (v, allowed, member) => {
      if (v === undefined) return undefined;
      const s = String(v);
      if (!allowed.includes(s)) throw new TypeError(`${what}: '${s}' is not a value of '${member}'`);
      return s;
    };
    const policies = ['', 'no-referrer', 'no-referrer-when-downgrade', 'same-origin', 'origin', 'strict-origin', 'origin-when-cross-origin', 'strict-origin-when-cross-origin', 'unsafe-url'];
    class Request {
      constructor(input, init = undefined) {
        if (arguments.length < 1) throw new TypeError(`${what}: 1 argument required, but only 0 present.`);
        const d = dict(init, what);
        // The dictionary's members, converted in their order (WebIDL §3.2.17).
        const body = d.body;
        const cache = enumOf(d.cache, ['default', 'no-store', 'reload', 'no-cache', 'force-cache', 'only-if-cached'], 'cache');
        const credentials = enumOf(d.credentials, ['omit', 'same-origin', 'include'], 'credentials');
        const duplex = enumOf(d.duplex, ['half'], 'duplex');
        const headers = d.headers;
        const integrity = d.integrity === undefined ? undefined : String(d.integrity);
        const keepalive = d.keepalive === undefined ? undefined : !!d.keepalive;
        const method = d.method === undefined ? undefined : String(d.method);
        const mode = enumOf(d.mode, ['same-origin', 'no-cors', 'cors', 'navigate'], 'mode');
        const priority = enumOf(d.priority, ['high', 'low', 'auto'], 'priority');
        const redirect = enumOf(d.redirect, ['follow', 'error', 'manual'], 'redirect');
        const referrer = d.referrer === undefined ? undefined : usv(d.referrer);
        const referrerPolicy = enumOf(d.referrerPolicy, policies, 'referrerPolicy');
        const signal = d.signal;
        if (signal !== undefined && signal !== null && !(signal instanceof AbortSignal)) throw new TypeError(`${what}: member signal is not of type 'AbortSignal'`);
        const win = d.window;
        const given = [body, cache, credentials, duplex, headers, integrity, keepalive, method, mode, priority, redirect, referrer, referrerPolicy, signal, win].some(v => v !== undefined);
        let st, source = null, inSignal = null;
        if (requests.has(input)) {
          source = input;
          st = { ...requests.get(input) };
          inSignal = st.signal;
        } else {
          const p = urlFields(usv(input), scriptBase());
          if (p === null) throw new TypeError(`${what}: Invalid URL`);
          if (p[3] !== '' || p[4] !== '') throw new TypeError(`${what}: the URL has credentials`);
          st = { url: p[0], method: 'GET', mode: 'cors', credentials: 'same-origin', cache: 'default', redirect: 'follow', referrer: 'about:client',
            referrerPolicy: '', integrity: '', keepalive: false, duplex: 'half', reload: false, history: false };
        }
        if (win !== undefined && win !== null) throw new TypeError(`${what}: member window must be null`);
        if (given) {
          if (st.mode === 'navigate') st.mode = 'same-origin';
          st.reload = false; st.history = false; st.referrer = 'about:client'; st.referrerPolicy = '';
        }
        if (referrer !== undefined) {
          if (referrer === '') st.referrer = '';
          else {
            const p = urlFields(referrer, scriptBase());
            if (p === null) throw new TypeError(`${what}: the referrer is not a URL`);
            st.referrer = p[0] === 'about:client' || p[1] !== pageOrigin() ? 'about:client' : p[0];
          }
        }
        if (referrerPolicy !== undefined) st.referrerPolicy = referrerPolicy;
        if (mode === 'navigate') throw new TypeError(`${what}: the mode 'navigate' is not allowed`);
        if (mode !== undefined) st.mode = mode;
        if (credentials !== undefined) st.credentials = credentials;
        if (cache !== undefined) st.cache = cache;
        if (st.cache === 'only-if-cached' && st.mode !== 'same-origin') throw new TypeError(`${what}: 'only-if-cached' needs the mode 'same-origin'`);
        if (redirect !== undefined) st.redirect = redirect;
        if (integrity !== undefined) st.integrity = integrity;
        if (keepalive !== undefined) st.keepalive = keepalive;
        if (method !== undefined) {
          const m = apiCall(89, [method]);
          if (typeof m !== 'string') throw new TypeError(`${what}: '${method}' is not a valid HTTP method`);
          st.method = m;
        }
        st.signal = followSignal(signal !== undefined ? signal : inSignal);
        if (st.mode === 'no-cors' && !['GET', 'HEAD', 'POST'].includes(st.method)) throw new TypeError(`${what}: '${st.method}' is not allowed in the mode 'no-cors'`);
        const hs = { list: [], guard: st.mode === 'no-cors' ? 'request-no-cors' : 'request' };
        if (given && headers !== undefined) hFill(hs, headers, what);
        else if (source) for (const e of headerState.get(requests.get(source).headers).list) hAppend(hs, e[0], e[1], what);
        st.headers = Object.create(makeHeaders().prototype);
        headerState.set(st.headers, hs);
        const inBody = source ? bodies.get(source) : null;
        const hasInit = body !== undefined && body !== null;
        if ((hasInit || (inBody && inBody.bytes !== null)) && (st.method === 'GET' || st.method === 'HEAD')) throw new TypeError(`${what}: a request with the method ${st.method} can not have a body`);
        let bytes = null;
        if (hasInit) {
          const [b, ct] = bodyInit(body, what);
          bytes = b;
          if (ct !== '' && hGet(hs, 'content-type') === null) hAppend(hs, 'Content-Type', ct, what);
        } else if (inBody && inBody.bytes !== null) {
          if (inBody.used || (inBody.stream && inBody.stream.locked)) throw new TypeError(`${what}: the body of the request was already read`);
          bytes = inBody.bytes;
          inBody.used = true;
        }
        requests.set(this, st);
        bodies.set(this, { bytes, used: false, stream: undefined, headers: st.headers });
      }
      get method() { return R(this, 'method').method; }
      get url() { return R(this, 'url').url; }
      get headers() { return R(this, 'headers').headers; }
      get destination() { R(this, 'destination'); return ''; }
      get referrer() { return R(this, 'referrer').referrer; }
      get referrerPolicy() { return R(this, 'referrerPolicy').referrerPolicy; }
      get mode() { return R(this, 'mode').mode; }
      get credentials() { return R(this, 'credentials').credentials; }
      get cache() { return R(this, 'cache').cache; }
      get redirect() { return R(this, 'redirect').redirect; }
      get integrity() { return R(this, 'integrity').integrity; }
      get keepalive() { return R(this, 'keepalive').keepalive; }
      get isReloadNavigation() { return R(this, 'isReloadNavigation').reload; }
      get isHistoryNavigation() { return R(this, 'isHistoryNavigation').history; }
      get signal() { return R(this, 'signal').signal; }
      get duplex() { return R(this, 'duplex').duplex; }
      clone() {
        const st = R(this, 'clone'), b = bodies.get(this);
        if (b.used || (b.stream && b.stream.locked)) throw new TypeError("Failed to execute 'clone' on 'Request': the body was already read");
        const r = Object.create(Request.prototype), hs = headerState.get(st.headers);
        const headers = headersOf(hs.list, hs.guard);
        requests.set(r, { ...st, headers, signal: followSignal(st.signal) });
        bodies.set(r, { bytes: b.bytes, used: false, stream: undefined, headers });
        return r;
      }
    }
    for (const k of ['method', 'url', 'headers', 'destination', 'referrer', 'referrerPolicy', 'mode', 'credentials', 'cache', 'redirect', 'integrity',
      'keepalive', 'isReloadNavigation', 'isHistoryNavigation', 'signal', 'duplex', 'clone'])
      Object.defineProperty(Request.prototype, k, { ...Object.getOwnPropertyDescriptor(Request.prototype, k), enumerable: true });
    bodyMixin(Request);
    setTag(Request, 'Request');
    return RequestC = Request;
  };
  lazy('Request', () => (apiCall(88, ['a']) !== '' ? undefined : makeRequest()));

  // ---- Response (Fetch §5.5) -----------------------------------------------------------------
  const responses = new WeakMap();
  // A response object from its parts: `guard` is its headers' guard.
  const responseOf = (parts, list, guard, bytes, signal) => {
    const r = Object.create(makeResponse().prototype), headers = headersOf(list, guard);
    responses.set(r, { ...parts, headers });
    // signal: the fetch's (Fetch §5.6 "fetch" step 11: aborting it errors the response's body)
    bodies.set(r, { bytes, used: false, stream: undefined, headers, signal });
    return r;
  };
  const makeResponse = () => {
    if (ResponseC) return ResponseC;
    const what = "Failed to construct 'Response'";
    const R = (o, attr) => brand(responses, o, 'Response.' + attr);
    // "Initialize a response" (§5.5): the status, the reason phrase, the fields, the body.
    const init = (r, d, body, what) => {
      const status = d.status === undefined ? 200 : (Math.trunc(Number(d.status)) || 0) & 0xFFFF;
      if (status < 200 || status > 599) throw new RangeError(`${what}: the status ${status} is outside 200 to 599`);
      const statusText = d.statusText === undefined ? '' : String(d.statusText);
      if (!/^[\t \x21-\x7e\x80-\xff]*$/.test(statusText)) throw new TypeError(`${what}: the status text is not a reason phrase`);
      const hs = { list: [], guard: 'response' };
      if (d.headers !== undefined) hFill(hs, d.headers, what);
      let bytes = null;
      if (body !== undefined && body !== null) {
        if ([101, 103, 204, 205, 304].includes(status)) throw new TypeError(`${what}: a response with the status ${status} can not have a body`);
        const [b, ct] = body;
        bytes = b;
        if (ct !== '' && hGet(hs, 'content-type') === null) hAppend(hs, 'Content-Type', ct, what);
      }
      const headers = Object.create(makeHeaders().prototype);
      headerState.set(headers, hs);
      responses.set(r, { status, statusText, headers, url: '', type: 'default', redirected: false });
      bodies.set(r, { bytes, used: false, stream: undefined, headers });
    };
    class Response {
      constructor(body = null, init_ = undefined) {
        const d = dict(init_, what);
        init(this, d, body === undefined || body === null ? null : bodyInit(body, what), what);
      }
      static error() { return responseOf({ status: 0, statusText: '', url: '', type: 'error', redirected: false }, [], 'immutable', null); }
      static redirect(url, status = 302) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'redirect' on 'Response': 1 argument required, but only 0 present.");
        const p = urlFields(usv(url), scriptBase());
        if (p === null) throw new TypeError("Failed to execute 'redirect' on 'Response': Invalid URL");
        const code = (Math.trunc(Number(status)) || 0) & 0xFFFF;
        if (![301, 302, 303, 307, 308].includes(code)) throw new RangeError("Failed to execute 'redirect' on 'Response': the status is not a redirect status");
        return responseOf({ status: code, statusText: '', url: '', type: 'default', redirected: false }, [['location', p[0]]], 'immutable', null);
      }
      static json(data, init_ = undefined) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'json' on 'Response': 1 argument required, but only 0 present.");
        const text = JSON.stringify(data);
        if (text === undefined) throw new TypeError("Failed to execute 'json' on 'Response': the value is not serializable");
        const r = Object.create(Response.prototype);
        init(r, dict(init_, "Failed to execute 'json' on 'Response'"), [utf8(text), 'application/json'], "Failed to execute 'json' on 'Response'");
        return r;
      }
      get type() { return R(this, 'type').type; }
      get url() { return R(this, 'url').url; }
      get redirected() { return R(this, 'redirected').redirected; }
      get status() { return R(this, 'status').status; }
      get ok() { const s = R(this, 'ok').status; return s >= 200 && s < 300; }
      get statusText() { return R(this, 'statusText').statusText; }
      get headers() { return R(this, 'headers').headers; }
      clone() {
        const st = R(this, 'clone'), b = bodies.get(this);
        if (b.used || (b.stream && b.stream.locked)) throw new TypeError("Failed to execute 'clone' on 'Response': the body was already read");
        const hs = headerState.get(st.headers);
        return responseOf({ status: st.status, statusText: st.statusText, url: st.url, type: st.type, redirected: st.redirected }, hs.list, hs.guard, b.bytes, b.signal);
      }
    }
    for (const k of ['type', 'url', 'redirected', 'status', 'ok', 'statusText', 'headers', 'clone'])
      Object.defineProperty(Response.prototype, k, { ...Object.getOwnPropertyDescriptor(Response.prototype, k), enumerable: true });
    for (const k of ['error', 'redirect', 'json'])
      Object.defineProperty(Response, k, { ...Object.getOwnPropertyDescriptor(Response, k), enumerable: true });
    bodyMixin(Response);
    setTag(Response, 'Response');
    return ResponseC = Response;
  };
  lazy('Response', () => (apiCall(88, ['a']) !== '' ? undefined : makeResponse()));
  lazy('fetch', () => {
    if (apiCall(75, []) !== '1') return undefined;
    return function fetch(input, init = undefined) {
      return new Promise((resolve, reject) => {
        const request = new (makeRequest())(input, init), st = requests.get(request), signal = st.signal;
        if (signal.aborted) { reject(signal.reason); return; }
        const x = new globalThis.XMLHttpRequest(), s = st_xhr(x);
        let settled = false;
        const fail = e => { if (!settled) { settled = true; reject(e); } };
        signal.addEventListener('abort', () => { if (settled) return; fail(signal.reason); try { x.abort(); } catch { /* done */ } });
        try { x.open(st.method, st.url, true); } catch (e) { fail(new TypeError(String(e && e.message || e))); return; }
        apiCall(73, [s.h, st.credentials === 'include' ? 1 : 0]);
        if (st.mode === 'same-origin') apiCall(77, [s.h, 1]);
        // redirect mode "error": Lean refuses the redirect (web_api op 79); "manual" is followed
        if (st.redirect === 'error') apiCall(79, [s.h, 1]);
        x.responseType = 'arraybuffer';
        for (const e of headerState.get(st.headers).list) x.setRequestHeader(e[0], e[1]);
        x.onload = () => {
          if (settled) return;
          settled = true;
          const raw = x.response, list = [];
          for (const line of x.getAllResponseHeaders().split('\r\n')) { const i = line.indexOf(': '); if (i > 0) list.push([line.slice(0, i).toLowerCase(), line.slice(i + 2)]); }
          const url = x.responseURL, p = urlFields(url);
          resolve(responseOf({ status: x.status, statusText: x.statusText, url, type: p !== null && p[1] !== pageOrigin() && p[2] !== 'data:' && p[2] !== 'blob:' ? 'cors' : 'basic',
            redirected: url !== '' && url !== st.url.split('#')[0] }, list, 'immutable', raw === null ? new Uint8Array(0) : new Uint8Array(raw), signal));
        };
        x.onerror = () => fail(new TypeError('Failed to fetch'));
        x.onabort = () => fail(new DOMException('The request was aborted.', 'AbortError'));
        x.ontimeout = () => fail(new TypeError('Failed to fetch'));
        const b = bodies.get(request);
        if (b.bytes !== null) b.used = true;
        x.send(b.bytes);
      });
    };
  });
  const st_xhr = x => xhrState.get(x);

  // ---- Origin (HTML §7.5 "Origin.from", the Origin interface) -----------------------------
  // An object for an origin: a tuple origin by its serialization, or an opaque origin that is
  // only itself. The origin of a URL is Lean's (the URL parser, web_api op 10); the page's is
  // the one of its URL. isSameSite needs registrable domains: there is no public suffix list
  // in this build, so it answers only what does not need one and throws for two different hosts.
  lazy('Origin', () => {
    const origins = new WeakMap();   // Origin -> { tuple: serialization } | { } (opaque: its identity)
    const what = "Failed to execute 'from' on 'Origin'";
    const internal = (o, name) => { const v = origins.get(o); if (!v) throw new TypeError(`Failed to execute '${name}' on 'Origin': Illegal invocation`); return v; };
    const made = v => { const o = Object.create(Origin.prototype); origins.set(o, v); return o; };
    const ofUrl = text => { const p = urlFields(String(text)); if (p === null) throw new TypeError(`${what}: not a URL`); return p[1] === 'null' ? {} : { tuple: p[1] }; };
    class Origin {
      constructor() { origins.set(this, {}); }
      static from(value) {
        if (typeof value === 'string') return made(ofUrl(value));
        if (value === null || (typeof value !== 'object' && typeof value !== 'function')) throw new TypeError(`${what}: the value has no origin`);
        if (origins.has(value)) return made(origins.get(value));
        // this global: the page's or worker's own origin
        if (value === globalThis) return made(ofUrl(href));
        // a same-origin frame's window shares this realm and its origin; a window of another origin has none to give
        if (frameOfWindow.has(value)) return made(ofUrl(href));
        if (typeof globalThis.URL === 'function' && value instanceof globalThis.URL) return made(ofUrl(value.href));
        if (ids.has(value) && value !== window) {
          const id = ids.get(value);
          if (info(id, 0) === 1 && (str(id, 0) === 'a' || str(id, 0) === 'area')) {
            // HTML a and area, and SVG a: the origin of the URL its href names
            const html = info(id, 8) === 1;
            const raw = html ? n.attr(id, 'href') : str(id, 2) === 'http://www.w3.org/2000/svg' && str(id, 0) === 'a' ? (value.getAttribute('href') ?? value.getAttributeNS('http://www.w3.org/1999/xlink', 'href')) : null;
            if (typeof raw === 'string') { const u = resolveURL(raw, value.baseURI || href); if (u !== null) return made(ofUrl(u)); }
          }
          throw new TypeError(`${what}: the element has no URL`);
        }
        // a message the user agent delivered: its sender's origin
        if (value instanceof MessageEvent && state(value).trusted && typeof value.origin === 'string' && value.origin !== '') return made(value.origin === 'null' ? {} : ofUrl(value.origin));
        throw new TypeError(`${what}: the value has no origin`);
      }
      get opaque() { return internal(this, 'opaque').tuple === undefined; }
      isSameOrigin(other) {
        const a = internal(this, 'isSameOrigin'), b = origins.get(other);
        if (!b) throw new TypeError("Failed to execute 'isSameOrigin' on 'Origin': parameter 1 is not of type 'Origin'");
        return a === b || (a.tuple !== undefined && a.tuple === b.tuple);
      }
      isSameSite(other) {
        const a = internal(this, 'isSameSite'), b = origins.get(other);
        if (!b) throw new TypeError("Failed to execute 'isSameSite' on 'Origin': parameter 1 is not of type 'Origin'");
        if (a === b) return true;
        if (a.tuple === undefined || b.tuple === undefined) return false;
        const pa = urlFields(a.tuple), pb = urlFields(b.tuple);
        if (pa === null || pb === null || pa[2] !== pb[2]) return false;
        if (pa[6] === pb[6]) return true;
        throw new DOMException("Failed to execute 'isSameSite' on 'Origin': two hosts need a public suffix list, which this build does not have", 'NotSupportedError');
      }
    }
    for (const k of ['opaque', 'isSameOrigin', 'isSameSite'])
      Object.defineProperty(Origin.prototype, k, { ...Object.getOwnPropertyDescriptor(Origin.prototype, k), enumerable: true });
    Object.defineProperty(Origin, 'from', { ...Object.getOwnPropertyDescriptor(Origin, 'from'), enumerable: true });
    setTag(Origin, 'Origin');
    return Origin;
  });

  // ==== SVG DOM (SVG 2 §4 "Basic data types and interfaces" and the element interfaces) ======
  // One table (`svgSpec`) names each element interface, its parent, its elements and the
  // attributes it reflects with their kinds; one implementation serves each kind of animated
  // value. Whether an attribute's text is a length, a number, a list or a transform list, and
  // its parts, is Lean's (DOM/SvgValues.lean, web_api ops 92 to 95): this is the WebIDL surface.
  // Built on first use (an SVG element reached by a script, or an SVG interface named): a page
  // with no SVG pays nothing.
  const SVG_NS = 'http://www.w3.org/2000/svg', XLINK_NS = 'http://www.w3.org/1999/xlink';
  // interface: [parent, element local names, reflected attributes "property:kind[:attribute[:default]]"]
  // kinds: L length, N number, I integer, B boolean, S string, E(k1,k2,…)[default index] enumeration,
  // R rect, P preserveAspectRatio, A angle, LL length list, NL number list, TL transform list,
  // SL string list, PL point list.
  const svgSpec = {
    SVGGraphicsElement: ['SVGElement', '', 'transform:TL requiredExtensions:SL systemLanguage:SL'],
    SVGGeometryElement: ['SVGGraphicsElement', '', 'pathLength:N'],
    SVGSVGElement: ['SVGGraphicsElement', 'svg', 'x:L y:L width:L::100% height:L::100% viewBox:R preserveAspectRatio:P'],
    SVGGElement: ['SVGGraphicsElement', 'g', ''],
    SVGDefsElement: ['SVGGraphicsElement', 'defs', ''],
    SVGDescElement: ['SVGElement', 'desc', ''],
    SVGMetadataElement: ['SVGElement', 'metadata', ''],
    SVGTitleElement: ['SVGElement', 'title', ''],
    SVGSymbolElement: ['SVGGraphicsElement', 'symbol', 'viewBox:R preserveAspectRatio:P'],
    SVGUseElement: ['SVGGraphicsElement', 'use', 'x:L y:L width:L height:L href:S'],
    SVGSwitchElement: ['SVGGraphicsElement', 'switch', ''],
    SVGStyleElement: ['SVGElement', 'style', ''],
    SVGScriptElement: ['SVGElement', 'script', 'href:S'],
    SVGAElement: ['SVGGraphicsElement', 'a', 'target:S href:S'],
    SVGViewElement: ['SVGElement', 'view', 'viewBox:R preserveAspectRatio:P'],
    SVGRectElement: ['SVGGeometryElement', 'rect', 'x:L y:L width:L height:L rx:L ry:L'],
    SVGCircleElement: ['SVGGeometryElement', 'circle', 'cx:L cy:L r:L'],
    SVGEllipseElement: ['SVGGeometryElement', 'ellipse', 'cx:L cy:L rx:L ry:L'],
    SVGLineElement: ['SVGGeometryElement', 'line', 'x1:L y1:L x2:L y2:L'],
    SVGPolylineElement: ['SVGGeometryElement', 'polyline', 'points:PL animatedPoints:PL:points'],
    SVGPolygonElement: ['SVGGeometryElement', 'polygon', 'points:PL animatedPoints:PL:points'],
    SVGPathElement: ['SVGGeometryElement', 'path', ''],
    SVGTextContentElement: ['SVGGraphicsElement', '', 'textLength:L lengthAdjust:E(spacing,spacingAndGlyphs)1'],
    SVGTextPositioningElement: ['SVGTextContentElement', '', 'x:LL y:LL dx:LL dy:LL rotate:NL'],
    SVGTextElement: ['SVGTextPositioningElement', 'text', ''],
    SVGTSpanElement: ['SVGTextPositioningElement', 'tspan', ''],
    SVGTextPathElement: ['SVGTextContentElement', 'textPath', 'startOffset:L method:E(align,stretch)1 spacing:E(auto,exact)2 side:E(left,right)1 href:S'],
    SVGImageElement: ['SVGGraphicsElement', 'image', 'x:L y:L width:L height:L preserveAspectRatio:P href:S'],
    SVGForeignObjectElement: ['SVGGraphicsElement', 'foreignObject', 'x:L y:L width:L height:L'],
    SVGMarkerElement: ['SVGElement', 'marker', 'refX:L refY:L markerUnits:E(userSpaceOnUse,strokeWidth)2 markerWidth:L::3 markerHeight:L::3 orientType:E(auto,angle,auto-start-reverse)2:orient orientAngle:A:orient viewBox:R preserveAspectRatio:P'],
    SVGGradientElement: ['SVGElement', '', 'gradientUnits:E(userSpaceOnUse,objectBoundingBox)2 gradientTransform:TL spreadMethod:E(pad,reflect,repeat)1 href:S'],
    SVGLinearGradientElement: ['SVGGradientElement', 'linearGradient', 'x1:L::0% y1:L::0% x2:L::100% y2:L::0%'],
    SVGRadialGradientElement: ['SVGGradientElement', 'radialGradient', 'cx:L::50% cy:L::50% r:L::50% fx:L::50% fy:L::50% fr:L::0%'],
    SVGStopElement: ['SVGElement', 'stop', 'offset:N'],
    SVGPatternElement: ['SVGElement', 'pattern', 'patternUnits:E(userSpaceOnUse,objectBoundingBox)2 patternContentUnits:E(userSpaceOnUse,objectBoundingBox)1 patternTransform:TL x:L y:L width:L height:L viewBox:R preserveAspectRatio:P href:S'],
    SVGClipPathElement: ['SVGGraphicsElement', 'clipPath', 'clipPathUnits:E(userSpaceOnUse,objectBoundingBox)1'],
    SVGMaskElement: ['SVGElement', 'mask', 'maskUnits:E(userSpaceOnUse,objectBoundingBox)2 maskContentUnits:E(userSpaceOnUse,objectBoundingBox)1 x:L::-10% y:L::-10% width:L::120% height:L::120%'],
    SVGFilterElement: ['SVGElement', 'filter', 'filterUnits:E(userSpaceOnUse,objectBoundingBox)2 primitiveUnits:E(userSpaceOnUse,objectBoundingBox)1 x:L::-10% y:L::-10% width:L::120% height:L::120% href:S'],
    SVGFEBlendElement: ['SVGElement', 'feBlend', 'in1:S:in in2:S mode:E(normal,multiply,screen,darken,lighten,overlay,color-dodge,color-burn,hard-light,soft-light,difference,exclusion,hue,saturation,color,luminosity)1'],
    SVGFEColorMatrixElement: ['SVGElement', 'feColorMatrix', 'in1:S:in type:E(matrix,saturate,hueRotate,luminanceToAlpha)1 values:NL'],
    SVGFEComponentTransferElement: ['SVGElement', 'feComponentTransfer', 'in1:S:in'],
    SVGComponentTransferFunctionElement: ['SVGElement', '', 'type:E(identity,table,discrete,linear,gamma)1 tableValues:NL slope:N::1 intercept:N amplitude:N::1 exponent:N::1 offset:N'],
    SVGFEFuncRElement: ['SVGComponentTransferFunctionElement', 'feFuncR', ''],
    SVGFEFuncGElement: ['SVGComponentTransferFunctionElement', 'feFuncG', ''],
    SVGFEFuncBElement: ['SVGComponentTransferFunctionElement', 'feFuncB', ''],
    SVGFEFuncAElement: ['SVGComponentTransferFunctionElement', 'feFuncA', ''],
    SVGFECompositeElement: ['SVGElement', 'feComposite', 'in1:S:in in2:S operator:E(over,in,out,atop,xor,arithmetic)1 k1:N k2:N k3:N k4:N'],
    SVGFEConvolveMatrixElement: ['SVGElement', 'feConvolveMatrix', 'in1:S:in orderX:I1:order:3 orderY:I2:order:3 kernelMatrix:NL divisor:N::1 bias:N targetX:I targetY:I edgeMode:E(duplicate,wrap,none)1 kernelUnitLengthX:N1:kernelUnitLength kernelUnitLengthY:N2:kernelUnitLength preserveAlpha:B'],
    SVGFEDiffuseLightingElement: ['SVGElement', 'feDiffuseLighting', 'in1:S:in surfaceScale:N::1 diffuseConstant:N::1 kernelUnitLengthX:N1:kernelUnitLength kernelUnitLengthY:N2:kernelUnitLength'],
    SVGFEDistantLightElement: ['SVGElement', 'feDistantLight', 'azimuth:N elevation:N'],
    SVGFEPointLightElement: ['SVGElement', 'fePointLight', 'x:N y:N z:N'],
    SVGFESpotLightElement: ['SVGElement', 'feSpotLight', 'x:N y:N z:N pointsAtX:N pointsAtY:N pointsAtZ:N specularExponent:N::1 limitingConeAngle:N'],
    SVGFEDisplacementMapElement: ['SVGElement', 'feDisplacementMap', 'in1:S:in in2:S scale:N xChannelSelector:E(R,G,B,A)4 yChannelSelector:E(R,G,B,A)4'],
    SVGFEDropShadowElement: ['SVGElement', 'feDropShadow', 'in1:S:in dx:N::2 dy:N::2 stdDeviationX:N1:stdDeviation:2 stdDeviationY:N2:stdDeviation:2'],
    SVGFEFloodElement: ['SVGElement', 'feFlood', ''],
    SVGFEGaussianBlurElement: ['SVGElement', 'feGaussianBlur', 'in1:S:in stdDeviationX:N1:stdDeviation stdDeviationY:N2:stdDeviation edgeMode:E(duplicate,wrap,none)3'],
    SVGFEImageElement: ['SVGElement', 'feImage', 'preserveAspectRatio:P href:S'],
    SVGFEMergeElement: ['SVGElement', 'feMerge', ''],
    SVGFEMergeNodeElement: ['SVGElement', 'feMergeNode', 'in1:S:in'],
    SVGFEMorphologyElement: ['SVGElement', 'feMorphology', 'in1:S:in operator:E(erode,dilate)1 radiusX:N1:radius radiusY:N2:radius'],
    SVGFEOffsetElement: ['SVGElement', 'feOffset', 'in1:S:in dx:N dy:N'],
    SVGFESpecularLightingElement: ['SVGElement', 'feSpecularLighting', 'in1:S:in surfaceScale:N::1 specularConstant:N::1 specularExponent:N::1 kernelUnitLengthX:N1:kernelUnitLength kernelUnitLengthY:N2:kernelUnitLength'],
    SVGFETileElement: ['SVGElement', 'feTile', 'in1:S:in'],
    SVGFETurbulenceElement: ['SVGElement', 'feTurbulence', 'baseFrequencyX:N1:baseFrequency baseFrequencyY:N2:baseFrequency numOctaves:I::1 seed:N stitchTiles:E(stitch,noStitch)2 type:E(fractalNoise,turbulence)2'],
  };
  // SVGFilterPrimitiveStandardAttributes (Filter Effects 1 §9.4): every filter primitive element.
  for (const name of ['Blend', 'ColorMatrix', 'ComponentTransfer', 'Composite', 'ConvolveMatrix', 'DiffuseLighting', 'DisplacementMap',
    'DropShadow', 'Flood', 'GaussianBlur', 'Image', 'Merge', 'Morphology', 'Offset', 'SpecularLighting', 'Tile', 'Turbulence'])
    svgSpec['SVGFE' + name + 'Element'][2] += ' x:L::0% y:L::0% width:L::100% height:L::100% result:S';
  // The constants of the interfaces (SVG 2 and Filter Effects IDL).
  const svgConsts = {
    SVGLength: 'SVG_LENGTHTYPE_UNKNOWN SVG_LENGTHTYPE_NUMBER SVG_LENGTHTYPE_PERCENTAGE SVG_LENGTHTYPE_EMS SVG_LENGTHTYPE_EXS SVG_LENGTHTYPE_PX SVG_LENGTHTYPE_CM SVG_LENGTHTYPE_MM SVG_LENGTHTYPE_IN SVG_LENGTHTYPE_PT SVG_LENGTHTYPE_PC',
    SVGAngle: 'SVG_ANGLETYPE_UNKNOWN SVG_ANGLETYPE_UNSPECIFIED SVG_ANGLETYPE_DEG SVG_ANGLETYPE_RAD SVG_ANGLETYPE_GRAD',
    SVGUnitTypes: 'SVG_UNIT_TYPE_UNKNOWN SVG_UNIT_TYPE_USERSPACEONUSE SVG_UNIT_TYPE_OBJECTBOUNDINGBOX',
    SVGTransform: 'SVG_TRANSFORM_UNKNOWN SVG_TRANSFORM_MATRIX SVG_TRANSFORM_TRANSLATE SVG_TRANSFORM_SCALE SVG_TRANSFORM_ROTATE SVG_TRANSFORM_SKEWX SVG_TRANSFORM_SKEWY',
    SVGPreserveAspectRatio: 'SVG_PRESERVEASPECTRATIO_UNKNOWN SVG_PRESERVEASPECTRATIO_NONE SVG_PRESERVEASPECTRATIO_XMINYMIN SVG_PRESERVEASPECTRATIO_XMIDYMIN SVG_PRESERVEASPECTRATIO_XMAXYMIN SVG_PRESERVEASPECTRATIO_XMINYMID SVG_PRESERVEASPECTRATIO_XMIDYMID SVG_PRESERVEASPECTRATIO_XMAXYMID SVG_PRESERVEASPECTRATIO_XMINYMAX SVG_PRESERVEASPECTRATIO_XMIDYMAX SVG_PRESERVEASPECTRATIO_XMAXYMAX|SVG_MEETORSLICE_UNKNOWN SVG_MEETORSLICE_MEET SVG_MEETORSLICE_SLICE',
    SVGTextContentElement: 'LENGTHADJUST_UNKNOWN LENGTHADJUST_SPACING LENGTHADJUST_SPACINGANDGLYPHS',
    SVGTextPathElement: 'TEXTPATH_METHODTYPE_UNKNOWN TEXTPATH_METHODTYPE_ALIGN TEXTPATH_METHODTYPE_STRETCH|TEXTPATH_SPACINGTYPE_UNKNOWN TEXTPATH_SPACINGTYPE_AUTO TEXTPATH_SPACINGTYPE_EXACT|TEXTPATH_SIDETYPE_UNKNOWN TEXTPATH_SIDETYPE_LEFT TEXTPATH_SIDETYPE_RIGHT',
    SVGMarkerElement: 'SVG_MARKERUNITS_UNKNOWN SVG_MARKERUNITS_USERSPACEONUSE SVG_MARKERUNITS_STROKEWIDTH|SVG_MARKER_ORIENT_UNKNOWN SVG_MARKER_ORIENT_AUTO SVG_MARKER_ORIENT_ANGLE SVG_MARKER_ORIENT_AUTO_START_REVERSE',
    SVGGradientElement: 'SVG_SPREADMETHOD_UNKNOWN SVG_SPREADMETHOD_PAD SVG_SPREADMETHOD_REFLECT SVG_SPREADMETHOD_REPEAT',
    SVGFEBlendElement: 'SVG_FEBLEND_MODE_UNKNOWN SVG_FEBLEND_MODE_NORMAL SVG_FEBLEND_MODE_MULTIPLY SVG_FEBLEND_MODE_SCREEN SVG_FEBLEND_MODE_DARKEN SVG_FEBLEND_MODE_LIGHTEN SVG_FEBLEND_MODE_OVERLAY SVG_FEBLEND_MODE_COLOR_DODGE SVG_FEBLEND_MODE_COLOR_BURN SVG_FEBLEND_MODE_HARD_LIGHT SVG_FEBLEND_MODE_SOFT_LIGHT SVG_FEBLEND_MODE_DIFFERENCE SVG_FEBLEND_MODE_EXCLUSION SVG_FEBLEND_MODE_HUE SVG_FEBLEND_MODE_SATURATION SVG_FEBLEND_MODE_COLOR SVG_FEBLEND_MODE_LUMINOSITY',
    SVGFEColorMatrixElement: 'SVG_FECOLORMATRIX_TYPE_UNKNOWN SVG_FECOLORMATRIX_TYPE_MATRIX SVG_FECOLORMATRIX_TYPE_SATURATE SVG_FECOLORMATRIX_TYPE_HUEROTATE SVG_FECOLORMATRIX_TYPE_LUMINANCETOALPHA',
    SVGComponentTransferFunctionElement: 'SVG_FECOMPONENTTRANSFER_TYPE_UNKNOWN SVG_FECOMPONENTTRANSFER_TYPE_IDENTITY SVG_FECOMPONENTTRANSFER_TYPE_TABLE SVG_FECOMPONENTTRANSFER_TYPE_DISCRETE SVG_FECOMPONENTTRANSFER_TYPE_LINEAR SVG_FECOMPONENTTRANSFER_TYPE_GAMMA',
    SVGFECompositeElement: 'SVG_FECOMPOSITE_OPERATOR_UNKNOWN SVG_FECOMPOSITE_OPERATOR_OVER SVG_FECOMPOSITE_OPERATOR_IN SVG_FECOMPOSITE_OPERATOR_OUT SVG_FECOMPOSITE_OPERATOR_ATOP SVG_FECOMPOSITE_OPERATOR_XOR SVG_FECOMPOSITE_OPERATOR_ARITHMETIC',
    SVGFEConvolveMatrixElement: 'SVG_EDGEMODE_UNKNOWN SVG_EDGEMODE_DUPLICATE SVG_EDGEMODE_WRAP SVG_EDGEMODE_NONE',
    SVGFEDisplacementMapElement: 'SVG_CHANNEL_UNKNOWN SVG_CHANNEL_R SVG_CHANNEL_G SVG_CHANNEL_B SVG_CHANNEL_A',
    SVGFEMorphologyElement: 'SVG_MORPHOLOGY_OPERATOR_UNKNOWN SVG_MORPHOLOGY_OPERATOR_ERODE SVG_MORPHOLOGY_OPERATOR_DILATE',
    SVGFETurbulenceElement: 'SVG_TURBULENCE_TYPE_UNKNOWN SVG_TURBULENCE_TYPE_FRACTALNOISE SVG_TURBULENCE_TYPE_TURBULENCE|SVG_STITCHTYPE_UNKNOWN SVG_STITCHTYPE_STITCH SVG_STITCHTYPE_NOSTITCH',
    SVGFEGaussianBlurElement: 'SVG_EDGEMODE_UNKNOWN SVG_EDGEMODE_DUPLICATE SVG_EDGEMODE_WRAP SVG_EDGEMODE_NONE',
  };
  const svgValueNames = ['SVGNumber', 'SVGLength', 'SVGAngle', 'SVGTransform', 'SVGPreserveAspectRatio', 'SVGUnitTypes',
    'SVGNumberList', 'SVGLengthList', 'SVGStringList', 'SVGPointList', 'SVGTransformList',
    'SVGAnimatedBoolean', 'SVGAnimatedEnumeration', 'SVGAnimatedInteger', 'SVGAnimatedNumber', 'SVGAnimatedLength',
    'SVGAnimatedAngle', 'SVGAnimatedString', 'SVGAnimatedRect', 'SVGAnimatedNumberList', 'SVGAnimatedLengthList',
    'SVGAnimatedTransformList', 'SVGAnimatedPreserveAspectRatio'];
  let svgBuilt = null;
  const svgDom = () => svgBuilt ?? (svgBuilt = buildSvgDom());
  svgProtoOf = tag => (svgDom().byTag[tag] ?? SVGElement).prototype;
  const buildSvgDom = () => {
    const classes = { SVGElement }, byTag = Object.create(null);
    const key = {};
    const illegal = () => { throw new TypeError('Illegal constructor'); };
    // WebIDL `float`: finite, and within the range of a single-precision number.
    const float = (v, what) => { const x = Number(v); if (!Number.isFinite(x) || Math.abs(x) > 3.4028234663852886e38) throw new TypeError(`${what}: the value is not a finite single-precision number`); return x; };
    const need = (n, have, what) => { if (have < n) throw new TypeError(`${what}: ${n} argument${n > 1 ? 's' : ''} required, but only ${have} present.`); };
    const noMod = what => { throw new DOMException(`${what}: the object is read-only`, 'NoModificationAllowedError'); };
    const brandOf = (map, o, what) => { const s = map.get(o); if (!s) throw new TypeError('Illegal invocation: ' + what); return s; };
    const mk = (C, map, s) => { const o = Object.create(C.prototype); map.set(o, s); return o; };
    // What Lean reads of a value.
    const lenOf = text => { const r = apiCall(92, [text]); if (typeof r !== 'string') return null; const p = r.split('\n'); return { n: Number(p[0]), u: p[1], t: Number(p[2]) }; };
    const numOf = text => { const r = apiCall(93, [text]); return typeof r === 'string' ? Number(r) : null; };
    const numsOf = text => { const r = apiCall(94, [text]); return typeof r !== 'string' ? null : r === '' ? [] : r.split('\n').map(Number); };
    const transformsOf = text => { const r = apiCall(95, [text]); return typeof r !== 'string' ? null : r === '' ? [] : r.split('\n').map(l => { const p = l.split(' '); return { name: p[0], args: p.slice(1).map(Number) }; }); };
    const fmt = x => String(x);

    // ---- SVGNumber ---------------------------------------------------------------------------
    const numbers = new WeakMap();
    class SVGNumber {
      constructor(k) { if (k !== key) illegal(); }
      get value() { return Math.fround(brandOf(numbers, this, 'SVGNumber.value').v); }
      set value(x) { const s = brandOf(numbers, this, 'SVGNumber.value'); if (s.readonly) noMod('SVGNumber.value'); s.v = float(x, 'SVGNumber.value'); if (s.owner) s.owner.commit(); }
    }
    const newNumber = (v, owner, readonly) => mk(SVGNumber, numbers, { v, owner: owner ?? null, readonly: !!readonly });

    // ---- SVGLength ---------------------------------------------------------------------------
    const UNITS = ['', '', '%', 'em', 'ex', 'px', 'cm', 'mm', 'in', 'pt', 'pc'];
    const lengths = new WeakMap();
    const fontPx = el => { try { const f = el ? parseFloat(getComputedStyle(el).fontSize) : NaN; return Number.isFinite(f) && f > 0 ? f : 16; } catch { return 16; } };
    const viewportOf = el => {
      for (let p = el && el.parentNode; p; p = p.parentNode) {
        if (p.namespaceURI === SVG_NS && p.localName === 'svg') {
          const vb = numsOf(p.getAttribute('viewBox') ?? '');
          if (vb && vb.length === 4) return [vb[2], vb[3]];
          const w = lenOf(p.getAttribute('width') ?? ''), h = lenOf(p.getAttribute('height') ?? '');
          return [w && w.t !== 2 ? w.n : 300, h && h.t !== 2 ? h.n : 150];
        }
      }
      return [globalThis.innerWidth ?? 800, globalThis.innerHeight ?? 600];
    };
    const horizontal = new Set(['x', 'cx', 'x1', 'x2', 'width', 'dx', 'rx', 'fx', 'refX', 'markerWidth', 'textLength', 'startOffset']);
    const vertical = new Set(['y', 'cy', 'y1', 'y2', 'height', 'dy', 'ry', 'fy', 'refY', 'markerHeight']);
    // User units for one unit of a length (CSS Values 4 §6 absolute lengths; font and viewport units from the page).
    const unitPx = (s, v) => {
      switch (v.u) {
        case '': case 'px': return 1;
        case 'cm': return 96 / 2.54;
        case 'mm': return 96 / 25.4;
        case 'q': return 96 / 101.6;
        case 'in': return 96;
        case 'pt': return 96 / 72;
        case 'pc': return 16;
        case 'em': case 'ic': return fontPx(s.el);
        case 'ex': case 'ch': return fontPx(s.el) / 2;
        case 'cap': return fontPx(s.el) * 0.7;
        case 'rem': return fontPx(document.documentElement);
        case 'rex': return fontPx(document.documentElement) / 2;
        case 'lh': return fontPx(s.el) * 1.2;
        case 'rlh': return fontPx(document.documentElement) * 1.2;
        case 'vw': case 'vi': return (globalThis.innerWidth ?? 800) / 100;
        case 'vh': case 'vb': return (globalThis.innerHeight ?? 600) / 100;
        case 'vmin': return Math.min(globalThis.innerWidth ?? 800, globalThis.innerHeight ?? 600) / 100;
        case 'vmax': return Math.max(globalThis.innerWidth ?? 800, globalThis.innerHeight ?? 600) / 100;
        case '%': {
          const [w, h] = viewportOf(s.el);
          return (horizontal.has(s.attr) ? w : vertical.has(s.attr) ? h : Math.sqrt((w * w + h * h) / 2)) / 100;
        }
        default: return 1;
      }
    };
    // A length's state reads and writes its value: a detached one its own, a reflecting one its attribute.
    const detachedLength = (v, owner) => ({ el: null, attr: '', v, owner: owner ?? null, readonly: false,
      read() { return this.v; }, write(n, unit) { this.v = { n, u: unit.u, t: unit.t }; if (this.owner) this.owner.commit(); } });
    const boundLength = (el, attr, dflt, readonly) => ({ el, attr, readonly,
      read() { const t = el.getAttribute(attr); return (t !== null && lenOf(t)) || lenOf(dflt) || { n: 0, u: '', t: 1 }; },
      write(n, unit) { el.setAttribute(attr, fmt(n) + unit.u); } });
    const unitOfType = (t, what) => { const k = Number(t) & 0xFFFF; if (k < 1 || k > 10) throw new DOMException(`${what}: the unit type ${k} is not supported`, 'NotSupportedError'); return { u: UNITS[k], t: k }; };
    class SVGLength {
      constructor(k) { if (k !== key) illegal(); }
      get unitType() { return brandOf(lengths, this, 'SVGLength.unitType').read().t; }
      get value() { const s = brandOf(lengths, this, 'SVGLength.value'), v = s.read(); return Math.fround(v.n * unitPx(s, v)); }
      set value(x) { const s = brandOf(lengths, this, 'SVGLength.value'); if (s.readonly) noMod('SVGLength.value'); const n = float(x, 'SVGLength.value'), v = s.read(); s.write(n / unitPx(s, v), v); }
      get valueInSpecifiedUnits() { return Math.fround(brandOf(lengths, this, 'SVGLength.valueInSpecifiedUnits').read().n); }
      set valueInSpecifiedUnits(x) { const s = brandOf(lengths, this, 'SVGLength.valueInSpecifiedUnits'); if (s.readonly) noMod('SVGLength.valueInSpecifiedUnits'); s.write(float(x, 'SVGLength.valueInSpecifiedUnits'), s.read()); }
      get valueAsString() { const v = brandOf(lengths, this, 'SVGLength.valueAsString').read(); return fmt(v.n) + v.u; }
      set valueAsString(t) {
        const s = brandOf(lengths, this, 'SVGLength.valueAsString');
        if (s.readonly) noMod('SVGLength.valueAsString');
        const v = lenOf(String(t));
        if (!v) throw new DOMException(`Failed to set 'valueAsString' on 'SVGLength': '${t}' is not a length`, 'SyntaxError');
        s.write(v.n, v);
      }
      newValueSpecifiedUnits(unitType, value) {
        need(2, arguments.length, "Failed to execute 'newValueSpecifiedUnits' on 'SVGLength'");
        const s = brandOf(lengths, this, 'SVGLength.newValueSpecifiedUnits');
        if (s.readonly) noMod('SVGLength.newValueSpecifiedUnits');
        const n = float(value, 'SVGLength.newValueSpecifiedUnits');
        s.write(n, unitOfType(unitType, 'SVGLength.newValueSpecifiedUnits'));
      }
      convertToSpecifiedUnits(unitType) {
        need(1, arguments.length, "Failed to execute 'convertToSpecifiedUnits' on 'SVGLength'");
        const s = brandOf(lengths, this, 'SVGLength.convertToSpecifiedUnits');
        if (s.readonly) noMod('SVGLength.convertToSpecifiedUnits');
        const unit = unitOfType(unitType, 'SVGLength.convertToSpecifiedUnits'), v = s.read();
        s.write(v.n * unitPx(s, v) / unitPx(s, unit), unit);
      }
    }
    const newLength = state => mk(SVGLength, lengths, state);

    // ---- SVGAngle ----------------------------------------------------------------------------
    const ANGLES = ['', '', 'deg', 'rad', 'grad'], angles = new WeakMap();
    const angleOf = text => {
      const m = /^(.*?)(deg|rad|grad|turn)?$/i.exec(String(text).trim());
      const n = m ? numOf(m[1]) : null, u = m && m[2] ? m[2].toLowerCase() : '';
      return n === null ? null : { n, u, t: u === '' ? 1 : ANGLES.indexOf(u) < 0 ? 0 : ANGLES.indexOf(u) };
    };
    const degrees = v => v.u === 'rad' ? v.n * 180 / Math.PI : v.u === 'grad' ? v.n * 0.9 : v.u === 'turn' ? v.n * 360 : v.n;
    const fromDegrees = (d, u) => u === 'rad' ? d * Math.PI / 180 : u === 'grad' ? d / 0.9 : d;
    const angleUnit = (t, what) => { const k = Number(t) & 0xFFFF; if (k < 1 || k > 4) throw new DOMException(`${what}: the unit type ${k} is not supported`, 'NotSupportedError'); return { u: ANGLES[k], t: k }; };
    class SVGAngle {
      constructor(k) { if (k !== key) illegal(); }
      get unitType() { return brandOf(angles, this, 'SVGAngle.unitType').read().t; }
      get value() { return Math.fround(degrees(brandOf(angles, this, 'SVGAngle.value').read())); }
      set value(x) { const s = brandOf(angles, this, 'SVGAngle.value'); if (s.readonly) noMod('SVGAngle.value'); const v = s.read(); s.write(fromDegrees(float(x, 'SVGAngle.value'), v.u), v); }
      get valueInSpecifiedUnits() { return Math.fround(brandOf(angles, this, 'SVGAngle.valueInSpecifiedUnits').read().n); }
      set valueInSpecifiedUnits(x) { const s = brandOf(angles, this, 'SVGAngle.valueInSpecifiedUnits'); if (s.readonly) noMod('SVGAngle.valueInSpecifiedUnits'); s.write(float(x, 'SVGAngle.valueInSpecifiedUnits'), s.read()); }
      get valueAsString() { const v = brandOf(angles, this, 'SVGAngle.valueAsString').read(); return fmt(v.n) + v.u; }
      set valueAsString(t) {
        const s = brandOf(angles, this, 'SVGAngle.valueAsString');
        if (s.readonly) noMod('SVGAngle.valueAsString');
        const v = angleOf(t);
        if (!v || v.t === 0) throw new DOMException(`Failed to set 'valueAsString' on 'SVGAngle': '${t}' is not an angle`, 'SyntaxError');
        s.write(v.n, v);
      }
      newValueSpecifiedUnits(unitType, value) {
        need(2, arguments.length, "Failed to execute 'newValueSpecifiedUnits' on 'SVGAngle'");
        const s = brandOf(angles, this, 'SVGAngle.newValueSpecifiedUnits');
        if (s.readonly) noMod('SVGAngle.newValueSpecifiedUnits');
        const n = float(value, 'SVGAngle.newValueSpecifiedUnits');
        s.write(n, angleUnit(unitType, 'SVGAngle.newValueSpecifiedUnits'));
      }
      convertToSpecifiedUnits(unitType) {
        need(1, arguments.length, "Failed to execute 'convertToSpecifiedUnits' on 'SVGAngle'");
        const s = brandOf(angles, this, 'SVGAngle.convertToSpecifiedUnits');
        if (s.readonly) noMod('SVGAngle.convertToSpecifiedUnits');
        const unit = angleUnit(unitType, 'SVGAngle.convertToSpecifiedUnits');
        s.write(fromDegrees(degrees(s.read()), unit.u), unit);
      }
    }
    const detachedAngle = () => ({ readonly: false, v: { n: 0, u: '', t: 1 }, read() { return this.v; }, write(n, unit) { this.v = { n, u: unit.u, t: unit.t }; } });

    // ---- SVGTransform ------------------------------------------------------------------------
    const transforms = new WeakMap();
    const rad = d => d * Math.PI / 180;
    const matrixFor = (name, a) => {
      switch (name) {
        case 'matrix': return [a[0], a[1], a[2], a[3], a[4], a[5]];
        case 'translate': return [1, 0, 0, 1, a[0], a[1] ?? 0];
        case 'scale': return [a[0], 0, 0, a[1] ?? a[0], 0, 0];
        case 'rotate': {
          const c = Math.cos(rad(a[0])), s = Math.sin(rad(a[0])), cx = a[1] ?? 0, cy = a[2] ?? 0;
          return [c, s, -s, c, cx - c * cx + s * cy, cy - s * cx - c * cy];
        }
        case 'skewX': return [1, 0, Math.tan(rad(a[0])), 1, 0, 0];
        case 'skewY': return [1, Math.tan(rad(a[0])), 0, 1, 0, 0];
        default: return [1, 0, 0, 1, 0, 0];
      }
    };
    const TRANSFORMS = ['', 'matrix', 'translate', 'scale', 'rotate', 'skewX', 'skewY'];
    const mul = (p, q) => [p[0] * q[0] + p[2] * q[1], p[1] * q[0] + p[3] * q[1], p[0] * q[2] + p[2] * q[3], p[1] * q[2] + p[3] * q[3],
      p[0] * q[4] + p[2] * q[5] + p[4], p[1] * q[4] + p[3] * q[5] + p[5]];
    const matrix2D = (m, what) => {
      if (m === undefined || m === null) return [1, 0, 0, 1, 0, 0];
      if (typeof m !== 'object') throw new TypeError(`${what}: the matrix is not an object`);
      const g = (x, y, d) => m[x] !== undefined ? Number(m[x]) : m[y] !== undefined ? Number(m[y]) : d;
      return [g('a', 'm11', 1), g('b', 'm12', 0), g('c', 'm21', 0), g('d', 'm22', 1), g('e', 'm41', 0), g('f', 'm42', 0)];
    };
    const domMatrix = v => new globalThis.DOMMatrix(v);
    const setT = (o, name, args) => {
      const s = brandOf(transforms, o, 'SVGTransform');
      if (s.readonly) noMod('SVGTransform');
      s.name = name; s.args = args; s.matrix = undefined;
      if (s.owner) s.owner.commit();
    };
    class SVGTransform {
      constructor(k) { if (k !== key) illegal(); }
      get type() { return TRANSFORMS.indexOf(brandOf(transforms, this, 'SVGTransform.type').name); }
      get matrix() { const s = brandOf(transforms, this, 'SVGTransform.matrix'); return s.matrix ?? (s.matrix = domMatrix(matrixFor(s.name, s.args))); }
      get angle() { const s = brandOf(transforms, this, 'SVGTransform.angle'); return s.name === 'rotate' || s.name === 'skewX' || s.name === 'skewY' ? Math.fround(s.args[0]) : 0; }
      setMatrix(matrix = undefined) { setT(this, 'matrix', matrix2D(matrix, 'SVGTransform.setMatrix')); }
      setTranslate(tx, ty) { need(2, arguments.length, "Failed to execute 'setTranslate' on 'SVGTransform'"); setT(this, 'translate', [float(tx, 'setTranslate'), float(ty, 'setTranslate')]); }
      setScale(sx, sy) { need(2, arguments.length, "Failed to execute 'setScale' on 'SVGTransform'"); setT(this, 'scale', [float(sx, 'setScale'), float(sy, 'setScale')]); }
      setRotate(angle, cx, cy) { need(3, arguments.length, "Failed to execute 'setRotate' on 'SVGTransform'"); setT(this, 'rotate', [float(angle, 'setRotate'), float(cx, 'setRotate'), float(cy, 'setRotate')]); }
      setSkewX(angle) { need(1, arguments.length, "Failed to execute 'setSkewX' on 'SVGTransform'"); setT(this, 'skewX', [float(angle, 'setSkewX')]); }
      setSkewY(angle) { need(1, arguments.length, "Failed to execute 'setSkewY' on 'SVGTransform'"); setT(this, 'skewY', [float(angle, 'setSkewY')]); }
    }
    const newTransform = (name, args, owner, readonly) => mk(SVGTransform, transforms, { name, args, matrix: undefined, owner: owner ?? null, readonly: !!readonly });
    const transformText = s => {
      const a = s.matrix ? [s.matrix.a, s.matrix.b, s.matrix.c, s.matrix.d, s.matrix.e, s.matrix.f] : s.args;
      return (s.matrix ? 'matrix' : s.name) + '(' + a.map(fmt).join(' ') + ')';
    };

    // ---- the lists (SVG 2 §4.6.4 "List interfaces") --------------------------------------------
    // A list reflects an attribute: it is read again when the attribute's text changed, and a
    // change of the list or of one of its items writes the attribute.
    const lists = new WeakMap();
    const makeList = (name, kind) => {
      // kind: { parse(text) -> items or null, text(items) -> string, accept(v, state, what) -> item }
      class List {
        constructor(k) { if (k !== key) illegal(); }
        get length() { return LS(this, 'length').sync().length; }
        get numberOfItems() { return LS(this, 'numberOfItems').sync().length; }
        clear() { const s = LS(this, 'clear'); s.guard('clear'); const old = s.items; s.items = []; if (kind.release) old.forEach(kind.release); s.commit(); }
        initialize(newItem) { need(1, arguments.length, `Failed to execute 'initialize' on '${name}'`); const s = LS(this, 'initialize'); s.guard('initialize'); const old = s.items, item = kind.accept(newItem, s, 'initialize'); s.items = [item]; if (kind.release) old.forEach(i => { if (i !== item) kind.release(i); }); s.commit(); return item; }
        getItem(index) { need(1, arguments.length, `Failed to execute 'getItem' on '${name}'`); const s = LS(this, 'getItem'), items = s.sync(), i = Number(index) >>> 0; if (i >= items.length) throw new DOMException(`Failed to execute 'getItem' on '${name}': the index ${i} is not in the list`, 'IndexSizeError'); return items[i]; }
        insertItemBefore(newItem, index) { need(2, arguments.length, `Failed to execute 'insertItemBefore' on '${name}'`); const s = LS(this, 'insertItemBefore'); s.guard('insertItemBefore'); const items = s.sync(), item = kind.accept(newItem, s, 'insertItemBefore'); items.splice(Math.min(Number(index) >>> 0, items.length), 0, item); s.commit(); return item; }
        replaceItem(newItem, index) { need(2, arguments.length, `Failed to execute 'replaceItem' on '${name}'`); const s = LS(this, 'replaceItem'); s.guard('replaceItem'); const items = s.sync(), i = Number(index) >>> 0, item = kind.accept(newItem, s, 'replaceItem'); if (i >= items.length) throw new DOMException(`Failed to execute 'replaceItem' on '${name}': the index ${i} is not in the list`, 'IndexSizeError'); const was = items[i]; items[i] = item; if (kind.release && was !== item) kind.release(was); s.commit(); return item; }
        removeItem(index) { need(1, arguments.length, `Failed to execute 'removeItem' on '${name}'`); const s = LS(this, 'removeItem'); s.guard('removeItem'); const items = s.sync(), i = Number(index) >>> 0; if (i >= items.length) throw new DOMException(`Failed to execute 'removeItem' on '${name}': the index ${i} is not in the list`, 'IndexSizeError'); const item = items.splice(i, 1)[0]; if (kind.release) kind.release(item); s.commit(); return item; }
        appendItem(newItem) { need(1, arguments.length, `Failed to execute 'appendItem' on '${name}'`); const s = LS(this, 'appendItem'); s.guard('appendItem'); const items = s.sync(), item = kind.accept(newItem, s, 'appendItem'); items.push(item); s.commit(); return item; }
      }
      const LS = (o, what) => brandOf(lists, o, `${name}.${what}`);
      Object.defineProperty(List, 'name', { value: name });
      const isIndex = p => typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p);
      const make = (el, attr, readonly) => {
        const s = { el, attr, readonly, items: [], text: undefined,
          // SVG 2 §4.6.4 "synchronize": the items that stay keep their objects and take the new
          // values; the ones past the new end are no longer the list's.
          sync() {
            const t = el.getAttribute(attr) ?? '';
            if (t === this.text) return this.items;
            this.text = t;
            const raw = kind.parse(t, this) ?? [], old = this.items;
            this.items = raw.map((v, i) => i < old.length && kind.assign ? kind.assign(old[i], v, this) : kind.make(v, this));
            if (kind.release) for (let i = raw.length; i < old.length; i++) kind.release(old[i]);
            return this.items;
          },
          commit() { this.text = kind.text(this.items); el.setAttribute(attr, this.text); },
          guard(what) { if (readonly) noMod(`${name}.${what}`); this.sync(); } };
        const target = Object.create(List.prototype);
        const proxy = new Proxy(target, {
          get(t, p, r) { if (isIndex(p)) { const items = s.sync(); return items[Number(p)]; } return Reflect.get(t, p, r); },
          set(t, p, v, r) { if (isIndex(p)) { proxy.replaceItem(v, Number(p)); return true; } return Reflect.set(t, p, v, r); },
          has(t, p) { return isIndex(p) ? Number(p) < s.sync().length : Reflect.has(t, p); },
          ownKeys(t) { return [...s.sync().keys()].map(String).concat(Reflect.ownKeys(t)); },
          getOwnPropertyDescriptor(t, p) { if (isIndex(p)) { const items = s.sync(); return Number(p) < items.length ? { value: items[Number(p)], writable: true, enumerable: true, configurable: true } : undefined; } return Reflect.getOwnPropertyDescriptor(t, p); },
        });
        lists.set(proxy, s);
        return proxy;
      };
      return { List, make };
    };
    const numberList = makeList('SVGNumberList', {
      parse: t => numsOf(t),
      make: (v, s) => newNumber(v, s, s.readonly),
      assign: (item, v) => { numbers.get(item).v = v; return item; },
      text: items => items.map(i => fmt(numbers.get(i).v)).join(' '),
      accept(v, s, what) { const st = numbers.get(v); if (!st) throw new TypeError(`Failed to execute '${what}' on 'SVGNumberList': parameter 1 is not of type 'SVGNumber'.`); return st.owner || st.readonly ? newNumber(st.v, s) : (st.owner = s, v); },
      release(item) { numbers.get(item).owner = null; },
    });
    const lengthList = makeList('SVGLengthList', {
      parse: (t, s) => {
        const parts = t.trim() === '' ? [] : t.trim().split(/[\t\n\f\r ]*,[\t\n\f\r ]*|[\t\n\f\r ]+/);
        const vs = parts.map(lenOf);
        return vs.some(v => v === null) ? null : vs;
      },
      make: (v, s) => { const l = newLength(detachedLength(v, s)); lengths.get(l).readonly = s.readonly; return l; },
      assign: (item, v) => { lengths.get(item).v = v; return item; },
      text: items => items.map(i => { const v = lengths.get(i).read(); return fmt(v.n) + v.u; }).join(' '),
      accept(v, s, what) { const st = lengths.get(v); if (!st) throw new TypeError(`Failed to execute '${what}' on 'SVGLengthList': parameter 1 is not of type 'SVGLength'.`); if (st.el || st.owner || st.readonly) return newLength(detachedLength({ ...st.read() }, s)); st.owner = s; return v; },
      release(item) { lengths.get(item).owner = null; },
    });
    const stringList = makeList('SVGStringList', {
      parse: t => t.trim() === '' ? [] : t.trim().split(/[\t\n\f\r ,]+/),
      make: v => v,
      text: items => items.join(' '),
      accept: v => String(v),
    });
    const pointList = makeList('SVGPointList', {
      parse: t => { const ns = numsOf(t); if (!ns) return null; const out = []; for (let i = 0; i + 1 < ns.length; i += 2) out.push([ns[i], ns[i + 1]]); return out; },
      make: v => new globalThis.DOMPoint(v[0], v[1]),
      assign: (item, v) => { item.x = v[0]; item.y = v[1]; return item; },
      text: items => items.map(p => fmt(p.x) + ',' + fmt(p.y)).join(' '),
      accept(v, s, what) { if (v === null || typeof v !== 'object' || !(v instanceof globalThis.DOMPointReadOnly)) throw new TypeError(`Failed to execute '${what}' on 'SVGPointList': parameter 1 is not of type 'SVGPoint'.`); return new globalThis.DOMPoint(v.x, v.y); },
    });
    const transformList = makeList('SVGTransformList', {
      parse: t => transformsOf(t),
      make: (x, s) => newTransform(x.name, x.args, s, s.readonly),
      assign: (item, x) => { const st = transforms.get(item); st.name = x.name; st.args = x.args; st.matrix = undefined; return item; },
      text: items => items.map(i => transformText(transforms.get(i))).join(' '),
      accept(v, s, what) { const st = transforms.get(v); if (!st) throw new TypeError(`Failed to execute '${what}' on 'SVGTransformList': parameter 1 is not of type 'SVGTransform'.`); if (st.owner || st.readonly) { const c = newTransform(st.name, st.args.slice(), s); if (st.matrix) transforms.get(c).matrix = domMatrix([st.matrix.a, st.matrix.b, st.matrix.c, st.matrix.d, st.matrix.e, st.matrix.f]); return c; } st.owner = s; return v; },
      release(item) { transforms.get(item).owner = null; },
    });
    const matrixOfTransform = st => st.matrix ? [st.matrix.a, st.matrix.b, st.matrix.c, st.matrix.d, st.matrix.e, st.matrix.f] : matrixFor(st.name, st.args);
    define(transformList.List.prototype, 'createSVGTransformFromMatrix', function createSVGTransformFromMatrix(matrix = undefined) {
      brandOf(lists, this, 'SVGTransformList.createSVGTransformFromMatrix');
      return newTransform('matrix', matrix2D(matrix, 'createSVGTransformFromMatrix'));
    });
    define(transformList.List.prototype, 'consolidate', function consolidate() {
      const s = brandOf(lists, this, 'SVGTransformList.consolidate');
      s.guard('consolidate');
      const items = s.sync();
      if (items.length === 0) return null;
      const m = items.reduce((acc, i) => mul(acc, matrixOfTransform(transforms.get(i))), [1, 0, 0, 1, 0, 0]);
      for (const i of items) transforms.get(i).owner = null;
      const t = newTransform('matrix', m, s);
      s.items = [t]; s.commit();
      return t;
    });

    // ---- SVGPreserveAspectRatio ----------------------------------------------------------------
    const ALIGN = ['', 'none', 'xMinYMin', 'xMidYMin', 'xMaxYMin', 'xMinYMid', 'xMidYMid', 'xMaxYMid', 'xMinYMax', 'xMidYMax', 'xMaxYMax'];
    const ratios = new WeakMap();
    const ratioOf = el => {
      const p = (el.getAttribute('preserveAspectRatio') ?? '').trim().split(/[\t\n\f\r ]+/).filter(x => x !== '');
      const align = p.length ? ALIGN.indexOf(p[0]) : 6, meet = p.length < 2 ? 1 : p[1] === 'meet' ? 1 : p[1] === 'slice' ? 2 : 0;
      return align < 1 || meet === 0 || p.length > 2 ? { align: 6, meet: 1 } : { align, meet };
    };
    class SVGPreserveAspectRatio {
      constructor(k) { if (k !== key) illegal(); }
      get align() { return ratioOf(brandOf(ratios, this, 'SVGPreserveAspectRatio.align').el).align; }
      set align(v) { const s = brandOf(ratios, this, 'SVGPreserveAspectRatio.align'); if (s.readonly) noMod('SVGPreserveAspectRatio.align'); const k = Number(v) & 0xFFFF; if (k < 1 || k > 10) throw new DOMException(`The alignment ${k} is not supported`, 'NotSupportedError'); const r = ratioOf(s.el); s.el.setAttribute('preserveAspectRatio', ALIGN[k] + (r.meet === 2 ? ' slice' : ' meet')); }
      get meetOrSlice() { return ratioOf(brandOf(ratios, this, 'SVGPreserveAspectRatio.meetOrSlice').el).meet; }
      set meetOrSlice(v) { const s = brandOf(ratios, this, 'SVGPreserveAspectRatio.meetOrSlice'); if (s.readonly) noMod('SVGPreserveAspectRatio.meetOrSlice'); const k = Number(v) & 0xFFFF; if (k < 1 || k > 2) throw new DOMException(`The meetOrSlice value ${k} is not supported`, 'NotSupportedError'); const r = ratioOf(s.el); s.el.setAttribute('preserveAspectRatio', ALIGN[r.align] + (k === 2 ? ' slice' : ' meet')); }
    }

    // ---- the animated values: each reflects one attribute of one element -----------------------
    const anims = new WeakMap();
    const AS = (o, what) => brandOf(anims, o, what);
    const hrefOf = el => el.getAttribute('href') ?? el.getAttributeNS(XLINK_NS, 'href') ?? '';
    const animated = {};
    const scalar = (name, read, write) => {
      const C = class { constructor(k) { if (k !== key) illegal(); }
        get baseVal() { return read(AS(this, name + '.baseVal')); }
        set baseVal(v) { write(AS(this, name + '.baseVal'), v); }
        get animVal() { return read(AS(this, name + '.animVal')); } };
      Object.defineProperty(C, 'name', { value: name });
      return animated[name] = C;
    };
    const numberIn = s => {
      const t = s.el.getAttribute(s.attr);
      if (t === null) return s.dflt === '' ? 0 : Number(s.dflt);
      // one number of a pair (`stdDeviation="2 3"`): the second is the first when it is absent
      if (s.part) { const ns = numsOf(t); return ns && ns.length >= 1 && ns.length <= 2 ? ns[Math.min(s.part, ns.length) - 1] : (s.dflt === '' ? 0 : Number(s.dflt)); }
      // `offset` of a gradient stop is a number or a percentage (SVG 2 §13.2.4)
      const pct = s.attr === 'offset' && s.el.localName === 'stop' && /%\s*$/.test(t) ? numOf(t.trim().slice(0, -1)) : null;
      const n = pct !== null ? pct / 100 : numOf(t);
      return n === null ? (s.dflt === '' ? 0 : Number(s.dflt)) : n;
    };
    // Writing one number of a pair keeps the other.
    const numberOut = (s, x) => {
      if (!s.part) { s.el.setAttribute(s.attr, fmt(x)); return; }
      const other = numberIn({ ...s, part: 3 - s.part });
      s.el.setAttribute(s.attr, s.part === 1 ? fmt(x) + ' ' + fmt(other) : fmt(other) + ' ' + fmt(x));
    };
    scalar('SVGAnimatedNumber', s => Math.fround(numberIn(s)), (s, v) => numberOut(s, float(v, 'SVGAnimatedNumber.baseVal')));
    scalar('SVGAnimatedInteger', s => Math.trunc(numberIn(s)) | 0, (s, v) => numberOut(s, Number(v) | 0));
    scalar('SVGAnimatedBoolean', s => s.el.getAttribute(s.attr) === 'true', (s, v) => s.el.setAttribute(s.attr, v ? 'true' : 'false'));
    scalar('SVGAnimatedString', s => s.attr === 'href' ? hrefOf(s.el) : (s.el.getAttribute(s.attr) ?? ''),
      (s, v) => { if (s.attr === 'href' && !s.el.hasAttribute('href') && s.el.hasAttributeNS(XLINK_NS, 'href')) s.el.setAttributeNS(XLINK_NS, 'xlink:href', String(v)); else s.el.setAttribute(s.attr, String(v)); });
    scalar('SVGAnimatedEnumeration', s => {
      const t = s.el.getAttribute(s.attr);
      if (s.attr === 'orient') return t === 'auto' ? 1 : t === 'auto-start-reverse' ? 3 : 2;
      // an absent or invalid value is the initial value (SVG 2 §4.6.3 "reflecting an enumerated attribute")
      return t === null || !s.values.includes(t) ? s.dflt : s.values.indexOf(t) + 1;
    }, (s, v) => {
      const k = Number(v) & 0xFFFF;
      if (s.attr === 'orient') { if (k < 1 || k > 3) throw new TypeError(`The enumeration value ${k} is not valid`); s.el.setAttribute('orient', k === 1 ? 'auto' : k === 3 ? 'auto-start-reverse' : '0'); return; }
      if (k < 1 || k > s.values.length) throw new TypeError(`Failed to set 'baseVal' on 'SVGAnimatedEnumeration': the value ${k} is not valid`);
      s.el.setAttribute(s.attr, s.values[k - 1]);
    });
    const pair = (name, make) => {
      const C = class { constructor(k) { if (k !== key) illegal(); }
        get baseVal() { const s = AS(this, name + '.baseVal'); return s.base ?? (s.base = make(s, false)); }
        get animVal() { const s = AS(this, name + '.animVal'); return s.anim ?? (s.anim = make(s, true)); } };
      Object.defineProperty(C, 'name', { value: name });
      return animated[name] = C;
    };
    pair('SVGAnimatedLength', (s, ro) => newLength(boundLength(s.el, s.attr, s.dflt === '' ? '0' : s.dflt, ro)));
    pair('SVGAnimatedAngle', (s, ro) => mk(SVGAngle, angles, { readonly: ro,
      read() { const t = s.el.getAttribute(s.attr); return (t !== null && angleOf(t)) || { n: 0, u: '', t: 1 }; },
      write(n, unit) { s.el.setAttribute(s.attr, fmt(n) + unit.u); } }));
    pair('SVGAnimatedRect', (s, ro) => {
      // A DOMRect whose members read the attribute; the base value's also write it.
      const r = Object.create(globalThis.DOMRect.prototype);
      const now = () => { const v = numsOf(s.el.getAttribute(s.attr) ?? ''); return v && v.length === 4 ? v : [0, 0, 0, 0]; };
      ['x', 'y', 'width', 'height'].forEach((k, i) => Object.defineProperty(r, k, { enumerable: true, configurable: true,
        get() { return now()[i]; },
        set(v) { if (ro) noMod('SVGRect.' + k); const c = now(); c[i] = float(v, 'SVGRect.' + k); s.el.setAttribute(s.attr, c.map(fmt).join(' ')); } }));
      return r;
    });
    pair('SVGAnimatedNumberList', (s, ro) => numberList.make(s.el, s.attr, ro));
    pair('SVGAnimatedLengthList', (s, ro) => lengthList.make(s.el, s.attr, ro));
    pair('SVGAnimatedTransformList', (s, ro) => transformList.make(s.el, s.attr, ro));
    pair('SVGAnimatedPreserveAspectRatio', (s, ro) => mk(SVGPreserveAspectRatio, ratios, { el: s.el, readonly: ro }));
    const kinds = { L: 'SVGAnimatedLength', N: 'SVGAnimatedNumber', I: 'SVGAnimatedInteger', B: 'SVGAnimatedBoolean', S: 'SVGAnimatedString',
      E: 'SVGAnimatedEnumeration', R: 'SVGAnimatedRect', P: 'SVGAnimatedPreserveAspectRatio', A: 'SVGAnimatedAngle',
      LL: 'SVGAnimatedLengthList', NL: 'SVGAnimatedNumberList', TL: 'SVGAnimatedTransformList' };

    // ---- the element interfaces ---------------------------------------------------------------
    // [SameObject]: one object for each element and property.
    const reflected = new WeakMap();
    const cached = (el, prop, make) => { let m = reflected.get(el); if (!m) reflected.set(el, m = new Map()); let v = m.get(prop); if (!v) m.set(prop, v = make()); return v; };
    const reflect = (C, name, entry) => {
      const [prop, kind, attr0, dflt0] = entry.split(':');
      const e = /^E\(([^)]*)\)([0-9]+)$/.exec(kind);
      const attr = attr0 || prop, dflt = dflt0 ?? '';
      const make = el => {
        if (kind === 'SL') return stringList.make(el, attr, false);
        if (kind === 'PL') return pointList.make(el, attr, prop === 'animatedPoints');
        const pairPart = /^[NI][12]$/.test(kind) ? Number(kind[1]) : 0;
        const base = e ? 'E' : pairPart ? kind[0] : kind;
        return mk(animated[kinds[base]], anims, { el, attr, dflt: e ? Number(e[2]) : dflt, values: e ? e[1].split(',') : null, part: pairPart, base: undefined, anim: undefined });
      };
      Object.defineProperty(C.prototype, prop, { enumerable: true, configurable: true, get() {
        if (!(this instanceof C)) throw new TypeError(`Illegal invocation: ${name}.${prop}`);
        return cached(this, prop, () => make(this));
      } });
    };
    for (const name in svgSpec) {
      const [parent, tags, attrs] = svgSpec[name];
      const P = classes[parent];
      const C = class extends P { constructor() { illegal(); } };
      Object.defineProperty(C, 'name', { value: name });
      setTag(C, name);
      for (const entry of attrs.split(' ')) if (entry !== '') reflect(C, name, entry);
      classes[name] = C;
      for (const tag of tags.split(' ')) if (tag !== '') byTag[tag] = C;
    }
    // SVGElement's own members (SVG 2 §4.5).
    Object.defineProperty(SVGElement.prototype, 'className', { enumerable: true, configurable: true, get() {
      return cached(this, 'className', () => mk(animated.SVGAnimatedString, anims, { el: this, attr: 'class', dflt: '' }));
    } });
    const outerSvg = el => { for (let p = el.parentNode; p; p = p.parentNode) if (p.namespaceURI === SVG_NS && p.localName === 'svg') return p; return null; };
    Object.defineProperty(SVGElement.prototype, 'ownerSVGElement', { enumerable: true, configurable: true, get() { return outerSvg(this); } });
    Object.defineProperty(SVGElement.prototype, 'viewportElement', { enumerable: true, configurable: true, get() { return outerSvg(this); } });
    // SVGSVGElement's factories (SVG 2 §5.1.x).
    const S = classes.SVGSVGElement.prototype;
    define(S, 'createSVGNumber', function createSVGNumber() { return newNumber(0); });
    define(S, 'createSVGLength', function createSVGLength() { return newLength(detachedLength({ n: 0, u: '', t: 1 })); });
    define(S, 'createSVGAngle', function createSVGAngle() { return mk(SVGAngle, angles, detachedAngle()); });
    define(S, 'createSVGPoint', function createSVGPoint() { return new globalThis.DOMPoint(0, 0); });
    define(S, 'createSVGMatrix', function createSVGMatrix() { return domMatrix([1, 0, 0, 1, 0, 0]); });
    define(S, 'createSVGRect', function createSVGRect() { return new globalThis.DOMRect(0, 0, 0, 0); });
    define(S, 'createSVGTransform', function createSVGTransform() { return newTransform('matrix', [1, 0, 0, 1, 0, 0]); });
    define(S, 'createSVGTransformFromMatrix', function createSVGTransformFromMatrix(matrix = undefined) { return newTransform('matrix', matrix2D(matrix, 'createSVGTransformFromMatrix')); });
    define(S, 'getElementById', function getElementById(id) { need(1, arguments.length, "Failed to execute 'getElementById' on 'SVGSVGElement'"); const e = this.ownerDocument.getElementById(String(id)); return e && this.contains(e) && e !== this ? e : null; });
    for (const k of ['createSVGNumber', 'createSVGLength', 'createSVGAngle', 'createSVGPoint', 'createSVGMatrix', 'createSVGRect', 'createSVGTransform', 'createSVGTransformFromMatrix', 'getElementById'])
      Object.defineProperty(S, k, { ...Object.getOwnPropertyDescriptor(S, k), enumerable: true });
    // The value interfaces and their constants.
    class SVGUnitTypes { constructor() { illegal(); } }
    Object.assign(classes, { SVGNumber, SVGLength, SVGAngle, SVGTransform, SVGPreserveAspectRatio, SVGUnitTypes,
      SVGNumberList: numberList.List, SVGLengthList: lengthList.List, SVGStringList: stringList.List, SVGPointList: pointList.List,
      SVGTransformList: transformList.List }, animated);
    for (const name of svgValueNames) setTag(classes[name], name);
    for (const name in svgConsts) {
      const table = {};
      for (const group of svgConsts[name].split('|')) group.split(' ').forEach((k, i) => { table[k] = i; });
      consts(classes[name], table); consts(classes[name].prototype, table);
    }
    // WebIDL §3.7: the attributes and operations of an interface are enumerable.
    for (const name in classes) {
      if (name === 'SVGElement') continue;
      const P = classes[name].prototype;
      for (const k of Object.getOwnPropertyNames(P)) {
        if (k === 'constructor') continue;
        const d = Object.getOwnPropertyDescriptor(P, k);
        if (d.configurable && !d.enumerable) Object.defineProperty(P, k, { ...d, enumerable: true });
      }
    }
    return { classes, byTag };
  };
  for (const name of [...Object.keys(svgSpec), ...svgValueNames]) lazy(name, () => svgDom().classes[name]);
  lazy('SVGPoint', () => globalThis.DOMPoint); lazy('SVGRect', () => globalThis.DOMRect); lazy('SVGMatrix', () => globalThis.DOMMatrix);
  // ==== end SVG DOM =============================================================================

  // ---- Web Storage (HTML §12.2): localStorage, sessionStorage, StorageEvent ----------------
  // The areas, their partition by origin and the quota are Lean's (Net/Storage.lean, web_api
  // ops 80 to 85): the origin is the engine's, never an argument, and an opaque origin gets
  // SecurityError. In memory for the session; nothing is written to disk. This is the WebIDL
  // surface: a legacy platform object's named properties (WebIDL §3.9), as a Proxy.
  // A string that is not well-formed (a lone surrogate) or holds U+0001 crosses the boundary
  // escaped (U+0001 and four hex digits a code unit), so distinct keys stay distinct there.
  const stEnc = x => {
    const s = String(x);
    if (s.indexOf('\u0001') < 0 && typeof s.isWellFormed === 'function' && s.isWellFormed()) return s;
    let out = '';
    for (let i = 0; i < s.length; i++) {
      const c = s.charCodeAt(i);
      out += c === 1 || (c >= 0xD800 && c <= 0xDFFF) ? '\u0001' + (c + 0x10000).toString(16).slice(1) : s[i];
    }
    return out;
  };
  const stDec = s => {
    if (s.indexOf('\u0001') < 0) return s;
    const u = [];
    for (let i = 0; i < s.length; i++) {
      if (s.charCodeAt(i) === 1) { u.push(parseInt(s.slice(i + 1, i + 5), 16)); i += 4; } else u.push(s.charCodeAt(i));
    }
    let out = '';
    for (let i = 0; i < u.length; i += 1024) out += String.fromCharCode(...u.slice(i, i + 1024));
    return out;
  };
  let StorageC;
  const storageKind = new WeakMap(), storageAreas = [undefined, undefined];
  // WebIDL §2.8.2 QuotaExceededError: a DOMException that can say the quota and the amount asked for.
  let QuotaErrorC;
  const quotaErrors = new WeakMap();
  const makeQuotaError = () => {
    if (QuotaErrorC) return QuotaErrorC;
    const amount = (v, member) => {
      if (v === undefined || v === null) return null;
      const x = Number(v);
      if (!Number.isFinite(x)) throw new TypeError(`Failed to construct 'QuotaExceededError': member ${member} is not a finite number`);
      if (x < 0) throw new RangeError(`Failed to construct 'QuotaExceededError': member ${member} is negative`);
      return x;
    };
    class QuotaExceededError extends DOMException {
      constructor(message = '', options = undefined) {
        super(message, 'QuotaExceededError');
        const d = dict(options, "Failed to construct 'QuotaExceededError'");
        const quota = amount(d.quota, 'quota'), requested = amount(d.requested, 'requested');
        if (quota !== null && requested !== null && requested < quota) throw new RangeError("Failed to construct 'QuotaExceededError': requested is less than quota");
        quotaErrors.set(this, { quota, requested });
      }
      get quota() { return brand(quotaErrors, this, 'QuotaExceededError.quota').quota; }
      get requested() { return brand(quotaErrors, this, 'QuotaExceededError.requested').requested; }
    }
    setTag(QuotaExceededError, 'QuotaExceededError');
    return QuotaErrorC = QuotaExceededError;
  };
  lazy('QuotaExceededError', makeQuotaError);
  const storageErr = (r, what) => {
    if (r === -27) throw new (makeQuotaError())(`Failed to execute '${what}' on 'Storage': the quota has been exceeded.`);
    if (r === -32) throw new DOMException('Storage is not available to this origin.', 'SecurityError');
    throw new TypeError(`Failed to execute '${what}' on 'Storage'`);
  };
  // One op on an area: a string, or null for "no such item".
  const storageCall = (kind, op, args, what) => {
    const r = apiCall(op, [kind, ...args]);
    if (typeof r === 'string') return r;
    return r === null || r === -1 ? null : storageErr(r, what);
  };
  // HTML §12.2.1 "broadcast": a change is told to every other Document of the origin that
  // holds the area. In this realm those are the page's window and its same-origin frames'
  // windows, but for the window of the script that made the change. A page with no frame
  // target (frameTargets is empty) pays one size check: the old value is read only for them.
  const storageMutate = (kind, key, value, op, args, what) => {
    if (frameTargets.size === 0) { storageCall(kind, op, args, what); return; }
    const read = k => { const v = apiCall(82, [kind, k]); return typeof v === 'string' ? stDec(v) : null; };
    const had = key === null ? Number(apiCall(80, [kind])) > 0 : read(stEnc(key));
    storageCall(kind, op, args, what);
    const now = key === null ? null : value;
    if (key === null ? !had : had === now) return;
    const own = windowOfScript(), from = scriptDocument !== null && scriptDocument !== document ? docURL(nodeId(scriptDocument)) : href;
    const tell = (target, doc) => {
      if (target === own) return;
      setTimeout(() => {
        const e = new globalThis.StorageEvent('storage', { key, oldValue: key === null ? null : had, newValue: now, url: from, storageArea: storageAreas[kind] });
        state(e).trusted = true;
        const before = scriptDocument;
        scriptDocument = doc > 0 ? wrap(doc) : null;
        try { dispatch(target, e); } finally { scriptDocument = before; }
      }, 0);
    };
    tell(window, 0);
    for (const [doc, target] of frameTargets) if (info(doc, 12) >= 0) tell(target, doc);
  };
  const storageNeed = (n, have, what) => { if (have < n) throw new TypeError(`Failed to execute '${what}' on 'Storage': ${n} argument${n > 1 ? 's' : ''} required, but only ${have} present.`); };
  const makeStorage = () => {
    if (StorageC) return StorageC;
    const K = (o, what) => { const k = storageKind.get(o); if (k === undefined) throw new TypeError('Illegal invocation: Storage.' + what); return k; };
    class Storage {
      constructor() { throw new TypeError('Illegal constructor'); }
      get length() { return Number(storageCall(K(this, 'length'), 80, [], 'length')); }
      key(index) {
        storageNeed(1, arguments.length, 'key');
        const k = storageCall(K(this, 'key'), 81, [index >>> 0], 'key');
        return k === null ? null : stDec(k);
      }
      getItem(key) {
        storageNeed(1, arguments.length, 'getItem');
        const v = storageCall(K(this, 'getItem'), 82, [stEnc(key)], 'getItem');
        return v === null ? null : stDec(v);
      }
      setItem(key, value) {
        storageNeed(2, arguments.length, 'setItem');
        const kind = K(this, 'setItem'), k = stEnc(key), v = stEnc(value);
        storageMutate(kind, String(key), String(value), 83, [k, v], 'setItem');
      }
      removeItem(key) {
        storageNeed(1, arguments.length, 'removeItem');
        storageMutate(K(this, 'removeItem'), String(key), null, 84, [stEnc(key)], 'removeItem');
      }
      clear() { storageMutate(K(this, 'clear'), null, null, 85, [], 'clear'); }
    }
    for (const k of ['length', 'key', 'getItem', 'setItem', 'removeItem', 'clear'])
      Object.defineProperty(Storage.prototype, k, { ...Object.getOwnPropertyDescriptor(Storage.prototype, k), enumerable: true });
    setTag(Storage, 'Storage');
    return StorageC = Storage;
  };
  // The area object of a kind (0 local, 1 session), made once; undefined on an engine
  // without the ops, SecurityError for an opaque origin.
  const storageArea = kind => {
    if (storageAreas[kind]) return storageAreas[kind];
    const probe = apiCall(80, [kind]);
    if (probe === -2) return undefined;
    if (typeof probe !== 'string') storageErr(probe, 'length');
    const Storage = makeStorage(), target = Object.create(Storage.prototype);
    const item = p => { const v = apiCall(82, [kind, stEnc(p)]); return typeof v === 'string' ? stDec(v) : undefined; };
    const named = (t, p) => typeof p === 'string' && !(p in t);
    const proxy = new Proxy(target, {
      get(t, p, r) { return named(t, p) ? item(p) : Reflect.get(t, p, r); },
      set(t, p, v, r) {
        if (typeof p === 'string' && r === proxy) { const k = stEnc(p), x = stEnc(v); storageMutate(kind, p, String(v), 83, [k, x], 'setItem'); return true; }
        return Reflect.set(t, p, v, r);
      },
      defineProperty(t, p, desc) {
        if (typeof p !== 'string') return Reflect.defineProperty(t, p, desc);
        if (!('value' in desc) && !('writable' in desc)) return false;
        const k = stEnc(p), x = stEnc(desc.value);
        storageMutate(kind, p, String(desc.value), 83, [k, x], 'setItem');
        return true;
      },
      deleteProperty(t, p) {
        if (named(t, p) && item(p) !== undefined) { storageMutate(kind, p, null, 84, [stEnc(p)], 'removeItem'); return true; }
        return Reflect.deleteProperty(t, p);
      },
      has(t, p) { return Reflect.has(t, p) || (typeof p === 'string' && item(p) !== undefined); },
      ownKeys(t) {
        const n = Number(storageCall(kind, 80, [], 'length')), keys = [];
        for (let i = 0; i < n; i++) { const k = storageCall(kind, 81, [i], 'key'); if (k !== null) { const d = stDec(k); if (!(d in t)) keys.push(d); } }
        return [...keys, ...Reflect.ownKeys(t)];
      },
      getOwnPropertyDescriptor(t, p) {
        if (named(t, p)) { const v = item(p); if (v !== undefined) return { value: v, writable: true, enumerable: true, configurable: true }; }
        return Reflect.getOwnPropertyDescriptor(t, p);
      },
    });
    storageKind.set(proxy, kind);
    return storageAreas[kind] = proxy;
  };
  lazy('Storage', () => (apiCall(80, [0]) === -2 ? undefined : makeStorage()));
  lazy('localStorage', () => storageArea(0));
  lazy('sessionStorage', () => storageArea(1));
  lazy('StorageEvent', () => {
    const nullable = v => v === undefined || v === null ? null : String(v);
    const area = v => {
      if (v === undefined || v === null) return null;
      if (!storageKind.has(v)) throw new TypeError("Failed to construct 'StorageEvent': member storageArea is not of type 'Storage'.");
      return v;
    };
    class StorageEvent extends Event {
      constructor(type, init = undefined) {
        super(type, init);
        const s = state(this), d = initOf(init);
        s.key = nullable(d.key); s.oldValue = nullable(d.oldValue); s.newValue = nullable(d.newValue);
        s.url = d.url === undefined ? '' : usv(d.url); s.storageArea = area(d.storageArea);
      }
      initStorageEvent(type, bubbles = false, cancelable = false, key = null, oldValue = null, newValue = null, url = '', storageArea = null) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'initStorageEvent' on 'StorageEvent': 1 argument required, but only 0 present.");
        const s = state(this);
        if (s.dispatching) return;
        const a = area(storageArea);
        this.initEvent(type, bubbles, cancelable);
        s.key = nullable(key); s.oldValue = nullable(oldValue); s.newValue = nullable(newValue); s.url = usv(url); s.storageArea = a;
      }
    }
    getters(StorageEvent, ['key', 'oldValue', 'newValue', 'url', 'storageArea']);
    setTag(StorageEvent, 'StorageEvent');
    return StorageEvent;
  });
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
    // File API §8.3: blob URLs. The store, its bounds and who may read a URL (its own origin
    // only) are Lean's (Net/BlobUrls.lean, web_api ops 90 and 91); a request for one is
    // answered in Lean (Net/PageFetch.lean blobStep).
    if (apiCall(91, ['']) !== -2) {
      define(URL, 'createObjectURL', function createObjectURL(blob) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'createObjectURL' on 'URL': 1 argument required, but only 0 present.");
        const b = blobs.get(blob);
        if (!b) throw new TypeError("Failed to execute 'createObjectURL' on 'URL': parameter 1 is not of type 'Blob'.");
        const r = apiCall(90, [b.type, b.bytes]);
        if (typeof r !== 'string') throw new DOMException("Failed to execute 'createObjectURL' on 'URL': too many blob URLs, or no entropy", 'QuotaExceededError');
        return r;
      });
      define(URL, 'revokeObjectURL', function revokeObjectURL(url) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'revokeObjectURL' on 'URL': 1 argument required, but only 0 present.");
        apiCall(91, [usv(url)]);
      });
    }
    setTag(URL, 'URL');
    return URL;
  });
  // ---- URL Pattern Standard: URLPattern ---------------------------------------------------
  // The engine compiles and matches (n.urlPattern: L4Factoidal.WHATWG.URLPattern, in Lean); this
  // class holds the record it answers. An engine without the native has no URLPattern.
  lazy('URLPattern', () => {
    if (typeof n.urlPattern !== 'function') return undefined;
    const patterns = new WeakMap();
    const st = o => brand(patterns, o, 'URLPattern');
    class URLPattern {
      // WebIDL overloads: (input, baseURL, options) and (input, options)
      constructor(input = {}, baseURL = undefined, options = undefined) {
        let base, opts;
        if (arguments.length >= 3) { base = usv(baseURL); opts = options; }
        else if (arguments.length === 2 && baseURL !== undefined && baseURL !== null && typeof baseURL !== 'object' && typeof baseURL !== 'function') base = usv(baseURL);
        else opts = baseURL;
        const o = dict(opts, "Failed to construct 'URLPattern'");
        patterns.set(this, n.urlPattern(0, input, base, !!o.ignoreCase));
      }
      test(input = {}, baseURL = undefined) { return n.urlPattern(1, st(this), input, baseURL === undefined ? undefined : usv(baseURL)) !== null; }
      exec(input = {}, baseURL = undefined) { return n.urlPattern(1, st(this), input, baseURL === undefined ? undefined : usv(baseURL)); }
      get hasRegExpGroups() { return st(this).hasRegExpGroups; }
    }
    for (const k of ['protocol', 'username', 'password', 'hostname', 'port', 'pathname', 'search', 'hash'])
      Object.defineProperty(URLPattern.prototype, k, { get() { return st(this)[k]; }, enumerable: true, configurable: true });
    setTag(URLPattern, 'URLPattern');
    return URLPattern;
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
          const g = normalize('get key length', derivedKeyType, 'g:');
          const args = ['deriveKey', 'baseKey', String(k.handle), 'extractable', extractable ? '1' : '0', ...usagePairs(us), ...a.pairs, ...t.pairs, ...g.pairs];
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

  // ==== frames (shadowframes) ==========================================================
  // A same-origin frame's document is in this realm's arena and its scripts run here
  // (Hosts.Page.Session.loadFrameP): while one runs, `addEventListener` on the window
  // registers on that frame's own window target, its uncaught errors go there, and its
  // `load` fires there before the iframe's (HTML §4.8.5 "iframe load event steps").
  // node_info 11 answers a frame's document only for the same origin (HTML.Frames).
  const frameTargets = new Map();
  const frameTarget = doc => { let t = frameTargets.get(doc); if (!t) { t = new EventTarget(); frameTargets.set(doc, t); } return t; };
  windowOfScript = () => scriptDocument ? frameTarget(nodeId(scriptDocument)) : window;
  frameLoad = el => { const d = info(el, 11), t = d >= 0 ? frameTargets.get(d) : undefined; if (t) { const e = new Event('load'); state(e).trusted = true; dispatch(t, e); } };
  for (const k of ['addEventListener', 'removeEventListener'])
    define(Window.prototype, k, function (...a) {
      // a frame's window (`frame.contentWindow.addEventListener`): that frame's target
      const cell = this == null ? undefined : frameOfWindow.get(this);
      return EventTarget.prototype[k].apply(cell ? frameTarget(cell.doc) : (this === window || this == null) && scriptDocument ? windowOfScript() : this, a);
    });
  // The window's event handler attributes too: `onmessage = f` in a frame's script is that
  // frame's window's handler, not the page's (it would replace the page's own).
  // They are own properties of the window: the members of a [Global] interface are on the
  // global object itself (Web IDL §3.7.6), so `window.hasOwnProperty('onload')` holds.
  for (const name of handlerNames) {
    const of = t => ((t === window || t == null) && scriptDocument ? windowOfScript() : t);
    delete Window.prototype['on' + name];
    Object.defineProperty(globalThis, 'on' + name, { get() { return handlerOf(of(this), name); },
      set(f) { setHandler(of(this), name, f); }, configurable: true, enumerable: true });
  }
  // document.open, write, writeln and close on a frame's document (HTML §8.4.3, §8.4.4). The
  // markup written since open() is parsed by Lean when the document is closed: the frame's
  // element gets the document the HTML parser makes of it (create_node kind 15, Hosts.Dom
  // frameWrite), and this Document object and the frame's window stay the frame's. Scripts in
  // the markup written do not run, and the page's own document is not rewritten: both are
  // refused or left out, not imitated.
  const written = new WeakMap();
  const writtenFrame = (d, what) => {
    const id = nodeId(d), el = id === 0 ? -1 : info(id, 12);
    if (el < 0) throw new DOMException(`Failed to execute '${what}' on 'Document': only a frame's document can be written in this build`, 'NotSupportedError');
    return el;
  };
  define(Document.prototype, 'open', function open() { writtenFrame(this, 'open'); written.set(this, ''); return this; });
  const docWrite = (d, text, what) => { writtenFrame(d, what); written.set(d, (written.get(d) ?? '') + text.map(String).join('')); };
  define(Document.prototype, 'write', function write(...text) { docWrite(this, text, 'write'); });
  define(Document.prototype, 'writeln', function writeln(...text) { docWrite(this, [...text, '\n'], 'writeln'); });
  define(Document.prototype, 'close', function close() {
    if (!written.has(this)) return;
    const el = writtenFrame(this, 'close'), old = nodeId(this), markup = written.get(this);
    written.delete(this);
    const fresh = chk(n.create(15, el + '\u0000' + markup));
    if (typeof fresh !== 'number' || fresh < 0) return;
    wrappers.delete(old); ids.set(this, fresh); wrappers.set(fresh, this);
    const cell = frameCells.get(old);
    if (cell) { cell.doc = fresh; frameWindows.set(fresh, frameWindows.get(old)); frameCells.set(fresh, cell); }
    const target = frameTargets.get(old);
    if (target) frameTargets.set(fresh, target);
    setTimeout(() => { const frame = wrap(el); if (frame && info(el, 11) === fresh) { frameLoad(el); fire(frame, 'load'); } }, 0);
  });
  // ==== end frames =====================================================================

  // ==== shadowframes: frames, the sandbox and postMessage ===============================
  // HTML §4.8.5, §7.1.5, §9.3. The decisions are Lean's (L4Factoidal.HTML.Frames through
  // Hosts.Dom): node_info 11 answers a frame's document only to a document of the same
  // origin, node_info 29 a frame's sandbox bits, node_query 32 the postMessage origin check.
  // An engine without them answers -2 to node_info 29 on an iframe: then postMessage is
  // the old stub.
  const frameEngine = () => shadowEngine();
  // HTML §4.8.5: `sandbox` is a DOMTokenList whose supported tokens are the keywords.
  const sandboxLists = new WeakMap();
  const sandboxTokens = ['allow-downloads', 'allow-forms', 'allow-modals', 'allow-orientation-lock', 'allow-pointer-lock',
    'allow-popups', 'allow-popups-to-escape-sandbox', 'allow-presentation', 'allow-same-origin', 'allow-scripts',
    'allow-top-navigation', 'allow-top-navigation-by-user-activation', 'allow-top-navigation-to-custom-protocols'];
  Object.defineProperty(named.HTMLIFrameElement.prototype, 'sandbox', {
    get() {
      let l = sandboxLists.get(this);
      if (!l) { sandboxLists.set(this, l = tokenList(this, 'sandbox')); Object.defineProperty(l, 'supports', { value: t => sandboxTokens.includes(String(t).toLowerCase()) }); }
      return l;
    },
    set(v) { this.setAttribute('sandbox', String(v)); }, configurable: true, enumerable: true });
  reflectString(named.HTMLIFrameElement, ['referrerPolicy', 'loading']);
  // A frame whose document this realm may not reach: a cross-origin WindowProxy (HTML
  // §7.2.3.x), with only postMessage, location assignment and the window names.
  const opaqueWindows = new Map();
  const opaqueWindow = el => {
    let w = opaqueWindows.get(el);
    if (w) return w;
    w = Object.freeze({
      postMessage(message, targetOrigin, transfer) { postAcross(el, message, targetOrigin); },
      get window() { return w; }, get self() { return w; }, get frames() { return w; },
      get parent() { return window; }, get top() { return window; }, get opener() { return null; },
      get closed() { return false; }, get length() { return 0; },
      get location() { return { set href(v) { wrap(el).setAttribute('src', String(v)); }, replace(v) { wrap(el).setAttribute('src', String(v)); } }; },
      set location(v) { wrap(el).setAttribute('src', String(v)); },
      close() {}, focus() {}, blur() {},
    });
    opaqueWindows.set(el, w);
    return w;
  };
  if (frameEngine()) Object.defineProperty(named.HTMLIFrameElement.prototype, 'contentWindow', { get() {
    const id = nodeId(this), d = info(id, 11);
    if (d >= 0) return frameWindow(d);
    return (info(id, 29) & 64) ? opaqueWindow(id) : null;
  }, configurable: true });
  // HTML §4.10.21.3 step 3: a form of a document with the sandboxed forms flag does not
  // submit.
  function formsSandboxed(form) {
    if (!frameEngine()) return false;
    const doc = info(nodeId(form), 7), el = doc === 0 ? -1 : info(doc, 12);
    return el >= 0 && (info(el, 29) & 4) === 0;
  }
  // HTML §9.3.3 "window post message steps": the target origin check is Lean's (node_query
  // 32: "1 origin" to deliver with the source's serialized origin, "0 origin" not to, -12
  // a target origin that is not a URL); the message is cloned at once and delivered as a
  // task (MessageEvent at the window).
  const postTo = (doc, message, targetOrigin, transfer) => {
    let options = targetOrigin;
    if (options === undefined || options === null || typeof options !== 'object') options = { targetOrigin: targetOrigin === undefined ? '/' : String(targetOrigin), transfer: transfer ?? [] };
    const to = options.targetOrigin === undefined ? '/' : String(options.targetOrigin);
    const r = doc < 0 ? '0 null' : n.query(doc, 32, to);
    if (r === -12) throw new DOMException(`Invalid target origin '${to}' in a call to 'postMessage'.`, 'SyntaxError');
    const ports = [...(options.transfer ?? [])].filter(p => p instanceof MessagePort);
    const data = globalThis.structuredClone(message);
    if (typeof r !== 'string' || !r.startsWith('1')) return;
    const origin = r.slice(2);
    // HTML §9.3.3 step 8.3: the source is the window of the script that posts. A frame's
    // script (running with its document as `document`) posts as its frame's window.
    const from = scriptDocument !== null && scriptDocument !== document ? frameWindow(nodeId(scriptDocument)) : window;
    setTimeout(() => {
      const e = new MessageEvent('message', { data, origin, source: from, ports });
      state(e).trusted = true;
      if (doc <= 0) { dispatch(window, e); return; }
      // To a frame's window: its listeners run with the frame's document as `document`.
      const before = scriptDocument;
      scriptDocument = wrap(doc);
      try { dispatch(frameTarget(doc), e); } finally { scriptDocument = before; }
    }, 0);
  };
  postFrame = postTo;
  // A message to a session of its own (a sandboxed frame, or from one to its parent):
  // Lean checks the origin and queues it (node_query 34); the host hands it to the other
  // session as a string, so the data must survive JSON (HTML.FrameSessions).
  const postAcross = (to, message, targetOrigin) => {
    let o = targetOrigin;
    if (o === undefined || o === null || typeof o !== 'object') o = { targetOrigin: targetOrigin === undefined ? '/' : String(targetOrigin) };
    const t = o.targetOrigin === undefined ? '/' : String(o.targetOrigin);
    const data = JSON.stringify(globalThis.structuredClone(message)) ?? 'null';
    const r = n.query(to, 34, t + '\u0000' + data);
    if (r === -12) throw new DOMException(`Invalid target origin '${t}' in a call to 'postMessage'.`, 'SyntaxError');
  };
  // In a frame's own session (node_info 29 on the document: 128), the parent is a window
  // of another origin.
  let parentProxy;
  const frameSession = () => frameEngine() && (info(0, 29) & 128) !== 0;
  const parentWindow = () => parentProxy ?? (parentProxy = Object.freeze({
    postMessage(message, targetOrigin) { postAcross(WINDOW, message, targetOrigin); },
    get window() { return parentProxy; }, get self() { return parentProxy; }, get closed() { return false; },
    get parent() { return parentProxy; }, get top() { return parentProxy; }, get length() { return 1; },
    close() {}, focus() {}, blur() {} }));
  if (frameEngine()) {
    Object.defineProperty(globalThis, 'parent', { get: () => frameSession() ? parentWindow() : scriptDocument && scriptDocument !== document ? parentOfDoc(nodeId(scriptDocument)) : window, configurable: true });
    Object.defineProperty(globalThis, 'top', { get: () => frameSession() ? parentWindow() : window, configurable: true });
  }
  if (frameEngine()) def('postMessage', function postMessage(message, targetOrigin, transfer) {
    if (arguments.length < 1) throw new TypeError("Failed to execute 'postMessage' on 'Window': 1 argument required, but only 0 present.");
    // `postMessage(…)` in a frame's script is that frame's window's: it posts to the frame's
    // own window, where the frame's listeners are, not to the page's
    postTo(scriptDocument !== null && scriptDocument !== document ? nodeId(scriptDocument) : 0, message, targetOrigin, transfer);
  });
  // HTML §9.4 MessageChannel and MessagePort: two entangled ports in this realm; a message
  // waits in the port's queue until the port is started (start() or onmessage).
  class MessagePort extends EventTarget {
    constructor() { if (!portMaking) throw new TypeError('Illegal constructor'); super(); this._q = []; this._started = false; this._other = null; this._closed = false; }
    postMessage(message, transfer) {
      const data = globalThis.structuredClone(message), o = this._other;
      if (!o || o._closed || this._closed) return;
      o._q.push(data); if (o._started) o._flush();
    }
    start() { if (this._started) return; this._started = true; this._flush(); }
    close() { this._closed = true; if (this._other) this._other._other = null; this._other = null; }
    _flush() { setTimeout(() => { while (this._q.length && !this._closed) { const e = new MessageEvent('message', { data: this._q.shift() }); state(e).trusted = true; dispatch(this, e); } }, 0); }
    get onmessage() { return handlerOf(this, 'message'); }
    set onmessage(f) { setHandler(this, 'message', f); this.start(); }
    get onmessageerror() { return handlerOf(this, 'messageerror'); }
    set onmessageerror(f) { setHandler(this, 'messageerror', f); }
  }
  let portMaking = false;
  class MessageChannel {
    constructor() {
      portMaking = true; const a = new MessagePort(), b = new MessagePort(); portMaking = false;
      a._other = b; b._other = a;
      Object.defineProperty(this, 'port1', { value: a, enumerable: true }); Object.defineProperty(this, 'port2', { value: b, enumerable: true });
    }
  }
  if (frameEngine()) { def('MessageChannel', MessageChannel); def('MessagePort', MessagePort); }
  // HTML §7.2.2.3 "Named access on the Window object": an element with an id is a property
  // of the window when nothing else has that name. The window's named properties object is
  // a proxy in its prototype chain (WebIDL §3.7.4); the lookup is Lean's (node_query 5),
  // asked only for a name nothing else defines. Only on an engine whose property lookups
  // consult a proxy in a prototype chain (probed once; BubblePopJS does not yet).
  const protoProxies = (() => { try { const o = Object.create(new Proxy({}, { get: (t, p) => p === 'x' ? 1 : undefined, has: (t, p) => p === 'x' })); return o.x === 1 && ('x' in o) && typeof o.hasOwnProperty === 'undefined'; } catch { return false; } })();
  if (frameEngine() && protoProxies) {
    const named = name => { const r = n.query(0, 5, name); return typeof r === 'string' ? wrap(Number(r)) : null; };
    Object.setPrototypeOf(Window.prototype, new Proxy(EventTarget.prototype, {
      get(t, p, r) { if (typeof p !== 'string' || p in t) return Reflect.get(t, p, r); return named(p) ?? undefined; },
      has(t, p) { return Reflect.has(t, p) || (typeof p === 'string' && p !== '' && named(p) !== null); },
    }));
  }
  // ==== end shadowframes: frames ========================================================
  for (const [k, v] of Object.entries({ EventTarget, Event, CustomEvent, UIEvent, MouseEvent, KeyboardEvent, FocusEvent, ErrorEvent,
    WheelEvent, PointerEvent, DOMRect, DOMRectReadOnly, CompositionEvent, InputEvent, DragEvent, HashChangeEvent, MessageEvent, StorageEvent, DeviceMotionEvent,
    DeviceOrientationEvent, BeforeUnloadEvent, TextEvent,
    PromiseRejectionEvent, Node, Element, HTMLElement, HTMLUnknownElement, SVGElement, MathMLElement, CharacterData, Text, CDATASection, Comment,
    ProcessingInstruction, DocumentType, DocumentFragment, Document, HTMLDocument, XMLDocument, DOMImplementation, NodeList, HTMLCollection, NamedNodeMap, Attr, DOMParser, SubmitEvent,
    DOMTokenList, DOMException, AbortController, AbortSignal, Window, MutationObserver, MutationRecord, ...named })) def(k, v);
  if (shadowEngine()) def('ShadowRoot', ShadowRoot);

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
  // `declarative`: the fragment parsing steps with declarative shadow roots allowed
  // (setHTMLUnsafe; createKind 14), else without (innerHTML; 13).
  const fragmentOf = (doc, ns, name, markup, declarative = false) => {
    const f = chk(n.create((declarative ? 14 : 13) + 16 * doc, (ns ?? '') + '\u0000' + name + '\u0000' + markup));
    scanHandlers(f, false);
    return f;
  };
  const contextOf = (ctx, doc) => (info(ctx, 0) !== 1 || (info(ctx, 8) === 1 && str(ctx, 0) === 'html'))
    ? [HTML_NS, 'body'] : [str(ctx, 2), str(ctx, 0)];
  const setInner = (el, v, declarative = false) => {
    const id = nodeId(el), f = fragmentOf(info(id, 7), str(id, 2), str(id, 0), v === null ? '' : String(v), declarative);
    const target = htmlEl(id) && str(id, 0) === 'template' ? info(id, 9) : id;
    chk(n.setText(target, '')); chk(n.insert(target, f, -1));
  };
  // getHTML(options) (HTML §8.4): GetHTMLOptions read in WebIDL order; the serialization is
  // Lean's (node_query 15 with "g": DOM.Fragment.getHTML).
  const getHTMLOf = (node, options) => {
    if (options !== undefined && options !== null && typeof options !== 'object' && typeof options !== 'function')
      throw new TypeError("Failed to execute 'getHTML': The provided value is not of type 'GetHTMLOptions'.");
    const o = options ?? {};
    const ssr = !!o.serializableShadowRoots, roots = o.shadowRoots === undefined ? [] : [...o.shadowRoots];
    const ids = roots.map(r => { if (!(r instanceof globalThis.ShadowRoot)) throw new TypeError("Failed to execute 'getHTML': Failed to read the 'shadowRoots' property from 'GetHTMLOptions': Failed to convert value to 'ShadowRoot'."); return nodeId(r); });
    return chk(n.query(nodeId(node), 15, 'g' + (ssr ? '1' : '0') + ids.map(i => ' ' + i).join('')));
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
    setHTMLUnsafe: { value(html) { setInner(this, String(html), true); }, writable: true, configurable: true },
    getHTML: { value(options = undefined) { return getHTMLOf(this, options); }, writable: true, configurable: true },
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
    // up to Element, whose rows are the ARIA attributes (ARIAMixin) and `slot`
    for (let P = C; P && P !== Node && !reflected.has(P); P = Object.getPrototypeOf(P)) {
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
            // one host call: Lean decides and sets the content attribute (with no observer or
            // custom element to tell, and no URL, whose iframe src navigates); else the decision,
            // then setAttribute
            if (!observed.size && !ceActive && k !== 'u') { op(nodeId(this), 167, row + '\u0000' + reflectConv[k](v)); return; }
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
    createContextualFragment(fragment) {
      needArgs(arguments, 1, 'createContextualFragment');
      const f = Number(op(rid(this), 116, String(fragment)));
      scanHandlers(f, false);
      // its script elements are not "already started": they run when the fragment is inserted
      for (const k of elementsOf(f)) if (str(k, 0) === 'script') noteFreshScript(k);
      return wrap(f);
    }
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
    // Selection API "modify": the engine moves the focus (DOM.Editing.modifyFocus, op 178).
    modify(alter = '', direction = '', granularity = '') { n.query(0, 178, [alter, direction, granularity].map(String).join(' ')); },
    getComposedRanges() { const s = selState(); return s ? [new StaticRange({ startContainer: wrap(s.b[0]), startOffset: s.b[1], endContainer: wrap(s.b[2]), endOffset: s.b[3] })] : []; },
    toString() { const s = selState(); return s ? op(s.k, 111) : ''; },
  })) define(Selection.prototype, k, ['addRange', 'removeRange', 'removeAllRanges', 'empty', 'collapse', 'setPosition', 'collapseToStart',
    'collapseToEnd', 'extend', 'setBaseAndExtent', 'selectAllChildren', 'deleteFromDocument', 'modify'].includes(k) ? selChanging(f) : f);
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
  // ---- Editing (W3C Editing APIs draft): execCommand and the queryCommand methods ----------
  // The algorithms are the engine's (DOM.Editing, node_query ops 175 to 177); this is the
  // WebIDL glue. No method throws for a command name: an unknown command answers false or ''.
  const editQuery = (k, s) => { const r = n.query(0, k, s); return typeof r === 'string' ? r : ''; };
  // The focused text control (an input with a text selection, or a textarea), if any: a
  // command then edits its value and selection (DOM.Editing.textEdit, op 179).
  const miscEdit = ['stylewithcss', 'usecss', 'defaultparagraphseparator', 'selectall'];
  const editControl = () => {
    const el = document.activeElement;
    if (el === null || el === undefined || el === document.body) return null;
    if (el.localName !== 'textarea' && el.localName !== 'input') return null;
    try { return typeof el.selectionStart === 'number' && typeof el.setSelectionRange === 'function' ? el : null; } catch { return null; }
  };
  const controlQuery = (el, command, value) => editQuery(179,
    [command, el.localName === 'textarea' ? '1' : '0', el.selectionStart, el.selectionEnd, value, el.value].join('\u0000'));
  // The document commands (styleWithCSS and the like) work from a text control only when
  // the control is in editable content.
  const controlInEditable = el => el.parentElement !== null && el.parentElement.isContentEditable === true;
  const controlCommand = (el, commandId, value) => {
    let command = String(commandId).toLowerCase(), text = String(value);
    if (miscEdit.includes(command) && command !== 'selectall') return null;
    if (command === 'inserthtml') { const t = document.createElement('template'); t.innerHTML = text; text = t.content.textContent; command = 'inserttext'; }
    const r = controlQuery(el, command, text);
    if (r === '') return false;
    const at = r.indexOf('\u0000'), [start, end, inputType] = r.slice(0, at).split(' '), next = r.slice(at + 1);
    if (next !== el.value) el.value = next;
    el.setSelectionRange(Number(start), Number(end));
    if (inputType !== '-') {
      const e = new InputEvent('input', { bubbles: true, cancelable: false, inputType, data: inputType === 'insertText' ? text : null });
      state(e).trusted = true;
      dispatch(el, e);
    }
    return true;
  };
  for (const [k, f] of Object.entries({
    execCommand(commandId, showUI = false, value = '') {
      needArgs(arguments, 1, 'execCommand');
      if (this !== document) return false;
      const control = editControl();
      if (control !== null) {
        const done = controlCommand(control, commandId, value);
        if (done !== null) return done;
        if (!controlInEditable(control)) return false;
      }
      const r = selChanging(() => editQuery(175, String(commandId) + '\u0000' + String(value)))().split('\u0000');
      if (r[0] !== '1') return false;
      if (r.length > 2) {
        // the `input` event of the command (the draft's step 7; no `beforeinput`, as browsers)
        const e = new InputEvent('input', { bubbles: true, cancelable: false, inputType: r[2], data: r.length > 3 ? r.slice(3).join('\u0000') : null });
        state(e).trusted = true;
        dispatch(wrap(Number(r[1])), e);
      }
      return true;
    },
    queryCommandEnabled(commandId) {
      needArgs(arguments, 1, 'queryCommandEnabled');
      if (this !== document) return false;
      const control = editControl();
      if (control !== null) {
        const command = String(commandId).toLowerCase();
        if (!miscEdit.includes(command) || command === 'selectall') return controlQuery(control, '?' + command, '') === '1';
        if (!controlInEditable(control)) return false;
      }
      return editQuery(176, 'e\u0000' + String(commandId)) === '1';
    },
    queryCommandIndeterm(commandId) { needArgs(arguments, 1, 'queryCommandIndeterm'); return this === document && editQuery(176, 'i\u0000' + String(commandId)) === '1'; },
    queryCommandState(commandId) { needArgs(arguments, 1, 'queryCommandState'); return this === document && editQuery(176, 's\u0000' + String(commandId)) === '1'; },
    queryCommandSupported(commandId) { needArgs(arguments, 1, 'queryCommandSupported'); return editQuery(176, 'u\u0000' + String(commandId)) === '1'; },
    queryCommandValue(commandId) { needArgs(arguments, 1, 'queryCommandValue'); return this === document ? editQuery(176, 'v\u0000' + String(commandId)) : ''; },
  })) define(Document.prototype, k, f);
  Object.defineProperty(Document.prototype, 'designMode', {
    get() { return this === document ? editQuery(177, 'd') : 'off'; },
    set(v) { v = String(v).toLowerCase(); if (this === document && (v === 'on' || v === 'off')) n.query(0, 177, v === 'on' ? 'd1' : 'd0'); },
    configurable: true, enumerable: true });
  // The page of a script session does not scroll (as window.scrollTo): nothing to bring into view.
  if (!('scrollIntoView' in Element.prototype)) define(Element.prototype, 'scrollIntoView', function scrollIntoView() {});
  if (!('dataTransfer' in InputEvent.prototype)) Object.defineProperty(InputEvent.prototype, 'dataTransfer', { get() { return null; }, configurable: true, enumerable: true });
  // Input Events §4.1.2: the ranges the engine gave a beforeinput of an editing command
  // (node numbers and offsets), or the StaticRanges of a script's init.
  if (!('getTargetRanges' in InputEvent.prototype)) define(InputEvent.prototype, 'getTargetRanges', function getTargetRanges() {
    return (state(this).ranges ?? []).map(r => Array.isArray(r)
      ? new StaticRange({ startContainer: wrap(r[0]), startOffset: r[1], endContainer: wrap(r[2]), endOffset: r[3] }) : r);
  });
  if (!('contentEditable' in HTMLElement.prototype)) Object.defineProperty(HTMLElement.prototype, 'contentEditable', {
    get() { const r = n.query(nodeId(this), 177, 'c'); return typeof r === 'string' ? r : 'inherit'; },
    set(v) {
      v = String(v).toLowerCase();
      if (v === 'inherit') this.removeAttribute('contenteditable');
      else if (v === 'true' || v === 'false' || v === 'plaintext-only') this.setAttribute('contenteditable', v);
      else throw new DOMException("The value provided ('" + v + "') is not one of 'true', 'false', 'plaintext-only', or 'inherit'.", 'SyntaxError');
    },
    configurable: true, enumerable: true });
  if (!('isContentEditable' in HTMLElement.prototype)) Object.defineProperty(HTMLElement.prototype, 'isContentEditable', {
    get() { return n.query(nodeId(this), 177, 'i') === '1'; }, configurable: true, enumerable: true });
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
  // The property names of Lean's computed style, once: the listed longhands (the layout
  // profile's first, in Lean's order), then the names that are answered for and not listed
  // (shorthands, legacy names): ComputedGeneric.namesText, node_query op 152. The value of the
  // k-th name is measure op 200 + k. An engine without op 152 has the names of op 20's answer.
  let computedNames = null, computedIndex = null;
  const namesOf = r => { const xs = r.split('\u0000'), out = []; for (let i = 0; i + 1 < xs.length; i += 2) out.push(xs[i]); return out; };
  const namesFor = el => {
    if (computedNames === null) {
      const all = n.query(0, 152, '');
      let listed, other = [];
      if (typeof all === 'string' && all !== '') { const parts = all.split('\u0001'); listed = parts[0].split('\u0000'); other = parts[1] ? parts[1].split('\u0000') : []; }
      else { const r = n.query(nodeId(el), 20, ''); if (typeof r !== 'string' || r === '') return []; listed = namesOf(r); }
      computedNames = listed;
      computedIndex = new Map(listed.concat(other).map((x, i) => [x, i]));
    }
    return computedNames;
  };
  const camel = name => name.replace(/-([a-z])/g, (m, c) => c.toUpperCase());
  const computedValue = (el, name) => {
    const id = nodeId(el);
    if (namesFor(el).length === 0) return '';
    const k = computedIndex.get(name);
    if (k === undefined) return '';
    if (name === 'width' || name === 'height') {
      const d = n.query(id, 200 + computedIndex.get('display'), '');
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
        return xs.length > 0 && (computedIndex.has(p) || computedIndex.has(cssName(p)));
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
  // scripts run, and a page can not add font faces here ----
  // showoff: the faces are those of the page's @font-face rules, from Lean (node_query op 23,
  // asked on first use): family, descriptors and status, "loaded" when the engine holds the
  // face for this page (the host fetched it because the page's text uses it), else
  // "unloaded". So nothing is loading and `ready` is resolved. load() and check() match the
  // families of a CSS font shorthand (§2.5, without weight and style, which this engine's
  // text does not have). An engine without op 23 answers no faces.
  const fontKey = {};
  let fontFaces;
  const facesNow = () => {
    if (fontFaces) return fontFaces;
    let list = [];
    try { const s = n.query(0, 23, ''); if (typeof s === 'string' && s !== '') list = JSON.parse(s); } catch { list = []; }
    return fontFaces = list.map(f => {
      const face = { family: f.family, style: f.style, weight: f.weight, stretch: 'normal', unicodeRange: f.unicodeRange,
        variant: 'normal', featureSettings: 'normal', display: 'auto', status: f.status };
      let loaded;
      Object.defineProperty(face, 'loaded', { get: () => loaded ??= (f.status === 'loaded' ? Promise.resolve(face)
        : Promise.reject(new DOMException('The font face was not loaded', 'NetworkError'))), enumerable: true });
      face.load = () => face.loaded;
      return Object.freeze(face);
    });
  };
  const faceRanges = face => face.unicodeRange.split(',').map(r => r.trim().replace(/^U\+/i, '').split('-').map(h => parseInt(h, 16)))
    .map(([lo, hi]) => [lo, hi ?? lo]);
  const matchingFaces = (font, text) => {
    const m = /(?:^|\s)[\d.]+(?:px|pt|pc|em|rem|ex|ch|%|vw|vh|vmin|vmax|in|cm|mm|q)(?:\/\S+)?\s+(.+)$/i.exec(String(font).trim());
    if (!m) throw new DOMException(`'${font}' is not a valid font`, 'SyntaxError');
    const names = m[1].split(',').map(x => x.trim().replace(/^(['"])(.*)\1$/, '$2').toLowerCase());
    const chars = [...String(text)].map(c => c.codePointAt(0));
    return facesNow().filter(face => names.includes(face.family.toLowerCase()) &&
      chars.some(c => faceRanges(face).some(([lo, hi]) => lo <= c && c <= hi)));
  };
  class FontFaceSet extends EventTarget {
    constructor(key) { if (key !== fontKey) throw new TypeError('Illegal constructor'); super(); }
    get status() { return 'loaded'; }
    get size() { return facesNow().length; }
    get ready() { return fontsReady; }
    check(font, text = ' ') { if (arguments.length < 1) throw new TypeError('check: 1 argument required');
      return matchingFaces(font, text).every(f => f.status === 'loaded'); }
    load(font, text = ' ') { if (arguments.length < 1) throw new TypeError('load: 1 argument required');
      try { return Promise.resolve(matchingFaces(font, text).filter(f => f.status === 'loaded')); } catch (e) { return Promise.reject(e); } }
    has(face) { return facesNow().includes(face); }
    add() { return this; }
    delete() { return false; }
    clear() {}
    forEach(f, self) { for (const face of facesNow()) f.call(self, face, face, this); }
    *entries() { for (const f of facesNow()) yield [f, f]; } *keys() { yield* facesNow(); } *values() { yield* facesNow(); }
  }
  define(FontFaceSet.prototype, Symbol.iterator, FontFaceSet.prototype.values);
  Object.defineProperty(FontFaceSet.prototype, Symbol.toStringTag, { value: 'FontFaceSet', configurable: true });
  addHandlers(FontFaceSet.prototype);
  const fontSet = new FontFaceSet(fontKey), fontsReady = Promise.resolve(fontSet);
  Object.defineProperty(Document.prototype, 'fonts', { get() { return fontSet; }, configurable: true, enumerable: true });
  def('FontFaceSet', FontFaceSet);
  // ---- CSSOM style sheets (CSSOM §6): document.styleSheets, a style element's sheet, the
  // rules and their text. The state of a sheet is its text: the text content of a style
  // element, or a string for a constructed sheet. Lean (CssSheet.sheetOp, node_query op 153)
  // reads the rules of a text and gives the text of a changed sheet; which rules are valid
  // and how they are written is decided there. An insertRule on a style element's sheet
  // writes the sheet's canonical text back as the element's text, so the cascade sees it.
  const sheetOp = (...parts) => { const r = n.query(0, 153, parts.join('\u0000')); return typeof r === 'string' ? r : ''; };
  const sheetState = new WeakMap(), ruleState = new WeakMap(), ruleLists = new WeakMap(), mediaLists = new WeakMap();
  const illegal = () => { throw new TypeError('Illegal constructor'); };
  class CSSRule { constructor() { illegal(); } }
  consts(CSSRule, { STYLE_RULE: 1, CHARSET_RULE: 2, IMPORT_RULE: 3, MEDIA_RULE: 4, FONT_FACE_RULE: 5, PAGE_RULE: 6, KEYFRAMES_RULE: 7,
    KEYFRAME_RULE: 8, MARGIN_RULE: 9, NAMESPACE_RULE: 10, COUNTER_STYLE_RULE: 11, SUPPORTS_RULE: 12, FONT_FEATURE_VALUES_RULE: 14 });
  class CSSGroupingRule extends CSSRule {}
  class CSSConditionRule extends CSSGroupingRule {}
  const ruleClasses = { Rule: CSSRule, GroupingRule: CSSGroupingRule, ConditionRule: CSSConditionRule };
  for (const [name, base] of [['Style', CSSGroupingRule], ['Media', CSSConditionRule], ['Supports', CSSConditionRule], ['Container', CSSConditionRule],
    ['LayerBlock', CSSGroupingRule], ['LayerStatement', CSSRule], ['Scope', CSSGroupingRule], ['StartingStyle', CSSGroupingRule],
    ['Import', CSSRule], ['Namespace', CSSRule], ['FontFace', CSSRule], ['Page', CSSGroupingRule], ['Property', CSSRule],
    ['CounterStyle', CSSRule], ['PositionTry', CSSRule], ['FontPaletteValues', CSSRule], ['ViewTransition', CSSRule],
    ['Keyframes', CSSRule], ['FontFeatureValues', CSSRule], ['Document', CSSConditionRule]])
    ruleClasses[name + 'Rule'] = ({ ['CSS' + name + 'Rule']: class extends base {} })['CSS' + name + 'Rule'];
  class CSSRuleList { constructor() { illegal(); } }
  class StyleSheet { constructor() { illegal(); } }
  class MediaList { constructor() { illegal(); } }
  class StyleSheetList { constructor() { illegal(); } }
  const sheetErr = name => new DOMException('The style sheet operation failed: ' + name, name);
  // A holder of rules (a sheet, or a group rule): `text()` and `write(t)` its rules' text.
  const rulesOf = holder => {
    const st = holder.st, text = st.text();
    if (st.rules && st.seen === text) return st.rules;
    const r = sheetOp('rules', text), old = st.rules || [];
    st.rules = r === '' ? [] : r.split('\u0001').map((row, i) => {
      const [kind, type, prelude, body, cssText] = row.split('\u0002');
      // the object of a rule that is as it was stays the same object
      const prev = old[i] && ruleState.get(old[i]);
      if (prev && prev.cssText === cssText) { prev.index = i; return old[i]; }
      const rule = Object.create((ruleClasses[kind + 'Rule'] || CSSRule).prototype);
      ruleState.set(rule, { kind, type: Number(type), prelude, body, cssText, index: i, holder });
      return rule;
    });
    st.seen = text;
    return st.rules;
  };
  const changed = (holder, answer) => {
    if (answer.charAt(0) === '\u0001') throw sheetErr(answer.slice(1));
    holder.st.write(answer.slice(1));
  };
  const ruleNow = rule => { const rs = ruleState.get(rule); if (!rs) throw new TypeError('Illegal invocation'); const xs = rulesOf(rs.holder); if (xs[rs.index] !== rule) rs.detached = true; return rs; };
  const insertInto = (holder, rule, index) => {
    const xs = rulesOf(holder), i = index >>> 0;
    if (i > xs.length) throw sheetErr('IndexSizeError');
    changed(holder, sheetOp('insert', holder.st.text(), String(rule), String(i)));
    return i;
  };
  const deleteFrom = (holder, index) => {
    const xs = rulesOf(holder), i = index >>> 0;
    if (i >= xs.length) throw sheetErr('IndexSizeError');
    changed(holder, sheetOp('delete', holder.st.text(), String(i)));
  };
  const ruleListOf = holder => {
    let l = ruleLists.get(holder);
    if (!l) {
      l = new Proxy(Object.create(CSSRuleList.prototype), {
        get(t, p) {
          if (p === 'length') return rulesOf(holder).length;
          if (p === 'item') return i => rulesOf(holder)[i >>> 0] ?? null;
          if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return rulesOf(holder)[Number(p)];
          return Reflect.get(t, p);
        },
        has(t, p) { return (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) ? Number(p) < rulesOf(holder).length : p === 'length' || p === 'item' || Reflect.has(t, p); },
        ownKeys(t) { return rulesOf(holder).map((x, i) => String(i)).concat(Reflect.ownKeys(t)); },
        getOwnPropertyDescriptor(t, p) {
          if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p) && Number(p) < rulesOf(holder).length)
            return { value: rulesOf(holder)[Number(p)], enumerable: true, configurable: true, writable: false };
          return Reflect.getOwnPropertyDescriptor(t, p);
        },
      });
      ruleLists.set(holder, l);
    }
    return l;
  };
  define(CSSRuleList.prototype, Symbol.iterator, function* () { for (let i = 0; i < this.length; i++) yield this[i]; });
  // A rule as a holder of the rules of its block, and of its declaration block.
  const groupHolder = rule => {
    const rs = ruleState.get(rule);
    if (!rs.group) rs.group = { st: {
      text: () => ruleNow(rule).body,
      // the group's new block replaces the rule in its parent: the rule's text with the new block
      write: t => { const r = ruleNow(rule), head = r.cssText.slice(0, r.cssText.indexOf('{')); const parent = r.holder;
        const all = rulesOf(parent).map((x, i) => i === r.index ? head + '{\n' + t + '\n}' : ruleState.get(x).cssText).join('\n');
        parent.st.write(all); const fresh = ruleState.get(rulesOf(parent)[r.index]); if (fresh) { ruleState.set(rule, Object.assign(rs, { body: fresh.body, cssText: fresh.cssText })); rulesOf(parent)[r.index] = rule; } },
    } };
    return rs.group;
  };
  const ruleStyle = rule => {
    const rs = ruleState.get(rule);
    if (!rs.style) rs.style = blockStyle(() => ruleNow(rule).body, nb => {
      const r = ruleNow(rule); if (r.detached) { r.body = nb; return; }
      const a = sheetOp('setbody', r.holder.st.text(), String(r.index), nb);
      if (a.charAt(0) === '\u0000') { r.holder.st.write(a.slice(1)); const fresh = ruleState.get(rulesOf(r.holder)[r.index]); Object.assign(rs, { body: fresh.body, cssText: fresh.cssText }); rulesOf(r.holder)[r.index] = rule; }
    });
    return rs.style;
  };
  for (const [k, f] of Object.entries({
    type() { return ruleNow(this).type; },
    cssText() { return ruleNow(this).cssText; },
    parentStyleSheet() { let h = ruleNow(this).holder; while (h.rule) h = ruleState.get(h.rule).holder; return h.sheet ?? null; },
    parentRule() { return ruleNow(this).holder.rule ?? null; },
  })) Object.defineProperty(CSSRule.prototype, k, { get: f, configurable: true, enumerable: true });
  Object.defineProperty(CSSRule.prototype, 'cssText', { get() { return ruleNow(this).cssText; }, set() {}, configurable: true, enumerable: true });
  Object.defineProperty(CSSGroupingRule.prototype, 'cssRules', { get() { const g = groupHolder(this); g.rule = this; return ruleListOf(g); }, configurable: true, enumerable: true });
  define(CSSGroupingRule.prototype, 'insertRule', function (rule, index = 0) { if (arguments.length < 1) throw new TypeError('insertRule: 1 argument required'); const g = groupHolder(this); g.rule = this; return insertInto(g, rule, index); });
  define(CSSGroupingRule.prototype, 'deleteRule', function (index) { if (arguments.length < 1) throw new TypeError('deleteRule: 1 argument required'); const g = groupHolder(this); g.rule = this; deleteFrom(g, index); });
  Object.defineProperty(CSSConditionRule.prototype, 'conditionText', { get() { return ruleNow(this).prelude; }, configurable: true, enumerable: true });
  Object.defineProperty(ruleClasses.StyleRule.prototype, 'selectorText', { get() { return ruleNow(this).prelude; },
    set(v) { const r = ruleNow(this); const a = sheetOp('setsel', r.holder.st.text(), String(r.index), String(v));
      if (a.charAt(0) === '\u0000') { r.holder.st.write(a.slice(1)); const fresh = ruleState.get(rulesOf(r.holder)[r.index]); Object.assign(r, { prelude: fresh.prelude, cssText: fresh.cssText }); rulesOf(r.holder)[r.index] = this; } },
    configurable: true, enumerable: true });
  for (const k of ['StyleRule', 'FontFaceRule', 'PageRule', 'PositionTryRule'])
    Object.defineProperty(ruleClasses[k].prototype, 'style', { get() { return ruleStyle(this); }, set(v) { ruleStyle(this).cssText = v; }, configurable: true, enumerable: true });
  const mediaListOf = (owner, get, set) => {
    let m = mediaLists.get(owner);
    if (!m) {
      m = Object.create(MediaList.prototype);
      const items = () => { const t = get(); return t === '' ? [] : t.split(',').map(x => x.trim()); };
      Object.defineProperties(m, {
        mediaText: { get, set: v => set(v === null ? '' : String(v)), enumerable: true, configurable: true },
        length: { get: () => items().length, enumerable: true, configurable: true },
        item: { value: i => items()[i >>> 0] ?? null, configurable: true, writable: true },
        appendMedium: { value: x => { const xs = items(); if (!xs.includes(String(x))) set(xs.concat(String(x)).join(', ')); }, configurable: true, writable: true },
        deleteMedium: { value: x => { const xs = items(); if (!xs.includes(String(x))) throw sheetErr('NotFoundError'); set(xs.filter(y => y !== String(x)).join(', ')); }, configurable: true, writable: true },
        toString: { value: () => get(), configurable: true, writable: true },
      });
      mediaLists.set(owner, m);
    }
    return m;
  };
  Object.defineProperty(ruleClasses.MediaRule.prototype, 'media', { get() { return mediaListOf(this, () => ruleNow(this).prelude, () => {}); }, configurable: true, enumerable: true });
  Object.defineProperty(ruleClasses.KeyframesRule.prototype, 'name', { get() { return ruleNow(this).prelude; }, configurable: true, enumerable: true });
  Object.defineProperty(ruleClasses.LayerBlockRule.prototype, 'name', { get() { return ruleNow(this).prelude; }, configurable: true, enumerable: true });
  Object.defineProperty(ruleClasses.ImportRule.prototype, 'href', { get() { const m = /^url\(\s*["']?([^"')]*)["']?\s*\)|^["']([^"']*)["']/.exec(ruleNow(this).prelude); return m ? (m[1] ?? m[2]) : ''; }, configurable: true, enumerable: true });
  // A sheet: of a style element (its text is the element's text), or constructed.
  const sheetOfText = (text, write, owner) => {
    const sheet = Object.create(CSSStyleSheet.prototype);
    const st = { text, write, owner, disabled: false, media: '' };
    sheetState.set(sheet, { st, sheet });
    return sheet;
  };
  const holderOf = sheet => { const h = sheetState.get(sheet); if (!h) throw new TypeError('Illegal invocation'); return h; };
  class CSSStyleSheet extends StyleSheet {
    constructor(options = {}) {
      let text = '';
      const sheet = sheetOfText(() => text, t => { text = t; }, null);
      const st = holderOf(sheet).st;
      st.constructed = true;
      if (options && options.media !== undefined) st.media = typeof options.media === 'string' ? options.media : String(options.media.mediaText ?? options.media);
      if (options && options.disabled) st.disabled = true;
      if (options && options.title !== undefined) st.title = String(options.title);
      return sheet;
    }
    get cssRules() { return ruleListOf(holderOf(this)); }
    get rules() { return ruleListOf(holderOf(this)); }
    get ownerRule() { return null; }
    insertRule(rule, index = 0) { if (arguments.length < 1) throw new TypeError('insertRule: 1 argument required'); return insertInto(holderOf(this), rule, index); }
    deleteRule(index) { if (arguments.length < 1) throw new TypeError('deleteRule: 1 argument required'); deleteFrom(holderOf(this), index); }
    addRule(selector = 'undefined', block = 'undefined', index = undefined) { const h = holderOf(this); insertInto(h, `${selector} { ${block} }`, index === undefined ? rulesOf(h).length : index); return -1; }
    removeRule(index = 0) { deleteFrom(holderOf(this), index); }
    replaceSync(text) { const h = holderOf(this); if (!h.st.constructed) throw sheetErr('NotAllowedError'); h.st.write(sheetOp('canon', String(text))); }
    replace(text) { try { this.replaceSync(text); return Promise.resolve(this); } catch (e) { return Promise.reject(e); } }
  }
  for (const [k, f] of Object.entries({
    type() { return 'text/css'; },
    href() { const o = holderOf(this).st.owner; return o && o.localName === 'link' ? o.href : null; },
    ownerNode() { return holderOf(this).st.owner; },
    parentStyleSheet() { return null; },
    title() { const st = holderOf(this).st; return st.owner ? (st.owner.getAttribute('title') || null) : (st.title ?? null); },
    media() { const st = holderOf(this).st; return mediaListOf(this, () => st.owner ? (st.owner.getAttribute('media') ?? '') : st.media,
      v => { if (st.owner) st.owner.setAttribute('media', v); else st.media = v; }); },
  })) Object.defineProperty(StyleSheet.prototype, k, { get: f, configurable: true, enumerable: true });
  Object.defineProperty(StyleSheet.prototype, 'disabled', { get() { return holderOf(this).st.disabled; }, set(v) { holderOf(this).st.disabled = !!v; }, configurable: true, enumerable: true });
  const elementSheets = new WeakMap();
  const sheetOfElement = el => {
    let sh = elementSheets.get(el);
    if (!sh) {
      sh = el.localName === 'style' ? sheetOfText(() => el.textContent, t => { el.textContent = t; }, el) : sheetOfText(() => '', () => {}, el);
      elementSheets.set(el, sh);
    }
    return sh;
  };
  const isSheetLink = el => el.localName === 'link' && /(^|\s)stylesheet(\s|$)/i.test(el.getAttribute('rel') ?? '');
  Object.defineProperty(named.HTMLStyleElement.prototype, 'sheet', { get() { return this.isConnected || elementSheets.has(this) ? sheetOfElement(this) : null; }, configurable: true, enumerable: true });
  Object.defineProperty(named.HTMLLinkElement.prototype, 'sheet', { get() { return this.isConnected && isSheetLink(this) ? sheetOfElement(this) : null; }, configurable: true, enumerable: true });
  const sheetsOfDocument = doc => Array.from(doc.querySelectorAll('style, link')).filter(el => el.localName === 'style' || isSheetLink(el)).map(sheetOfElement);
  const sheetLists = new WeakMap();
  Object.defineProperty(Document.prototype, 'styleSheets', { get() {
    let l = sheetLists.get(this);
    if (!l) {
      const doc = this;
      l = new Proxy(Object.create(StyleSheetList.prototype), {
        get(t, p) {
          if (p === 'length') return sheetsOfDocument(doc).length;
          if (p === 'item') return i => sheetsOfDocument(doc)[i >>> 0] ?? null;
          if (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) return sheetsOfDocument(doc)[Number(p)];
          return Reflect.get(t, p);
        },
        has(t, p) { return (typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p)) ? Number(p) < sheetsOfDocument(doc).length : p === 'length' || p === 'item' || Reflect.has(t, p); },
      });
      sheetLists.set(this, l);
    }
    return l;
  }, configurable: true, enumerable: true });
  define(StyleSheetList.prototype, Symbol.iterator, function* () { for (let i = 0; i < this.length; i++) yield this[i]; });
  for (const [k, v] of Object.entries(Object.assign({ CSSRuleList, StyleSheet, CSSStyleSheet, MediaList, StyleSheetList }, Object.fromEntries(Object.entries(ruleClasses).map(([k, v]) => ['CSS' + k, v]))))) {
    Object.defineProperty(v.prototype, Symbol.toStringTag, { value: k, configurable: true });
    def(k, v);
  }
  // ---- CSS Typed OM 1. The classes hold their fields. Lean (CssTyped.typedOp, node_query
  // op 154) decides what a CSS value is as a typed object (reify), what a typed object is as
  // CSS text, the types of numeric values and their arithmetic; whether a value is one a
  // property takes is the property table's answer (op 151). A numeric value goes to Lean as
  // text: u(3.14 "px"), sum(a, b), product(a, b), negate(a), invert(a), min, max, clamp.
  const typedOp = (...parts) => { const r = n.query(0, 154, parts.join('\u0000')); return typeof r === 'string' ? r : ''; };
  const typedKey = {}, typedState = new WeakMap();
  const tstateOf = v => { const s = typedState.get(v); if (!s) throw new TypeError('Illegal invocation'); return s; };
  class CSSStyleValue {
    constructor(key) { if (key !== typedKey) illegal(); }
    toString() { return tstateOf(this).text ?? ''; }
    static parse(property, cssText) {
      if (arguments.length < 2) throw new TypeError('CSSStyleValue.parse: 2 arguments required');
      const name = knownProperty(property), text = String(cssText);
      if (styleOp('val', name, text).charAt(0) !== '1') throw new TypeError(`CSSStyleValue.parse: '${text}' is not a value of '${name}'`);
      return reified(listValued(name) ? JSON.parse(typedOp('reifyall', text))[0] : JSON.parse(typedOp('reify', text)));
    }
    static parseAll(property, cssText) {
      if (arguments.length < 2) throw new TypeError('CSSStyleValue.parseAll: 2 arguments required');
      const name = knownProperty(property), text = String(cssText);
      if (styleOp('val', name, text).charAt(0) !== '1') throw new TypeError(`CSSStyleValue.parseAll: '${text}' is not a value of '${name}'`);
      return listValued(name) ? JSON.parse(typedOp('reifyall', text)).map(reified) : [reified(JSON.parse(typedOp('reify', text)))];
    }
  }
  const opaque = (C, text) => { const v = Object.create(C.prototype); typedState.set(v, { text }); return v; };
  class CSSImageValue extends CSSStyleValue {}
  class CSSKeywordValue extends CSSStyleValue {
    constructor(value) {
      super(typedKey);
      if (arguments.length < 1) throw new TypeError('CSSKeywordValue: 1 argument required');
      value = String(value);
      if (value === '') throw new TypeError('CSSKeywordValue: the keyword is empty');
      typedState.set(this, { value });
    }
    get value() { return tstateOf(this).value; }
    set value(v) { v = String(v); if (v === '') throw new TypeError('CSSKeywordValue: the keyword is empty'); tstateOf(this).value = v; }
    toString() { return op(0, 166, tstateOf(this).value); }
  }
  const numText = x => Number.isNaN(x) ? 'nan' : x === Infinity ? 'infinity' : x === -Infinity ? '-infinity' : String(x);
  const wireOf = v => {
    const s = tstateOf(v);
    if (s.op === undefined) return `u(${numText(s.value)} ${JSON.stringify(s.unit)})`;
    if (s.op === 'negate' || s.op === 'invert') return `${s.op}(${wireOf(s.value)})`;
    if (s.op === 'clamp') return `clamp(${wireOf(s.lower)}, ${wireOf(s.value)}, ${wireOf(s.upper)})`;
    return `${s.op}(${Array.from(s.values).map(wireOf).join(', ')})`;
  };
  const numberish = x => {
    if (typeof x === 'number') return new CSSUnitValue(x, 'number');
    if (x instanceof CSSNumericValue) return x;
    throw new TypeError('The value is not a number or a CSSNumericValue');
  };
  const mathClasses = {};
  const numericArray = xs => {
    const a = Object.create(CSSNumericArray.prototype);
    xs.forEach((x, i) => Object.defineProperty(a, i, { value: x, enumerable: true, configurable: true }));
    Object.defineProperty(a, 'length', { value: xs.length, configurable: true });
    return a;
  };
  // A typed value from Lean's JSON.
  const reified = j => {
    switch (j.t) {
      case 'u': { const v = Object.create(CSSUnitValue.prototype); typedState.set(v, { value: Number(j.v), unit: j.u }); return v; }
      case 'kw': return new CSSKeywordValue(j.v);
      case 'image': return opaque(CSSImageValue, j.c);
      case 'style': return opaque(CSSStyleValue, j.c);
      case 'unparsed': return new CSSUnparsedValue(j.a.map(m => typeof m === 'string' ? m : new CSSVariableReferenceValue(m.v, m.f === null ? null : reified(m.f))));
      case 'negate': case 'invert': { const v = Object.create(mathClasses[j.t].prototype); typedState.set(v, { op: j.t, value: reified(j.a[0]) }); return v; }
      case 'clamp': { const v = Object.create(mathClasses.clamp.prototype); typedState.set(v, { op: 'clamp', lower: reified(j.a[0]), value: reified(j.a[1]), upper: reified(j.a[2]) }); return v; }
      default: {
        const C = mathClasses[j.t];
        if (!C) return opaque(CSSStyleValue, '');
        const v = Object.create(C.prototype); typedState.set(v, { op: j.t, values: numericArray(j.a.map(reified)) }); return v;
      }
    }
  };
  const arith = (verb, a, vs) => {
    const r = typedOp(verb, wireOf(a), ...vs.map(v => wireOf(numberish(v))));
    if (r === '') throw new TypeError(`${verb}: the values do not have compatible types`);
    return reified(JSON.parse(r));
  };
  class CSSNumericValue extends CSSStyleValue {
    add(...vs) { return arith('add', this, vs); }
    sub(...vs) { return arith('sub', this, vs); }
    mul(...vs) { return arith('mul', this, vs); }
    div(...vs) { return arith('div', this, vs); }
    min(...vs) { return arith('min', this, vs); }
    max(...vs) { return arith('max', this, vs); }
    equals(...vs) { return typedOp('equals', wireOf(this), ...vs.map(v => wireOf(numberish(v)))) === '1'; }
    to(unit) {
      if (arguments.length < 1) throw new TypeError('to: 1 argument required');
      if (typedOp('unit', String(unit)) !== '1') throw new DOMException(`'${unit}' is not a unit`, 'SyntaxError');
      const r = typedOp('to', wireOf(this), String(unit));
      if (r === '') throw new TypeError(`The value can not be converted to '${unit}'`);
      return reified(JSON.parse(r));
    }
    type() { const r = typedOp('type', wireOf(this)); if (r === '') throw new TypeError('The value has no type'); return JSON.parse(r); }
    toString() { return typedOp('css', wireOf(this)); }
    static parse(cssText) {
      if (arguments.length < 1) throw new TypeError('CSSNumericValue.parse: 1 argument required');
      const r = typedOp('parse', String(cssText));
      if (r === '') throw new DOMException(`'${cssText}' is not a numeric value`, 'SyntaxError');
      return reified(JSON.parse(r));
    }
  }
  class CSSUnitValue extends CSSNumericValue {
    constructor(value, unit) {
      super(typedKey);
      if (arguments.length < 2) throw new TypeError('CSSUnitValue: 2 arguments required');
      value = Number(value);
      if (!Number.isFinite(value)) throw new TypeError('CSSUnitValue: the value is not a finite number');
      unit = String(unit);
      if (typedOp('unit', unit) !== '1') throw new TypeError(`CSSUnitValue: '${unit}' is not a unit`);
      typedState.set(this, { value, unit: unit.toLowerCase() });
    }
    get value() { return tstateOf(this).value; }
    set value(v) { v = Number(v); if (!Number.isFinite(v)) throw new TypeError('CSSUnitValue: the value is not a finite number'); tstateOf(this).value = v; }
    get unit() { return tstateOf(this).unit; }
  }
  class CSSMathValue extends CSSNumericValue { get operator() { return tstateOf(this).op; } }
  class CSSNumericArray { constructor() { illegal(); } }
  for (const [k, f] of Object.entries({
    forEach(f, self) { for (let i = 0; i < this.length; i++) f.call(self, this[i], i, this); },
    *entries() { for (let i = 0; i < this.length; i++) yield [i, this[i]]; },
    *keys() { for (let i = 0; i < this.length; i++) yield i; },
    *values() { for (let i = 0; i < this.length; i++) yield this[i]; },
  })) define(CSSNumericArray.prototype, k, f);
  define(CSSNumericArray.prototype, Symbol.iterator, CSSNumericArray.prototype.values);
  // A math value is made only if its values have compatible types (Lean's answer).
  const mathOf = (self, state) => {
    typedState.set(self, state);
    if (typedOp('type', wireOf(self)) === '') { typedState.delete(self); throw new TypeError('The values do not have compatible types'); }
  };
  for (const [name, opName] of [['Sum', 'sum'], ['Product', 'product'], ['Min', 'min'], ['Max', 'max']]) {
    const C = ({ ['CSSMath' + name]: class extends CSSMathValue {
      constructor(...args) {
        super(typedKey);
        if (args.length === 0) throw new DOMException('A math value needs at least one value', 'SyntaxError');
        mathOf(this, { op: opName, values: numericArray(args.map(numberish)) });
      }
      get values() { return tstateOf(this).values; }
    } })['CSSMath' + name];
    mathClasses[opName] = C;
  }
  for (const [name, opName] of [['Negate', 'negate'], ['Invert', 'invert']]) {
    const C = ({ ['CSSMath' + name]: class extends CSSMathValue {
      constructor(arg) {
        super(typedKey);
        if (arguments.length < 1) throw new TypeError('1 argument required');
        mathOf(this, { op: opName, value: numberish(arg) });
      }
      get value() { return tstateOf(this).value; }
    } })['CSSMath' + name];
    mathClasses[opName] = C;
  }
  class CSSMathClamp extends CSSMathValue {
    constructor(lower, value, upper) {
      super(typedKey);
      if (arguments.length < 3) throw new TypeError('CSSMathClamp: 3 arguments required');
      mathOf(this, { op: 'clamp', lower: numberish(lower), value: numberish(value), upper: numberish(upper) });
    }
    get lower() { return tstateOf(this).lower; }
    get value() { return tstateOf(this).value; }
    get upper() { return tstateOf(this).upper; }
  }
  mathClasses.clamp = CSSMathClamp;
  class CSSVariableReferenceValue {
    constructor(variable, fallback = null) {
      if (arguments.length < 1) throw new TypeError('CSSVariableReferenceValue: 1 argument required');
      variable = String(variable).trim();
      if (!variable.startsWith('--') || variable.length < 3) throw new TypeError('CSSVariableReferenceValue: not a custom property name');
      if (fallback !== null && fallback !== undefined && !(fallback instanceof CSSUnparsedValue)) throw new TypeError('CSSVariableReferenceValue: the fallback is not a CSSUnparsedValue');
      typedState.set(this, { variable, fallback: fallback ?? null });
    }
    get variable() { return tstateOf(this).variable; }
    set variable(v) { v = String(v).trim(); if (!v.startsWith('--') || v.length < 3) throw new TypeError('CSSVariableReferenceValue: not a custom property name'); tstateOf(this).variable = v; }
    get fallback() { return tstateOf(this).fallback; }
  }
  class CSSUnparsedValue extends CSSStyleValue {
    constructor(members) {
      super(typedKey);
      if (arguments.length < 1) throw new TypeError('CSSUnparsedValue: 1 argument required');
      const xs = Array.from(members);
      for (const m of xs) if (typeof m !== 'string' && !(m instanceof CSSVariableReferenceValue)) throw new TypeError('CSSUnparsedValue: a member is not a string or a CSSVariableReferenceValue');
      typedState.set(this, { members: xs });
      xs.forEach((x, i) => Object.defineProperty(this, i, { get: () => tstateOf(this).members[i],
        set: v => { if (typeof v !== 'string' && !(v instanceof CSSVariableReferenceValue)) throw new TypeError('not a string or a CSSVariableReferenceValue'); tstateOf(this).members[i] = v; },
        enumerable: true, configurable: true }));
    }
    get length() { return tstateOf(this).members.length; }
    forEach(f, self) { tstateOf(this).members.forEach((x, i) => f.call(self, x, i, this)); }
    *entries() { yield* tstateOf(this).members.entries(); }
    *keys() { yield* tstateOf(this).members.keys(); }
    *values() { yield* tstateOf(this).members.values(); }
    toString() { return tstateOf(this).members.map(m => typeof m === 'string' ? m : `var(${m.variable}${m.fallback ? ',' + m.fallback.toString() : ''})`).join(''); }
  }
  define(CSSUnparsedValue.prototype, Symbol.iterator, CSSUnparsedValue.prototype.values);
  // Transform values: the components as objects; their text is the transform function's.
  class CSSTransformComponent {
    constructor(key) { if (key !== typedKey) illegal(); }
    get is2D() { return tstateOf(this).is2D; }
    set is2D(v) { tstateOf(this).is2D = !!v; }
  }
  const lengthArg = x => { const v = numberish(x); return v; };
  class CSSTranslate extends CSSTransformComponent {
    constructor(x, y, z) { super(typedKey); if (arguments.length < 2) throw new TypeError('CSSTranslate: 2 arguments required');
      typedState.set(this, { x: lengthArg(x), y: lengthArg(y), z: z === undefined ? new CSSUnitValue(0, 'px') : lengthArg(z), is2D: z === undefined }); }
    get x() { return tstateOf(this).x; } get y() { return tstateOf(this).y; } get z() { return tstateOf(this).z; }
    set x(v) { tstateOf(this).x = lengthArg(v); } set y(v) { tstateOf(this).y = lengthArg(v); } set z(v) { tstateOf(this).z = lengthArg(v); }
    toString() { const s = tstateOf(this); return s.is2D ? `translate(${s.x}, ${s.y})` : `translate3d(${s.x}, ${s.y}, ${s.z})`; }
  }
  class CSSRotate extends CSSTransformComponent {
    constructor(a, b, c, d) { super(typedKey);
      if (arguments.length === 1) typedState.set(this, { x: new CSSUnitValue(0, 'number'), y: new CSSUnitValue(0, 'number'), z: new CSSUnitValue(1, 'number'), angle: numberish(a), is2D: true });
      else if (arguments.length >= 4) typedState.set(this, { x: numberish(a), y: numberish(b), z: numberish(c), angle: numberish(d), is2D: false });
      else throw new TypeError('CSSRotate: 1 or 4 arguments required'); }
    get x() { return tstateOf(this).x; } get y() { return tstateOf(this).y; } get z() { return tstateOf(this).z; } get angle() { return tstateOf(this).angle; }
    set x(v) { tstateOf(this).x = numberish(v); } set y(v) { tstateOf(this).y = numberish(v); } set z(v) { tstateOf(this).z = numberish(v); } set angle(v) { tstateOf(this).angle = numberish(v); }
    toString() { const s = tstateOf(this); return s.is2D ? `rotate(${s.angle})` : `rotate3d(${s.x}, ${s.y}, ${s.z}, ${s.angle})`; }
  }
  class CSSScale extends CSSTransformComponent {
    constructor(x, y, z) { super(typedKey); if (arguments.length < 2) throw new TypeError('CSSScale: 2 arguments required');
      typedState.set(this, { x: numberish(x), y: numberish(y), z: z === undefined ? new CSSUnitValue(1, 'number') : numberish(z), is2D: z === undefined }); }
    get x() { return tstateOf(this).x; } get y() { return tstateOf(this).y; } get z() { return tstateOf(this).z; }
    set x(v) { tstateOf(this).x = numberish(v); } set y(v) { tstateOf(this).y = numberish(v); } set z(v) { tstateOf(this).z = numberish(v); }
    toString() { const s = tstateOf(this); return s.is2D ? `scale(${s.x}, ${s.y})` : `scale3d(${s.x}, ${s.y}, ${s.z})`; }
  }
  class CSSSkew extends CSSTransformComponent {
    constructor(ax, ay) { super(typedKey); if (arguments.length < 2) throw new TypeError('CSSSkew: 2 arguments required'); typedState.set(this, { ax: numberish(ax), ay: numberish(ay), is2D: true }); }
    get ax() { return tstateOf(this).ax; } get ay() { return tstateOf(this).ay; }
    set ax(v) { tstateOf(this).ax = numberish(v); } set ay(v) { tstateOf(this).ay = numberish(v); }
    get is2D() { return true; } set is2D(v) {}
    toString() { const s = tstateOf(this); return `skew(${s.ax}, ${s.ay})`; }
  }
  class CSSSkewX extends CSSTransformComponent {
    constructor(ax) { super(typedKey); if (arguments.length < 1) throw new TypeError('CSSSkewX: 1 argument required'); typedState.set(this, { ax: numberish(ax), is2D: true }); }
    get ax() { return tstateOf(this).ax; } set ax(v) { tstateOf(this).ax = numberish(v); }
    get is2D() { return true; } set is2D(v) {}
    toString() { return `skewX(${tstateOf(this).ax})`; }
  }
  class CSSSkewY extends CSSTransformComponent {
    constructor(ay) { super(typedKey); if (arguments.length < 1) throw new TypeError('CSSSkewY: 1 argument required'); typedState.set(this, { ay: numberish(ay), is2D: true }); }
    get ay() { return tstateOf(this).ay; } set ay(v) { tstateOf(this).ay = numberish(v); }
    get is2D() { return true; } set is2D(v) {}
    toString() { return `skewY(${tstateOf(this).ay})`; }
  }
  class CSSPerspective extends CSSTransformComponent {
    constructor(length) { super(typedKey); if (arguments.length < 1) throw new TypeError('CSSPerspective: 1 argument required');
      typedState.set(this, { length: length instanceof CSSKeywordValue || typeof length === 'string' ? (typeof length === 'string' ? new CSSKeywordValue(length) : length) : numberish(length), is2D: false }); }
    get length() { return tstateOf(this).length; } set length(v) { tstateOf(this).length = v instanceof CSSKeywordValue ? v : numberish(v); }
    get is2D() { return false; } set is2D(v) {}
    toString() { return `perspective(${tstateOf(this).length})`; }
  }
  class CSSMatrixComponent extends CSSTransformComponent {
    constructor(matrix, options = undefined) { super(typedKey); if (arguments.length < 1) throw new TypeError('CSSMatrixComponent: 1 argument required');
      const is2D = options && options.is2D !== undefined ? !!options.is2D : !!matrix.is2D;
      typedState.set(this, { matrix, is2D }); }
    get matrix() { return tstateOf(this).matrix; } set matrix(m) { tstateOf(this).matrix = m; }
    toString() { const s = tstateOf(this), m = s.matrix;
      return s.is2D ? `matrix(${[m.a, m.b, m.c, m.d, m.e, m.f].join(', ')})`
        : `matrix3d(${[m.m11, m.m12, m.m13, m.m14, m.m21, m.m22, m.m23, m.m24, m.m31, m.m32, m.m33, m.m34, m.m41, m.m42, m.m43, m.m44].join(', ')})`; }
  }
  class CSSTransformValue extends CSSStyleValue {
    constructor(transforms) {
      super(typedKey);
      if (arguments.length < 1) throw new TypeError('CSSTransformValue: 1 argument required');
      const xs = Array.from(transforms);
      if (xs.length === 0) throw new TypeError('CSSTransformValue: no transform');
      for (const x of xs) if (!(x instanceof CSSTransformComponent)) throw new TypeError('CSSTransformValue: a member is not a CSSTransformComponent');
      typedState.set(this, { members: xs });
      xs.forEach((x, i) => Object.defineProperty(this, i, { get: () => tstateOf(this).members[i], set: v => { tstateOf(this).members[i] = v; }, enumerable: true, configurable: true }));
    }
    get length() { return tstateOf(this).members.length; }
    get is2D() { return tstateOf(this).members.every(x => x.is2D); }
    forEach(f, self) { tstateOf(this).members.forEach((x, i) => f.call(self, x, i, this)); }
    *entries() { yield* tstateOf(this).members.entries(); }
    *keys() { yield* tstateOf(this).members.keys(); }
    *values() { yield* tstateOf(this).members.values(); }
    toString() { return tstateOf(this).members.map(String).join(' '); }
  }
  define(CSSTransformValue.prototype, Symbol.iterator, CSSTransformValue.prototype.values);
  // Style property maps: the declared values of a block (element.attributeStyleMap, a rule's
  // styleMap) and the computed values (element.computedStyleMap()).
  const knownProperty = property => {
    const name = String(property);
    if (name.startsWith('--')) return name;
    if (styleOp('sup', name, 'initial') !== '1') throw new TypeError(`'${name}' is not a CSS property`);
    return name.toLowerCase();
  };
  const listValued = name => typedOp('islist', name) === '1';
  const mapState = new WeakMap();
  const mstate = m => { const s = mapState.get(m); if (!s) throw new TypeError('Illegal invocation'); return s; };
  class StylePropertyMapReadOnly {
    constructor(key) { if (key !== typedKey) illegal(); }
    get(property) {
      if (arguments.length < 1) throw new TypeError('get: 1 argument required');
      const name = knownProperty(property), text = mstate(this).read(name);
      if (text === '') return undefined;
      return reified(listValued(name) ? JSON.parse(typedOp('reifyall', text))[0] : JSON.parse(typedOp('reify', text)));
    }
    getAll(property) {
      if (arguments.length < 1) throw new TypeError('getAll: 1 argument required');
      const name = knownProperty(property), text = mstate(this).read(name);
      if (text === '') return [];
      return listValued(name) ? JSON.parse(typedOp('reifyall', text)).map(reified) : [reified(JSON.parse(typedOp('reify', text)))];
    }
    has(property) { if (arguments.length < 1) throw new TypeError('has: 1 argument required'); return mstate(this).read(knownProperty(property)) !== ''; }
    get size() { return mstate(this).names().length; }
    *entries() { for (const name of mstate(this).names().slice().sort()) yield [name, this.getAll(name)]; }
    *keys() { for (const [k] of this.entries()) yield k; }
    *values() { for (const [, v] of this.entries()) yield v; }
    forEach(f, self) { for (const [k, v] of this.entries()) f.call(self, v, k, this); }
  }
  define(StylePropertyMapReadOnly.prototype, Symbol.iterator, StylePropertyMapReadOnly.prototype.entries);
  // The CSS text of the values given to set() or append(), and the text to check them by: a
  // number is checked as calc(n), so a unitless zero is not taken for a length.
  const valueTexts = (name, values) => values.map(v => {
    if (typeof v === 'string') return { text: v, check: v };
    if (!(v instanceof CSSStyleValue)) throw new TypeError(`The value given for '${name}' is not a string or a CSSStyleValue`);
    const text = v.toString();
    if (v instanceof CSSUnitValue) return { text, check: tstateOf(v).unit === 'number' ? `calc(${text})` : text, unit: true };
    return { text, check: text };
  });
  class StylePropertyMap extends StylePropertyMapReadOnly {
    set(property, ...values) {
      if (arguments.length < 2) throw new TypeError('set: 2 arguments required');
      const name = knownProperty(property), st = mstate(this), xs = valueTexts(name, values);
      if (xs.length > 1 && !listValued(name)) throw new TypeError(`'${name}' takes one value`);
      const ok = t => styleOp('val', name, t).charAt(0) === '1';
      let text = xs.map(x => x.text).join(', ');
      if (!ok(xs.map(x => x.check).join(', '))) {
        // a unit value outside the range of the property is kept as a calc() (Typed OM §4.1.2)
        const wrapped = xs.map(x => x.unit ? `calc(${x.text})` : x.text).join(', ');
        if (!xs.some(x => x.unit) || !ok(wrapped)) throw new TypeError(`The value is not one '${name}' takes`);
        text = wrapped;
      }
      st.set(name, text);
    }
    append(property, ...values) {
      if (arguments.length < 2) throw new TypeError('append: 2 arguments required');
      const name = knownProperty(property), st = mstate(this), xs = valueTexts(name, values);
      if (!listValued(name)) throw new TypeError(`'${name}' is not a list-valued property`);
      const old = st.read(name), text = (old === '' ? [] : [old]).concat(xs.map(x => x.text)).join(', ');
      if (styleOp('val', name, text).charAt(0) !== '1') throw new TypeError(`The value is not one '${name}' takes`);
      st.set(name, text);
    }
    delete(property) { if (arguments.length < 1) throw new TypeError('delete: 1 argument required'); mstate(this).remove(knownProperty(property)); }
    clear() { mstate(this).clear(); }
  }
  const declaredMap = style => {
    const m = Object.create(StylePropertyMap.prototype);
    mapState.set(m, { read: name => style.getPropertyValue(name), names: () => Array.from(style),
      set: (name, text) => style.setProperty(name, text), remove: name => { style.removeProperty(name); }, clear: () => { style.cssText = ''; } });
    return m;
  };
  const styleMaps = new WeakMap();
  const attributeStyleMap = { get() { let m = styleMaps.get(this); if (!m) styleMaps.set(this, m = declaredMap(this.style)); return m; }, configurable: true, enumerable: true };
  Object.defineProperty(HTMLElement.prototype, 'attributeStyleMap', attributeStyleMap);
  Object.defineProperty(SVGElement.prototype, 'attributeStyleMap', attributeStyleMap);
  Object.defineProperty(ruleClasses.StyleRule.prototype, 'styleMap', { get() { let m = styleMaps.get(this); if (!m) styleMaps.set(this, m = declaredMap(this.style)); return m; }, configurable: true, enumerable: true });
  define(Element.prototype, 'computedStyleMap', function () {
    const el = this, m = Object.create(StylePropertyMapReadOnly.prototype);
    mapState.set(m, { read: name => computedValue(el, name), names: () => namesFor(el) });
    return m;
  });
  for (const [k, unit] of Object.entries({ number: 'number', percent: 'percent', em: 'em', rem: 'rem', ex: 'ex', rex: 'rex', cap: 'cap', rcap: 'rcap', ch: 'ch', rch: 'rch', ic: 'ic', ric: 'ric',
    lh: 'lh', rlh: 'rlh', vw: 'vw', vh: 'vh', vi: 'vi', vb: 'vb', vmin: 'vmin', vmax: 'vmax', svw: 'svw', svh: 'svh', svi: 'svi', svb: 'svb', svmin: 'svmin', svmax: 'svmax',
    lvw: 'lvw', lvh: 'lvh', lvi: 'lvi', lvb: 'lvb', lvmin: 'lvmin', lvmax: 'lvmax', dvw: 'dvw', dvh: 'dvh', dvi: 'dvi', dvb: 'dvb', dvmin: 'dvmin', dvmax: 'dvmax',
    cqw: 'cqw', cqh: 'cqh', cqi: 'cqi', cqb: 'cqb', cqmin: 'cqmin', cqmax: 'cqmax', cm: 'cm', mm: 'mm', Q: 'q', in: 'in', pt: 'pt', pc: 'pc', px: 'px',
    deg: 'deg', grad: 'grad', rad: 'rad', turn: 'turn', s: 's', ms: 'ms', Hz: 'hz', kHz: 'khz', dpi: 'dpi', dpcm: 'dpcm', dppx: 'dppx', fr: 'fr' }))
    define(CSSns, k, function (value) { if (arguments.length < 1) throw new TypeError(`CSS.${k}: 1 argument required`); return new CSSUnitValue(value, unit); });
  for (const [k, v] of Object.entries({ CSSStyleValue, CSSImageValue, CSSKeywordValue, CSSNumericValue, CSSUnitValue, CSSMathValue, CSSNumericArray,
    CSSMathSum: mathClasses.sum, CSSMathProduct: mathClasses.product, CSSMathMin: mathClasses.min, CSSMathMax: mathClasses.max,
    CSSMathNegate: mathClasses.negate, CSSMathInvert: mathClasses.invert, CSSMathClamp, CSSVariableReferenceValue, CSSUnparsedValue,
    CSSTransformComponent, CSSTranslate, CSSRotate, CSSScale, CSSSkew, CSSSkewX, CSSSkewY, CSSPerspective, CSSMatrixComponent, CSSTransformValue,
    StylePropertyMapReadOnly, StylePropertyMap })) {
    Object.defineProperty(v.prototype, Symbol.toStringTag, { value: k, configurable: true });
    def(k, v);
  }
  def('getComputedStyle', (el, pseudo) => {
    if (!(el instanceof Element)) throw new TypeError("Failed to execute 'getComputedStyle': parameter 1 is not of type 'Element'.");
    return computedStyle(el);
  });
  def('getSelection', getSelection);
  for (const C of new Set([HTMLElement, HTMLUnknownElement, ...Object.values(named)])) reflectInstall(C);
  // ---- IDL attributes that reflect an element or elements (HTML §2.6.1) ----
  // `ariaActiveDescendantElement`, `ariaLabelledByElements` and the other ARIA element
  // attributes, `popoverTargetElement`, `commandForElement`. The page keeps the explicitly set
  // elements; which element the getter answers is Lean's (DOM.ElementRef, node_query 184 and
  // 185): an explicit element only when it is a descendant of a shadow-including ancestor,
  // else the element of the same tree that the content attribute's ID names.
  {
    const explicitRefs = new WeakMap();
    // the explicitly set value, unless the content attribute changed since by other means
    const explicitOf = (el, content) => {
      const m = explicitRefs.get(el), x = m && m.get(content);
      if (!x) return undefined;
      if (el.getAttribute(content) !== '') { m.delete(content); return undefined; }
      return x;
    };
    const setExplicit = (el, content, value) => {
      el.setAttribute(content, '');
      let m = explicitRefs.get(el); if (!m) explicitRefs.set(el, m = new Map());
      m.set(content, { value });
    };
    const clearExplicit = (el, content) => { const m = explicitRefs.get(el); if (m) m.delete(content); el.removeAttribute(content); };
    const needElement = (v, idl) => { if (!(v instanceof Element)) throw new TypeError(`Failed to set the '${idl}' property: the value is not of type 'Element'.`); return v; };
    const reflectElement = (C, idl, content) => Object.defineProperty(C.prototype, idl, {
      get() {
        const x = explicitOf(this, content);
        const r = n.query(nodeId(this), 184, content + '\u0000' + (x ? nodeId(x.value) : ''));
        return typeof r === 'string' && r !== '' ? wrap(Number(r)) : null;
      },
      set(v) { if (v === null || v === undefined) clearExplicit(this, content); else setExplicit(this, content, needElement(v, idl)); },
      configurable: true, enumerable: true });
    const reflectElements = (C, idl, content) => {
      const cached = new WeakMap();
      Object.defineProperty(C.prototype, idl, {
        get() {
          const x = explicitOf(this, content);
          const r = n.query(nodeId(this), 185, content + '\u0000' + (x ? x.value.map(nodeId).join(' ') : '-'));
          if (typeof r !== 'string' || r === '-') return null;
          const ks = r === '' ? [] : r.split(' ').map(Number), old = cached.get(this);
          if (old && old.ks.length === ks.length && old.ks.every((k, i) => k === ks[i])) return old.array;
          const array = Object.freeze(ks.map(wrap));
          cached.set(this, { ks, array });
          return array;
        },
        set(v) {
          if (v === null || v === undefined) { clearExplicit(this, content); return; }
          if (typeof v !== 'object' && typeof v !== 'function') throw new TypeError(`Failed to set the '${idl}' property: the value is not a sequence.`);
          setExplicit(this, content, [...v].map(e => needElement(e, idl)));
        },
        configurable: true, enumerable: true });
    };
    reflectElement(Element, 'ariaActiveDescendantElement', 'aria-activedescendant');
    for (const [idl, content] of [['ariaControlsElements', 'aria-controls'], ['ariaDescribedByElements', 'aria-describedby'],
      ['ariaDetailsElements', 'aria-details'], ['ariaErrorMessageElements', 'aria-errormessage'], ['ariaFlowToElements', 'aria-flowto'],
      ['ariaLabelledByElements', 'aria-labelledby'], ['ariaOwnsElements', 'aria-owns']]) reflectElements(Element, idl, content);
    for (const C of [named.HTMLButtonElement, named.HTMLInputElement]) reflectElement(C, 'popoverTargetElement', 'popovertarget');
    reflectElement(named.HTMLButtonElement, 'commandForElement', 'commandfor');
  }
  // Document.dir reflects the `dir` of the html element, and fgColor, linkColor, vlinkColor,
  // alinkColor and bgColor the `text`, `link`, `vlink`, `alink` and `bgcolor` of the body
  // element, [LegacyNullToEmptyString] (HTML §3.1.4 and §16.3).
  {
    const htmlRoot = doc => { const e = doc.documentElement; return e && info(nodeId(e), 8) === 1 && e.localName === 'html' ? e : null; };
    const bodyOf = doc => { const b = doc.body; return b && b.localName === 'body' ? b : null; };
    Object.defineProperty(Document.prototype, 'dir', { get() { const e = htmlRoot(this); return e ? e.dir : ''; },
      set(v) { const e = htmlRoot(this); if (e) e.dir = v; }, configurable: true, enumerable: true });
    for (const [idl, content] of [['fgColor', 'text'], ['linkColor', 'link'], ['vlinkColor', 'vlink'], ['alinkColor', 'alink'], ['bgColor', 'bgcolor']])
      Object.defineProperty(Document.prototype, idl, { get() { const b = bodyOf(this); return b ? b.getAttribute(content) ?? '' : ''; },
        set(v) { const b = bodyOf(this); if (b) b.setAttribute(content, v === null ? '' : String(v)); }, configurable: true, enumerable: true });
  }
  for (const [k, v] of Object.entries({ AbstractRange, Range, StaticRange, Selection, NodeFilter, NodeIterator, TreeWalker, CSSStyleDeclaration })) {
    if (k !== 'NodeFilter') Object.defineProperty(v.prototype, Symbol.toStringTag, { value: k, configurable: true });
    def(k, v);
  }
  // ==== end dombreadth ====

  // ==== xmlweb: DOM XPath (DOM §8 "XPath") ================================================
  // The expression is parsed and evaluated by Lean: DOM.XPathDom over the XPath 1.0
  // evaluator of the engine (XPath.Full), node_query ops 121 (the prefixes an expression
  // uses), 122 (evaluate) and 123 (the DOM's change count). Here: the interfaces, the calls
  // of the page's XPathNSResolver, and the result object.
  {
    const SEP = '\u0001', SEP2 = '\u0002';
    const xpThrow = r => {
      const name = r.slice(1);
      if (name === 'TypeError') throw new TypeError('The result is not a node set, and therefore cannot be converted to the desired type.');
      const text = { SyntaxError: 'The string is not a valid XPath expression.',
        NamespaceError: 'The string contains an invalid namespace.',
        NotSupportedError: 'The node provided is not a valid context node type, or the result type is not known.' }[name] ?? 'XPath error';
      throw new DOMException(text, name);
    };
    const xpAns = r => (typeof r === 'string' && r.charCodeAt(0) === 33 ? xpThrow(r) : r);
    const badNs = () => new DOMException('The string contains an invalid namespace.', 'NamespaceError');
    // XPathNSResolver is a callback interface (Web IDL §3.11 "call a user object's
    // operation"): a function is called, any other object's lookupNamespaceURI is read at
    // each call; an exception of the page's code is reported, and the prefix has no namespace.
    const lookup = (resolver, prefix) => {
      if (resolver === null || resolver === undefined) throw badNs();
      let r = null;
      try {
        let v;
        if (typeof resolver === 'function') v = resolver.call(undefined, prefix);
        else {
          const m = resolver.lookupNamespaceURI;
          if (typeof m !== 'function') throw new TypeError('XPathNSResolver.lookupNamespaceURI is not a function');
          v = m.call(resolver, prefix);
        }
        r = v === null || v === undefined ? null : `${v}`;
      } catch (e) { report(e); r = null; }
      if (r === null) throw badNs();
      return r;
    };
    const resolverArg = r => {
      if (r === null || r === undefined) return null;
      if (typeof r !== 'object' && typeof r !== 'function') throw new TypeError("parameter is not of type 'XPathNSResolver'");
      return r;
    };
    // An expression with its prefixes resolved: what createExpression keeps.
    const compile = (expression, resolver) => {
      expression = `${expression}`;
      const ps = xpAns(op(0, 121, expression));
      const bindings = [];
      if (typeof ps === 'string' && ps !== '') for (const p of ps.split(SEP)) bindings.push(p + SEP2 + lookup(resolver, p));
      return { expression, bindings };
    };
    const contextOf = node => {
      if (node instanceof Attr) {
        const a = attrState.get(node);
        if (!a.el) throw new DOMException('The node provided is not a valid context node type.', 'NotSupportedError');
        return { id: nodeId(a.el), spec: 'a' + (a.ns ?? '') + SEP2 + a.lname };
      }
      return { id: nodeId(node), spec: '' };
    };
    const results = new WeakMap(), expressions = new WeakMap();
    const xr = o => { const s = results.get(o); if (!s) throw new TypeError('Illegal invocation'); return s; };
    const run = (c, ctx, type) => {
      type = (Number(type) >>> 0) & 0xFFFF;
      const r = xpAns(op(ctx.id, 122, [String(type), ctx.spec, String(c.bindings.length), ...c.bindings, c.expression].join(SEP)));
      const i = r.indexOf(SEP), kind = Number(i < 0 ? r : r.slice(0, i)), rest = i < 0 ? null : r.slice(i + 1);
      const st = { type: kind, value: null, nodes: null, next: 0, stamp: '' };
      if (kind === 1) st.value = Number(rest);
      else if (kind === 2) st.value = rest ?? '';
      else if (kind === 3) st.value = rest === '1';
      else {
        st.nodes = rest === null || rest === '' ? [] : rest.split(SEP).map(x => {
          if (x.charCodeAt(0) !== 97) return wrap(Number(x));
          const [el, ns, lname] = x.slice(1).split(SEP2);
          return attrNode(wrap(Number(el)), ns || null, lname);
        });
        st.stamp = op(0, 123);
      }
      const o = Object.create(XPathResult.prototype);
      results.set(o, st);
      return o;
    };
    const isIter = s => s.type === 4 || s.type === 5, isSnap = s => s.type === 6 || s.type === 7;
    class XPathResult {
      constructor() { throw new TypeError('Illegal constructor'); }
      get resultType() { return xr(this).type; }
      get numberValue() { const s = xr(this); if (s.type !== 1) throw new TypeError('The result type is not a number.'); return s.value; }
      get stringValue() { const s = xr(this); if (s.type !== 2) throw new TypeError('The result type is not a string.'); return s.value; }
      get booleanValue() { const s = xr(this); if (s.type !== 3) throw new TypeError('The result type is not a boolean.'); return s.value; }
      get singleNodeValue() { const s = xr(this); if (s.type !== 8 && s.type !== 9) throw new TypeError('The result type is not a single node.'); return s.nodes[0] ?? null; }
      get invalidIteratorState() { const s = xr(this); return isIter(s) && op(0, 123) !== s.stamp; }
      get snapshotLength() { const s = xr(this); if (!isSnap(s)) throw new TypeError('The result type is not a snapshot.'); return s.nodes.length; }
      iterateNext() {
        const s = xr(this);
        if (!isIter(s)) throw new TypeError('The result type is not an iterator.');
        if (op(0, 123) !== s.stamp) throw new DOMException('The document has mutated since the result was returned.', 'InvalidStateError');
        return s.next < s.nodes.length ? s.nodes[s.next++] : null;
      }
      snapshotItem(index) {
        const s = xr(this);
        if (!isSnap(s)) throw new TypeError('The result type is not a snapshot.');
        needArgs(arguments, 1, 'snapshotItem');
        return s.nodes[Number(index) >>> 0] ?? null;
      }
    }
    const types = { ANY_TYPE: 0, NUMBER_TYPE: 1, STRING_TYPE: 2, BOOLEAN_TYPE: 3, UNORDERED_NODE_ITERATOR_TYPE: 4,
      ORDERED_NODE_ITERATOR_TYPE: 5, UNORDERED_NODE_SNAPSHOT_TYPE: 6, ORDERED_NODE_SNAPSHOT_TYPE: 7,
      ANY_UNORDERED_NODE_TYPE: 8, FIRST_ORDERED_NODE_TYPE: 9 };
    consts(XPathResult, types); consts(XPathResult.prototype, types);
    class XPathExpression {
      constructor() { throw new TypeError('Illegal constructor'); }
      evaluate(contextNode, type = 0, result = null) {
        const c = expressions.get(this);
        if (!c) throw new TypeError('Illegal invocation');
        needArgs(arguments, 1, 'evaluate');
        return run(c, contextOf(contextNode), type);
      }
    }
    // XPathEvaluatorBase (DOM §8.3): Document and XPathEvaluator include it.
    const evaluatorBase = {
      createExpression(expression, resolver = null) {
        needArgs(arguments, 1, 'createExpression');
        const e = Object.create(XPathExpression.prototype);
        expressions.set(e, compile(expression, resolverArg(resolver)));
        return e;
      },
      createNSResolver(nodeResolver) {
        needArgs(arguments, 1, 'createNSResolver');
        if (!(nodeResolver instanceof Node)) throw new TypeError("parameter 1 is not of type 'Node'");
        return nodeResolver;
      },
      evaluate(expression, contextNode, resolver = null, type = 0, result = null) {
        needArgs(arguments, 2, 'evaluate');
        const ctx = contextOf(contextNode);
        return run(compile(expression, resolverArg(resolver)), ctx, type);
      },
    };
    class XPathEvaluator {}
    mix(XPathEvaluator, evaluatorBase); mix(Document, evaluatorBase);
    // Document.rootElement (SVG 2 §4.3.1): the document element when it is an svg element.
    Object.defineProperty(Document.prototype, 'rootElement', { get() {
      const e = this.documentElement;
      return e && e.namespaceURI === 'http://www.w3.org/2000/svg' && e.localName === 'svg' ? e : null;
    }, configurable: true, enumerable: true });
    // XSLTProcessor (HTML §4.12.1.4 names it; the transform is XSLT 1.0). The engine's XSLT
    // processor runs on the two DOM trees (node_query op 127, DOM.XsltDom) and answers the
    // serialised result and the output method; the engine's HTML or XML parser reads it.
    const xslt = new WeakMap();
    const xs = o => { const s = xslt.get(o); if (!s) throw new TypeError('Illegal invocation'); return s; };
    const transformed = (p, source) => {
      const s = xs(p), src = nodeId(source);
      if (s.style === null) return null;
      const r = op(nodeId(s.style), 127, String(src));
      if (typeof r !== 'string' || r.charCodeAt(0) !== 49) return null;
      const i = r.indexOf(SEP);
      return { method: r.slice(1, i), text: r.slice(i + 1) };
    };
    const xmlNodesOf = text => {
      const d = new DOMParser().parseFromString('<r>' + text + '</r>', 'application/xml'), root = d.documentElement;
      return root && root.localName === 'r' && root.namespaceURI === null ? root : null;
    };
    class XSLTProcessor {
      constructor() { xslt.set(this, { style: null, params: new Map() }); }
      importStylesheet(style) { needArgs(arguments, 1, 'importStylesheet'); nodeId(style); xs(this).style = style; }
      transformToFragment(source, output) {
        needArgs(arguments, 2, 'transformToFragment');
        if (!(output instanceof Document)) throw new TypeError("parameter 2 is not of type 'Document'");
        const r = transformed(this, source);
        if (r === null) return null;
        const f = output.createDocumentFragment();
        if (r.method === 'html' || r.method === 'text') {
          // the HTML fragment parser with a body context, as createContextualFragment runs
          // it: a script of the result runs when the fragment is inserted
          const range = document.createRange();
          range.selectNodeContents(document.body || document.documentElement || document);
          const parsed = range.createContextualFragment(r.text);
          if (r.method === 'text') f.appendChild(output.createTextNode(parsed.textContent));
          else while (parsed.firstChild) f.appendChild(output === document ? parsed.firstChild : output.adoptNode(parsed.firstChild));
        } else {
          const root = xmlNodesOf(r.text);
          if (root === null) return null;
          while (root.firstChild) f.appendChild(output.adoptNode(root.firstChild));
        }
        return f;
      }
      transformToDocument(source) {
        needArgs(arguments, 1, 'transformToDocument');
        const r = transformed(this, source);
        if (r === null) return null;
        if (r.method === 'html') return new DOMParser().parseFromString(r.text, 'text/html');
        if (r.method === 'text') {
          const d = new DOMParser().parseFromString('<html xmlns="http://www.w3.org/1999/xhtml"><head><title/></head><body><pre/></body></html>', 'application/xml');
          const t = document.createElement('template'); t.innerHTML = r.text;
          const pre = d.getElementsByTagName('pre')[0]; if (pre) pre.textContent = t.content.textContent;
          return d;
        }
        const d = new DOMParser().parseFromString(r.text, 'application/xml');
        return d;
      }
      setParameter(namespaceURI, localName, value) { needArgs(arguments, 3, 'setParameter'); xs(this).params.set(String(namespaceURI ?? '') + SEP + String(localName), value); }
      getParameter(namespaceURI, localName) { needArgs(arguments, 2, 'getParameter'); const v = xs(this).params.get(String(namespaceURI ?? '') + SEP + String(localName)); return v === undefined ? null : v; }
      removeParameter(namespaceURI, localName) { needArgs(arguments, 2, 'removeParameter'); xs(this).params.delete(String(namespaceURI ?? '') + SEP + String(localName)); }
      clearParameters() { xs(this).params.clear(); }
      reset() { const s = xs(this); s.style = null; s.params.clear(); }
    }
    // XMLSerializer (DOM Parsing §2.2): the XML serialization is Lean's (DOM.XmlSerialize,
    // node_query op 124). An Attr is not a node of the arena; it serializes as "" (§3.2.1.7).
    class XMLSerializer {
      serializeToString(root) {
        needArgs(arguments, 1, 'serializeToString');
        if (root instanceof Attr) return '';
        return op(nodeId(root), 124);
      }
    }
    for (const [k, v] of Object.entries({ XPathResult, XPathExpression, XPathEvaluator, XSLTProcessor, XMLSerializer })) {
      Object.defineProperty(v.prototype, Symbol.toStringTag, { value: k, configurable: true });
      def(k, v);
    }
  }
  // ==== end xmlweb ========================================================================

  // ==== workers: Dedicated Workers (HTML §10; docs/designissues/2026-11-09-dedicated-workers.md) ====
  // BubblePopJS only: the structured clone (n.serialize, n.deserialize) walks the heap in
  // Lean (L4Factoidal.JS.Clone), so on an engine without it `Worker` stays undefined.
  // Lean (Hosts.LeanJSWorkers) keeps each worker's realm, event loop and budget, and
  // decides when its tasks run; this is the WebIDL glue: Worker, the worker global scope,
  // importScripts, and the message and error events, one task per event (WORKER_EVENT).
  const WORKER_EVENT = 0x7FFFFFF0;
  const workersOn = typeof n0.serialize === 'function' && typeof n0.worker === 'function';
  let inWorker = false;
  const workerSlots = new WeakMap(), workerObjects = new Map();
  const cloneOut = (message, options, what) => {
    let transfer = [];
    if (Array.isArray(options)) transfer = options;
    else if (options !== undefined && options !== null) {
      if (typeof options !== 'object' && typeof options !== 'function') throw new TypeError(`Failed to execute 'postMessage' on '${what}': The provided value is not of type 'StructuredSerializeOptions'.`);
      if (options.transfer !== undefined) {
        if (options.transfer === null || typeof options.transfer[Symbol.iterator] !== 'function') throw new TypeError(`Failed to execute 'postMessage' on '${what}': The provided value cannot be converted to a sequence.`);
        transfer = Array.from(options.transfer);
      }
    }
    try { return n0.serialize(message, transfer); }
    catch (e) {
      const m = String(e && e.message !== undefined ? e.message : e);
      if (m.startsWith('DataCloneError: ')) throw new DOMException(`Failed to execute 'postMessage' on '${what}': ${m.slice(16)}`, 'DataCloneError');
      throw e;
    }
  };
  const handlerProp = (proto, names) => {
    for (const name of names) Object.defineProperty(proto, 'on' + name, { get() { return handlerOf(this, name); },
      set(f) { setHandler(this, name, f); }, configurable: true, enumerable: true });
  };
  // One event for this realm (Lean queued the task with it, in order).
  const workerEvent = () => {
    const head = n.worker(3);
    if (typeof head !== 'string' || head === '') return;
    const { w, k, h } = JSON.parse(head);
    const target = inWorker ? globalThis : workerObjects.get(w);
    if (!target || (!inWorker && workerSlots.get(target).terminated)) return;
    if (k === 'message') {
      let data, ok = true;
      try { data = n0.deserialize(n.worker(4)); } catch { ok = false; }
      const e = new MessageEvent(ok ? 'message' : 'messageerror', { data: ok ? data : null, origin: '' });
      state(e).trusted = true;
      dispatch(target, e);
    } else if (k === 'error') {
      const d = JSON.parse(h);
      const init = { message: d.message, filename: d.file, lineno: d.line, colno: d.col, cancelable: true };
      const e = new ErrorEvent('error', init);
      state(e).trusted = true;
      // HTML §10.2.5: not canceled at the Worker object, it is an error of this global too.
      if (dispatch(target, e)) {
        const g = new ErrorEvent('error', init);
        state(g).trusted = true;
        if (dispatch(window, g)) { if (uncaughtHook) uncaughtHook(d.message, null); else n.log('Uncaught (in worker) ' + d.message); }
      }
    } else if (k === 'loaderror') {
      const e = new Event('error');
      state(e).trusted = true;
      dispatch(target, e);
    }
  };
  if (workersOn) callbacks.set(WORKER_EVENT, workerEvent);
  const scriptBase = () => inWorker ? href : (globalThis.document?.baseURI || href);
  const originOf = u => { try { return new URL(u).origin; } catch { return 'null'; } };
  class Worker extends EventTarget {
    constructor(scriptURL, options = undefined) {
      if (arguments.length < 1) throw new TypeError("Failed to construct 'Worker': 1 argument required, but only 0 present.");
      super();
      const o = options == null ? {} : options;
      if (typeof o !== 'object' && typeof o !== 'function') throw new TypeError("Failed to construct 'Worker': The provided value is not of type 'WorkerOptions'.");
      const type = o.type === undefined ? 'classic' : String(o.type);
      if (type !== 'classic' && type !== 'module') throw new TypeError(`Failed to construct 'Worker': The provided value '${type}' is not a valid enum value of type WorkerType.`);
      const name = o.name === undefined ? '' : String(o.name);
      const url = resolveURL(String(scriptURL), scriptBase());
      if (url === null) throw new DOMException(`Failed to construct 'Worker': The URL '${scriptURL}' is invalid.`, 'SyntaxError');
      if (type === 'module') throw new DOMException("Failed to construct 'Worker': module workers are not supported here.", 'NotSupportedError');
      const scheme = /^[a-z][a-z0-9+.-]*:/i.exec(url)?.[0] ?? '';
      if (scheme !== 'data:' && scheme !== 'blob:' && originOf(url) !== originOf(href))
        throw new DOMException(`Failed to construct 'Worker': Script at '${url}' cannot be accessed from origin '${originOf(href)}'.`, 'SecurityError');
      const id = n.worker(0, url, name);
      workerSlots.set(this, { id, terminated: false });
      workerObjects.set(id, this);
    }
    postMessage(message, options = undefined) {
      const s = workerSlots.get(this);
      if (!s) throw new TypeError("Illegal invocation");
      if (arguments.length < 1) throw new TypeError("Failed to execute 'postMessage' on 'Worker': 1 argument required, but only 0 present.");
      const bytes = cloneOut(message, options, 'Worker');
      if (!s.terminated) n.worker(1, s.id, bytes);
    }
    terminate() {
      const s = workerSlots.get(this);
      if (!s) throw new TypeError("Illegal invocation");
      if (!s.terminated) { s.terminated = true; n.worker(2, s.id); }
    }
  }
  handlerProp(Worker.prototype, ['message', 'messageerror', 'error']);
  Object.defineProperty(Worker.prototype, Symbol.toStringTag, { value: 'Worker', configurable: true });
  if (workersOn) def('Worker', Worker);
  // The globals a dedicated worker's scope keeps (HTML §10.2.1 and the [Exposed=Worker]
  // interfaces this engine has), besides the language's own (`esGlobals`).
  const workerGlobals = new Set(['self', 'console', 'setTimeout', 'setInterval', 'clearTimeout', 'clearInterval',
    'queueMicrotask', 'reportError', 'structuredClone', 'atob', 'btoa', 'WebAssembly', 'DOMException', 'EventTarget', 'Event',
    'CustomEvent', 'MessageEvent', 'ErrorEvent', 'PromiseRejectionEvent', 'ProgressEvent', 'AbortController', 'AbortSignal',
    'TextEncoder', 'TextDecoder', 'TextEncoderStream', 'TextDecoderStream', 'URL', 'URLSearchParams', 'URLPattern', 'crypto', 'Crypto',
    'SubtleCrypto', 'CryptoKey', 'performance', 'Performance', 'PerformanceEntry', 'PerformanceMark', 'PerformanceMeasure',
    'Blob', 'File', 'FileReader', 'FormData', 'Headers', 'Request', 'Response', 'fetch', 'XMLHttpRequest',
    'XMLHttpRequestEventTarget', 'XMLHttpRequestUpload', 'ReadableStream', 'WritableStream',
    'TransformStream', 'MessageChannel', 'MessagePort', 'BroadcastChannel', 'webkitURL',
    // WebGL's interfaces are [Exposed=(Window,Worker)].
    'WebGLRenderingContext', 'WebGL2RenderingContext', 'WebGLObject', 'WebGLBuffer', 'WebGLFramebuffer', 'WebGLProgram',
    'WebGLRenderbuffer', 'WebGLShader', 'WebGLTexture', 'WebGLQuery', 'WebGLSampler', 'WebGLSync', 'WebGLTransformFeedback',
    'WebGLVertexArrayObject', 'WebGLUniformLocation', 'WebGLActiveInfo', 'WebGLShaderPrecisionFormat', 'WebGLContextEvent',
    // WebCodecs' are [Exposed=(Window,DedicatedWorker)].
    'VideoColorSpace', 'VideoFrame', 'EncodedVideoChunk', 'EncodedAudioChunk', 'AudioData', 'AudioDecoder', 'VideoDecoder',
    'AudioEncoder', 'VideoEncoder', 'ImageDecoder', 'ImageTrackList', 'ImageTrack', 'DOMRectReadOnly', 'DOMRect']);
  // HTML §10.2.1: WorkerGlobalScope, DedicatedWorkerGlobalScope, WorkerLocation, WorkerNavigator.
  const makeWorkerScope = (url, name) => {
    inWorker = true;
    href = url;
    const nav = globalThis.navigator;
    class WorkerGlobalScope extends EventTarget { constructor() { throw new TypeError('Illegal constructor'); } }
    class DedicatedWorkerGlobalScope extends WorkerGlobalScope { constructor() { throw new TypeError('Illegal constructor'); } }
    const parts = new WeakMap();
    class WorkerLocation { constructor() { throw new TypeError('Illegal constructor'); } toString() { return parts.get(this).href; } }
    for (const k of ['href', 'origin', 'protocol', 'host', 'hostname', 'port', 'pathname', 'search', 'hash'])
      Object.defineProperty(WorkerLocation.prototype, k, { get() { return parts.get(this)[k]; }, configurable: true, enumerable: true });
    class WorkerNavigator { constructor() { throw new TypeError('Illegal constructor'); } }
    for (const k of ['userAgent', 'language', 'languages', 'platform', 'onLine', 'hardwareConcurrency'])
      Object.defineProperty(WorkerNavigator.prototype, k, { get() { return nav[k]; }, configurable: true, enumerable: true });
    for (const [k, v] of [['appCodeName', 'Mozilla'], ['appName', 'Netscape'], ['product', 'Gecko']])
      Object.defineProperty(WorkerNavigator.prototype, k, { get() { return v; }, configurable: true, enumerable: true });
    Object.defineProperty(WorkerNavigator.prototype, 'appVersion', { get() { return String(nav.userAgent).replace(/^Mozilla\//, ''); }, configurable: true, enumerable: true });
    const u = new URL(url);
    const loc = Object.create(WorkerLocation.prototype);
    parts.set(loc, { href: u.href, origin: u.origin, protocol: u.protocol, host: u.host, hostname: u.hostname, port: u.port,
      pathname: u.pathname, search: u.search, hash: u.hash });
    const wnav = Object.create(WorkerNavigator.prototype);
    for (const k of Object.getOwnPropertyNames(globalThis))
      if (!esGlobals.has(k) && !workerGlobals.has(k)) { try { delete globalThis[k]; } catch {} }
    Object.setPrototypeOf(globalThis, DedicatedWorkerGlobalScope.prototype);
    const WP = WorkerGlobalScope.prototype, DP = DedicatedWorkerGlobalScope.prototype;
    const getter = (o, k, f) => Object.defineProperty(o, k, { get: f, configurable: true, enumerable: true });
    getter(WP, 'self', function () { return globalThis; });
    getter(WP, 'location', () => loc);
    getter(WP, 'navigator', () => wnav);
    getter(WP, 'origin', () => u.origin);
    getter(WP, 'isSecureContext', () => u.protocol === 'https:' || u.hostname === 'localhost' || u.hostname === '127.0.0.1');
    getter(WP, 'crossOriginIsolated', () => false);
    define(WP, 'importScripts', function importScripts(...urls) {
      const abs = urls.map(x => {
        const r = resolveURL(String(x), href);
        if (r === null) throw new DOMException(`Failed to execute 'importScripts' on 'WorkerGlobalScope': The URL '${x}' is invalid.`, 'SyntaxError');
        return r;
      });
      for (const a of abs) {
        const src = n.worker(12, a);
        // -1: the embedder fetches it now; Lean undoes this run and runs it again then.
        if (src === -1) throw new DOMException(`importScripts: '${a}' is being fetched.`, 'NetworkError');
        if (typeof src !== 'string') throw new DOMException(`Failed to execute 'importScripts' on 'WorkerGlobalScope': The script at '${a}' failed to load.`, 'NetworkError');
        n0.runScript(src);
      }
    });
    getter(DP, 'name', () => name);
    define(DP, 'postMessage', function postMessage(message, options = undefined) {
      if (arguments.length < 1) throw new TypeError("Failed to execute 'postMessage' on 'DedicatedWorkerGlobalScope': 1 argument required, but only 0 present.");
      n.worker(1, 0, cloneOut(message, options, 'DedicatedWorkerGlobalScope'));
    });
    define(DP, 'close', function close() { n.worker(10); });
    handlerProp(WP, ['error', 'languagechange', 'offline', 'online', 'rejectionhandled', 'unhandledrejection']);
    handlerProp(DP, ['message', 'messageerror']);
    Object.defineProperty(WP, Symbol.toStringTag, { value: 'WorkerGlobalScope', configurable: true });
    Object.defineProperty(DP, Symbol.toStringTag, { value: 'DedicatedWorkerGlobalScope', configurable: true });
    for (const [k, v] of Object.entries({ WorkerGlobalScope, DedicatedWorkerGlobalScope, WorkerLocation, WorkerNavigator })) def(k, v);
    uncaughtHook = (message, e) => n.worker(11, message, href, 0, 0);
  };
  // ==== end workers ====

  // Content event handler attributes (HTML §8.1.8.1): onclick="..." and <body onload>.
  // The event handler content attributes of the elements of a subtree (a page's, or a clone's:
  // a clone's attributes are set by Lean, not through setAttribute).
  const scanHandlers = (root, inclusive) => {
    for (const k of inclusive && info(root, 0) === 1 ? [root, ...elementsOf(root)] : elementsOf(root)) {
      // HTML, SVG and MathML elements have event handler content attributes
      if (!htmlEl(k)) { const ns = str(k, 2); if (ns !== 'http://www.w3.org/2000/svg' && ns !== 'http://www.w3.org/1998/Math/MathML') continue; }
      const a = str(k, 6) ?? ''; const xs = a === '' ? [] : a.split('\u0000');
      for (let i = 0; i + 1 < xs.length; i += 2) if (/^on[a-z]+$/.test(xs[i])) contentHandler(wrap(k), xs[i].slice(2), xs[i + 1]);
    }
  };
  // An attribute is compiled as an event handler only when Lean's table of event handler
  // content attributes names it (HTML.TrustedTypes.isEventHandlerName, asked once for each
  // name): so every attribute that can run script is a TrustedScript sink there.
  const handlerNamed = new Map();
  const handlerName = name => { let v = handlerNamed.get(name); if (v === undefined) handlerNamed.set(name, v = n.query(0, 194, 'h\u0000on' + name) === '1'); return v; };
  const contentHandler = (el, name, source) => {
    if (!handlerNames.includes(name) || !handlerName(name) || !(el instanceof HTMLElement || el instanceof SVGElement || el instanceof MathMLElement)) return;
    const onBody = windowReflecting(el) && bodyWindowHandlers.has(name);
    const t = onBody ? bodyWindow(el) : el;
    // HTML "getting the current value of the event handler": the window's onerror handler has
    // the parameters event, source, lineno, colno and error. A source that does not compile
    // sets the handler to null (replacing an earlier one) and the error is reported.
    const winError = onBody && name === 'error';
    let f;
    try { f = winError ? new Function('event', 'source', 'lineno', 'colno', 'error', source) : new Function('event', source); }
    catch (e) { setHandler(t, name, null); report(e); return; }
    setHandler(t, name, f);
  };

  // ==== forms: the script interface of form controls (HTML §4.10) ========================
  // The collections and the selectedness are Lean's (DOM.FormControls, node_query 186): "f"
  // form owner, "e" the elements of a form, "o" the options of a select, "s" its selected
  // options, "l" the labels of a control, "c" a label's control, "x" an option's
  // selectedness; tree_op 6 sets an option's selectedness. The selection of a text control is
  // the page's state; `setRangeText`'s arithmetic is Lean's (HTML.TextSelection, 187).
  // A textarea's value is its text content and an input's its `value` attribute, as before
  // (there is no separate dirty value yet).
  {
    const fq = (el, q) => { const r = n.query(nodeId(el), 186, q); return typeof r === 'string' ? r : ''; };
    const idsOf = r => (r === '' ? [] : r.split(' ').map(Number));
    const one = r => (r === '' ? null : wrap(Number(r)));
    const prop = (C, name, get, set) => Object.defineProperty(C.prototype, name, { get, set, configurable: true, enumerable: true });
    const method = (C, name, f) => Object.defineProperty(C.prototype, name, { value: f, writable: true, configurable: true, enumerable: true });
    const I = named.HTMLInputElement, S = named.HTMLSelectElement, O = named.HTMLOptionElement, T = named.HTMLTextAreaElement,
      F = named.HTMLFormElement, L = named.HTMLLabelElement, B = named.HTMLButtonElement, OUT = named.HTMLOutputElement,
      FS = named.HTMLFieldSetElement;
    const isIndex = p => typeof p === 'string' && /^(0|[1-9][0-9]*)$/.test(p);
    const task = f => { chk(n.timer(register(f), 0, 0)); };

    // ---- collections with named items ----
    class HTMLFormControlsCollection extends HTMLCollection {}
    class HTMLOptionsCollection extends HTMLCollection {}
    class RadioNodeList extends NodeList {}
    def('HTMLFormControlsCollection', HTMLFormControlsCollection); def('HTMLOptionsCollection', HTMLOptionsCollection); def('RadioNodeList', RadioNodeList);
    const radioIds = new WeakMap(), ownerOf = new WeakMap();
    const namedIn = (ks, name) => (name === '' ? [] : ks.filter(k => n0.attr(k, 'id') === name || n0.attr(k, 'name') === name));
    const radioList = ids => { const l = liveList(ids, RadioNodeList.prototype); radioIds.set(l, ids); return l; };
    prop(RadioNodeList, 'value', function () {
      for (const k of radioIds.get(this)()) if (str(k, 0) === 'input' && chk(n.query(k, 14, '')) === 'radio' && chk(n.treeOp(k, 0, 7)) === 1) return n0.attr(k, 'value') ?? 'on';
      return '';
    }, function (v) {
      v = String(v);
      for (const k of radioIds.get(this)()) if (str(k, 0) === 'input' && chk(n.query(k, 14, '')) === 'radio' && (typeof n0.attr(k, 'value') === 'string' ? n0.attr(k, 'value') : 'on') === v) { chk(n.treeOp(k, 1, 6)); return; }
    });
    // `radio`: several controls of one name are a RadioNodeList (form.elements), else the first
    const collectionOf = (ids, proto, radio) => {
      const item = name => { const xs = namedIn(ids(), name); return xs.length === 0 ? null : xs.length === 1 || !radio ? wrap(xs[0]) : radioList(() => namedIn(ids(), name)); };
      const c = new Proxy(Object.create(proto), {
        get(t, p, recv) {
          if (isIndex(p)) { const k = ids()[Number(p)]; return k === undefined ? undefined : wrap(k); }
          if (p === 'length') return ids().length;
          if (p === 'namedItem') return name => item(String(name));
          if (typeof p === 'string' && !(p in t)) { const x = item(p); if (x !== null) return x; }
          return Reflect.get(t, p, recv);
        },
        // an accessor of the interface (`length`, `selectedIndex`) is called on the collection
        set(t, p, v, recv) {
          if (isIndex(p)) return false;
          for (let o = t; o; o = Object.getPrototypeOf(o)) { const d = Object.getOwnPropertyDescriptor(o, p); if (d) { if (d.set) { d.set.call(recv, v); return true; } break; } }
          return Reflect.set(t, p, v, recv);
        },
        defineProperty(t, p, desc) { if (isIndex(p)) return false; return Reflect.defineProperty(t, p, desc); },
        has(t, p) { if (isIndex(p)) return Number(p) < ids().length; return p === 'length' || Reflect.has(t, p) || (typeof p === 'string' && namedIn(ids(), p).length > 0); },
        ownKeys() { return [...ids().keys()].map(String); },
        getOwnPropertyDescriptor(t, p) {
          if (isIndex(p) && Number(p) < ids().length) return { value: wrap(ids()[Number(p)]), enumerable: true, configurable: true, writable: false };
          return undefined;
        },
      });
      return c;
    };
    const cachedColl = () => { const m = new WeakMap(); return (el, make) => { let c = m.get(el); if (!c) m.set(el, c = make()); return c; }; };

    // ---- form ----
    const formElements = cachedColl();
    prop(F, 'elements', function () { const f = this; return formElements(f, () => collectionOf(() => idsOf(fq(f, 'e')), HTMLFormControlsCollection.prototype, true)); });
    prop(F, 'length', function () { return idsOf(fq(this, 'e')).length; });

    // ---- label and labels ----
    prop(L, 'control', function () { return one(fq(this, 'c')); });
    prop(L, 'form', function () { const c = one(fq(this, 'c')); return c ? formOf(c) : null; });
    const labelLists = cachedColl();
    const labelsGetter = function () { const el = this; return labelLists(el, () => liveList(() => idsOf(fq(el, 'l')))); };
    for (const C of [B, S, T, OUT, named.HTMLMeterElement, named.HTMLProgressElement]) prop(C, 'labels', labelsGetter);
    prop(I, 'labels', function () { return typeState(this) === 'hidden' ? null : labelsGetter.call(this); });
    for (const C of [S, T, OUT, FS, named.HTMLObjectElement]) prop(C, 'form', function () { return formOf(this); });

    // ---- select and option ----
    const optionIds = sel => idsOf(fq(sel, 'o')), selectedIds = sel => idsOf(fq(sel, 's'));
    // the nearest ancestor select of an option
    const selectOf = o => { for (let p = o.parentNode; p; p = p.parentNode) if (p instanceof S) return p; return null; };
    const setSelected = (k, v) => { chk(n.treeOp(k, v ? 1 : 0, 6)); };
    const optionsOf = cachedColl(), selectedOf = cachedColl();
    prop(S, 'options', function () { const sel = this; return optionsOf(sel, () => { const c = collectionOf(() => optionIds(sel), HTMLOptionsCollection.prototype, false); ownerOf.set(c, sel); return c; }); });
    prop(S, 'selectedOptions', function () { const sel = this; return selectedOf(sel, () => liveCollection(() => selectedIds(sel))); });
    prop(S, 'length', function () { return optionIds(this).length; }, function (v) {
      v = v >>> 0;
      const ks = optionIds(this);
      if (v > 100000) return;
      for (let i = ks.length - 1; i >= v; i--) wrap(ks[i]).remove();
      for (let i = ks.length; i < v; i++) this.appendChild(this.ownerDocument.createElement('option'));
    });
    method(S, 'item', function item(i) { const k = optionIds(this)[i >>> 0]; return k === undefined ? null : wrap(k); });
    method(S, 'namedItem', function namedItem(name) { const xs = namedIn(optionIds(this), String(name)); return xs.length ? wrap(xs[0]) : null; });
    method(S, 'add', function add(element, before = null) {
      if (!(element instanceof O) && !(element instanceof named.HTMLOptGroupElement)) throw new TypeError("Failed to execute 'add' on 'HTMLSelectElement': parameter 1 is not an option or an optgroup.");
      let ref = null;
      if (before !== null && before !== undefined) ref = before instanceof Element ? before : this.item(before);
      for (let a = this; a; a = a.parentNode) if (a === element) throw new DOMException('The element is an ancestor of the select.', 'HierarchyRequestError');
      (ref ? ref.parentNode : this).insertBefore(element, ref);
    });
    method(S, 'remove', function remove(index) {
      if (arguments.length === 0) { Element.prototype.remove.call(this); return; }
      const k = optionIds(this)[index | 0]; if (k !== undefined) wrap(k).remove();
    });
    prop(S, 'selectedIndex', function () { const s = selectedIds(this); return s.length ? optionIds(this).indexOf(s[0]) : -1; }, function (v) {
      v = v | 0;
      const ks = optionIds(this);
      for (const k of ks) setSelected(k, false);
      if (v >= 0 && v < ks.length) setSelected(ks[v], true);
    });
    prop(S, 'value', function () { const s = selectedIds(this); return s.length ? wrap(s[0]).value : ''; }, function (v) {
      v = String(v);
      const ks = optionIds(this);
      for (const k of ks) setSelected(k, false);
      for (const k of ks) if (wrap(k).value === v) { setSelected(k, true); break; }
    });
    prop(S, 'type', function () { return this.hasAttribute('multiple') ? 'select-multiple' : 'select-one'; });
    HTMLOptionsCollection.prototype.add = function add(element, before = null) { ownerOf.get(this).add(element, before); };
    HTMLOptionsCollection.prototype.remove = function remove(index) { ownerOf.get(this).remove(index | 0); };
    Object.defineProperty(HTMLOptionsCollection.prototype, 'length', { get() { return ownerOf.get(this).length; }, set(v) { ownerOf.get(this).length = v; }, configurable: true, enumerable: true });
    Object.defineProperty(HTMLOptionsCollection.prototype, 'selectedIndex', { get() { return ownerOf.get(this).selectedIndex; }, set(v) { ownerOf.get(this).selectedIndex = v; }, configurable: true, enumerable: true });
    prop(O, 'selected', function () { const sel = selectOf(this); return sel ? selectedIds(sel).includes(nodeId(this)) : fq(this, 'x') === '1'; }, function (v) {
      const id = nodeId(this), sel = selectOf(this);
      setSelected(id, !!v);
      if (v && sel && !sel.hasAttribute('multiple')) for (const k of optionIds(sel)) if (k !== id) setSelected(k, false);
    });
    prop(O, 'index', function () { const sel = selectOf(this); return sel ? Math.max(0, optionIds(sel).indexOf(nodeId(this))) : 0; });
    prop(O, 'form', function () { const sel = selectOf(this); return sel ? formOf(sel) : null; });
    prop(O, 'text', function () { return this.textContent.replace(/[\t\n\f\r ]+/g, ' ').replace(/^ | $/g, ''); }, function (v) { this.textContent = v; });
    const OptionFactory = function Option(text = undefined, value = undefined, defaultSelected = false, selected = false) {
      if (!new.target) throw new TypeError("Failed to construct 'Option': Please use the 'new' operator.");
      const o = (scriptDocument ?? document).createElement('option');
      if (text !== undefined && String(text) !== '') o.textContent = String(text);
      if (value !== undefined) o.setAttribute('value', String(value));
      if (defaultSelected) o.setAttribute('selected', '');
      if (selected) setSelected(nodeId(o), true);
      return o;
    };
    OptionFactory.prototype = O.prototype; def('Option', OptionFactory);
    const ImageFactory = function Image(width = undefined, height = undefined) {
      if (!new.target) throw new TypeError("Failed to construct 'Image': Please use the 'new' operator.");
      const img = (scriptDocument ?? document).createElement('img');
      if (width !== undefined) img.setAttribute('width', String(width >>> 0));
      if (height !== undefined) img.setAttribute('height', String(height >>> 0));
      return img;
    };
    ImageFactory.prototype = named.HTMLImageElement.prototype; def('Image', ImageFactory);

    // ---- textarea, output, fieldset ----
    prop(T, 'value', function () { return this.textContent.replace(/\r\n?/g, '\n'); }, function (v) {
      v = v === null ? '' : String(v);
      if (v !== this.textContent) { this.textContent = v; selOf(this).start = selOf(this).end = v.length; selOf(this).dir = 'none'; }
    });
    prop(T, 'defaultValue', function () { return this.textContent; }, function (v) { this.textContent = String(v); });
    prop(T, 'textLength', function () { return this.value.length; });
    prop(T, 'type', function () { return 'textarea'; });
    prop(OUT, 'value', function () { return this.textContent; }, function (v) { this.textContent = String(v); });
    prop(OUT, 'defaultValue', function () { return this.textContent; }, function (v) { this.textContent = String(v); });
    prop(OUT, 'type', function () { return 'output'; });
    prop(FS, 'type', function () { return 'fieldset'; });
    const fieldsetElements = cachedColl();
    prop(FS, 'elements', function () { const fs = this; return fieldsetElements(fs, () => collectionOf(() => [...fs.querySelectorAll('button,fieldset,input,object,output,select,textarea')].map(nodeId), HTMLFormControlsCollection.prototype, true)); });

    // ---- input: the members that are not plain reflection ----
    const indeterminate = new WeakMap();
    prop(I, 'indeterminate', function () { return indeterminate.get(this) === true; }, function (v) { indeterminate.set(this, !!v); });
    prop(I, 'list', function () {
      const id = this.getAttribute('list');
      if (id === null || id === '') return null;
      const root = this.getRootNode(), el = root.getElementById ? root.getElementById(id) : root.querySelector('#' + CSSns.escape(id));
      return el instanceof named.HTMLDataListElement ? el : null;
    });
    prop(I, 'files', function () { return null; });

    // ---- the selection of a text control (HTML §4.10.20) ----
    const selState = new WeakMap();
    const selOf = el => { let s = selState.get(el); if (!s) selState.set(el, s = { start: 0, end: 0, dir: 'none' }); return s; };
    const selects = el => el instanceof T || ['text', 'search', 'url', 'tel', 'password'].includes(typeState(el));
    const needSel = (el, what) => { if (!selects(el)) throw new DOMException(`Failed to read or set '${what}': the element's type does not have a text selection.`, 'InvalidStateError'); };
    const fireSelect = el => task(() => { const e = new Event('select', { bubbles: true }); state(e).trusted = true; dispatch(el, e); });
    // "Set the selection range": the end at most the length, the start at most the end.
    const setSel = (el, start, end, dir) => {
      const len = el.value.length, s = selOf(el);
      end = end === null || end === undefined ? len : Math.min(end, len);
      start = Math.min(start === null || start === undefined ? 0 : start, end);
      dir = dir === 'backward' || dir === 'forward' ? dir : 'none';
      const changed = s.start !== start || s.end !== end || s.dir !== dir;
      s.start = start; s.end = end; s.dir = dir;
      if (changed) fireSelect(el);
    };
    const clamp = (el, x) => Math.min(x, el.value.length);
    for (const C of [I, T]) {
      prop(C, 'selectionStart', function () { return selects(this) ? clamp(this, selOf(this).start) : null; },
        function (v) { needSel(this, 'selectionStart'); const s = selOf(this); v = v === null ? 0 : v >>> 0; setSel(this, v, Math.max(clamp(this, s.end), v), s.dir); });
      prop(C, 'selectionEnd', function () { return selects(this) ? clamp(this, selOf(this).end) : null; },
        function (v) { needSel(this, 'selectionEnd'); const s = selOf(this); setSel(this, clamp(this, s.start), v === null ? 0 : v >>> 0, s.dir); });
      prop(C, 'selectionDirection', function () { return selects(this) ? selOf(this).dir : null; },
        function (v) { needSel(this, 'selectionDirection'); const s = selOf(this); setSel(this, clamp(this, s.start), clamp(this, s.end), String(v)); });
      method(C, 'setSelectionRange', function setSelectionRange(start, end, direction = undefined) {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'setSelectionRange': 2 arguments required.");
        needSel(this, 'setSelectionRange');
        setSel(this, start >>> 0, end >>> 0, direction === undefined ? 'none' : String(direction));
      });
      method(C, 'select', function select() {
        if (this instanceof I && ['hidden', 'checkbox', 'radio', 'submit', 'image', 'reset', 'button', 'range', 'file', 'color'].includes(typeState(this))) return;
        setSel(this, 0, null, 'none');
      });
      method(C, 'setRangeText', function setRangeText(replacement, start = undefined, end = undefined, selectionMode = 'preserve') {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'setRangeText': 1 argument required.");
        needSel(this, 'setRangeText');
        replacement = String(replacement);
        const s = selOf(this), value = this.value;
        if (arguments.length === 1) { start = clamp(this, s.start); end = clamp(this, s.end); }
        else { if (arguments.length < 3) throw new TypeError("Failed to execute 'setRangeText': 3 arguments required."); start = start >>> 0; end = end >>> 0; }
        if (start > end) throw new DOMException('The start is greater than the end.', 'IndexSizeError');
        const mode = String(selectionMode);
        if (!['select', 'start', 'end', 'preserve'].includes(mode)) throw new TypeError(`Failed to execute 'setRangeText': '${mode}' is not a valid SelectionMode.`);
        const r = chk(n.query(0, 187, [value.length, start, end, clamp(this, s.start), clamp(this, s.end), replacement.length, mode].join(' '))).split(' ').map(Number);
        const next = value.slice(0, r[0]) + replacement + value.slice(r[1]);
        const dir = s.dir;
        if (next !== value) { if (this instanceof T) this.textContent = next; else this.setAttribute('value', next); }
        setSel(this, r[2], r[3], mode === 'preserve' ? dir : 'none');
      });
    }
    // ---- the typed value of an input, stepping and constraint validation (HTML §4.10.5,
    // §4.10.21): Lean's (DOM.FormValidity over HTML.InputValue, node_query 188) ----
    const vq = (el, ...parts) => { const r = n.query(nodeId(el), 188, parts.join('\u0000')); return typeof r === 'string' ? r : ''; };
    const numericTypes = ['date', 'month', 'week', 'time', 'datetime-local', 'number', 'range'];
    // The value (HTML §4.10.5.1.x "value sanitization"): the `value` attribute as the type reads
    // it. A one-line text needs no sanitizing, so no question is asked for it.
    const inputValue = el => {
      const t = typeState(el), raw = el.getAttribute('value');
      if (t === 'hidden' || t === 'submit' || t === 'image' || t === 'reset' || t === 'button') return raw ?? '';
      if (t === 'checkbox' || t === 'radio') return raw ?? 'on';
      if (t === 'file') return '';
      const v = raw ?? '';
      if ((t === 'text' || t === 'search' || t === 'tel' || t === 'password') && !/[\r\n]/.test(v)) return v;
      return vq(el, 'S', v);
    };
    prop(I, 'value', function () { return inputValue(this); }, function (v) {
      v = v === null ? '' : String(v);
      if (typeState(this) === 'file') { if (v !== '') throw new DOMException('The value of a file input can only be set to the empty string.', 'InvalidStateError'); return; }
      const before = inputValue(this);
      this.setAttribute('value', v);
      const now = inputValue(this);
      // a value that a script sets moves the cursor to its end
      if (now !== before) { const s = selOf(this); s.start = s.end = now.length; s.dir = 'none'; }
    });
    const step = (el, dir, k) => {
      const r = vq(el, dir, inputValue(el), String(k === undefined ? 1 : k | 0));
      if (r === 'e' || r === '') throw new DOMException('The element has no allowed value step.', 'InvalidStateError');
      if (r[0] === 'v') el.value = r.slice(1);
    };
    method(I, 'stepUp', function stepUp(n = 1) { step(this, '+', n); });
    method(I, 'stepDown', function stepDown(n = 1) { step(this, '-', n); });
    prop(I, 'valueAsNumber', function () { const r = vq(this, 'N', inputValue(this)); return r === '' ? NaN : Number(r); }, function (v) {
      v = Number(v);
      if (!numericTypes.includes(typeState(this))) throw new DOMException('This input type has no value as a number.', 'InvalidStateError');
      if (v === Infinity || v === -Infinity) throw new TypeError("Failed to set the 'valueAsNumber' property: the value is infinite.");
      const r = Number.isNaN(v) ? '' : vq(this, 'n', String(v));
      this.value = r[0] === 'v' ? r.slice(1) : '';
    });
    prop(I, 'valueAsDate', function () {
      if (!['date', 'month', 'week', 'time'].includes(typeState(this))) return null;
      const r = vq(this, 'D', inputValue(this)); return r === '' ? null : new Date(Number(r));
    }, function (v) {
      if (!['date', 'month', 'week', 'time'].includes(typeState(this))) throw new DOMException('This input type has no value as a date.', 'InvalidStateError');
      if (v === null) { this.value = ''; return; }
      if (!(v instanceof Date)) throw new TypeError("Failed to set the 'valueAsDate' property: the value is not a Date.");
      const r = Number.isNaN(v.getTime()) ? '' : vq(this, 'd', String(v.getTime()));
      this.value = r[0] === 'v' ? r.slice(1) : '';
    });
    method(I, 'showPicker', function showPicker() {
      if (this.hasAttribute('disabled') || this.hasAttribute('readonly')) throw new DOMException('The input is not mutable.', 'InvalidStateError');
      throw new DOMException('showPicker() needs a user gesture.', 'NotAllowedError');
    });

    class ValidityState { constructor() { throw new TypeError('Illegal constructor'); } }
    def('ValidityState', ValidityState);
    const validityEl = new WeakMap(), validityObj = new WeakMap(), customMessage = new WeakMap();
    const patternMismatch = el => {
      const p = el.getAttribute('pattern'), t = typeState(el);
      if (p === null || !['text', 'search', 'url', 'tel', 'email', 'password'].includes(t)) return false;
      const v = inputValue(el);
      if (v === '') return false;
      let re;
      try { re = new RegExp('^(?:' + p + ')$', 'v'); } catch { try { re = new RegExp('^(?:' + p + ')$', 'u'); } catch { return false; } }
      return t === 'email' && el.hasAttribute('multiple') ? !v.split(',').every(x => re.test(x)) : !re.test(v);
    };
    // The validity states as bits: 1 valueMissing, 2 typeMismatch, 4 patternMismatch, 8 tooLong,
    // 16 tooShort, 32 rangeUnderflow, 64 rangeOverflow, 128 stepMismatch, 256 badInput,
    // 512 customError. Lean decides 1, 2, 32, 64 and 128; the pattern is a JavaScript regular
    // expression; tooLong and tooShort need a user edit, which a script's value is not.
    const validityBits = el => {
      let bits = 0;
      if (el instanceof I) { bits = Number(vq(el, 'V', inputValue(el))) || 0; if (patternMismatch(el)) bits |= 4; }
      else if (el instanceof T) bits = Number(vq(el, 'V', el.value)) || 0;
      else if (el instanceof S) bits = Number(vq(el, 'V', '')) || 0;
      if ((customMessage.get(el) ?? '') !== '') bits |= 512;
      return bits;
    };
    ['valueMissing', 'typeMismatch', 'patternMismatch', 'tooLong', 'tooShort', 'rangeUnderflow', 'rangeOverflow', 'stepMismatch', 'badInput', 'customError']
      .forEach((name, i) => prop(ValidityState, name, function () { return (validityBits(validityEl.get(this)) & (1 << i)) !== 0; }));
    prop(ValidityState, 'valid', function () { return validityBits(validityEl.get(this)) === 0; });
    const messages = ['Please fill out this field.', 'Please enter a value of the right type.', 'Please match the requested format.', 'Please shorten this text.',
      'Please lengthen this text.', 'The value is too low.', 'The value is too high.', 'Please enter a valid value.', 'Please enter a valid value.'];
    const willValidate = el => vq(el, 'W') === '1';
    const check = el => {
      if (!willValidate(el) || validityBits(el) === 0) return true;
      const e = new Event('invalid', { cancelable: true }); state(e).trusted = true; dispatch(el, e);
      return false;
    };
    for (const C of [I, T, S, B, OUT, FS, named.HTMLObjectElement]) {
      prop(C, 'willValidate', function () { return willValidate(this); });
      prop(C, 'validity', function () { let v = validityObj.get(this); if (!v) { v = Object.create(ValidityState.prototype); validityEl.set(v, this); validityObj.set(this, v); } return v; });
      prop(C, 'validationMessage', function () {
        if (!willValidate(this)) return '';
        const bits = validityBits(this);
        if (bits & 512) return customMessage.get(this);
        for (let i = 0; i < 9; i++) if (bits & (1 << i)) return messages[i];
        return '';
      });
      method(C, 'checkValidity', function checkValidity() { return check(this); });
      method(C, 'reportValidity', function reportValidity() { return check(this); });
      method(C, 'setCustomValidity', function setCustomValidity(message) {
        if (arguments.length < 1) throw new TypeError("Failed to execute 'setCustomValidity': 1 argument required.");
        customMessage.set(this, String(message));
      });
    }
    // "Statically validate the constraints" of a form (HTML §4.10.21.3)
    const checkForm = form => { let ok = true; for (const k of idsOf(fq(form, 'e'))) if (!check(wrap(k))) ok = false; return ok; };
    method(F, 'checkValidity', function checkValidity() { return checkForm(this); });
    method(F, 'reportValidity', function reportValidity() { return checkForm(this); });
  }
  // ---- new FormData(form, submitter) (XMLHttpRequest §5.3; HTML §4.10.21.4) -----------------
  // Which controls contribute and what each gives is Lean's (HTML.FormEntries, node_query
  // 196); here the checks' exceptions, the empty file of a file control and the formdata event.
  {
    const formData = new WeakMap();
    class FormDataEvent extends Event {
      constructor(type, init = undefined) {
        if (arguments.length < 2 || init === null || typeof init !== 'object' || !(init.formData instanceof globalThis.FormData))
          throw new TypeError("Failed to construct 'FormDataEvent': member formData is required and must be an instance of FormData.");
        super(type, init);
        formData.set(this, init.formData);
      }
      get formData() { return formData.get(this); }
    }
    def('FormDataEvent', FormDataEvent);
    const constructing = new Set();
    const unesc = t => t.replace(/\u0007([\s\S])/g, (m, c) => String.fromCharCode(c.charCodeAt(0) - 64));
    formEntryList = (form, submitter, make, read) => {
      const what = "Failed to construct 'FormData'";
      if (!(form instanceof named.HTMLFormElement)) throw new TypeError(`${what}: parameter 1 is not of type 'HTMLFormElement'.`);
      if (submitter !== null && !(submitter instanceof HTMLElement)) throw new TypeError(`${what}: parameter 2 is not of type 'HTMLElement'.`);
      const id = nodeId(form);
      const r = op(id, 196, submitter === null ? '' : String(nodeId(submitter)));
      if (r[0] === 'T') throw new TypeError(`${what}: The specified element is not a submit button.`);
      if (r[0] === 'N') throw new DOMException(`${what}: The specified element is not owned by this form element.`, 'NotFoundError');
      if (constructing.has(id)) throw new DOMException(`${what}: The form is constructing its entry list.`, 'InvalidStateError');
      const entries = r.length === 1 ? [] : r.slice(1).split('\u0002').map(e => {
        const [name, value, file] = e.split('\u0001');
        return [unesc(name), file === '1' ? new globalThis.File([], '', { type: 'application/octet-stream' }) : unesc(value)];
      });
      const fd = make(entries);
      constructing.add(id);
      try { const e = new FormDataEvent('formdata', { bubbles: true, formData: fd }); state(e).trusted = true; dispatch(form, e); }
      finally { constructing.delete(id); }
      return read(fd);
    };
  }
  // ==== end forms =========================================================================

  // ==== innertext: innerText and outerText (HTML §3.2.7) ==================================
  // The getter walks the element's rendered subtree with Lean's computed styles and gives
  // Lean the items of the "rendered text collection steps" (text runs with their white-space
  // behaviour, br, the tab and line feed of table cells and rows, required line breaks); the
  // text (white space collapsed, line breaks merged) is Lean's: HTML.InnerText, node_query 190.
  {
    const cv = (el, name) => computedValue(el, name);
    const parentOf = e => { const p = e.parentNode; return p instanceof ShadowRoot ? p.host : p; };
    const rendered = el => { if (!el.isConnected) return false; for (let e = el; e instanceof Element; e = parentOf(e)) if (cv(e, 'display') === 'none') return false; return true; };
    const blocks = new Set(['block', 'flow-root', 'flex', 'grid', 'table', 'list-item', 'table-caption']);
    const wsLetter = el => { const w = cv(el, 'white-space'); return w === 'pre' || w === 'pre-wrap' || w === 'break-spaces' ? 'p' : w === 'pre-line' ? 'l' : 'c'; };
    const transformed = (el, text) => {
      const t = cv(el, 'text-transform');
      return t === 'uppercase' ? text.toUpperCase() : t === 'lowercase' ? text.toLowerCase()
        : t === 'capitalize' ? text.replace(/(^|[\t\n\f\r ])([^\t\n\f\r ])/g, (m, a, b) => a + b.toUpperCase()) : text;
    };
    const visibleEl = el => { const v = cv(el, 'visibility'); return v !== 'hidden' && v !== 'collapse'; };
    // the items of the children of `el` (its own text runs are written when it is visible)
    const children = (el, out, visible) => {
      let letter = null;
      for (const c of el.childNodes) {
        if (c.nodeType === 3) { if (visible) { letter ??= wsLetter(el); out.push(letter + transformed(el, c.data).replace(/\u0000/g, '�')); } }
        else if (c.nodeType === 1) collect(c, out);
      }
    };
    const collect = (el, out) => {
      const display = cv(el, 'display');
      if (display === 'none') return;
      const visible = visibleEl(el), html = htmlEl(nodeId(el)), name = el.localName;
      if (html && name === 'br') { if (visible) out.push('b'); return; }
      const block = blocks.has(display), p = html && name === 'p';
      if (visible) { if (p) out.push('n2'); if (block) out.push('n1'); }
      children(el, out, visible);
      if (!visible) return;
      if (display === 'table-cell' && el.nextElementSibling !== null) out.push('t\t');
      if (display === 'table-row' && (el.nextElementSibling !== null || (el.parentNode instanceof Element && cv(el.parentNode, 'display').startsWith('table-') && el.parentNode.nextElementSibling !== null))) out.push('t\n');
      if (p) out.push('n2');
      if (block) out.push('n1');
    };
    const textOf = el => {
      if (!rendered(el)) return el.textContent;
      const out = [];
      children(el, out, visibleEl(el));
      const r = n.query(0, 191, out.join('\u0000'));
      // an engine without op 190, or more text than one question holds: the text content
      return typeof r === 'string' ? r : el.textContent;
    };
    // The fragment of the setters: the lines of the text, a `br` between two of them.
    const fragmentOf = (el, v) => {
      const doc = el.ownerDocument, f = doc.createDocumentFragment();
      v.split(/\r\n|\r|\n/).forEach((line, i) => {
        if (i > 0) f.appendChild(doc.createElement('br'));
        if (line !== '') f.appendChild(doc.createTextNode(line));
      });
      return f;
    };
    Object.defineProperty(HTMLElement.prototype, 'innerText', { get() { return textOf(this); }, set(v) {
      const f = fragmentOf(this, v === null ? '' : String(v));
      this.textContent = '';
      if (f.firstChild) this.appendChild(f);
    }, configurable: true, enumerable: true });
    Object.defineProperty(HTMLElement.prototype, 'outerText', { get() { return textOf(this); }, set(v) {
      const parent = this.parentNode;
      if (parent === null) throw new DOMException('The element has no parent.', 'NoModificationAllowedError');
      const next = this.nextSibling, prev = this.previousSibling;
      const f = fragmentOf(this, String(v));
      if (!f.firstChild) f.appendChild(this.ownerDocument.createTextNode(''));
      parent.replaceChild(f, this);
      // adjacent Text nodes are merged, as the setter's steps 7 and 8 say
      if (next !== null && next.nodeType === 3 && next.previousSibling !== null && next.previousSibling.nodeType === 3) { next.previousSibling.data += next.data; next.remove(); }
      if (prev !== null && prev.nodeType === 3 && prev.nextSibling !== null && prev.nextSibling.nodeType === 3) { const m = prev.nextSibling; prev.data += m.data; m.remove(); }
    }, configurable: true, enumerable: true });
  }
  // ==== end innertext =====================================================================

  // ==== focus: the focused element (HTML §6.6) ============================================
  // Which node `focus()` focuses is Lean's (DOM.Focus, node_query 189: the element when it is
  // a focusable area, else the first focusable area of a shadow tree that delegates focus).
  // The focused element is the page's state, mirrored into the arena (`Node.states` bit 8) for
  // `:focus`, `:focus-visible` and `:focus-within`. A page that never calls focus() does
  // nothing here.
  let focusedId = -1;
  const focusBit = (id, on) => { const b = n.treeOp(id, 0, 31); if (typeof b !== 'number' || b < 0) return; const nb = on ? b | 8 : b & ~8; if (nb !== b) n.treeOp(id, nb, 30); };
  // the focused node, or -1: an element that left its document no longer has the focus
  const focusCurrent = () => { if (focusedId >= 0 && !connectedId(focusedId)) { focusBit(focusedId, false); focusedId = -1; } return focusedId; };
  const fireFocusEvent = (el, type, bubbles, related) => {
    const e = new FocusEvent(type, { bubbles, composed: true, relatedTarget: related, view: window });
    state(e).trusted = true;
    dispatch(el, e);
  };
  // The focus update steps (HTML §6.6.4): blur and focusout at the old element, then focus and
  // focusin at the new one (-1: the viewport).
  const focusMove = to => {
    const from = focusCurrent();
    if (from === to) return;
    const oldEl = from >= 0 ? wrap(from) : null, newEl = to >= 0 ? wrap(to) : null;
    if (from >= 0) { focusBit(from, false); focusedId = -1; fireFocusEvent(oldEl, 'blur', false, newEl); fireFocusEvent(oldEl, 'focusout', true, newEl); }
    if (to >= 0 && focusedId === -1 && connectedId(to)) { focusedId = to; focusBit(to, true); fireFocusEvent(newEl, 'focus', false, oldEl); fireFocusEvent(newEl, 'focusin', true, oldEl); }
  };
  const focusQuery = (id, q) => { const r = n.query(id, 189, q); return typeof r === 'string' && r !== '' ? Number(r) : -1; };
  for (const C of [HTMLElement, SVGElement, MathMLElement]) {
    // an editing host that takes the focus gets the selection first (node_query 177 "f": a caret at its first caret position unless the selection is in it)
    define(C.prototype, 'focus', function focus(options = undefined) { const t = focusQuery(nodeId(this), ''); if (t >= 0) { n.query(t, 177, 'f'); focusMove(t); } });
    define(C.prototype, 'blur', function blur() { if (focusCurrent() === nodeId(this)) focusMove(-1); });
  }
  // `activeElement` (DOM §4.5, HTML §6.6.6): the focused element retargeted against the
  // document or the shadow root; a document with no focused element answers its body.
  const focusRetarget = rootId => {
    let k = focusCurrent();
    for (let i = 0; k >= 0 && i < 1024; i++) {
      const r = info(k, 28);
      if (r === rootId) return wrap(k);
      k = r >= 0 && info(r, 0) === 11 ? info(r, 21) : -1;
    }
    return null;
  };
  Object.defineProperty(Document.prototype, 'activeElement', { get() { return focusRetarget(nodeId(this)) ?? this.body; }, configurable: true, enumerable: true });
  // ==== end focus ==========================================================================

  // ==== popover: popovers, dialogs and their invoker buttons (HTML §6.12, §4.11.4, §4.10.6) ====
  // Which popovers show and which dialog is modal is the page's state, mirrored into the
  // arena as element states (tree_op 30 and 31, `Node.states`: bit 1 a showing popover, bit 2
  // a modal dialog) so that Lean's selectors match `:popover-open` and `:modal`. A page with
  // no popover and no dialog call does nothing here.
  {
    const prop = (C, name, get, set) => Object.defineProperty(C.prototype, name, { get, set, configurable: true, enumerable: true });
    const method = (C, name, f) => Object.defineProperty(C.prototype, name, { value: f, writable: true, configurable: true, enumerable: true });
    const task = f => { chk(n.timer(register(f), 0, 0)); };
    const getStates = id => { const b = n.treeOp(id, 0, 31); return typeof b === 'number' && b >= 0 ? b : 0; };
    const setState = (id, bit, on) => { const b = getStates(id), nb = on ? b | bit : b & ~bit; if (nb !== b) chk(n.treeOp(id, nb, 30)); };
    const toggleInit = new WeakMap();
    class ToggleEvent extends Event {
      constructor(type, init = undefined) {
        super(type, init);
        const d = init === undefined || init === null ? {} : init;
        toggleInit.set(this, { oldState: d.oldState === undefined ? '' : String(d.oldState), newState: d.newState === undefined ? '' : String(d.newState), source: d.source === undefined ? null : d.source });
      }
      get oldState() { return toggleInit.get(this).oldState; }
      get newState() { return toggleInit.get(this).newState; }
      get source() { return toggleInit.get(this).source; }
    }
    def('ToggleEvent', ToggleEvent);
    const commandInit = new WeakMap();
    class CommandEvent extends Event {
      constructor(type, init = undefined) {
        super(type, init);
        const d = init === undefined || init === null ? {} : init;
        commandInit.set(this, { command: d.command === undefined ? '' : String(d.command), source: d.source === undefined ? null : d.source });
      }
      get command() { return commandInit.get(this).command; }
      get source() { return commandInit.get(this).source; }
    }
    def('CommandEvent', CommandEvent);
    const fireToggle = (el, type, oldState, newState, cancelable, source) => {
      const e = new ToggleEvent(type, { cancelable, oldState, newState, source });
      state(e).trusted = true;
      return dispatch(el, e);
    };
    // "Queue a popover toggle event task" (and a dialog's): a task not yet run is replaced,
    // and the event keeps the first old state.
    const pendingToggle = new WeakMap();
    const queueToggle = (el, oldState, newState, source) => {
      const p = pendingToggle.get(el);
      if (p) { oldState = p.oldState; p.cancelled = true; }
      const rec = { oldState, cancelled: false };
      pendingToggle.set(el, rec);
      task(() => { if (rec.cancelled) return; pendingToggle.delete(el); fireToggle(el, 'toggle', oldState, newState, false, source); });
    };

    // ---- popovers ----
    const showing = new Set(), modal = new Set();
    let watching = false;
    const kindOf = el => (el instanceof HTMLElement ? el.popover : null);
    // "Check popover validity" (HTML §6.12.1)
    const valid = (el, expectShowing, throws) => {
      if (kindOf(el) === null) { if (throws) throw new DOMException('The element is not a popover.', 'NotSupportedError'); return false; }
      const id = nodeId(el);
      if (expectShowing !== showing.has(id)) return false;
      if (!el.isConnected || (modal.has(id) && el.hasAttribute('open'))) {
        if (throws) throw new DOMException('The popover is not connected, or is a modal dialog.', 'InvalidStateError');
        return false;
      }
      return true;
    };
    const hidePop = (el, fire, source) => {
      const id = nodeId(el);
      if (!showing.has(id)) return;
      // the auto popovers shown after this one close first
      if (kindOf(el) !== 'manual') { const order = [...showing]; for (let i = order.length - 1; i > order.indexOf(id); i--) { const o = wrap(order[i]); if (showing.has(order[i]) && kindOf(o) !== 'manual') hidePop(o, fire, null); } }
      if (fire) { fireToggle(el, 'beforetoggle', 'open', 'closed', false, source); if (!showing.has(id)) return; }
      showing.delete(id); setState(id, 1, false);
      if (fire) queueToggle(el, 'open', 'closed', source);
    };
    // a showing popover that leaves the document or loses its attribute hides, with no events
    const watch = () => {
      if (watching) return;
      watching = true;
      const sweep = () => { for (const k of [...showing]) { const o = wrap(k); if (!o.isConnected || kindOf(o) === null) hidePop(o, false, null); } };
      for (const k of ['remove', 'replace', 'setText', 'setAttr', 'removeAttr']) {
        const f = n[k];
        n[k] = (...a) => { const r = f.apply(n, a); if (showing.size) sweep(); return r; };
      }
    };
    const showPop = (el, source) => {
      if (!valid(el, false, true)) return;
      if (!fireToggle(el, 'beforetoggle', 'closed', 'open', true, source)) return;
      if (!valid(el, false, true)) return;
      const id = nodeId(el);
      if (kindOf(el) !== 'manual') {
        // an auto popover closes the other auto popovers, except those it is inside (by the tree, or by its invoker)
        for (const k of [...showing]) { const o = wrap(k); if (showing.has(k) && kindOf(o) !== 'manual' && !o.contains(el) && !(source && o.contains(source))) hidePop(o, true, null); }
        if (!valid(el, false, true)) return;
      }
      watch();
      showing.add(id); setState(id, 1, true);
      queueToggle(el, 'closed', 'open', source);
    };
    const sourceOf = options => (options !== null && typeof options === 'object' && options.source !== undefined && options.source !== null ? options.source : null);
    method(HTMLElement, 'showPopover', function showPopover(options = undefined) { showPop(this, sourceOf(options)); });
    method(HTMLElement, 'hidePopover', function hidePopover() { if (valid(this, true, true)) hidePop(this, true, null); });
    method(HTMLElement, 'togglePopover', function togglePopover(options = undefined) {
      const force = typeof options === 'boolean' ? options : options !== null && typeof options === 'object' ? options.force : undefined;
      const id = nodeId(this), source = sourceOf(options);
      if (showing.has(id) && force !== true) { if (valid(this, true, true)) hidePop(this, true, source); }
      else if (!showing.has(id) && force !== false) showPop(this, source);
      else valid(this, showing.has(id), true);
      return showing.has(id);
    });

    // ---- dialog ----
    const D = named.HTMLDialogElement, returnValues = new WeakMap();
    const closeDialog = (el, result, source) => {
      if (!el.hasAttribute('open')) return;
      const id = nodeId(el);
      fireToggle(el, 'beforetoggle', 'open', 'closed', false, source);
      if (!el.hasAttribute('open')) return;
      queueToggle(el, 'open', 'closed', source);
      el.removeAttribute('open');
      if (modal.delete(id)) setState(id, 2, false);
      if (result !== undefined && result !== null) returnValues.set(el, String(result));
      const back = previousFocus.get(el);
      previousFocus.delete(el);
      if (back !== undefined && back >= 0 && connectedId(back)) { const t = focusQuery(back, ''); if (t >= 0) focusMove(t); }
      task(() => { const e = new Event('close'); state(e).trusted = true; dispatch(el, e); });
    };
    const openDialog = (el, asModal, source) => {
      const id = nodeId(el), isModal = modal.has(id) && el.hasAttribute('open');
      if (el.hasAttribute('open') && isModal === asModal) return;
      if (el.hasAttribute('open')) throw new DOMException('The dialog is already open in the other way.', 'InvalidStateError');
      if (asModal && !el.isConnected) throw new DOMException('The dialog is not connected.', 'InvalidStateError');
      if (asModal && showing.has(id)) throw new DOMException('The dialog is a showing popover.', 'InvalidStateError');
      if (!fireToggle(el, 'beforetoggle', 'closed', 'open', true, source)) return;
      if (el.hasAttribute('open') || (asModal && (!el.isConnected || showing.has(id)))) return;
      queueToggle(el, 'closed', 'open', source);
      el.setAttribute('open', '');
      if (asModal) { modal.add(id); setState(id, 2, true); for (const k of [...showing]) if (kindOf(wrap(k)) !== 'manual') hidePop(wrap(k), true, null); }
      // the dialog focusing steps (HTML §4.11.4): the focus goes to the dialog's focus delegate,
      // and comes back to the element that had it when the dialog closes
      previousFocus.set(el, focusCurrent());
      const t = focusQuery(id, 'd');
      if (t >= 0) focusMove(t); else if (asModal) focusMove(-1);
    };
    const previousFocus = new WeakMap();
    method(D, 'show', function show() { openDialog(this, false, null); });
    method(D, 'showModal', function showModal() { openDialog(this, true, null); });
    method(D, 'close', function close(returnValue = undefined) { closeDialog(this, returnValue, null); });
    const requestClose = (el, result, source) => {
      if (!el.hasAttribute('open')) return;
      const e = new Event('cancel', { cancelable: true }); state(e).trusted = true;
      if (dispatch(el, e)) closeDialog(el, result, source);
    };
    method(D, 'requestClose', function requestClose_(returnValue = undefined) { requestClose(this, returnValue, null); });
    prop(D, 'returnValue', function () { return returnValues.get(this) ?? ''; }, function (v) { returnValues.set(this, String(v)); });

    // ---- invoker buttons: `commandfor` with `command`, and `popovertarget` ----
    const commands = ['toggle-popover', 'show-popover', 'hide-popover', 'close', 'request-close', 'show-modal'];
    const commandOf = el => { const c = el.getAttribute('command'); if (c === null) return ''; if (c.startsWith('--')) return c; const l = c.toLowerCase(); return commands.includes(l) ? l : ''; };
    prop(named.HTMLButtonElement, 'command', function () { return commandOf(this); }, function (v) { this.setAttribute('command', String(v)); });
    invokerActivation = (el, t) => {
      const isButton = el instanceof named.HTMLButtonElement;
      if (!isButton && !['button', 'submit', 'reset', 'image'].includes(t)) return;
      const target = isButton ? el.commandForElement : null;
      if (target) {
        const command = commandOf(el);
        if (command === '') return;
        const e = new CommandEvent('command', { cancelable: true, composed: true, command, source: el });
        state(e).trusted = true;
        if (!dispatch(target, e) || command.startsWith('--')) return;
        const id = nodeId(target), isPop = kindOf(target) !== null;
        if (command === 'toggle-popover' && isPop) { if (showing.has(id)) hidePop(target, true, el); else showPop(target, el); }
        else if (command === 'show-popover' && isPop) { if (!showing.has(id)) showPop(target, el); }
        else if (command === 'hide-popover' && isPop) { if (showing.has(id)) hidePop(target, true, el); }
        else if (target instanceof D) {
          if (command === 'show-modal') { if (!target.hasAttribute('open')) openDialog(target, true, el); }
          else if (command === 'close') closeDialog(target, el.value === '' ? undefined : el.value, el);
          else if (command === 'request-close') requestClose(target, el.value === '' ? undefined : el.value, el);
        }
        return;
      }
      const pop = el.popoverTargetElement;
      if (!pop || kindOf(pop) === null) return;
      const action = el.popoverTargetAction, id = nodeId(pop);
      if (action === 'show' && showing.has(id)) return;
      if (action === 'hide' && !showing.has(id)) return;
      if (showing.has(id)) hidePop(pop, true, el); else showPop(pop, el);
    };
  }
  // ==== end popover =======================================================================

  // ==== dynscripts: scripts that a script inserts (HTML §4.12.1 "prepare the script element") ====
  // A script element made by createElement runs when it is connected and has a source: an
  // inline classic script at once; a `src` script when its text has arrived, then `load` (or
  // `error`). Its kind is Lean's (HTML.ScriptType, node_query 183). The script elements of the
  // document as the parser made it are run by the engine in document order and never come
  // here; an element that innerHTML made does not run (its "already started" flag is set).
  // The natives are wrapped when the first such element is made, and do nothing new while no
  // made script element waits.
  {
    const fresh = new Set();
    let wrappedForScripts = false;
    const runText = typeof n0.runScript === 'function' ? src => n0.runScript(src) : src => (0, eval)(src);
    // The script runs with its element's node document as `document` (a frame's document
    // for a script inserted there), as the engine does for the scripts of a parsed frame.
    const execute = (el, text) => {
      const before = currentScript, beforeDocument = scriptDocument;
      const d = info(nodeId(el), 7);
      currentScript = el;
      scriptDocument = d > 0 ? wrap(d) : null;
      try { runText(text); } catch (e) { report(e); } finally { currentScript = before; scriptDocument = beforeDocument; }
    };
    const fire = (el, type) => { const e = new Event(type); state(e).trusted = true; dispatch(el, e); };
    // Scripting is enabled only in a document with a browsing context: the page's (0), or
    // a frame's (node_info 12 answers its iframe) while that iframe is in a document.
    const scripting = id => {
      const doc = info(id, 7);
      if (doc === 0) return true;
      const frame = info(doc, 12);
      return frame >= 0 && connectedId(frame);
    };
    const prepare = id => {
      if (info(id, 0) !== 1 || str(id, 0) !== 'script') { fresh.delete(id); return; }
      if (!connectedId(id)) return;
      if (!scripting(id)) return;
      const src = n0.attr(id, 'src'), el = wrap(id);
      const text = typeof src === 'string' ? '' : el.textContent;
      if (typeof src !== 'string' && text === '') return;
      fresh.delete(id);
      if (n.query(id, 183, '') !== 'classic') return;
      if (typeof src !== 'string') { execute(el, text); return; }
      const url = src === '' ? null : resolveURL(src);
      const fetcher = url === null || url === undefined ? undefined : globalThis.fetch;
      if (typeof fetcher !== 'function') { Promise.resolve().then(() => fire(el, 'error')); return; }
      fetcher(url).then(r => { if (!r.ok) throw new TypeError('script load failed'); return r.text(); })
        .then(code => { if (!scripting(id)) return; execute(el, code); fire(el, 'load'); }, () => { if (scripting(id)) fire(el, 'error'); });
    };
    const after = r => { if (r === 0 && fresh.size) for (const id of [...fresh]) prepare(id); return r; };
    noteFreshScript = id => {
      fresh.add(id);
      if (wrappedForScripts) return;
      wrappedForScripts = true;
      const insert0 = n.insert, replace0 = n.replace, setText0 = n.setText;
      n.insert = (p, node, child) => (fresh.size ? after(insert0(p, node, child)) : insert0(p, node, child));
      n.replace = (p, node, child) => (fresh.size ? after(replace0(p, node, child)) : replace0(p, node, child));
      n.setText = (id2, value) => (fresh.size ? after(setText0(id2, value)) : setText0(id2, value));
    };
  }
  // ==== end dynscripts ====================================================================

  // ==== imagesource: the image an img element asks for (HTML §4.8.4.3) =====================
  // `currentSrc`: the source that Lean selects from `srcset`, `sizes`, `src` and the `source`
  // children of a `picture` (HTML.ImageSource, node_query 195) for the device pixel ratio and
  // the viewport of the element's document, resolved against that document's URL.
  Object.defineProperty(named.HTMLImageElement.prototype, 'currentSrc', { get() {
    const id = nodeId(this), d = info(id, 7), frame = d > 0 ? info(d, 12) : -1;
    let size;
    if (frame >= 0) { const b = layoutOf(wrap(frame)); size = [b[6], b[7]]; } else size = viewport();
    const r = n.query(id, 195, globalThis.devicePixelRatio + '\u0000' + size[0] + '\u0000' + size[1]);
    if (typeof r !== 'string' || r === '') return '';
    return (frame >= 0 ? resolveURL(r.slice(1), docURL(d)) : resolveURL(r.slice(1))) ?? '';
  }, configurable: true, enumerable: true });
  // ==== end imagesource ===================================================================

  // ==== trustedtypes: Trusted Types (https://w3c.github.io/trusted-types/dist/spec/) =====
  // The objects are here: `trustedTypes`, the policies (whose functions are the page's) and
  // the three trusted value types. Every decision is Lean's (HTML.TrustedTypes, node_query
  // 194): whether a sink requires a trusted value, what happens to a value that is not one,
  // whether a policy may be created, and which attributes and properties are sinks. The
  // policies of a document are those of its `meta` elements; once seen, a policy stays (a
  // policy does not go when its element is removed). The sinks ask nothing until the page
  // goes live: it uses `trustedTypes`, or one of its documents declares a policy.
  {
    const isObj = v => v !== null && (typeof v === 'object' || typeof v === 'function');
    const illegal = () => { throw new TypeError('Illegal constructor'); };
    const ask = (doc, q) => { const r = n.query(doc, 194, q); return typeof r === 'number' ? fail(r) : r; };
    // ---- the trusted values -----------------------------------------------------------------
    const values = new WeakMap();
    const stringOf = (o, kind) => { const v = isObj(o) ? values.get(o) : undefined; if (v === undefined || v.kind !== kind) throw new TypeError('Illegal invocation'); return v.s; };
    class TrustedHTML { constructor() { illegal(); } toString() { return stringOf(this, 'TrustedHTML'); } toJSON() { return stringOf(this, 'TrustedHTML'); } }
    class TrustedScript { constructor() { illegal(); } toString() { return stringOf(this, 'TrustedScript'); } toJSON() { return stringOf(this, 'TrustedScript'); } }
    class TrustedScriptURL { constructor() { illegal(); } toString() { return stringOf(this, 'TrustedScriptURL'); } toJSON() { return stringOf(this, 'TrustedScriptURL'); } }
    const classes = { TrustedHTML, TrustedScript, TrustedScriptURL };
    const make = (kind, s) => { const o = Object.create(classes[kind].prototype); values.set(o, { kind, s }); return o; };
    const isKind = (v, kind) => { const t = isObj(v) ? values.get(v) : undefined; return t !== undefined && t.kind === kind; };
    // ---- policies ---------------------------------------------------------------------------
    const functionOf = { TrustedHTML: 'createHTML', TrustedScript: 'createScript', TrustedScriptURL: 'createScriptURL' };
    const policies = new WeakMap();
    const policyOf = p => { const v = isObj(p) ? policies.get(p) : undefined; if (v === undefined) throw new TypeError('Illegal invocation'); return v; };
    // "Get Trusted Type policy value"
    const policyValue = (p, kind, value, args, throwIfMissing) => {
      const f = p[functionOf[kind]];
      if (f === null) {
        if (throwIfMissing) throw new TypeError(`Policy ${p.name}'s TrustedTypePolicyOptions did not specify a '${functionOf[kind]}' member.`);
        return null;
      }
      return f(value, ...args);
    };
    // "Create a Trusted Type"
    const createValue = (self, kind, args) => {
      const p = policyOf(self);
      if (args.length < 1) throw new TypeError(`Failed to execute '${functionOf[kind]}' on 'TrustedTypePolicy': 1 argument required, but only 0 present.`);
      const v = policyValue(p, kind, String(args[0]), Array.prototype.slice.call(args, 1), true);
      return make(kind, v === null || v === undefined ? '' : String(v));
    };
    class TrustedTypePolicy {
      constructor() { illegal(); }
      get name() { return policyOf(this).name; }
      createHTML(input) { return createValue(this, 'TrustedHTML', arguments); }
      createScript(input) { return createValue(this, 'TrustedScript', arguments); }
      createScriptURL(input) { return createValue(this, 'TrustedScriptURL', arguments); }
    }
    // ---- the policies of a document, and reports ----------------------------------------------
    // the document whose policies govern a node: a frame's own document, else the page's
    const docOf = id => { const d = info(id, 7); return d > 0 && info(d, 12) >= 0 ? d : 0; };
    const globalDoc = () => (scriptDocument ? docOf(nodeId(scriptDocument)) : 0);
    const seenPolicies = new Map();
    const cspOf = doc => {
      const now = ask(doc, 'm');
      let list = seenPolicies.get(doc);
      if (now !== '') {
        if (!list) seenPolicies.set(doc, list = []);
        for (const p of now.split('\u0001')) if (!list.includes(p)) list.push(p);
      }
      return list ? list.join('\u0001') : '';
    };
    const violationFields = { documentURI: '', referrer: '', blockedURI: '', effectiveDirective: '', violatedDirective: '', originalPolicy: '',
      sourceFile: '', sample: '', disposition: 'enforce', statusCode: 0, lineNumber: 0, columnNumber: 0 };
    if (typeof globalThis.SecurityPolicyViolationEvent !== 'function') {
      const inits = new WeakMap();
      class SecurityPolicyViolationEvent extends Event {
        constructor(type, init = undefined) {
          super(type, init);
          const d = init === undefined || init === null ? {} : init, o = {};
          for (const k of Object.keys(violationFields)) {
            const v = d[k];
            o[k] = v === undefined ? violationFields[k] : typeof violationFields[k] === 'number' ? Number(v) >>> 0 : String(v);
          }
          inits.set(this, o);
        }
      }
      for (const k of Object.keys(violationFields))
        Object.defineProperty(SecurityPolicyViolationEvent.prototype, k, { get() { return inits.get(this)[k]; }, enumerable: true, configurable: true });
      def('SecurityPolicyViolationEvent', SecurityPolicyViolationEvent);
    }
    // a report to each violated policy (their places in the list, as Lean answers them)
    const violations = (doc, csp, places, directive, blockedURI, sample) => {
      const list = csp.split('\u0001');
      for (const i of places.split(' ')) {
        const p = i === '' ? undefined : list[Number(i)];
        if (p === undefined) continue;
        const init = { bubbles: true, composed: true, documentURI: String(wrap(doc).URL), blockedURI, effectiveDirective: directive,
          violatedDirective: directive, originalPolicy: p.slice(1), disposition: p[0] === 'r' ? 'report' : 'enforce', sample };
        setTimeout(() => { const e = new globalThis.SecurityPolicyViolationEvent('securitypolicyviolation', init); state(e).trusted = true; dispatch(wrap(doc), e); }, 0);
      }
    };
    // ---- the factory --------------------------------------------------------------------------
    const created = [];
    let defaultPolicy = null;
    const lower = t => t.replace(/[A-Z]/g, c => c.toLowerCase());
    const nullable = v => (v === null || v === undefined ? '' : String(v));
    const emptyHTML = make('TrustedHTML', ''), emptyScript = make('TrustedScript', '');
    class TrustedTypePolicyFactory {
      constructor() { illegal(); }
      createPolicy(policyName, policyOptions = undefined) {
        const what = "Failed to execute 'createPolicy' on 'TrustedTypePolicyFactory'";
        if (arguments.length < 1) throw new TypeError(`${what}: 1 argument required, but only 0 present.`);
        const name = String(policyName);
        if (policyOptions !== undefined && policyOptions !== null && !isObj(policyOptions)) throw new TypeError(`${what}: parameter 2 is not of type 'TrustedTypePolicyOptions'.`);
        const o = policyOptions ?? {};
        const member = k => { const f = o[k]; if (f === undefined || f === null) return null; if (typeof f !== 'function') throw new TypeError(`${what}: '${k}' is not a function.`); return f; };
        const createHTML = member('createHTML'), createScript = member('createScript'), createScriptURL = member('createScriptURL');
        const doc = globalDoc(), csp = cspOf(doc), plain = t => t.replace(/[\u0000-\u0002]/g, '�');
        const r = ask(doc, 'c\u0000' + csp + '\u0000' + plain(name) + '\u0000' + created.map(x => plain(x) + '\u0002').join(''));
        if (r.length > 2) violations(doc, csp, r.slice(2), 'trusted-types', 'trusted-types-policy', name.slice(0, 40));
        if (r[0] === '1') throw new TypeError(`${what}: Policy "${name}" disallowed.`);
        if (name === 'default' && defaultPolicy !== null) throw new TypeError(`${what}: Policy with name "default" already exists.`);
        const p = Object.create(TrustedTypePolicy.prototype);
        policies.set(p, { name, createHTML, createScript, createScriptURL });
        if (name === 'default') defaultPolicy = p;
        created.push(name);
        return p;
      }
      isHTML(value) { return isKind(value, 'TrustedHTML'); }
      isScript(value) { return isKind(value, 'TrustedScript'); }
      isScriptURL(value) { return isKind(value, 'TrustedScriptURL'); }
      get emptyHTML() { return emptyHTML; }
      get emptyScript() { return emptyScript; }
      getAttributeType(tagName, attribute, elementNs = '', attrNs = '') {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'getAttributeType' on 'TrustedTypePolicyFactory': 2 arguments required.");
        const local = lower(String(tagName)), attr = lower(String(attribute)), ens = nullable(elementNs) || HTML_NS, ans = nullable(attrNs);
        if ((local + attr + ens + ans).includes('\u0000')) return null;
        const r = ask(0, 'a\u0000' + ens + '\u0000' + local + '\u0000' + ans + '\u0000' + attr);
        return r === '' ? null : r.split('\u0000')[0];
      }
      getPropertyType(tagName, property, elementNs = '') {
        if (arguments.length < 2) throw new TypeError("Failed to execute 'getPropertyType' on 'TrustedTypePolicyFactory': 2 arguments required.");
        const local = lower(String(tagName)), prop = String(property), ens = nullable(elementNs) || HTML_NS;
        if ((local + prop + ens).includes('\u0000')) return null;
        const r = ask(0, 'p\u0000' + ens + '\u0000' + local + '\u0000' + prop);
        return r === '' ? null : r;
      }
      get defaultPolicy() { return defaultPolicy; }
    }
    const factory = Object.create(TrustedTypePolicyFactory.prototype);
    for (const [k, C] of Object.entries({ TrustedHTML, TrustedScript, TrustedScriptURL, TrustedTypePolicy, TrustedTypePolicyFactory })) def(k, C);
    // ---- "Get Trusted Type compliant string" --------------------------------------------------
    const requiresOf = new Map();
    const compliant = (kind, doc, input, sink) => {
      if (isKind(input, kind)) return values.get(input).s;
      const csp = cspOf(doc);
      let required = requiresOf.get(csp);
      if (required === undefined) { if (requiresOf.size >= 64) requiresOf.clear(); requiresOf.set(csp, required = ask(doc, 'r\u0000' + csp) === '1'); }
      const text = String(input);
      if (!required) return text;
      // "Process value with a default policy": the page's function; an exception of it goes on
      const converted = defaultPolicy === null ? null : policyValue(policies.get(defaultPolicy), kind, text, [kind, sink], false);
      const gave = converted !== null && converted !== undefined;
      const r = ask(doc, 'o\u0000' + csp + '\u00000\u0000' + (gave ? '1' : '0'));
      if (r.length > 2) violations(doc, csp, r.slice(2), 'require-trusted-types-for', 'trusted-types-sink', sink + '|' + text.slice(0, 40));
      if (r[0] === 'x') throw new TypeError(`This document requires '${kind}' assignment. The sink is '${sink}'.`);
      return r[0] === 'd' ? String(converted) : text;
    };
    // "Get Trusted Types-compliant attribute value": `ns` null or '' for no namespace, `name`
    // the qualified name given (lower case for an HTML element when there is no namespace)
    const attrSinks = new Map();
    const attrValue = (el, ns, name, value) => {
      const id = nodeId(el);
      const local = ns === null || ns === '' ? lowerIfHtml(el, name) : name.slice(name.indexOf(':') + 1);
      const key = (str(id, 2) ?? '') + '\u0000' + str(id, 0) + '\u0000' + (ns ?? '') + '\u0000' + local;
      let sink = attrSinks.get(key);
      if (sink === undefined) {
        if (attrSinks.size >= 512) attrSinks.clear();
        const r = local.includes('\u0000') ? '' : ask(0, 'a\u0000' + key);
        attrSinks.set(key, sink = r === '' ? null : r.split('\u0000'));
      }
      return sink === null ? String(value) : compliant(sink[0], docOf(id), value, sink[1]);
    };
    // ---- going live ---------------------------------------------------------------------------
    let live = false;
    const goLive = () => {
      if (live) return;
      live = true; ttMeta = null; ttStart = null; ttDoc = null;
      ttAttr = attrValue;
      ttValue = (kind, id, value, sink) => compliant(kind, id === null ? globalDoc() : docOf(id), value, sink);
    };
    const checked = new Set();
    ttMeta = goLive;
    ttStart = () => { if (ask(0, 'm') !== '') goLive(); };
    ttDoc = d => { if (!checked.has(d)) { checked.add(d); if (ask(d, 'm') !== '') goLive(); } };
    Object.defineProperty(Window.prototype, 'trustedTypes', { get() { goLive(); return factory; }, enumerable: true, configurable: true });
    // ---- the sinks that take markup or script (the attribute sinks are in Element and Attr) ----
    const setterSink = (C, prop, kind, sink, nullEmpty = false) => {
      const d = C && Object.getOwnPropertyDescriptor(C.prototype, prop);
      if (!d || !d.set) return;
      const set = d.set;
      Object.defineProperty(C.prototype, prop, { get: d.get, enumerable: d.enumerable, configurable: true,
        set(v) { set.call(this, ttValue === null ? v : ttValue(kind, nodeId(this), nullEmpty && v === null ? '' : v, sink)); } });
    };
    setterSink(Element, 'innerHTML', 'TrustedHTML', 'Element innerHTML', true);
    setterSink(Element, 'outerHTML', 'TrustedHTML', 'Element outerHTML', true);
    if (typeof ShadowRoot === 'function') setterSink(ShadowRoot, 'innerHTML', 'TrustedHTML', 'ShadowRoot innerHTML', true);
    setterSink(globalThis.HTMLIFrameElement, 'srcdoc', 'TrustedHTML', 'HTMLIFrameElement srcdoc');
    setterSink(globalThis.HTMLScriptElement, 'src', 'TrustedScriptURL', 'HTMLScriptElement src');
    const argSink = (C, name, index, kind, sink) => {
      const f = C && C.prototype[name];
      if (typeof f !== 'function') return;
      define(C.prototype, name, Object.defineProperty(function (...args) {
        if (ttValue !== null && args.length > index) args[index] = ttValue(kind, this instanceof Node ? nodeId(this) : null, args[index], sink);
        return f.apply(this, args);
      }, 'name', { value: name, configurable: true }));
    };
    argSink(Element, 'insertAdjacentHTML', 1, 'TrustedHTML', 'Element insertAdjacentHTML');
    argSink(globalThis.DOMParser, 'parseFromString', 0, 'TrustedHTML', 'DOMParser parseFromString');
    argSink(globalThis.Range, 'createContextualFragment', 0, 'TrustedHTML', 'Range createContextualFragment');
    // document.write and writeln: the arguments joined; trusted when every one is TrustedHTML
    for (const name of ['write', 'writeln']) {
      const f = Document.prototype[name];
      define(Document.prototype, name, Object.defineProperty(function (...text) {
        if (ttValue === null || text.every(t => isKind(t, 'TrustedHTML'))) return f.apply(this, text);
        return f.call(this, ttValue('TrustedHTML', nodeId(this), text.map(String).join(''), 'Document ' + name));
      }, 'name', { value: name, configurable: true }));
    }
    // the script element's text: `text`, and `innerText` and `textContent` on a script element
    const S = globalThis.HTMLScriptElement;
    if (S) {
      const textContent = Object.getOwnPropertyDescriptor(Node.prototype, 'textContent');
      const innerText = Object.getOwnPropertyDescriptor(HTMLElement.prototype, 'innerText');
      const checkedText = (self, v, name) => (ttValue === null ? v : ttValue('TrustedScript', nodeId(self), v, 'HTMLScriptElement ' + name));
      Object.defineProperty(S.prototype, 'text', { enumerable: true, configurable: true,
        get() { let t = ''; for (const c of this.childNodes) if (c.nodeType === 3) t += c.data; return t; },
        set(v) { textContent.set.call(this, checkedText(this, v, 'text')); } });
      Object.defineProperty(S.prototype, 'textContent', { enumerable: true, configurable: true,
        get() { return textContent.get.call(this); },
        set(v) { textContent.set.call(this, checkedText(this, v === null ? '' : v, 'textContent')); } });
      if (innerText && innerText.set) Object.defineProperty(S.prototype, 'innerText', { enumerable: true, configurable: true,
        get() { return innerText.get.call(this); },
        set(v) { innerText.set.call(this, checkedText(this, v === null ? '' : v, 'innerText')); } });
    }
  }
  // ==== end trustedtypes ==================================================================

  // ==== sanitizer: HTML sanitization and the HTML insertion methods (HTML §8.5.2, §8.6) ====
  // A Sanitizer's configuration, every method on it, and what a configuration keeps of
  // parsed markup are Lean's (HTML.Sanitizer: node_query 192 the methods, 193 the tree).
  // Here: Web IDL conversion of the dictionaries to the text Lean reads (`configWire` there),
  // the objects, and the insertion methods. The markup is parsed into a fragment that no
  // script can reach, sanitized there, and only then inserted; for the safe methods its
  // event handler content attributes are never read.
  {
    const isObj = v => v !== null && (typeof v === 'object' || typeof v === 'function');
    // a name, a namespace or a target in the wire: no character below U+0008
    const esc = t => t.replace(/[\u0000-\u0007]/g, c => '\u0007' + String.fromCharCode(c.charCodeAt(0) + 64));
    const unesc = t => t.replace(/\u0007([\s\S])/g, (m, c) => String.fromCharCode(c.charCodeAt(0) - 64));
    const seq = (v, what) => {
      if (!isObj(v) || typeof v[Symbol.iterator] !== 'function') throw new TypeError(`${what}: the value is not a sequence.`);
      return [...v];
    };
    // "canonicalize a sanitizer name": a DOMString, or a dictionary with `name` and `namespace`
    const nameWire = (v, defaultNs, what) => {
      if (v === null || v === undefined || isObj(v)) {
        const d = v ?? {}, nm = d.name;
        if (nm === undefined) throw new TypeError(`${what}: required member name is undefined.`);
        const name = String(nm), nsv = d.namespace;
        const ns = nsv === undefined ? defaultNs : nsv === null ? null : String(nsv);
        return esc(name) + '\u0005' + esc(ns ?? '');
      }
      return esc(String(v)) + '\u0005' + esc(defaultNs ?? '');
    };
    const attrList = (v, sep, what) => v === undefined ? '0' : '1' + seq(v, what).map(x => nameWire(x, null, what)).join(sep);
    // "canonicalize a SanitizerElementWithAttributes"
    const ruleWire = (v, what) => {
      const name = nameWire(v, HTML_NS, what);
      const dict = isObj(v);
      const attributes = attrList(dict ? v.attributes : undefined, '\u0004', what);
      const removeAttributes = attrList(dict ? v.removeAttributes : undefined, '\u0004', what);
      return name + '\u0003' + attributes + '\u0003' + removeAttributes;
    };
    // "canonicalize a processing instruction"
    const piTarget = (v, what) => {
      if (v === null || v === undefined || isObj(v)) {
        const t = (v ?? {}).target;
        if (t === undefined) throw new TypeError(`${what}: required member target is undefined.`);
        return String(t);
      }
      return String(v);
    };
    // a SanitizerConfig dictionary (members read in Web IDL order) as the wire text
    const configWire = (v, what) => {
      if (v !== null && v !== undefined && !isObj(v)) throw new TypeError(`${what}: the value is not of type 'SanitizerConfig'.`);
      const d = v ?? {};
      const names = (x, ns) => x === undefined ? '0' : '1' + seq(x, what).map(i => nameWire(i, ns, what)).join('\u0002');
      const bool = x => x === undefined ? '' : (x ? '1' : '0');
      const pis = x => x === undefined ? '0' : '1' + seq(x, what).map(i => '\u0005' + esc(piTarget(i, what))).join('\u0002');
      const attributes = names(d.attributes, null), comments = bool(d.comments), dataAttributes = bool(d.dataAttributes);
      const ex = d.elements, elements = ex === undefined ? '0' : '1' + seq(ex, what).map(i => ruleWire(i, what)).join('\u0002');
      const javascriptURLs = bool(d.javascriptURLs), processingInstructions = pis(d.processingInstructions);
      const removeAttributes = names(d.removeAttributes, null), removeElements = names(d.removeElements, HTML_NS);
      const removeProcessingInstructions = pis(d.removeProcessingInstructions);
      const replaceWithChildrenElements = names(d.replaceWithChildrenElements, HTML_NS);
      return [elements, removeElements, replaceWithChildrenElements, processingInstructions, removeProcessingInstructions,
        attributes, removeAttributes, comments, dataAttributes, javascriptURLs].join('\u0001');
    };
    // the wire text as a SanitizerConfig dictionary (members in Web IDL order)
    const nameObj = w => { const i = w.indexOf('\u0005'), ns = unesc(w.slice(i + 1)); return { name: unesc(w.slice(0, i)), namespace: ns === '' ? null : ns }; };
    const listOf = (w, sep, f) => w[0] !== '1' ? undefined : w.length === 1 ? [] : w.slice(1).split(sep).map(f);
    const ruleObj = w => {
      const [name, attributes, removeAttributes] = w.split('\u0003'), o = nameObj(name);
      const a = listOf(attributes, '\u0004', nameObj), r = listOf(removeAttributes, '\u0004', nameObj);
      if (a !== undefined) o.attributes = a;
      if (r !== undefined) o.removeAttributes = r;
      return o;
    };
    const configObj = w => {
      const [elements, removeElements, replace, pis, removePis, attributes, removeAttributes, comments, data, js] = w.split('\u0001');
      const o = {}, put = (k, v) => { if (v !== undefined) o[k] = v; }, pi = t => ({ target: unesc(t.slice(1)) });
      put('attributes', listOf(attributes, '\u0002', nameObj));
      if (comments !== '') o.comments = comments === '1';
      if (data !== '') o.dataAttributes = data === '1';
      put('elements', listOf(elements, '\u0002', ruleObj));
      if (js !== '') o.javascriptURLs = js === '1';
      put('processingInstructions', listOf(pis, '\u0002', pi));
      put('removeAttributes', listOf(removeAttributes, '\u0002', nameObj));
      put('removeElements', listOf(removeElements, '\u0002', nameObj));
      put('removeProcessingInstructions', listOf(removePis, '\u0002', pi));
      put('replaceWithChildrenElements', listOf(replace, '\u0002', nameObj));
      return o;
    };
    const ask = q => { const r = n.query(0, 192, q); return typeof r === 'number' ? fail(r) : r; };
    const wires = new WeakMap();
    const wireOf = s => { const w = wires.get(s); if (w === undefined) throw new TypeError('Illegal invocation'); return w; };
    const presetWire = (v, what) => {
      if (String(v) !== 'default') throw new TypeError(`${what}: '${String(v)}' is not a valid enum value of type SanitizerPresets.`);
      return 'default';
    };
    class Sanitizer {
      constructor(configuration = 'default') {
        const what = "Failed to construct 'Sanitizer'";
        const w = configuration === null || isObj(configuration) ? configWire(configuration, what) : presetWire(configuration, what);
        const r = ask('new\u0000' + w + '\u00001');
        if (r[0] !== 'K') throw new TypeError(`${what}: the configuration is not valid.`);
        wires.set(this, r.slice(1));
      }
      get() { return configObj(ask('get\u0000' + wireOf(this))); }
      removeUnsafe() { const r = ask('removeUnsafe\u0000' + wireOf(this)); wires.set(this, r.slice(1)); return r[0] === '1'; }
    }
    // the modifier methods: Lean answers the method's result and the configuration after it
    const named = (name, f) => Object.defineProperty(f, 'name', { value: name, configurable: true });
    const modifier = (name, argWire) => {
      const f = named(name, function (arg) {
        const w = wireOf(this);
        if (arguments.length < 1) throw new TypeError(`Failed to execute '${name}' on 'Sanitizer': 1 argument required, but only 0 present.`);
        const r = ask(name + '\u0000' + w + '\u0000' + argWire(arg, `Failed to execute '${name}' on 'Sanitizer'`));
        wires.set(this, r.slice(1));
        return r[0] === '1';
      });
      Object.defineProperty(Sanitizer.prototype, name, { value: f, writable: true, configurable: true });
    };
    modifier('allowElement', ruleWire);
    modifier('removeElement', (v, what) => nameWire(v, HTML_NS, what));
    modifier('replaceElementWithChildren', (v, what) => nameWire(v, HTML_NS, what));
    modifier('allowProcessingInstruction', (v, what) => esc(piTarget(v, what)));
    modifier('removeProcessingInstruction', (v, what) => esc(piTarget(v, what)));
    modifier('allowAttribute', (v, what) => nameWire(v, null, what));
    modifier('removeAttribute', (v, what) => nameWire(v, null, what));
    modifier('setComments', v => (v ? '1' : '0'));
    modifier('setDataAttributes', v => (v ? '1' : '0'));
    modifier('setJavascriptURLs', v => (v ? '1' : '0'));
    def('Sanitizer', Sanitizer);

    // "Get a sanitizer config from options": the prepared configuration (a wire text), or
    // null for an unsafe method with no sanitizer. A configuration is prepared by Lean once
    // for each text and mode (the texts of the last few are kept).
    const preparedWires = new Map();
    const optionsOf = (options, safe, what) => {
      if (options !== undefined && options !== null && !isObj(options)) throw new TypeError(`${what}: the options are not an object.`);
      const o = options ?? {};
      const runScripts = safe ? false : !!o.runScripts;
      let input = o.sanitizer;
      if (input === undefined) { if (!safe) return { config: null, runScripts }; input = 'default'; }
      const w = input instanceof Sanitizer ? wireOf(input)
        : input === null || isObj(input) ? configWire(input, what) : presetWire(input, what);
      const key = (safe ? '1' : '0') + w;
      let config = preparedWires.get(key);
      if (config === undefined) {
        const r = ask('prepare\u0000' + w + '\u0000' + (safe ? '1' : '0'));
        if (r[0] !== 'K') throw new TypeError(`${what}: the sanitizer configuration is not valid.`);
        config = r.slice(1);
        if (preparedWires.size >= 16) preparedWires.clear();
        preparedWires.set(key, config);
      }
      return { config, runScripts };
    };
    const hierarchy = () => new DOMException('The operation would yield an incorrect node tree.', 'HierarchyRequestError');
    const isHtmlNamed = (id, name) => info(id, 0) === 1 && str(id, 2) === HTML_NS && str(id, 0) === name;
    // "Parse HTML for insertion": the sanitized fragment of `markup` for the context element
    // `ctx` in the node document of `target`, or -1 when a safe method has a script context.
    const parseFor = (ctx, markup, o, safe) => {
      const ns = str(ctx, 2), name = str(ctx, 0);
      if (safe && name === 'script' && (ns === HTML_NS || ns === 'http://www.w3.org/2000/svg')) return -1;
      const f = chk(n.create(14 + 16 * info(ctx, 7), (ns ?? '') + '\u0000' + name + '\u0000' + markup));
      if (o.config !== null) op(f, 193, (safe ? '1' : '0') + '\u0000' + o.config);
      if (!safe) scanHandlers(f, false);
      return f;
    };
    // the context element of a target: the element, or a shadow root's host
    const contextOf2 = target => (info(target, 0) === 11 ? info(target, 21) : target);
    // "target for HTML insertion": a template's contents, else the element
    const targetOf = id => (isHtmlNamed(id, 'template') ? info(id, 9) : id);
    // "parent for HTML insertion"
    const parentFor = id => {
      const p = info(id, 1);
      if (p < 0) return -1;
      if (info(p, 0) === 1) { if (isHtmlNamed(p, 'template')) throw hierarchy(); return p; }
      if (info(p, 0) === 11 && info(p, 21) >= 0) return p;
      throw hierarchy();
    };
    // "Filter and set HTML", "filter and pre-insert HTML", "filter and replace with HTML"
    const setHTML = (ctx, target, markup, o, safe) => {
      const f = parseFor(ctx, markup, o, safe);
      if (f < 0) return;
      chk(n.setText(target, '')); chk(n.insert(target, f, -1));
    };
    const preInsertHTML = (ctx, parent, child, markup, o, safe) => {
      if (isHtmlNamed(ctx, 'html')) throw hierarchy();
      const f = parseFor(ctx, markup, o, safe);
      if (f >= 0) chk(n.insert(parent, f, child));
    };
    const replaceHTML = (ctx, parent, node, markup, o, safe) => {
      if (isHtmlNamed(ctx, 'html')) throw hierarchy();
      const f = parseFor(ctx, markup, o, safe);
      if (f >= 0) chk(n.replace(parent, f, node));
    };
    const method = (C, name, f) => Object.defineProperty(C.prototype, name, { value: f, writable: true, configurable: true });
    // the markup of a method: an unsafe method is a TrustedHTML sink (section trustedtypes)
    const markupOf = (safe, id, html, sink) => (safe || ttValue === null ? String(html) : ttValue('TrustedHTML', id, html, sink));
    // the six methods of an Element or a ShadowRoot and of a child node, safe and unsafe
    for (const safe of [true, false]) {
      const sfx = safe ? '' : 'Unsafe';
      const args = (iface, name, a, k = 1) => {
        const what = `Failed to execute '${name}' on '${iface}'`;
        if (a.length < k) throw new TypeError(`${what}: ${k} argument required, but only ${a.length} present.`);
        return what;
      };
      const roots = typeof ShadowRoot === 'function' ? [[Element, 'Element'], [ShadowRoot, 'ShadowRoot']] : [[Element, 'Element']];
      for (const [C, iface] of roots) {
        const place = self => { const id = nodeId(self); return iface === 'Element' ? [id, targetOf(id)] : [info(id, 21), id]; };
        method(C, 'setHTML' + sfx, named('setHTML' + sfx, function (html, options = undefined) {
          const what = args(iface, 'setHTML' + sfx, arguments), [ctx, target] = place(this);
          setHTML(ctx, target, markupOf(safe, nodeId(this), html, iface + ' setHTML' + sfx), optionsOf(options, safe, what), safe);
        }));
        method(C, 'appendHTML' + sfx, named('appendHTML' + sfx, function (html, options = undefined) {
          const what = args(iface, 'appendHTML' + sfx, arguments), [ctx, target] = place(this);
          preInsertHTML(ctx, target, -1, markupOf(safe, nodeId(this), html, iface + ' appendHTML' + sfx), optionsOf(options, safe, what), safe);
        }));
        method(C, 'prependHTML' + sfx, named('prependHTML' + sfx, function (html, options = undefined) {
          const what = args(iface, 'prependHTML' + sfx, arguments), [ctx, target] = place(this);
          preInsertHTML(ctx, target, info(target, 2), markupOf(safe, nodeId(this), html, iface + ' prependHTML' + sfx), optionsOf(options, safe, what), safe);
        }));
      }
      for (const C of [Element, CharacterData]) {
        const iface = C === Element ? 'Element' : 'CharacterData';
        method(C, 'beforeHTML' + sfx, named('beforeHTML' + sfx, function (html, options = undefined) {
          const what = args(iface, 'beforeHTML' + sfx, arguments), id = nodeId(this), markup = markupOf(safe, id, html, 'Node beforeHTML' + sfx), o = optionsOf(options, safe, what);
          const parent = parentFor(id);
          if (parent >= 0) preInsertHTML(contextOf2(parent), parent, id, markup, o, safe);
        }));
        method(C, 'afterHTML' + sfx, named('afterHTML' + sfx, function (html, options = undefined) {
          const what = args(iface, 'afterHTML' + sfx, arguments), id = nodeId(this), markup = markupOf(safe, id, html, 'Node afterHTML' + sfx), o = optionsOf(options, safe, what);
          const parent = parentFor(id);
          if (parent >= 0) preInsertHTML(contextOf2(parent), parent, info(id, 5), markup, o, safe);
        }));
        method(C, 'replaceWithHTML' + sfx, named('replaceWithHTML' + sfx, function (html, options = undefined) {
          const what = args(iface, 'replaceWithHTML' + sfx, arguments), id = nodeId(this), markup = markupOf(safe, id, html, 'Node replaceWithHTML' + sfx), o = optionsOf(options, safe, what);
          const parent = parentFor(id);
          if (parent >= 0) replaceHTML(contextOf2(parent), parent, id, markup, o, safe);
        }));
      }
    }
    // Document.parseHTML and Document.parseHTMLUnsafe: a document with no browsing context
    // that the HTML parser makes, sanitized before it is answered.
    const parseDocument = (markup, o, safe) => {
      const doc = chk(n.create(11, markup));
      if (o.config !== null) op(doc, 193, (safe ? '1' : '0') + '\u0000' + o.config);
      return wrap(doc);
    };
    define(Document, 'parseHTML', function parseHTML(html, options = undefined) {
      if (arguments.length < 1) throw new TypeError("Failed to execute 'parseHTML' on 'Document': 1 argument required, but only 0 present.");
      return parseDocument(String(html), optionsOf(options, true, "Failed to execute 'parseHTML' on 'Document'"), true);
    });
    define(Document, 'parseHTMLUnsafe', function parseHTMLUnsafe(html, options = undefined) {
      if (arguments.length < 1) throw new TypeError("Failed to execute 'parseHTMLUnsafe' on 'Document': 1 argument required, but only 0 present.");
      return parseDocument(markupOf(false, null, html, 'Document parseHTMLUnsafe'), optionsOf(options, false, "Failed to execute 'parseHTMLUnsafe' on 'Document'"), false);
    });
  }
  // ==== end sanitizer =====================================================================

  // ---- Interface objects as Web IDL defines them (§3.7.1 to §3.7.3) ----
  // An interface's attributes, operations and constants are enumerable own properties of its
  // interface prototype object (of the interface object when static), and the prototype's
  // class string is the interface's name. The classes above are JavaScript classes, whose
  // members are not enumerable: one pass sets both for every interface on the global, names
  // the accessor functions, and puts the interface check in front of a getter that lacks it.
  // It runs when the prelude runs (once for the engine, not for each page).
  for (const name of Object.getOwnPropertyNames(globalThis)) {
    if (esGlobals.has(name) || !/^[A-Z]/.test(name)) continue;
    const gd = Object.getOwnPropertyDescriptor(globalThis, name);
    const C = gd && gd.value;
    if (typeof C !== 'function') continue;
    const cd = Object.getOwnPropertyDescriptor(C, 'prototype');
    const P = cd && cd.value;
    if (P === null || typeof P !== 'object') continue;
    if (C.name === name && !Object.prototype.hasOwnProperty.call(P, Symbol.toStringTag))
      Object.defineProperty(P, Symbol.toStringTag, { value: name, writable: false, enumerable: false, configurable: true });
    // The window and the worker scopes are global objects: their attributes are read with
    // no `this`, so they keep no check.
    const globalInterface = name === 'Window' || name.endsWith('GlobalScope');
    for (const k of Object.getOwnPropertyNames(P)) {
      if (k === 'constructor') continue;
      const pd = Object.getOwnPropertyDescriptor(P, k);
      if (!pd.configurable) continue;
      let changed = false;
      if (!pd.enumerable) { pd.enumerable = true; changed = true; }
      if (typeof pd.get === 'function') {
        // An attribute getter throws a TypeError for a `this` that is not an object of the
        // interface (Web IDL §3.7.6). Most getters do already (they read the object's state);
        // one that answers for a plain object gets the check in front. Asked once, here.
        if (!globalInterface) {
          let throws = false;
          try { pd.get.call({}); } catch (e) { throws = e instanceof TypeError; }
          if (!throws) {
            const g = pd.get;
            pd.get = function () { if (!(this instanceof C)) throw new TypeError('Illegal invocation'); return g.call(this); };
            changed = true;
          }
        }
        // the names of the accessor functions: "get x" and "set x" (Web IDL §3.7.6)
        if (pd.get.name !== 'get ' + k) Object.defineProperty(pd.get, 'name', { value: 'get ' + k, configurable: true });
        if (typeof pd.set === 'function' && pd.set.name !== 'set ' + k) Object.defineProperty(pd.set, 'name', { value: 'set ' + k, configurable: true });
      }
      if (changed) Object.defineProperty(P, k, pd);
    }
    for (const k of Object.getOwnPropertyNames(C)) {
      if (k === 'prototype' || k === 'length' || k === 'name') continue;
      const sd = Object.getOwnPropertyDescriptor(C, k);
      if (sd.configurable && !sd.enumerable) { sd.enumerable = true; Object.defineProperty(C, k, sd); }
    }
  }

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
      let C = type.startsWith('pointer') ? PointerEvent : type === 'click' || type.startsWith('mouse') ? MouseEvent : type === 'message' ? MessageEvent : Event;
      const init = { bubbles: (flags & 1) !== 0, cancelable: (flags & 2) !== 0, composed: (flags & 4) !== 0, view: window };
      // The pointer's coordinates, buttons and pointer fields, as Lean gives them; the key of
      // a keyboard event; the inputType and data of an input event of an editing command.
      let data = {};
      const keyOrInput = type === 'keydown' || type === 'keyup' || type === 'keypress' || type === 'beforeinput' || type === 'input';
      if (C !== Event || keyOrInput) { const s = n.query(0, 16, ''); if (typeof s === 'string' && s !== '') { try { data = JSON.parse(s); } catch {} } }
      if (keyOrInput && typeof data.key === 'string') C = KeyboardEvent;
      else if (keyOrInput && typeof data.inputType === 'string') C = InputEvent;
      // shadowframes: a message from another session (HTML.FrameSessions): its data is
      // serialized; its source is the frame it came through, or the parent.
      let via = -1;
      if (C === MessageEvent) { try { data.data = JSON.parse(data.data); } catch { data.data = null; } via = data.frame; data.source = data.frame >= 0 ? opaqueWindow(data.frame) : parentWindow(); delete data.frame; }
      const e = new C(type, Object.assign({}, data, init));
      for (const k of ['pageX', 'pageY', 'offsetX', 'offsetY', 'movementX', 'movementY']) if (typeof data[k] === 'number') state(e)[k] = data[k];
      if (C === KeyboardEvent && typeof data.keyCode === 'number') { state(e).keyCode = data.keyCode; state(e).which = data.keyCode; }
      state(e).trusted = true;
      if (type === 'DOMContentLoaded') readyState = 'interactive';
      if (type === 'load' && target === WINDOW) readyState = 'complete';
      if (type === 'load' && target !== WINDOW && target !== 0 && info(target, 29) >= 0) frameLoad(target);
      // A message from a frame's own session is for the window of the document that holds
      // its iframe: a same-origin frame's window when the iframe is in that frame's document.
      if (via >= 0 && target === WINDOW) {
        const d = info(via, 7);
        if (d > 0) { const before = scriptDocument; scriptDocument = wrap(d); try { return dispatch(frameTarget(d), e) ? '' : 'prevented'; } finally { scriptDocument = before; } }
      }
      return dispatch(wrapTarget(target), e) ? '' : 'prevented';
    },
    report(e) { report(e); },
    // A page starts: the content event handler attributes of its elements. The host may
    // run the prelude once on an empty document and copy that state for each page.
    start() { if (ttStart !== null) ttStart(); scanHandlers(0, false); },
    script(id) { currentScript = id < 0 ? null : wrap(id); const d = id < 0 ? 0 : info(id, 7); scriptDocument = d > 0 ? wrap(d) : null; if (d > 0 && ttDoc !== null) ttDoc(d); },
    url(u) { href = String(u); },
    release(id) { callbacks.delete(id); },
    // Section workers: this realm becomes a dedicated worker's global scope.
    worker(url, name) { makeWorkerScope(String(url), String(name)); },
  };
})
