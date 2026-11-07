// This function is serialized as source and runs INSIDE the script engine, never in
// the browser's JS realm. It exposes a bounded projection of Lean node handles.
// Every DOM change is a typed command that Lean validates and applies
// (WebRenderScript.applyCommand); queries use Lean's selector matcher. With the
// synchronous Lean capability (lean-dom.mjs), reads see Lean's arena; without it,
// they see this projection and its provisional writes. Issue 1271.
export function installGuest(snapshot) {
  const stringify = JSON.stringify.bind(JSON), parse = JSON.parse.bind(JSON);
  const freeze = Object.freeze.bind(Object), own = Object.hasOwn;
  const mutate = typeof globalThis.__factoidalDOM === 'function' ? globalThis.__factoidalDOM : null;
  const lookup = typeof globalThis.__factoidalQuery === 'function' ? globalThis.__factoidalQuery : null;
  delete globalThis.__factoidalDOM; delete globalThis.__factoidalQuery;
  const initial = Array.isArray(snapshot) ? { nodes: snapshot } : snapshot;
  const records = new Map(), handles = new Map(), callbacks = new Map();
  let connected = new Set(), order = [], next = Number.isInteger(initial.next) ? initial.next : null, nextKnown = next !== null;
  let commands = [], pending = [], logs = [], errors = [], lastDefaultPrevented = false;
  const copy = item => ({ ...item, attributes: { ...item.attributes } });
  const refresh = view => {
    if (!view || !Array.isArray(view.nodes)) throw new TypeError('Invalid Lean DOM response');
    connected = new Set(view.nodes.map(item => item.id));
    order = view.nodes.map(item => item.id);
    for (const item of view.nodes) records.set(item.id, copy(item));
    if (Number.isInteger(view.next)) { next = view.next; nextKnown = true; }
  };
  refresh(initial);
  const budget = () => { if (commands.length + pending.length >= 1024) throw new RangeError('DOM command budget exceeded'); };
  // Send the queued commands to Lean as one batch. On a refusal the batch is not
  // kept, the projection is read again from Lean, and the error goes to the script.
  const flush = () => {
    if (!pending.length || !mutate) return;
    const batch = pending; pending = [];
    try { refresh(parse(mutate(stringify(batch)))); }
    catch (error) { try { refresh(parse(mutate('[]'))); } catch {} throw error; }
    commands.push(...batch);
  };
  const emit = command => {
    budget();
    if (mutate) pending.push(command); else commands.push(command);
  };
  const text = value => {
    value = String(value ?? '');
    if (value.length > 65536) throw new RangeError('DOM string budget exceeded');
    return value;
  };
  const read = () => flush();
  // Attribute names that Lean accepted: name validity (DOM §4.9) depends on the name only,
  // so a later write with the same name can wait for the batch and still not fail there.
  const acceptedNames = new Set();
  // The exact next node id: Lean's, after every queued command.
  const sync = () => { flush(); if (!nextKnown && mutate) refresh(parse(mutate('[]'))); };
  const record = id => { read(); return records.get(id); };
  const outside = name => () => { throw new TypeError(`${name} is outside the foafnaut script profile (issue 1271)`); };
  const camel = name => String(name).replace(/[A-Z]/g, c => '-' + c.toLowerCase());
  const declarations = value => String(value ?? '').split(';').map(item => item.split(':')).filter(p => p.length > 1)
    .map(([k, ...v]) => [k.trim().toLowerCase(), v.join(':').trim()]);
  const listen = (state, type, callback) => {
    if (typeof callback !== 'function' && !(callback && typeof callback.handleEvent === 'function')) return;
    const list = state.listeners[type] ??= [];
    if (list.length >= 32) throw new RangeError('Listener budget exceeded');
    if (!list.includes(callback)) list.push(callback);
  };
  const unlisten = (state, type, callback) => {
    const list = state.listeners[type]; if (!list) return;
    const at = list.indexOf(callback); if (at >= 0) list.splice(at, 1);
  };
  const EVENTS = ['click', 'input', 'keydown', 'keyup'];
  const stateOf = id => {
    let state = callbacks.get(id);
    if (!state) { state = { listeners: {}, handlers: {} }; callbacks.set(id, state); }
    return state;
  };
  const queryIds = (selector, scope) => {
    selector = text(selector);
    if (!lookup) {
      if (/^#[A-Za-z_][A-Za-z0-9_-]*$/.test(selector)) {
        const found = order.find(id => records.get(id)?.attributes.id === selector.slice(1));
        return found === undefined ? [] : [found];
      }
      throw new TypeError('Selector queries need the Lean DOM in the script worker');
    }
    read();
    const answer = parse(lookup(stringify({ selector, scope })));
    if (!Array.isArray(answer.ids)) throw new TypeError('Invalid Lean query response');
    return answer.ids;
  };
  const handleOf = id => {
    if (id === null || id === undefined || !records.has(id)) return null;
    let handle = handles.get(id);
    if (handle) return handle;
    const state = stateOf(id), html = records.get(id).namespace !== 'svg';
    const attributes = () => record(id).attributes;
    const attrName = name => html ? String(name).toLowerCase() : String(name);
    const classTokens = () => String(attributes()[attrName('class')] ?? '').split(/[ \t\n\r\f]+/).filter(Boolean);
    const classList = freeze({
      add(...tokens) { for (const token of tokens) { emit({ op: 'classList', nodeId: id, action: 'add', token: text(token) }); flush(); provisional('class', [...new Set([...classTokens(), String(token)])].join(' ')); } },
      remove(...tokens) { for (const token of tokens) { emit({ op: 'classList', nodeId: id, action: 'remove', token: text(token) }); flush(); provisional('class', classTokens().filter(t => t !== String(token)).join(' ')); } },
      toggle(token, force) {
        token = text(token);
        const has = classTokens().includes(token), want = force === undefined ? !has : !!force;
        if (want !== has) this[want ? 'add' : 'remove'](token);
        return want;
      },
      contains(token) { return classTokens().includes(String(token)); },
      get length() { return classTokens().length; },
      get value() { return classTokens().join(' '); },
      item(i) { return classTokens()[i] ?? null; }
    });
    // A provisional write for a projection with no Lean capability; Lean's answer replaces it.
    const provisional = (name, value) => {
      if (mutate) return;
      const target = records.get(id).attributes;
      if (value === null) delete target[attrName(name)]; else target[attrName(name)] = value;
    };
    const setStyle = (property, value) => {
      property = text(property).trim().toLowerCase(); value = text(value);
      emit({ op: 'setStyleProperty', nodeId: id, property, value });
      flush();
      if (!mutate) {
        const rest = declarations(attributes().style).filter(([k]) => k !== property);
        if (value.trim()) rest.push([property, value.trim()]);
        provisional('style', rest.length ? rest.map(([k, v]) => `${k}: ${v}`).join('; ') : null);
      }
    };
    const style = new Proxy(freeze({
      setProperty(property, value) { setStyle(property, value ?? ''); },
      removeProperty(property) { const old = this.getPropertyValue(property); setStyle(property, ''); return old; },
      getPropertyValue(property) {
        const found = declarations(attributes().style).find(([k]) => k === String(property).trim().toLowerCase());
        return found ? found[1] : '';
      },
      get cssText() { return attributes().style ?? ''; }
    }), {
      get(target, key) { return typeof key !== 'string' || key in target ? target[key] : target.getPropertyValue(camel(key)); },
      set(target, key, value) {
        if (typeof key !== 'string' || key in target) throw new TypeError(`style.${String(key)} can not be set`);
        setStyle(camel(key), value ?? ''); return true;
      }
    });
    const childIds = () => { read(); return order.filter(child => records.get(child)?.parent === id && connected.has(child)); };
    const node = {
      nodeId: id, nodeType: 1,
      get tagName() { const name = records.get(id).tagName; return html ? name.toUpperCase() : name; },
      get nodeName() { return this.tagName; },
      get localName() { return records.get(id).tagName; },
      get namespaceURI() { return html ? 'http://www.w3.org/1999/xhtml' : 'http://www.w3.org/2000/svg'; },
      get isConnected() { read(); return connected.has(id); },
      get id() { return attributes().id ?? ''; },
      set id(value) { this.setAttribute('id', value); },
      get className() { return attributes()[attrName('class')] ?? ''; },
      set className(value) { this.setAttribute('class', value); },
      get textContent() { return record(id).textContent; },
      set textContent(value) {
        value = text(value);
        emit({ op: 'setTextContent', nodeId: id, value }); nextKnown = false;
        // Without Lean the projection keeps the write; Lean's answer replaces it.
        if (!mutate) records.get(id).textContent = value;
      },
      get innerText() { return this.textContent; },
      set innerText(value) { this.textContent = value; },
      get innerHTML() { return outside('innerHTML')(); },
      set innerHTML(_) { outside('innerHTML')(); },
      get outerHTML() { return outside('outerHTML')(); },
      getAttribute(name) {
        const values = attributes(), key = attrName(name);
        return own(values, key) ? values[key] : null;
      },
      hasAttribute(name) { return own(attributes(), attrName(name)); },
      setAttribute(name, value) {
        name = text(name); value = text(value);
        emit({ op: 'setAttribute', nodeId: id, name, value });
        if (!mutate) provisional(name, value);
        else if (!acceptedNames.has(name)) { flush(); acceptedNames.add(name); }
      },
      removeAttribute(name) {
        name = text(name);
        emit({ op: 'removeAttribute', nodeId: id, name });
        provisional(name, null);
      },
      classList, style,
      get dataset() { return outside('dataset')(); },
      get parentNode() { return handleOf(record(id)?.parent ?? null); },
      get parentElement() { return this.parentNode; },
      get children() { return childIds().map(handleOf); },
      get childElementCount() { return childIds().length; },
      get firstElementChild() { return handleOf(childIds()[0] ?? null); },
      get lastElementChild() { const list = childIds(); return handleOf(list[list.length - 1] ?? null); },
      appendChild(child) {
        if (!child || typeof child.nodeId !== 'number') throw new TypeError('appendChild needs an element of this document');
        emit({ op: 'appendChild', nodeId: id, child: child.nodeId });
        flush();
        return child;
      },
      append(...children) { for (const child of children) this.appendChild(child); },
      removeChild(child) {
        if (!child || typeof child.nodeId !== 'number') throw new TypeError('removeChild needs an element of this document');
        emit({ op: 'removeChild', nodeId: id, child: child.nodeId });
        flush();
        return child;
      },
      remove() { const parent = this.parentNode; if (parent) parent.removeChild(this); },
      querySelector(selector) { return handleOf(queryIds(selector, id)[0] ?? null); },
      querySelectorAll(selector) { return freeze(queryIds(selector, id).map(handleOf)); },
      addEventListener(type, callback) {
        if (!EVENTS.includes(type)) throw new TypeError(`Only ${EVENTS.join(', ')} listeners are supported`);
        listen(state, type, callback);
      },
      removeEventListener(type, callback) { unlisten(state, type, callback); },
      getBoundingClientRect: outside('getBoundingClientRect'),
      focus() {}, blur() {}
    };
    for (const type of EVENTS) Object.defineProperty(node, 'on' + type, {
      get() { return state.handlers[type] ?? null; },
      set(callback) {
        if (callback !== null && typeof callback !== 'function') throw new TypeError(`on${type} requires a function`);
        state.handlers[type] = callback;
      }
    });
    handle = freeze(node);
    handles.set(id, handle);
    return handle;
  };
  const create = (tag, namespace) => {
    if (!mutate) throw new TypeError('createElement needs the Lean DOM in the script worker');
    tag = text(tag);
    if (!nextKnown) sync();
    if (!nextKnown || next === null) throw new TypeError('createElement: the next node id is not known');
    const id = next;
    emit({ op: 'createElement', nodeId: id, tagName: tag, namespace });
    flush();
    next = id + 1;
    records.set(id, { id, tagName: namespace === 'html' ? tag.toLowerCase() : tag, namespace, parent: null, attributes: {}, textContent: '' });
    return handleOf(id);
  };
  const documentState = stateOf('document'), windowState = stateOf('window');
  const document = {
    nodeType: 9,
    getElementById(name) {
      read();
      const found = order.find(id => connected.has(id) && records.get(id)?.attributes.id === String(name));
      return handleOf(found ?? null);
    },
    querySelector(selector) { return handleOf(queryIds(selector, 0)[0] ?? null); },
    querySelectorAll(selector) { return freeze(queryIds(selector, 0).map(handleOf)); },
    getElementsByTagName(name) { return freeze(queryIds(String(name), 0).map(handleOf)); },
    getElementsByClassName(name) { return freeze(queryIds('.' + String(name).trim().split(/\s+/).join('.'), 0).map(handleOf)); },
    createElement(tag) { return create(tag, 'html'); },
    createElementNS(namespace, tag) {
      if (namespace === 'http://www.w3.org/2000/svg') return create(tag, 'svg');
      if (namespace === 'http://www.w3.org/1999/xhtml') return create(tag, 'html');
      throw new TypeError('createElementNS supports the HTML and SVG namespaces');
    },
    createTextNode: outside('createTextNode'),
    get body() { read(); return handleOf(order.find(id => records.get(id)?.tagName === 'body') ?? null); },
    get documentElement() { read(); return handleOf(order[0] ?? null); },
    addEventListener(type, callback) {
      if (!EVENTS.includes(type)) throw new TypeError(`Only ${EVENTS.join(', ')} listeners are supported`);
      listen(documentState, type, callback);
    },
    removeEventListener(type, callback) { unlisten(documentState, type, callback); }
  };
  Object.defineProperty(globalThis, 'document', { value: freeze(document) });
  // Timers and animation frames (HTML §8.6, §8.10). The host clock of the turn is
  // `clock`; the host asks for a turn when the next timer is due or a frame is wanted.
  let clock = 0, timerSeq = 0, frameSeq = 0;
  const timers = new Map(), frames = new Map();
  const schedule = (callback, ms, args, repeat) => {
    if (typeof callback !== 'function') throw new TypeError('Timers take a function; code strings are outside this profile');
    if (timers.size >= 256) throw new RangeError('Timer budget exceeded');
    const delay = Math.min(2147483647, Math.max(0, Number(ms) || 0));
    const id = ++timerSeq;
    timers.set(id, { callback, args, due: clock + (repeat ? Math.max(4, delay) : delay), interval: repeat ? Math.max(4, delay) : null });
    return id;
  };
  const report = error => {
    if (errors.length < 8) errors.push(text(String(error?.name ? `${error.name}: ${error.message}` : error)).slice(0, 512));
  };
  const call = (callback, self, args) => {
    try {
      if (typeof callback === 'function') return callback.apply(self, args);
      return callback.handleEvent(...args);
    } catch (error) {
      // An interrupt (the budget ended) stops the turn; any other error is reported and the turn goes on.
      if (error?.name === 'InternalError') throw error;
      report(error);
    }
  };
  const timerGlobals = {
    setTimeout: (callback, ms, ...args) => schedule(callback, ms, args, false),
    setInterval: (callback, ms, ...args) => schedule(callback, ms, args, true),
    clearTimeout: id => { timers.delete(id); },
    clearInterval: id => { timers.delete(id); },
    requestAnimationFrame: callback => {
      if (typeof callback !== 'function') throw new TypeError('requestAnimationFrame takes a function');
      if (frames.size >= 256) throw new RangeError('Animation frame budget exceeded');
      const id = ++frameSeq; frames.set(id, callback); return id;
    },
    cancelAnimationFrame: id => { frames.delete(id); },
    queueMicrotask: callback => { if (typeof callback === 'function') Promise.resolve().then(callback); }
  };
  for (const [name, value] of Object.entries(timerGlobals)) Object.defineProperty(globalThis, name, { value: freeze(value) });
  Object.defineProperty(globalThis, 'performance', { value: freeze({ now: () => clock }) });
  Object.defineProperty(globalThis, 'window', { value: globalThis });
  Object.defineProperty(globalThis, 'addEventListener', { value: (type, callback) => {
    if (!EVENTS.includes(type)) throw new TypeError(`Only ${EVENTS.join(', ')} listeners are supported`);
    listen(windowState, type, callback);
  } });
  Object.defineProperty(globalThis, 'removeEventListener', { value: (type, callback) => unlisten(windowState, type, callback) });
  Object.defineProperty(globalThis, 'console', { value: freeze(Object.fromEntries(['log', 'info', 'warn', 'error', 'debug'].map(name => [name, (...values) => {
    if (logs.length < 32) logs.push(text(values.map(String).join(' ')));
  }]))) });
  Object.defineProperty(globalThis, 'alert', { value: outside('alert') });
  Object.defineProperty(globalThis, 'fetch', { value: outside('fetch') });
  Object.defineProperty(globalThis, '__factoidalClock', { value: now => { clock = Number(now) || clock; } });
  Object.defineProperty(globalThis, '__factoidalTick', { value: now => {
    clock = Number(now) || clock;
    for (let ran = 0; ran < 64; ran++) {
      let chosen;
      for (const [id, timer] of timers) if (timer.due <= clock && (!chosen || timer.due < chosen[1].due)) chosen = [id, timer];
      if (!chosen) break;
      const [id, timer] = chosen;
      if (timer.interval === null) timers.delete(id); else timer.due = Math.max(timer.due + timer.interval, clock + 1);
      call(timer.callback, globalThis, timer.args);
    }
  } });
  Object.defineProperty(globalThis, '__factoidalFrame', { value: now => {
    clock = Number(now) || clock;
    const due = [...frames.values()]; frames.clear();
    for (const callback of due) call(callback, globalThis, [clock]);
  } });
  // One event through its path: the target, its ancestors, the document, the window.
  // A keyboard event has no focused element in this profile: its target is the document.
  Object.defineProperty(globalThis, '__factoidalDispatch', { value: wire => {
    const event = parse(wire);
    if (!EVENTS.includes(event.type)) throw new TypeError('Unknown event type');
    const path = [];
    if (typeof event.nodeId === 'number') {
      read();
      if (!records.has(event.nodeId)) throw new TypeError('Unknown event target');
      for (let id = event.nodeId, steps = 0; id !== null && id !== undefined && steps < 1024; id = records.get(id)?.parent, steps++) path.push([handleOf(id), stateOf(id)]);
    }
    path.push([document, documentState], [globalThis, windowState]);
    let defaultPrevented = false, stopped = false;
    const target = path[0][0];
    const delivered = { type: event.type, target, currentTarget: target, cancelable: true, bubbles: true, timeStamp: clock,
      get defaultPrevented() { return defaultPrevented; },
      preventDefault() { defaultPrevented = true; },
      stopPropagation() { stopped = true; },
      stopImmediatePropagation() { stopped = true; } };
    if (event.type === 'keydown' || event.type === 'keyup') {
      Object.assign(delivered, { key: String(event.key ?? ''), code: String(event.code ?? ''), shiftKey: !!event.shiftKey, metaKey: !!event.metaKey, altKey: !!event.altKey, ctrlKey: !!event.ctrlKey, repeat: false });
    }
    for (const [current, state] of path) {
      delivered.currentTarget = current;
      const handler = state.handlers[event.type];
      if (handler && call(handler, current, [delivered]) === false) defaultPrevented = true;
      for (const callback of (state.listeners[event.type] ?? []).slice()) call(callback, current, [delivered]);
      if (stopped) break;
    }
    lastDefaultPrevented = defaultPrevented;
  } });
  Object.defineProperty(globalThis, '__factoidalDrain', { value: () => {
    // A batch Lean refuses here is reported, and none of it is kept.
    try { flush(); } catch (error) { report(error); }
    const listeners = [], document = [];
    for (const [key, state] of callbacks) {
      const types = EVENTS.filter(type => state.handlers[type] || state.listeners[type]?.length);
      if (!types.length) continue;
      if (key === 'document' || key === 'window') { for (const type of types) if (!document.includes(type)) document.push(type); }
      else if (connected.has(key)) for (const type of types) if (type === 'click' || type === 'input') listeners.push({ nodeId: key, type });
    }
    let due = null;
    for (const timer of timers.values()) if (due === null || timer.due < due) due = timer.due;
    const wire = stringify({ commands, listeners, documentListeners: document, logs, errors, defaultPrevented: lastDefaultPrevented,
      timer: due === null ? null : Math.max(0, due - clock), frame: frames.size > 0 });
    commands = []; logs = []; errors = []; lastDefaultPrevented = false;
    return wire;
  } });
}

// Parse data as JSON: embedding it as an object literal changes the meaning
// of a real "__proto__" attribute before the binding can inspect it.
export const bootstrap = snapshot => `(${installGuest.toString()})(JSON.parse(${JSON.stringify(JSON.stringify(snapshot))}));`;
