// This function is serialized as source and runs INSIDE QuickJS, never in the
// browser's JS realm. It exposes only a bounded projection of Lean node handles.
export function installGuest(snapshot) {
  const stringify = JSON.stringify.bind(JSON), parse = JSON.parse.bind(JSON);
  const freeze = Object.freeze.bind(Object);
  const own = Object.hasOwn;
  const nodes = new Map(), callbacks = new Map();
  const records = new Map(snapshot.map(item => [item.id, { ...item, attributes: { ...item.attributes } }]));
  let connected = new Set(records.keys());
  const mutate = typeof globalThis.__factoidalDOM === 'function' ? globalThis.__factoidalDOM : null;
  if (mutate) delete globalThis.__factoidalDOM;
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
  for (const item of snapshot) {
    const record = () => records.get(item.id);
    const listeners = [];
    const node = Object.freeze({
      nodeId: item.id, tagName: item.tagName,
      get isConnected() { return connected.has(item.id); },
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
      addEventListener(type, callback) {
        if (type !== 'click' || typeof callback !== 'function') throw new TypeError('Only click listeners are supported');
        if (listeners.length >= 32) throw new RangeError('Listener budget exceeded');
        if (!listeners.includes(callback)) listeners.push(callback);
      },
      get onclick() { return callbacks.get(item.id)?.onclick ?? null; },
      set onclick(callback) {
        if (callback !== null && typeof callback !== 'function') throw new TypeError('onclick requires a function');
        callbacks.get(item.id).onclick = callback;
      }
    });
    callbacks.set(item.id, { node, listeners, onclick: null });
    nodes.set(item.id, node);
  }
  const getElementById = id => [...connected].map(key => nodes.get(key)).find(node => node && node.getAttribute('id') === String(id)) ?? null;
  Object.defineProperty(globalThis, 'document', { value: Object.freeze({
    getElementById,
    querySelector(selector) {
      if (typeof selector !== 'string' || !/^#[A-Za-z_][A-Za-z0-9_-]*$/.test(selector)) throw new TypeError('Only simple #id selectors are supported');
      return getElementById(selector.slice(1));
    }
  }) });
  Object.defineProperty(globalThis, 'console', { value: Object.freeze({ log(...values) {
    if (logs.length < 32) logs.push(text(values.map(String).join(' ')));
  } }) });
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
    for (const [nodeId, state] of callbacks) if (connected.has(nodeId) && (state.onclick || state.listeners.length)) listeners.push({ nodeId, type: 'click' });
    const wire = stringify({ commands, listeners, logs, defaultPrevented: lastDefaultPrevented });
    commands = []; logs = []; lastDefaultPrevented = false;
    return wire;
  } });
}

// Parse data as JSON: embedding it as an object literal changes the meaning
// of a real "__proto__" attribute before the binding can inspect it.
export const bootstrap = nodes => `(${installGuest.toString()})(JSON.parse(${JSON.stringify(JSON.stringify(nodes))}));`;
