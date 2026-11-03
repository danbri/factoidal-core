// This function is serialized as source and runs INSIDE QuickJS, never in the
// browser's JS realm. It exposes only a bounded projection of Lean node handles.
export function installGuest(snapshot) {
  const stringify = JSON.stringify.bind(JSON), parse = JSON.parse.bind(JSON);
  const nodes = new Map(), callbacks = new Map();
  let commands = [], logs = [];
  const emit = command => {
    if (commands.length >= 256) throw new RangeError('DOM command budget exceeded');
    commands.push(command);
  };
  const text = value => {
    value = String(value ?? '');
    if (value.length > 65536) throw new RangeError('DOM string budget exceeded');
    return value;
  };
  for (const item of snapshot) {
    let content = item.textContent;
    const attributes = Object.assign(Object.create(null), item.attributes);
    const listeners = [];
    const node = Object.freeze({
      nodeId: item.id, tagName: item.tagName,
      get textContent() { return content; },
      set textContent(value) {
        value = text(value);
        emit({ op: 'setTextContent', nodeId: item.id, value });
        content = value;
      },
      getAttribute(name) { return attributes[String(name)] ?? null; },
      setAttribute(name, value) {
        name = text(name); value = text(value);
        emit({ op: 'setAttribute', nodeId: item.id, name, value });
        attributes[name] = value;
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
  const getElementById = id => [...nodes.values()].find(node => node.getAttribute('id') === String(id)) ?? null;
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
    const delivered = Object.freeze({ type: 'click', target: state.node, currentTarget: state.node });
    if (state.onclick) state.onclick.call(state.node, delivered);
    for (const callback of state.listeners.slice()) callback.call(state.node, delivered);
  } });
  Object.defineProperty(globalThis, '__factoidalDrain', { value: () => {
    const listeners = [];
    for (const [nodeId, state] of callbacks) if (state.onclick || state.listeners.length) listeners.push({ nodeId, type: 'click' });
    const wire = stringify({ commands, listeners, logs });
    commands = []; logs = [];
    return wire;
  } });
}

export const bootstrap = nodes => `(${installGuest.toString()})(${JSON.stringify(nodes)});`;
