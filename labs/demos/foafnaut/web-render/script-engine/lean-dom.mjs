// Synchronous DOM authority for a QuickJS worker. The separate Lean instance
// owns parsing and mutation semantics; this module transports checked JSON.
export async function createLeanDOM({ source, url, commands = [], moduleURL }, engine) {
  if (typeof source !== 'string' || source.includes('\0') || new TextEncoder().encode(source).length > 1048576) throw Error('Invalid script document source');
  if (typeof url !== 'string' || !Array.isArray(commands) || commands.length > 4096) throw Error('Invalid script document context');
  if (!engine) {
    const { default: createModule } = await import(moduleURL);
    engine = await createModule();
  }
  let history = commands.slice();
  return commandWire => {
    if (history.length >= 4096) throw Error('Document DOM command history exceeds 4096');
    const command = JSON.parse(commandWire), next = [...history, command];
    const request = JSON.stringify({ op: 'inspect', url, commands: next });
    if (new TextEncoder().encode(request).length > 20971520) throw Error('DOM history exceeds transport budget');
    const pointer = engine.ccall('web_document_call', 'number', ['string','string','number','number'], [source,request,1,1]);
    if (!pointer) throw Error('Lean DOM initialization or allocation failed');
    let result;
    try { result = engine.UTF8ToString(pointer); }
    finally { engine.ccall('web_render_free', null, ['number'], [pointer]); }
    const snapshot = JSON.parse(result);
    if (snapshot.error) {
      const error = Error(snapshot.error);
      // The currently exposed setAttribute operation can report this DOM
      // error. Preserve its name without installing a fake DOMException API.
      if (snapshot.error === 'script command: InvalidCharacterError') error.name = 'InvalidCharacterError';
      throw error;
    }
    if (!Array.isArray(snapshot.nodes)) throw Error('Invalid Lean DOM snapshot');
    // The QuickJS capability has the same response limit. Check before
    // committing history so a caught rejection cannot leave a hidden write.
    if (new TextEncoder().encode(result).length > 2097152) throw Error('Host capability result exceeds budget');
    history = next;
    return result;
  };
}

// The HTML event loop of the page (Lean `L4Factoidal.EventLoop`, op `eventLoop`).
// Lean decides which callback runs next, the timer and frame ids, and the order
// of event listeners. This object keeps the loop state between calls; QuickJS
// only runs the callbacks it is told to run. No host timer decides any order.
export async function createLeanLoop({ moduleURL, engine } = {}) {
  if (!engine) {
    const { default: createModule } = await import(moduleURL);
    engine = await createModule();
  }
  const call = request => {
    const pointer = engine.ccall('web_document_call', 'number', ['string','string','number','number'], ['', JSON.stringify(request), 1, 1]);
    if (!pointer) throw Error('Lean event loop allocation failed');
    let text;
    try { text = engine.UTF8ToString(pointer); }
    finally { engine.ccall('web_render_free', null, ['number'], [pointer]); }
    const answer = JSON.parse(text);
    if (answer.error) throw Error(answer.error);
    return answer;
  };
  let state = call({ op: 'eventLoop', action: 'init' }).state;
  const loop = {
    engine,
    get clock() { return state.clock; },
    // The due time of the first armed timer, or null; and whether frame callbacks wait.
    get nextDue() { return state.timers.length ? state.timers[0][2] : null; },
    get framesWaiting() { return state.frames.length > 0; },
    act(action, fields = {}) {
      if (action === 'dispatch' || action === 'afterStop') return call({ op: 'eventLoop', action, ...fields });
      const answer = call({ op: 'eventLoop', action, ...fields, state });
      state = answer.state;
      delete answer.state;
      return answer;
    },
    // The capability QuickJS calls: one JSON action in, its answer out, without the state.
    capability(wire) {
      const request = JSON.parse(wire);
      if (!request || typeof request.action !== 'string' || ['init','step','advance','render','frameStep'].includes(request.action)) throw Error('Event loop action not allowed from page script');
      const { action, ...fields } = request;
      return JSON.stringify(loop.act(action, fields));
    }
  };
  return loop;
}
