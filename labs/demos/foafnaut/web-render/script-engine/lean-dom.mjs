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
