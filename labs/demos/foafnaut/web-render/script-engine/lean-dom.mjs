// Synchronous DOM authority for a script engine worker. The separate Lean instance
// owns parsing, mutation semantics, selector matching and history compaction
// (WebRenderScript.lean); this module transports checked JSON.
const encoder = new TextEncoder();
export async function createLeanDOM({ source, url, commands = [], moduleURL }, engine) {
  if (typeof source !== 'string' || source.includes('\0') || encoder.encode(source).length > 1048576) throw Error('Invalid script document source');
  if (typeof url !== 'string' || !Array.isArray(commands) || commands.length > 4096) throw Error('Invalid script document context');
  if (!engine) {
    const { default: createModule } = await import(moduleURL);
    engine = await createModule();
  }
  const call = request => {
    const wire = JSON.stringify(request);
    if (encoder.encode(wire).length > 20971520) throw Error('DOM history exceeds transport budget');
    const pointer = engine.ccall('web_document_call', 'number', ['string','string','number','number'], [source,wire,1,1]);
    if (!pointer) throw Error('Lean DOM initialization or allocation failed');
    let text;
    try { text = engine.UTF8ToString(pointer); }
    finally { engine.ccall('web_render_free', null, ['number'], [pointer]); }
    const answer = JSON.parse(text);
    if (answer.error) {
      const error = Error(answer.error);
      // Keep the DOM exception name (WebIDL §2.8.1) without installing a fake DOMException API.
      const named = /^script command: ([A-Za-z]+Error)$/.exec(answer.error) ?? /^(SyntaxError)\b/.exec(answer.error);
      if (named) error.name = named[1];
      throw error;
    }
    return { answer, text };
  };
  // An engine built before scriptSnapshot answers it with an error; inspect gives the same nodes.
  let snapshotOp = 'scriptSnapshot';
  const snapshot = next => {
    try { return call({ op: snapshotOp, url, commands: next }); }
    catch (error) {
      if (snapshotOp !== 'scriptSnapshot' || !/unknown document operation/.test(String(error.message))) throw error;
      snapshotOp = 'inspect';
      return call({ op: snapshotOp, url, commands: next });
    }
  };
  let history = commands.slice();
  // A command, or a batch of commands applied together: all or none.
  const mutate = commandWire => {
    const parsed = JSON.parse(commandWire), batch = Array.isArray(parsed) ? parsed : [parsed];
    let next = [...history, ...batch];
    if (next.length > 1024) next = call({ op: 'compactCommands', url, commands: next }).answer.commands;
    if (next.length > 4096) throw Error('Document DOM command history exceeds 4096');
    const { answer, text } = snapshot(next);
    if (!Array.isArray(answer.nodes)) throw Error('Invalid Lean DOM snapshot');
    // The engine capability has the same response limit. Check before
    // committing history so a caught rejection cannot leave a hidden write.
    if (encoder.encode(text).length > 2097152) throw Error('Host capability result exceeds budget');
    history = next;
    return text;
  };
  // querySelectorAll over the committed history, with Lean's selector matcher.
  mutate.query = queryWire => {
    const { selector, scope = 0 } = JSON.parse(queryWire);
    return call({ op: 'scriptQuery', url, commands: history, selector: String(selector), scope }).text;
  };
  return mutate;
}
