// @ts-self-types="./page-scripts.d.ts"
// The page script runtime of one document, shared by the web build, the desktop
// window and the Hub (issue 1271). It keeps the document's DOM command history,
// runs input, timer and animation frame turns one at a time in the order they come,
// and asks for the next timer or frame turn only after the host has used the last
// batch (`onBatch` resolves when the frame with its commands is shown). Lean
// validates every command and compacts the history; this module makes no DOM,
// CSS, layout or event-target decision.
export function createPageScripts({ session, compact, onBatch = async () => {}, onStop = () => {},
  frameInterval = 16, setTimer = (f, ms) => setTimeout(f, ms), clearTimer = id => clearTimeout(id), now = () => performance.now() } = {}) {
  let commands = [], stopped = null, timer, frameTimer, lastFrame = -Infinity, frameWanted = false;
  const stats = { turns: 0, frames: 0, timers: 0, events: 0, commands: 0, compactions: 0, errors: 0 };
  const stop = reason => {
    if (stopped) return;
    stopped = String(reason?.message ?? reason ?? 'stopped');
    clearTimer(timer); clearTimer(frameTimer); timer = frameTimer = undefined;
    session.reset();
    onStop(stopped);
  };
  // Batches are used one at a time, in the order their turns ended.
  let applying = Promise.resolve();
  const take = (batch, kind) => { const next = applying.then(() => use(batch, kind)); applying = next.catch(() => {}); return next; };
  const use = async (batch, kind) => {
    stats.turns++; stats.commands += batch.commands.length; stats.errors += batch.errors.length;
    if (batch.commands.length) {
      commands = [...commands, ...batch.commands];
      // Lean keeps a shorter history that replays to the same arena (WebRenderScript.compact).
      if (commands.length > 1024 && compact) { commands = await compact(commands); stats.compactions++; }
      if (commands.length > 4096) throw Error('Document DOM command history exceeds 4096 after compaction');
    }
    await onBatch(batch, kind);
    schedule(batch);
    return batch;
  };
  const run = (kind, work) => {
    if (stopped) return Promise.reject(Error(`Page scripts stopped: ${stopped}`));
    return work().then(batch => take(batch, kind)).catch(error => { stop(error); throw error; });
  };
  const schedule = batch => {
    if (stopped) return;
    // The latest batch states every timer of the guest: one host timer for the earliest.
    clearTimer(timer); timer = undefined;
    if (batch.timer !== null) timer = setTimer(() => { timer = undefined; stats.timers++; run('timers', () => session.timers()).catch(() => {}); }, Math.max(1, batch.timer));
    frameWanted = batch.frame;
    if (frameWanted && frameTimer === undefined) {
      const wait = Math.max(0, lastFrame + frameInterval - now());
      frameTimer = setTimer(() => {
        frameTimer = undefined;
        if (stopped || !frameWanted) return;
        lastFrame = now(); stats.frames++;
        run('frame', () => session.frame()).catch(() => {});
      }, wait);
    }
  };
  return {
    get commands() { return commands; },
    get stopped() { return stopped; },
    get listeners() { return session.listeners; },
    get documentListeners() { return session.documentListeners; },
    get animating() { return frameWanted || frameTimer !== undefined; },
    stats,
    start(args) { return run('start', () => session.start(args)); },
    /** A click or input event on a node, or a key event on the document. */
    dispatch(event) { stats.events++; return run('event', () => session.dispatch(event)); },
    /** The node of the click target: a node with a listener, else the document's listener. */
    wants(type, nodeId) {
      return session.listeners.some(l => l.type === type && l.nodeId === nodeId) || session.documentListeners.includes(type);
    },
    stop
  };
}
