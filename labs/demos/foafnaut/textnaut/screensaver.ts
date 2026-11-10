// textnaut --screensaver [NAME]: colour screensavers for the terminal. Uses no page and no engine.
// Two pixels per cell (half blocks) where the locale has them; background colour or a character
// ramp where it does not. 24-bit, 256, 16 or no colour. Keys: Tab, Space and n for the next
// effect, b for the one before (history is kept), q or Ctrl-C to quit; any other key quits too.
// The terminal is restored on every way out. Started from the browser's help screen, the same
// loop runs on the browser's screen and input and returns to it.
import { type Level } from "./grid.ts";
import { Input, keysOf } from "./input.ts";
import { eggs, savers } from "./savers.ts";
import { Navigator, Renderer, type Saver } from "./saver-core.ts";

export { eggs, savers } from "./savers.ts";
export { mengerCells4, mengerGrid, rotate4, unrotate4 } from "./savers.ts";
export { hsv, mulberry32, Navigator, Presenter, Renderer, Surface, type Saver } from "./saver-core.ts";

/** Savers named on the command line or chosen at random: the normal list, and the hidden ones in December. */
export function pool(month = new Date().getMonth() + 1): Saver[] {
  return month === 12 ? [...savers, ...eggs] : savers;
}
/** Any saver by name, hidden ones included; `xmas` is a short name for the tree. */
export function findSaver(name: string): Saver | undefined {
  return [...savers, ...eggs].find((s) => s.name === name) ?? (name === "xmas" ? eggs[0] : undefined);
}
/** The order Tab and Space walk: the normal list (and the hidden ones in December); a hidden saver outside December walks the hidden ones. */
export function orderFor(name: string, month = new Date().getMonth() + 1): string[] {
  const saver = findSaver(name);
  return (saver?.egg && month !== 12 ? eggs : pool(month)).map((s) => s.name);
}

export type SaverIO = {
  /** Where keys come from; absent when there is no terminal input (a pipe or a test): no key then ends it. */
  input?: { next(timeout?: number): Promise<Uint8Array | null>; closed: boolean };
  write: (s: string) => void;
  size: () => { columns: number; rows: number };
  level: Level;
  utf8: boolean;
  /** Inside the browser: it owns the alternate screen, raw mode and signals. */
  embedded?: boolean;
};

export type SaverEnd = "quit" | "exit";

/**
 * Runs savers until a quit key. Returns "quit" for q or another key (back to whatever started
 * it) or the end of input, "exit" for Ctrl-C. `frames` stops after that many frames.
 */
export async function runSavers(io: SaverIO, start: string | undefined, options: { frames?: number; seed?: number; month?: number; fps?: number; stop?: () => boolean; onFrame?: (ms: number) => void } = {}): Promise<SaverEnd> {
  const month = options.month ?? new Date().getMonth() + 1;
  const seed = options.seed ?? (Date.now() & 0x7fffffff);
  const first = start ? findSaver(start)! : (() => { const p = pool(month); return p[Math.floor(Math.random() * p.length)]; })();
  const nav = new Navigator(first.name, orderFor(first.name, month));
  const base = 1000 / (options.fps ?? 30);
  let interval = base;
  let serial = 0;
  const make = () => new Renderer(findSaver(nav.current)!, { seed: seed + serial++ * 7919, level: io.level, utf8: io.utf8 });
  let renderer = make();
  const begin = performance.now();
  let last = begin, size = io.size();
  const caption = () => `${nav.current}: ${findSaver(nav.current)!.help}  [Tab] next  [b] back  [q] quit`;
  for (let n = 0; !options.stop?.() && (options.frames === undefined || n < options.frames); n++) {
    const now = performance.now();
    size = io.size();
    const t = (now - begin) / 1000, dt = (now - last) / 1000;
    last = now;
    const bytes = renderer.frame(t, dt, size.columns, size.rows, caption());
    // Synchronized output, where the terminal has it: a frame appears whole.
    io.write("\x1b[?2026h" + bytes + "\x1b[?2026l");
    options.onFrame?.(performance.now() - now);
    // Cap the output at about 6 MB a second: a full 24-bit redraw of a big terminal runs slower than a small one.
    interval = Math.max(base, Math.min(70, bytes.length / 6000));
    const due = now + interval;
    // Wait for the next frame; a key or a resize ends the wait early. No busy loop.
    while (!options.stop?.()) {
      const wait = due - performance.now();
      if (!io.input) { if (wait > 0) await new Promise((r) => setTimeout(r, wait)); break; }
      const chunk = await io.input.next(Math.max(1, wait));
      let redraw = false;
      if (chunk) for (const key of keysOf(chunk)) {
        const result = nav.key(key);
        if (result === "quit" || result === "exit") return result;
        if (result === "switch") { renderer = make(); redraw = true; last = performance.now(); }
      }
      if (io.input.closed) return "quit";
      const now2 = io.size();
      if (now2.columns !== size.columns || now2.rows !== size.rows) redraw = true;
      if (redraw || performance.now() >= due) break;
    }
  }
  return "quit";
}

/** The standalone command: owns the terminal, restores it on every way out. */
export async function screensaver(name: string | undefined, frames?: number, caps: { level: Level; utf8: boolean } = { level: 2, utf8: true }): Promise<number> {
  if (name && !findSaver(name)) { console.error(`textnaut: no screensaver ${name}; there are: ${savers.map((s) => s.name).join(", ")}`); return 2; }
  const encoder = new TextEncoder();
  let dead = false;
  const write = (s: string) => {
    let bytes = encoder.encode(s);
    try { while (bytes.length && !dead) bytes = bytes.subarray(Deno.stdout.writeSync(bytes)); } catch { dead = true; }
  };
  const tty = Deno.stdin.isTerminal() && Deno.stdout.isTerminal();
  const size = () => { if (!tty) return { columns: 80, rows: 24 }; try { const c = Deno.consoleSize(); return { columns: Math.max(1, c.columns), rows: Math.max(1, c.rows) }; } catch { return { columns: 80, rows: 24 }; } };
  let stopping = false, restored = false;
  const input = tty ? new Input() : undefined;
  const stop = () => { stopping = true; input?.poke(); };
  const signals: Deno.Signal[] = ["SIGINT", "SIGTERM", "SIGHUP", "SIGQUIT"];
  const winch = () => input?.poke();
  const restore = () => {
    if (restored) return;
    restored = true;
    for (const s of signals) { try { Deno.removeSignalListener(s, stop); } catch { /* not installed */ } }
    try { Deno.removeSignalListener("SIGWINCH", winch); } catch { /* not installed */ }
    write("\x1b[?2026l\x1b[0m\x1b[?7h\x1b[?25h\x1b[?1049l");
    if (tty) { try { Deno.stdin.setRaw(false); } catch { /* the terminal has gone */ } }
  };
  const fail = (error: unknown) => { restore(); console.error(`textnaut: ${error instanceof Error ? error.message : error}`); Deno.exit(1); };
  const onError = (event: ErrorEvent | PromiseRejectionEvent) => { event.preventDefault(); fail("error" in event ? event.error : event.reason); };
  globalThis.addEventListener("unhandledrejection", onError);
  globalThis.addEventListener("error", onError);
  for (const s of signals) Deno.addSignalListener(s, stop);
  if (tty) Deno.addSignalListener("SIGWINCH", winch);
  write("\x1b[?1049h\x1b[?25l\x1b[?7l\x1b[2J");
  try {
    if (tty) Deno.stdin.setRaw(true);
    await runSavers({ input, write, size, level: caps.level, utf8: caps.utf8 }, name, { frames, stop: () => stopping });
  } finally {
    restore();
    globalThis.removeEventListener("unhandledrejection", onError);
    globalThis.removeEventListener("error", onError);
  }
  return 0;
}
