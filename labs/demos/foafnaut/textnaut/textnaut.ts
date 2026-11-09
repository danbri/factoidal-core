// textnaut: a text-mode web browser on the Foafnaut engine
// (https://github.com/danbri/factoidal-core/issues/371). The engine loads and lays out the page;
// this host maps its text to terminal cells and terminal bytes.
import { loadHTML, type HTMLEngine, type ScriptTurn } from "../native_html_engine.ts";
import { inputURL, loadFontFile, navigationURL, prepareHTML, setScriptHost } from "../native_html_document.ts";
import { barRow, CELL_HEIGHT, CELL_WIDTH, dumpText, fillerRow, type GlyphRun, type Grid, layoutGrid, type Level, type LinkRow, readPaint, sanitizeText, styledRow } from "./grid.ts";
import { useWasm } from "./web-render-select.mjs";

export type Options = { cols: number; rows: number; scripts: boolean; liberal: boolean; verbose: boolean };
type Doc = Awaited<ReturnType<typeof prepareHTML>>;
const decoder = new TextDecoder(), encoder = new TextEncoder();
const here = (path: string) => decodeURIComponent(new URL(path, import.meta.url).pathname);
const isFile = (p?: string) => { if (!p) return false; try { return Deno.statSync(p).isFile; } catch { return false; } };

/** The first native library that exists: the argument, the environment, a local build, the scratch copy. */
export const findNative = (path?: string): string | undefined =>
  [path, Deno.env.get("TEXTNAUT_NATIVE"), here("../.build/web-render/engines/libweb-render.dylib"), here("../../../../.scratch/libweb-render.dylib")].find(isFile);
/** The first Wasm runtime (`web-render.mjs` beside its `.wasm`) that exists. */
export const findWasm = (): string | undefined =>
  [Deno.env.get("TEXTNAUT_WASM_DIR"), here("../.build/native-html/runtime"), here("../../../../.scratch/wasm")]
    .map((dir) => dir ? `${dir}/web-render.mjs` : undefined).find(isFile);

export type Engine = { engine: HTMLEngine; name: "native" | "wasm" };

/** The native library when present, else the Wasm runtime; `--wasm` asks for the Wasm runtime. */
export async function startEngine(wantWasm: boolean, nativePath?: string): Promise<Engine> {
  const native = wantWasm ? undefined : findNative(nativePath);
  if (native) return { engine: await loadHTML(native), name: "native" };
  const wasm = findWasm();
  if (!wasm) throw new Error(wantWasm ? "no Wasm runtime: set TEXTNAUT_WASM_DIR" : "no engine: give --engine FILE, or set TEXTNAUT_NATIVE or TEXTNAUT_WASM_DIR");
  // The query keeps this import away from the import map's entry for the same path.
  useWasm(`file://${encodeURI(wasm)}?runtime`);
  return { engine: await loadHTML(), name: "wasm" };
}

function pageViewport(options: Options, charWidth = CELL_WIDTH) {
  const cols = Math.max(10, options.cols), cellWidth = Math.min(charWidth, 4080 / cols), cellHeight = charWidth * CELL_HEIGHT / CELL_WIDTH;
  return { cols, cellWidth, cellHeight, width: Math.round(cols * cellWidth + 16), height: Math.min(4096, Math.max(240, Math.round(options.rows * CELL_HEIGHT))) };
}

/** Bitmap advance of the font size that has the most characters: one cell is one character of the body text. */
function bodyCharWidth(runs: GlyphRun[]): number {
  const count = new Map<number, number>();
  for (const run of runs) count.set(run.size, (count.get(run.size) ?? 0) + run.text.length);
  let best = 16, most = 0;
  for (const [size, n] of count) if (n > most && size > 0) { best = size; most = n; }
  return best * CELL_WIDTH / 16;
}

/** Run page scripts on the engine's BubblePopJS. Returns false when this engine has none. */
export function enableScripts(engine: HTMLEngine, options: Options): boolean {
  const off = () => { setScriptHost({ start: () => undefined }); return false; };
  if (!options.scripts) return off();
  try { if (!engine.scriptInfo().engines?.includes("bubblepop")) return off(); } catch { return off(); }
  setScriptHost({
    start: (source, url, resources, encoding, mode = {}) => {
      const { width, height } = pageViewport(options);
      const turn = engine.scriptSession(source, {
        action: "start", url, resources, width, height, engine: "bubblepop",
        layout: { url, textScalePercent: 100, ...mode }, ...(encoding ? { encoding } : {}),
      });
      note(turn, options);
      return turn;
    },
  });
  return true;
}
function note(turn: ScriptTurn, options: Options) {
  if (!options.verbose) return;
  for (const line of [...turn.logs, ...turn.errors]) console.error(`page: ${sanitizeText(line)}`);
}

/** A bounded run of the page's timers: up to 8 turns and 1 second of page time. */
function settle(engine: HTMLEngine, doc: Doc, options: Options) {
  const script = doc.script;
  if (!script) return;
  let turn = script.turn, budget = 1000;
  for (let i = 0; i < 8 && turn.nextWake !== null; i++) {
    const ms = Math.max(0, Math.ceil(turn.nextWake - turn.clock));
    if (ms > budget) break;
    budget -= ms;
    turn = engine.scriptSession("", { action: "advance", session: script.session, ms });
    note(turn, options);
    doc.applyTurn(turn);
  }
}

export type Rendered = { doc: Doc; grid: Grid; charWidth: number; ms: { load: number; layout: number; cells: number } };

/** Lay out a loaded page. No fetch and no script runs. With no `charWidth`, a page whose body text is not 16 px is laid out twice. */
export async function layoutDoc(doc: Doc, options: Options, charWidth?: number) {
  const t0 = performance.now();
  type Frame = Parameters<typeof readPaint>[0] & { webRender: { glyphRuns: GlyphRun[]; links: LinkRow[] } };
  const compile = async (width: number) => {
    const view = pageViewport(options, width);
    return { view, artifact: await doc.compile(view.width, view.height) as unknown as Frame };
  };
  let width = charWidth ?? CELL_WIDTH, frame = await compile(width);
  if (charWidth === undefined) {
    const measured = bodyCharWidth(frame.artifact.webRender.glyphRuns);
    if (Math.abs(measured - width) > 0.5) { width = measured; frame = await compile(width); }
  }
  const { view, artifact } = frame;
  const t1 = performance.now();
  const grid = layoutGrid({
    runs: artifact.webRender.glyphRuns, links: artifact.webRender.links as LinkRow[], cols: view.cols, cellWidth: view.cellWidth, cellHeight: view.cellHeight, trimLeft: true,
    paint: readPaint(artifact), resolve: (href) => new URL(href, doc.baseURL).href,
  });
  return { grid, charWidth: width, layout: t1 - t0, cells: performance.now() - t1 };
}

export async function renderPage(engine: HTMLEngine, url: string, options: Options, inline?: string, signal?: AbortSignal): Promise<Rendered> {
  const t0 = performance.now();
  const doc = await prepareHTML(engine, url, signal, inline, { liberal: options.liberal });
  settle(engine, doc, options);
  const load = performance.now() - t0;
  const { grid, charWidth, layout, cells } = await layoutDoc(doc, options);
  return { doc, grid, charWidth, ms: { load, layout, cells } };
}

function parseArgs(args: string[]) {
  const out = { width: 0, dump: false, engine: undefined as string | undefined, wasm: false, font: undefined as string | undefined,
    strict: false, scripts: true, timing: false, verbose: false, colour: undefined as Level | undefined, input: undefined as string | undefined };
  for (let i = 0; i < args.length; i++) {
    const a = args[i];
    if (a === "--width") out.width = Number(args[++i]);
    else if (a === "--dump") out.dump = true;
    else if (a === "--engine") out.engine = args[++i];
    else if (a === "--wasm") out.wasm = true;
    else if (a === "--font") out.font = args[++i];
    else if (a === "--strict") out.strict = true;
    else if (a === "--no-scripts") out.scripts = false;
    else if (a === "--timing") out.timing = true;
    else if (a === "--verbose") out.verbose = true;
    else if (a === "--colour") {
      const level = { none: 0, "16": 1, "256": 2, "24bit": 3 }[args[++i]];
      if (level === undefined) throw new Error("--colour must be none, 16, 256 or 24bit");
      out.colour = level as Level;
    } else if (a.startsWith("--")) throw new Error(`unknown option ${a}`);
    else if (out.input === undefined) out.input = a;
    else throw new Error("give one URL or file");
  }
  if (out.width && !(Number.isInteger(out.width) && out.width >= 20 && out.width <= 300)) throw new Error("--width must be 20 to 300");
  return out;
}
const isURL = (input: string) => /^[a-zA-Z][a-zA-Z0-9+.-]+:/.test(input);
const toURL = (input: string) => isURL(input) ? inputURL(input) : inputURL(input, true);
const reason = (error: unknown) => sanitizeText(String(error instanceof Error ? error.message : error).replace(/^(Error: )?Lean HTML: /, ""));

// ---------------------------------------------------------------- interactive viewer

/** Reads stdin in one loop, so that a query with a timeout does not lose a key. */
class Input {
  private queue: Uint8Array[] = [];
  private wake?: () => void;
  private poked = false;
  closed = false;
  constructor() { this.pump(); }
  private async pump() {
    const buffer = new Uint8Array(4096);
    while (true) { // Ends at the end of input.
      const n = await Deno.stdin.read(buffer).catch(() => null);
      if (n === null) { this.closed = true; this.wake?.(); return; }
      this.queue.push(buffer.slice(0, n));
      this.wake?.();
    }
  }
  /** Make a waiting or the next `next` return at once. */
  poke() { this.poked = true; this.wake?.(); }
  /** The next chunk; null on timeout, on poke or at the end of input. */
  async next(timeout?: number): Promise<Uint8Array | null> {
    if (!this.queue.length && !this.poked && !this.closed) {
      let timer: number | undefined;
      await new Promise<void>((resolve) => {
        this.wake = resolve;
        if (timeout !== undefined) timer = setTimeout(resolve, timeout);
      });
      clearTimeout(timer);
      this.wake = undefined;
    }
    this.poked = false;
    return this.queue.shift() ?? null;
  }
}

export type Caps = { level: Level; osc8: boolean; sync: boolean; utf8: boolean; version: string };

/** What the environment and the terminal's own answers say. No answer means not supported. */
export function capabilities(env: (name: string) => string | undefined, answer: string, forced?: Level): Caps {
  const version = /\x1bP>\|([^\x1b]*)\x1b\\/.exec(answer)?.[1] ?? "";
  const sync = /\x1b\[\?2026;[12]\$y/.test(answer);
  const colourterm = (env("COLORTERM") ?? "").toLowerCase(), term = env("TERM") ?? "";
  const level: Level = forced ?? (env("NO_COLOR") !== undefined || term === "" || term === "dumb" ? 0
    : colourterm === "truecolor" || colourterm === "24bit" ? 3 : /256color/.test(term) ? 2 : 1);
  const program = env("TERM_PROGRAM") ?? "", vte = Number(env("VTE_VERSION") ?? 0);
  const osc8 = !env("TMUX") && !term.startsWith("screen") &&
    (/kitty|wezterm|foot|ghostty|iterm2|alacritty/i.test(version) || /iTerm|WezTerm|vscode|ghostty/i.test(program) ||
      !!env("KITTY_WINDOW_ID") || !!env("WT_SESSION") || vte >= 5000);
  const utf8 = /utf-?8/i.test(env("LC_ALL") || env("LC_CTYPE") || env("LANG") || "");
  return { level, osc8, sync, utf8, version: sanitizeText(version) };
}

async function queryTerminal(input: Input, write: (s: string) => void): Promise<string> {
  write("\x1b[?2026$p\x1b[>0q\x1b[c");
  let answer = "";
  const end = performance.now() + 300;
  while (performance.now() < end && !/\x1b\[\?[0-9;]*c/.test(answer)) {
    const chunk = await input.next(Math.max(1, end - performance.now()));
    if (chunk) answer += decoder.decode(chunk);
  }
  return answer;
}

/** Key names of one input chunk. An unknown sequence gives no key. */
export function keysOf(bytes: Uint8Array): string[] {
  const text = decoder.decode(bytes), keys: string[] = [];
  const names: Record<string, string> = { A: "up", B: "down", C: "right", D: "left", H: "home", F: "end", Z: "backtab", "5~": "pageup", "6~": "pagedown", "1~": "home", "4~": "end" };
  for (let i = 0; i < text.length;) {
    if (text[i] !== "\x1b") { keys.push(text[i]); i++; continue; }
    const match = /^\x1b(?:\[([0-9;?]*[ -/]*[@-~])|O([@-~])|.)?/s.exec(text.slice(i))!;
    const name = names[match[1] ?? match[2] ?? ""];
    if (name) keys.push(name);
    i += match[0].length;
  }
  return keys;
}

/** Visible characters above a row: a position in the text that a new width keeps. */
export function charsAbove(grid: Grid, row: number): number {
  let n = 0;
  for (let r = 0; r < row && r < grid.rows.length; r++) for (const cell of grid.rows[r]) if (cell.c !== " " && cell.w) n++;
  return n;
}
export function rowAtChars(grid: Grid, chars: number): number {
  let n = 0;
  for (let r = 0; r < grid.rows.length; r++) {
    if (n >= chars) return r;
    for (const cell of grid.rows[r]) if (cell.c !== " " && cell.w) n++;
  }
  return Math.max(0, grid.rows.length - 1);
}

async function viewer(run: Engine, first: Rendered, firstURL: string, options: Options, forced?: Level) {
  let writing = "", dead = false;
  const write = (s: string) => { writing += s; };
  const flush = () => {
    let bytes = encoder.encode(writing);
    writing = "";
    try { while (bytes.length && !dead) bytes = bytes.subarray(Deno.stdout.writeSync(bytes)); } catch { dead = true; }
  };
  let restored = false;
  const restore = () => {
    if (restored) return;
    restored = true;
    write("\x1b[?2026l\x1b[0m\x1b[?7h\x1b[?25h\x1b[?1049l");
    flush();
    try { Deno.stdin.setRaw(false); } catch { /* stdin already closed */ }
  };
  const fail = (error: unknown) => { restore(); console.error(`textnaut: ${reason(error)}`); Deno.exit(1); };
  globalThis.addEventListener("unhandledrejection", (event) => { event.preventDefault(); fail(event.reason); });
  globalThis.addEventListener("error", (event) => { event.preventDefault(); fail(event.error); });
  for (const signal of ["SIGINT", "SIGTERM", "SIGHUP", "SIGQUIT"] as const) Deno.addSignalListener(signal, () => { restore(); Deno.exit(130); });

  Deno.stdin.setRaw(true);
  const input = new Input();
  try {
    write("\x1b[?1049h\x1b[?25l\x1b[?7l\x1b[2J");
    flush();
    const caps = capabilities((name) => Deno.env.get(name), await queryTerminal(input, (s) => { write(s); flush(); }), forced);
    const blocks = caps.utf8 && caps.level > 0;
    const size = () => { try { const s = Deno.consoleSize(); return { columns: Math.max(1, s.columns), rows: Math.max(1, s.rows) }; } catch { return screen; } };
    let screen = { columns: first.grid.cols, rows: options.rows + 2 };
    screen = size();

    let current = first, top = 0, focus = 0, typed = "", message = "", loading = false, clear = false;
    const history = [firstURL];
    let index = 0, previous: string[] = [];
    let token = 0, abort: AbortController | undefined;
    const bars = () => screen.rows >= 3;
    const bodyRows = () => bars() ? screen.rows - 2 : screen.rows;
    const lastTop = () => Math.max(0, current.grid.rows.length - bodyRows());
    const layoutOptions = () => ({ ...options, cols: screen.columns, rows: bodyRows() });

    const draw = () => {
      const lines: string[] = [];
      const style = { level: caps.level, osc8: caps.osc8, focus, targets: current.grid.targets, width: screen.columns };
      if (bars()) {
        const name = blocks ? " \u2593\u2592\u2591 TEXTNAUT \u2591\u2592\u2593 " : " == TEXTNAUT == ";
        const title = sanitizeText(current.doc.title || current.doc.url);
        lines.push(barRow([{ text: name, bold: true }, { text: title }], ` ${loading ? "loading " : ""}${run.name} engine `, screen.columns, caps.level, 280));
      }
      for (let y = 0; y < bodyRows(); y++) {
        const row = current.grid.rows[top + y];
        lines.push(row ? styledRow(row, { ...style, row: top + y }) : fillerRow(screen.columns, caps.level, blocks, y));
      }
      if (bars()) {
        const total = current.grid.rows.length;
        const shown = total ? Math.min(top + bodyRows(), total) / total : 1;
        const meterWidth = 12, filled = Math.round(shown * meterWidth);
        const meter = blocks ? "\u2588".repeat(filled) + "\u2591".repeat(meterWidth - filled) : "#".repeat(filled) + "-".repeat(meterWidth - filled);
        const hints = message || (typed ? `go to link ${typed} then Enter` : "[n] Enter follow | Tab next | b back | q quit ");
        lines.push(barRow([{ text: ` ${meter} ${Math.round(shown * 100)}% `, bold: true }], hints, screen.columns, caps.level, 160));
      }
      let changed = "";
      lines.forEach((line, y) => { if (clear || line !== previous[y]) changed += `\x1b[${y + 1};1H${line}`; });
      previous = lines;
      if (!changed && !clear) return;
      write((caps.sync ? "\x1b[?2026h" : "") + (clear ? "\x1b[2J" : "") + changed + (caps.sync ? "\x1b[?2026l" : ""));
      clear = false;
      flush();
    };
    const relayout = async () => {
      const chars = charsAbove(current.grid, top);
      try {
        const { grid } = await layoutDoc(current.doc, layoutOptions(), current.charWidth);
        current = { ...current, grid };
        top = Math.min(lastTop(), rowAtChars(grid, chars));
      } catch (error) { message = `layout refused: ${reason(error)}`; }
      clear = true;
    };
    let resizePending = false, resizeDue = 0, firstResize = 0;
    const goTo = (url: string, record: boolean) => {
      abort?.abort();
      const controller = new AbortController();
      abort = controller;
      const mine = ++token;
      loading = true;
      message = "";
      renderPage(run.engine, url, layoutOptions(), undefined, controller.signal).then((next) => {
        if (mine !== token) return;
        current = next; top = 0; focus = 0; clear = true;
        if (record) { history.length = index + 1; history.push(next.doc.url); index = history.length - 1; }
        if (next.grid.cols !== Math.max(10, screen.columns)) resizeDue = performance.now();
      }).catch((error) => { if (mine === token && !controller.signal.aborted) message = `refused: ${reason(error)}`; })
        .finally(() => { if (mine === token) loading = false; input.poke(); });
    };
    const follow = (n: number) => {
      const href = current.grid.targets[n - 1];
      if (!href) { message = `no link ${n}`; return; }
      try { goTo(navigationURL(href, current.doc.baseURL, current.doc.url), true); }
      catch (error) { message = `refused: ${reason(error)}`; }
    };
    const moveFocus = (delta: number) => {
      const count = current.grid.targets.length;
      if (!count) return;
      focus = ((focus - 1 + delta + count) % count) + 1;
      const row = current.grid.linkRows[focus - 1] ?? 0;
      if (row < top || row >= top + bodyRows()) top = Math.min(lastTop(), Math.max(0, row - 2));
    };
    Deno.addSignalListener("SIGWINCH", () => { resizePending = true; input.poke(); });
    if (first.grid.cols !== Math.max(10, screen.columns)) await relayout();
    clear = true;
    draw();

    while (true) { // Ends on the key q, Ctrl-C or the end of input.
      const now0 = performance.now();
      const chunk = await input.next(resizeDue ? Math.max(0, resizeDue - now0) : undefined);
      if (resizePending) {
        resizePending = false;
        const next = size();
        if (next.columns !== screen.columns || next.rows !== screen.rows) {
          screen = next;
          clear = true;
          const now = performance.now();
          firstResize ||= now;
          // After the last signal of a burst, and at the longest 150 ms after its first signal.
          resizeDue = Math.min(now + 30, firstResize + 150);
          top = Math.min(lastTop(), top);
        }
      }
      if (resizeDue && performance.now() >= resizeDue) {
        resizeDue = 0;
        firstResize = 0;
        if (current.grid.cols !== Math.max(10, screen.columns)) await relayout();
        top = Math.min(lastTop(), top);
      }
      if (chunk) for (const key of keysOf(chunk)) {
        if (key === "q" || key === "\x03") return;
        if (/^[0-9]$/.test(key)) { typed += key; continue; }
        message = "";
        if (key === "\r" || key === "\n" || key === "right") {
          const n = typed ? Number(typed) : focus;
          typed = "";
          if (n) follow(n);
        } else if (key === "\x7f") typed = typed.slice(0, -1);
        else if (key === "up" || key === "k") top = Math.max(0, top - 1);
        else if (key === "down" || key === "j") top = Math.min(lastTop(), top + 1);
        else if (key === " " || key === "pagedown") top = Math.min(lastTop(), top + bodyRows() - 1);
        else if (key === "pageup") top = Math.max(0, top - bodyRows() + 1);
        else if (key === "home") top = 0;
        else if (key === "end") top = lastTop();
        else if (key === "\t") moveFocus(1);
        else if (key === "backtab") moveFocus(-1);
        else if (key === "left" || key === "b") {
          if (index > 0) { index--; goTo(history[index], false); } else message = "no earlier page";
        } else typed = "";
      }
      draw();
      if (input.closed) return;
    }
  } finally { restore(); }
}

const USAGE = "usage: textnaut.ts [--width COLS] [--dump] [--wasm | --engine FILE] [--font FILE] [--colour none|16|256|24bit] [--strict] [--no-scripts] [--timing] [--verbose] URL_OR_FILE";

export async function main(args: string[]): Promise<number> {
  const saver = args.indexOf("--screensaver");
  if (saver >= 0) {
    const { screensaver } = await import("./screensaver.ts");
    const name = args[saver + 1], frames = args.indexOf("--frames");
    return screensaver(name && !name.startsWith("-") ? name : undefined, frames >= 0 ? Number(args[frames + 1]) : undefined);
  }
  const started = performance.now();
  let parsed: ReturnType<typeof parseArgs>;
  try { parsed = parseArgs(args); } catch (error) { console.error(`${reason(error)}\n${USAGE}`); return 2; }
  if (!parsed.input) { console.error(USAGE); return 2; }
  const tty = Deno.stdout.isTerminal() && Deno.stdin.isTerminal() && (Deno.env.get("TERM") ?? "dumb") !== "dumb";
  const dump = parsed.dump || !tty;
  const size = !dump || (Deno.stdout.isTerminal() && !parsed.width) ? Deno.consoleSize() : { columns: 80, rows: 24 };
  const options: Options = { cols: parsed.width || size.columns, rows: dump ? size.rows : Math.max(1, size.rows - 2), scripts: parsed.scripts, liberal: !parsed.strict, verbose: parsed.verbose };
  let url = "";
  try {
    url = toURL(parsed.input);
    const run = await startEngine(parsed.wasm, parsed.engine);
    if (parsed.font) await loadFontFile(run.engine, parsed.font, "font");
    const scripts = enableScripts(run.engine, options);
    const ready = performance.now();
    const rendered = await renderPage(run.engine, url, options);
    if (parsed.timing) {
      const { load, layout, cells } = rendered.ms;
      console.error(`timing: engine ${run.name}; start ${Math.round(ready - started)} ms; load ${Math.round(load)} ms; layout ${Math.round(layout)} ms; cells ${Math.round(cells)} ms; rows ${rendered.grid.rows.length}; links ${rendered.grid.targets.length}; scripts ${scripts ? "bubblepop" : "off"}`);
    } else if (dump) console.error(`textnaut: engine ${run.name}`);
    if (dump) { await Deno.stdout.write(encoder.encode(dumpText(rendered.grid))); return 0; }
    await viewer(run, rendered, rendered.doc.url, options, parsed.colour);
    return 0;
  } catch (error) {
    console.error(`textnaut: page refused: ${sanitizeText(url || parsed.input)}: ${reason(error)}`);
    return 1;
  }
}

if (import.meta.main) Deno.exit(await main(Deno.args));
