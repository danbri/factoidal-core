// Screensaver core: a pixel surface (two pixels per cell, upper and lower half), an optional glyph
// layer, and a presenter that turns a surface into terminal bytes: changed rows only, at any
// colour level (24-bit, 256, 16, none), with or without UTF-8. No page and no engine.
import { type Level, nearest16, nearest256 } from "./grid.ts";

export type Rng = () => number;
/** A small seeded generator, so that tests and replays get the same frames. */
export function mulberry32(seed: number): Rng {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/** Colour scratch: `hsv` fills and returns it. Valid until the next call. */
const C: [number, number, number] = [0, 0, 0];
export function hsv(h: number, s: number, v: number): [number, number, number] {
  h -= Math.floor(h);
  const f = (n: number) => { const k = (n + h * 6) % 6; return 255 * (v - v * s * Math.max(0, Math.min(k, 4 - k, 1))); };
  C[0] = f(5); C[1] = f(3); C[2] = f(1);
  return C;
}

/** Pixels (w by h, h = 2 * rows) and glyphs (cols by rows). Savers draw a whole frame each time. */
export class Surface {
  cols = 0; rows = 0; w = 0; h = 0;
  px = new Uint8ClampedArray(0);
  glyph = new Int32Array(0);
  gfg = new Int32Array(0);
  constructor(public level: Level, public utf8: boolean) {}
  resize(cols: number, rows: number) {
    cols = Math.max(1, cols | 0); rows = Math.max(1, rows | 0);
    if (cols === this.cols && rows === this.rows) return false;
    this.cols = cols; this.rows = rows; this.w = cols; this.h = rows * 2;
    this.px = new Uint8ClampedArray(this.w * this.h * 3);
    this.glyph = new Int32Array(cols * rows);
    this.gfg = new Int32Array(cols * rows);
    return true;
  }
  clear() { this.px.fill(0); this.glyph.fill(0); }
  /** Overwrites a pixel; out of range is ignored. Float values are rounded and clamped. */
  set(x: number, y: number, r: number, g: number, b: number) {
    x |= 0; y |= 0;
    if (x < 0 || y < 0 || x >= this.w || y >= this.h) return;
    const i = (y * this.w + x) * 3;
    this.px[i] = r; this.px[i + 1] = g; this.px[i + 2] = b;
  }
  /** Adds to a pixel, saturating at 255. */
  add(x: number, y: number, r: number, g: number, b: number) {
    x |= 0; y |= 0;
    if (x < 0 || y < 0 || x >= this.w || y >= this.h) return;
    const i = (y * this.w + x) * 3;
    this.px[i] += r; this.px[i + 1] += g; this.px[i + 2] += b;
  }
  /** One character in a cell. Without UTF-8, a character above ASCII is shown as `*`. */
  put(col: number, row: number, ch: string, r: number, g: number, b: number) {
    col |= 0; row |= 0;
    if (col < 0 || row < 0 || col >= this.cols || row >= this.rows) return;
    let code = ch.codePointAt(0) ?? 32;
    if (!this.utf8 && code > 126) code = 42;
    const i = row * this.cols + col;
    this.glyph[i] = code;
    this.gfg[i] = (Math.max(0, Math.min(255, r | 0)) << 16) | (Math.max(0, Math.min(255, g | 0)) << 8) | Math.max(0, Math.min(255, b | 0));
  }
  /** Dims the two pixels of a cell row, for text on top. */
  dim(row: number, keep: number) {
    if (row < 0 || row >= this.rows) return;
    for (let y = row * 2; y < row * 2 + 2; y++) for (let i = y * this.w * 3, e = i + this.w * 3; i < e; i++) this.px[i] *= keep;
  }
}

const RAMP = " .:-=+*#%@";
const lut256 = new Int16Array(32768).fill(-1), lut16 = new Int8Array(32768).fill(-1);
const q256 = (r: number, g: number, b: number) => {
  const k = ((r >> 3) << 10) | ((g >> 3) << 5) | (b >> 3);
  let v = lut256[k];
  if (v < 0) { v = nearest256([(r & 0xf8) | 4, (g & 0xf8) | 4, (b & 0xf8) | 4]); lut256[k] = v; }
  return v;
};
const q16 = (r: number, g: number, b: number) => {
  const k = ((r >> 3) << 10) | ((g >> 3) << 5) | (b >> 3);
  let v = lut16[k];
  if (v < 0) { v = nearest16([(r & 0xf8) | 4, (g & 0xf8) | 4, (b & 0xf8) | 4]); lut16[k] = v; }
  return v;
};

/** Turns surfaces into bytes. A row is written only when its cells changed. */
export class Presenter {
  private ch = new Int32Array(0); private fg = new Int32Array(0); private bg = new Int32Array(0);
  private pch = new Int32Array(0); private pfg = new Int32Array(0); private pbg = new Int32Array(0);
  private valid = false;
  rowsWritten = 0;
  /** The next frame is written whole, after a clear. */
  invalidate() { this.valid = false; }
  private quant(r: number, g: number, b: number, level: Level): number {
    return level === 3 ? (r << 16) | (g << 8) | b : level === 2 ? q256(r, g, b) : level === 1 ? q16(r, g, b) : 0;
  }
  private seq(code: number, level: Level, back: boolean): string {
    if (level === 3) return `${back ? 48 : 38};2;${code >> 16};${(code >> 8) & 255};${code & 255}`;
    if (level === 2) return `${back ? 48 : 38};5;${code}`;
    return String((code < 8 ? 30 + code : 82 + code) + (back ? 10 : 0));
  }
  frame(s: Surface): string {
    const { cols, rows, w, level, px, glyph, gfg } = s;
    const n = cols * rows;
    if (this.ch.length !== n) {
      this.ch = new Int32Array(n); this.fg = new Int32Array(n); this.bg = new Int32Array(n);
      this.pch = new Int32Array(n); this.pfg = new Int32Array(n); this.pbg = new Int32Array(n);
      this.valid = false;
    }
    const half = s.utf8 && level > 0;
    for (let r = 0; r < rows; r++) {
      let u = (2 * r * w) * 3, l = ((2 * r + 1) * w) * 3;
      for (let c = 0; c < cols; c++, u += 3, l += 3) {
        const i = r * cols + c;
        const g = glyph[i];
        const ur = px[u], ug = px[u + 1], ub = px[u + 2], lr = px[l], lg = px[l + 1], lb = px[l + 2];
        if (level === 0) {
          if (g) { this.ch[i] = g; } else {
            const lum = (0.3 * (ur + lr) + 0.59 * (ug + lg) + 0.11 * (ub + lb)) / 2;
            this.ch[i] = RAMP.charCodeAt(Math.min(9, (lum * 10 / 256) | 0));
          }
          this.fg[i] = 0; this.bg[i] = 0;
        } else if (g) {
          const f = gfg[i];
          this.ch[i] = g;
          this.fg[i] = this.quant(f >> 16, (f >> 8) & 255, f & 255, level);
          this.bg[i] = this.quant((ur + lr) >> 1, (ug + lg) >> 1, (ub + lb) >> 1, level);
        } else if (half) {
          const a = this.quant(ur, ug, ub, level), b = this.quant(lr, lg, lb, level);
          if (a === b) { this.ch[i] = 32; this.fg[i] = 0; this.bg[i] = b; }
          else { this.ch[i] = 0x2580; this.fg[i] = a; this.bg[i] = b; }
        } else {
          this.ch[i] = 32; this.fg[i] = 0;
          this.bg[i] = this.quant((ur + lr) >> 1, (ug + lg) >> 1, (ub + lb) >> 1, level);
        }
      }
    }
    const out: string[] = [];
    if (!this.valid) out.push("\x1b[0m\x1b[2J");
    this.rowsWritten = 0;
    for (let r = 0; r < rows; r++) {
      const a = r * cols, b = a + cols;
      let same = this.valid;
      for (let i = a; same && i < b; i++) if (this.ch[i] !== this.pch[i] || this.fg[i] !== this.pfg[i] || this.bg[i] !== this.pbg[i]) same = false;
      if (same) continue;
      this.rowsWritten++;
      const line: string[] = [`\x1b[${r + 1};1H`];
      let lf = -1, lb = -1;
      for (let i = a; i < b; i++) {
        const ch = this.ch[i];
        if (level > 0) {
          const needF = ch !== 32 && this.fg[i] !== lf, needB = this.bg[i] !== lb;
          if (needF || needB) {
            line.push(`\x1b[${needF ? this.seq(this.fg[i], level, false) : ""}${needF && needB ? ";" : ""}${needB ? this.seq(this.bg[i], level, true) : ""}m`);
            if (needF) lf = this.fg[i];
            if (needB) lb = this.bg[i];
          }
        }
        line.push(String.fromCodePoint(ch));
      }
      out.push(line.join(""));
    }
    this.valid = true;
    [this.pch, this.ch] = [this.ch, this.pch];
    [this.pfg, this.fg] = [this.fg, this.pfg];
    [this.pbg, this.bg] = [this.bg, this.pbg];
    return out.join("");
  }
}

export type Instance = (s: Surface, t: number, dt: number) => void;
export type Saver = { name: string; help: string; egg?: boolean; make: (rng: Rng) => Instance };

/** A saver, a surface and a presenter: one frame of bytes for a size and a time. */
export class Renderer {
  surface: Surface;
  presenter = new Presenter();
  private instance: Instance;
  private born = -1;
  constructor(public saver: Saver, opts: { seed?: number; level: Level; utf8: boolean }) {
    this.surface = new Surface(opts.level, opts.utf8);
    this.instance = saver.make(mulberry32(opts.seed ?? 1));
  }
  /** `t` is seconds since the program started. The caption shows for 4 seconds after the first frame. */
  frame(t: number, dt: number, cols: number, rows: number, caption = ""): string {
    if (this.surface.resize(cols, rows)) this.presenter.invalidate();
    const s = this.surface;
    if (this.born < 0) this.born = t;
    s.clear();
    this.instance(s, t, Math.max(0, Math.min(0.1, dt)));
    const age = t - this.born;
    if (caption && age < 4 && s.rows >= 3) {
      const row = s.rows - 1, fade = age < 3 ? 1 : 4 - age;
      s.dim(row, 0.25 * (1 - fade) + 0.2 * fade);
      const text = [...caption].slice(0, s.cols - 2);
      const v = 170 + 85 * fade;
      for (let i = 0; i < text.length; i++) s.put(1 + i, row, text[i], v, v, v * 0.9);
    }
    return this.presenter.frame(s);
  }
}

/** Next, back, quit: the keys inside a screensaver and the history that `b` walks back through. */
export class Navigator {
  history: string[] = [];
  constructor(public current: string, public order: string[]) {}
  /** "switch" when the saver changed, "quit" to end it (back to what started it), "exit" for Ctrl-C, "none" when nothing happened. */
  key(key: string): "switch" | "quit" | "exit" | "none" {
    if (key === "\t" || key === " " || key === "n") {
      this.history.push(this.current);
      const i = this.order.indexOf(this.current);
      this.current = this.order[(i + 1) % this.order.length];
      return "switch";
    }
    if (key === "b" || key === "backtab") {
      const previous = this.history.pop();
      if (previous === undefined) return "none";
      this.current = previous;
      return "switch";
    }
    if (key === "\x03") return "exit";
    return "quit"; // q, and any other key
  }
}
