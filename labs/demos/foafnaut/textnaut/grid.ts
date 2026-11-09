// Pure mapping from the engine's positioned text to a grid of terminal cells, and from cells
// to terminal bytes. No I/O and no engine import, so the tests need no native library.
// The layout decisions stay in the engine: this file maps positions to cells.

/** One advance of the engine's built-in bitmap face at 16 CSS px: one cell (96/7 px). */
export const CELL_WIDTH = 96 / 7;
/** One line of 16 CSS px text at the engine's default line height: one row. */
export const CELL_HEIGHT = 19.2;
/** At most this many rows between two lines of text: two blank rows. */
export const MAX_ROW_STEP = 3;

export type RGB = [number, number, number];
/** A glyph row is [glyph id, x, y, advance, cluster start, cluster end]. */
export type GlyphRun = { text: string; size: number; glyphs: number[][]; source?: number };
/** [source node, href, x, y, width, height]. */
export type LinkRow = [number, string, number, number, number, number];
/**
 * `band` is the heading panel (1 or 2); `deco` marks a cell that is not page text (a border, a
 * padding cell, a repeated row); `rule` is a horizontal line; `bullet` is a list marker.
 */
export type Cell = { c: string; w: number; fg?: RGB; bg?: RGB; link?: number; mark?: boolean; head?: boolean; band?: 1 | 2; deco?: boolean; rule?: boolean; bullet?: boolean };
export type Rect = { x0: number; y0: number; x1: number; y1: number; rgb: RGB };
export type Paint = { glyphs: Rect[]; fills: Rect[] };
export type GridInput = {
  runs: GlyphRun[];
  links: LinkRow[];
  cols: number;
  resolve?: (href: string) => string;
  paint?: Paint;
  /** The engine's [source node, x, y, width, height] rows: used only to find list markers. */
  boxes?: number[][];
  cellWidth?: number;
  cellHeight?: number;
  /** Move the text left by the leftmost text position, so that column 0 is used. */
  trimLeft?: boolean;
};
export type Grid = {
  cols: number;
  rows: Cell[][];
  /** Target of link n is `targets[n - 1]`. */
  targets: string[];
  /** The first row of link n is `linkRows[n - 1]`. */
  linkRows: number[];
  /** Heading blocks, in row order: `start` to `end` inclusive. */
  headings: { level: 1 | 2 | 3; start: number; end: number }[];
  /** Blank rows that the engine paints a horizontal rule across. */
  rules: number[];
  /** Set by `decorateGrid`: how each row goes to the terminal. Absent means one normal row. */
  kinds?: RowKind[];
};
/** A row of `Grid.kinds`: two rows of a DEC double-height line, or two rows of one OSC 66 line. */
export type RowKind = "dec-top" | "dec-bottom" | "kitty-first" | "kitty-second" | undefined;

/** Bitmap size of the font size that has the most characters. */
export function bodySize(runs: GlyphRun[]): number {
  const count = new Map<number, number>();
  for (const run of runs) count.set(run.size, (count.get(run.size) ?? 0) + run.text.length);
  let best = 16, most = 0;
  for (const [size, n] of count) if (n > most && size > 0) { best = size; most = n; }
  return best;
}
/** Heading level from the ratio of a font size to the body size: the engine gives no element names. */
export function headingLevel(size: number, body: number): 0 | 1 | 2 | 3 {
  const ratio = size / body;
  return ratio >= 1.75 ? 1 : ratio >= 1.3 ? 2 : ratio >= 1.1 ? 3 : 0;
}
const MARKER = /^(\*|[0-9]+\.|[a-zA-Z]+\.)$/;

const REPLACEMENT = "\ufffd";

/**
 * The rule for page content: no text from a page reaches the terminal with a control
 * character in it. C0, DEL and C1 (with ESC, CSI, OSC, DCS and ST) become U+FFFD; tab and line
 * ends become a space; bidirectional formatting controls are removed, because they reorder
 * the text around them on a terminal that applies them.
 */
export function sanitizeText(text: string): string {
  return text.toWellFormed()
    .replace(/[\t\n\r\u2028\u2029]/g, " ")
    .replace(/[\u0000-\u001f\u007f-\u009f]/g, REPLACEMENT)
    .replace(/[\u061c\u200e\u200f\u202a-\u202e\u2066-\u2069]/g, "");
}

/** A URL for a terminal control string: every byte outside printable ASCII is percent-encoded. */
export function sanitizeURL(url: string): string {
  const bytes = new TextEncoder().encode(url.toWellFormed());
  let out = "";
  for (const b of bytes) {
    out += b > 0x20 && b < 0x7f ? String.fromCharCode(b) : "%" + b.toString(16).toUpperCase().padStart(2, "0");
  }
  return out;
}

const segmenter = new Intl.Segmenter(undefined, { granularity: "grapheme" });
export const graphemes = (text: string): string[] => Array.from(segmenter.segment(text), (s) => s.segment);

const WIDE =
  /^[\u1100-\u115f\u2e80-\u303e\u3041-\u33ff\u3400-\u4dbf\u4e00-\u9fff\ua000-\ua4cf\ua960-\ua97f\uac00-\ud7a3\uf900-\ufaff\ufe30-\ufe6f\uff00-\uff60\uffe0-\uffe6\u{20000}-\u{3fffd}]/u;
const ZERO = /^[\p{Mn}\p{Me}\p{Cf}]+$/u;

/** Terminal cells of one grapheme cluster. Approximate: terminals differ for emoji and ambiguous-width text. */
export function cellWidth(cluster: string): number {
  if (cluster === "" || ZERO.test(cluster)) return 0;
  if (cluster.includes("\ufe0f") || /^\p{Emoji_Presentation}/u.test(cluster) || WIDE.test(cluster)) return 2;
  return 1;
}
export const textWidth = (text: string): number => graphemes(text).reduce((n, g) => n + cellWidth(g), 0);

const RECT_TAG = 1, PATH_TAG = 6, POLYGON_TAG = 5;

/**
 * Colours from the draw list of an artifact with ABI `lean-svg-v1`, read only for colour
 * (rows as in `Primitive.fixedRows` of SVG.lean). Returns undefined when the list does not
 * have the expected form: the page is then shown with no colour.
 */
export function readPaint(artifact: { abi?: string; primitiveCount?: number; data?: ArrayLike<number> }): Paint | undefined {
  const data = artifact.data, count = artifact.primitiveCount;
  if (artifact.abi !== "lean-svg-v1" || !data || !count) return undefined;
  const rowCount = data.length / 4, glyphs: Rect[] = [], fills: Rect[] = [];
  let base = 2;
  for (let n = 0; n < count; n++) {
    if (base + 5 > rowCount) return undefined;
    const at = base * 4, tag = data[at + 4], shapes = data[at + 5], mode = data[at + 7], dashes = data[at + 18];
    const a = data[at + 11], rgb = [data[at + 8], data[at + 9], data[at + 10]].map((v) => Math.round(v * 255)) as RGB;
    const [p, q, r, s] = [data[at], data[at + 1], data[at + 2], data[at + 3]];
    if (a > 0.1 && (tag === RECT_TAG || tag === PATH_TAG || tag === POLYGON_TAG)) {
      const box = tag === RECT_TAG ? { x0: p, y0: q, x1: p + r, y1: q + s, rgb } : { x0: p, y0: q, x1: r, y1: s, rgb };
      if (tag === PATH_TAG) glyphs.push(box);
      if (a > 0.5) fills.push(box);
    }
    const shapeRows = tag === PATH_TAG ? shapes : (shapes + 1) >> 1;
    base += 5 + shapeRows + 5 * dashes + (mode % 4 >= 2 ? 2 : 0) + 3 * (mode >> 2);
  }
  return base === rowCount ? { glyphs, fills } : undefined;
}

type Item = { x: number; endX: number; y: number; size: number; text: string; link?: number; marker?: string; fg?: RGB; bullet?: boolean };

function buckets<T extends { y0: number; y1: number }>(boxes: T[], step: number) {
  const map = new Map<number, T[]>();
  for (const box of boxes) {
    for (let k = Math.floor(box.y0 / step); k <= Math.floor(box.y1 / step); k++) {
      const list = map.get(k);
      if (list) list.push(box); else map.set(k, [box]);
    }
  }
  return (y: number) => map.get(Math.floor(y / step)) ?? [];
}

/** Map positioned text to cells. Lines are the clusters of glyph tops; a word keeps its characters together. */
export function layoutGrid(input: GridInput): Grid {
  const cols = Math.max(10, input.cols), cw = input.cellWidth ?? CELL_WIDTH, ch = input.cellHeight ?? CELL_HEIGHT;
  // Numbers follow the engine's document order of link nodes.
  const numberOf = new Map<number, number>(), targets: string[] = [];
  const rects: { y0: number; y1: number; x0: number; x1: number; n: number }[] = [];
  for (const [node, href, x, y, w, h] of input.links) {
    if (!numberOf.has(node)) {
      numberOf.set(node, numberOf.size + 1);
      let target = href;
      try { target = input.resolve ? input.resolve(href) : href; } catch { /* shown as written */ }
      targets.push(sanitizeText(target));
    }
    rects.push({ x0: x, y0: y, x1: x + w, y1: y + h, n: numberOf.get(node)! });
  }
  const linkAt = buckets(rects, 64);
  const glyphAt = input.paint ? buckets(input.paint.glyphs, 32) : undefined;
  const items: Item[] = [];
  const seen = new Set<number>();
  const body = bodySize(input.runs);
  // A run whose source node also has a box much wider than the run is a list marker of that element.
  const widest = new Map<number, number>();
  for (const box of input.boxes ?? []) widest.set(box[0], Math.max(widest.get(box[0]) ?? 0, box[3]));
  for (const run of input.runs) {
    const first = run.glyphs[0], last = run.glyphs[run.glyphs.length - 1];
    const text = sanitizeText(run.text);
    if (!first || !last || text === "") continue;
    const [x, y] = [first[1], first[2]], advance = first[3], size = run.size || 16;
    const cx = x + advance / 2, cy = y + size * 0.4;
    const link = linkAt(cy).find((r) => cx >= r.x0 && cx <= r.x1 && cy >= r.y0 && cy <= r.y1)?.n;
    if (link) seen.add(link);
    let fg: RGB | undefined;
    if (glyphAt) {
      // The last glyph-sized shape that overlaps the first glyph is the glyph itself.
      const limit = 4 * size * size;
      fg = glyphAt(cy).findLast((b) =>
        b.x0 < x + advance && b.x1 > x && b.y0 < y + size && b.y1 > y && (b.x1 - b.x0) * (b.y1 - b.y0) <= limit
      )?.rgb;
    }
    const endX = last[1] + last[3];
    const bullet = MARKER.test(text) && run.source !== undefined && (widest.get(run.source) ?? 0) >= 2 * (endX - x);
    items.push({ x, endX, y, size, text, link, fg, bullet });
  }
  // A link with no text (an image, for example) still gets its number at its place.
  for (const r of rects) {
    if (seen.has(r.n)) continue;
    seen.add(r.n);
    items.push({ x: r.x0, endX: r.x0, y: r.y0, size: r.y1 - r.y0 || 16, text: "", link: r.n });
  }
  items.sort((a, b) => a.y - b.y || a.x - b.x);
  const origin = input.trimLeft && items.length ? Math.min(...items.map((i) => i.x)) : 0;
  for (const item of items) { item.x -= origin; item.endX -= origin; }

  // Lines: glyph tops within 0.4 of the font size are one line.
  const lines: Item[][] = [];
  for (const item of items) {
    const line = lines[lines.length - 1];
    if (line && item.y - line[0].y < 0.4 * Math.max(line[0].size, item.size)) line.push(item);
    else lines.push([item]);
  }
  for (const line of lines) {
    line.sort((a, b) => a.x - b.x);
    for (const item of line.slice(1)) item.bullet = false;
  }
  // The number follows the last word of its link in reading order.
  const lastOf = new Map<number, Item>();
  for (const line of lines) for (const item of line) if (item.link) lastOf.set(item.link, item);
  for (const [n, item] of lastOf) item.marker = `[${n}]`;

  const rows: Cell[][] = [], rowY: number[] = [], linkRows: number[] = [];
  const row = (r: number) => (rows[r] ??= []);
  const headings: Grid["headings"] = [];
  let r = -1, prevY = 0, lastHeadingY = 0;
  const put = (c: string, w: number, col: number, item: Item, mark: boolean) => {
    const cells = row(r), base = { fg: item.fg, link: item.link, mark, head: item.size >= 1.1 * body, bullet: item.bullet };
    cells[col] = { c, w, ...base };
    if (w === 2 && col + 1 < cols) cells[col + 1] = { c: "", w: 0, ...base };
    if (item.link && linkRows[item.link - 1] === undefined) linkRows[item.link - 1] = r;
  };
  for (const line of lines) {
    const y = line[0].y;
    const step = r < 0 ? 1 : Math.min(MAX_ROW_STEP, Math.max(1, Math.round((y - prevY) / ch)));
    for (let k = 1; k < step; k++) rowY[r + k] = prevY + ch * k;
    r += step;
    rowY[r] = y;
    prevY = y;
    const lineStart = r;
    const firstCol = Math.min(Math.round(line[0].x / cw), cols - 1);
    const indent = Math.min(firstCol, cols >> 1);
    let cursor = 0, prevEnd = line[0].x;
    for (const item of line) {
      const marker = item.marker ?? "";
      const words = graphemes(item.text), width = textWidth(item.text) + marker.length;
      let col = Math.min(Math.round(item.x / cw), cols - 1);
      const gap = item.x - prevEnd;
      // A word space is one cell at any font size; a wider gap (table cell, preformatted text) follows x.
      if (item !== line[0] && gap > 1.5 && gap <= item.size) col = cursor + 1;
      else if (col < cursor) col = cursor + (gap > 1.5 ? 1 : 0);
      if (col + width > cols && col > indent) { r++; rowY[r] = y; col = indent; }
      const place = (clusters: string[], mark: boolean) => {
        for (const g of clusters) {
          const w = cellWidth(g);
          if (w === 0) {
            // A mark with no base cell of its own joins the cell before it.
            const cells = row(r);
            for (let p = col - 1; p >= 0; p--) if (cells[p]?.w) { cells[p] = { ...cells[p], c: cells[p].c + g }; break; }
            continue;
          }
          if (col + w > cols) { r++; rowY[r] = y; col = indent; }
          put(g, w, col, item, mark);
          col += w;
        }
      };
      place(words, false);
      place(graphemes(marker), true);
      cursor = col;
      prevEnd = item.endX;
    }
    // A heading line has only text of one heading size or more. The lines of one wrapped heading join.
    const levels = line.filter((i) => i.text !== "").map((i) => headingLevel(i.size, body));
    const level = levels.length && !levels.includes(0) ? Math.max(...levels) as 1 | 2 | 3 : 0;
    if (level) {
      const open = headings[headings.length - 1];
      if (open && open.level === level && y - lastHeadingY < 1.6 * line[0].size) open.end = r;
      else headings.push({ level, start: lineStart, end: r });
      lastHeadingY = y;
    }
  }
  rows.length = r + 1;
  for (let k = 0; k < rows.length; k++) {
    const cells = (rows[k] ??= []);
    for (let col = 0; col < cols; col++) cells[col] ??= { c: " ", w: 1 };
    cells.length = cols;
  }
  if (input.paint) paintBackgrounds(rows, rowY, input.paint.fills, cols, cw, origin);
  return { cols, rows, targets, linkRows, headings, rules: input.paint ? findRules(rows, rowY, input.paint.fills, cols * cw, ch) : [] };
}

/** A painted line at least half the text width and at most 3.5 px high, placed on a blank row at its height. */
function findRules(rows: Cell[][], rowY: number[], fills: Rect[], textWidthPx: number, ch: number): number[] {
  const blank = (r: number) => r >= 0 && r < rows.length && rows[r].every((c) => c.c === " ");
  const found = new Set<number>();
  for (const fill of fills) {
    if (fill.y1 - fill.y0 > 3.5 || fill.x1 - fill.x0 < 0.5 * textWidthPx) continue;
    const y = (fill.y0 + fill.y1) / 2;
    let low = 0, high = rows.length;
    while (low < high) { const mid = (low + high) >> 1; if (rowY[mid] + ch / 2 < y) low = mid + 1; else high = mid; }
    const row = [low, low - 1].find((r) => blank(r) && Math.abs(rowY[r] + ch / 2 - y) <= 1.5 * ch);
    if (row !== undefined) found.add(row);
  }
  return [...found].sort((a, b) => a - b);
}

// ---------------------------------------------------------------- heading panels

/** "dec": ESC # 3 and ESC # 4. "kitty": OSC 66 with s=2. "none": heading text at the normal size. */
export type BigText = "none" | "dec" | "kitty";
export type Decor = { level: Level; utf8: boolean; big: BigText };
type Atom = { cells: Cell[]; w: number };
const isSpace = (a: Atom) => a.cells.length === 1 && a.cells[0].c === " " && !a.cells[0].link && !a.cells[0].mark;

function atomsOf(rows: Cell[][]): Atom[] {
  const out: Atom[] = [];
  for (const row of rows) {
    const atoms: Atom[] = [];
    for (const cell of row) {
      if (cell.w === 0 && cell.c === "") { if (atoms.length) atoms[atoms.length - 1].cells.push(cell); }
      else atoms.push({ cells: [cell], w: cell.w });
    }
    while (atoms.length && isSpace(atoms[atoms.length - 1])) atoms.pop();
    while (atoms.length && isSpace(atoms[0])) atoms.shift();
    if (atoms.length && out.length) out.push({ cells: [{ c: " ", w: 1 }], w: 1 });
    out.push(...atoms);
  }
  return out;
}

/** Word wrap with no character lost: a word wider than the line breaks between its cells. */
function wrapAtoms(atoms: Atom[], width: number): Atom[][] {
  const words: Atom[][] = [[]];
  for (const a of atoms) if (isSpace(a)) words.push([]); else words[words.length - 1].push(a);
  const lines: Atom[][] = [];
  let line: Atom[] = [], used = 0;
  const widthOf = (word: Atom[]) => word.reduce((n, a) => n + a.w, 0);
  const flush = () => { if (line.length) lines.push(line); line = []; used = 0; };
  for (const word of words) {
    if (!word.length) continue;
    const w = widthOf(word);
    if (line.length && used + 1 + w > width) flush();
    if (w > width) {
      for (const a of word) {
        if (used + a.w > width) flush();
        line.push(a);
        used += a.w;
      }
      continue;
    }
    if (line.length) { line.push({ cells: [{ c: " ", w: 1 }], w: 1 }); used++; }
    line.push(...word);
    used += w;
  }
  flush();
  return lines.length ? lines : [[]];
}

const pad = (n: number, band: 1 | 2): Cell[] => Array.from({ length: Math.max(0, n) }, () => ({ c: " ", w: 1, band, deco: true }));
const edge = (c: string, band: 1 | 2): Cell => ({ c, w: 1, band, deco: true });

/**
 * The rows that the viewer shows: a panel for each H1, a band for each H2, a line for each rule.
 * The result has more rows than `grid`; link numbers and targets stay. `--dump` does not call this.
 */
export function decorateGrid(grid: Grid, decor: Decor): Grid {
  const { cols } = grid, rows: Cell[][] = [], kinds: RowKind[] = [];
  const big: BigText = decor.level === 0 || cols < 40 ? "none" : decor.big;
  const rules = new Set(grid.rules), blocks = new Map(grid.headings.filter((h) => h.level < 3).map((h) => [h.start, h]));
  const push = (row: Cell[], kind?: RowKind) => { rows.push(row); kinds.push(kind); };
  const emitH1 = (block: Cell[][]) => {
    const width = big === "none" ? cols : cols >> 1, outer = big === "none" ? cols : width * 2;
    const [tl, tr, bl, br, h, v] = decor.utf8 ? ["\u250f", "\u2513", "\u2517", "\u251b", "\u2501", "\u2503"]
      : decor.level ? [" ", " ", " ", " ", " ", " "] : ["=", "=", "=", "=", "=", " "];
    const border = (left: string, right: string) => [edge(left, 1), ...Array.from({ length: outer - 2 }, () => edge(h, 1)), edge(right, 1), ...pad(cols - outer, 1)];
    push(border(tl, tr));
    for (const line of wrapAtoms(atomsOf(block), Math.max(6, width - 4))) {
      const used = line.reduce((n, a) => n + a.w, 0), left = (width - 2 - used) >> 1;
      const row: Cell[] = [edge(v, 1), ...pad(left, 1)];
      for (const atom of line) for (const cell of atom.cells) row.push({ ...cell, band: 1, head: true });
      row.push(...pad(width - 2 - used - left, 1), edge(v, 1));
      if (big === "none") push(row);
      else {
        push(row, big === "dec" ? "dec-top" : "kitty-first");
        push(row.map((cell) => ({ ...cell, deco: true })), big === "dec" ? "dec-bottom" : "kitty-second");
      }
    }
    push(border(bl, br));
  };
  const emitH2 = (block: Cell[][]) => {
    const lines = wrapAtoms(atomsOf(block), Math.max(6, cols - 4));
    const widest = Math.max(...lines.map((l) => l.reduce((n, a) => n + a.w, 0)));
    const barWidth = Math.min(cols, widest + 4), start = (cols - barWidth) >> 1;
    for (const line of lines) {
      const used = line.reduce((n, a) => n + a.w, 0), left = (barWidth - used) >> 1;
      const row: Cell[] = Array.from({ length: start }, () => ({ c: " ", w: 1 }));
      row.push(...pad(left, 2));
      for (const atom of line) for (const cell of atom.cells) row.push({ ...cell, band: 2, head: true });
      row.push(...pad(barWidth - used - left, 2));
      while (row.reduce((n, c) => n + c.w, 0) < cols) row.push({ c: " ", w: 1 });
      push(row);
    }
  };
  for (let r = 0; r < grid.rows.length; r++) {
    const block = blocks.get(r);
    if (block) {
      const source = grid.rows.slice(block.start, block.end + 1);
      if (block.level === 1) emitH1(source); else emitH2(source);
      r = block.end;
    } else if (rules.has(r)) {
      push(Array.from({ length: cols }, () => ({ c: decor.utf8 ? "\u2500" : "-", w: 1, rule: true, deco: true })));
    } else push(grid.rows[r]);
  }
  const linkRows: number[] = [];
  rows.forEach((row, r) => { for (const cell of row) if (cell.link && linkRows[cell.link - 1] === undefined) linkRows[cell.link - 1] = r; });
  return { ...grid, rows, kinds, linkRows };
}

/** In paint order, each fill larger than one cell gives the background of the cells it covers. */
function paintBackgrounds(rows: Cell[][], rowY: number[], fills: Rect[], cols: number, cw: number, origin: number) {
  for (const fill of fills) {
    if (fill.x1 - fill.x0 < cw || fill.y1 - fill.y0 < 10) continue;
    let low = 0, high = rows.length;
    while (low < high) { const mid = (low + high) >> 1; if (rowY[mid] + 8 < fill.y0) low = mid + 1; else high = mid; }
    const start = Math.max(0, Math.round((fill.x0 - origin) / cw)), end = Math.min(cols, Math.round((fill.x1 - origin) / cw));
    for (let r = low; r < rows.length && rowY[r] + 8 < fill.y1; r++) {
      for (let col = start; col < end; col++) rows[r][col] = { ...rows[r][col], bg: fill.rgb };
    }
  }
}

export const plainRow = (cells: Cell[]): string => cells.map((c) => c.c).join("").trimEnd();

/** Plain text and a numbered list of link targets. */
export function dumpText(grid: Grid): string {
  const body = grid.rows.map(plainRow).join("\n").trimEnd();
  if (!grid.targets.length) return body + "\n";
  return `${body}\n\nLinks:\n${grid.targets.map((t, i) => `[${i + 1}] ${t}`).join("\n")}\n`;
}

// ---------------------------------------------------------------- colour

/** 0 plain text, 1 sixteen colours, 2 the 256-colour palette, 3 24-bit colour. */
export type Level = 0 | 1 | 2 | 3;
const ANSI16: RGB[] = [[0,0,0],[205,0,0],[0,205,0],[205,205,0],[0,0,238],[205,0,205],[0,205,205],[229,229,229],
  [127,127,127],[255,0,0],[0,255,0],[255,255,0],[92,92,255],[255,0,255],[0,255,255],[255,255,255]];
const distance = (a: RGB, b: RGB) => (a[0] - b[0]) ** 2 + (a[1] - b[1]) ** 2 + (a[2] - b[2]) ** 2;
export function nearest16(c: RGB): number {
  let best = 0;
  ANSI16.forEach((p, i) => { if (distance(c, p) < distance(c, ANSI16[best])) best = i; });
  return best;
}
export function nearest256(c: RGB): number {
  const level = (v: number) => v < 48 ? 0 : v < 115 ? 1 : Math.min(5, Math.floor((v - 35) / 40));
  const [r, g, b] = c.map(level), cube = 16 + 36 * r + 6 * g + b;
  const steps = [0, 95, 135, 175, 215, 255];
  const grey = Math.max(0, Math.min(23, Math.round((c[0] + c[1] + c[2]) / 3 - 8) / 10 | 0));
  const greyValue = 8 + 10 * grey, cubeRGB: RGB = [steps[r], steps[g], steps[b]];
  return distance(c, [greyValue, greyValue, greyValue]) < distance(c, cubeRGB) ? 232 + grey : cube;
}
/** The SGR parameters of a colour at a level; empty at level 0. */
export function sgrColour(c: RGB, level: Level, background: boolean): string {
  if (level === 3) return `${background ? 48 : 38};2;${c.join(";")}`;
  if (level === 2) return `${background ? 48 : 38};5;${nearest256(c)}`;
  if (level === 1) { const n = nearest16(c); return String((n < 8 ? 30 + n : 82 + n) + (background ? 10 : 0)); }
  return "";
}
export function hsl(h: number, s: number, l: number): RGB {
  const a = s * Math.min(l, 1 - l);
  const f = (n: number) => { const k = (n + h / 30) % 12; return Math.round(255 * (l - a * Math.max(-1, Math.min(k - 3, 9 - k, 1)))); };
  return [f(0), f(8), f(4)];
}
const lightness = (c: RGB) => 0.299 * c[0] + 0.587 * c[1] + 0.114 * c[2];
/** At 16 colours a colour pair can become one colour: then the text takes black or white. */
function readable(fg: RGB, bg: RGB | undefined, level: Level): RGB {
  if (level !== 1 || !bg || nearest16(fg) !== nearest16(bg)) return fg;
  return lightness(bg) > 128 ? [0, 0, 0] : [255, 255, 255];
}

export type StyleOptions = { level: Level; osc8: boolean; focus?: number; targets: string[]; width: number; row?: number; utf8?: boolean; scale?: boolean };

/** A heading panel's background at a column: a gradient at 24-bit and 256 colours, one colour at 16, none in plain mode. */
function bandColour(band: 1 | 2, col: number, width: number, level: Level): RGB | undefined {
  if (level === 0) return undefined;
  if (level === 1) return band === 1 ? [0, 0, 238] : [0, 205, 205];
  const t = col / Math.max(1, width - 1);
  return band === 1 ? hsl(Math.floor((262 + 50 * t) / 6) * 6, 0.8, 0.36) : hsl(Math.floor((185 + 35 * t) / 6) * 6, 0.75, 0.78);
}
const OSC8 = (url: string) => `\x1b]8;;${url}\x1b\\`;
const allowed = (u: string | undefined) => !!u && /^(https?|file):/i.test(u);

/** One row of exactly `width` columns as terminal bytes. Every string in it is sanitised text or a sanitised URL. */
export function styledRow(cells: Cell[], options: StyleOptions): string {
  const level = options.level, y = options.row ?? 0;
  let out = "", sgr = "", link: number | undefined, width = 0, lastBg: RGB | undefined;
  for (let col = 0; col < cells.length; col++) {
    const cell = cells[col];
    if (cell.w === 0 && cell.c === "") continue;
    if (width + cell.w > options.width) break;
    if (options.osc8 && cell.link !== link) {
      if (link && allowed(options.targets[link - 1])) out += OSC8("");
      if (cell.link && allowed(options.targets[cell.link - 1])) out += OSC8(sanitizeURL(options.targets[cell.link - 1]));
      link = cell.link;
    }
    const bg = level ? cell.bg : undefined, parts: string[] = ["0"];
    let fg = level ? cell.fg : undefined;
    const band = cell.band ? bandColour(cell.band, col, options.width, level) : undefined;
    let bgOut = cell.band ? band : bg;
    const light = bgOut ? lightness(bgOut) > 128 : false;
    if (cell.band && level === 0) parts.push("7");
    if (cell.link !== undefined) {
      const hue = (cell.link * 47) % 360;
      if (cell.link === options.focus) { parts.push("1"); if (level) { fg = [0, 0, 0]; bgOut = [255, 235, 0]; } else parts.push("7"); }
      else if (cell.mark) { parts.push("1"); if (level) { fg = lightness(hsl(hue, 1, 0.5)) > 128 ? [0, 0, 0] : [255, 255, 255]; bgOut = hsl(hue, 1, 0.5); } }
      else { parts.push("4"); if (level) fg = cell.band ? (light ? [0, 0, 0] : [255, 255, 255]) : hsl(hue, 1, light ? 0.32 : 0.72); }
    } else if (cell.band) {
      if (!cell.deco) { parts.push("1"); if (cell.band === 2 && level === 0) parts.push("4"); }
      if (level) fg = light ? [0, 0, 0] : [255, 255, 255];
    } else if (cell.rule) {
      if (level === 1) fg = [0, 205, 205];
      else if (level) fg = hsl((col * 3) % 360, 0.9, 0.6);
    } else if (cell.bullet) {
      parts.push("1");
      if (level === 1) fg = [255, 255, 0];
      else if (level) fg = hsl((y * 37) % 360, 1, light ? 0.35 : 0.68);
    } else if (cell.head) {
      parts.push("1");
      if (level === 1) fg = light ? [205, 0, 205] : [255, 0, 255];
      else if (level) fg = hsl((col * 7 + y * 11) % 360, 1, light ? 0.35 : 0.68);
    }
    if (fg) { const shown = readable(fg, bgOut, level); parts.push(sgrColour(shown, level, false)); }
    if (bgOut) parts.push(sgrColour(bgOut, level, true));
    const want = parts.filter(Boolean).join(";");
    if (want !== sgr) { out += `\x1b[${want}m`; sgr = want; }
    const shownText = cell.bullet && cell.c === "*" && options.utf8 && level ? "\u2022" : cell.c;
    out += options.scale ? `\x1b]66;s=2;${shownText}\x1b\\` : shownText;
    width += cell.w;
    lastBg = bgOut;
  }
  if (options.osc8 && link && allowed(options.targets[link - 1])) out += OSC8("");
  if (width < options.width) {
    const pad = level && lastBg ? `\x1b[0;${sgrColour(lastBg, level, true)}m` : "\x1b[0m";
    out += pad + " ".repeat(options.width - width);
  }
  return out + "\x1b[0m";
}

/**
 * One grid row as terminal bytes, where `y` is its row in the body area of `bodyRows` rows. An
 * OSC 66 line covers two terminal rows: half of one at an edge of the body is a normal row, and
 * the second row of a whole one gives an empty string, which means "write nothing".
 */
export function displayRow(grid: Grid, index: number, y: number, bodyRows: number, style: StyleOptions, big: BigText): string {
  const cells = grid.rows[index], kind = grid.kinds?.[index], half = Math.min(cells.length, style.width >> 1);
  if (kind === "dec-top") return "\x1b#3" + styledRow(cells, { ...style, width: half });
  if (kind === "dec-bottom") return "\x1b#4" + styledRow(cells, { ...style, width: half });
  if (kind === "kitty-first" && y < bodyRows - 1) return "\x1b[2K\x1b[B\x1b[2K\x1b[A" + styledRow(cells, { ...style, width: half, scale: true });
  if (kind === "kitty-second" && y > 0) return "";
  return (big === "dec" ? "\x1b#5" : "") + styledRow(cells, style);
}

export type BarText = { text: string; bold?: boolean };

/** A full-width bar: colour by column in hue when the level has enough colours, one solid colour at 16, reverse video in plain mode. */
export function barRow(left: BarText[], right: string, width: number, level: Level, hue: number): string {
  const cells: { c: string; w: number; bold: boolean }[] = [];
  const add = (text: string, bold: boolean, room: number) => {
    let used = 0;
    for (const g of graphemes(sanitizeText(text))) {
      const w = cellWidth(g);
      if (w === 0) { if (cells.length) cells[cells.length - 1].c += g; continue; }
      if (used + w > room) break;
      cells.push({ c: g, w, bold });
      used += w;
    }
    return used;
  };
  const rightWidth = Math.min(width, textWidth(sanitizeText(right)));
  let used = 0;
  for (const part of left) used += add(part.text, !!part.bold, Math.max(0, width - rightWidth - used));
  const gap = Math.max(0, width - rightWidth - used);
  for (let i = 0; i < gap; i++) cells.push({ c: " ", w: 1, bold: false });
  add(right, true, width - used - gap);
  if (level === 0) return `\x1b[0;7m${cells.map((c) => c.c).join("")}\x1b[0m`;
  let out = "", sgr = "", col = 0;
  for (const cell of cells) {
    const h = level === 1 ? hue : Math.floor((hue + 300 * col / Math.max(1, width)) / 6) * 6;
    const bg = hsl(h % 360, 1, 0.42), fg: RGB = lightness(bg) > 140 ? [0, 0, 0] : [255, 255, 255];
    const want = `${cell.bold ? "0;1" : "0"};${sgrColour(fg, level, false)};${sgrColour(bg, level, true)}`;
    if (want !== sgr) { out += `\x1b[${want}m`; sgr = want; }
    out += cell.c;
    col += cell.w;
  }
  return out + "\x1b[0m";
}

/** A row past the end of the page, so that the whole terminal area is drawn. */
export function fillerRow(width: number, level: Level, utf8: boolean, y: number): string {
  if (level === 0) return "~" + " ".repeat(Math.max(0, width - 1));
  const glyph = utf8 ? "\u2591" : ":";
  let out = "", sgr = "";
  for (let col = 0; col < width; col++) {
    const want = `0;${sgrColour(hsl((col * 5 + y * 13) % 360, 0.9, 0.3), level, false)}`;
    if (want !== sgr) { out += `\x1b[${want}m`; sgr = want; }
    out += glyph;
  }
  return out + "\x1b[0m";
}
