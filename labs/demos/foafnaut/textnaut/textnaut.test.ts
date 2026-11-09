// Run in labs/demos/foafnaut with:
//   deno test --no-prompt --allow-read --allow-ffi --allow-env --allow-run --import-map=textnaut/import_map.json --no-check textnaut/textnaut.test.ts
// Local content only; no network. The engine tests are ignored when no engine library is found.
import { strict as assert } from "node:assert";
import { barRow, cellWidth, dumpText, fillerRow, type GlyphRun, layoutGrid, type LinkRow, plainRow, sanitizeText, sanitizeURL, styledRow } from "./grid.ts";
import { capabilities, charsAbove, enableScripts, findNative, keysOf, renderPage, rowAtChars, startEngine } from "./textnaut.ts";

const run = (text: string, x: number, y: number, advance = 12): GlyphRun =>
  ({ text, size: 14, glyphs: [...text].map((_, i) => [65, x + i * advance, y, advance, i, i + 1]) });
const CTRL = /[\u0000-\u0008\u000b-\u001f\u007f-\u009f]/;

Deno.test("control characters: C0, DEL, C1 and ESC are replaced", () => {
  const text = sanitizeText("a\u001b]0;own\u0007b\u009b31m\u0090c\u007fd\u0000e");
  assert(!CTRL.test(text), JSON.stringify(text));
  assert.equal(sanitizeText("a\tb\nc"), "a b c");
});
Deno.test("control characters: bidirectional overrides are removed", () => {
  assert.equal(sanitizeText("ab\u202ecd\u2066ef"), "abcdef");
});
Deno.test("control characters: a URL for OSC 8 has only printable ASCII", () => {
  const url = sanitizeURL("https://a.test/\u001b]8;;x\u009c ok\u00e9");
  assert(/^[\x21-\x7e]+$/.test(url), url);
});
Deno.test("page text with escape sequences gives none in the dump or a styled row", () => {
  const grid = layoutGrid({ cols: 40, runs: [run("\u001b[31mred\u009b2J", 0, 0)], links: [] });
  for (const out of [dumpText(grid), styledRow(grid.rows[0], { level: 3, osc8: true, targets: [], width: 40 }).replace(/\u001b\[[0-9;]*m/g, "")]) {
    assert(!/[\u001b\u009b]/.test(out), JSON.stringify(out));
  }
});
Deno.test("OSC 8 target from a page can not close the sequence", () => {
  const links: LinkRow[] = [[1, "https://a.test/\u001b\\\u001b[2J", 0, 0, 100, 20]];
  const grid = layoutGrid({ cols: 40, runs: [run("go", 0, 2)], links });
  const row = styledRow(grid.rows[0], { level: 0, osc8: true, targets: grid.targets, width: 40 });
  assert(!row.includes("\u001b[2J"), JSON.stringify(row));
});
Deno.test("cell width: wide, combining, plain", () => {
  assert.equal(cellWidth("a"), 1);
  assert.equal(cellWidth("\u65e5"), 2);
  assert.equal(cellWidth("e\u0301"), 1);
  assert.equal(cellWidth("\u0301"), 0);
  assert.equal(cellWidth("\u{1f600}"), 2);
});
Deno.test("column mapping: x gives the column, top y gives the row", () => {
  const cw = 96 / 7;
  const grid = layoutGrid({ cols: 40, runs: [run("ab", 0, 0, cw), run("cd", cw * 10, 0, cw), run("ef", cw * 5, 19.2, cw)], links: [] });
  assert.equal(plainRow(grid.rows[0]), "ab        cd");
  assert.equal(plainRow(grid.rows[1]), "     ef");
});
Deno.test("a word space is one cell at any font size", () => {
  const big: GlyphRun = { text: "aa", size: 32, glyphs: [[1, 0, 0, 27, 0, 1], [1, 27, 0, 27, 1, 2]] };
  const next: GlyphRun = { text: "bb", size: 32, glyphs: [[1, 70, 0, 27, 0, 1], [1, 97, 0, 27, 1, 2]] };
  assert.equal(plainRow(layoutGrid({ cols: 40, runs: [big, next], links: [] }).rows[0]), "aa bb");
});
Deno.test("vertical gaps are limited to two blank rows", () => {
  const grid = layoutGrid({ cols: 40, runs: [run("a", 0, 0), run("b", 0, 500)], links: [] });
  assert.equal(grid.rows.length, 4);
});
Deno.test("trimLeft moves the text to column 0", () => {
  const grid = layoutGrid({ cols: 40, trimLeft: true, runs: [run("a", 137, 0)], links: [] });
  assert.equal(grid.rows[0][0].c, "a");
});
Deno.test("numbered links: one number per link node, after its last word, with a list", () => {
  const links: LinkRow[] = [[5, "/one", 0, 0, 24, 20], [5, "/one", 36, 0, 24, 20], [9, "http://x.test/two", 80, 0, 24, 20]];
  const grid = layoutGrid({ cols: 40, runs: [run("ab", 0, 2), run("cd", 36, 2), run("ef", 80, 2)], links, resolve: (h) => new URL(h, "http://b.test/").href });
  assert.equal(plainRow(grid.rows[0]), "ab cd[1]  ef[2]".replace("  ", " "));
  assert.deepEqual(grid.targets, ["http://b.test/one", "http://x.test/two"]);
  assert.match(dumpText(grid), /\[1\] http:\/\/b\.test\/one\n\[2\] http:\/\/x\.test\/two\n$/);
});
Deno.test("a link with no text keeps its number", () => {
  const grid = layoutGrid({ cols: 40, runs: [], links: [[3, "/i", 0, 0, 50, 20]] });
  assert.equal(plainRow(grid.rows[0]), "[1]");
});
Deno.test("wide text wraps at the width and fills two cells", () => {
  const grid = layoutGrid({ cols: 10, runs: [run("\u65e5".repeat(8), 0, 0)], links: [] });
  assert.equal(grid.rows.length, 2);
  for (const row of grid.rows) assert.equal(row.length, 10);
  assert.equal(plainRow(grid.rows[0]), "\u65e5".repeat(5));
});
const visible = (s: string) => s.replace(/\u001b\[[0-9;?]*[A-Za-z]/g, "").replace(/\u001b\]8;;[^\u001b]*\u001b\\/g, "");
for (const level of [0, 1, 2, 3] as const) {
  Deno.test(`a styled row, a bar and a filler row have the full width at colour level ${level}`, () => {
    const grid = layoutGrid({ cols: 30, runs: [run("hello", 0, 0)], links: [[1, "https://a.test/", 0, 0, 60, 20]] });
    const row = styledRow(grid.rows[0], { level, osc8: true, targets: grid.targets, width: 30 });
    assert.equal(visible(row).length, 30);
    assert.equal(visible(barRow([{ text: "TITLE", bold: true }], "right", 30, level, 280)).length, 30);
    assert.equal(visible(fillerRow(30, level, false, 0)).length, 30);
  });
}
Deno.test("colour level from the environment, and plain text with no information", () => {
  const env = (o: Record<string, string>) => (n: string) => o[n];
  assert.equal(capabilities(env({ TERM: "xterm-256color", COLORTERM: "truecolor" }), "").level, 3);
  assert.equal(capabilities(env({ TERM: "xterm-256color" }), "").level, 2);
  assert.equal(capabilities(env({ TERM: "xterm" }), "").level, 1);
  assert.equal(capabilities(env({ TERM: "dumb", COLORTERM: "truecolor" }), "").level, 0);
  assert.equal(capabilities(env({ TERM: "xterm", NO_COLOR: "1" }), "").level, 0);
});
Deno.test("capabilities: synchronized output and OSC 8 only when detected", () => {
  const env = (o: Record<string, string>) => (n: string) => o[n];
  assert.equal(capabilities(env({ TERM: "xterm" }), "").sync, false);
  assert.equal(capabilities(env({ TERM: "xterm" }), "\u001b[?2026;2$y").sync, true);
  assert.equal(capabilities(env({ TERM: "xterm" }), "").osc8, false);
  assert.equal(capabilities(env({ TERM: "xterm" }), "\u001bP>|kitty(0.3)\u001b\\").osc8, true);
  assert.equal(capabilities(env({ TERM: "screen", TMUX: "x" }), "\u001bP>|kitty(0.3)\u001b\\").osc8, false);
});
Deno.test("keys: arrows, page keys, tab, letters", () => {
  const keys = (s: string) => keysOf(new TextEncoder().encode(s));
  assert.deepEqual(keys("\u001b[A\u001b[B\u001b[5~\u001b[6~\u001b[Zq"), ["up", "down", "pageup", "pagedown", "backtab", "q"]);
  assert.deepEqual(keys("\u001b[?1;2c"), []);
});
Deno.test("a position in the text is kept across widths", () => {
  const words = Array.from({ length: 40 }, (_, i) => run("word", i % 8 * 60, Math.floor(i / 8) * 19.2));
  const wide = layoutGrid({ cols: 60, runs: words, links: [], cellWidth: 12 });
  const narrow = layoutGrid({ cols: 20, runs: words, links: [], cellWidth: 12 });
  const chars = charsAbove(wide, 2);
  const row = rowAtChars(narrow, chars);
  assert(row >= 2 && charsAbove(narrow, row) >= chars);
});

const library = findNative();
const options = { cols: 60, rows: 24, scripts: false, liberal: true, verbose: false };
const started = library ? await startEngine(false) : undefined;
const local = "file:///textnaut-test/page.html";
Deno.test({ name: "engine: page text with control characters gives none on output", ignore: !started, fn: async () => {
  enableScripts(started!.engine, options);
  const page = '<!doctype html><meta charset=utf-8><title>t</title><p>&#27;[31mred &#x9b;2J <a href="/x&#27;y">go</a>';
  const out = dumpText((await renderPage(started!.engine, local, options, page)).grid);
  assert(!CTRL.test(out), JSON.stringify(out));
  assert.match(out, /\[1\]/);
} });
Deno.test({ name: "engine: pages/showcase.html from disk has text and numbered links", ignore: !started, fn: async () => {
  const url = new URL("../pages/showcase.html", import.meta.url).href;
  const grid = (await renderPage(started!.engine, url, options)).grid;
  assert(grid.targets.length > 5);
  assert.match(dumpText(grid), /showcase/);
  assert(grid.rows.every((row) => row.length === 60));
} });
Deno.test({ name: "engine: a refused page gives a reason on stderr and exit code 1", ignore: !started, fn: async () => {
  const output = await new Deno.Command(Deno.execPath(), {
    args: ["run", "--no-prompt", "--allow-read", "--allow-ffi", "--allow-net", "--allow-env", `--import-map=${new URL("./import_map.json", import.meta.url).pathname}`, new URL("./textnaut.ts", import.meta.url).pathname, "--dump", "--width", "80", "/nonexistent/textnaut-page.html"],
    stdout: "piped", stderr: "piped",
  }).output();
  assert.equal(output.code, 1);
  assert.match(new TextDecoder().decode(output.stderr), /page refused: .*textnaut-page/);
} });

// Shortfalls that stay open under issue 371. When one of these fails, change it to assert the
// correct behaviour.
const GAP = "expected failure of https://github.com/danbri/factoidal-core/issues/371 no longer fails";
Deno.test({ name: "expected failure, issue 371: a form control gives no cells", ignore: !started, fn: async () => {
  const out = dumpText((await renderPage(started!.engine, local, options, "<!doctype html><p>x<input value=typed>")).grid);
  assert(!out.includes("typed"), `${GAP}: forms`);
} });
Deno.test({ name: "expected failure, issue 371: a loaded image gives no cells", ignore: !started, fn: async () => {
  const url = new URL("../pages/images.html", import.meta.url).href;
  const page = '<!doctype html><p><img src="images-badge.png" alt="">';
  const out = dumpText((await renderPage(started!.engine, url, options, page)).grid);
  assert.equal(out.trim(), "", `${GAP}: images`);
} });

Deno.test("screensavers draw a frame of colour cells at any size", async () => {
  const { effects } = await import("./screensaver.ts");
  for (const [name, make] of Object.entries(effects)) {
    const frame = make();
    for (const [cols, rows] of [[80, 24], [1, 1], [200, 60]]) {
      const out = frame(1.5, cols, rows, "24bit");
      if (!out.includes("\x1b[")) throw new Error(`${name} drew nothing at ${cols}x${rows}`);
      frame(1.6, cols, rows, "256");
    }
  }
});
