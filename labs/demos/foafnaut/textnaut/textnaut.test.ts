// Run in labs/demos/foafnaut with:
//   deno test --no-prompt --allow-read --allow-ffi --allow-env --allow-run --import-map=textnaut/import_map.json --no-check textnaut/textnaut.test.ts
// Local content only; no network. The engine tests are ignored when no engine library is found.
import { strict as assert } from "node:assert";
import { barRow, type BigText, cellWidth, textWidth, decorateGrid, displayRow, dumpText, fillerRow, type GlyphRun, type Grid, headingLevel, layoutGrid, type LinkRow, plainRow, sanitizeText, sanitizeURL, styledRow } from "./grid.ts";
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

// ---------------------------------------------------------------- heading panels
const sized = (text: string, size: number, x: number, y: number, source = 1): GlyphRun => {
  const advance = size * 6 / 7;
  return { text, size, source, glyphs: [...text].map((_, i) => [65, x + i * advance, y, advance, i, i + 1]) };
};
const BODY = "body text body text body text body text body text";
const sample = (headingText: string, size: number, links: LinkRow[] = [], cols = 40) =>
  layoutGrid({ cols, runs: [sized(headingText, size, 0, 0), sized(BODY, 16, 0, 60), sized("last", 16, 0, 80)], links });
const text = (grid: Grid) => grid.rows.map((row) => row.filter((c) => !c.deco).map((c) => c.c).join("").trim()).filter(Boolean);
const decor = (level: 0 | 1 | 2 | 3, big: BigText = "none", utf8 = true) => ({ level, utf8, big });

Deno.test("heading level comes from the font size against the body size", () => {
  assert.deepEqual([32, 24, 19, 16, 13].map((s) => headingLevel(s, 16)), [1, 2, 3, 0, 0]);
  assert.deepEqual(sample("Title", 32).headings, [{ level: 1, start: 0, end: 0 }]);
  // A larger word in a line of body text is not a heading.
  const mixed = layoutGrid({ cols: 40, runs: [sized("Large", 32, 0, 0), sized("small body words here", 16, 100, 0), sized(BODY, 16, 0, 40)], links: [] });
  assert.deepEqual(mixed.headings, []);
});
Deno.test("an H1 panel adds a row above and below; the body text moves down in order", () => {
  const grid = sample("Title", 32), shown = decorateGrid(grid, decor(3));
  assert.equal(shown.rows.length, grid.rows.length + 2);
  assert.equal(plainRow(shown.rows[0])[0], "\u250f");
  assert.equal(shown.rows[0].length, 40);
  assert(shown.rows[0].every((c) => c.band === 1));
  assert(shown.rows[2].every((c) => c.band === 1));
  const row = plainRow(shown.rows[1]);
  assert.equal(row.length, 40);
  assert.equal(row.indexOf("Title"), 17, "centred");
  assert.deepEqual(text(shown).slice(1), text(grid).slice(1));
});
Deno.test("an H2 band is shorter than the width, with no extra rows", () => {
  const grid = sample("Part", 24), shown = decorateGrid(grid, decor(3));
  assert.equal(shown.rows.length, grid.rows.length);
  const band = shown.rows[0].filter((c) => c.band === 2);
  assert.equal(band.length, 8);
  assert.equal(shown.rows[0].length, 40);
});
Deno.test("an H3 keeps its row and is bold text with no band", () => {
  const shown = decorateGrid(sample("Sub", 19), decor(3));
  assert(shown.rows[0].every((c) => !c.band));
  assert(styledRow(shown.rows[0], { level: 3, osc8: false, targets: [], width: 40 }).includes("\x1b[0;1;38;2;"));
});
Deno.test("links in and below a heading keep their numbers and targets, and the rows are found again", () => {
  const links: LinkRow[] = [[7, "http://a.test/h", 0, 0, 150, 38], [8, "http://a.test/b", 0, 60, 60, 19]];
  const grid = sample("Linked", 32, links), shown = decorateGrid(grid, decor(3));
  assert.deepEqual(shown.targets, grid.targets);
  assert.equal(shown.linkRows[0], 1);
  assert.equal(shown.rows[shown.linkRows[1]].find((c) => c.link === 2)?.c, "b");
  assert.match(plainRow(shown.rows[1]), /Linked\[1\]/);
  assert(shown.linkRows[1] > grid.linkRows[1]);
});
Deno.test("a long H1 wraps in the panel and loses no text", () => {
  const words = "A very long heading that does not fit on one row of a narrow terminal at all";
  const runs = words.split(" ").reduce((acc: { list: GlyphRun[]; x: number; y: number }, w) => {
    const width = w.length * 27.4;
    if (acc.x + width > 500) { acc.x = 0; acc.y += 38.4; }
    acc.list.push(sized(w, 32, acc.x, acc.y));
    acc.x += width + 27.4;
    return acc;
  }, { list: [], x: 0, y: 0 }).list;
  const grid = layoutGrid({ cols: 30, runs: [...runs, sized(BODY.repeat(3), 16, 0, 400)], links: [] });
  assert.equal(grid.headings.length, 1);
  const shown = decorateGrid(grid, decor(3));
  const panel = shown.rows.filter((row) => row.some((c) => c.band === 1));
  assert(panel.length >= 5);
  assert.equal(text({ ...shown, rows: panel.slice(1, -1) }).join(" "), words);
  for (const row of panel) assert.equal(row.reduce((n, c) => n + c.w, 0), 30);
  const unbroken = "x".repeat(70);
  const wide = decorateGrid(layoutGrid({ cols: 30, runs: [sized(unbroken, 32, 0, 0), sized(BODY, 16, 0, 60), sized(BODY, 16, 0, 80)], links: [] }), decor(3));
  assert.equal(wide.rows.filter((r) => r.some((c) => c.band === 1)).flatMap((r) => r.filter((c) => !c.deco && c.c === "x")).length, 70);
});
for (const level of [0, 1, 2, 3] as const) {
  Deno.test(`heading rows keep the full width at colour level ${level}`, () => {
    for (const utf8 of [true, false]) {
      const shown = decorateGrid(sample("Heading", 32), decor(level, "none", utf8));
      for (let r = 0; r < shown.rows.length; r++) {
        const out = styledRow(shown.rows[r], { level, osc8: false, targets: [], width: 40, utf8 });
        assert.equal(visible(out).length, 40, `row ${r}: ${JSON.stringify(out)}`);
      }
    }
  });
}
Deno.test("plain mode: the dump has no escape and no panel; level 0 has no colour or size sequence", () => {
  const grid = sample("Title", 32);
  const dump = dumpText(grid);
  assert(!dump.includes("\x1b"), JSON.stringify(dump));
  assert(!/[\u2500-\u257f]/.test(dump), dump);
  assert.equal(plainRow(grid.rows[0]), "Title");
  const shown = decorateGrid(grid, decor(0, "dec"));
  assert.equal(shown.kinds?.includes("dec-top"), false, "no double-size lines in plain mode");
  for (let r = 0; r < shown.rows.length; r++) {
    const out = displayRow(shown, r, r, 24, { level: 0, osc8: false, targets: [], width: 40, utf8: true }, "none");
    assert(!/\x1b\[[0-9;]*(38|48)[;m]/.test(out) && !out.includes("\x1b#") && !out.includes("\x1b]66"), JSON.stringify(out));
  }
});
Deno.test("colour fallback: a heading at 16 colours and at 256 colours uses only that palette", () => {
  const shown = decorateGrid(sample("Title", 32), decor(1));
  assert(!/\x1b\[[^m]*(38|48);[25];/.test(styledRow(shown.rows[1], { level: 1, osc8: false, targets: [], width: 40 })));
  const at256 = decorateGrid(sample("Title", 32), decor(2));
  assert(/48;5;/.test(styledRow(at256.rows[1], { level: 2, osc8: false, targets: [], width: 40 })));
  assert(!/;2;/.test(styledRow(at256.rows[1], { level: 2, osc8: false, targets: [], width: 40 }).replace(/\x1b\[0;1m|48;5;\d+|38;5;\d+/g, "")));
});
Deno.test("DEC double size: two rows at half the width, single-width reset on other rows", () => {
  const shown = decorateGrid(sample("Title", 32), decor(3, "dec"));
  assert.deepEqual(shown.kinds?.slice(0, 4), [undefined, "dec-top", "dec-bottom", undefined]);
  assert.equal(shown.rows[1].length, 20);
  const style = { level: 3 as const, osc8: false, targets: [], width: 40, utf8: true };
  const top = displayRow(shown, 1, 1, 24, style, "dec"), bottom = displayRow(shown, 2, 2, 24, style, "dec");
  assert(top.startsWith("\x1b#3") && bottom.startsWith("\x1b#4"));
  assert.equal(visible(top.slice(3)).length, 20);
  assert(displayRow(shown, 4, 4, 24, style, "dec").startsWith("\x1b#5"));
  // The repeated half is not counted again as text.
  assert.equal(charsAbove(shown, 4), "Title".length);
});
Deno.test("OSC 66: the first row carries the text, the second row writes nothing, and the edges fall back", () => {
  const shown = decorateGrid(sample("A;b", 32), decor(3, "kitty"));
  const style = { level: 3 as const, osc8: false, targets: [], width: 40, utf8: true };
  const first = displayRow(shown, 1, 1, 24, style, "kitty");
  assert(first.includes("\x1b]66;s=2;A\x1b\\"), JSON.stringify(first));
  assert.equal(displayRow(shown, 2, 2, 24, style, "kitty"), "");
  assert(!displayRow(shown, 1, 23, 24, style, "kitty").includes("\x1b]66"), "last body row has no room for two rows");
  assert(visible(displayRow(shown, 2, 0, 24, style, "kitty")).length === 40, "half a line at the top is a normal row");
  const hostile = decorateGrid(layoutGrid({ cols: 40, runs: [sized("a\u001b\\\u0007b", 32, 0, 0), sized(BODY, 16, 0, 60)], links: [] }), decor(3, "kitty"));
  const bytes = displayRow(hostile, 1, 1, 24, style, "kitty").replace(/\x1b\]66;s=2;[^\x1b\x07]*\x1b\\/g, "").replace(/\x1b\[[0-9;?]*[A-Za-z]/g, "");
  assert(!/[\x07\x1b]/.test(bytes), JSON.stringify(bytes));
});
Deno.test("large text is detected from the terminal's answers, never assumed", () => {
  const env = (o: Record<string, string>) => (n: string) => o[n];
  const xterm = env({ TERM: "xterm-256color" });
  assert.equal(capabilities(xterm, "", undefined, 80).big, "none");
  assert.equal(capabilities(xterm, "\x1b[1;1R\x1b[1;80R", undefined, 80).big, "none");
  assert.equal(capabilities(xterm, "\x1b[1;1R\x1b[1;40R", undefined, 80).big, "dec");
  assert.equal(capabilities(xterm, "\x1b[1;3R\x1b[1;80R", undefined, 80).big, "kitty");
  assert.equal(capabilities(xterm, "\x1b[1;3R\x1b[1;80R", undefined, 80, "off").big, "none");
  assert.equal(capabilities(xterm, "", undefined, 80, "on").big, "dec");
  assert.equal(capabilities(env({ TERM: "screen", TMUX: "x" }), "\x1b[1;3R\x1b[1;40R", undefined, 80).big, "none");
  assert.equal(capabilities(env({ TERM: "xterm", NO_COLOR: "1" }), "\x1b[1;3R", undefined, 80, "on").big, "none");
});
Deno.test("a position in the text ignores panel borders and is kept across widths", () => {
  const wide = decorateGrid(sample("Title", 32, [], 60), decor(3)), narrow = decorateGrid(sample("Title", 32, [], 30), decor(3));
  assert.equal(charsAbove(wide, 3), "Title".length);
  assert.equal(charsAbove(narrow, 3), "Title".length);
  assert.equal(rowAtChars(narrow, charsAbove(wide, 2)), rowAtChars(narrow, "Title".length));
});
Deno.test("a painted line on a blank row is a rule, in the viewer only", () => {
  const paint = { glyphs: [], fills: [{ x0: 8, y0: 30, x1: 500, y1: 31, rgb: [128, 128, 128] as [number, number, number] }] };
  const grid = layoutGrid({ cols: 40, runs: [run("above", 0, 0), run("below", 0, 60)], links: [], paint });
  assert.equal(grid.rules.length, 1);
  assert.equal(grid.rows[grid.rules[0]].every((c) => c.c === " "), true, "dump text does not change");
  assert.equal(dumpText(grid), "above\n\n\nbelow\n");
  const shown = decorateGrid(grid, decor(3));
  assert.equal(plainRow(shown.rows[grid.rules[0]]), "\u2500".repeat(40));
  assert.equal(visible(styledRow(shown.rows[grid.rules[0]], { level: 3, osc8: false, targets: [], width: 40 })).length, 40);
  assert.equal(layoutGrid({ cols: 40, runs: [run("a", 0, 0)], links: [], paint: { glyphs: [], fills: [{ x0: 8, y0: 2, x1: 40, y1: 3, rgb: [0, 0, 0] }] } }).rules.length, 0);
});
Deno.test("a list marker becomes a coloured bullet in the viewer; the dump keeps the engine's text", () => {
  const boxes = [[5, 48, 0, 500, 19], [6, 80, 0, 40, 19]];
  const marker: GlyphRun = { text: "*", size: 16, source: 5, glyphs: [[42, 48, 2, 13.7, 0, 1]] };
  const word: GlyphRun = { text: "item", size: 16, source: 6, glyphs: [[65, 80, 2, 13.7, 0, 1], [65, 93.7, 2, 13.7, 1, 2]] };
  const grid = layoutGrid({ cols: 40, runs: [marker, word], links: [], boxes });
  assert(grid.rows[0].some((c) => c.bullet));
  assert.equal(plainRow(grid.rows[0]).trim(), "* item");
  const out = styledRow(grid.rows[0], { level: 3, osc8: false, targets: [], width: 40, utf8: true });
  assert(out.includes("\u2022"));
  assert(!styledRow(grid.rows[0], { level: 0, osc8: false, targets: [], width: 40, utf8: true }).includes("\u2022"));
  // The same text with no marker box stays page text.
  assert(!layoutGrid({ cols: 40, runs: [marker, word], links: [] }).rows[0].some((c) => c.bullet));
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

Deno.test({ name: "expected failure, issue 371: an h4 is not identified, and has the same size as the body", ignore: !started, fn: async () => {
  const grid = (await renderPage(started!.engine, local, options, "<!doctype html><h4>Four</h4><p>body words that are the body of this page")).grid;
  assert.equal(grid.headings.length, 0, `${GAP}: h4`);
} });
Deno.test({ name: "expected failure, issue 371: blockquote, code, pre and table have no style of their own", ignore: !started, fn: async () => {
  const page = "<!doctype html><blockquote>quoted</blockquote><p>a <code>c</code> b<pre>pre</pre><table border=1><tr><td>cell</table>";
  const grid = decorateGrid((await renderPage(started!.engine, local, options, page)).grid, { level: 3, utf8: true, big: "none" });
  assert(grid.rows.every((row) => row.every((c) => !c.bg && !c.deco && !c.rule)), `${GAP}: block styles`);
} });
Deno.test({ name: "engine: h1 to h3 are identified from the glyph runs, and the dump has no panel", ignore: !started, fn: async () => {
  const page = '<!doctype html><h1>One</h1><p>words of the body text of the page, more of them than in the headings</p><h2>Two</h2><p>body</p><h3>Three</h3><hr><ul><li>item</ul><p><a href="/x">link</a>';
  const grid = (await renderPage(started!.engine, local, options, page)).grid;
  assert.deepEqual(grid.headings.map((h) => h.level), [1, 2, 3]);
  assert.equal(grid.rules.length, 1);
  assert(grid.rows.some((row) => row.some((c) => c.bullet)));
  const dump = dumpText(grid);
  assert(!/[\u2500-\u257f\u2022\u001b]/.test(dump), dump);
  const shown = decorateGrid(grid, { level: 3, utf8: true, big: "none" });
  assert.equal(shown.rows.length, grid.rows.length + 2);
  assert.equal(shown.rows[shown.linkRows[0]].find((c) => c.link === 1)?.c, "l");
} });

const SGR = /\x1b\[[0-9;]*m/g;
/** The rows of one presenter output: [row number, visible text]. */
function frameRows(out: string): Map<number, string> {
  const rows = new Map<number, string>();
  for (const m of out.matchAll(/\x1b\[(\d+);1H((?:(?!\x1b\[\d+;1H)[^])*)/g)) rows.set(Number(m[1]), m[2].replace(SGR, "").replace(/\x1b\[\?2026[hl]/g, ""));
  return rows;
}

Deno.test("every screensaver draws whole frames of the right size at every colour level, with and without UTF-8", async () => {
  const { savers, eggs, Renderer } = await import("./screensaver.ts");
  for (const saver of [...savers, ...eggs]) {
    for (const [cols, rows] of [[80, 24], [1, 1], [2, 3], [37, 11], [200, 60]]) {
      for (const level of [0, 1, 2, 3] as const) for (const utf8 of [true, false]) {
        const r = new Renderer(saver, { seed: 5, level, utf8 });
        const where = `${saver.name} ${cols}x${rows} level ${level} utf8 ${utf8}`;
        const first = r.frame(1.5, 0.033, cols, rows, "a caption");
        const lines = frameRows(first);
        assert.equal(lines.size, rows, `${where}: rows`);
        for (const [y, text] of lines) {
          assert(y >= 1 && y <= rows, `${where}: row ${y}`);
          assert.equal(textWidth(text), cols, `${where}: row ${y} is ${textWidth(text)} wide`);
          if (!utf8) assert(!/[^\x20-\x7e]/.test(text), `${where}: non-ASCII without UTF-8`);
        }
        const second = r.frame(1.533, 0.033, cols, rows);
        for (const y of frameRows(second).keys()) assert(y >= 1 && y <= rows, `${where}: second frame row ${y}`);
        const colours = (first + second).match(/\x1b\[[0-9;]*m/g) ?? [];
        const kinds = new Set(colours.map((c) => /38;2|48;2/.test(c) ? "24" : /38;5|48;5/.test(c) ? "256" : /\x1b\[(?:[0-9;]*;)?(?:3[0-7]|4[0-7]|9[0-7]|10[0-7])(?:;[0-9;]*)?m/.test(c) ? "16" : "other"));
        if (level === 0) assert(!kinds.has("24") && !kinds.has("256") && !kinds.has("16"), `${where}: colour at level 0`);
        if (level === 1) assert(!kinds.has("24") && !kinds.has("256"), `${where}: 24-bit or 256 colour at level 1`);
        if (level === 2) assert(!kinds.has("24"), `${where}: 24-bit colour at level 2`);
        if (level === 3 && cols >= 80) assert(kinds.has("24"), `${where}: no colour at level 3`);
      }
    }
  }
});

Deno.test("a screensaver with the same seed draws the same frames", async () => {
  const { savers, eggs, Renderer } = await import("./screensaver.ts");
  for (const saver of [...savers, ...eggs]) {
    const a = new Renderer(saver, { seed: 42, level: 3, utf8: true }), b = new Renderer(saver, { seed: 42, level: 3, utf8: true });
    for (let i = 0; i < 4; i++) assert.equal(a.frame(i / 30, 1 / 30, 60, 20), b.frame(i / 30, 1 / 30, 60, 20), `${saver.name} frame ${i}`);
  }
});

Deno.test("a screensaver follows a resize at once, with a full redraw of the new size", async () => {
  const { savers, eggs, Renderer } = await import("./screensaver.ts");
  for (const saver of [...savers, ...eggs]) {
    const r = new Renderer(saver, { seed: 1, level: 2, utf8: true });
    for (const [cols, rows] of [[80, 24], [100, 30], [20, 5], [200, 60]]) {
      const out = r.frame(1, 0.033, cols, rows);
      assert(out.includes("\x1b[2J"), `${saver.name}: no clear on resize to ${cols}x${rows}`);
      const lines = frameRows(out);
      assert.equal(lines.size, rows, `${saver.name} ${cols}x${rows}`);
      for (const text of lines.values()) assert.equal(textWidth(text), cols);
    }
  }
});

Deno.test("the presenter writes only the rows that changed", async () => {
  const { Presenter, Surface } = await import("./screensaver.ts");
  const s = new Surface(3, true), p = new Presenter();
  s.resize(10, 4);
  for (let i = 0; i < s.px.length; i++) s.px[i] = (i * 7) & 255;
  assert.equal(frameRows(p.frame(s)).size, 4);
  assert.equal(p.frame(s), "", "an identical frame writes nothing");
  s.set(3, 5, 255, 0, 0); // pixel row 5 is in cell row 2
  const out = p.frame(s);
  assert.deepEqual([...frameRows(out).keys()], [3]);
});

Deno.test("screensaver keys: Tab, Space and n go on; b goes back through the history; q, Ctrl-C and others end it", async () => {
  const { Navigator } = await import("./screensaver.ts");
  const nav = new Navigator("plasma", ["plasma", "tunnel", "fire", "rain"]);
  assert.equal(nav.key("\t"), "switch"); assert.equal(nav.current, "tunnel");
  assert.equal(nav.key(" "), "switch"); assert.equal(nav.current, "fire");
  assert.equal(nav.key("n"), "switch"); assert.equal(nav.current, "rain");
  assert.equal(nav.key("n"), "switch"); assert.equal(nav.current, "plasma", "the list wraps");
  for (const want of ["rain", "fire", "tunnel", "plasma"]) { assert.equal(nav.key("b"), "switch"); assert.equal(nav.current, want); }
  assert.equal(nav.key("b"), "none", "nothing before the first");
  assert.equal(nav.current, "plasma");
  assert.equal(nav.key("q"), "quit");
  assert.equal(nav.key("\x03"), "exit");
  assert.equal(nav.key("z"), "quit");
  assert.equal(nav.key("up"), "quit");
});

Deno.test("hidden savers are out of the list and the random choice except in December", async () => {
  const { savers, eggs, pool, orderFor, findSaver } = await import("./screensaver.ts");
  assert.equal(savers.length, 15);
  assert(eggs.length >= 2 && eggs.every((e) => e.egg));
  assert(savers.every((s) => !s.egg && !/xmas/.test(s.name + s.help)));
  for (let month = 1; month <= 11; month++) assert(pool(month).every((s) => !s.egg), `month ${month}`);
  assert(eggs.every((e) => pool(12).includes(e)));
  assert(orderFor("plasma", 6).every((n) => !findSaver(n)!.egg));
  assert(orderFor("plasma", 12).includes("xmas-tree"));
  assert.deepEqual(orderFor("xmas-tree", 6), eggs.map((e) => e.name), "a hidden one outside December walks the hidden ones");
  assert.equal(findSaver("xmas")?.name, "xmas-tree");
  assert.equal(findSaver("nonesuch"), undefined);
});

/** A fake terminal input: one chunk per call, then the end of input. */
function fakeInput(chunks: string[]) {
  const queue = chunks.map((c) => new TextEncoder().encode(c));
  const input = { closed: false, async next(_timeout?: number) { await new Promise((r) => setTimeout(r, 1)); const c = queue.shift(); if (!c) { if (queue.length === 0 && chunks.length) input.closed = true; return null; } return c; } };
  return input;
}

Deno.test("runSavers: Tab, Space, b and q on a terminal input; a started saver names itself", async () => {
  const { runSavers } = await import("./screensaver.ts");
  let out = "";
  // Frames take 30 ms; each key arrives while the frame wait is on.
  const input = fakeInput(["\t", " ", "b", "n", "q"]);
  const end = await runSavers({ input, write: (s) => { out += s; }, size: () => ({ columns: 80, rows: 24 }), level: 3, utf8: true }, "plasma", { seed: 1, month: 6 });
  assert.equal(end, "quit");
  const names = [...out.replace(SGR, "").matchAll(/(plasma|tunnel|fire|rain): /g)].map((m) => m[1]);
  assert.deepEqual(names.filter((n, i) => n !== names[i - 1]), ["plasma", "tunnel", "fire", "tunnel", "fire"]);
});

Deno.test("runSavers: Ctrl-C is exit, any other key is quit, a pipe with frames just stops", async () => {
  const { runSavers } = await import("./screensaver.ts");
  const run = (keys: string[]) => runSavers({ input: fakeInput(keys), write: () => {}, size: () => ({ columns: 40, rows: 10 }), level: 0, utf8: false }, "stars", { seed: 1, month: 6 });
  assert.equal(await run(["\x03"]), "exit");
  assert.equal(await run(["x"]), "quit");
  assert.equal(await run(["\x1b[A"]), "quit");
  let n = 0;
  assert.equal(await runSavers({ write: () => { n++; }, size: () => ({ columns: 40, rows: 10 }), level: 3, utf8: true }, "fire", { frames: 3, fps: 1000 }), "quit");
  assert.equal(n, 3);
});

Deno.test("4D: a rotation keeps the distance from the centre, and unrotate undoes it", async () => {
  const { rotate4, unrotate4 } = await import("./screensaver.ts");
  let seed = 7;
  const rnd = () => { seed = (seed * 1103515245 + 12345) & 0x7fffffff; return seed / 0x7fffffff * 2 - 1; };
  for (let i = 0; i < 200; i++) {
    const p: [number, number, number, number] = [rnd(), rnd(), rnd(), rnd()], a = rnd() * 7, b = rnd() * 7, c = rnd() * 7;
    const q = rotate4(p, a, b, c);
    assert(Math.abs(Math.hypot(...q) - Math.hypot(...p)) < 1e-12, "distance from the centre");
    const back = unrotate4(q, a, b, c);
    for (let k = 0; k < 4; k++) assert(Math.abs(back[k] - p[k]) < 1e-12);
  }
  // XW turns x into w: a quarter turn takes (1,0,0,0) to (0,0,0,1).
  const turned = rotate4([1, 0, 0, 0], Math.PI / 2, 0);
  assert(Math.abs(turned[0]) < 1e-12 && Math.abs(turned[3] - 1) < 1e-12);
  // YW leaves x alone.
  assert.equal(rotate4([1, 0, 0, 0], 0, 1.3)[0], 1);
});

Deno.test("Menger sponges: 20 of 27 cubes per step in 3D, 48 of 81 hypercells per step in 4D", async () => {
  const { mengerGrid, mengerCells4 } = await import("./screensaver.ts");
  for (const level of [1, 2, 3]) assert.equal(mengerGrid(level).count, 20 ** level);
  for (const level of [1, 2]) assert.equal(mengerCells4(level).count, 48 ** level);
  // The 4D sponge keeps the corners and drops the centre; 3D drops the centre and the face centres.
  const one = mengerCells4(1);
  assert.equal(one.cells[0], 1);
  assert.equal(one.cells[1 + 3 * (1 + 3 * (1 + 3 * 1))], 0);
});

Deno.test("help: lists every saver, fills the screen, scrolls and keeps its selection in view", async () => {
  const { HelpView } = await import("./help.ts");
  const { savers } = await import("./screensaver.ts");
  for (const [cols, rows] of [[80, 24], [40, 8], [200, 60], [20, 3], [10, 1]]) for (const level of [0, 1, 2, 3] as const) {
    const help = new HelpView();
    const lines = help.render(cols, rows, level, level > 1, "A page");
    assert.equal(lines.length, rows);
    for (const line of lines) assert.equal(textWidth(line.replace(SGR, "")), cols, `${cols}x${rows} level ${level}`);
  }
  const help = new HelpView();
  const all = help.render(200, 100, 3, true, "").map((l) => l.replace(SGR, "")).join("\n");
  for (const s of savers) assert(all.includes(s.name), s.name);
  assert(/\[n\] then Enter/.test(all) && /follow link number n/.test(all));
  assert(!/xmas/i.test(all), "hidden savers are not listed");
  // Moving down through the list of a small window keeps the selection on screen.
  for (let i = 0; i < 14; i++) {
    help.key("down");
    const view = help.render(60, 10, 0, false, "").join("\n");
    assert(view.includes("\x1b[7m"), `selection ${help.selected} is visible`);
  }
});

Deno.test("help keys: arrows and Enter, a number and Enter, close, quit and the hidden one", async () => {
  const { HelpView } = await import("./help.ts");
  const { savers } = await import("./screensaver.ts");
  const help = new HelpView();
  assert.deepEqual(help.key("down"), { action: "none" });
  assert.deepEqual(help.key("down"), { action: "none" });
  assert.deepEqual(help.key("\r"), { action: "launch", saver: savers[2].name });
  assert.deepEqual(help.key("up"), { action: "none" });
  assert.equal(help.key("\r").saver, savers[1].name);
  help.key("7"); assert.equal(help.key("\r").saver, savers[6].name);
  help.key("1"); help.key("2"); assert.equal(help.key("\r").saver, savers[11].name);
  help.key("9"); help.key("9"); const none = help.key("\r");
  assert.equal(none.action, "none"); assert(/no screensaver 99/.test(none.message ?? ""));
  for (const k of ["q", "?", "h", "b", "left"]) assert.equal(help.key(k).action, "close", k);
  assert.equal(help.key("\x03").action, "exit");
  assert.equal(help.key("x").saver, "xmas-tree");
  assert.equal(help.typed, "");
});

Deno.test("help: a page title with escape sequences reaches the terminal only as text", async () => {
  const { HelpView } = await import("./help.ts");
  const title = "Evil \x1b[2J\x1b]0;owned\x07 \x9b31m title ‮";
  for (const level of [0, 3] as const) {
    const out = new HelpView().render(80, 24, level, true, title).join("\n").replace(SGR, "");
    assert(!/[\x00-\x08\x0b-\x1f\x7f-\x9f‮]/.test(out.replace(/\n/g, "")), JSON.stringify(out.slice(0, 200)));
    assert(/Evil/.test(out));
  }
});

Deno.test("the browser's hint line names the help key", async () => {
  const src = await Deno.readTextFile(new URL("./textnaut.ts", import.meta.url));
  assert(/"\? help \| \[n\] Enter follow/.test(src));
});

Deno.test("screensaver frame time stays usable: every saver under 60 ms a frame at 200x60 (generous bound)", async () => {
  const { savers, eggs, Renderer } = await import("./screensaver.ts");
  for (const saver of [...savers, ...eggs]) {
    const r = new Renderer(saver, { seed: 3, level: 3, utf8: true });
    r.frame(0, 0.033, 200, 60);
    const start = performance.now();
    for (let i = 1; i <= 10; i++) r.frame(i / 30, 1 / 30, 200, 60);
    const each = (performance.now() - start) / 10;
    assert(each < 60, `${saver.name}: ${each.toFixed(1)} ms a frame`);
  }
});

Deno.test("text with no colour of its own on a background gets a colour with contrast", async () => {
  const { styledRow } = await import("./grid.ts");
  const cell = { c: "x", w: 1, bg: [240, 244, 249] as [number, number, number] };
  const out = styledRow([cell as never], { level: 3, osc8: false, targets: [], width: 1 } as never);
  if (!/38;2;0;0;0/.test(out)) throw new Error("no dark text on a light background: " + JSON.stringify(out));
});

Deno.test("input: a URL as it is, a file wins, a bare host name becomes https with a note", async () => {
  const { resolveInput, START_PAGE } = await import("./textnaut.ts");
  assert(resolveInput("https://info.cern.ch/").url === "https://info.cern.ch/" && !resolveInput("https://info.cern.ch/").note);
  const bare = resolveInput("info.cern.ch", () => false);
  assert(bare.url === "https://info.cern.ch/" && /no file named info\.cern\.ch/.test(bare.note ?? ""));
  assert(resolveInput("example.org/a/b", () => false).url === "https://example.org/a/b");
  assert(resolveInput("info.cern.ch", () => true).url.startsWith("file:"));
  assert(resolveInput("notes", () => false).url.startsWith("file:"));
  assert(START_PAGE.startsWith("file:") && START_PAGE.endsWith("/start.html"));
});
