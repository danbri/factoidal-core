// The browser's help screen: keys, options and the screensavers, each startable from the list.
// A view with its own state (selection, scroll, a typed number) that never touches the page's
// position. Pure: `key` says what to do, `render` gives the rows. Nothing from a page is shown
// except its title, which goes through the same sanitiser as the header bar.
import { barRow, graphemes, type Level, sanitizeText, sgrColour, textWidth } from "./grid.ts";
import { savers } from "./savers.ts";

type Line = { text: string; kind: "plain" | "heading" | "item" | "dim"; saver?: number };

/** Words wrapped to a width, the continuation lines indented. */
export function wrap(text: string, width: number, indent = 0): string[] {
  const out: string[] = [];
  let line = "";
  for (const word of text.split(" ")) {
    if (line && textWidth(line) + 1 + textWidth(word) > width) { out.push(line); line = " ".repeat(indent) + word; }
    else line = line ? `${line} ${word}` : word;
  }
  if (line) out.push(line);
  return out;
}

export type HelpAction = { action: "close" | "exit" | "launch" | "none"; saver?: string; message?: string };

export class HelpView {
  selected = 0;
  top = 0;
  typed = "";
  message = "";
  /** What a key does in help. Digits then Enter, or arrows then Enter, start a screensaver; x starts a hidden one. */
  key(key: string, windowRows = 10): HelpAction {
    this.message = "";
    if (key === "\x03") return { action: "exit" };
    if (/^[0-9]$/.test(key)) { this.typed += key; return { action: "none" }; }
    if (key === "\r" || key === "\n" || key === "right") {
      const n = this.typed ? Number(this.typed) : this.selected + 1;
      this.typed = "";
      if (!Number.isInteger(n) || n < 1 || n > savers.length) { this.message = `no screensaver ${n}`; return { action: "none", message: this.message }; }
      this.selected = n - 1;
      return { action: "launch", saver: savers[n - 1].name };
    }
    this.typed = key === "\x7f" ? this.typed.slice(0, -1) : "";
    if (key === "q" || key === "?" || key === "h" || key === "b" || key === "left") return { action: "close" };
    if (key === "x") return { action: "launch", saver: "xmas-tree" }; // hidden
    if (key === "down" || key === "j" || key === "\t") this.selected = (this.selected + 1) % savers.length;
    else if (key === "up" || key === "k" || key === "backtab") this.selected = (this.selected + savers.length - 1) % savers.length;
    else if (key === "pagedown" || key === " ") this.top += Math.max(1, windowRows - 1);
    else if (key === "pageup") this.top = Math.max(0, this.top - Math.max(1, windowRows - 1));
    else if (key === "home") { this.selected = 0; this.top = 0; }
    else if (key === "end") this.selected = savers.length - 1;
    return { action: "none" };
  }

  private lines(width: number): Line[] {
    const w = Math.max(20, width - 2), out: Line[] = [];
    const add = (kind: Line["kind"], text: string, indent = 0, saver?: number) => { for (const l of wrap(text, w, indent)) out.push({ kind, text: l, saver }); };
    const row = (keys: string, what: string) => add("plain", `${keys.padEnd(22)} ${what}`, 23);
    add("heading", "Keys in the browser");
    row("Up Down j k", "scroll a line; Page Up, Page Down or Space scroll a page; Home and End");
    row("[n] then Enter", "follow link number n: type its number (shown beside the link), then press Enter");
    row("Tab, Shift-Tab", "select the next or previous link; Enter or Right follows it");
    row("b or Left", "back to the previous page");
    row("? or h", "this help; q, b or ? closes it");
    row("q or Ctrl-C", "quit");
    out.push({ kind: "plain", text: "" });
    add("heading", "Screensavers: Up Down or a number, then Enter, to start one");
    add("dim", "In a screensaver: Tab, Space or n for the next one; b for the one before; q or Ctrl-C to quit; any other key quits too. A screensaver started here returns to this screen.");
    savers.forEach((s, i) => add("item", `${String(i + 1).padStart(2)}. ${s.name.padEnd(10)} ${s.help}`, 16, i));
    out.push({ kind: "plain", text: "" });
    add("heading", "Options");
    row("--width COLS", "layout width for --dump");
    row("--dump", "print the page as plain text and exit");
    row("--colour LEVEL", "none, 16, 256 or 24bit; the default follows COLORTERM, TERM and NO_COLOR");
    row("--big-headings=M", "auto, on or off: large text for the first heading level");
    row("--wasm, --engine F", "choose the Wasm runtime, or a native library file");
    row("--font F", "a font file for the engine");
    row("--strict --no-scripts", "refuse bad HTML; do not run page scripts");
    row("--timing --verbose", "timings and details on standard error");
    row("--screensaver [NAME]", "a screensaver, with no page; --frames N stops after N frames");
    return out;
  }

  /** `rows` exactly: the header bar, the body, the footer bar. */
  render(width: number, rows: number, level: Level, utf8: boolean, pageTitle: string): string[] {
    width = Math.max(1, width);
    const bars = rows >= 3, body = bars ? rows - 2 : rows;
    const lines = this.lines(width);
    // Keep the selected screensaver in the window; keep the window in range.
    const first = lines.findIndex((l) => l.saver === this.selected), last = lines.length - 1 - [...lines].reverse().findIndex((l) => l.saver === this.selected);
    if (first >= 0) {
      if (first < this.top) this.top = first;
      if (last >= this.top + body) this.top = last - body + 1;
    }
    this.top = Math.max(0, Math.min(this.top, Math.max(0, lines.length - body)));
    const heading = level === 0 ? "\x1b[1m" : `\x1b[1;${sgrColour([255, 214, 90], level, false)}m`;
    const dim = level === 0 ? "" : `\x1b[${sgrColour([150, 160, 190], level, false)}m`;
    const item = level === 0 ? "" : `\x1b[${sgrColour([190, 230, 255], level, false)}m`;
    const fit = (text: string) => { const g = graphemes(text); let w = 0, s = ""; for (const c of g) { const cw = textWidth(c); if (w + cw > width) break; s += c; w += cw; } return s + " ".repeat(Math.max(0, width - w)); };
    const out: string[] = [];
    const title = sanitizeText(pageTitle);
    if (bars) out.push(barRow([{ text: utf8 && level > 0 ? " ▓▒░ TEXTNAUT HELP ░▒▓ " : " == TEXTNAUT HELP == ", bold: true }, { text: title ? `page: ${title}` : "" }], "page position kept ", width, level, 200));
    for (let y = 0; y < body; y++) {
      const l = lines[this.top + y];
      if (!l) { out.push(fit("")); continue; }
      const selected = l.kind === "item" && l.saver === this.selected;
      const marker = l.kind === "item" && l.text.match(/^ ?\d+\./) ? (selected ? (utf8 ? "▶" : ">") : " ") : " ";
      const style = selected ? "\x1b[7m" : l.kind === "heading" ? heading : l.kind === "dim" ? dim : l.kind === "item" ? item : "";
      out.push(`\x1b[0m${style}${fit(marker + l.text)}\x1b[0m`);
    }
    if (bars) {
      const hint = this.message || (this.typed ? `start screensaver ${this.typed}, then Enter` : "Up/Down choose | number Enter start | q back to the page ");
      out.push(barRow([{ text: ` ${this.selected + 1}/${savers.length} `, bold: true }], hint, width, level, 160));
    }
    return out;
  }
}
