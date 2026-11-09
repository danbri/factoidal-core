# textnaut

A text-mode web browser on the Foafnaut engine. Investigation:
https://github.com/danbri/factoidal-core/issues/371 (terminal WWW browser on the Foafnaut engine).
The engine loads the page, lays it out and runs its scripts; textnaut maps the positioned text
to terminal cells. Prototype: stage 0 and stage 1 of that issue, plus page scripts at load.

Run from `labs/demos/foafnaut`. The engine library is not in the repository: set
`TEXTNAUT_NATIVE` to a built `libweb-render.dylib`, or `TEXTNAUT_WASM_DIR` to a directory with
`web-render.mjs` and `web-render.wasm`. The native library is used when present; `--wasm` asks
for the Wasm runtime. The header bar, `--timing` and a line on standard error in `--dump` mode
name the engine that ran.

    deno run --no-prompt --allow-read --allow-ffi --allow-net --allow-env \
      --import-map=textnaut/import_map.json textnaut/textnaut.ts pages/showcase.html
    deno run ... textnaut/textnaut.ts --dump --width 80 https://info.cern.ch/
    deno run ... textnaut/textnaut.ts --wasm --timing --dump pages/showcase.html

Options: `--width COLS` (`--dump`), `--dump`, `--wasm`, `--engine FILE`, `--font FILE`,
`--colour none|16|256|24bit`, `--big-headings=auto|on|off`, `--strict`, `--no-scripts`, `--timing`, `--verbose`.

Output is plain text when standard input or output is not a terminal, or when `TERM` is unset or
`dumb`. A page that the engine refuses gives the reason on standard error and exit code 1.

## Keys

Arrows, `j`, `k`, Page Up, Page Down, space, Home, End scroll. A number, then Enter, follows that
link; Tab and Shift-Tab select a link, Enter or Right follows it. `b` or Left goes back. `q` or
Ctrl-C quits.

## What the display does

- It uses every row and column. Layout is to the terminal's actual width; rows past the end of
  the page are filled.
- Header and status bars change colour by column. Links have a colour from their number and a
  bold number badge.
- Colour level: `COLORTERM` truecolor or 24bit gives 24-bit colour; `TERM` with 256color gives
  the 256-colour palette; another `TERM` gives 16 colours; `NO_COLOR`, an empty `TERM` or `dumb`
  gives no colour. Block characters need a UTF-8 locale.
- Terminal queries at start (DECRQM 2026, XTVERSION, DA1, 300 ms at most): synchronized output
  is used only when the terminal says so. OSC 8 links are used only for terminals named by
  XTVERSION or the environment, and never inside tmux or screen.
- Only changed rows are written. There is no scroll-region optimisation.
- Resize: each SIGWINCH redraws the current text in the new size at once, and a new layout runs
  30 ms after the last signal of a burst, at the longest 150 ms after its first. The top row
  stays at about the same text. A resize that changes only the height redraws with no layout.
- The terminal is restored on `q`, Ctrl-C, end of input, SIGINT, SIGTERM, SIGHUP, SIGQUIT and on
  an uncaught error.

## Headings, rules and bullets

Interactive mode only; `--dump` output does not change. The engine gives no element names, so
each of these comes from what it does give:

- A heading is a line of text where every text item has a font size well above the body size
  (the size with the most characters on the page): 1.75 times or more is H1, 1.3 is H2, 1.1 is
  H3. A line that also has body-size text is not a heading. The lines of one wrapped heading
  join and wrap again to the terminal width; no character is cut.
- H1 is a centred panel in heavy box-drawing lines over a full-width band, gradient at 24-bit
  and 256 colours, blue at 16 colours, reverse video with no colour. H2 is a centred lighter
  band as wide as its text. H3 stays in place, in bold colour. The panel rows move the page
  down: the scroll length grows, and link numbers and targets stay.
- A horizontal rule is a painted line at least half the text width and at most 3.5 px high,
  drawn across the blank row at its height. With no blank row there, no line is drawn.
- A list marker is a run that reads `*` or `1.` or `a.` and whose source node has a box at
  least twice as wide as the run. It shows in colour, with `*` as a bullet in a UTF-8 locale.

Large text for H1 (`--big-headings=auto`, the default), used only when the terminal's answer at
start shows it. Each answer is a cursor position report (CPR):

- OSC 66 with `s=2` (Kitty's text sizing protocol): the cursor moves to column 3 after a space
  at scale 2. Expected from Kitty 0.40 and later (not run here).
- DEC double-width and double-height lines (ESC # 3 and ESC # 4): `CUF 999` on a DECDWL line
  stops at half the width. Expected from xterm and Windows Terminal (not run here).
- Any other answer, no answer, tmux or screen: the colour band. `on` uses DEC lines when
  nothing was detected; `off` never uses large text. Plain mode never uses it.

An OSC 66 line covers two terminal rows. When only one of them is in the body area, that row
is drawn at normal size. The tests and `pty_check.py` use simulated answers; no real Kitty,
xterm or Windows Terminal was run.

## Safety rule

No text from a page reaches the terminal with a control character in it. C0, DEL and C1
(with ESC and CSI) become U+FFFD; tabs and line ends become a space; bidirectional formatting
controls are removed. URLs in OSC 8 sequences are percent-encoded to printable ASCII; only
`http`, `https` and `file` URLs get one. The rule applies to page text, titles, link targets
and error messages. Tests: `textnaut.test.ts`.

## How positions map to cells

With no `--font`, the engine uses its built-in bitmap face, where one character is one advance.
The cell width is the advance of the font size that has the most characters, so body text is
one character per cell. These parts are approximate:

- Vertical distance: lines are the clusters of glyph tops; rows between two lines are limited
  to two blank rows.
- Words keep their own characters. A wider heading font has gaps only at word boundaries. A
  line that does not fit, for example after the link numbers are added, wraps at a word.
- Character width comes from a small table in `grid.ts`: terminals differ for emoji and
  ambiguous-width text. Right-to-left text is not tested.
- Colours come from the engine's draw list (`lean-svg-v1`); with another format the page shows
  no page colours. Fills larger than a cell give the background. Gradients do not.

## Page scripts

Scripts run at load on the engine's BubblePopJS when the engine has it (native and Wasm), with
up to 8 timer turns and 1 second of page time. An endless loop stops at the engine's limit (one
test page: 1 second). After load, the page gets no timer, key or pointer events. With
`--no-scripts`, no script runs. `<noscript>` content is shown in both modes.

## Not done yet (all under https://github.com/danbri/factoidal-core/issues/371)

H4, H5 and H6 have no heading style: H4 has the body size, and H5 and H6 are smaller. `<code>`,
`<pre>`, `<blockquote>` and tables have no style of their own: the engine's boxes, runs and
draw list do not tell them apart from other blocks, and no engine change is made here. Forms and text input; images, SVG and canvas (only a link's number shows for a linked image);
in-page `#fragment` scrolling; page key and pointer events. Expected-failure tests: the end of `textnaut.test.ts`.

## Tests

Run from `labs/demos/foafnaut`. No network.

    deno test --no-prompt --no-check --allow-read --allow-ffi --allow-env --allow-run --allow-net \
      --import-map=textnaut/import_map.json textnaut/textnaut.test.ts
    python3 textnaut/pty_check.py pages/showcase.html

`pty_check.py` drives the program on a pseudo-terminal at each colour level: frame size, a burst
of resizes, signals, follow and back. Its exit code is the number of failed checks.

## Screensavers

`textnaut --screensaver [plasma|tunnel|fire|rain|stars]` (a random one with no name). `n` changes effect; any other key quits. No engine and no page. 24-bit colour when `COLORTERM` says so, else 256 colours.
