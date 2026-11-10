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
`--colour none|16|256|24bit`, `--big-headings=auto|on|off`, `--strict`, `--no-scripts`, `--timing`, `--verbose`, `--screensaver [NAME]` (see Screensavers).

Output is plain text when standard input or output is not a terminal, or when `TERM` is unset or
`dumb`. A page that the engine refuses gives the reason on standard error and exit code 1.

## Keys

Arrows, `j`, `k`, Page Up, Page Down, space, Home, End scroll. `[n]` is a link number: type the
number shown beside a link, then Enter, to follow it. Tab and Shift-Tab select a link, Enter or
Right follows it. `b` or Left goes back. `?` or `h` opens the help screen (below). `q` or Ctrl-C
quits. The bottom line shows `? help | [n] Enter follow | Tab next | b back | q quit`.

### Help screen

`?` or `h` opens a full-screen help: all the keys, the options, and the list of screensavers.
Up and Down (or `j`, `k`, Tab, Shift-Tab) move the selection; a number then Enter, or Enter on
the selection, starts that screensaver. Page Up, Page Down and Space scroll the help. `q`, `?`,
`h`, `b` or Left close it. Ctrl-C quits. Opening help does not touch the page: its scroll
position, selected link and typed number are as they were when you close it. A screensaver
started from help returns to help when you quit it (`q` or another key); Ctrl-C quits the
program. Help redraws on resize. The header shows the page title through the same sanitiser as
the page header.

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
of resizes, signals, follow and back; every screensaver on its own (frame, keys, resize, exits,
frame cap); and the help screen (open, page position kept, start a saver and return, a number and
Enter, resize, Ctrl-C and signals inside a saver). Its exit code is the number of failed checks.
The `--wasm` checks are skipped when no Wasm runtime is found.

`textnaut.test.ts` also covers every saver at several sizes (1x1 to 200x60), at all four colour
levels with and without UTF-8 (frame size, colour kinds, ASCII only without UTF-8), seeded
determinism, resize, changed-row output, the key handling, the help view and its keys, the
sanitised page title in help, the 4D rotation, and the sponge cell counts.

## Screensavers

`textnaut --screensaver [NAME]` (a random one with no name). No engine and no page. `--frames N`
stops after N frames (for tests and pipes); `--colour none|16|256|24bit` sets the colour level.
The browser's help screen starts any of them too, and returns to help afterwards.

Keys inside a screensaver:

- Tab, Space or `n`: the next one. `b` (or Shift-Tab): the one before; the history is kept, so
  `b` walks back through every one you have seen. `b` with nothing before it does nothing.
- `q` or Ctrl-C: quit. Any other key (arrows, Enter, letters) also quits.
- Each saver shows a one-line caption on the bottom row for four seconds: its name, what it is,
  and these keys.

The savers:

| name | what you see |
| --- | --- |
| `plasma` | sine plasma in rainbow colour |
| `tunnel` | a chequered tunnel, flying down it |
| `fire` | flames rising from the bottom edge |
| `rain` | falling glyphs in rainbow columns |
| `stars` | stars flying towards you |
| `life` | Conway's Game of Life on a torus: young cells white, older cells shift hue, the dead leave a glow; it reseeds when it settles |
| `snakes` | snakes hunting dots on a wrapping board, growing as they eat, leaving colour trails |
| `sponge` | a rotating 3D Menger sponge, ray-cast through a voxel grid and lit (level 2, level 3 on tall terminals) |
| `sponge4d` | a 4D Menger sponge turning in the XW and YW planes (see below) |
| `lissajous` | three Lissajous curves drawn with a phosphor glow that fades |
| `metaballs` | blobs that merge and part as their fields add |
| `torus` | a spinning shaded torus with a specular highlight |
| `waves` | ripples from raindrops, spreading and reflecting from the edges |
| `maze` | a maze carved depth-first, then flooded in colour from the corner and solved |
| `cyclic` | a cyclic cellular automaton: 14 states chase each other into nested bands |

There are also a few hidden ones, which are not listed here, in help or in the normal rotation.

### The 4D sponge

The 4D Menger sponge keeps 48 of the 81 sub-hypercubes at each step (the 3D one keeps 20 of 27),
shown at level 2 (2304 hypercubes). It turns in the XW and YW planes, so parts of it pass
through the fourth dimension. The picture is made in two steps. The eye is at a point in 4D; each
voxel of a 3D "retina" cube looks along a 4D ray (with 4D perspective: things nearer the eye in W
are larger) through a slab of W and takes the first hypercube it meets. That 3D shape is then
ray-cast, lit and drawn like the 3D sponge. Colour is W depth: red nearest the eye in W, through
yellow and green, to blue farthest. Parts of the sponge appear, vanish and change colour as the
rotation carries them into and out of the slab; this is a view through a slab, not a full 4D
projection of every hypercube, and it shows the sponge's outer surface only. The rotation code
(`rotate4`) is checked in the tests to keep distance from the centre.

### How they are drawn

Each saver fills a pixel surface (two pixels per cell: an upper and a lower half block, so 80x24
is 80x48 pixels) and sometimes a glyph layer. A presenter turns it into bytes and writes only the
rows that changed, in one synchronized-output block. Frames are capped at 30 a second and at
about 6 MB a second of output (a full 24-bit redraw of a 200x60 terminal runs at about 20 a
second); the loop waits on input with a timeout, so it never spins. Resize is read every frame; the surface and the saver's state are
rebuilt for the new size.

Colour: 24-bit when `COLORTERM` says so, 256 colours for a `256color` `TERM`, 16 colours for
another `TERM`, none with `NO_COLOR` or no `TERM`. With no colour a saver is drawn as characters
from a brightness ramp. Without a UTF-8 locale there are no half blocks: a cell is a space with
a background colour (one colour per cell, half the vertical detail) and glyphs are ASCII.

The terminal is restored (alternate screen, cursor, wrap, raw mode) on `q`, Ctrl-C, end of
input, SIGINT, SIGTERM, SIGHUP, SIGQUIT and an uncaught error. Savers show no text from any page.
