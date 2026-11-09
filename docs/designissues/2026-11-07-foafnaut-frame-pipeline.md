# Foafnaut desktop frame pipeline: input, Lean frame build, GPU (2026-11-07)

Tracking: https://github.com/danbri/factoidal/issues/1268 (responsiveness and frame time).
Owner, 2026-11-07, verbatim: "Goal set: much faster perf, responsive, never miss a click!"

## Threads

- **Main thread** (Cocoa requires it): the native window library (`native_window.m`), the
  event pump, input handling, the GPU device and surface, and a Wasm engine for small calls
  only (`shellHit`, `hit`, `pointerUp`, `command`, history, address bar text). Each small
  call is timed; a call over 2 ms is traced as `native-html-slow-call`.
- **Engine worker** (`native_html_worker.ts`, `native_html_compile.ts`): one ordered queue of
  every slow Lean call (`render` compile, graph start, event and page, selected text, XSLT,
  inspect, font load, font requests). All Lean calls for a document run on this one thread,
  because the Lean runtime state (the held font) is not shared between threads.

## Engine backends

The worker calls `call(html, requestJSON, width, height) -> string`, from one of:

- the Wasm engine (`web-render.wasm`), and
- the native library `libweb-render.dylib`, opened through Deno FFI. `build-web-render.sh
  --native` links it from the same objects as `web-render-native` and the same C shim as
  the Wasm build, with a static Lean runtime. The release package puts it beside the
  window program; with no library, or with `--wasm-engine`, the worker uses Wasm.

A render goes through `call_bin(html, requestJSON, width, height) -> bytes`
(`web_document_call_bin`, 2026-11-07, branch `wip/1268-bytes`): a JSON head and the
storage floats and tile words as raw sections, with no Base64 and no inspector tree
(`tree:true` asks for it). The host views the sections as typed arrays of one buffer
and the worker transfers that buffer. The text call stays the reference
(`native_html_bytes_test.ts`).

Measured 2026-11-07, 1600 by 1200, Noto Sans, 5 pages: the native output is the same
bytes as the Wasm output. Frame build time is 1.6 to 1.9 times less (status page 99.5 ms
against 162.6 ms; index 11.7 ms against 19.5 ms).

## Input

- The window library queue grows (to 65,536 events, then it counts refusals in
  `ng_events_dropped`). No click, key or other discrete event is dropped. Adjacent moves and
  resizes keep the newest position; adjacent scroll steps add up.
  `native_window_queue_test.ts` checks this with 5,000 rounds of mixed events.
- Each event carries the time it was queued (`ng_event_clock`). Input latency
  (`native-html-input-latency`) runs from that time to the present of the first frame that
  includes the effect of the event.
- Graph input is queued in order. Moves, resizes and clock ticks not yet started merge, the
  newest wins; presses, releases and keys never merge.

## GPU

- One session per window. The pipeline is rebuilt only when the WGSL or the pipeline
  description changes; buffers are recreated only when they must grow; the surface is
  reconfigured only on a size change.
- An interactive frame does not read pixels back. The readback, the pixel check and the
  FNV hash run on every frame with `--check-pixels` and in sweeps, and in normal use once,
  500 ms after input stops, on the frame on screen (`native-html-checked`).
  `--idle-checks-only` gives a sweep the normal-use rule.

## Measurements (2026-11-07, Apple silicon laptop, 1600 by 1000)

- GPU session per frame: 26 ms before, 1 ms after.
- Draw of an unchecked frame: 2.6 ms (a checked frame: about 46 ms).
- Time the window takes no input (pump gap) after the first frame, `--idle-checks-only`:
  p50 about 10 ms, max 14 to 37 ms. Before: at least the whole frame, 100 to 290 ms.
- Click to present, from queue time, command sweep: 337 ms (Wasm) and 200 ms (native)
  before; 52 ms (Wasm) and 41 ms (native) after. Graph click: 179 ms before; 118 ms (Wasm)
  and 94 ms (native) after. These sweeps have 1 or 2 events each, so these are single
  readings, not percentiles.

## Scroll in a drawn band: two layers (done 2026-11-07)

Branch `wip/1268-gpu-scroll`. Before this, a scroll step was one full Lean frame: every
primitive moves, so all floats are packed again and the tiles are binned again.

Design:

- A render with `layers:true` and a shell (`WebDocument.layersJSON`) answers two scenes.
  The chrome layer holds window rows `0 .. top`. The page layer holds the page rows of a
  band, `band.top .. band.top+band.height`: the view plus `bandMargin` (512) rows above
  and below, at most `maxLayerRows` (4096). Lean also answers the composite WGSL
  (`compositeShader`) and the scroll range that the band keeps with no new render,
  `keepFrom .. keepTo` (`refreshMargin`, 128 rows, from a band edge that the page goes on
  past).
- The host (`layer_compositor.ts`, `native_html_session.ts`) draws each layer once into
  its own texture with the Lean plan. Each present runs the Lean composite: window row
  `y < top` from chrome row `y`, else page row `y-top+offset`, `offset = scroll-band.top`.
  The host decides no colour; it computes only the offset, kept in the band.
- `run_html.ts`: a scroll in the keep range presents the composite only (no Lean call;
  trace `native-html-scroll`). Outside the keep range it asks the worker for a new band
  and goes on presenting; past the band the view stays at the band edge until the new
  band arrives, and that scroll's latency is counted to that frame. With a drag
  selection (window coordinates) a scroll still makes a Lean frame. `--single-frame`
  keeps the old path for comparison.
- Link picking: the page layer's links are in band rows; the host converts the window
  row (`pageRow`).

Proof and tests:

- Lean (`WebDocument.lean`): `band_fits` (the band holds the view), `band_height_le`,
  `keep_fits` (every kept scroll is in the band), `composite_eq_frame` (for any page
  image, the composite at `scroll-band.top` is the chrome over the page from row
  `scroll`), `composite_row_lt` (the composite reads only band rows).
- The GPU part, that drawing the page moved by `band.top` gives the image moved by
  `band.top`, is not proved: Float has no algebraic laws in Lean. Two checks instead:
  `#guard sameAsFrame` in `WebDocumentTests.lean` compares the Lean CPU sampler of the
  composite with one frame (compose) at scrolls in bands made at other scrolls, exactly
  (a mutation with the offset off by one fails it); and `scroll_layers_check.ts`
  (in `test.sh`) compares the GPU bytes of the composite with one Lean frame.
- GPU result, status page, 1600 by 1000, Noto Sans, 8 scrolls: 6 pass with 1 to 3
  pixels different (the moved geometry rounds to float32 differently in the band than in
  one frame; offsets are whole device pixels). 2 are an expected failure: the 16-sample
  edge rule depends on the scene row count (65,536), and the band and the frame fall on
  different sides of it (about 35,000 pixels differ):
  https://github.com/danbri/factoidal/issues/1269 (refinement depends on the row count).
  One frame on main has the same defect from one scroll to the next.

Measurements: see `docs/20261105-render-embedded-perf.md`, section "Scroll in a drawn
band".

## Scroll prefetch of the next band (done 2026-11-07)

Branch `wip/1268-prefetch`. Before this, a scroll step that left the keep range waited
for a full Lean frame in the worker (one band render, then the GPU draw of both layers).

Rule (`scroll_prefetch.ts`, applied in `run_html.ts`):

- The host keeps the scroll motion: direction, and rows per millisecond (the mean of the
  last and the new step; a turn takes the new speed; a pause of more than 250 ms ends it).
- A prefetch is due when the scroll is in the keep range and moving, and either it is 256
  rows or fewer from the edge in its direction, or its speed reaches that edge within
  two frames (33 ms) plus the time of the last band render in the worker.
- Target: the next band starts its keep range where the band on screen ends. Down, the
  target scroll is `keepTo + reach`; up, `keepFrom - reach`; clamped to the page. `reach`
  is read from Lean's answer: `(bandHeight-view)/2 - (bandTop+bandHeight-view-keepTo)`,
  384 rows for `bandMargin` 512 and `refreshMargin` 128. No prefetch when the band on
  screen already reaches the page edge.
- The request is the one a frame at the target would send. Its state key is that request
  with `shell.scroll` left out: the document, the width and height, the resources (by
  identity), the graph model, and every other option and shell field. A prefetched band
  is shown only when its key equals the key now, the band on screen does not keep the
  scroll, and the prefetched band does. The chrome does not depend on the scroll
  (`WebShell.compose` uses it only to move the page), and `composite_eq_frame` holds for
  any band that keeps the scroll, so the swap shows what a Lean frame at that scroll shows.
- Priority (`native_html_worker.ts`): a request with `low` runs only when no ordinary
  request waits; before it starts, the worker takes in the messages that came while a
  Lean call ran. A newer low request replaces an unstarted one (answered `dropped`). A
  frame for another state sends `dropLow`. A low request that has started runs to its
  end: one Lean call holds the thread. The host sends a prefetch only when the worker has
  no ordinary call, no frame is due or running, no page loads and the graph queue is empty.
- A scroll past the band while a prefetch for the same state is made, within `reach` of
  its target, waits for it and makes no frame; when it comes and does not keep the scroll,
  or is dropped or stale, the host makes a frame (`missed` in the summary).
- Input order does not change: clicks, keys and graph events take the paths they took
  before; the prefetch only adds a low request.

Tests: `scroll_prefetch_test.ts` (7 tests: reach, trigger, contiguous next band down and
up and at both page ends, speed, motion, state key, swap rule) and a worker test in
`native_html_test.ts` (with the Wasm engine: order, replace, `dropLow`, and the prefetched
band equals an ordinary call for the same request).

Window sweep, status page, 1600 by 1000, layers, Apple M1, engines from `724f5bf7a`
(12 scroll steps of 120 rows; trace `native-html-scroll`, `native-html-prefetch`):

- Idle checks only (`--idle-checks-only`), max input latency: native 100.4 and 104.0 ms
  before; 33.3, 17.1 and 18.5 ms after. Wasm 135.0 and 133.8 ms before; 18.1, 17.0 and
  17.6 ms after. Lean frames after the first: 3 (native) and 2 (Wasm) before, 0 after.
  One prefetch was sent, made and shown in each run; the swap present took 5 to 8 ms.
- Every frame checked (no `--idle-checks-only`; every probe pixel checked, so a swap reads
  back both layers): max input latency native 428.8 ms before, 109.4 ms after; Wasm 459.8 ms
  before, 127.0 ms after. All probe checks pass.
- `--graph-sweep` (no scroll; one event): native 170.5 ms before, 161.9 ms after; Wasm
  245.7 ms before, 171.9 ms after. No prefetch is sent.

`--perf-summary` and the start trace (`native-html-engine`) name the engine: `engine:
native PATH` or `engine: wasm`. When the worker can not start, Lean runs on the main
thread, which has only the Wasm engine; the summary said `native` then.

## Graph page history and the pointer (done 2026-11-07)

Owner report, 2026-11-07, verbatim: "back arrow nav fails on foaf viz interactive." and
"having mouse pointer change to a hand when over a link".

Cause of the back failure: the link `foafnaut:graph` was a browser command, and the host
opened the graph in a NEW tab whose session history had one entry. Back had no entry to
go to, by the history rule (`WebHistory.History.back`); the chrome's back button, Command-[
and Command-Left all did nothing.

Fix: `WebShell.link` and `WebShell.submit` answer `.page "foafnaut:graph"` for the graph
(`WebShell.command`). The host loads that URL with the graph app in the same tab, and
pushes it on the tab's history like any page. Back from the graph loads the page before
it; forward loads a new graph (the graph state is not kept). Guards: `WebShell` (the link
answers) and `WebHistory` (back and forward over the graph entry). Window check:
`run_html.ts --back-sweep` (each `url:X` step fails the run unless the page shown ends
with X; the steps press the chrome's back button, Command-[, Command-Left and
Command-Right, before and after graph clicks and a drag).

Pointer: Lean answers `pointerCursor` on the main-thread engine for each coalesced
pointer move: `WebShell.pointer` gives the I-beam over the address bar, the pointing hand
over a chrome control that acts (back and forward only when they have an entry), and on
the page the hand over a link of the frame on screen (`Rendering.hitLink`) or over a
person of the graph (`WebGraph.acts`), else the arrow. The host keeps the link list as
text for each frame, and calls `ng_set_cursor` only when the answer changes. The window
library sets the NSCursor again when a move comes back into the view after AppKit's
window-edge pointer. `--back-sweep` checks the hand over a link and the arrow off it.

## Press acknowledgement, `:active`, `:hover`, `:visited` (2026-11-07)

Branch `wip/1268-press-feedback`. Owner, 2026-11-07, verbatim: "Still something off in
the ux, maybe things like having mouse pointer change to a hand when over a link, mayb
other css-esque conventions like underlines on links or some visual acknwoeldgement when a
link is pressed. Definitely need that when a button is pressed." (The cursor is a separate
task.)

Lean (`formal/lean4/L4Factoidal/Rendering/Style.lean`, `Layout.lean`):

- Selectors: `:link`, `:visited`, `:any-link`, `:hover`, `:active` (Selectors Level 4 §8,
  §9). They match over an `ElementState` from the request: `hover` and `active` are node
  ids (the element and its ancestors match), `visited` the hyperlinks whose resolved
  `href` is in the session history. A pseudo-class counts as a class in specificity. Other
  pseudo-classes still drop their rule.
- The user agent sheet (`userAgentSheet`) is a cascade origin below the author (CSS
  Cascade 4 §6.1): `:link` #0000EE, `:visited` #551A8B, `:link:active`/`:visited:active`
  #FF0000, `:any-link` underlined (HTML §15.3.4); `button` an inline-block, `padding:1px
  6px`, `border:2px outset #767676`, background #EFEFEF, #E5E5E5 on `:hover`, and on
  `:active` `border-style:inset` with #C8C8C8 (HTML §15.5.4 leaves the look to the user
  agent; these values are this profile's choice). Before, a link was #0000FF from a
  built-in initial value, and an author rule could not tell `:visited` from `:link`.
- A rule that matches only through `:visited` sets colours only (`visitedProperties`).
- Borders (`border`, `border-width`, `border-style`, `border-color`; none, solid, inset,
  outset) on blocks and inline-blocks. An inline-block is one atomic box (CSS 2.2 §10.3.9
  shrink-to-fit); its glyph runs and boxes are kept, so selection and links inside work.
  Its bottom margin edge sits on the baseline, as a replaced element does here.
- `hover`, `active` and `visited` are layout fields (`WebDocument.layoutFields`): a
  change lays out again. `WebShell.Shell.pressed` is not: a sunken chrome button reuses
  the kept layout and changes only the chrome layer.

Press acknowledgement (no Lean frame):

- On a pointer press the host makes one small main-thread call, `press`. Lean answers the
  chrome control or the link (`sourceNode`) under the pointer, and up to 8 rectangles in
  source rows (chrome rows, then page-layer rows plus `top`): the control's box, or every
  link region of that anchor.
- The composite shader (`WebDocument.compositeShader`, model `compositePress`) multiplies
  the colour by 0.75 inside the rectangles. The host presents the composite at once.
  `compositePress_nil`: with no rectangle it is `composite`, so `composite_eq_frame` holds.
  Page rectangles move with the page in the band (`sourceRow_page`).
- A press held 150 ms gets a Lean frame with the press (`active`, `shell.pressed`). When a
  Lean frame that includes the press is presented, the darkening is cleared for it. A
  release clears the darkening at once (one more composite), and asks for a Lean frame
  only if one with the press was asked for.
- A present with the darkening is not checked against Lean's probes (it is not Lean's
  frame); no idle check runs during a press. A prefetched band swap during a press
  clears the darkening and asks for a Lean frame (the rectangles are in band rows).
- Order: the press present only adds a GPU present; it does not wait for Lean and it
  takes no event out of order. The chrome action still runs on the press, as before.
- `:hover`: the layers answer has `hoverRules` (an author rule names `:hover`). Only
  then does a pointer move send the link under it (`hit`), and only a change makes a frame.
- `--no-press-look` gives the behaviour before, for comparison.

Tests: `L4Factoidal/Rendering/Tests.lean` (UA colours, `:active` on a descendant, author
over UA, `:visited` colour-only rule, specificity, button box 28 by 13, pressed and idle
buttons paint different colours); `WebShell.lean` and `WebDocumentTests.lean` (`press`
answers, `compositePress`, layout cache with state, `hoverRules`);
`native_html_test.ts` (engine `press`, `:active` and sunken chrome frames);
`scroll_layers_check.ts` (on the GPU: the composite darkens exactly the press rectangles;
a frame with reload pressed differs from the idle frame only in the button's box).
Expected failures: https://github.com/danbri/factoidal/issues/1277 (`:hover`/`:active` on
elements that are not links: the host has no element hit test).

Window sweep, `--press-sweep` (press and hold link 0 for 300 ms, release; press and hold
reload, release), index page, Apple M1, `--idle-checks-only`, two runs each, engines from
this branch. Times are from the queue time of the press to the present.

- Before (`--no-press-look`): a link press presents nothing until the release (no frame,
  no latency entry). A reload press shows first in the reload frame: native 67.9 and
  63.5 ms, Wasm 96.4 and 93.0 ms.
- After: the darkening is presented in 12.4 to 16.6 ms (native) and 12.3 to 14.8 ms
  (Wasm), for both the link and reload. The present itself takes 0.8 to 1.3 ms; the rest
  is the wait for the next event pump (8 ms) and the window's queue.
- The Lean frame of a held link press (`:active`, laid out again): 169 to 215 ms after the
  press (150 ms hold rule plus about 20 to 65 ms of frame). The reload frame, which now
  includes the sunken button: 74 to 161 ms native, 105 to 136 ms Wasm.

The approach with the lower measured latency is the composite darkening: it needs no Lean
call, so it takes one present (about 1 ms) where a Lean frame with the kept layout would
take the frame build and both layer draws (the reload frame above, 64 ms and more).

## Mac app conventions, address bar editing and printing (2026-11-07)

Owner, 2026-11-07, verbatim: "Can we add more conventional OSX-isms for it to work nicely
as an OSX app? Like can I alt-tab to it, my focus automatically beginning in the URL bar,
and be able to do command-a select all and command-c or command-x or whatever as well as
command-v? (and same on other platform builds which I hope are continuing, and ideally in
hub/web version too). In OSX I want to be able to print a showcaase page, and print in
general, which should be easy since osx is nicely designed, right? So we'll need a demo
page well suited for printing. As well as maybe the svg tiny page of comparisons."

### The app

- `foafnaut.app` is a regular app: no `LSUIElement`; `Info.plist` has `CFBundleName`,
  `CFBundleDisplayName`, `CFBundleIconFile` (`AppIcon.icns`, a FOAF graph drawn by
  `make-icon.py` and made with `sips` and `iconutil` in `build-executables.sh`), version,
  category and `NSPrincipalClass`. The `run` script `exec`s the window program, so the
  process keeps the bundle's identity.
- `ng_app_start` (window library) sets the regular activation policy, installs the menu,
  calls `finishLaunching` and activates the app. `run_html.ts` calls it before it loads the
  engine, so the Dock icon and Command-Tab entry are there at once. `ng_create` and
  `ng_show_after_surface` activate again with `[NSApp activate]` (macOS 14 and later; the
  older `activateIgnoringOtherApps:` before that).
- The window title is the page title (Safari), else "foafnaut".

### The address bar is a text field (Lean: `WebShell`)

The `Shell` value has a selection anchor, one undo step and one redo step, and a
`typing` flag (typed text after typed text is one undo step). `Shell.edit` does `focus`
(the address, all selected), `selectAll`, `copy`, `cut`, `paste`, `undo` and `redo`, and
answers the text for the clipboard. `Shell.key` takes the modifier bits: Shift extends the
selection, Option moves and deletes by word (`wordStart`, `wordEnd`), Command goes to the
end of the line; delete with a selection removes it; left or right with a selection goes to
its start or end. Typed and pasted text replaces the selection; a pasted line break and
the white space around it go (`clean`). The bar draws the selection behind the text and
hides the caret, as a macOS field does.

- A new window and a new tab start with the bar focused and the address selected.
- The `command` op takes `focused`. Lean answers `target:"address"` for copy, select
  all, cut, paste, undo and redo when the bar has the focus, and for paste always (the
  bar is the only text field). Else copy and select all act on the page, as before.
- The host keeps the edit state (`editJson`) and only reads and writes the clipboard.
- Menus: Edit has Undo (Command-Z), Redo (Shift-Command-Z), Cut, Copy, Paste, Select
  All; File has Page Setup (Shift-Command-P, the system panel) and Print (Command-P).
- Command-Left and Command-Right stay Back and Forward (History menu) when the bar has
  the focus; Home and End, Up and Down, and Option with the arrows move in the bar.

### The Hub page

`browser.mjs` gets Lean's key table (`keyTable` op, platform `mac` or `other`) from the
worker at start, and keeps from the host browser each key in it (Command on a Mac,
Control elsewhere). Paste comes from the `paste` event, which carries the clipboard text;
copy and cut send the text Lean chose to `navigator.clipboard.writeText`. The worker uses
the same `shellEdit` and `command` ops as the window host.

### Printing

1. Command-P sends command 18; Lean answers `print`.
2. The host reads the paper of the page setup (`ng_print_paper`, points) and lays the page
   out at 2 device pixels a point, text at 150% (16 CSS px is 12 pt), with
   `media:"print"`.
3. CSS: `CSS.parseFor medium` reads the rules of `@media` blocks whose media query list
   holds for the medium (a media type, `all`, with `only`; a query with a feature, `not`
   or `and` does not hold). `CSS.parse` is `parseFor "screen"`. Style sheets with
   `media="print"` apply when printing; `inspect` lists them, so the host fetches them.
4. `printLayout` answers the page breaks (`WebPrint.paginate`): a forced break at
   `break-before`/`break-after: page` (and the CSS 2 `page-break-*: always`), counted
   once when two have no text between them; else the lowest row that no line box, image or
   `break-inside: avoid` block crosses; else the page edge (a box taller than a page is
   cut). At most 200 pages. The break properties come from the cascade
   (`WebPrint.declared`: importance, `style` attribute, specificity, order).
5. For each page, a render with `printPage:[top,rows]` draws those rows at the top of a
   page image, white below them. The GPU renders it offscreen (`gpu_transport.render`).
6. `ng_print` gives the images to `NSPrintOperation` with an `NSView` that knows its pages.
   The print panel shows, modal, as in other Mac apps: Save as PDF, Preview, printers.
   With `--print-pdf FILE` the job is saved to the file with no panel, and the host counts
   the PDF's pages against Lean's.

Page images are raster (144 dpi). There is no vector path for the HTML scene:
`SceneSVG.lean` exports the older `NativeGraphics` scene, not `Rendering.Scene`.

### Checks (2026-11-07, Apple M1 laptop, screen locked)

- Lean guards, in the native and the Wasm build of `build-web-render.sh`: the address
  edits (`WebShell`), the page breaks (`WebPrint`), the `command` target, `shellEdit` and
  `keyTable` ops (`WebDocumentTests`), and `@media` (`Rendering.Tests`).
- `test.sh --skip-build`: exit 0. Demo pages: 14 rendered, 0 failed (out of 14), with
  `print-showcase.html`. New in it: `native_print_check.ts` (three page images to a PDF
  with no panel: 3 pages, each 595 by 842 points, A4); `print_layout_check.ts` (the
  showcase in Lean: 4 pages, each chapter starts a page, the screen note is not in the
  print layout and is on screen); `print_document_check.ts` (the whole path with no
  window: Lean pages, GPU images, `NSPrintOperation`; 4 pages laid out, 4 in the PDF).
- The same path on other pages: `svg-gallery.html` 1 page, `status.html` 3 pages. Pages
  looked at as images (`pdftoppm`): no line cut at a page edge.
- `open -n foafnaut.app`: LaunchServices lists it as `type="Foreground"` (Dock and
  Command-Tab), `Version="1"`, check-in 3.1 s after launch.
- NOT RUN in a window: `--edit-sweep`, `--print-pdf` and the frontmost check. The screen
  was locked, so the window could not present (`native-html-sweep-blocked`, exit 3). The
  Dock icon was not seen.
- The Hub page: syntax checked only (`node --check`); no WebGPU browser here.
- SVG Tiny: no comparison page is in `labs/demos/foafnaut/pages`; the hub page
  `render-scores` is a Nunjucks template. `svg-gallery.html` prints on one page.

### Open

- Printing gaps, one issue: https://github.com/danbri/factoidal/issues/1279 (vector
  output, panel paper changes, tables, Hub print, `@page`).
- Printing is raster at 144 dpi; a vector PDF needs a `Rendering.Scene` to PDF or SVG
  writer.
- The page is laid out for the paper of Page Setup when Command-P is pressed. A paper
  change in the print panel does not lay the page out again.
- HTML tables are not laid out as tables (cells stack). The print showcase uses rows of
  fixed-width inline blocks.
- The Hub page does not print through Lean: Command-P there is the host browser's print
  of the canvas.
- Linux and Windows have no window library: https://github.com/danbri/factoidal/issues/1278
  (foafnaut desktop window on Linux and Windows).

## Keys, selection colours, images and tab icons (2026-11-07)

Owner, 2026-11-07, verbatim: "todo: add command-r for reload (or ctrl, per platform). And
most common other keyboard shortcuts that are dominant especially cross-browser." / "the
toolbar ctrl-a ctrl-c etc needs to use CSS to style text differently when selected" /
"please support favicons, at least SVG ones." / "can we display GIF or PNG or JPEG or
animated GIFs or similar yet?"

- **Keys.** `WebHistory.keyTable` is the one table, for macOS (Command) and other
  platforms (Control): reload (Command-R, Shift-Command-R, F5), new, close and reopen tab
  (T, W, Shift-T), tab 1 to 8 and the last tab (1 to 9), next and previous tab
  (Control-Tab, Shift-Control-Tab, Shift-Command-[ and ], Control-Page Up and Down), find
  (F), page and line scroll (Space, Shift-Space, Page Up and Down, arrows), top and bottom
  (Home, End, Command-Up and Down), stop (Escape, Command-.). Lean answers the tab to show
  (`tabTarget`) and the scroll (`scrollTarget`) in the `command` answer. The macOS menu
  has an item for each key with Command and for Control-Tab; other keys come from the
  window as key codes and Lean maps them (`pageKey`). The Hub page reads the same table.
  Find is refused: https://github.com/danbri/factoidal/issues/1280.
- **Selection colours.** Selected address text is white on blue
  (`WebSelection.selectionBackground`, `selectionText`), and the caret is hidden. The page
  selection uses the same blue as a translucent mark; its glyphs keep their colour:
  https://github.com/danbri/factoidal/issues/1281.
- **Images.** HTML `img` is main's replaced element (92e82d268, `Layout` `Picture`,
  `WebRender.makeReplaced`); the branch's own `img` box (`Layout.imageSize`,
  `WebRender.sizeImages`) was dropped when the branches were merged. The branch adds GIF
  to the one image store: `ImageGIF` reads every frame with its delay and disposal, and
  a page shows the first frame: https://github.com/danbri/factoidal/issues/1284. WebP and
  AVIF: https://github.com/danbri/factoidal/issues/1283. Page `showcase-image-formats.html`
  shows PNG, JPEG, GIF and animated GIF.
- **Tab icons.** `WebDocument.iconURL` chooses the icon (HTML §4.6.7.8): scalable first,
  then the smallest at least 32 device pixels, the last of equal ones, then an
  `apple-touch-icon`. No link gives no icon; `/favicon.ico` is not tried. ICO is skipped:
  https://github.com/danbri/factoidal/issues/1282. `iconPrepare` keeps SVG text (drawn by
  the SVG engine in the tab) or fits a bitmap to 16 points. The built-in pages name
  `pages/foafnaut-icon.svg`, the graph of the app icon.
  The native window shows them; the Hub page does not fetch them yet (its files are kept
  as main has them; the dropped hunks are with the Hub session).

## Open

- The scroll sweep moves down only. Scroll up is tested by the rule tests, not in a window.
- The status page has 1,424 rows of scroll, so a sweep makes one prefetch; a chain of
  prefetches on a long page was not measured in a window.
- The Hub page (`docs/web/hub/foafnaut/browser-worker.mjs`) loads its GPU transport from
  a published package. It gets the layer path with the next release.
- https://github.com/danbri/factoidal/issues/1269 (16-sample rule depends on the row count).
- A drag selection is in window coordinates, so a scroll with one makes a Lean frame.
- A graph frame is built from the model with no SVG text (`graphModel`, 2026-11-07,
  branch `wip/1268-packed`): one worker call for the event, then the frame build, with no
  `graphPage` call. Checked by differential guards, not proved.
- `:hover` and `:active` match only links and chrome controls in the window:
  https://github.com/danbri/factoidal/issues/1277 (no element hit test).
- An `:active` link frame lays out again (the state is a layout field); a paint-only
  restyle with the kept layout is not done.

## Links below the first screen, the scroll limit (2026-11-07)

Owner reports: a link of `showcase.html` below the first screen did nothing when
clicked after a scroll; the data visualisation and lettering pages did not scroll to
the end.

- Cause 1, in Lean. `Layout.render` cut each link region at the viewport height, so a
  link below the first screen had no region in any frame, and a click on it found no
  link. Main repaired this first (0e4f29e01, `linkHeight`, theorems in 8655a2bb5); the
  branch's own repair was dropped when the branches were merged.
- Cause 2, in the host. A navigation could finish while a frame of the old page was
  being drawn; the end of that frame cleared `candidate`, so the new page was never
  drawn. The frame now clears `candidate` only when it drew it.
- Cause 3, in the host. `scrollLimit` took the chrome as 60 rows; it is 65 (39 when
  narrow) at scale 1, so the last 5 to 10 rows were out of reach. Lean now gives the
  limit with the layers (`WebDocument.scrollLimit`, the page bottom less the view;
  theorems `scrollLimit_reaches`, `scrollLimit_short`).

Window checks: `run_html.ts --follow-links --link-scroll-sweep` on `showcase.html`
(wheel steps down to each page link, the hand pointer over it, a click at its drawn
place, the URL after the load, back; then the last link again from the end of the
page). `run_html.ts --scroll-end-sweep` scrolls to the end and fails unless the last
row of the layout is in the view.

## Engine capability and host permissions (2026-11-08)

Two failures of 2026-11-08 had the same form: host code used something that the engine or the
compiled program in use did not give.

1. **Page code must probe the engine before it uses a new ABI.** The Hub page called the
   font export with 5 arguments (fallback fonts) on a published engine whose export takes 4.
   The engine aborted and the page fell back to the bitmap font. Rule: a new argument, op or
   export is used only after the page reads the engine's capability list (`scriptInfo().ops`,
   `info().ops`, or the export's presence), and the page has a path for the older engine.
   Fixes: 34a00e5a7 and 463c07016 (`fontBytesTakeFallback`).
2. **A compiled host must have every permission its source uses.** `run_html.ts` started to
   read `HOME` (to find the QuickJS guest, ac482fba8), but `deno compile` in
   `build-executables.sh` gave no `--allow-env`. Every test from source passed; the app
   stopped at start. Fix: 384230207, `--allow-env=HOME`, and `build-executables.sh` now starts
   the compiled program off screen (graph sweep) and fails when it does not start. A new
   `Deno.env` read needs its name added to that flag.

Related measurement: `sweeps.sh` input latency includes a pixel check of every frame (a sweep
sets `everyFrame`). The graph click is 195 ms there and 27.6 ms with `--idle-checks-only`
(native engine, off screen); in a window it is 23 ms.

### Where a frame on a kept layout goes (measured 2026-11-08)

The index page (1,063 primitives, 229 links), native engine, `compileLayers` at 1600 by 1000
with `checks:false`, 10 calls each: the same request 28.7 ms; `active` toggled 53.1 ms;
scroll toggled 31.9 ms. `frameWork`: 0 layouts, 10 kept, so the layout cache works. With
`checks` left on, each call is about 60 ms more. A `sample` profile of the same request
repeated (2,693 samples in the library): `layersJSON` 2,420, of which `WebRender.artifactWith`
1,342 (`Scene.make`, `DisplayNode.lowerTR`, `Scene.tiles`, `compilePrimitivesLoop`) and
`Scene.jsonWith` 629 with `float32BytesFast` 581. So a frame on a kept layout builds the
whole scene and its bytes again. The next step is in Lean: keep the lowered scene and its
bytes with the layout, and write again only the primitives that a pointer state changes.

A host cache of whole Lean answers by state (scroll left out) was tried and dropped: in the
press, graph and scroll sweeps it gave 0 hits, because the release frame differs from the
idle frame (`live`, `loading` after a link, the address, the tab title).

The `press` call costs about 1 ms with the 229 links (0.02 ms with none); not the cost.

### Frame and click costs, 2026-11-08 (measured, native unless named)

| Change | Commit | Before | After |
|---|---|---|---|
| Page layer kept for a chrome-only frame (`pageArtifact`) | aa23d058f | 28.7 ms | 3.0 ms |
| Link regions decoded once per frame (`decodeLinks`, `pickKept`), Wasm | 0fb2e20b7 | hit 4.7 ms, press 6.1 ms | 0.12 ms, 0.9 ms |
| Loading state drawn at once; painted pointer states kept | bfbed32a8 | click to first frame, max 730-800 ms | 72 ms |
| SVG text `fmt` without the general formatter | f9deb4cac | new dataviz layout 665-833 ms | 230-257 ms |

Next, from a profile of a new dataviz layout after f9deb4cac (2,256 samples in the
library): the SVG reader parses the path text that `NativeSVGText.lowerSfnt` writes
(`readListWith`/`readNode`, 811), and writing it costs 595 (`lowerTree`). Giving the
reader the glyph geometry directly, with no text, removes both; it changes the reader in
`SVG.lean`, which the CPU backend also uses.
