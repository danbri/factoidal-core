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
- No press state is drawn before Lean answers.
