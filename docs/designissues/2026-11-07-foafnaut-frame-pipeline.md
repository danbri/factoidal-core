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
