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

## Open

- The window sweep (`--scroll-sweep`, before with `--single-frame`, after without) was not
  run on 2026-11-07: the screen was locked, so the window could not present (exit 3).
  The numbers above are off screen on the same GPU.
- The Hub page (`docs/web/hub/foafnaut/browser-worker.mjs`) loads its GPU transport from
  a published package. It gets the layer path with the next release.
- https://github.com/danbri/factoidal/issues/1269 (16-sample rule depends on the row count).
- A drag selection is in window coordinates, so a scroll with one makes a Lean frame.
- A graph frame is built from the model with no SVG text (`graphModel`, 2026-11-07,
  branch `wip/1268-packed`): one worker call for the event, then the frame build, with no
  `graphPage` call. Checked by differential guards, not proved.
- No press state is drawn before Lean answers.
