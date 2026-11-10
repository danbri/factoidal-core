# Engine state cells: what the browser engine keeps between calls, and how it is passed

Date: 2026-11-11. Issue: https://github.com/danbri/factoidal-core/issues/390.
Scope: the Lean modules of the built-in engine under `labs/demos/foafnaut/`. Counts are
from `tools/lean-hygiene-audit.py` (comments and strings stripped) on `main` at
`4078eafa2`: 29 `unsafe`, 29 `@[implemented_by]`.

## 1. The form today

Each cell is an `initialize x : IO.Ref T`. A pure-typed function reads or writes it
through `unsafeBaseIO` in an `unsafe` definition named by `@[implemented_by]`. The
logical model (the body Lean proves things about) is the uncached function, or an
`opaque` with no body. Calls are kept in place by `noinline`, a request argument, or
`compiler.extract_closed false`; that is a convention, not a guarantee.

## 2. The cells

"C ABI op" is the shim function (`web_render_shim.c`) whose call reaches the cell.
Every one of them is reached through `web_document_call` / `web_document_call_bin`
(Lean `WebDocument.compile` / `compileBin`); other entry points are listed where they apply.
Lifetime is the process unless a bound is given; nothing is cleared when a page changes,
except where said.

| # | Cell (file) | Holds | Written by | Read by (C ABI op) | Bound |
|---|---|---|---|---|---|
| 1 | `heldRef` (WebScripts) | page-script engine state: guest module, AOT module, session, BubblePopJS realm and session, pending AOT turn | `take`/`keep` around every `scriptSession` action; `loadModuleBytes` | `web_document_call(_bin)` op `scriptSession`; `web_document_font_call_bin` with family `guest:quickjs(-aot)` | one module, one session |
| 2 | `entropy` (WebScripts) | no cell: 32 bytes of `IO.getRandomBytes` read from pure code | — | `scriptSession` `start` (session `crypto.getRandomValues`) | — |
| 3 | `timed` (WebWasm; used by WebScripts) | no cell: the host clock read from pure code | — | `scriptSession`, WasmVM ops (`wasmRun`, demos, spec sample) | — |
| 4 | `timed` (WebSparql) | no cell: the host clock | — | SPARQL planner ops | — |
| 5 | `keptWordsRef` (SVGText) | SVG text words shaped, by font SHA-256s, text, px | `wordKept` inside SVG text lowering | every render with inline SVG text | 8,192 words, then emptied |
| 6 | `imageStoresKept` (WebRender) | decoded image stores by image keys and bytes | `imageStoreKept` in `makeReplaced` | renders with images; `web_render_call` too | last 2 |
| 7 | `parsedKept` (WebDocument) | parsed DOM by source and syntax | `parseKept` in `prepareDOM` | every document op that parses | last 2 |
| 8 | `shapedKept` | words shaped outside the font memo (bidi pieces, other direction) | `shapeKept`, the shaper given to `SfntProfile.profile`, called inside layout | renders with a held font | 16,384, then emptied |
| 9 | `sheetsKept` | parsed style sheets by text | `sheetKept` in `rulesOfSheets` | renders, `inspect`-like ops | last 8 |
| 10 | `keptLinksRef` | link regions decoded from the last `linksText` | `decodeLinks` | `web_render_hit`; op `press` | 1 |
| 11 | `keptPageRef`, `pageWorkRef`, `pageIdRef` | page-layer answers (scene, boxes, face, band, flags, retained compile, layout text, damage id); counters | `pageArtifact` (kept answer by `ptrEq` of its inputs; retained compile compares primitives by `ptrEq`) | render with `layers:true`; op `frameWork` reads the counters (`pageWork`) | last 2 |
| 12 | `heldFontRef` | held fonts and their word memo | `keepFont` (`fontLoad`), `keepWords` (each layout with a held font) | `heldFont` in layout, `canvasEnv`, `fontFaces`, render key | 64 fonts; memo 65,536 words |
| 13 | `webFontRef` | `@font-face` fonts by SHA-256 | `keepWebFont` (`fontLoad` mode 2) | `webFontsHeld` in layout | 16 |
| 14 | `heldImagesRef` | image bytes by key and SHA-256 | `keepImages` (`imageLoad`, `imageDrop`) | `heldImages` in layout, `canvasEnv`, `imageInfo`; `web_document_image_call_bin` | 64 images, 32 MiB |
| 15 | `layoutRef`, `frameWorkRef` | layout memo (`Lru LayoutKey Laid`); layouts/kept/repaints counters | `keptLayout`, `keepLayout`, `countRepaint` (in `cachedFrame`) | every render; `frameWork` reads the counters | `layoutSlots` |
| 16 | `paintedRef` | frames with a pointer state painted on a kept layout | `keptPainted`, `keepPainted` | renders with hover/active | 2 |
| 17 | `paintWorkRef`, `paintedSceneRef` | last paint-only scene by base scene (`ptrEq`) and values; counter | `painted` | renders of pages with script transforms or SVG animation; `frameWork` | 1 |

The 29 `@[implemented_by]`: WebScripts 4 (take, keep, peek, entropy), WebWasm 1 and
WebSparql 1 (timed), SVGText 1, WebRender 1, WebDocument 21 (parseKept, shapeKept,
sheetKept, decodeLinks, pageArtifact, heldFont, keepFont, keepWords, webFontsHeld,
keepWebFont, heldImages, keepImages, painted, paintWork, keptLayout, keepLayout,
countRepaint, frameWork, pageWork, keptPainted, keepPainted). Each has one `unsafe` body.

Which theorems run through a cell: `SVGText.wordKept_eq`, `WebDocument.pageArtifact_eq`
and `pickKept_eq` are `rfl` about the model, not the compiled code. `frameWith_eq`,
`lookupLayout_eq` and `stored_valid` are about an explicit memo value and do not read a
cell; the engine's use of them assumes that `layoutRef` holds a valid memo, which no
proof covers.

## 3. The replacement: the engine state is a value

The engine is `Engine → Request → Engine × Answer`. `WebDocument.Engine` is an ordinary
structure with a field per cell. The shim keeps one handle:

```c
static lean_object *engine;               /* made by web_engine_new in ready() */
lean_object *r = web_document_compile_bin(engine, html, request, w, h, lean_io_mk_world());
lean_object *pair = lean_io_result_get_value(r);
engine = lean_ctor_get(pair, 0); lean_inc(engine);   /* the new state */
lean_object *answer = lean_ctor_get(pair, 1); lean_inc(answer);
lean_dec(r);                                          /* engine is unique again */
```

- The handle is passed owned, so Lean holds the only reference and updates in place:
  no copy of the state per call. Inside, a field is taken out before it changes
  (`let held := e.scripts; let e := {e with scripts := {}}`), as `take` did, so the
  JS heap, the memo and the held images stay unique.
- The hosts' ABI does not change: `native_window.m`, `run_html.ts`, the Hub's Wasm
  `.mjs` call the same shim functions with the same arguments. Only the shim and the Lean exports change, and they are built together
  into one library (native) or one `.wasm` (Wasm). As before, one call at a
  time per loaded engine.
- The exports are `BaseIO` only for what reads the machine: the clock (`timed`, now
  `BaseIO`) and `IO.getRandomBytes` for a new script session. Every other op is a pure
  function of the state and the request, called from the `BaseIO` export.
- `WebDocument.run` and `runUncached` stay pure for the tests: `run` starts from
  `{}` (an empty engine).
- `ptrEq` is itself `unsafe` in Lean core. The kept page answer (cell 11) and the
  paint-only scene (cell 17) compare inputs by address. Without `unsafe` they need an
  identity that the engine assigns: a serial number on each `Laid` when the layout is
  made, and the paint values' key. The retained compile's per-primitive `ptrEq`
  (partial frames) needs WebPaint to say which primitives it changed. That is the part
  of this issue with a speed risk; it is done last and measured.
- Caches used inside layout (cells 5 to 9) are passed into `layOut` and come back
  with the `Laid`. The shaper given to `SfntProfile.profile` (cell 8) and SVG text
  words (cell 5) are called from inside `Rendering.Layout` and SVG lowering, which
  are pure and keep no table; they need either a lookup-only table passed in plus
  the words a layout made coming back out, or a pass that shapes the words before
  layout. Both change `formal/lean4` code and are measured before they land.

## 4. Order of work and status

1. This record (done).
2. Plumbing: `Engine`, the handle in the shim, `BaseIO` exports.
3. WebScripts (cells 1 to 3), WebWasm and WebSparql (`timed` in `BaseIO`).
4. WebDocument cells used at the top of a request: 10, 12 to 16.
5. Layout caches: 7, 9, 6; then 8 and 5.
6. Identity by serial: 11 and 17.

Each step lowers `LAB_BASELINE` in `tools/lean-hygiene-audit.py`. Status is kept in
section 5.

## 5. Status

Branch `wip/390-state`. Lab counts 29/29 → 3/3.

| Cell | Now |
|---|---|
| 1 `heldRef` | `Engine.scripts`; taken out of the state for a `scriptSession` call |
| 2 `entropy` | `WebWasm.Machine.randomBytes` (`BaseIO`: `IO.getRandomBytes`; `Id`: none) |
| 3, 4 `timed` | `WebWasm.Machine.timed` (`BaseIO`: host clock; `Id`: 0). WasmVM ops, SPARQL ops and script sessions run in `M` |
| 5 SVG words | `Kept.words`; `NativeSVGText.wordIn`, `wordIn_eq` |
| 6 image stores | `Kept.stores`; `WebRender.storeIn`, `storeIn_eq` |
| 7 parsed trees | `Kept.parsed`; `parseIn`, `parseIn_eq` |
| 8 `shapeKept` | **left** (see below) |
| 9 sheets | `Kept.sheets`; `sheetIn`, `sheetIn_eq` |
| 10 links | `Engine.links`; `decodeKept`, `decodeKept_eq`, `decodeKept_valid`, `pickIn_eq` |
| 11 page layers | **left**: `pageArtifact`, `pageWork` (see below) |
| 12–14 fonts, web fonts, images | `Engine.holds` (`Holds`), passed to layout as a value; a layout gives back its word memo (`Laid.words`) |
| 15, 16 layout memos, counters | `Engine.layouts`, `Engine.painted`, `Engine.frameWork`; `Engine.layOutKept`, `frameKept`, `frame` |
| 17 paint-only scene | `Engine.paintedScene`, `paintWork`; kept by the layout's number (`Laid.serial`) in place of `ptrEq` |

How a layout uses `Kept`: it looks entries up and gives back what it made (`Laid.made`);
`Engine.layOutKept` adds them and keeps the layout without them. In liberal mode the
liberal run gets what the strict run made, as the old cells gave it.

Left, and why:

- `shapeKept` (cell 8): the shaper is a closure that `Rendering.Layout` calls for words
  outside the memo; it can look a table up, but the layout has no way to give back what
  it shaped. Needs either a layout that returns its shaped words (a change in
  `formal/lean4/L4Factoidal/Rendering/Layout.lean`) or a pass that finds those words
  (bidi pieces, other directions) before layout. Measure before choosing.
- `pageArtifact`, `pageWork` (cell 11): the kept page-layer answer compares scene, boxes,
  face and marks by address, and the retained compile (partial frames) compares each
  primitive, geometry and style by address (`WebPaint.retainedAnswer`'s `reuseLeaf`).
  The layout serial covers the first part; the per-primitive part needs `WebPaint.patch`
  to say which primitives it changed. Released in 0.35.0, so left for a separate change
  with the partial-frame tests and timings.

Not proved: that the memos in `Engine` are valid for `Engine.holds` and `Kept` (a layout
changes the word memo and `Kept`, which by design change no layout). The refinement
theorems above each take validity as a hypothesis.

## 6. Timings (2026-11-10, M-series Mac, main `4078eafa2` against this branch, alternated runs)

| Measure | main | branch |
|---|---|---|
| Frame engine ms p50, `pages/status.html`, 1600×1000 dpr 2 (`frame_split_bench.ts`) | 3.8–4.0 | 3.9–4.1 |
| Same, `pages/spinal-tap-sparql.html` | 11.3–11.5 | 11.3–11.5 |
| First compile ms, native: foaf-explorer / timers-and-clicks / json-script (`first_compile_bench.ts`) | 22–23 / 8 / 2 | 21–22 / 8 / 2 |
| First compile ms, Wasm, same pages | 208–249 / 16–18 / 3–4 | 220–221 / 17–18 / 3 |
| `fib(24)` page start, QuickJS-NG in WasmVM, native, wall ms | 1328–1331 | 794–803 |
| `fib(24)` page start, BubblePopJS, native, wall ms | 28.0–28.2 | 27.5 |
| WPT page start (Node-appendChild), QuickJS-NG, native ms (`bubblepop_bench.ts`) | 807 | 508 |
| Timer frame mean ms, QuickJS-NG, native | 0.52 | 0.35 |

The QuickJS-NG gain was not a goal. A likely cause, not checked: the old `timed` kept the
closure `fun _ => (f s).runLocal` alive for its error path, so the session was shared and
its arrays were copied on write; `Machine.timed` drops it. `partial_frame_test.ts` passes
(retained bytes equal to `retained:false`).
