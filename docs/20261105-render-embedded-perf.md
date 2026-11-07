# Render performance pass, with an ESP32-P4 target

Date: 5 November 2026. Scope: the Lean web renderer (foafnaut2525) on the bitmap
font path. All numbers are local, on an Apple Silicon Mac under load from other
work. Instructions and peak memory are the main measures, because wall time is noisy.

## Results

`labs/demos/foafnaut/web-render/fixtures/status.html` (3,017 bytes), 800×600:

| Measure | Before | After |
|---|---|---|
| Paint items | 21,237 | 8,658 |
| Packed floats | 594,484 | 242,272 |
| Native instructions | 9.31 G | 2.39 G |
| Native peak memory (RSS) | 152 MB | 32.6 MB |
| Native time | 0.66–0.74 s | 0.18 s |
| Artifact JSON | 2.84 MB | 1.55 MB |
| Wasm call in Node, 5 calls | 2.7–6.6 s | 1.0–1.5 s |

`default.html`: 0.94 G to 0.31 G instructions, 19.8 MB to 11.8 MB, wasm about
220 ms to about 100 ms. Empty engine start (refused page): 56 M to about 40 M
instructions.

## Correction: layout is not the main cost

The status note and earlier reports say that layout takes about 2 seconds. That
figure is the whole Lean compile. A profile from the first instruction of the native
build shows, before this pass: `Scene.json` 96%, of which CPU check samples 73% of the
artifact time, number formatting 9%, packed data 6%, tiles 4%. All of DOM, style and
layout was about 2%. After this pass layout is about 9% of the artifact time.
This split was measured native. The wasm build has no symbols, so it is not measured
there. `fixtures/status.html` line 28 still says the old claim; correct it with that
file's owner. A shaped-word cache will not fix frame time on this evidence.

## Changes

1. `bitmapOutline` emitted one 1×1 rectangle for each lit font pixel. It now merges
   runs and equal rows. Rectangles stay in integer glyph units and the transform acts
   on the sample position, so the covered area is exactly the same. A `#guard` checks
   all 95 characters: each lit cell covered, no unlit cell covered, no overlap.
2. `Expr.prepare` called `Float.ofNat` for each literal, which uses bignum
   conversion. `literalFloat` gives closed values, with theorem `literalFloat_eq`.
3. `Prepared.and` and `or` fold a known left operand. `andThen` does not prepare the
   right side when the left side decides. The `eval` theorems are unchanged in meaning.
4. `rectHit` tests a rectangle in direct code, with the same Float operations in the
   same order. It replaces about 30 nested closures. `rectHit_eq_fillCondition` is `rfl`.
   `overColors_no_stroke` proves that the stroke test cannot change a sample with no
   stroke paint, and `prepareSample_correct` still holds for all primitives. Note: stroke
   width defaults to 1 with stroke paint `none`, so a test on width alone never fires.
5. The HTML entity map is a `Thunk`. It was built at each engine start.
6. `web-render/check-budget.mjs` fails a native build that exceeds a paint item or
   float budget. Counts are deterministic.

## Verification

- Full `--pixels` images, old against new binary: 4 of 4 identical. Inputs: all printable
  ASCII at 7, 11, 13.5 and 17 px at 150×140 and 97×71; `flow` at 90×60; `links` at 120×70.
- `checks`, `boxes`, `glyphRuns`, `links` in the artifact: identical on `status.html`.
- `check-wasm.mjs` passes on the new engine. `check-budget.mjs` passes.
- The artifact itself changes (fewer primitives). `tree` is no longer `null` on the status
  page, because it now fits the inspector limit.
- WebGPU in Chrome on Metal, old against new artifact: 9 of 9 full images byte-identical,
  including `status.html` at 800×600 and 500×700. `check-browser.mjs` passes 5 of 5.
  That check needs `.build/font-shape`, `.build/script-engine/qjs-wasi-reactor.wasm` and
  Python Pillow.
- Not tested: full-size CPU images (over 9 minutes for one 380×340 image), a comparison of
  real-font pages, any real ESP32.

## Suggested target

**ESP32-P4, on the M5Stack Tab5** (ESP32-P4NRW32): dual RISC-V up to 400 MHz (one source
gives 360 MHz for this board), 768 KB L2 memory, 32 MB in-package PSRAM, 16 MB flash,
5 inch 1280×720 MIPI-DSI touch panel, 2D Pixel Processing Accelerator, ESP32-C6 for Wi-Fi.
Sources: https://www.espboards.dev/esp32/microcontroller/esp32p4/esp32-p4/ ,
https://docs.m5stack.com/en/core/Tab5 ,
https://docs.zephyrproject.org/latest/boards/espressif/common/soc-esp32p4-features.html .
A 16-bit 1280×720 frame is 1.8 MB, so it fits PSRAM with room for a scene.

Limits that shape the design:

- **Single-precision FPU only.** Lean `Float` is 64-bit, so it becomes software floating
  point. The device raster path must use fixed point or Float32.
- **No GPU or WebGPU.** The device needs a strip or tile CPU rasteriser. The current
  per-pixel closure sampler is a test oracle, not a renderer.
- **32 MB for everything.** 32.6 MB peak on a 64-bit host does not fit yet. Boxed floats,
  lists of strings and JSON are the main causes.
- **Runtime port not proven.** Lean's C and C++ runtime has not run under ESP-IDF. wasm32
  shows that 32-bit Lean works. The web-render binary is 7.4 MB, which fits 16 MB flash.

## Next steps, in order

1. A binary scene format (`ByteArray` or `FloatArray`). This removes number formatting,
   string quoting and JSON parsing, and boxed floats in the packed data.
2. One paint item for each glyph, which names a shared outline. This must come before real
   fonts: a path for each glyph instance through the winding test costs far more than
   today's rectangles.
3. Find why wasm is about 5× slower than native. It predicts 32-bit behaviour. Lack of
   GMP in that build is a guess, not a measurement.
4. Measure on rv32: a Lean hello build under ESP-IDF, then instruction counts.
5. An integer strip rasteriser in Lean, checked against the existing CPU sampler.

## Graph frame cost (2026-11-06)

`foafnaut:graph`, 1600 by 1200, 649 primitives, Wasm, median of 8 frames. Measured
by calling the document operations in turn. The model transition is 1.4 ms and the
SVG text is 1.8 ms; the rest is `compile`: HTML parse about 69 ms, layout and SVG
about 39 ms, artifact about 145 ms before the cuts.

`web-render-native FILE W H --svg-profile` times each artifact part. Native, 292
primitives: CPU probes 11.8 ms, float text 6.5 ms, shader text 4.4 ms, tiles 3 ms.

Three cuts took `compile` from 257 ms to 190 ms: a render lists only script elements,
not the whole DOM snapshot; the shader text is made once; a frame of a page already
on screen has one CPU probe, not six. Paint data of such a frame is unchanged
(`native_html_test.ts`). The next costs are the 49 KB HTML parse and the float text.

A stack sample of the frame (`web-render-native FILE W H --document-repeat OPTIONS N`
under `/usr/bin/sample`) showed `HTML.adjustName` at 1,253 of 3,432 samples: it lowered
the whole SVG name table for each name. The tables are now lowered once
(`adjustLowered_eq` proves the same result). `compile` went from 190 ms to 133 ms in
Wasm and from 83 ms to 50 ms native. Next in that sample: SVG parse, then float text.

## Real font and float transfer (2026-11-07)

Stack samples of `status.html` with Noto Sans gave two faults. First, `wordsOf` splits on
spaces, so the space was never in the word memo, and layout ran the whole shaper for it at
each gap: 42% of the frame. Second, decimal text for the storage floats was 57% of what
remained. Hosts stored those floats as binary32 anyway, so `render` with `binary` now sends
them as Base64 bytes (`float32Base64`). `native_html_test.ts` checks the bytes equal the
text form exactly.

Wasm, 1600 by 1200, repeat frames, with other builds running on the machine:

| Page | Bitmap before | Bitmap after | Real font before | Real font after |
| --- | --- | --- | --- | --- |
| Demo index | 80 ms | 37 ms | 181 ms | 26 ms |
| Settings | 89 ms | 43 ms | 243 ms | 31 ms |
| Architecture | 294 ms | 146 ms | 868 ms | 117 ms |
| Project status | 384 ms | 209 ms | 1,756 ms | 175 ms |

The real font is now faster than the bitmap font, because it has about a third of the
primitives. Graph frame `compile`: 133 ms to 106 ms.

## Zoom, frame compile cuts and a kept layout (2026-11-07, afternoon)

Tracking: https://github.com/danbri/factoidal/issues/1268 (responsiveness and frame time).

Zoom. There is no largest text scale; the smallest is 50%. A zoom step multiplies by
about 1.1, rounded to a multiple of 5 (`WebSelection.zoomIn`, `zoomOut`). A new window
starts at 150%. The cost does not grow with scale: outlines are kept in font units, one
shaped word serves every size, and `inWindow` leaves out glyphs far from the window.
Native, status page, 1600 by 1200: 150% 112 ms, 2000% 75 ms per frame (repeat of 10);
one frame at 100000% renders. The external-shaper path (`fontData`, HarfBuzz) still
refuses pixel sizes above 512 (`FontRequests.add`); the default Noto Sans path does not.

Where the frame went (stack samples, native, `--document-repeat`, Noto Sans). The HTML
parse is not the main cost now: `prepareDOM` is 9% of the graph frame (about 4 ms
native). The earlier "HTML parse about 69 ms" in Wasm was measured before the
`adjustName` cut and counted the inline SVG with it. The costs were:

- Status page: artifact 97%. `Scene.data` 25%, CPU probe (`Scene.checks`, one probe)
  16%, `Scene.make` 17%, `Scene.tiles` 12%, `float32Base64` 11%. The point-box fold (tuple
  of boxed floats) was 13%, from `compilePrimitive`, `screenBox` and `fixedRows`.
- Graph page: inline SVG parse 44% (path tokens from a list of characters 14%,
  `NativeSVG.number` 18%), artifact 40%, CPU probe 19%.
- Top self time, status: `_tlv_get_addr` (allocator thread-local), `mi_free`,
  `lean_dec_ref_cold`, the `float32Base64` loop, `List.reverseAux`, the point-box fold,
  `mi_malloc_small`, `Array.appendList`, `lean_byte_array_push`, `List.zipWith`. That is,
  allocation of boxed floats and list cells.

Cuts:

- Point-box fold over an unboxed record, `pow10` with no list, `Scene.data` pushed onto
  one array: `@[csimp]` with proofs (`pointBox_eq_fast`, `pointBounds_eq_fast`,
  `pow10_eq_fast`, `Scene.data_eq_fast`).
- A gradient box is made only for gradient paint (definitional).
- Path data of ASCII bytes is tokenised by byte index (`tokensAscii`), and
  `[+-]digits[.digits]` numbers are read from bytes (`numberSimple?`). Other text goes
  to the reference. These two are checked by differential `#guard`s against the
  reference (`sameTokens`, `sameNumber`), not by a proof.
- A request with `checks:false` has no CPU probe. Hosts send it for interactive frames.
- The layout of the last render is kept (`WebDocument.layOut`, `LayoutKey`). The key is
  the HTML, the request fields that layout reads (`layoutFields`), width, height, chrome
  height and the held font (family, SHA-256). `layOut` gets only the key, so it can
  read nothing else. `lookupLayout_eq` proves a lookup over a valid entry equals
  `layOut key`; `stored_valid` proves the stored entry is valid. Guards compare `run`
  with `runUncached` over scroll, selection, width, scale and document changes. The
  font memo is a shortcut only: for one DOM, `remember` adds all its words before
  layout, so the memo state does not change a layout.

Output bytes are equal before and after on the 10 demo pages and the graph frame.

Measurements, 1600 by 1200, Noto Sans, scale 150%, median of 9 (Wasm, `web_document_call`
time only) or mean of 40 (native, the first frame with the cold font memo included in
"full"). "Scroll" is the same document with `shell.scroll` 40 pixels further each frame.

| Page, frame | Wasm before | Wasm after | Wasm after, checks:false | Native before | Native after | Native after, checks:false |
| --- | --- | --- | --- | --- | --- | --- |
| Status, full | 136 ms | 118 ms | 80 ms | 100 ms | 85 ms | 71 ms |
| Status, scroll | 149 ms | 129 ms | 84 ms | 100 ms | 69 ms | 55 ms |
| Graph, full | 78 ms | 64 ms | 49 ms | 43 ms | 32 ms | 25 ms |
| Graph, scroll | 78 ms | 30 ms | 15 ms | 43 ms | 13 ms | 9.6 ms |

A status scroll frame is still mostly the artifact: every frame packs all floats of the
visible glyphs again, because a scroll moves every primitive. The next cut is the
pre-rendered band with a GPU offset (issue item 2), or keeping the packed data of the
page and changing only the page transform. After that: `Primitive.rows` makes lists of
boxed floats (a `FloatArray` data path), and `float32Base64`.

## Scroll in a drawn band (2026-11-07, evening)

Tracking: https://github.com/danbri/factoidal/issues/1268 (responsiveness and frame time).
Design and proofs: `docs/designissues/2026-11-07-foafnaut-frame-pipeline.md`, section
"Scroll in a drawn band: two layers". Branch `wip/1268-gpu-scroll`.

A render with `layers:true` answers the chrome and a band of the page as two layers. The
host draws each layer once; a scroll inside the band presents only the Lean composite at
a new offset, with no Lean call.

Measurement: `scroll_layers_check.ts --bench`, off screen on the laptop GPU (the screen
was locked, so the window sweep could not run). Status page, 1600 by 1000, Noto Sans,
scale 150%, `checks:false`, 20 steps of 120 backing pixels from the top (scroll limit
1424). "Before" is one Lean frame and its draw for each step (the path that
`--single-frame` keeps). "After" is the composite for each step. A Deno
`onSubmittedWorkDone` wait has a delay of its own (14.6 ms for an empty submit), so the
GPU time is also given from 20 passes with one wait.

| Per scroll step | Native before | Native after | Wasm before | Wasm after |
| --- | --- | --- | --- | --- |
| Lean call | 63.7 ms | none | 86.7 ms | none |
| Host CPU to submit | 2.4 ms | 0.2 ms (max 0.3) | 2.5 ms | 0.2 ms (max 0.4) |
| GPU, one pass | 22.1 ms | 0.15 ms | 21.9 ms | 0.16 ms |
| Step to GPU done, p50 (includes the 14.6 ms wait) | 107.7 ms | 14.8 ms | 128.4 ms | 14.7 ms |

A new band was needed at steps 8 and 12 of 20 (Lean keep range): 113 to 133 ms native,
141 to 163 ms Wasm, for the layer render and the two layer draws. In the window host this
runs in the worker while composites go on; the view stays at the band edge only if the
scroll passes the band before it arrives.

The before figure here is larger than the 55 ms of the section above because it
includes the GPU draw of the frame to the end (22 ms) and runs the engine on the
calling thread.

Pixels: the composite is compared with one Lean frame at 8 scrolls (`scroll_layers_check.ts`,
in `test.sh`). 6 pass with 1 to 3 pixels different (float32 rounding of the moved
geometry). 2 are an expected failure,
https://github.com/danbri/factoidal/issues/1269 (the 16-sample edge rule depends on
the scene row count).

Not measured yet: `run_html.ts --scroll-sweep` in a window (input latency from queue
time to present), before with `--single-frame` and after without, Wasm and native.

## Packed scene bytes and graph frames from the model (2026-11-07, night)

Tracking: https://github.com/danbri/factoidal/issues/1268 (responsiveness and frame time).
Branch `wip/1268-packed`.

Changes, in order:

1. Storage bytes with no list of floats. `Scene.float32Bytes` pushes the binary32 bytes
   of each record onto one `ByteArray` (`Primitive.writeRows`). Proof:
   `Primitive.writeRows_eq` (the bytes of the reference list `Primitive.rows`) and the
   `csimp` theorem `Scene.float32Bytes_eq_fast`. Edge counts with no edge list: `csimp`
   on `Geometry.recordTagCount`, `geometryTailRowCount` and
   `BackendPrimitive.storageRows` (`edges_length`). `Scene.json` takes the size from
   `Scene.dataSize` (`Scene.dataSize_eq`) and builds `s.data` only for the CPU probes and
   the decimal text. The Base64 text is valid UTF-8 by construction
   (`ascii_push_valid`), so no pass checks it; it is compared with the reference
   `float32Base64Ref` by differential `#guard`s, not by a proof.
2. Tile boxes with no list: `csimp` `Primitive.screenBox_eq_fast` (bounds by a fold
   over the contours, four corners as values, the same Float operations in the same
   order).
3. Graph frames from the model. A render with `graphModel` lays out `WebGraph.skeleton`
   (the graph page with an empty `svg` element, so the same layout, boxes and node
   numbers) and takes the picture from `WebGraph.embedding`, which builds the scene
   from the model (`WebGraph.directScene`). There is no SVG text, XML parse or path
   parse. `graphPage` still gives the SVG text for export. Not proved: differential
   `#guard`s in `WebDocumentTests.lean` compare the artifact of the direct scene with
   the artifact of the parsed SVG text, and the frame through `graphModel` with the
   frame of the page text, for three models; a changed stroke cap fails both.
   `native_html_test.ts` compares the frames of three models with three requests.

Output bytes: SHA-256 of the render of each of the 13 demo pages and the graph frame,
5 requests each (binary with and without probes, decimal text, scroll 400, layers),
equal before and after each step, native (library and CLI) and Wasm.

Measurements, 1600 by 1200, Noto Sans, scale 150%, `checks:false`. Native: mean of 40
(`web-render-native --document-repeat`, `--document-scroll`). Wasm: median of 9
(`web_document_call` time only). Before is the branch `wip/1268-gpu-scroll`.

| Page, frame | Native before | Native after | Wasm before | Wasm after |
| --- | --- | --- | --- | --- |
| Status, full | 70 ms | 44 ms | 80 ms | 48 ms |
| Status, scroll | 54 ms | 29 ms | 82 ms | 49 ms |
| Architecture, full | 45 ms | 29 ms | 53 ms | 34 ms |
| Architecture, scroll | 31 ms | 17 ms | 53 ms | 33 ms |
| Graph, full, page text | 25 ms | 21 ms | 48 ms | 44 ms |
| Graph, full, `graphModel` | | 8 ms | | 22 ms |
| Graph, scroll | 9.6 ms | 5.8 ms | 15 ms | 11 ms |

Where the status frame goes now (stack samples, native): Base64 text 15%, storage bytes
16%, inspector tree JSON 10%, tiles 8%, `Scene.make` 22% (curve flattening 14%, mostly
allocation of a list and an array for each path segment), layout and the rest 29%.
Next cuts: push flattened points onto the contour array in `NativeSVGCurves.flatten`;
Base64 from the record writer in one pass; leave out the inspector tree on interactive
frames (a request field).

### Proposal, not landed: an edge rule independent of the scene row count

https://github.com/danbri/factoidal/issues/1269 (refinement depends on the row count).
Today a pixel takes 16 samples at an edge only when the whole scene has at most 65,536
rows. The status page has 73,521 rows, so its frame never refines, and a band of it
does. The limit was set before tiles, when each pixel visited every row. With tiles,
a pixel visits only the records of its tile. Per-tile work (sum of record rows of the
listed primitives), from the artifacts:

| Scene | Scene rows | Largest tile | 99th percentile tile |
| --- | --- | --- | --- |
| Status page | 73,521 | 2,891 | 1,078 |
| Architecture page | 48,396 | 2,630 | 383 |
| Graph page | 13,110 | 545 | 427 |
| W3C `metadata-example-01-t.svg` (forgiving mode) | 11,186 | 6,533 | 6,125 |

Rule: refine a pixel at an edge when the rows of its tile are at most 65,536. That keeps
the per-pixel bound of the old rule. `Scene.tiles` adds the rows of each list (one
addition per entry) and sets the top bit of the tile start offset (offsets are below
1,000,000, so the bit is free). The shader tests that bit in place of
`arrayLength(&params.rows)`; the CPU sampler (`samplesWithData`) reads the same bit.
Cost: no new words; Lean CPU about one pass over the tile entries; GPU: edge pixels of
pages above 65,536 rows take 16 samples in place of 4. On the status page that is the
cost the band already pays; the GPU time of a full frame is not measured yet (the
screen was locked). A band and a frame still have different tile grids, so a tile near
the bound can differ between them; anchoring page tiles to page rows removes that.

## No inspector tree, bytes answers, curve points pushed in place (2026-11-07, late)

Tracking: https://github.com/danbri/factoidal/issues/1268 (responsiveness and frame time).
Branch `wip/1268-bytes`, from `wip/1268-packed`.

Changes, in order:

1. The inspector tree only on request. A document render answers `"tree":null` unless
   the request has `tree:true`. No frame host reads the tree (`svg_engine.ts` and the
   browser-webgpu lab read it from the SVG export `svg_compile`, which is not changed).
   It was about 84 KB of each status frame. Evidence: with `tree:true`, the answers of
   13 demo pages and the graph frame, 5 requests each, are the bytes of before (native
   library and Wasm); `#guard`s in `WebDocumentTests.lean` compare the answers with and
   without the tree apart from that field, for one frame and for layers.
2. Bytes answers. The export `web_document_call_bin(html, request, width, height,
   out_len)` (`WebDocument.compileBin`) answers bytes (`WebDocument.packAnswer`): uint32
   little-endian total length, head length, section count and section lengths; the JSON
   head (spaces to a multiple of 4 bytes); then the sections, each from a multiple of 4
   bytes. The head is the `web_document_call` answer with `"dataSection":k` in place of
   `"dataBase64"` and `"tilesSection":k+1` in place of `"tiles"` (layers: page 0 and 1,
   chrome 2 and 3). Section `k` is the binary32 storage bytes, `k+1` the uint32 tile
   words. Other answers have no section. `native_html_engine.ts` reads it from Wasm
   (one `HEAPU8` copy) and from the native library (`Deno.UnsafePointerView.getArrayBuffer`,
   one copy) and gives `data` and `tiles` as `Float32Array` and `Uint32Array` views of
   the one buffer; the worker transfers that buffer once. `loadHTML(engine,"text")`
   keeps the JSON and Base64 path; it is the reference. The Hub worker uses the export
   when its runtime has it, else the text path. Evidence: `native_html_bytes_test.ts`
   (in `test.sh`): 10 HTML demo pages, 4 requests (frame, scroll 400, CPU probes,
   layers), 50 scenes with the same storage bytes, tile words and other fields, Wasm and
   native library; Lean `#guard`s put the sections back as Base64 and decimal tiles and
   compare with the text answer; the GPU layer check passes as before (6 pass, 2
   expected failures, https://github.com/danbri/factoidal/issues/1269).
3. Curve points pushed in place. `NativeSVGCurves.flatten` pushes each line end, curve
   point and arc point onto the contour array (`flattenBezierInto`, `flattenArcInto`),
   with no list and array for each segment. `flattenRef` is the old function. Not proved:
   differential `#guard`s in `SVGCurves.lean` compare the two (point bits and error text)
   on lines, quadratics, cubics, arcs, five transforms, three tolerances and the point
   budget errors. A second change, the padding of the flatness test with no list, was
   measured and left out: it made the Wasm status frame 2.5 to 4 ms slower (native
   faster).

Output bytes: the text answers of the 13 demo pages and the graph frame, 5 requests
each, are equal after steps 2 and 3 to the answers after step 1 (native library, CLI
and Wasm).

Measurements, 1600 by 1200, Noto Sans, scale 150%, `checks:false`. "CLI": mean of 40
(`web-render-native --document-repeat`, `--document-scroll`, text answer). "Library" and
"Wasm": median of 9, the Lean call alone (`decode-bench.ts`, the same request as the
CLI); "host decode" is the time from the answer pointer to the scene with typed arrays
(text: `UTF8ToString` or `getCString`, `JSON.parse`, Base64; bytes: copy, head parse,
views). Before is `wip/1268-packed`.

| Page, frame | Before | Step 1 | Step 2 (bytes) | Step 3 |
| --- | --- | --- | --- | --- |
| Status, full, CLI | 44 ms | 41 ms | 41 ms | 40 ms |
| Status, scroll, CLI | 29.1 ms | 25.9 ms | 25.9 ms | 24.8 ms |
| Architecture, full, CLI | 29 ms | 27 ms | 27 ms | 26 ms |
| Architecture, scroll, CLI | 17.1 ms | 14.9 ms | 14.9 ms | 14.4 ms |
| Graph, full, CLI (page text) | 21 ms | 20 ms | 20 ms | 20 ms |
| Graph, scroll, CLI | 5.7 ms | 4.8 ms | 4.8 ms | 4.7 ms |
| Status, full, Wasm | 49.1 ms | 44.5 ms | 34.7 ms | 33.4 ms |
| Status, scroll, Wasm | 48.7 ms | 43.7 ms | 34.7 ms | 33.1 ms |
| Architecture, full, Wasm | 34.2 ms | 30.7 ms | 25.1 ms | 23.7 ms |
| Architecture, scroll, Wasm | 32.5 ms | 28.9 ms | 23.0 ms | 22.1 ms |
| Graph, full, Wasm (page text) | 43.7 ms | 42.4 ms | 40.7 ms | 40.4 ms |
| Graph, scroll, Wasm | 10.7 ms | 9.5 ms | 7.5 ms | 7.3 ms |
| Status, full, library | | 29.5 ms (text) | 22.9 ms | 21.9 ms |
| Architecture, full, library | | 20.0 ms (text) | 15.3 ms | 14.5 ms |
| Graph, scroll, library | | 5.3 ms (text) | 3.7 ms | 3.6 ms |

Host decode of one frame, text against bytes: status 4.4 against 0.9 ms (Wasm), 3.0
against 0.9 ms (native); architecture 2.7 against 0.5 ms and 2.1 against 0.4 ms; graph
0.8 against 0.05 ms and 0.5 against 0.04 ms. The bytes host decode left is mostly
`JSON.parse` of the head (the `webRender` glyph runs and links).

The CLI writes the text answer, so its step 2 column does not change. A status frame is
about 8 ms (Wasm 11 ms) faster in the Lean call with bytes than with text, as the
library and Wasm columns show. Status frame, native samples after step 3:
`NativeSVGCurves.flatten` 12.6% (16% before step 3).

Not measured: the window host end to end (the screen was locked).
