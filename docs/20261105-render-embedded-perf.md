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
