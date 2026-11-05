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
