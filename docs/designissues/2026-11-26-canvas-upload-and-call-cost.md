# Canvas 2D: pixel upload by rectangle, and the cost of one canvas call

Issue: https://github.com/danbri/factoidal-core/issues/1098 (canvas game at 10 fps), items 3 and 4.
Record of 2026-11-26. Measurements are from a Linux VM with 4 vCPUs, native engines built from
this repository (`build-web-render.sh --native`), best of 5 runs.

## 1. How a canvas reaches the screen

1. The page calls the 2D context. The prelude (`tools/wasmvm/quickjs/prelude.js`, section
   "Canvas 2D") appends numbers to a batch. At the end of the task it sends the batch to Lean
   with one `gpu_command` import (op 200 binary, op 203 text).
2. Lean decodes the batch (`PageCanvas/Wire.lean`) and draws each command into the canvas
   bitmap (`PageCanvas/Canvas.lean`, `Raster.lean`).
3. At the end of the turn, `Store.emit` gives host commands: a texture when the host has none
   of the canvas's size, then `pixels`.
4. `HostCmd.json` writes `pixels` as JSON: straight RGBA, run-length coded (`rleRect`), base64.
5. The host (`docs/web/hub/foafnaut/page-gpu.mjs`, on the Hub and through
   `labs/demos/foafnaut/layer_compositor.ts` in the window) decodes it (`decodePixels`) and
   calls `writeTexture`. The page-GPU blit draws the texture into the page layer.

## 2. Upload by rectangle (item 3)

- Each `Canvas` has `damage : Box`. `Canvas.onBitmapIn box f` changes the bitmap and adds
  `box` to the damage (`Box.hull`). The box is the one the draw visits: `Draw.visits` (the
  coverage box, or the whole canvas for an unbounded operator such as `copy`). A shadow, a
  full `clearRect`, `reset()` and a new bitmap use the whole canvas. `putImageData` uses its
  own rectangle.
- `emitOne` sends the damage (`Box.within` the canvas), or the whole canvas when the texture
  is new. It sends nothing when the damage is empty. `Store.sent` clears the damage.
- The JSON carries `x` and `y`. The host passes them as the `writeTexture` origin.
- `rleRect` reads the rectangle in place: one range when the rectangle has the canvas's
  width, else one range for each row (`rleRangeInto`). The first version called a closure
  for each pixel's index. It cost 16 % of a frame of 3,000 calls.
- Proofs: `emitOne_pixels` and `emit_pixels` state that every `pixels` command has the
  canvas's size and a rectangle inside the canvas. `Box.within_le` gives the bound.
- What is tested, not proved: that the damage covers every changed pixel. The Lean test
  `uploads` (`PageCanvas/Tests.lean`) replays each rectangle onto a texture and compares the
  texture with the canvas after every batch. It covers rects, fractional edges, alpha,
  stroke, partial and full `clearRect`, a path, `copy`, a shadow, `putImageData` and
  `reset`. A theorem would need `composite` to change only pixels of `Draw.visits`. That is
  a statement about `Raster.lean`, which another session changes often.

Measured (`labs/demos/foafnaut/canvas_cost_bench.ts`, one animation frame after the start):

| Case | Before (main 9fa1d855) | After |
| --- | --- | --- |
| 20x20 fillRect on 1600x1000: bytes uploaded | 6,400,000 | 1,600 |
| 20x20 fillRect on 1600x1000: wall time of the frame | 9.24 ms | 0.14 ms |

Particle Rex does not get faster from this. It paints its sky over the whole canvas in each
frame, so the damage is the whole canvas (4,096,000 bytes a frame at 1280x800). For a game
like that, the transfer itself must be cheaper: a bytes answer for script turns, so the pixels
do not go through run-length coding, base64 and JSON. That is not done.

## 3. The cost of one canvas call (item 4)

A pair of calls (`globalAlpha`, then `fillRect`) on an 800x500 canvas, per call:

| Engine | µs per call |
| --- | --- |
| main 9fa1d855 | 8.1 |
| after `typedBytes` fast form, `rleRect` and `Wire.f64` | 5.1 (4.7 after rebase on main) |

Where the time was:

1. `JS.typedBytes` had no fast form for Float32 and Float64. Each byte was
   `v / 2^(8k) % 256` on a `Nat`. For `k ≥ 4` that is big-number arithmetic (GMP). The
   prelude packs every batch with `Float64Array.set`, so this was 30 % of the turn.
   `leBytesU64` and `leBytesU32` now give the bytes from shifts. `leBytes8_eq` and
   `leBytes4_eq` prove them equal to the reference, so `typedBytes_eq_byteFast` (`@[csimp]`)
   still holds.
2. BubblePopJS call overhead, measured with plain JavaScript in the same engine:

   | Form | µs per call |
   | --- | --- |
   | plain function that pushes the numbers | 1.0 |
   | method, no checks | 1.0 to 1.1 |
   | method with `this?.[K]` and `s.kind` check | 1.8 to 2.3 |
   | method that reads `arguments.length` | 2.0 to 2.7 |

   `arguments` cost about 1.1 µs, even when the read was not run: the interpreter built the
   arguments object at entry and the function lost the plain slot frame. The prelude's
   `fillRect`, `strokeRect` and `clearRect` read `arguments.length` on each call (the
   WebIDL arity check). Repair: the resolver gives `Expr.argCount` for `arguments.length`
   in a function that uses `arguments` in no other way (`JS/Resolve.lean`, `rFun` and
   `rFunAs`). Any other use, a direct eval or a `with` resolves the function as written.
3. Lean per call: the batch decode is small (`Wire.f64` now reads eight bytes with no list).
   Most of the Lean time per call is in `composite` and the coverage of each draw
   (`Raster.lean`).

## 3a. Later steps of the same night

| Step | Change | Measured (same machine, two builds of one base) |
| --- | --- | --- |
| 068b8b4b0 | `arguments.length` with no arguments object | pairs 4.6 to 4.9 → 3.8 µs per call; game-like frame 27.7 → 19.0 ms engine time |
| 7111c6c24 | run scan two pixels per 8-byte load; prelude receiver checks with no optional chain | pairs 3.8 to 4.0 → 2.8 to 3.5 µs per call; game-like frame wall 29.7 → 24.0 ms |
| 14bc1cf1c | host `unrle` with a `DataView` and one scratch buffer | decode of a 1600x1000 frame 7 to 13 → 1.1 to 1.4 ms; rig present p50 15.5 to 16.6 → 13.6 to 13.7 ms |

Particle Rex on the rig moved from 4.4 fps (main 9fa1d855) to 7.2 to 8.6 fps, most of it from
the raster session's work on `Raster.lean`. Runs of the game differ by more than the later
steps (the game state at each press differs), so its fps is not used to judge a single step.

## 4. Defects found

- `canvas2d_reference.mjs` checked for Chrome at the Mac path when imported and called
  `process.exit(0)`. `canvas2d_test.ts` imports it, so on every machine without that file the
  test ran nothing and exited 0. Repaired. The hidden failure is
  https://github.com/danbri/factoidal-core/issues/1134 (setting `canvas.width` to its own
  value does not reset the canvas), an expected failure in the test.
- https://github.com/danbri/factoidal-core/issues/1148: `arguments` in a default parameter
  value and in a direct eval is a ReferenceError in BubblePopJS. Expected failures in
  `JS/RegressionTests.lean`.

## 5. How to measure

- `FOAFNAUT_NATIVE_ENGINE=PATH deno run --no-check -A labs/demos/foafnaut/canvas_cost_bench.ts 5`
  (from `labs/demos/foafnaut`): one JSON line per case, with frame time, µs per call, pixel
  bytes and host decode time.
- The window on the Linux rig: `tools/foafnaut-linux-rig/run.sh --html pages/particle-rex.html
  --window-size 1280x800 --steps fixtures/particle-rex-play.json --perf-summary`.
  `native-html-page-canvas` lines carry `uploadBytes` and `rects`; the summary has
  `pageCanvasPresents.uploadBytesP50`.
- Two engine builds of one base: copy `.build/web-render/engines/libweb-render.so` after each
  build and run the bench on both in one run.
