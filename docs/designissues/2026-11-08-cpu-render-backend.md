# A CPU backend for the render plan

Date: 2026-11-08. Author: cpu, a subagent of session depmap-0e.
Related: https://github.com/danbri/factoidal/issues/1295 (graphics on ESP32-class
devices), issue 1268 (layers and bands), record `2026-10-30-lean-render-plan.md`.

## 0. Goal and status

Lean makes every frame of Foafnaut as data: a scene (storage floats and tile words), one
scene shader in WGSL, and a render plan (`RenderPlan.lean`). Until now only a GPU ran
them. This record adds a CPU backend that runs the same scene and gives the same pixels
with no GPU, for:

1. the Hub when WebGPU is missing (no `navigator.gpu`, or no adapter);
2. native builds without a GPU;
3. headless pixel tests;
4. later, microcontrollers such as the ESP32-P4 and ESP32-S3 (issue 1295).

What runs now (section 9 has the numbers):

- `labs/demos/foafnaut/SVGRaster.lean`: a pure Lean function scene → RGBA bytes, a
  reference form (`Scene.rasterSpec`) and a fast form (`Scene.rasterFast`), with the
  theorems of section 7.
- `SVG.lean`: `pathHitFast`, the path fill test as plain code, proved equal to the
  expression-tree test (`pathHitFast_eq`); the GPU readback probes use it too.
- The op: `cpuInfo` (a probe), and `cpu:true` on a render, which gives each scene of a
  bytes answer a `pixelsSection` (`DataForm.sectionsCpu`).
- The Hub: the worker probes `cpuInfo` once when it has no WebGPU adapter and then shows
  Lean's CPU pixels (`layers.mjs` `createCpuLayerSurface`). The hosts only copy bytes.
  With an engine without the op the Hub says, as before, "This browser does not provide
  WebGPU."
- `cpu_render_diff_check.mjs`: every demo page and SVG test file, drawn by WebGPU in
  headless Chrome and by the CPU backend, compared per pixel; in `test.sh`.
- `hub_cpu_check.mjs`: the Hub in Chrome with WebGPU switched off.
- `web-render-native --document-bin`: one packed answer to a file, and timed repeats.

## 1. What the GPU runs

One frame, from Lean to the screen:

1. `WebRender.artifactWith` turns the common scene (`Rendering.Scene`) into a
   `NativeSVG.Scene`: compiled primitives in paint order (`compilePrimitives`).
2. `Scene.data`: vec4 rows of binary floats. Row 0 is `(sx, sy, tx, ty)`, row 1
   `(minX, minY, viewportWidth, viewportHeight)`; then one record per primitive: five
   fixed rows (geometry or bounds; header `(tag, count, rule, mode)`; fill paint; stroke
   paint; stroke width, opacity, dash count, dash flag), the geometry tail (polygon points,
   or path edges as `(a, b)` pairs), dash pieces (five rows each), the inverse affine
   (two rows) when the primitive has a transform, and clip rectangles (three rows each).
3. `Scene.tiles`: tile side (32), tiles across, tiles down, start offsets, then each
   tile's list of record rows in paint order (a primitive is listed in every tile its
   conservative pixel box `Primitive.screenBox` touches), then the paint table
   (gradient records, image headers, image pixels as RGBA words).
4. `sceneShader`: one WGSL text for every scene. Binding 0 the floats, binding 1 the tile
   words.
5. The render plan (`NativeRenderPlan.commands`): `beginPass` (clear to opaque black),
   `setPipeline`, `setBindGroup`, `draw` (one full-screen triangle), `endPass`, and for
   offscreen targets `copyTextureToBuffer`, `submit`, `mapRead`, `readMapped`, `unmap`;
   for a window `submit`, `present`.
6. With layers (issue 1268) a render answers two scenes: the chrome (window rows
   `0 .. top`) and a band of the page (`FrameCost.band`: the view and up to 512 rows each
   side). `compositeShader` makes the window: row `y < top` from chrome row `y`, row
   `y ≥ top` from page row `y-top+offset`, white past the page layer, and three quarters of
   each colour inside a press rectangle (`compositePress`; the Hub draws none). A scroll
   inside the band only runs the composite again.
7. Page GPU canvases (`canvasBlitShader`) are drawn by the page's own WebGPU commands and
   blitted into the page layer.

## 2. Each plan step on the CPU

| Plan step | CPU work |
|---|---|
| `beginPass`, clear `(0,0,0,1)` | none: every pixel is written, always opaque |
| `setPipeline` | none: there is one shader, and its CPU statement is Lean code |
| `setBindGroup` (floats, tiles) | `Scene.data` and `Scene.tiles`, the same arrays; index records by row (`Raster.items`); prepare each primitive once (`Primitive.prepareSample`, `Raster.prep`) |
| `draw` (full-screen triangle) | loop over the target's rows and pixels; per pixel `adaptiveSample` of `samplePixel` |
| `endPass`, `copyTextureToBuffer`, `mapRead`, `readMapped`, `unmap` | none: the `ByteArray` is the readback, rows unpadded (no 256-byte row alignment) |
| `submit`, `present` | the host copies the bytes: `putImageData`, or a frame buffer write |
| composite | row copies: chrome rows, then page rows from `offset`, white past the layer (`layers.mjs compositeBytes`; Lean states it as `FrameCost.composite`) |
| press rectangles | `compositePress` with `pressShade` (Lean); not used on the Hub |
| page GPU canvas blit | none: a page's own WebGPU needs a GPU; its box stays as Lean drew it |

## 3. Rasterisation rules

These are the rules of `sceneShader`, which the CPU follows exactly. All of them were
already stated in Lean for the GPU readback probes (`Scene.checks`); this backend runs
them for every pixel.

- **Samples.** A pixel has a 16 × 16 grid of cells; a sample is at a cell centre, at
  `(2c+1)/32` from the pixel's origin, one in each row and column of the grid
  (`pixelSampleCells`). The GPU adds `offset-0.5` to the fragment centre; the CPU adds
  `offset` to the pixel origin; `pixelSample_cpu_gpu_coordinate_agreement` proves these
  are the same points. Both are exact dyadic numbers in binary32 and binary64.
- **Four or sixteen.** The first four samples are taken; if two of them differ by more
  than `1/64` in a channel and the scene has at most 65536 rows, the other twelve are
  taken too. The pixel is the mean.
- **One sample.** Past the viewport's right or bottom edge it is white. Otherwise the page
  point is `(p-(tx,ty))/(sx,sy)+(minX,minY)`, the tile is that of the pixel (every sample
  of pixel `(x,y)` truncates to `(x,y)`), and each record of the tile's list is applied in
  order to an opaque accumulator that starts white:
  - its local point, through the inverse affine when it has a transform;
  - its clips: every clip rectangle must hold the point;
  - fill coverage: rectangle, circle, ellipse; polygon and path by winding number
    (non-zero or even-odd) over their edges, after a bounds test;
  - stroke coverage: rectangle ring, circle annulus, line (butt, or capsule for round
    caps), and dashes as pieces (strips, disks, triangles);
  - paint: a solid row; a gradient record (linear or radial, stop search, mix, then
    premultiply); an image record (bilinear on premultiplied texels, edge texels past the
    edge, then un-premultiplied);
  - the element: stroke over fill, premultiplied, times the element's opacity, over the
    accumulator.
- **Anti-aliasing** is these point samples. There is no analytic area coverage on either
  side.
- **Alpha.** Fill and stroke are composed premultiplied; the accumulator is opaque, so the
  output alpha is 1 (255).
- **Gamma.** None on either side: the scene shader works on the sRGB-encoded values, and
  the target is `rgba8unorm` (not `-srgb`), so the GPU stores them as they are. The CPU
  does the same.
- **Store.** Each channel is clamped to `[0,1]`, times 255, rounded to the nearest
  integer (`Raster.channel`).

## 4. Tolerance

The CPU runs binary64 on `Scene.data` and the Lean primitives; the GPU runs binary32 on
the same floats rounded to binary32, and WGSL lets `/` and `sqrt` be off by 2.5 ULP.
So:

- A sample within a rounding step of an edge can fall on different sides. The pixel then
  differs by one sample's share of the edge contrast (1/4 or 1/16), and if the flip
  changes the four-sample spread test, by the difference between the four- and the
  sixteen-sample mean.
- A channel whose exact value lies on `n+0.5` after `×255` can round either way: 1.
- Gradients and bilinear image samples interpolate in binary32 on the GPU: usually 1.

The differential test (section 8) counts, for each scene, the pixels whose largest
channel difference is above 8 (a third of a 1/16 share of black on white is 5; a 1/4 share
is 64), and passes a scene when they are at most 0.2% of its pixels. It also reports the
largest and mean differences and a histogram, so that a change that moves many pixels
by 1 or 2 shows up.

A binary32 CPU form (Lean `Float32`) would come closer but still not equal: GPU
arithmetic is not IEEE-exact in WGSL. It matters more for microcontrollers (section 10).

## 5. Data layout and the fast form

The CPU reads the same two arrays the GPU binds. `Scene.data` is an `Array Float` (boxed
binary64), `Scene.tiles` an `Array Nat`; the records are the Lean primitives that wrote
those rows, so the CPU reads geometry from the floats (paths, rectangles) and paints from
the Lean records (`GradientRecord.colorAt`, `ImageRecord.colorAt`), as `Scene.checks`
does.

`Scene.rasterFast` does the reference's work in this order:

1. Each record is prepared once (`Primitive.prepareSample`): its inverse transform, its
   conditions with their data folded in, clips as a plain loop (`clipPass`), a constant
   paint row made once (`constantPaint`).
2. Each record gets its conservative pixel box (`Primitive.screenBox`, the box the tile
   lists come from).
3. For each pixel row: the records of that row of tiles whose box meets the row, each
   made ready for the row once however many tiles list it (`rowPrep`). A path fill learns,
   for each of the row's sixteen sample lines, the edges that cross the line
   (`pathSpansAt`); at a sample on one of those lines (its local `y` equal) only those
   edges are tested (`pathHitSpans`), elsewhere all are.
4. For each pixel: `adaptiveSampleAt` with the pixel's coordinates converted once; each
   sample folds the records whose box meets the pixel's column; a record that covers no
   sample is skipped (its step would add 0 and keep the colour).
5. A dashed stroke (`prepareCoverageCulled`) tests a piece only when the point is in the
   piece's box (`pieceBox`). A stroked path is drawn as dash pieces (strips, disks,
   triangles), up to a few hundred for one ellipse, so this decides SVG-heavy pages.

Steps 1 and 4's coordinate conversion are proved (section 7). Steps 2, 3's span lists, 4's
skip and 5 rest on facts about IEEE arithmetic and geometry that Lean's opaque `Float`
cannot state (a step with no coverage is the identity; a point outside a conservative box
is not covered; equal `Float`s compare alike). The `#guard`s in `SVGRaster.lean` check
`rasterFast` against `rasterSpec` byte for byte on a scene with every kind of record, and
the differential test checks the result against the GPU on every demo page.

The output is one `ByteArray` of `width × rows × 4`, made with its full capacity and
pushed in order by a tail-recursive loop that alone holds it, so each push is in place
(no copy on write).

## 6. The op and the hosts

- `{"op":"cpuInfo"}` answers `{"engine":"cpu","pixels":"rgba8","ops":["render","chromeLayer"]}`.
  An older engine answers "unknown document operation".
- `cpu:true` on `render` (with or without `layers`, `printPage`) and on `chromeLayer`, on
  the bytes call (`web_document_call_bin`): each scene of the answer has
  `"pixelsSection":k+2` after its `dataSection` and `tilesSection`, and the section holds
  `width × height × 4` bytes, RGBA, row by row (`DataForm.sectionsCpu`). The text call
  ignores it.
- The Hub worker asks for a GPU adapter while the engine loads. With none, it asks
  `cpuInfo` once. If the engine answers, every render carries `cpu:true` and the layer
  surface is `createCpuLayerSurface`: `drawLayers` keeps the two layers' bytes, `composite`
  copies rows, `drawSingle` copies a frame; frames go to the page as RGBA and the page
  paints them with `putImageData`, as the `?check=1` readback path does. Printing uses the
  pixels of the print frames. If the engine does not answer, the worker stops with "This
  browser does not provide WebGPU." as before. There is no JavaScript renderer and no older
  engine path.
- Native: the same Lean code is in `web-render-native` and `libweb-render.dylib`.

## 7. Theorems

In `SVGRaster.lean`:

- `foldPrepared_eq`, `samplePrepared_eq`: folding the prepared records over a sample
  gives the reference sample.
- `rasterPrepared_eq`: each pixel of the prepared form is the reference pixel.

In `SVG.lean` and `GraphicsPrepared.lean` (each a refinement of the code the GPU probes
already ran, and `@[csimp]` where the compiler should use the fast form everywhere):

- `pathWindingFrom_eq`, `pathHitFast_eq`: the path fill test as a loop of plain Float
  code is `pathHit`, the expression-tree winding test (`edgeUp_eq`, `edgeDown_eq` by
  `rfl`: the same operations in the same order).
- `polygonWindingFrom_eq`, `windingHitFast_eq`: the same for polygons (`windingHit`).
- `Primitive.prepareLocal_correct`, `Primitive.prepareCoverage_correct`: the prepared
  coverage, now with clips (`clipped`) and dashes (`local`) prepared too, is
  `Primitive.coverageAt`; `Primitive.prepareSample_correct` follows.
- `Expr.eval_eq_evalFast` (`@[csimp]`): literals come from `literalFloat`, not a bignum
  conversion at each evaluation.
- `Transform.apply_eq_fast` (`@[csimp]`, by `rfl`): the affine map written out, not
  through the scalar-operations record.

`#print axioms` for every one of them: `[propext, Classical.choice, Quot.sound]`; no
`sorry`, no `native_decide`, no `bv_decide`.

## 8. Differential test

`cpu_render_diff_check.mjs` (run by `test.sh`): for each `pages/*.html` at 800 × 600
with Noto Sans and text zoom 150, and each SVG file of the svg-wpt `shapes`,
`pservers/reftests` and `painting/reftests` folders, the native engine answers the scene
and its CPU pixels; headless Chrome (`--enable-unsafe-webgpu`) draws the scene with the Hub's
`layers.mjs` (`drawSingle`, readback), and the page compares.

Results: section 9.

## 9. Results

Measured 2026-11-08 on an Apple M1 (macOS), headless Chrome with WebGPU on Metal.

**Differential test** (`cpu_render_diff_check.mjs`, 800 × 600): 149 scenes, all pass.

| Set | Scenes | Pixels | Pixels that differ | Over 8 | Largest |
|---|---|---|---|---|---|
| Demo pages (`pages/*.html`) | 28 | 13,440,000 | 125,423 (0.93%) | 33 | 28 |
| svg-wpt shapes, pservers, painting reftests | 121 (79 drawn) | 58,080,000 | 1,599 | 1 | 32 |

Nearly every differing pixel differs by 1 in one channel (the histogram bucket for 1 holds
all but 37 of them): a channel whose exact value is near `n+0.5` after `×255`, or a
gradient interpolated in binary32. The pixels over the tolerance are edge pixels where
one sample fell on the other side of a glyph or shape edge (differences of 13 to 32, one
sixteenth to one quarter of the edge contrast). The worst page has 6 such pixels of
480,000. Five SVG files are refused by the engine before any drawing (an external paint
URL, `paint-order`); 42 draw nothing (scripted tests).

**Frame time** (`cpu_render_bench.mjs`, 800 × 600 window, text zoom 150, Noto Sans; the
median of three; "Lean" is the render a GPU host asks for, "CPU draw" is the extra time of
`cpu:true`):

| Page | Form | Lean, native | CPU draw, native | Lean, Wasm (Node) | CPU draw, Wasm |
|---|---|---|---|---|---|
| index.html | frame (600 rows) | 7 ms | 861 ms | 15 ms | 1364 ms |
| index.html | band (chrome + 1,624 rows) | 9 ms | 2295 ms | 16 ms | 3686 ms |
| status.html (long text) | frame | 12 ms | 1036 ms | 19 ms | 1623 ms |
| status.html | band | 22 ms | 2435 ms | 40 ms | 3897 ms |
| svg-gallery.html (SVG) | frame | 0.6 ms | 2223 ms | 0.7 ms | 3823 ms |
| svg-gallery.html | band | 1.6 ms | 2518 ms | 5 ms | 4767 ms |

The GPU draws the same scenes in 8 to 270 ms from a cold pipeline in headless Chrome
(the `gpuMs` of the differential test, which includes the readback) and in a few
milliseconds warm. So the CPU backend is a correct fallback, not yet a fast one: about
1.8 µs a pixel natively for the text pages and 4.6 µs for the SVG page, and 1.6 to 1.7
times that in Wasm. A scroll inside a band is a row copy (0 to 1 ms in the Hub, no Lean call), so the
cost is paid once a band. The steps in section 5 took the SVG page from 20.7 s to 2.2 s
and the text pages from 1.7 s to 0.86 s.

**Hub** (`hub_cpu_check.mjs`, Chrome with `--disable-blink-features=WebGPU`, this
change's Wasm engine): `status.html` shows; every frame has `stats.cpu`; the first frame
takes 2.4 s; six scrolls inside the band are row copies of 0 to 1 ms with no Lean render;
the frame differs from the same page in a Chrome with WebGPU in 880 pixels of 480,000, 2
of them by more than 8. With the published engine (no `cpuInfo`) the page says "This
browser does not provide WebGPU." as before.

## 10. Microcontrollers

The Lean code compiles to C, so the same functions run on a microcontroller once the Lean
runtime does (allocation and reference counts; issue 1295). The parts that change:

- **Precision.** The ESP32-P4 and ESP32-S3 have single-precision FPUs; binary64 is
  software there. The MCU form should read the binary32 words the GPU reads
  (`Scene.float32Bytes`, `Scene.tiles` as words) with `Float32`, which is also nearer the
  GPU. Edge tests could use fixed point (16.16) with the same sample lattice.
- **Memory.** `Array Float` boxes each float (24 bytes); the MCU form reads `ByteArray`
  words in place. A tile of 32 × 32 RGB565 pixels is 2 KiB; the P4's 768 KiB of internal
  SRAM holds a tile row of a 1024-pixel-wide target several times over, and the band and
  frame buffer live in PSRAM.
- **Tiles and DMA.** Draw one tile into SRAM, then move it to the PSRAM frame or band with
  the P4's 2D-DMA (a rectangular copy with source and destination strides), while the next
  tile is drawn. An empty tile list is a white tile: a PPA fill, no sampling.
- **Composite with the PPA.** The window from the chrome and the band is two rectangular
  copies (2D-DMA, or the PPA's SRM with no scaling); a scroll inside the band moves only
  the source offset, as on the GPU. A press rectangle is a PPA blend of black at 25%
  (`pressShade` 0.75). Colour conversion to the panel's RGB565 is the PPA's too.
- **Images.** JPEG decodes with the P4's JPEG codec into the image table.
- **ESP32-S3.** No PPA and no 2D-DMA engine: tiles go by GDMA to the RGB/i80 LCD
  interface; the PIE vector instructions can run four edge tests at once; 8 MiB of PSRAM
  bounds the band.

## 11. What is left

- **Speed.** Per sample the fast form still allocates (Lean `Float` pairs, colour
  records, closures over `List Float` paint rows): the profile is mostly allocation.
  Next: an unboxed form that reads the binary32 words (`Scene.float32Bytes`, the tile
  words) into `FloatArray`s and keeps the colour in scalars; a tile whose list is empty
  filled white without sampling; the first four samples shared between a pixel and the
  next when no record's box changes; and drawing the view's rows of a band first, the
  margins after.
- **Proofs.** The culling steps of section 5 are tested, not proved. A form over
  binary32 words with `Float32` would let a statement name the exact operations; the
  IEEE facts would still be assumptions.
- **Native window.** `native_window.m` has no path that shows RGBA bytes in the window;
  the native CPU path is the library and `web-render-native` (headless). A window blit
  (`CGImage` from the bytes, as `ng_print` does for pages) is the next native step.
- **Page GPU canvases** stay blank with no GPU.
- **Press rectangles** are not drawn on the CPU Hub (none are on the GPU Hub either);
  `compositePress` in Lean is ready for a host that wants them.
- **Microcontrollers** (section 10): the binary32 form, the Lean runtime on the P4, and
  the PPA and 2D-DMA bindings.
