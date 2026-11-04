# One canonical path for HTML, SVG and real fonts

Tracking: https://github.com/danbri/factoidal/issues/1230 .

`Rendering.Path` is now the sole Point/PathSegment/Contour/LinearContour data
algebra. SVG's public path names alias those exact core types. Canonical
contours distinguish empty+closed values and retain their start, ordered
line/quadratic/cubic/arc controls, flags and closedness. FontData M/L/Q/C/Z
records construct those same canonical contours directly; there is no
font-specific curve model or early chord substitution.

The shared scene preserves every path control and Primitive.pathLength.
`WebRenderSVG.toScene` now returns `Except String NativeSVG.Scene`: checked
backend compilation must succeed before painting or serialization. Every
error propagates through the HTML/font/RDF artifact path, CPU pixel CLI and
probes. `scene_roundtrip` proves `.ok originalScene` for every admitted SVG
scene using `Scene.make_existing`, including its lowering and compiled-cache
witnesses. Geometry, segment, style, primitive, clip and tree roundtrips also
compile; only standard Lean axioms occur. This is structural/cache assurance,
not a proof of ideal curve error or GPU Float32 raster equivalence.

The shared CPU sampler keeps the root lane's proved prepared traversal over
the compiled backend cache. Canonical geometry remains available in retained
inspection. Root owns the performance proof port; its exact operation-order
and short-circuit requirements remain in force.

## Actual source checks

Targeted core renderer, font provider/face/layout/request tests pass after the
migration. Font tests now inspect retained quadratic and cubic control values.
Line leading uses actual ascent+descent, which need not equal one em; a new
non-em metric guard checks the resulting 20px line flow.

Fresh adapter compilation checks complete SVG cache roundtrips. Twelve prior
lab CPU guards pass. Six new `WebRenderCurveTests` guards sample actual HTML-
embedded Q/C fills, inspect retained Q controls, and verify a path-budget
failure stays an error. The native build script registers all these guards.
No fresh combined browser runtime is claimed at this source checkpoint.

An actual local Arial source probe consumed real HB/FT data, font SHA
`525979822591a3447cfc49d943d6f7683508e25543407871c0ed8fed05fd2bd9`.
The five word/space resources contain 272 quadratic/cubic commands. Original
HTML `Lean renders real fonts` wraps from real advances, emits 21 paint items
including an inline blue SVG circle, and produces a readable 240 by 90 CPU
image. The image was visually inspected. Evidence:
`/tmp/factoidal-web-arial-{artifact.json,pixels.json,cpu.png}`; original input
and supplied data are `/tmp/factoidal-web-arial.html` and
`/tmp/factoidal-web-arial-font-data.json`. This ran through the fresh Lean
source evaluator, not yet a newly linked standalone/WASM engine. No system
font file is copied into the repository or distributed.

The earlier five real-Ahem native/WASM and CPU/GPU comparisons remain exact
within that renderer, while all independent Chrome oracle differences remain
recorded as failures. Real-font raster equivalence, paragraph itemization,
font fallback/defaults and margin collapse are still incomplete. The SVG
curve lane also retains its known four-pixel annular-stroke numeric failure.
