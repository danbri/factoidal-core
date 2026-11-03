# Retained linear SVG strokes — 2026-11-01

The Lean SVG lab now uses one retained stroke union for rectangles, lines, polygons, polylines and linear `M/L/H/V/Z` paths. Open stroke contours remain open even though their fills close implicitly. Explicitly closed contours join across the seam. All subpaths belong to one painted element: overlapping strips, disks and join triangles do not multiply opacity.

`SVGStroke.lean` computes directed edges, splits painted dash intervals into butt strips, places round caps at actual dash endpoints, and adds outer miter triangles with bevel fallback when the default miter limit is exceeded. Dash phase restarts on each subpath. Author `pathLength` calibration uses the sum of subpath lengths; the existing typed percentage exemption remains. Repeated zero-length edges do not manufacture directions; round-capped zero-length segments still paint a disk.

`SVG.lean` evaluates the same typed strip/disk/triangle predicates on CPU and emits them as WGSL. CPU stroke-tail indexing now skips polygon/path fill geometry before reading retained pieces, including transformed paths. The host still submits the shader and data generated together. Retained data layout has changed: do not pair this source's shader with an older engine's buffers. The outer artifact ABI label alone does not establish storage compatibility.

## Standards and scope

Sources: [SVG 2 painting: stroke shape, joins and dashing](https://www.w3.org/TR/SVG2/painting.html#StrokeShape), [SVG 2 paths: closure and distance calibration](https://www.w3.org/TR/SVG2/paths.html#PathLengthAttribute). No fixture string special cases or CSS expansion were added.

This is a bounded linear geometry slice, not full SVG stroke conformance. Curved paths remain refused; dashed circles/ellipses remain refused; square caps and explicitly selected round/bevel joins remain refused. The exposed miter setting remains default 4. Existing zero-pathLength infinite nonpercentage dash calibration refusal remains. Resource bounds are 128 contours, 512 total contour points and 4096 retained pieces, in addition to existing parser/dash limits. Float geometry and CPU/GPU rounding are not proved equivalent by this change; no new geometry correctness theorem is claimed.

## Validation

Fresh source modules checked with Lean 4.33.1 in an isolated temporary overlay. Six suites pass: SVGLinearStrokeTests, SVGDashTests, SVGPathLengthTests, SVGPathTests, SVGTransformTests and SVGPercentageTests. Controls cover open versus closed edges, default miter and acute bevel fallback, reversal, zero-length round caps, total pathLength with phase reset, one opacity application across crossing subpaths, transformed path-tail offsets and polygon/path geometry agreement. The official unchanged pathlength-001 test/reference and pathlength-004a test/reference are admitted by current source.

The parent GPU runner rendered the unchanged official `pathlength-001.svg` and `pathlength-001-ref.svg` source artifacts at 800 × 600 using Chrome 156 / Apple Metal. Input hashes were checked against the pinned fixture manifest; the original zero tolerance was retained. **The two images match exactly: zero differing pixels and channels.** Evidence: `/private/tmp/solving-linear-pathlength-pair.json` and corresponding GPU result directories. This is one same-renderer reftest result, not a full-suite score or a rebuilt WASM result. The earlier independent browser comparison still has 1512 differing antialiased edge pixels (maximum channel difference 64); matching the reference within our renderer does not erase that limitation.

Final source-artifact SHA256:

- test: `6022ac40510a2a9fa741ed7cf39b648e446970f2021b3027a6f476379844ad4b`
- reference: `62688f139ea86db3463cd50d08fad3fe4bcb0811756dbca5048b510294f5c91d`

Build ordering and link inputs include SVGStroke; shell syntax checks pass. Deno artifact tests were updated for supported linear strokes but were not run against a freshly rebuilt WASM engine. No heavy WASM rebuild, executable release or browser runtime deployment was performed.

## Endpoint rounding regression

A follow-up reproduced loss of the terminal round cap on the open contour `(0,0), (1,1), (2,2), (3,3)`: summing three `sqrt(2)` lengths and repeatedly subtracting can leave a value just larger than the final segment. The former fallback placed that cap at the contour start. Endpoint lookup now selects the actual final stroke-edge endpoint at total distance and on traversal fallthrough; degenerate contours retain their sole point. The new regression failed before the fix and passes afterward, also checking that the start cap is not duplicated. This is a concrete floating-point regression check, not a proof covering all Float geometry.


## Polygon reftest and full source admission replay

A subsequent fresh source export and GPU run also matches the unchanged
`pathlength-004a.svg` polygon test to `pathlength-004-ref.svg` exactly: zero
pixel or channel differences, retaining the upstream zero tolerance. Both ran
at 800×600 through Chrome 156 / Apple metal-3. All pinned fixture hashes passed
before comparison. Evidence: `/private/tmp/solving-pathlength-004a-pair.json`
and the corresponding `*-gpu/candidate.json` reports. Together with 001 this
is two targeted same-renderer source-artifact reftest matches, not two new
independent-browser matches or a complete binary-backed suite score.

A replay of all 38 unchanged test inputs with the current source reports
**six accepted and 32 unsupported**. Newly accepted relative to the earlier
four-case admission are pathlength-001 and pathlength-004a. The other four
are fallback-001/002 and percentage/percentage-attribute. All original runtime
requirements remain recorded. This admission result means compilation only;
it does not promote the other unsupported cases or prove visual conformance.
Report: `/private/tmp/solving-linear-admission.json`.
