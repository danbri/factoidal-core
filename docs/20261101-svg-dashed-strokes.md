# Retained dashed SVG strokes

Source: SVGDash.lean and SVG.lean in labs/demos/foafnaut. The scope is rect and
line strokes, including viewport-relative dash lengths and offsets, existing
butt/round caps and rectangle miter joins. Square caps, rounded rectangles,
curved/path/polygon strokes, variable join styles and pathLength calibration
remain unsupported. No extra CSS support was added.

[SVG 2 stroke dashing](https://www.w3.org/TR/SVG2/painting.html#StrokeDashing)
defines repeating dash/gap arrays, odd-list duplication, zero-total solid strokes
and signed offset behavior. SVGDash normalizes these and retains painted
arc-length intervals. Rectangles use one continuous clockwise perimeter from
the top-left corner. Intervals split into butt-ended strips, outer miter corner
quadrants and round endpoint disks. A dash crossing the closed seam joins there;
endpoints that terminate at a corner do not gain a join.

The pieces belong to one primitive. The same typed strip/disk/box expressions
are interpreted by Lean on the CPU and lowered to WGSL, where their boolean union
is evaluated before stroke/fill compositing. Overlapping caps do not apply stroke
or element opacity twice. Child affine transforms apply to the complete region.

Bounds: at most 64 input dash lengths (odd lists duplicate), 8192 interval steps
and 4096 retained pieces per primitive, within the existing whole-artifact storage
bound. Negative/nonfinite lengths, nonfinite totals including after duplication,
and offset/period magnitudes above 10^12 refuse explicitly. Float phase and
geometry are not a real-number theorem; tiny periods/large offsets can therefore
be outside the admitted numeric profile.

The JSON envelope remains lean-svg-v1 because the host passes paired shader and
storage bytes without interpreting primitive rows. The internal storage layout
has changed: row4.z is piece count, row4.w indicates an active dash union; each
piece adds five rows before any inverse-transform rows. Never mix an old shader
with new data or vice versa. A rebuilt engine and its source/provenance inventory
must be packaged together. Existing buffers are not a separately stable ABI.

## Validation before antialiasing follow-up

Fresh source checks passed SVGDashTests, SVGPercentageTests,
SVGCSSIntegrationTests, SVGTransformTests and SVGPathTests using existing lab
checked dependencies and isolated temporary oleans. Dash controls include odd
and zero patterns, signed phase, overflow/precision refusal, rectangle crossing
and seam joins, zero-length round dashes/lines, gap pixels, and overlapping-cap
opacity. The public artifact regression removes the obsolete dash refusal and
adds actual compile/sample checks; it requires a rebuilt WASM to run.

All 38 selected WPT SVG inputs were replayed unchanged at revision
70dae60789ef6220d9b4e60c92c5b2107b4e2b93: **4 admitted, 34 refused**. The new
admissions are percentage.svg and percentage-attribute.svg. This is not four
visual passes. Both CSS fixture tests now require admission instead of asserting
the former dashed-stroke failure.

The coordinator rendered both source-exported artifacts on the real GPU at their
intrinsic 310x170 viewport, white-padding to the independent 800x600 screenshot
without rescaling. Each exact comparison **failed: 533 different pixels, maximum
channel difference 191**. Every difference is edge coverage: 531 blue candidate
pixels correspond to oracle (128,128,255), and two correspond to (191,191,255).
There were no other mismatch pairs in that comparison. Reports are
/private/tmp/solving-percentage-gpu and
/private/tmp/solving-percentage-attribute-gpu. This supports aligned interior
geometry, but is not an antialiasing pass. The coordinator's subsequent shared
CPU/WGSL coverage work is a separate change and must be measured again.

Source artifacts: /private/tmp/solving-percentage.json and
/private/tmp/solving-percentage-attribute.json (800x600 forced viewport), plus
/private/tmp/solving-percentage-intrinsic.json (310x170). Output dimensions must
not be confused with the containing page's screenshot dimensions. Fixtures and
oracles were not modified. No heavy WASM rebuild was performed in this step.

## Follow-up: shared coverage sampling

The coordinator added one four-point unit-pixel sample list in Graphics.lean,
used by both CPU sampling and generated WGSL. Each sample composites the whole
scene before averaging; overlap is not approximated by independently reducing
primitive opacity. The sample count has a kernel-checked length theorem. This
is not a proof of analytic coverage or CPU/GPU numeric equivalence.

Fresh source-generated310x170 artifacts for both unchanged percentage fixtures
were rendered through Chrome156 on Apple metal-3, then placed without scaling
on the800x600 screenshot canvas. Comparison with the hash-verified independent
browser references now gives ZERO differing pixels and ZERO channel difference
for each. Evidence: /private/tmp/solving-percentage-aa-gpu and
/private/tmp/solving-percentage-attribute-aa-gpu (candidate/comparison.json).
The earlier533pixel mismatches remain the before-change evidence above.

Dash, percentage, CSS integration, affine and linear-path source regression
suites pass after the coverage change. These two exact visual matches are
source-artifact diagnostics, not a fresh full38-case run or rebuilt WASM claim.
Four samples do not guarantee exact results for arbitrary curves/transforms;
performance and broader antialiasing quality remain open obligations.

## Finite performance comparison

Same Chrome156/Apple metal-3 host, percentage.svg310x170 intrinsic viewport,
20 resident frames per artifact, measured sequentially. Before four-sample
coverage, median frame plus readback0.60ms (first3.10ms); after1.40ms
(first3.90ms). Excluding the first frame gives the same medians. Both use one
pipeline, one upload, two buffers, one texture and20 submissions. This is a
small-scene host round-trip comparison, not GPU-only timing, throughput at
other scene sizes or a general frame-rate guarantee. Four samples increase
work; future culling/coverage optimizations must preserve the image result.
Evidence: /private/tmp/solving-percentage-before-perf/candidate.json and
/private/tmp/solving-percentage-aa-perf/candidate.json.

## Full admission replay and earlier-case regression

The current source admission replay checks all38 unchanged cases with75/75
fixture hashes/sizes verified:4accepted,34unsupported. Nine cases have original
runtime/resource requirements and are all unsupported; the remaining29 have
4accepted and25unsupported. This is not a rebuilt-artifact suite score.

Both previous fallback001/002 cases were regenerated with the new coverage
rule and an explicit800x600 host viewport (their roots omit dimensions).
GPU results each exactly match the independently captured reference: zero
pixel/channel differences. Together with the two percentage cases, four
individual source-artifact visual comparisons now match. The first intrinsic
attempt correctly refused omitted root dimensions; the hosted replay supplies
the required context rather than inventing intrinsic dimensions.

The16 first-error link failures in the admission report are rel=author,
not stylesheet links as an earlier note suggested. Added author to the inert
metadata allowlist with a regression check; stylesheet rejection remains.
This removes a metadata blocker, not a rendering feature or visual pass.
