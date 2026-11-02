# SVG document input in the Foafnaut lab

The native SVG screenshot tool parses a real XML document with this checkout's
Factoidal `XML.NamespaceView`, then builds a Float scene and WGSL in Lean. The
host only reads UTF-8 files, loads WASM, transfers GPU buffers, checks readback,
and saves/opens an image. It uses no browser or external SVG renderer. This is
a painted-primitives experiment, not SVG Tiny/full SVG conformance.

From an extracted release directory:

```sh
./native-webgpu-svg-darwin-arm64 svg-fixtures/gallery.svg render-svg.ppm
./native-webgpu-svg-darwin-arm64 INPUT.svg OUTPUT.ppm --no-open
./native-webgpu-svg-darwin-arm64 INPUT.svg --width 800 --height 600 --emit-artifact scene.json
```

`SVG Demo.command` runs the locally authored gallery. Successful screenshots
open with `/usr/bin/open` unless `--no-open` is present. `--emit-artifact` writes
Lean geometry/WGSL/reference samples and exits before requesting a GPU. No
adapter means exit 2 with no image, never a CPU image substituted for a GPU result.

## Dashed strokes

Rectangles, lines, polygons, polylines and linear paths now support bounded dash
arrays and signed offsets, including percentage lengths, odd-list repetition
and zero-sum solid strokes. Dash pieces share one element opacity calculation.
Curved path strokes and dashed ellipses remain unsupported. Source tests and
unchanged WPT cases have targeted GPU comparisons; see the coverage report for
which renderer/artifact each result covers.

## CSS subset

Type-selector stylesheets and inline declarations now use a bounded Lean CSS
reader. Presentation attributes have lower priority than matched author rules;
inline declarations win, and later equal-priority declarations win. Inherited
paint values still flow through groups. Only absent/empty/all media and
absent/empty/text/css type are admitted. Unsupported selectors, properties,
!important and invalid declarations explicitly refuse the document; normal
CSS error recovery remains unimplemented. This is not full CSS conformance.

## Supported subset

SVG-namespace `svg`/`g`, sharp `rect`, `circle`, filled `ellipse`, butt- or
round-cap stroked `line`, filled and stroked `polygon`/`polyline`, and filled
and stroked linear/compound `path` are supported, plus text-only
`title`/`desc` metadata. Stroked contours support bounded dash arrays and
offsets, butt/round caps, and default miter joins with bevel fallback. SVG
`metadata` subtrees are non-rendering; XHTML `link rel="match"` and
`link rel="help"` are recognized as reftest metadata. Other HTML links
(including stylesheets) remain explicit refusals.
Namespace prefixes resolve by expanded name; lookalike namespaces, unbound
prefixes, duplicate expanded attributes and foreign elements/qualified attributes
are refused. Geometry accepts signed fractional decimal/exponent numbers and
unitless/px lengths and viewport-relative percentages for shape coordinates,
dimensions, radii and stroke width. Horizontal/vertical lengths use the respective
viewport axis; circle radius and stroke width use the normalized diagonal.
With a viewBox, its dimensions supply these bases. Rect/circle/ellipse zero size disables painting; negative
sizes are errors. Ellipses require explicit numeric rx/ry and have no stroke.

Default paint is black fill and no stroke. Fill/stroke/color/width, fill/stroke
opacity and fill-rule inherit through groups. `currentColor` stays symbolic
until the leaf resolves its own color; a child's color override therefore works
under an inherited currentColor fill. `inherit`, `none`, 3/6-digit hex colors,
comma-separated `rgb()` numeric/percentage triples, the 16 HTML4 color names and
orange are supported. Paint channels/opacities clamp to their ranges.

Rectangles/circles support centered strokes; rectangles use sharp miter corners.
Lines default to butt caps and support inherited round caps. Round caps use a
capsule, including a disk for zero-length lines; zero-length butt lines and
zero stroke width paint nothing. Polygon fill implements nonzero and evenodd
winding for 3–64 vertices. Shared stroke construction handles open/closed
polygon, polyline and linear-path contours, including total `pathLength` dash
calibration. Ellipse strokes and curved path commands remain unsupported.
Non-inherited leaf opacity is applied once after premultiplied fill/stroke
composition, including overlap.
Group/root opacity is refused rather than approximated per descendant.

Root viewBox mapping follows default xMidYMid meet, all nine alignments, slice,
and none. Positive unitless/px root width/height are required unless both output
viewport dimensions are supplied; source dimensions are still validated. Root
percentage dimensions require that explicit host viewport. The supplied output
size overrides root dimensions; this is an embedding contract, not CSS sizing. A
fractional SVG viewport stays Float for mapping/clipping while the backing image
size is its ceiling. Subpixel edges use a shared 2×2 sampling approximation on
CPU and GPU, not analytic area coverage. `Graphics.lean` defines its four
sample coordinates as exact quarter-pixel integers; Lean proves the sample
count, strict interior bounds and center symmetry before deriving the Float
offsets consumed by both the CPU sampler and WGSL generator. This proves a
shared sample schedule, and `pixelSample_cpu_gpu_coordinate_agreement` proves
that pixel-origin plus offset and fragment-center plus relative offset identify
the same exact quarter-pixel locations. Neither theorem proves equal
Float/Float32 shader/CPU arithmetic or a raster error bound.
The transparent SVG canvas is composited over a documented white backdrop for
opaque RGB PPM output.

These choices refer to W3C [painting](https://www.w3.org/TR/SVG11/painting.html)
and [viewport transformation](https://www.w3.org/TR/SVG2/coords.html#ComputingAViewportsTransform),
without claiming all their semantics or other SVG features are implemented.

## Explicit refusals and limits

CSS class/id selectors and broader CSS cascade, root transforms, curved path
commands and their strokes, text/fonts, nested viewports, images, use/links,
scripting, animation, defs/gradients/patterns, filters, masks,
clips, markers, rounded rects, conditional processing,
paint-order changes, group opacity, square caps, custom joins/miterlimits,
ellipse strokes, font-relative/other non-px lengths, and unknown colors are
errors.
Unsupported features are not silently dropped, even on a zero-size primitive.
IDs and version labels 1.1/2.0 are recognized metadata, not schema validation.
Only unresolved simple local paint-fragment fallback is currently implemented. Full SVG remains open work.

### `display` and `visibility` subset

The parser supports SVG 2 `display="none"` by omitting that element and its
subtree from the retained paint scene. It still parses and validates the
subtree before omitting it, so unsupported markup does not become silently
accepted just because it is hidden. Other `display` values use the ordinary
paint path in this restricted profile; this is not full CSS `display`
validation. `visibility="visible"`, `hidden`, and `collapse` are inherited.
Hidden/collapsed paint records remain in the retained scene but lower with zero
effective opacity; a descendant can set `visibility="visible"` again.

This graphics picker is geometric, not a browser DOM event target. It does not
implement `pointer-events` or claim SVG event-dispatch behavior. See the SVG 2
[rendering model](https://www.w3.org/TR/SVG2/render.html) for full browser
semantics.

DOCTYPE/DTD, processing instructions and non-UTF-8 encoding declarations are
refused. Host UTF-8 decoding is strict. Profile limits: 1,048,576 characters (host
file cap 4,194,304 UTF-8 bytes), 12,288 painted primitives, 32 SVG group levels,
262,144 Float values (1,048,576 bytes), numeric token length 48, 24 mantissa digits, exponent magnitude
12, and numeric magnitude 1,000,000. SVG depth/count checks occur after XML
parsing; they do not provide a pre-parse DOM-depth guarantee. The reused XML
parser retains its existing behavior/limits. Initial parsing happens twice to
inspect metadata and obtain the checked namespace view.

SVG parameter data uses a read-only storage buffer, with a compact data-driven
WGSL loop rather than shader code expanded for every primitive. Lean's render
plan checks the actual device storage-binding and buffer-size limits before
allocation; over-budget documents are refused without truncation. Small UI
scenes retain their existing uniform-buffer path. The generated default
8-person FOAF scene measures 47,845 characters, 292 SVG primitives and 39,452
Float values; a dense 16-person/48-link scene measures 154,860 characters,
716 primitives and 133,208 Float values. The current counts include retained
linear-stroke geometry; the previous 32,792/114,728 totals predate that storage
tail. Both remain below the 262,144-float cap. Before compound glyph paths the
scenes were 128,347/1,880/37,608 and 455,470/6,748/134,968 respectively. These
measurements motivate the bounded profile, not a frame-rate guarantee.

Geometry has hard boundaries without antialiasing. CPU reference Float and GPU
f32 may differ at boundaries; readback comparisons allow one channel value of
rounding tolerance. Typed expressions and shared predicates are useful checks,
not proofs of WGSL validity, compiler correctness, CPU/GPU equivalence, or SVG
conformance. Errors are surfaced instead of silently ignoring mismatched pixels.

## Build and validation

Use the shared lab `build-engines.sh`, `test.sh`, and `build-executables.sh` from
[README.md](README.md). The SVG module compiles current XML.Document, Parser,
Wellformedness, Namespaces and NamespaceView sources into an ignored shadow
closure. It does not link old XML objects from an unrelated checkout. Cached
pinned Init/Std/runtime objects are shared; source hashes/tool versions travel
with the release. No binaries, generated C/WASM/glue/JSON or caches are committed.

Seventeen local SVG regression groups cover namespace semantics, XML character
references, symbolic paint inheritance/defaults, fractional data, viewport
mapping, butt/round/zero strokes, opacity overlap, polygon winding, zero/negative
geometry, tiny viewports, explicit refusal paths and GPU transport encodings.
The WASM tests exercise the actual Lean engine and host transport, without
executing a GPU. Native capacity tests also accepted both complete generated
FOAF scenes and compared eight CPU reference samples per scene; serializer
and render-plan tests cover explicit capacity refusals. The storage-path
change passed named native Lean tests and Deno typechecking; fresh WASM test
execution and actual GPU validation are separate checks, not implied by those
results. CPU sample agreement does not prove all-pixel, floating-point boundary,
or GPU equivalence.

Official SVG inputs are managed separately in the [external SVG suite](../../../tests/external/svg/README.md).
Accepted/refused input audits are not raster results. Test/reference relations
rendered by this same implementation may share bugs, so those comparisons alone
are not an independent conformance proof. The local
gallery and regression tests are not official suite cases. Parser/CPU success
and emitted artifacts must never be reported as a successful GPU render.


Missing local paint-server fragments now use the specified color/none fallback;
without a fallback they paint nothing. `currentColor` fallbacks remain symbolic
until the leaf's color resolves. This is limited to simple ASCII fragment IDs:
percent-escaped, escaped CSS, external URLs and existing paint-server targets
remain explicit refusals. No gradients/patterns are implemented by this change.
Identifier traversal is iterative and refuses nesting beyond 32 after XML parse;
the existing 1 MiB character and primitive/float budgets are unchanged.

The unchanged WPT `fallback-001.svg` and `fallback-002.svg` now compile and pass
known green/white CPU sample regressions. This is compiler/CPU evidence, not a
visual pass. See the [independent-image runner](../../../tests/external/svg/README.md)
for the complete 38-case denominator, installed-browser oracle measurements and
GPU result boundaries. Curved path commands and their strokes remain
unsupported; linear paths and affine transforms are described below.


## Shared affine transforms and actual GPU evidence

`Math/Affine.lean` provides typed six-coefficient affine values with explicit
scalar operations. SVG uses its Float specialization for composition, inverse
and point mapping; exact tests reuse existing MathML rational and TOAN matrix
operations. A `Float32` scalar backend now supplies the same affine operations
at WGSL's binary32 width, including a proved rejection of determinants equal to
zero. It is a Lean reference backend; SVG does not yet use it, and this does
not prove equivalence to WGSL evaluation. The generic
`Affine2.packed_applyPoint` theorem has no axiom dependencies and applies to
binary32, binary64 and exact scalar operations. It proves that packed Lean
evaluation preserves the scalar reference's operation order, not GPU arithmetic.
Matrix/translate/scale/rotate
(including a center)/skewX/skewY lists
work on groups and painted primitives, with column-vector composition in SVG
order. Both CPU hit predicates and generated WGSL evaluate the local shape using
the inverse composed transform, including local stroke geometry under shear and
nonuniform scale. Singular matrices have effective opacity zero; their identity
inverse fallback cannot paint. Point/direction/normal and corner helpers are
shared algebra APIs, not a new arbitrary-SVG UI policy or picking controller.

Transform lists have at most 32 functions, existing numeric bounds still apply,
and composed/inverse coefficients are finite and bounded by 1e9. Ill-conditioned
input can be refused; these bounds are not a numerical stability theorem. Root
transform, CSS transform-origin/transform-box and nested viewport interactions
remain unsupported. Identity records keep the previous 20-float primitive layout;
other records append eight inverse floats. Existing storage/primitive/input
budgets remain unchanged. Data serialization reuses the existing TDB2 shortest
Float formatter so small inverse coefficients survive JSON transport.

The shared `AffineRows.toVec4Rows` representation names the two four-lane
groups that WGSL indexes. `toVec4Rows_flatten` proves that flattening those
groups reproduces the canonical eight-scalar payload, and the SVG producer
uses that flattening for inverse transforms. This checks the Lean-side lane
ordering; it does not prove host byte encoding, GPU `f32` equivalence, or a
GPU speedup.

`Primitive.fixedRows_length` proves that the bounds, header and paint/style
prefix is exactly five vec4 rows. The affine tail row count comes from the
shared `AffineRows.vec4RowCount`, whose theorem establishes two four-lane rows.
`geometryTailData_length` proves that polygon point pairs (including odd-point
padding) and retained path edges occupy the row count used by the shader's
tail calculation. `Geometry.recordTagCount` now supplies the tag/count pair in
the fixed header, and `Geometry.shaderTailRowsFromHeader_eq_tailRows` proves
that the shader's path-versus-polygon row formula agrees with the Lean geometry
tail count. This is a Nat-level relationship; exact `Float.ofNat` to WGSL
`u32` conversion and the host upload remain outside the theorem.
Dashed-stroke records now have a shared `dashPieceRowCount` used by the Lean
layout theorem and WGSL offset generation. Kernel-checked theorems establish that
each encoded dash piece occupies five vec4 rows and that concatenating pieces
has exactly the row-stride length the shader loop advances over. This closes
the Lean-side variable-record stride gap; it does not yet verify the host's
Float32 upload or the shader's field interpretation. The new Lean theorems
compile with only Lean's standard `propext`, `Classical.choice` and `Quot.sound`
axioms in their dependency sets.

`Primitive.rows_length` proves that the entire flattened primitive buffer is
four scalars per `Primitive.rowCount`; `Primitive.shaderRowAdvance_eq_rowCount`
equates this to the Lean-level cursor calculation. The header-mode proofs tie
its low bit to round-cap selection and its high bit to transform presence. The
WGSL generator still emits a string, so we have not proved that WGSL parses the
same way or that its `Float`-to-`u32` casts preserve these fields.

`Primitive.rows_length` proves the complete flattened record has exactly four
scalars per `Primitive.rowCount`, and
`Primitive.shaderRowAdvance_eq_rowCount` proves the Nat-level cursor formula
agrees with that count. `headerModeCode_roundCap` and
`headerModeCode_hasTransform` prove the low and high mode bits mean round cap
and transform-present respectively. The generated WGSL remains text, so these
theorems do not certify that text's parsing or the `Float`-to-`u32` header cast.
The CPU reference sampler builds the packed array once for all antialias samples
in a pixel. `Scene.json` reuses one array for every reference probe and for the
returned GPU payload. Cursor advancement uses the proved four-lane row length
instead of rebuilding each primitive's scalar list to count it.
`Primitive.rows_offsets_eq_flattened_length` and
`Scene.data_size_eq_record_cursor` have only Lean standard axioms in their
`#print axioms` reports.

The actual browser-host raw WebGPU track now has **2 matches, 23 unsupported and
13 unavailable** out of the unchanged 38 WPT cases, with no mismatches/rejections.
The two missing-paint fallback cases match every pixel of their independently
captured 800×600 references, with zero channel difference. This uses installed
Chrome 156.0.8078.76 and an Apple `metal-3` non-fallback adapter, the exact Lean
SVG/WGSL compiler and existing Lean render-plan/WebGPU bridge. The browser does
not interpret SVG for the candidate image. Native Deno adapter lookup remains
unavailable here; the result does not establish native-window presentation.

The affine gallery and full generated eight-person FOAF SVG also rendered and
passed Lean readback samples on this GPU; these local examples do not add WPT
passes. Full SVG feature goals and remaining work are in the
[declared feature target](../../../docs/designissues/2026-10-31-svg2-static-feature-target.md).

The shared rendering scene and cross-backend proof objectives are in the
[Solving design](../../../docs/designissues/2026-11-01-svg-scene-compositor.md).
The first shared source-over operation and ordered batch partition theorem are
recorded in the [worknote](../../../docs/20261101-solving-source-over-batching.md).


## Retained linear paths and compound glyphs

Filled paths support absolute/relative M, L, H, V and Z, repeated numeric
arguments, implicit lineto after moveto, adjacent signs/decimals/exponents,
multiple subpaths, closepath current-point restoration, nonzero/evenodd rules
and implicit closure for fill. Closedness is retained separately for stroke.
Empty/moveto-only paths paint nothing. The SVG 2 `none` value is recognized.
The stroker supports these linear contours, including `pathLength` calibration.
Curves/arcs and their strokes remain explicit refusals. Invalid data is currently
rejected rather than implementing SVG 2 partial-prefix error recovery; this is a
material remaining path-conformance gap.

Additional per-path bounds are 65,536 raw characters, 4,096 tokens, 128 subpaths
and 512 points/edges. Numeric scanning stops at 49 characters and refuses tokens
over the existing 48-character numeric limit; long digit runs do not reach an
unbounded numeric scanner. Resolved relative coordinates retain the existing
1e6 magnitude bound. No consumer budget was raised or payload truncated.

Each bitmap glyph now serializes as one compound path retaining exactly its
painted cell squares. This remains vector bitmap geometry, not SVG text/fonts.
Local path/polygon bounds avoid running winding tests outside the actual point
bounds. The storage shader uses a runtime array and bounded data-driven loop;
its source is identical across different valid scene sizes and primitive kinds,
so it can be cached independently of the payload size.

For the generated eight-person example, all old/new 800×600 PPM bytes match.
On the same Apple Metal browser host, 20 resident frame/readbacks improved from
median 131.4ms to 22.0ms while preserving one shader/pipeline/upload. These include
queue/readback/byte costs and are not GPU-only timings or an interactive/OS
scheduling guarantee. Source-branch changes are not automatically present in
older downloaded executables. See the dated linear-path measurement worknote.

## Solving and the shared visuals engine

**Solving** is the SVG-scene rendering pipeline. It is intended to sit on top of
Factoidal's shared visual model, so work on SVG geometry can benefit graph,
compositor and future HTML visuals, while work on that model and its backends can
expand the SVG features Solving can render. The current `Math/Affine.lean`
sharing is an early concrete example; the broader cross-application guarantee is
an architectural target, not something the demo has established yet.

The current renderer still has two scene vocabularies: `NativeGraphics.Shape`
in `Graphics.lean` and SVG `Primitive` in `SVG.lean`. They share affine
algebra, but not yet a common retained scene, clipping model, paint model or
hit-region representation. An SVG feature therefore does not automatically
become available to graph/UI visuals, and a new graphics backend does not by
itself increase SVG syntax coverage. The shared-scene criterion in the Solving
design note requires this boundary to become real; until then, describe reuse
per operation instead of inferring it from the architecture goal.

The boundary should be a typed, backend-independent scene with shared transforms,
shapes, bounds, hit regions and applicable layout-policy parameters. SVG parsing
lowers supported source into that scene. Web-platform SVG, raw WebGPU, CPU raster
and future device-specific targets are separate lowerings of the same scene;
none is privileged as the only possible backend. Policies such as overlap bounds
belong to the shared scene/application layer and should be stated once, with
application-chosen values checked against proved useful lower and upper limits.

Theorems worth building toward are: lowering preserves scene meaning; hit testing
and rendering use the same geometry; backend fast paths agree with a reference
lowering (or state a proved error bound); and policy checks apply to the scene
before backend choice. This lets a new backend add speed or reach without
weakening application-level guarantees. Where the backend contract cannot yet be
proved, the evidence must say so and the feature must not be presented as covered
by the shared theorem. Backend-specific GPU execution and floating-point
boundaries remain separate obligations.
