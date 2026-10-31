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

## Supported subset

SVG-namespace `svg`/`g`, sharp `rect`, `circle`, filled `ellipse`, butt- or round-cap stroked
`line`, filled `polygon`, and filled linear/compound `path` are supported, plus text-only `title`/`desc` metadata. SVG `metadata` subtrees are non-rendering; XHTML `link rel="match"` is recognized as reftest metadata. Other HTML links (including stylesheets) remain explicit refusals.
Namespace prefixes resolve by expanded name; lookalike namespaces, unbound
prefixes, duplicate expanded attributes and foreign elements/qualified attributes
are refused. Geometry accepts signed fractional decimal/exponent numbers and
unitless/px lengths. Rect/circle/ellipse zero size disables painting; negative
sizes are errors. Ellipses require explicit numeric rx/ry and have no stroke.

Default paint is black fill and no stroke. Fill/stroke/color/width, fill/stroke
opacity and fill-rule inherit through groups. `currentColor` stays symbolic
until the leaf resolves its own color; a child's color override therefore works
under an inherited currentColor fill. `inherit`, `none`, 3/6-digit hex colors,
comma-separated `rgb()` numeric/percentage triples, the 16 HTML4 color names and
orange are supported. Paint channels/opacities clamp to their ranges.

Rectangles/circles support centered strokes, with sharp miter rectangle corners
and default miterlimit 4. Lines default to butt caps and support inherited round caps. Round caps use
a capsule, including a disk for zero-length lines; zero-length butt lines and
zero stroke width paint nothing. Polygon fill implements nonzero and evenodd winding
for 3–64 vertices; polygon strokes/joins are refused. Non-inherited leaf opacity
is applied once after premultiplied fill/stroke composition, including overlap.
Group/root opacity is refused rather than approximated per descendant.

Root viewBox mapping follows default xMidYMid meet, all nine alignments, slice,
and none. Positive unitless/px root width/height are required unless both output
viewport dimensions are supplied; source dimensions are still validated. A
fractional SVG viewport stays Float for mapping/clipping while the backing image
size is its ceiling. Subpixel edges use pixel-center classification, not area
coverage. The transparent SVG canvas is composited over a documented white
backdrop for opaque RGB PPM output.

These choices refer to W3C [painting](https://www.w3.org/TR/SVG11/painting.html)
and [viewport transformation](https://www.w3.org/TR/SVG 2/coords.html#ComputingAViewportsTransform),
without claiming all their semantics or other SVG features are implemented.

## Explicit refusals and limits

CSS style/class, root transforms, curved/stroked paths, polylines, text/fonts, nested viewports,
images, use/links, scripting, animation, defs/gradients/patterns, filters, masks,
clips, markers, rounded rects, conditional processing, visibility/display,
paint-order changes, group opacity, square caps, custom joins/miterlimits,
ellipse/polygon strokes, relative/non-px lengths, and unknown colors are errors.
Unsupported features are not silently dropped, even on a zero-size primitive.
IDs and version labels 1.1/2.0 are recognized metadata, not schema validation.
Only unresolved simple local paint-fragment fallback is currently implemented. Full SVG remains open work.

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
8-person FOAF scene now measures 47,845 characters, 292 SVG primitives and 32,792
Float values; a dense 16-person/48-link scene measures 154,860 characters,
716 primitives and 114,728 Float values. Before compound glyph paths these were
128,347/1,880/37,608 and 455,470/6,748/134,968 respectively. These measurements motivate the
bounded profile, not a frame-rate guarantee.

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
GPU result boundaries. Curved/stroked paths remain unsupported; linear paths and affine transforms are described below.


## Shared affine transforms and actual GPU evidence

`Math/Affine.lean` provides typed six-coefficient affine values with explicit
scalar operations. SVG uses its Float specialization for composition, inverse
and point mapping; exact tests reuse existing MathML rational and TOAN matrix
operations. Matrix/translate/scale/rotate (including a center)/skewX/skewY lists
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


## Retained linear paths and compound glyphs

Filled paths support absolute/relative M, L, H, V and Z, repeated numeric
arguments, implicit lineto after moveto, adjacent signs/decimals/exponents,
multiple subpaths, closepath current-point restoration, nonzero/evenodd rules
and implicit closure for fill. Closedness is retained for future stroke work.
Empty/moveto-only paths paint nothing. The SVG 2 `none` value is recognized.
Curves/arcs, pathLength and path strokes/joins remain explicit refusals. Invalid
data is currently rejected rather than implementing SVG 2 partial-prefix error
recovery; this is a material remaining path-conformance gap.

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
