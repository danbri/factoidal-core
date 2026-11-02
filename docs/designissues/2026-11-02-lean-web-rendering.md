# HTML layout into the shared retained vector scene

Tracking: https://github.com/danbri/factoidal/issues/1230 (Lean HTML/CSS layout
and shared scene). This implements the direction in the
[Solving design](2026-11-01-svg-scene-compositor.md).

The earlier browser plan, https://github.com/danbri/factoidal/issues/1167
(Lean browser engine), listed Stylo, Taffy, Parley, Vello and Blitz. The owner
subsequently asked that HTML layout use the same SVG-derived graphical model
as SVG and other producers. This work implements style, layout, DOM traversal
and scene construction in Lean. It does not adopt those external engines as
alternate style/layout semantics. A vetted font library can provide font data
and shaping results. The reconciliation is explicit: the earlier external
engine list remains prior design input, not a second implementation target
silently maintained beside the common scene.

## Representation and execution

`formal/lean4/L4Factoidal/Rendering/Scene.lean` defines binary64 Float geometry,
paint, stroke records, affine transforms and an ordered retained paint/group
tree. Geometry includes rectangles, circles, ellipses, lines, polygons and the
current polygonal path contours. No constructor contains an opaque SVG scene
or HTML producer payload. Paint leaves optionally retain the source DOM arena
index. `GlyphRun` records contain font identity, glyph indices, positions,
advances and source character clusters.

`labs/demos/foafnaut/WebRenderSVG.lean` explicitly converts each field of the
existing SVG semantic records. `scene_roundtrip` proves that a parsed SVG
scene converted through the common scene and back has exactly its original
mapping, retained tree and complete paint records. This preserves all Float
values and paint order; it does not prove binary64/binary32 raster equality.
The common scene can lower into the current SVG CPU/WGSL backend without
serializing or reparsing SVG. Shared operation extensions must update both
adapters and their theorems. Curves, clips and isolated group effects require
explicit semantics and backend capability work; they must not be stored as
opaque source-specific cases.

`Style.lean` computes styles over the existing DOM arena. `Layout.lean`
performs block flow and word wrapping, constructs shared baselines before
positioning glyphs/replaced elements, and emits the common geometry. The
`WebRender.lean` adapter uses `DOM.parseHtmlDocument`, whose HTML tokenizer and
tree builder are the existing Lean implementation. Embedded SVG transfers
namespace-aware DOM records directly, with no host DOM extraction or SVG text
round trip.

## Initial admitted scope

The current CSS subset has compound universal/type/id/class selectors,
selector lists and descendant selectors. Cascade priority is lexicographic
importance, inline origin, ID count, class count, type count and source order.
Supported background shorthand is normalized before cascade. Color,
visibility and font metrics inherit; inherited unitless line height retains
its multiplier. Supported lengths are px and percentages for content widths,
absolute heights, nonnegative px box edges and automatic content sizing.

Normal block flow supports anonymous inline contexts, whitespace collapse,
word wrapping, explicit line breaks and shared line baselines. Nonzero
collapsing block margins, decorated inline boxes, inline-block, percentage
heights without a definite containing height and other CSS properties are
explicit unsupported results. This is not general CSS conformance.

The initial font is `factoidal-ascii-bitmap-v1`: original 5 by 7 bitmap outlines
from the existing lab font, six-unit monospace advance, seven-unit em/ascent,
zero-unit descent, ASCII U+0020 to U+007E. Glyph runs are consumed to construct
paint geometry; they are not decorative inspector metadata. Ahem and other
font families are refused. This temporary font profile is not a font-backed
HTML/text MVP and provides no Unicode shaping, bidi, ligatures, selection or
font fallback. HarfBuzz/FreeType data adapters are a subsequent milestone.

## Verification checkpoint, 2026-11-02 22:55 UTC

`LEAN_NUM_THREADS=2 lake build L4Factoidal.Rendering.Tests` from `formal/lean4`
passed 16 executable guards using the actual HTML parser and DOM arena. They
check word wrapping, CSS width changes, `DOM.setAttribute` reflow, source
clusters, differing font sizes on a shared baseline, eleven classes versus
one ID, important declarations, background shorthand order, inherited
unitless line height and named unsupported results.

Fresh lab compilation checked geometry/style/primitive/tree/scene adapters.
`geometry_roundtrip`, `style_roundtrip` and `primitive_roundtrip` use only
`propext` and `Quot.sound`. `scene_roundtrip` additionally uses Lean core
`Classical.choice`. Common retained lowering has checked reverse-accumulator
`csimp` twins and a painter-order append theorem, with only those standard
Lean axioms. No `sorry` or added axiom is present.

This checkpoint has no CPU image, WebGPU image or browser WASM result yet.
Those are separate required milestones. Logs are
`/tmp/factoidal-web-tests-build.log`, `/tmp/factoidal-web-lab-build.log` and
`/tmp/factoidal-web-adapter-build.log`. `tools/ensure-test-env.sh` exited 1:
GitHub API DNS was unavailable and unrelated fixtures/binaries were absent.
No unavailable corpus is reported as a passing zero-test run. Disk free was
4.2 GiB; heavy builds require at least 3 GiB.

## Actual browser vertical slice, 2026-11-02 23:07 UTC

The native and WASM frontend, existing WGSL/WebGPU backend, editable HTML/CSS
viewer and independent whole-image comparison now run. Five local named
checks pass, including exact CPU/GPU/original-HTML browser agreement over a
7,680-pixel box/embedding fixture. The default has actual word flow and
1,579 paint items. This supersedes only the earlier checkpoint's missing-image
status; font and CSS limitations remain. Full evidence and build limits:
[first image worknote](../20261102-lean-web-renderer-first-images.md).
The vetted native [font-data adapter](../../labs/demos/foafnaut/tools/FONT_DATA.md)
is separate from layout and awaits typed Lean consumption.

## Link activation, 2026-11-02

The shared scene now carries typed link fragments built from the actual Lean
line/replaced-element boxes. Blue underlines, CSS overrides and the Lean
region picker are exercised from the browser, with clicks logged to console
and server stdout. Exact DOM-anchor and picker membership proofs, test
results and limits: [link worknote](../20261102-lean-renderer-links.md).
