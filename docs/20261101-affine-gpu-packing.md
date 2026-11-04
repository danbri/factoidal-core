# Shared affine GPU row packing

SVG now obtains its transform payload from `Math.Affine2.toPackedRows`,
instead of constructing an independent coefficient list. The eight-scalar
layout remains `[a,c,e,0,b,d,f,0]`; the homogeneous third row is implicit.
`AffineRows` records the two rows and padding explicitly. This is a reusable
Factoidal representation, not an SVG-only matrix type. Exact/symbolic scalar
values and GPU floats remain distinct specializations.

Four kernel-checked properties establish fixed payload length, coefficient
round-trip through decoding, padding independence, and equality of packed
point evaluation with `Affine2.applyPoint`. These properties require no
algebraic laws and preserve the operation order, so they also apply to the
Lean Float specialization. They do not prove f64-to-f32 conversion, byte
alignment, GPU instruction equivalence, reassociation safety or numerical
error bounds. Eight f32 values occupy 32 bytes only after the host selects
and correctly implements that scalar encoding.

Validation: the changed shared module compiles. Existing exact TOAN matrix
comparison tests pass (16 products, determinants, inverse and point/direction
checks), together with new asymmetric coefficient-order and point-evaluation
controls. The point control uses six distinct coefficients to expose a
transpose or translation-slot swap. The changed SVG source also passes Lean checking against the refreshed
shared module.
No WASM engine or released executable has been rebuilt for this change.

The next obligations are a typed scalar encoding/decoding contract, an actual
shader-load refinement check, and floating-point error policies. General
matrix multiplication and GPU batching remain separate work; this change
centralizes the existing production payload rather than introducing an
unused parallel GPU matrix library.

## HTML and SVG rendering architecture

HTML parsing, CSS resolution and text/layout algorithms can lower to the
same typed rendering scene as SVG. Do not stringify and reparse SVG as an
internal boundary. Preserve source-node identities for hit-testing, links,
selection, focus and accessibility. The scene must retain glyph placement,
paths, transforms, paint, clipping and compositing groups. The HTML DOM and
SVG document trees remain distinct from this rendering representation.
This is an architectural direction, not an implemented HTML layout engine.

See the [SVG 2 rendering tree](https://www.w3.org/TR/SVG2/render.html#RenderingTree)
and the [static feature target](designissues/2026-10-31-svg2-static-feature-target.md).
