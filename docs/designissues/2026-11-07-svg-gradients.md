# SVG gradients in the foafnaut Lean engine

Owner, 2026-11-07, verbatim: "do gradients and so on ... let's get svg drawing
basics nailed down".

This record says how `linearGradient`, `radialGradient` and `solidColor` paint
go from the document to the GPU. Source: `labs/demos/foafnaut/SVG.lean`,
`labs/demos/foafnaut/SVGForgiving.lean`,
`formal/lean4/L4Factoidal/Rendering/Scene.lean`. Tests:
`labs/demos/foafnaut/SVGGradientTests.lean`, `labs/demos/foafnaut/svg_test.ts`.

## From document to record

1. `readPaint` resolves `url(#id)`. A target that is not a paint server gives
   the fallback paint. A `solidColor` becomes a one-stop gradient in user space.
2. `readGradient` follows the `xlink:href` chain with `gradientChain`, which
   refuses a cycle. Coordinates come only from gradients of the same kind; units,
   transform and stops come from any gradient in the chain.
3. Stop properties are computed where the stop stands: `inherit` and
   `currentColor` use the ancestors of the stop in the document, not the
   ancestors of the element that uses the gradient (SVG Tiny 1.2 §6.7).
   `normalizeStops` clamps the offsets.
4. The result is `Paint.gradient`, which is also a value of the shared
   `L4Factoidal.Rendering.Paint`, so SVG inside HTML keeps it.
5. `compilePrimitive` lowers it for one primitive with `Gradient.lower`: one
   affine map from the primitive's local frame to a space where the parameter is
   x (linear) or the distance from the origin (radial). The map contains
   `gradientUnits`, `gradientTransform` and the gradient vector or circle. A
   degenerate vector, or `r` of zero, gives the last stop only.

A gradient with no stops lowers to `none`. A bounding box with no width or no
height, or a singular `gradientTransform`, gives the fallback paint.

## Text

The forgiving pass lowers each glyph to a `path` with its own transform, so a
glyph is not the element that SVG paints. The pass writes the box of the character
cells of the whole text on each glyph, in the attribute
`text-box` of the namespace `urn:factoidal:svg-internal`. The reader then sets the
gradient's `frame` to the glyph transform and its `box` to that box. Paint
therefore uses the user space and the bounding box of the text.

The same pass lowers a `use` of text from the `use` element's font values, because
an instance inherits from its `use` element (§5.6). It keeps each `switch` branch
that it does not draw as a definition, so that a reference into it still works.

## Wire form

The fill and stroke rows stay four floats. `[cursor, opacity, 0, -1]` marks a
gradient: the negative fourth float is the mark, and `cursor` is a word offset in
the paint table.

The paint table is the tail of the `tiles` buffer: the words of all records as
binary32 bit patterns, then their count as the last word. The shader finds the
table from `arrayLength(&tiles)` and reads a word with `bitcast<f32>`. This place
was chosen over a table at the end of `Scene.data` because `validateStorage` in
`svg_engine.ts` walks `data` to its exact end, and `Scene.data_size_eq_record_cursor`
and `Scene.data_within_storage_budget` state its size. A tail on `tiles` changes
no theorem about the primitive record, and both the tile path and the dense page
path of `Scene.tiles` append it. A GPU session reuses a pipeline only when `tiles`
is equal, so a changed table starts a new one.

A record is eight words (map x row, radial flag, map y row, stop count), then five
words for each stop (offset, red, green, blue, opacity).

An image uses the same table: see `docs/designissues/2026-11-07-svg-images-text.md`.

## Limits

- 64 stops for each gradient (`maxGradientStops`): a refusal with the number.
- 1,048,576 words for each scene (`maxPaintTableWords`): a refusal with the number.
- Pad spread only, and no focal point: SVG Tiny 1.2 has neither `spreadMethod`
  nor `fx`/`fy`. The strict reader refuses them, and the forgiving pass removes
  them and logs each one.

## CPU and GPU

`GradientRecord.colorAt` is the reference; `paintSample` in the shader states the
same steps. Colour and opacity interpolate separately and are premultiplied by the
existing compositing. `Scene.checks` runs on this reference, so each GPU run
compares its pixels with it.

## Open

- https://github.com/danbri/factoidal/issues/1253 (a stroke narrower than the
  sample grid can draw nothing)
- https://github.com/danbri/factoidal/issues/1254 (animation of paint)
- https://github.com/danbri/factoidal/issues/1255 (references to another document)

The W3C reference PNGs put a stroke of width 1 at x=1 on pixel 1 alone; the
geometry covers half of pixels 0 and 1, and this engine draws that. The references
are 0.5 pixel from the geometry at every edge, which keeps each file out of the
MATCH band. This engine does not copy that offset.
