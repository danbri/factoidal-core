# SVG strokes in the foafnaut Lean engine

Owner, 2026-11-07, verbatim: "let's get svg drawing basics nailed down".

This record says how a stroke goes from the document to the GPU, and what the
limits on paths are. Source: `labs/demos/foafnaut/SVGStroke.lean`,
`labs/demos/foafnaut/SVG.lean`, `labs/demos/foafnaut/SVGPathData.lean`. Tests:
`labs/demos/foafnaut/SVGLinearStrokeTests.lean`,
`labs/demos/foafnaut/SVGTransformTests.lean`,
`labs/demos/foafnaut/svg_test.ts`. Paint of a stroke:
`docs/designissues/2026-11-07-svg-gradients.md`.

## Pieces

`NativeSVGStroke.retain` turns a stroke into a list of pieces, and the pixel is
in the stroke when it is in any piece. There are three kinds: `strip`, `disk` and
`triangle`. Each piece is a fixed record of five rows.

| Feature | Pieces |
|---|---|
| A segment, or the part of it in a dash | one strip |
| Miter join | two triangles to the tip |
| Bevel join | one triangle between the outer corners |
| Round join | one disk at the vertex, also at a reversal |
| Round cap | one disk |
| Square cap | one strip of half the stroke width, away from the stroke |

A miter is a bevel when the ratio of the miter length to the stroke width is more
than `stroke-miterlimit`. A value below 1 is refused.

So joins and caps add no new record kind and no shader code. The theorems
`Primitive.rowCount_eq_storageRows`, `Scene.data_size_eq_record_cursor` and
`shaderRowAdvance_eq_rowCount` keep their statements.

Flattened curves use the join of the element at each flattened vertex. These
corners are smaller than the flatness limit, so the kind of join has no visible
effect there.

The tile box of a primitive is wider for a miter limit above 4, because a tip is
at most `miterLimit*width/2` from its vertex.

## Dashes on circles and ellipses

A circle with a dash array, and an ellipse with a stroke, become a path of two
arcs. The outline starts at 3 o'clock and goes through 6 o'clock (SVG Tiny 1.2
§9.3, §9.4), so dashes start there.

## Zero-length subpaths

§11.4 draws a circle or a square at the point for `round` and `square`, and
nothing for `butt`. It gives no orientation for the square. This engine aligns it
with the x axis of the user space, as SVG 2 does.

`paint-stroke-205-t.svg` compares such a square with a very short diagonal
segment, whose caps are a rotated square. Its reference image shows the
zero-length square rotated too. The specification gives no rule for that rotation,
and this engine does not copy it, so red corners stay visible in that test.

## Limits

- `maxPathPoints`, 8192: the points of one path after flattening, and the
  segments of one contour. A refusal names the number. The limit was 512. At a
  flatness of 1/64 pixel a detailed outline passes that, and six W3C files lost a
  whole group.
- 8 tokens for each point (65536), the same as the limit on the characters of `d`.
- `maxStrokePieces`, 32768: a strip and two triangles at each point, and space
  for caps.
- 128 contours.
- `maxDataFloats` stays the limit on storage, checked for each scene. The theorem
  `maxStrokePath_within_storage` states that one path of the largest size, with
  its largest stroke, fits.

The cost of a larger path: `retain` visits every segment for each dash, so the
worst case is 8192 dash steps by 8192 segments for one element.

## Constrained transforms

`transform="ref(svg)"` and `transform="ref(svg, x, y)"` (§7.7.5) give an element
the CTM of the root `viewBox` mapping and the translation by x and y. The reader
stores a transform relative to the parent, so the local transform is the inverse
of the parent CTM and that translation. No user agent transform exists here, so
the only effect is to leave out the transforms of the ancestors.

## Forgiving pass

A value that the reader refuses for `stroke-linejoin`, `stroke-linecap`,
`stroke-miterlimit` or `stroke-dashoffset` is removed and logged as
`approximated`. Only that value goes: `stripAttr` leaves the same property with
another value. `paint-stroke-202-t.svg` has `stroke-dashoffset="none"` on a group
and valid offsets on its children.

## Open

- https://github.com/danbri/factoidal/issues/1256 (`ref(svg)` under a singular
  parent transform is refused; the specification draws it)
