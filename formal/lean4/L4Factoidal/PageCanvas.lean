/-
L4Factoidal.PageCanvas: Canvas 2D for page scripts, drawn by Lean
(record: docs/designissues/2026-11-08-canvas-2d.md).

- `PageCanvas.Color`: CSS colours (parse, serialise).
- `PageCanvas.Geometry`: matrices, paths (arcs as cubic Béziers), flattening.
- `PageCanvas.Paint`: bitmaps, gradients (linear, radial, conic), patterns.
- `PageCanvas.Raster`: coverage (nonzero, even-odd), compositing and blending operators.
- `PageCanvas.Stroke`: strokes as polygons (widths, caps, joins, miter limit, dashes).
- `PageCanvas.State`: the drawing state and its save/restore stack.
- `PageCanvas.Text`: the `font` attribute; text shaped by the Lean shaper.
- `PageCanvas.Png`: the PNG file of a canvas (`toDataURL`).
- `PageCanvas.Canvas`: canvases, the display list (`Cmd`), queries, host commands.
- `PageCanvas.Wire`: the bytes of the `gpu_command` import for Canvas 2D.
- `PageCanvas.Theorems`, `PageCanvas.Tests`.
-/
import L4Factoidal.PageCanvas.Wire
import L4Factoidal.PageCanvas.Theorems
import L4Factoidal.PageCanvas.Tests
