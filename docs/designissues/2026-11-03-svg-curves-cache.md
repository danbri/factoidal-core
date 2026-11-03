# SVG curves and the checked backend cache

The SVG reader retains line, quadratic, cubic and elliptical arc commands as
typed absolute segments. A contour is either empty with its closed flag, or
has a start point, a segment list and a closed flag. This sum preserves the
old empty contours without adding a fabricated point. Arc flags, Float
coordinates, controls, radii and rotation remain in the source scene.

Rendering uses a separate `LinearContour`. The Lean compiler subdivides
quadratic/cubic curves with de Casteljau operations and converts endpoint arcs
to center parameters. It measures flatness after the complete viewport and
primitive linear transform. The present threshold is 1/64 screen pixel, with
finite-resolution padding, subdivision depth 20 and the existing total budget
of 512 generated path points. These are numeric admission checks. They are
not a proved error bound for ideal real curves or GPU Float32 evaluation.
Failure returns an error; no empty output or chord replaces a failed curve.

One compiled contour list feeds fill, stroke, dash/pathLength, picking and
packed GPU data. The source tree keeps its canonical curves. `Scene.make`
returns an `Except` and stores the compiled primitives with a proof that
`compilePrimitives mapping primitives = .ok compiled`. The checked cache
preserves painter count and source indices. The packed-length proof connects
its cumulative row budget to the actual maximum 262144-float storage buffer.
`Scene.make_existing` proves exact reconstruction of every admitted scene.
These statements prove cache correspondence and bounds, not ideal geometry.

The common HTML/SVG/font model uses the sole canonical types in core
`Rendering/Path.lean`. `NativeSVG.Point` and the `NativeSVGPath` data names are
exact aliases, with constructor compatibility names; no Float conversion or
second record algebra remains. The shared linear-contour round-trip theorem
is reused directly. The common scene adapter must return structured compilation failures and keep
every Float field. Font Q/C outlines must use that model rather than a second
linear path representation. The native Solving adapter already propagates
the checked constructor result and retains its Option compatibility view.

Independent analytic quarter-grid controls cover a quadratic parabola, a
genuine cubic graph, circular arcs and an annular stroke. The native checks
pass. Real GPU full-image comparisons pass exactly for four fill controls;
the annular stroke differs at four diagonal pixels (maximum channel delta
64). That failure is retained. Original upstream curve fixtures also need
markers/textPath, so these authored controls do not establish upstream passes.
See the [implementation and measurement record](../20261102-svg-standards-overnight.md)
for exact logs, source/runtime identities, caps and remaining numeric issues.

The interpretation follows SVG 2 [path commands](https://www.w3.org/TR/SVG2/paths.html),
[arc conversion](https://www.w3.org/TR/SVG/implnote.html#ArcImplementationNotes)
and [stroke rules](https://www.w3.org/TR/SVG2/painting.html#SpecifyingStrokePaint).
The latter distinguishes a moveto-only subpath from an actual zero-length
drawing segment. The former produces no round-cap disk; the latter retains
the specified line cap.


The CPU sampler uses typed partial evaluation of its original expression AST.
It caches fixed parameters, inverse transforms, colors and winding counts for
batch samples, with exact evaluation-order and painter-order theorems. The
reference winding traversal and all clipped/dashed coverage checks remain.
A proved tail-loop replacement avoids recursive batch-list stack growth.
This optimizes the CPU reference checks; it changes neither WGSL nor its numeric
semantics. The SVG port's complete raw artifacts and all83 Deno groups pass.
Paired same-feature timing is a separate measurement gate.
