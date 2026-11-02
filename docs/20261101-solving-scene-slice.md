# Solving retained scene slice

`labs/demos/foafnaut/Solving.lean` is the first implementation slice of
Solving, the SVG-scene rendering pipeline. It defines ordered scene nodes with
stable numeric IDs, the existing `NativeGraphics.Shape`, integer translations,
and optional rectangular clips. `lower` creates backend-facing render items.
The Lean proofs in that module establish painter-order and shape preservation,
that a successful hit test returns an ID present in the scene, and that a point
outside a node's clip cannot hit that node.

The Lean hit test uses the current `NativeGeometry.hit` predicate for the exact
same shape value used by the SVG export. It applies the inverse translation and
checks the scene-space clip. Curves currently have no hit predicate in
`NativeGeometry`; they therefore do not hit. This is not a general geometry
equivalence theorem between SVG rasterization and pointer events.

`Solving.serializeSVG` is a concrete export backend. The launcher
`labs/demos/foafnaut/Solving.command` compiles the module, generates an SVG in
the ignored `.build` directory, and asks macOS `open` to display it. The
current machine has no registered SVG handler, so I opened the generated path
in Chrome. Browser code does not recreate shapes or paths. The rendering
itself is still delegated to the browser's SVG implementation.

## One policy input carried to the backend

`SolvingPolicy.lean` derives conservative layout footprints from actual scene
nodes, applying their translations, rectangular clips and the scene viewport.
The application names semantic participants by stable node ID; this lets it
exclude connector decoration while checking the people/card boxes. Missing,
duplicate, or empty participant selections cannot produce a `CertifiedScene`.
The checker uses the shared `LayoutPolicy.Config`, so applications can choose
a stricter overlap bound within its validated 300–700 basis-point envelope.
The configuration's 12–24 Hz field remains policy metadata; this module does
not schedule periodic checks.

`CertifiedScene.applicationOverlapBound` proves that every accepted participant
report has positive area and that its summed pairwise intersection-box areas
stay within the application's maximum. `lower_preserves_policyFootprints`,
`lower_preserves_policyChecks`, and `lower_preserves_policyCertificate` show
that the backend-facing `RenderItem` lowering leaves those same policy inputs
unchanged. `Solving.svgBackend` consumes a `CertifiedScene`, and the showcase
build successfully certifies participant IDs 10, 11, 12, 13 and 20 before
writing its SVG output.

This is a policy theorem over conservative boxes, not exact pixel overlap; the
pairwise sum may count an area more than once. It currently covers Solving's
programmatic integer-shape scene, not the separately parsed Float-based SVG
scene. `Backend` makes the checked input common to adapters, but does not prove
that an adapter's output renders the scene correctly. The WebGPU adapter and
cross-renderer refinement proof remain open.

## Evidence and next work

The SVG picker now operates on `NativeSVG.Scene` in reverse painter order.
`Primitive.coverageAt` is shared by the Lean CPU sampler and picker; WGSL is
generated from the same typed fill/stroke condition expressions.
`SolvingSVG.lean` exposes this as `Solving.SVGScene`, `parseSVG` and `pickSVG`, with an
`Option (Fin primitiveCount)` result: an out-of-range paint index cannot be
returned; `Scene.hitTestAt_none_outside_viewport` proves outside queries have no
hit. `NativeSVG.DisplayNode` now retains nested `<g>` boundaries, group IDs and
local transforms. `NativeSVG.Scene.tree` is the parsed structure;
`Scene.primitives` is a cached painter-ordered lowering, with
`Scene.loweringCorrect` recording that it equals the lowering of the tree.
Theorems establish sibling order, group transform/path accumulation and that
the lowering preserves each paint record's geometry and style.
`paintCount_eq_lowerLength` and `paintCountList_eq_lowerLength` prove that the
structural paint count used by the parser limit equals the lowered leaf length,
without allocating a temporary primitive list at each group level. The Lean
SVG artifact also emits the retained tree as optional inspection JSON; the
browser page displays it without reconstructing SVG semantics. The local
compiled WASM artifact still predates that field. Lean omits the inspector
payload above 16,384 nodes; this does not limit scene rendering.
`Solving.pickSVGTarget`
combines a valid paint index with its group path, and
`pickSVGTarget_retains_group_path` proves the path belongs to the indexed
primitive. SVG 2 `display="none"` subtrees are omitted after strict parsing;
inherited `visibility="hidden"` or `collapse` stays in the tree and has zero
effective opacity, with descendants able to restore visibility.
`Primitive.effectiveOpacity_eq_zero_when_hidden` proves the hidden case. This
is a retained logical tree, not yet an independently composited group surface
or author-element hit target. The picker remains geometric and does not
implement `pointer-events` or browser event dispatch. See the SVG 2
[rendering model](https://www.w3.org/TR/SVG2/render.html). The picker's axioms are
`propext`, `Quot.sound`, and Lean core `Classical.choice`;
the retained conversion theorems use only `propext` and `Quot.sound`. It does
not preserve author `id` attributes as pick targets, and this
new picker is not yet wired to the browser UI/C shim or its warm WASM artifact.

The programmatic `Solving.Scene` still uses an integer-only shape vocabulary,
separate from the Float-based parsed SVG scene. The next architectural step is
partly addressed by `Solving.RetainedScene`: one ordered list can preserve
either a full programmatic node or a full SVG display node. The adapters preserve
programmatic IDs and SVG painter order/mapping. Theorems
`RetainedScene.fromProgrammatic_roundTrips` and
`RetainedScene.fromSVG_roundTrips` prove exact conversion back to both source
scenes. Both backend adapters refuse mixed lists instead of dropping items.
The kernel theorems `toSVGScene?_refuses_programmatic_item` and
`toProgrammatic?_refuses_svg_item` prove those refusals for any retained-list
member from the other producer. These conversion and refusal theorems depend
only on `propext` and `Quot.sound`.
This is still a tagged envelope, not shared geometry operations: existing
CPU/WGSL code consumes `NativeSVG.Scene.primitives` and native graphics still
consumes `NativeGraphics.Shape`. The SVG tree is retained but the current
renderer flattens it; group opacity/isolation, clipping and paint-element IDs
are not implemented. HTML layout, CSS,
shaped text, opacity groups, WebGPU refinement, and visual compatibility
remain later steps.

`SVG.lean` and `SolvingSVG.lean` compiled with Lean 4.33.1 after the retained
tree change. The full `build-engines.sh` was not run; the generated WASM runtime
was not rebuilt, so the browser page still uses the prior engine artifact. No
visual or browser validation was performed for this Lean change.

See the [Solving architecture record](designissues/2026-11-01-svg-scene-compositor.md)
for the acceptance criteria and open theorem targets.
