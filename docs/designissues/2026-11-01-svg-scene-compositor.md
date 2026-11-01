# Solving: an SVG-scene rendering pipeline

**Component name:** Solving (`solving` in lowercase contexts).
**Role:** an SVG-scene rendering pipeline.

The owner proposes modeling visual output from HTML layout in SVG terms,
with explicit compositing layers, to reduce backend-specific complexity and
permit proved optimizations. This is a proposed architecture, not a claim
that the present flattened primitive renderer implements it.

Use typed Lean paths, paint, transforms, clipping, masks, glyph runs and
isolated compositing groups. Preserve separate spatial/scroll, clipping and
effect relationships and stable source-node identities. SVG documents and
HTML layout fragments lower to this shared representation. SVG serialization
is an inspection/export adapter; it must not be the internal computation path.
Glyph runs need explicit font identity, glyph indices, positions and text
cluster mappings; exporting outlines alone loses text semantics.

Logical groups must not force an offscreen texture each. The backend chooses
raster tiles, caches, batching and physical surfaces under a semantics-preserving
lowering contract. GPU/CPU adapters declare capabilities and numeric behavior;
fallbacks or explicit errors must preserve the selected application contract.
3D transforms, external video surfaces, synchronization and resource lifetimes
require compositor machinery beyond a static SVG document.

Useful proof targets: ordered batching preserves source-over composition;
conservative bounds make clipping/culling sound; unchanged dependencies justify
cached output reuse; transform fusion preserves ideal geometry with explicit
floating-error bounds; hit-testing shares scene transforms and clip scopes.
Do not distribute group opacity over overlapping children: two overlapping
opaque children at group opacity 0.5 have overlap alpha 0.5, whereas giving
each child opacity 0.5 produces overlap alpha 0.75 under source-over.
Pixel equality and interaction equivalence are distinct obligations.

This boundary isolates backend work but does not remove CSS layout complexity,
font shaping/rasterization, color management, antialiasing or driver trust.
Portable layout itself should consume explicit font metrics and viewport
inputs and produce immutable fragments with incremental invalidation.

## Expert implementation references

- [Chromium RenderingNG](https://developer.chrome.com/docs/chromium/renderingng-architecture):
  layout fragments, display lists/property trees, layerization, raster and compositor stages.
- [Servo layout](https://book.servo.org/design-documentation/layout.html):
  box tree to fragments to WebRender display items, with separate spatial and clip trees.
- [Firefox rendering](https://firefox-source-docs.mozilla.org/gfx/RenderingOverview.html):
  display lists transferred to WebRender scenes.
- [SVG rendering tree](https://www.w3.org/TR/SVG2/render.html):
  document/rendering distinction and compositing semantics.

The recommendation follows these architectural separations while giving the
shared vector semantics an SVG-based, formally specified vocabulary. It does
not claim that these browsers use SVG itself as their internal backend.

## MVP entry point and draft objectives (owner discussion, 2026-11-01)

Start the shared pipeline MVP before complete SVG Tiny or SVG2 conformance.
The MVP is a vertical implementation slice, not a reduced replacement for the
existing static SVG compatibility target. Continue curves/arcs, strokes, CSS,
text and official visual comparisons alongside it. A percentage of SVG tags
is not an entry criterion.

Before calling it a graphical-pipeline MVP, require: the existing primitive/
linear-path and affine core; typed retained scene nodes and resource references;
rectangular clipping; correct isolated group opacity; explicit source-over
compositing; stable node identities shared with hit testing; bounded validation;
and one useful optimization with a checked preservation theorem. Font-backed
positioned glyph runs are required before calling it an HTML/text MVP. They
need shaping and cluster/source mappings, not the temporary bitmap font.
Do not wait for filters, patterns, arbitrary masks, full CSS layout, 3D, video,
animations or scripting to demonstrate the first pipeline. These remain later
capabilities and SVG coverage obligations, not silently abandoned requirements.

### O1: One semantic scene used by multiple producers and backends

- KR1: SVG and a small programmatic UI producer emit the same typed scene with
  transforms, clips, isolated groups and source identities. No serialize/parse
  round trip and no independent TypeScript drawing semantics.
- KR2: A CPU reference and WebGPU renderer consume the scene. Declare scalar,
  color-space, alpha and sampling contracts; show reference images and GPU
  comparisons for clipping, overlap, opacity and transformed input targets.
- KR3: A small block/inline HTML producer with real shaped text follows, with
  defined CSS scope and preserved link/selection mappings. Label it a subset.

### Cross-producer reuse acceptance criterion

Owner emphasis, 2026-11-01: SVG improvements should benefit all visuals, and
backend improvements should benefit SVG and every other scene producer.
For each new scene operation, put its semantics and geometry in the shared
layer and exercise it from both SVG and a programmatic scene. For each new
backend or fast path, state its admitted capabilities, refinement theorem or
remaining proof gap, numeric contract and benchmark evidence against the same
scene corpus. Do not fork the geometry or move drawing decisions into host
adapters to obtain a passing result. Frontend-only parsing/style improvements
need not affect every producer; backend support does not itself add missing
SVG syntax. Track semantic coverage and frontend conformance separately.

### O2: Optimizations carry explicit correctness obligations

The statements below are targets, not existing proved theorems. Fix reference
semantics independently of optimized implementations; never define equality
as agreement of two calls to the same optimized routine.

| Target | Statement / assumptions | Completion evidence |
| --- | --- | --- |
| Lowering refinement | Interpreting an admitted frontend scene equals its lowered scene under declared resource/style inputs. | Theorem about the actual producer and a malformed-input refusal test. |
| Ordered batch composition | Rendering concatenated ordered batches equals sequential composition. | Proof retaining painter order; mutation that reverses overlap order rejected. |
| Clip and cull soundness | A node with conservative support disjoint from the effective clip contributes nothing. Include stroke/effect expansion. | Actual bounds producer proof and border/stroke controls; visual culling never deletes semantic hit targets. |
| Cache validity | Equal relevant dependency versions and render parameters imply equal reusable output. | Version/resource/viewport dependency model, invalidation theorem and stale-resource mutation tests. |
| Geometry and input agreement | Hit coordinates use the same scene transforms and clip scopes as drawing, under an explicit pointer-events policy. | Shared producer theorem, singular-transform case, invisible-but-interactive controls. |
| Representation refinement | Packed buffers decode to the semantic values; dimension/alignment/index bounds hold. | Shared actual encoder/decoder theorem, host byte-encoding tests and shader load validation. `AffineRows.toVec4Rows_flatten` now proves that the SVG inverse-transform producer's two four-lane groups flatten to the canonical eight-scalar payload; host byte encoding, shader indexing and GPU arithmetic remain separate obligations. |
| Numeric refinement | Backend arithmetic approximates ideal geometry within an explicit error budget. | Stated finite-input/range conditions; conservative bounds include error. Edge pixels need coverage tolerances, not an unsupported universal exact-pixel theorem. |
| Policy preservation | Certified optimizations preserve named layout/input policies for the resulting scene. | Checker soundness linked to actual optimized geometry and application parameters. |

Start with ordered batch composition and rectangular clip/cull proofs. Cache
and numeric refinement need stronger dependency and arithmetic models. General
Float associativity is false: do not justify transform fusion with ring laws
for Float. Exact geometry theorems and rounded backend execution are separate
links in the argument. Bounds on allocations/operations require a cost model;
logical equivalence alone proves no speedup.

The SVG GPU shader generator uses `primitiveFixedRowCount`,
`dashPieceRowCount` and `affineTransformRowCount` when emitting record offsets.
`Primitive.fixedRows_length` proves the five-vec4 fixed prefix;
`geometryTailData_length` proves padded polygon coordinates and path edges occupy
the expected variable geometry rows;
`Geometry.shaderTailRowsFromHeader_eq_tailRows` proves the Nat-level tag/count
formula used by WGSL matches that geometry-tail count;
`dashPieceData_length` and `dashPayloadData_length` prove the five-vec4 dash
stride used by the loop. The affine row count is derived from shared
`AffineRows.vec4RowCount`. `Primitive.rows_length` proves the complete payload
length is four scalar lanes per row, and `Primitive.shaderRowAdvance_eq_rowCount`
ties that length to the Lean-level cursor formula. Header mode bits for round
caps and transform presence are also checked. The WGSL remains generated text,
and Float-to-u32 conversion, host upload and shader-load refinement remain open.

### Progress: ordered source-over batches (2026-11-01)

`NativeGraphics.PremultipliedLayer.overOpaque` is now the shared CPU source-over
operation, and SVG's CPU reference calls it for each painted element. The
kernel-checked `compositeOpaqueLayers_append` theorem proves that folding an
ordered layer list in two batches gives the same result as folding the
concatenated list. The induction preserves each Float operation's order; it
does not authorize painter-order changes or arithmetic reassociation.

This is a reference-level partition theorem, not an implemented batching
optimization. No WGSL blend path, GPU numeric-refinement theorem, alpha-bearing
destination, group-isolation semantics or clip/cull theorem follows yet. A
future optimized backend must consume the same layer meaning and prove its own
lowering contract.

### O3: Demonstrate useful performance without losing scope

- KR1: Record before/after frame, upload, allocation and memory measurements
  on the same scene/device, including warm/cold distinction and readback cost.
- KR2: Show scrolling or transform updates avoid layout and unchanged uploads
  for a controlled scene, while preserving image/input behavior.
- KR3: Preserve all38 existing WPT cases and their unsupported/unavailable
  outcomes; add a separate MVP corpus. Each compatibility improvement reports
  fresh comparisons against an independent renderer, not only our CPU sampler.

Status: draft objectives. Existing affine packing and source renderer tests are
inputs, not completion evidence for O1–O3. No new scheduler, release or GPU
correctness claim is created by this plan.

## Appendix: naming decision and future candidates

Owner decision, 2026-11-01: call this component **Solving** or **solving**.
The connection to Lean proofs and theorems is intentional. The suggested
stylization “SolVinG” inspired the choice, but do not use fiddly internal
capitalization in the component name. No acronym expansion is prescribed.

“SVG-scene rendering pipeline” describes its role: typed scenes expressed in
SVG graphical concepts, with composition and backend rendering. The name does
not assert full SVG conformance, a complete HTML/browser layout engine, or that
every optimization and backend is already proved correct. Existing implementation
and proof boundaries in this document remain in force. This records a component
name, not a package/module/API rename or a legal availability determination.

The owner's candidate list, retained for reference:

- savage
- saving
- serving
- salvage
- solving
- surviving
- surveying
- sovereign
- scavenger
- disadvantage

**saving**, **serving**, **salvage**, and **scavenger** are possible future
component names. No responsibilities or implementation commitments are assigned
to them yet.
