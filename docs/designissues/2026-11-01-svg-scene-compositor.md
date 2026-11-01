# SVG vocabulary as a shared rendering scene

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
