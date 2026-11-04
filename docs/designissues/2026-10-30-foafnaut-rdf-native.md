# FOAFNaut 2.0 native study: RDF data, Lean layout and GPU labels

The owner asked to revisit the archived FOAFNaut HTML/JavaScript/SVG and use
Factoidal RDF data to drive a native scene. They then clarified that a fun,
modern design is preferred over exact historical replication. The original
Jim Ley / Liz Turner / Dean Jackson work supplies visual and interaction
inspiration; provenance and source anchors are recorded in
[`foafnaut-reference/`](../../labs/demos/foafnaut/foafnaut-reference/README.md).
Original application code/path artwork is not copied into this implementation.

## Implemented boundary

`FoafGraph.lean` calls the real Factoidal Turtle parser, with RDF 1.1 semantics,
and derives people from asserted `foaf:Person` subjects and resource endpoints
of exact `foaf:knows` triples. Typed RDF identities stay separate from display
labels. Directed and self links are preserved; duplicates add no visual weight.
Labels prefer `foaf:name`, then `rdfs:label`, with explicit fallbacks. No inference
or cross-document blank-node identity is implied. The checked JSON model uses
Factoidal's own JSON parser/serializer rather than a new host-side codec.

`FoafNaut.lean` owns graph layout, mouse hit testing, capture, selection, focus,
hide/restore state and WGSL scene generation. The small view is bounded to 16
people and 48 links. It uses deterministic radial targets, one-sixth easing,
fixed 16 ms steps and bounded catch-up. The original used random radial expansion
and easing; this implementation is not a spring or JavaScript execution engine.
The existing spring demo remains a separate experiment.

Dragging pins a name card until reset. Plus heads reveal loaded direct neighbors;
minus feet hide that person and incident links. Neither operation changes other
positions or radial targets. Space pauses easing, and R restores visibility and
clears pins. Resize changes data without rebuilding the shader. Self links
are present in the data but their first segment-based drawing is not yet a
useful loop. There is no network expansion or DOM implementation.

The updated scene uses a light canvas, pastel halos, slate outlines and rounded
name cards. `Font.lean` supplies a newly written 5×7 ASCII bitmap alphabet. Lean
positions characters and encodes row bits; the GPU shader paints cells. This is
temporary lab lettering, not SVG text, font parsing, shaping or full Unicode
rendering. Full Unicode names remain in RDF/model/selection output; unsupported
glyphs display `?`. Labels truncate to their available card width.

The browser pass adds lowercase ASCII glyphs, slightly reinforced bitmap strokes,
a dark header with mint/cyan accents, and an editable address bar. Lean owns its
focus, cursor, selection and copy/cut/paste effects. Enter selects a loaded RDF
identity; it does not fetch a URL. The address is limited to 512 Unicode scalars;
cursor movement is scalar-based, not grapheme shaping. Cocoa supplies committed
text/key events and clipboard I/O; paste enters Lean as one string transaction.

## Packaging and operation

The FOAF small WASM module links the current 13-module RDF/Turtle/JSON source
closure plus Graphics, Font, FoafGraph and FoafNaut. No full library or runtime
rebuild is needed for a warm cache. UI packaging embeds the module and synthetic
eight-person Turtle fixture; it is also possible to read a supplied local Turtle
file through `--rdf`. A sixth small module supplies the typed Lean GPU plan.
The host performs file/clipboard I/O, ABI transport and WebGPU/native window
operations; resource lifetime and presentation scheduling remain host policy.
The precise proof boundary is recorded in
[the render-plan design](2026-10-30-lean-render-plan.md). Source launchers forward to the ignored `.build/dist` output.

At the owner's request the native UI is compiled with FFI permission granted,
removing the per-process prompt needed by `UnsafeWindowSurface`. This grants
native-code capability to the packaged host; it is not a sandbox for arbitrary
plug-ins. The app does not execute scripts found in RDF or the archived SVG.

CLI examples and limits are in the [lab README](../../labs/demos/foafnaut/README.md).
Offscreen `--snapshot` checks GPU pixels and opens the saved PPM; headless
`--emit-artifact` emits scene/reference data without requesting a GPU.

## Evidence

The browser/render-plan integration passed 12 native RDF adapter groups, nine
native graph/editor groups, 51 Deno/WASM tests and 12 C coordinate checks.
RenderPlan kernel proofs and native guards also compile. The model tests replay
focus, dragging, hide/restore, pause, resize and close, and verify shader/slot
stability across states. WASM tests verify that changing Turtle changes graph
data and glyph uniforms, as well as checked model rejection and snapshot probes.

The owner ran the first graph on Apple M1 and observed the bitmap labels;
the log records a first native frame at 1536×1024. That binary SHA-256 was
`9a84a3e01d579162b65099ab8063f92e38fcee4e4c3d17b16f94d2a5ec7e68f2`.
This applies to the initial visual style, before the modern styling and
compile-time FFI grant. Rebuilt binaries require their own desktop review.
The historical SVG reconstruction fixture separately compiles through the
restricted XML/SVG engine; the interactive graph uses direct Lean graphics.
