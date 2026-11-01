# SVG source-level diagnostic artifacts

`labs/demos/foafnaut/SVGArtifact.lean` calls the actual `NativeSVG.compile`
producer from Lean evaluation and writes its JSON scene/WGSL. Set SVG_INPUT
and SVG_OUTPUT; SVG_WIDTH/HEIGHT default to800/600. Run Lean with the lab's
freshly checked olean dependencies, from formal/lean4. This does not rebuild
WASM or establish that an installed executable matches current source.

The existing browser GPU comparison runner now accepts --artifact FILE only
with --fixture FILE, as a local diagnostic. It records the artifact hash and
explicitly labels producer/source correspondence unestablished by the runner.
Original WPT runs remain on their default WASM producer path. Render-plan WASM
is still required for graphics transport. The new path avoids loading the SVG
WASM producer; it does not remove every WASM dependency.

Validation: generated fallback-001's800x600 scene from the current checked
Lean source; parsed the JSON and checked nonempty WGSL/data. JavaScript syntax
check passes. Found cached Playwright outside the workspace and added a Node22 built-in
TypeScript stripping fallback, avoiding another dependency install. Actual
Chrome156/Apple metal-3 non-fallback WebGPU rendered the artifact successfully;
all six CPU reference samples matched. The800x600 RGB output exactly matches
the previously captured independent Chrome reference for fallback-001: zero
differing pixels, maximum channel difference0. Verified recorded oracle image
hash and fixture source hash before comparison. Evidence is in
/private/tmp/svg-source-gpu-check/{candidate,comparison}.json.

This revalidates an already-supported case, not an increase in official suite
coverage. The source-level SVG artifact uses the prior checked SVG module;
this run is not evidence for newer CSS edits or a rebuilt package. The render
plan still comes from the existing separately hashed WASM engine.
