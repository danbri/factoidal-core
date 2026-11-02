# SVG standards implementation, overnight 2026-11-02

The SVG lane starts from `9c67291515833dd8b76f0da3f605a7d452943844` on
`codex/svg-standards-overnight`, in the isolated `factoidal-svg-overnight`
worktree. The existing viewer worktree remains unchanged.

## Environment and public DOM interface checkpoint

`tools/ensure-test-env.sh --check` exited 1: unrelated test submodules and
native release binaries are absent in the new worktree. No whole-suite or
zero-test score is inferred. The SVG fixture checker separately verified all
75 original pinned files and the unchanged 38-pair inventory. The broader SVG
corpus is being inventoried by the corpus lane.

The cold targeted source build exposed a real closure omission:
`FoafPresentationProofs` imports `FoafGeometryProofs`, and the presentation
tests import the first module. The script had checked these proof files
without emitting their `.olean` files, so a warm cache hid the missing outputs.
The script now emits both in dependency order. Their proofs and presentation
regressions passed in the fresh worktree.

`NativeSVG.parseRoot` now accepts a namespace-expanded SVG DOM root, explicit
embedding viewport and inherited paint style. The standalone string reader
retains XML/namespace/DTD validation and delegates to this same SVG root
reader. Public `Scene.artifact`, `Scene.samplePixel` and `Scene.samplePixels`
let HTML adapters use the actual SVG packed-data/WGSL producer and CPU sampler
without serializing/reparsing XML. The batch API constructs packed data once;
its equality with individual samples is proved by `rfl`.

Native regressions construct a namespace DOM directly, check inherited
`currentColor`, compare the complete artifact with the equivalent standalone
SVG, test embedding viewBox geometry, compare batch/single samples, and retain
foreign-root and malformed/DTD input checks. This interface checkpoint adds no
new SVG feature or rendering-conformance claim. It unblocks the shared
HTML/SVG renderer lane while substantive instancing work proceeds.

Evidence: `/tmp/factoidal-overnight-svg-{step0,fixtures,source-baseline,api-checkpoint}.log`.
The focused API/proof checkpoint exited 0. Builds use only the targeted Lean
closure and local outputs; no full library/native build is run. Before heavy
phases the lane requires at least 3 GiB free. Last precompile free space was
4.190 GiB. The stable runtime cache's patched source/object witness is verified
read-only; no shared runtime or engine output is changed.

## Next implementation

Implement same-document `defs`/`use`/`symbol` instances, reference identity and
cycle handling, style/transform order and real viewport clipping. The design
follows [SVG 2 structure](https://www.w3.org/TR/SVG2/struct.html#UseElement)
and [URL processing](https://www.w3.org/TR/SVG2/linking.html#processingIRI).
The corpus lane supplies original upstream relations; original fixtures,
denominators and tolerances remain unchanged. Acceptance alone is not a
rendering pass.

## Viewport clip foundation

SVG symbols need actual viewport clipping before they can be admitted. A new
`ClipRect` records local bounds and a Float affine transform. `DisplayNode.clipped`
keeps the content CTM independent from the viewport CTM: a symbol viewBox moves
and scales its contents, while its viewport rectangle stays in the containing
coordinate frame. Lowering transforms both frames through each parent and
retains nested intersections on each primitive. Existing reference traversals
remain declarative, with the same proved tail-recursive replacements extended
for the new constructor.

The packed storage adds three rows per clip after existing geometry, dash and
affine rows. Unclipped records retain their old bytes. Header mode bits preserve
line-cap and affine flags and encode clip count above those bits. Lean theorems
bind clip counts, payload lengths, record cursors and bounded clip-row access;
shader and host validate remaining storage and exact integer counts. The host
validation interprets only the ABI, with no SVG geometry or layout semantics.
CPU sampling, picking and WGSL apply inverse clip-local half planes rather than
world-space bounding boxes. Singular or empty clip frames paint and pick nothing.

Native tests independently describe a rotated square by half-plane equations,
including partial quarter-grid coverage, translated parent, distinct content
transform and nested intersection. Five generated artifacts include independent
full 64×64 RGBA expectations. These are backend diagnostics, not WPT cases or
proof that an SVG source document was interpreted correctly. Source/model/CPU
checks pass in `/tmp/factoidal-overnight-svg-clip-{model,wire,renderer,native,controls}.log`;
All five actual WebGPU controls passed every RGBA pixel exactly (4096 pixels
each, zero differing channels/max delta zero) on Apple Metal, using the frozen
raw bridge. Evidence: `/tmp/factoidal-overnight-corpus-clip-math/report.json`,
with full native-size PNGs and readback hashes matching independent expected
bytes. Standard small-engine build exited 0 (`...-clip-engines.log`), using the
verified runtime cache read-only and our own EM_CACHE/outputs. The rebuilt
SVG WASM passed 23 Deno tests; the remaining lab files passed 52 tests (75 total,
zero failures), including ABI rejection for fractional counts, truncated clips,
forged cursors, inactive flags and zero active bounds. Logs:
`/tmp/factoidal-overnight-svg-clip-deno-{isolated,other}.log`. Tests type-check
with `--no-config --no-lock` because the unrelated root Deno configuration
requires missing node_modules types; the original failed environment attempt
is retained as `...-clip-deno.log`. No type checking was skipped.

The selected original upstream symbol cases include CSS dimensions. The
[SVGWG February 2026 resolution and merged PR1059](https://github.com/w3c/svgwg/pull/1059)
clarify that width/height CSS properties apply to outer SVG (and rect/image/
foreignObject), but are ignored on nested svg/use/symbol; their XML dimensions
still apply. This supersedes conflicting older prose. Instancing tests must
check this rule alongside specified target style overriding inherited use style.
