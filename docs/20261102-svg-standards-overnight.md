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
