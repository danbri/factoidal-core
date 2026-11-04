# Linked RDF graphs in the Lean renderer

The same renderer now accepts RDF1.1 N-Triples. The existing strict Lean reader
produces RDF terms; a Lean adapter adds text nodes and anchor attributes directly
to the existing DOM arena. The same CSS cascade, block/inline layout, source
clusters, shared scene and WebGPU painter then render the graph. RDF values are
never inserted into an HTML source string.

Tracker: https://github.com/danbri/factoidal/issues/1230 .
Implementation: https://github.com/danbri/factoidal-core/pull/308 .
Build packaging: https://github.com/danbri/factoidal-builds/pull/11 .

At http://127.0.0.1:8099/ choose **RDF N-Triples**, then **Load example**.
IRIs are blue underlined anchors; clicks use the Lean picker and log the original
IRI and DOM source node. Literal text, language tags and blank-node labels are
shown as RDF values. Editing a literal changes the actual image. A malformed
suffix rejects the whole input and clears the previous canvas.

The native macOS ARM64 CLI accepts:

```sh
web-render-native graph.nt 380 340 --rdf
web-render-native graph.nt 128 96 --rdf --pixels
```

The first emits the same complete scene artifact as WASM; the second emits CPU
reference RGB pixels. Native GPU/window presentation remains unverified: Deno
2.9.4 returns no adapter in this session, including explicit Metal selection.

## Checks and proofs

Eighteen Lean guards check strict whole-document parsing, text-node handling of
markup-looking literals, language-tag preservation, original href values, blank
nodes, empty graphs, exact filters and graph bounds. `mem_select` proves that a
selected triple is precisely an input triple matching the typed filter;
`predicate_link` proves preservation of the predicate IRI. These are limited
claims about the adapter, not a proof of the complete parser/renderer/compiler.

The actual WASM check exposed missing `padding-bottom`. The engine now expands
margin/padding shorthands before cascading eight longhands. Importance,
specificity, declaration order and geometry have62core and12lab guards; the RDF
fixture was retained throughout the fix.

The actual integration check passed six groups, including complete native/WASM
artifact equality and the whole128×96 native CPU/GPU text image:12,288pixels,
zero different pixels, maximum channel difference0. It also verifies actual blue
link pixels, pointer picking, click logs, literal edits and stale-image clearing.
The screenshots were inspected. This local fixture is not a WPT conformance
score or an independent browser-font comparison.

Five paired default-page calls before/after RDF+CSS support retained identical
raw artifact bytes, with warm compilation around208ms and ratios0.989–1.028.
This preserves the earlier proved sampler gain; it is not another speedup.

Evidence:
- `/tmp/factoidal-web-rdf-integration-final/report.json`
- `/tmp/factoidal-web-rdf-integration-final/rdf-graph.png`
- `/tmp/factoidal-web-rdf-longhands-abi.json`
- `/tmp/factoidal-web-rdf-performance.json`

Tested WASM SHA256:
`3f4d98939422b96fd1ecbd22c32e3bd85cc46becc0decbb0445483439c14ac73`.
Native CLI SHA256:
`b9441516438f780f7bedfde46d003b8a77592f709b56489e27abffe99e629a17`.

## Current bounds

The graph adapter refuses input above1MiB or256triples; downstream scene/data
bounds can refuse a smaller graph rather than silently truncate it. The current
live text profile remains the explicit ASCII bitmap font. Checked real font
resources and shaping adapters exist, with layout integration in progress.
The native typed filter API is not a SPARQL implementation or an entailment
engine. Public Hub source includes RDF mode; public deployment still requires
the checked browser-runtime release path and exact-source CI gates.
