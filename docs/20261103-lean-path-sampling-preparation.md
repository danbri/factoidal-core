# Share winding geometry preparation across CPU samples

The canonical curve renderer stores a checked linear backend cache. CPU
sampling previously rebuilt the flattened edge list and counted it for each
sample of each un-clipped, un-dashed path. A four-quarter pixel grid repeats
that work four times per pixel. Polygons likewise counted their point list
for each sample.

`Primitive.prepareCoverage` now stores the path edge count or polygon point
count in the prepared coverage closure. It also prepares the polygon bounds
test and the existing stroke predicate. Path winding still calls the original
`pathHit` interpreter. Clipped and dashed primitives retain the original
coverage function.

`Primitive.prepareCoverage_correct` proves identical results for every backend
primitive, packed data array, record base and sample position. The proof
preserves the original floating-point operations and their order; it does
not assume real-number algebra or change the sampling grid. The existing
batch equivalence proof continues to connect the compiler replacement to the
reference sampler.

## Validation on 2026-11-03

Lean 4.33.1 checked the complete SVG module against the fresh shared-path
dependency closure. The batch compiler-replacement theorem reports only
`propext`, `Classical.choice` and `Quot.sound`.

Generated C has a three-argument `Primitive_prepareCoverage` and separate
sample closures which capture the base, cached count and fill rule. The path
sample closure calls `pathHit` with the cached count; edge reconstruction
occurs during preparation.

Local evidence is `/tmp/factoidal-winding-prepared-proof.log` and
`/tmp/factoidal-winding-prepared.c`. The independently applicable source patch
is `/tmp/factoidal-svg-prepared-winding-counts.patch`.

## Same-feature WebAssembly measurement

The combined standalone SVG build at
`a7c5c2f3f9acf10b729b9f6384836078fe3925c9` passes the standard build, native
guards and 83 Deno tests. Its five complete raw curve artifacts are unchanged.
The candidate WASM SHA256 is
`520224f6274333deb13a70b55ecf29db20edf1cbc3720beed5b421424171af36`.

A scratch reference removes only the `csimp` attribute from
`Scene.samplesWithData_eq_fast`. Exact source comparison verifies that single
change. It uses the same remaining object files, runtime and linker flags.
Emitted reference C calls `samplesWithData`; candidate C calls
`samplesWithDataFast`. The exact formatter cache remains enabled in both.

Two alternating paired runs each used two warm-up pairs followed by six
measured pairs for each authored input, at 380 by 340. Every complete raw
artifact is byte-identical in all 48 pairs, including warm-ups.

| Input | Reference ms | Prepared ms | Paired speed ratio |
| --- | ---: | ---: | ---: |
| 192 rectangles | 73--84 | 26--34 | 2.51--2.90 |
| 24 closed cubic paths with holes | 44--47 | 33--35 | 1.28--1.34 |
| 192 closed cubic paths with holes | 276--290 | 193--201 | 1.42--1.49 |

This measures whole SVG frontend compilation, including parsing, curve
lowering, CPU check samples, exact formatting and JSON transport. It compares
the complete prepared batch replacement with the reference; it does not
isolate the edge-count extension or measure GPU drawing. The authored scaling
inputs are performance fixtures, not additional SVG conformance passes.

The reusable `labs/demos/foafnaut/bench-svg-sampling.mjs` checks the exact source
difference before running, hashes inputs and engines, alternates order and
requires complete raw artifact equality. Reports are
`/tmp/factoidal-curve-sampler-reference/paired-report.json` and
`/tmp/factoidal-svg-sampler-paired-harness-check/paired-report.json`.
`/tmp/factoidal-curve-sampler-reference/experiment-witness.json` records source,
C/object and engine hashes; the reference build script and log are retained.

This does not fix the retained GPU arc-stroke or affine-boundary discrepancies
and does not increase the WPT match count.
