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

No runtime speed ratio is claimed for this extension yet. Paired runtime
measurement and the next native/WebAssembly artifact comparison must use the
combined canonical-path build. This does not fix the retained GPU arc-stroke
or affine-boundary discrepancies and does not increase the WPT match count.
