# Paralliverse Query Constellation — SPARQL BGP, readable terms, GPU packing

20 November 2026. Work: [PR #671](https://github.com/danbri/factoidal-core/pull/671) and [issue #665](https://github.com/danbri/factoidal-core/issues/665). The [public Paralliverse page](https://danbri.github.io/factoidal/web/hub/paralliverse/) receives this experiment only after the PR is merged and Pages redeployed.

## Concrete basic graph pattern

```sparql
PREFIX ex: <https://example.org/paralliverse/>
SELECT ?person ?colleague WHERE {
  ?person ex:knows ?colleague .
  ?colleague ex:worksOn ex:Atlas .
}
ORDER BY ?person ?colleague
```

Generate n = 64, 256, or 1024 people. For each i, the input contains two distinct `ex:knows` arcs to (i+1) and (i+7) modulo n; one `ex:worksOn` arc to Atlas if i is a multiple of 4, otherwise Orion; and one literal `ex:label`. Consequently, the graph contains **4n distinct RDF triples**: 256, 1,024, or 4,096. The individual patterns return 2n and n/4 mappings; the join returns **n/2** mappings (32, 128, or 512). The query uses `ORDER BY` only to order the output. SPARQL results have bag semantics even though RDF graphs have set semantics.

Visitors can see the actual source triple strings, the SPARQL syntax, first per-pattern bindings, and **all final solution mappings in pages of 20**, preserving lexical RDF term spellings beside numeric IDs.

## Actual execution boundaries

1. JavaScript deterministically *generates input RDF*, but does **not evaluate the BGP**.
2. A browser Web Worker uses the full published Lean `l4factoidal.wasm` runtime (already used by Hub notebook 51). Three `datasetOpen` calls create the separate source handles and the complete dataset; two independent `datasetQuery` calls evaluate individual triple patterns, and one `datasetQuery` evaluates the full BGP. These are actual local Lean calls, **not** remote Shardborough or Kubernetes workers.
3. Only on explicit request, the host maps `ex:person/NNNN` injectively to fixture-local `UInt32(NNNN+1)`. These are **not** the SBM11 backend's 64-bit term dictionary IDs and do not define an arbitrary RDF-to-integer serialization.
4. The 512 returned pairs at the largest scale become exactly 1,024 u32 words in at most 128 packing rows; the pre-existing **compiled Paralliverse Lean/Wasm CPU** path packs them and compares with **actual WebGPU Count→Scan→Scatter readback**. The GPU does **not** evaluate SPARQL.

The existing Paralliverse Lean packing theorems cover the admitted packing function; they do **not** prove the preceding fixture generator, BGP semantics, term-ID encoding, browser transport or physical GPU compiler/driver. The fixture generator and ID adapter are independently tested in Node. Browser CI tests actual compiled-Wasm BGP runs at 256 and 4,096 triples, complete solution counts and result paging, then byte-compares the final GPU packing of 1,024 words against actual Lean CPU readback. It identifies SwiftShader/software execution; it is not hardware benchmark or GPU correctness proof.

CPU BGP times include runtime startup, input generation/parsing and host overhead, and GPU packing has different transport costs. No comparative speedup is inferred.

Sources: [fixtures](web/hub/paralliverse/bgp-fixtures.mjs), [Lean BGP worker](web/hub/paralliverse/bgp-worker.mjs), [UI](web/hub/paralliverse/bgp-studio.mjs), [unit tests](../tests/hub/paralliverse_bgp_test.mjs), [browser acceptance](../tools/paralliverse-browser-smoke.mjs).
