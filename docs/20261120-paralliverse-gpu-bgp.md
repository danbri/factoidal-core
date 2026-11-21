# Paralliverse: GPU evaluation of a two-triple-pattern BGP over integer RDF terms

20 November 2026. [Implementation PR #675](https://github.com/danbri/factoidal-core/pull/675), [work item #674](https://github.com/danbri/factoidal-core/issues/674).

## The actual computation

Input: an RDF *graph* whose distinct triples are encoded as three `UInt32` values `(s,p,o)`. The caller must use a collision-free, term-type- and scope-correct dictionary, with admitted term IDs fitting `u32`. This initial profile does **not** support arbitrary 64-bit store IDs or full SPARQL 1.1 query algebra.

The BGP fragment:

```sparql
SELECT ?person ?colleague WHERE {
  ?person :knows ?colleague .
  ?colleague :worksOn :Atlas .
}
```

In the existing generic typed `Paralliverse.Program`:
```
fanout(
  projectKnows(:knows)     : Triples -> Bag(Person,Colleague),
  projectAtlas(:worksOn,:Atlas) : Triples -> Bag(Colleague)
)
  -> equijoin on Colleague
  -> Bag(Person,Colleague)
```

`IntegerBgp.lean` defines the independent bag denotation, ordered per-row join lists, a count/scan representation, and an actual `Par.mapChunks` CPU evaluator. It proves that the task-based CPU version agrees with the ordinary denotation for every worker count and input, and that `fusedJoin` (the optimization that filters original triples while probing) agrees with the unfused typed BGP. Counts sum to the exact result cardinality, including any repeated intermediate bindings. These are theorems in **Lean's logical model**, not device or driver proofs.

## First GPU lowering that now actually runs

The bounded fixed-query WGSL sources in `docs/web/hub/paralliverse/integer-bgp-gpu.mjs` use **three compute passes**:

1. **Count/probe.** One GPU invocation per source triple. For a `:knows` triple, it scans the input graph for matching `:worksOn :Atlas` triples with matching subject. It writes how many pairs that left triple produces, otherwise zero. This fuses both pattern filters into a nested-loop equijoin; GPU code performs the comparisons.
2. **Exclusive scan.** One GPU invocation scans those counts, storing `offset[i]` for each input triple and a terminal total at `offset[n]`. The host reads back the count and prefix arrays, validates monotonic cumulative totals, and refuses output above the admitted maximum (512 pairs).
3. **Emit.** One GPU invocation per original input triple. It probes the original graph again and writes **every** matching `(person,colleague)` pair at `2*(offset[i]+localRank)`. Distinct left row intervals are disjoint by the prefix rule. The host reads and checks the complete output including two trailing sentinel words. It never computes result pairs or join membership.

The source graph must contain unique triples. A repeated RDF triple is rejected rather than treated as duplicate solution evidence. Conversely, a relational join is modeled as a **bag join**: an independent right relation containing duplicate compatible bindings produces duplicate output bindings. The initial anchored right pattern has one match per colleague in an ordinary RDF set, so later projected-variable fixtures are needed to exercise repeated GPU output pairs from distinct right triples.

The first lowering is intentionally not performance-optimized. At 1,024 people it scans up to 4,096 source triples for each of 2,048 matching `:knows` candidates, **about 8.39 million right-triple probes per count pass, repeated for emission**. It is not the 524,288 comparisons of an optimized join on materialized 2,048- and 256-row pattern relations. The exclusive scan is also a single GPU invocation.

A first generic/fast lowering would instead:
```
triples -> select/project knows  (parallel flag -> scan -> scatter)
        -> select/project Atlas  (parallel flag -> scan -> scatter)
        -> equijoin with per-left counts -> scan -> emit
        -> optional SPARQL ORDER BY
```
A hash/merge join and parallel scan are later optimizations with their own proof obligations. This is separate from the old Query Constellation GPU *packing of already-computed results*, which was not GPU BGP evaluation.

## Evidence

- `formal/lean4/L4Factoidal/Paralliverse/IntegerBgp.lean`: typed relational operators, reference semantics, CPU task equality, fixed-query fusion theorem and count/offset invariants.
- `formal/lean4/Harness/ParalliverseIntegerBgpDevice.lean`: independent **native Lean** queries and expected counts/offsets/solution pairs, for 0/8/64/256/1024 people (0/32/256/1024/4096 triples).
- `tools/paralliverse-integer-bgp-device-smoke.mjs`: runs the three **actual** Deno WebGPU shaders on Mesa Vulkan llvmpipe, records shader hashes and compares every count, prefix and returned solution pair against the native-Lean fixture. Missing GPU is an error, not a fake pass.
- The initial actual-device check passed all five cases on a **software fallback adapter**. [CI run 44782366605](https://github.com/danbri/factoidal-core/actions/runs/44782366605).

**Open:** shader-source interpretation and lowering correctness proof (as done for Paralliverse's earlier packing WGSL subset); general RDF-term dictionary soundness and full existing `SPARQL.evalBgp` correspondence; broader BGP pattern/variable handling; full 64-bit IDs as two u32 lanes or admitted dense remapping; named graphs; stable SPARQL bag semantics and ORDER BY; physical GPU and browser Studio demonstration; scaling benchmarks. The current CI evidence is not proof of a general Ethereum- or RDF-style interpreter, and it is not physical hardware CI.
