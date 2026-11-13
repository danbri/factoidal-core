# CompactLTJ-inspired Lean 4 experiment (Apache-2.0)

Branch: `experiment/lean-compact-ltj` · Draft PR #417

## Licence and provenance

This is newly written Lean 4 source under Apache-2.0. Design ideas:
Veldhuizen's Leapfrog Triejoin (ICDT 2014), the Ring and CompactLTJ
papers, and classical LOUDS/rank/select succinct dictionaries.
**No implementation source from the GPL-3.0 CompactLTJ, Ring or
ring-basic-p repositories has been translated or copied.**

Apache Jena's published WCOJ branch provides a permissive reference,
but its Java source has not been copied here either. Cite papers and
experiments, not Java or GPL code, when revising the Lean implementation.
A patent review is independent of copyright-licence compatibility.

## What exists in this PR

- `CompactLTJ.Model`: integer-encoded RDF triple patterns, a finite
  variable-domain solver, intersection across *all* incident triple patterns,
  the soundness property, and list-based reference semantics.
- `CompactLTJ.Succinct`: LOUDS-style unary-degree bit sequence,
  rank1/rank0, select1/select0, degrees and child-position primitives,
  structural equations and `#guard` tests.
- `CompactLTJ.SparqlBridge`: restricted conversion from Factoidal's RDF
  graph and SPARQL triple patterns to integer IDs, with an explicit
  unsupported case for nested RDF 1.2 triple-term patterns, and a
  comparison entry point against `SPARQL.evalBgp`.
- `L4Factoidal.CompactLTJ` is imported from `L4Factoidal` to force the
  modules through the normal proof and Lean hygiene gate.

The candidate-domain implementation uses ordinary finite lists and is
**not yet** a succinct compressed trie. It is **not worst-case optimal**,
nor a replacement for Leana's existing production BGP evaluator.

### Semantics caveats

- The current solver checks **existential set-valued** pattern matching.
  SPARQL's solution multiset semantics, multiplicities, ordering and blank
  node treatment require separate refinement work.
- A `TermId` represents an RDF term equality class rather than an XSD
  numeric value. Datatype comparisons remain with the existing SPARQL
  expression engine after a BGP.
- RDF 1.2 nested triple-term patterns are not yet supported by the bridge.
- No native or WASM performance claims are made for these modules.

## What is required for a genuine CompactLTJ executor

1. **Cursor seam**: an immutable seek/open/up/next sorted-trie iterator over
   the existing six Qlvr permutations; prove the ordered-domain contract.
2. **Multiway Leapfrog**: replace `intersectMany` lists with cursor
   intersection, prove exact candidate intersection for finite domains.
3. **Full BGP refinement**: prove output *bags* (not incidental list order)
   agree with `SPARQL.evalBgp`, including repeated variables and missing
   terms. This is the production dispatch prerequisite.
4. **LOUDS packed representation**: compact bitvector, rank/select
   directory, and labels for first/second/third-order trie edges; prove
   navigational equivalence to a plain trie.
5. **Partial-order trie switching**: implement alternative coordinate order
   traversal without retaining all six complete tries. Prove every switch
   preserves the relation represented by the cursor.
6. **Planner**: evaluate fixed and adaptive variable orderings, preserving
   the complete BGP solution bag.
7. **Wire into Leana**: once proved, use the new operator inside the
   existing Factoidal WASM BGP execution path; Leana itself is a
   JavaScript API facade in `danbri/echochamber`, not another Lean engine.
8. **Compare** Qlvr binary join, Leapfrog on Qlvr, and packed CompactLTJ
   with the same datasets and SPARQL queries. Measure native and WASM
   latency, time to first binding, memory, index size and bulk-load cost.

## Verification

From `formal/lean4`:

```sh
lake build L4Factoidal.CompactLTJ
lake build L4Factoidal
```

The PR includes a focused GitHub Actions job and is also checked by
the repository's full Lean verification workflow.

Proof claims should be documented only after an actual clean build and
`#print axioms` check. In particular, a `#guard` is a concrete
regression check, not a universally quantified theorem.

## Relation to previous Factoidal design

This extends the plan already in
`docs/designissues/2026-08-22-indexing-and-join-processing.md`.
It reuses the reference algebra and Qlvr work, rather than copying Jena's
Java architecture into the Lean formal semantics.

The next implementation target is the **cursor seam**, not replacing the
production evaluator prematurely.
