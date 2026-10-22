# Certified OWL fragment decisions and model-preservation gate

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

Date: 2026-10-21. Status: local implementation and checked library build;
RDF-to-ontology proofs and public adapter integration remain unfinished.
Follow-up: [reader preservation and generated-name repair](20261021-owl-reader-preservation.md)
adds a proved atomic-fragment bridge; the historical results below describe
the initial two-failure stage. The legacy annotation case still fails.

This follows the [methodology design](designissues/2026-10-21-semantic-proof-boundaries.md).
GitHub main was rechecked at `3a38e658c372b111132eb08237ff01a245abd960`.
The existing local repair checkout remains based on `d83100e6`; reconcile
with main before integration. This work does not reopen npm publication.

## Implemented against the real checker

[OWL/CertifiedDecision.lean](../formal/lean4/L4Factoidal/OWL/CertifiedDecision.lean)
uses the exact ontology, interpretation and model existential of
`DirectCert.checkCert_sound`. It is imported by the normal library root.

- `CertifiedVerdict O` requires either a model proof for `O`, a no-model
  proof for `O`, or an explicit unknown reason. Evidence for another
  ontology cannot be substituted.
- `checkedRefutation O certificate` calls the actual `checkCert`. An
  accepted certificate yields a justified inconsistent result. Rejection
  yields unknown, never consistency.
- `erase_sound` proves that removing the proof for wire representation
  preserves the verdict's meaning.
- `no_contradictory_booleans` proves that certified verdicts about the
  same ontology cannot report both consistency and inconsistency.
- `checkCert_rejects_model` proves that **every** certificate is rejected
  for an ontology with a model. This is a universal theorem derived from
  the actual checker soundness theorem, not a finite test assertion.

The composition functions keep the missing work explicit. To lift a
refutation to a source language they require
`SatSource x -> HasModel (lower x)`. To lift a model verdict they require
the reverse implication. These are useful conditional theorems; this file
does not prove either implication for the RDF reader or RL preprocessing.

The existing DirectCert model is a specific OWL fragment. Reusing it does
not complete a formalization of all OWL Direct Semantics or establish its
adequacy to every W3C input.

## Acceptance tests on actual input transformations

[OwlModelPreservation.lean](../tests/assurance/OwlModelPreservation.lean)
specifies intended ontologies independently of the reader under test and
proves Unit-domain models for them. Each also has a theorem that every
certificate is rejected by the real checker on that intended ontology.
The correspondence between these intended ontologies and the RDF fixtures
is an explicit W3C mapping judgment requiring review; it is not the missing
general reader theorem disguised as a definition.

The fixture then parses the actual RDF, invokes the real transformation
and checks the resulting ontology. Its two acceptance conditions are:

| Case | Required checker observation | Current observation |
| --- | --- | --- |
| Annotation-property domain, after RL closure | Reject a refutation | Accepts: fail |
| User class IRI matching the generated-name prefix | Reject a refutation | Accepts: fail |

These are failing acceptance conditions, not XFAIL successes. They expose
the model-preservation defects even though `checkCert_sound` itself is
proved and the new certified boundary builds. The tests make no claim that
the second case is a public API failure; the separate full-search probe
returned `notRefuted` for that input.

Run the [gate](../tools/check-owl-model-preservation.py) from the repo root:

```sh
python3 tools/check-owl-model-preservation.py --json /absolute/path/to/new-report.json
```

It builds the actual dependencies before invoking Lean, requires the exact
nonempty case inventory, audits the independent model proofs' axioms,
preserves parse errors, and requires both successful Lean checking and
rejection of all reported refutations. It records phase commands, return
codes, output and selected source hashes. Those hashes do not cover the
entire transitive compiler/build dependency closure. Build and test timeouts
kill the subprocess group. An existing report is never overwritten.

## Verification

- `lake build L4Factoidal`: passed, 806 jobs, including the new module.
  Existing unrelated deprecation warnings remain. Log in the review:
  `logs/certified-decision-library-build.log`.
- Six executable controls and three rejected constructions in the module
  pass. They include an actual model of the empty ontology and a directly
  proved same/different-individual contradiction.
- The new theorem axiom reports contain only the project's permitted
  standard foundations, or no axioms. The model-to-rejection theorem
  inherits the foundations of `checkCert_sound`.
- Import-root audit: 813 modules, 813 reachable, zero unreachable.
- The real model-preservation gate exits **1** with both named failures;
  its dependency build and independent model-proof axiom audits pass.
  The latest report is `logs/owl-model-preservation-acceptance-v2.json` in
  the review workspace. The earlier report is retained.
- Runner controls reject empty/missing/duplicate reports, duplicate case
  IDs, altered expectations and null observations. Missing Lake exits 2;
  an attempted report overwrite exits 2.

## Remaining public contract

| Public route | Required semantic theorem | Remaining work |
| --- | --- | --- |
| `owlIsConsistent` and its parsed/dataset forms | A definitive wire verdict implies model existence or nonexistence for the original accepted input, under the declared regime | Reviewed source semantics and scope, reader/preprocessing proofs, certified producer and wire integration |
| `owlEntails` and its parsed/dataset forms | A definitive wire verdict implies entailment or a justified countermodel for the original premise/conclusion | The same input bridges plus the goal-reduction theorem O3 |
| Dispatch/native/npm adapters | They preserve the input, regime, options and meaning of the certified producer's result | Actual adapter proof where feasible and exact-artifact tests |

The new module does not change these routes. The finite preservation gate
does not generate an exhaustive export inventory or prove their contracts.
It is not yet called by the live publication workflow. Those limitations
are tracked, rather than reporting the new library theorem as API assurance.

The next implementation target is a role-aware reader for an explicitly
supported structural fragment, with tagged generated names or proved
freshness. Prove its model-preserving relationship to reviewed source
semantics, then supply that theorem to the certified boundary. Restrict or
replace preprocessing that cannot satisfy the corresponding theorem.
Only then can public verdicts safely rely on this boundary for those inputs.
