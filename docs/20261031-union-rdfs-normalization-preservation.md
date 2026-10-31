# Checked normalization preservation for the union-to-RDFS link

Tracking: https://github.com/danbri/factoidal/issues/1214 (actual compositor
links). Follow-up to the [public union adapter](20261031-compositor-union-handoff.md),
https://github.com/danbri/factoidal-core/pull/286.

The actual `closureStreamOf` producer now has a theorem connecting a certified
union input to its exact RDFS algorithm result, under the normalizer's checked
syntactic profile. This changes no runtime normalization or closure definition.

## Conditions and result

The premises are explicit:

1. The input is a set (`Dataset.IsSet`), carried by stored handle certificates.
2. `roundTripSafe .rdf12 input = true`, the actual computable syntactic check
   used by `datasetForOps`. It checks printable IRIs, blank-node labels,
   language syntax, and the supported escaped-character subset.
3. The existing closure producer returns `.ok output`. Its serialization
   refusal is still an error; no output-existence claim is added.

`RDF/DatasetNormalizePreservation.lean` proves that lowerTags is identity on
all typed terms, including nested RDF 1.2 triple terms. This follows from the
existing canonical-language-tag invariant of WfLiteral, Term.joinKey_eq_self,
and Term.joinKey_lowerTags. Thus normalizeDataset preserves a certified set's
default list exactly, including order. On the checked branch,
datasetForOps_default_preserved and datasetForOps_default_den connect that
fact to the actual operation normalizer.

`Wasm/Ops/Reason.closureStreamOf_rdfs_safe_output` proves that the actual
successful output equals the existing SoundReasoner.run result on this exact
input default graph. This is algorithm agreement, not semantic completeness.
`closureStreamOf_rdfs_safe_sound` then applies the reasoner's soundness field.
`closureStreamOf_union_rdfs_handoff` combines exact output agreement, regime
entailment and the original source-union membership witness proved earlier.
Its source predicates are DatasetDen membership, not a duplicate adapter model.

The actual RDFS branch selects rdfsReasoner(withMinimalD []). Its existing
soundness proof is reused. No completeness assumption is used, no evaluator
fragment is widened, and no new application-wide HTML or display guarantee is
introduced. The producer also leaves the operation's error check intact.

## Limits tested explicitly

Normalization can delete empty named-graph declarations. The theorem states
default-graph preservation; it does not assert full DatasetDen equality for
arbitrary datasets with empty named graphs. The union adapter has deliberately
already dropped source graph names.

A false roundTripSafe check does not mean failure. A literal containing a
Unicode-escaped control character takes the existing parser fallback and is
accepted in a regression control. This accepted fallback remains outside the
new theorem. Proving preservation for all accepted fallback inputs remains open.
A non-set duplicate list changes length under normalization, so its set premise
cannot be omitted from an exact-list theorem. Handle certification discharges
that premise for the production handoff.

Other compositor obligations remain separate: source graph assignment,
closure-delta retagging, query/result transport, lexical display projection,
XSLT and browser rendering. No full-pipeline badge is added. These source proofs
are not an artifact validation report for the pinned 0.27 demo.

## Validation

Named warm `lake build +L4Factoidal.Dataflow.NormalizationHandoffTests` passes
(415 jobs). Eight controls cover the actual union precondition, exact normalized
input/order, RDFS consequences and blank nodes, public stored-handle closure,
canonical language/nested triple terms, the necessary set premise, empty-name
loss, and an accepted fallback outside the theorem.

Returning an empty graph from the actual closureStreamOf success branch fails
the exact producer-agreement theorem (`g=[]` cannot supply `g=reasoner.run input`).
The source was restored and the named target rebuilt green. Soundness alone
would allow an empty subset; the separate exact-output theorem is material.

Kernel reports contain only propext, Classical.choice and Quot.sound. No new
axiom, sorry, native_decide, partial definition, raised proof budget or audit
allow-list is introduced. The existing assurance CI builds the new test module.
No full local build, WASM rebuild, workflow dispatch or release mutation was run.

Scoped compiled-C tail-recursion and csimp-reach gates pass for Reason and the
new preservation module. No allow-list entries or gate logic were changed.
