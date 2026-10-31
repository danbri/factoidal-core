# Variable SERVICE correlation in the backend evaluator

Tracking: https://github.com/danbri/factoidal/issues/1212 (backend/reference mismatch).

## Failure and repair

The public dataset query path supplied a backend. Its JOIN arm evaluated
both operands independently, then hash-joined them. A variable SERVICE
operand therefore lowered against an empty binding and lost the endpoint
provided by VALUES, BIND or a triple pattern. The reference evaluator
already implements per-binding endpoint resolution in either join order.

The backend now delegates a whole JOIN with an immediate variable SERVICE
operand to that existing reference evaluator. Other JOINs retain the hash
join. This fallback materializes the dataset and active graph, as other
non-native arms already do. Memory and time can increase with dataset size;
this is not an optimized remote federation implementation. The providers
remain caller-registered local graph snapshots, with no network transport.

SPARQL 1.1 Federated Query section 4 describes SERVICE variables informatively
and explicitly supplies no normative semantics. This repair restores the
engine's existing reference behavior; it does not establish a new normative
SPARQL conformance claim.

## Proof boundary

`NativeFrag` and `plannerFragment` continue to exclude SERVICE variables.
Their theorem statements, assumptions and assurance classifications are
unchanged. Small exclusion lemmas discharge the new branch guard in the
existing BackendRefinement, BackendAgreement, DatasetRestriction and
SelectedDataset proof bodies. Successful compilation prints only the existing
`propext`, `Classical.choice` and `Quot.sound` axioms for these results.
There is no new axiom, partial definition, sorry or audit allow-list entry.
No theorem for arbitrary SERVICE behavior is claimed.

## Validation

The parsed-query comparison independently checks each reference answer
against expected values/errors, then compares backend answers. Before the
repair: 17 reference controls correct, 8 backend matches, 9 mismatches.
After repair: 17 correct reference controls, 17 matches, 0 mismatches.
Cases cover both operand orders, VALUES, grouped BIND, triple bindings,
duplicates, shared-binding compatibility, nested SERVICE, SILENT missing and
non-IRI endpoints, denied providers and an empty binder. A late ungrouped
BIND remains a parser scope error.

Named warm build: `lake build ServiceVariableRegression
+L4Factoidal.Storage.BackendRefinement +L4Factoidal.Storage.BackendAgreement
l4wasm-cli` passed (1745 jobs). The non-default regression library has an
explicit Lake root and is included in the core assurance workflow.
Scoped compiled-C tail-recursion and csimp-reach gates for StoreDataset pass,
with no policy changes. `git diff --check` passes.

A freshly linked native dispatch `callseq` registers two provider graphs and
returns both expected VALUES/SERVICE results. This verifies actual dispatch
state sharing in one process, rather than replacing the evaluator in JS.
The six new public API/node test groups use real WASM and no network. Against
the installed older 0.27 engine they measured 2 pass, 4 fail, establishing
artifact-level red evidence. Fresh WASM CI is still required for green public
API evidence; no local full WASM build was run.

The same native sequence exposed a separate existing serialized-output gap:
`queryRaw` did not pass SERVICE snapshots to its reference evaluator. This
needs snapshot threading, not a JS serializer workaround, in a follow-up.
