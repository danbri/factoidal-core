# Scoped query provider grants: experimental prototype

This independent branch adds an executable Lean prototype for an explicitly
captured query context. It does not change the frozen 0.28 release candidate,
existing public API defaults, production dispatch, or the dataflow registry.

## API and authority

`L4Factoidal.Dataflow.ExecutionContext.Grants` contains exact SERVICE and host
extension IRI lists, both empty by default. The trusted application chooses
these values; query input must never be allowed to supply its own grants.
`Snapshot α` captures filtered provider values and carries kernel-checked proofs
that every admitted service/extension belongs to its grants. A caller cannot
construct an unbounded snapshot without proving those bounds.

`Wasm.Ops.ScopedQuery.captureContext grants now? : IO Captured` reads each
ambient registry once and stores immutable values. `now?` is an explicit optional
host value; the prototype does not read an ambient clock. `runCaptured context
nquads sparql : String` invokes the actual `queryParsedCertified` producer with
those provider tables. `queryScoped grants nquads sparql : IO String` captures
and runs once. There is no query-text permission scanner and no temporary swap
of a global registry. Registry mutation after capture cannot change the captured
SERVICE graphs or admitted extension IRI list. Captures read the two registries
once each; no atomic cross-registry epoch is claimed.

Denied SERVICE providers use the evaluator's ordinary unavailable-endpoint
semantics. Non-SILENT fails; SILENT may succeed with an empty binding. That success
is not evidence that no lookup was attempted. Result metadata names admitted
providers and explicitly says `attemptTrace: false`; it is not an effect log.
The primary input dataset must itself already be authorized by the caller.

## Theorems and actual consumer

The generic membership and unavailable-lookup lemmas prove the filter's bounds.
`ScopedQuery.denied_service_no_resolver` is about the actual
`SPARQL.EvalEnv.resolveService`, with arbitrary other environment fields.
Variable and nested SERVICE lowering use this same resolver.
`context_denied_extension_no_host_branch` links every proof-carrying context to
the existing `extFnsWith` host-call gate. A denied host extension does not select
its FFI branch; pure built-in GeoSPARQL is a separate excluded branch.

These prove provider admission, not confidentiality/noninterference, input-source
authorization, output-sink policy, transport safety, scheduler behavior or whole
query conformance. The general context invariants cannot grant authority by
proving facts about an untrusted caller's chosen policy.

The current JS extension bridge is a realm-global callback. Capturing admitted
IRIs does NOT capture the implementation identity of an allowed JS callback.
The prototype does not use the public async-extension retry trampoline and does
not claim immutable host callbacks, per-tenant JS isolation, or positive native
FFI callback execution. A later host boundary must capture implementation values
per context and use an explicit context-aware bridge. General resource callback
and sink capabilities also remain future work; current QT4 external-resource
operations continue to refuse I/O.

## Executable checks and remaining gap

`ScopedQueryTests.lean` imports the actual query implementation. Its controls
include the ambient registered secret; a nonvacuous literal SERVICE denial and
explicit grant; SILENT; nested literal SERVICE with outer-only and both grants;
registry replacement and separately spawned evaluations; extension admission and
denial before the actual host branch. Four additional pure guards cover the
empty policy and abstract callback dispatch. Generic callback guards are not
reported as actual JS FFI callback tests.

Bound-variable SERVICE currently returns no rows even with a registered/granted
provider, reproduced independently in published 0.27.0 with VALUES, BIND and a
triple-bound endpoint. Its positive case remains a separate expected failure,
with XPASS failing the probe:
https://github.com/danbri/factoidal/issues/1212 (bound variable SERVICE coverage).
The variable-denial case alone is vacuous as an enforcement control. SPARQL 1.1
Federated Query section 4 explicitly treats SERVICE variables informatively and
supplies no official evaluation semantics, so this is a desired-support gap,
not a normative SPARQL 1.1 conformance failure:
https://www.w3.org/TR/sparql11-federated-query/#variableService

Named Lean compilation uses the existing read-only dependency cache with private
output files, never a full library/WASM build. Final compiled runtime checks:
14 pass, 0 unexpected fail, 1 expected failure; four pure guards passed. The
spawned pair of captured-context evaluations passed with separate old/new
SERVICE snapshot contents. Kernel proofs use only `propext`,
`Classical.choice`, and `Quot.sound` (generic filter lemmas use `propext` only).
No new axioms, sorry, native_decide or partial definitions were added.

This module is a standalone prototype, not yet registered in a public engine or
wired into a CI job. Production adoption needs that wiring, fresh artifact
checks, captured host callback identities, capability propagation across adapters
and explicit source/sink policy. It must not be called a shipped secure API.
