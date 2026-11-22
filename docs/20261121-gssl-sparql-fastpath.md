# GSSL SPARQL fast path: specification and first integration boundary

The objective is a selectively accelerated BGP in the actual SPARQL engine,
with the indexed CPU evaluator as fallback. The initial candidate shape is
`?person <p> ?colleague . ?colleague <q> <object>`, with distinct variables
and IRI predicates and object. The recogniser is syntactic, not evidence that
the graph can be encoded or that a GPU is present.

`SPARQL.GsslFastPath` supplies an executable pure resolution function and
conditional Lean theorems against `SPARQL.evalBgpIdx`, the BGP path used by
`GraphPattern.evalIn`. It refuses to select a candidate for an unsupported
pattern; absence of a candidate falls back. `some []` is a successful empty
answer. A candidate is accepted without executing the CPU evaluator only under
the theorem's explicit premise that it is the exact indexed-engine result.
The code itself does not validate that premise and must not be wired into
production as though an arbitrary host or GPU result satisfied it.

`GsslBgpRefinement.rdfPlan` selects the first predicate relation and feeds its
RDF bindings to the existing second-pattern matcher. Its theorem connects this
plan to `evalBgpIdx` for all graphs and distinct variable names. This is a
source-level RDF refinement: its second stage still uses the CPU RDF matcher;
it does not execute GSSL or establish integer encoding and device correctness.
`resolve_rdfPlan` applies that result to the candidate/fallback boundary,
without assuming correctness of the concrete RDF plan.

The refinement must preserve the exact list of bindings, their internal
association-list representation and multiplicities. `evalBgpIdx_eq_evalBgp`
already relates this engine path to the sequential BGP evaluator. The stronger
ordered requirement avoids unsound substitution beneath downstream operators
that observe order. The Studio's bag comparison alone does not discharge it.

## Required implementation before enabling

1. Translate the matched actual AST and active graph into a GSSL plan. Prove
   this translation, including repeated variables and RDF equality, agrees
   with `evalBgpIdx`; unsupported shapes and datasets fall back. An exact
   graph snapshot, dataset/active-graph identity and request identity must be
   bound to the returned result, so a stale or cross-query answer is refused.
2. Define a collision-free and reversible term encoding that respects engine
   equality, blank-node scope and complete literal identity. Do not truncate
   the engine's identifiers. Check capacity and all input/output bounds;
   overflow, device loss, invalid results and timeouts produce no candidate.
3. Implement asynchronous GPU dispatch and decode without altering the pure
   evaluator's synchronous contract. Establish how the existing external API
   exposes that integration. Preserve exact ordering and binding layout, or
   prove a separate context-sensitive substitution at a safe boundary.
4. Prove the generated WGSL implements the GSSL model under explicit memory,
   scheduling and integer assumptions; until then the backend refinement is
   an unproved external premise. Drivers and hardware are external to the
   Lean model. Test actual devices and software adapters separately.
5. Run W3C SPARQL tests with the hybrid route and CPU oracle, asserting fallback
   for unsupported cases, bag multiplicities, edge cases, device failure and
   no fabricated success. Benchmark end-to-end including encoding, upload,
   dispatch and readback; only select a speed path when measured beneficial.

This change does not wire GPU execution into the shipping evaluator, prove
the candidate premise, establish SPARQL conformance or establish a speedup.
