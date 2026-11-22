# Checked saturation for local ASK attestations

Work item: [Local ASK attestation, issue 745](https://github.com/danbri/factoidal-core/issues/745).

## Problem and API

The ordinary RDFS and SPARQL-RL loops return their current graph when fuel
ends. A caller cannot treat that return as evidence of a completed closure.
In particular, evaluating ASK over a partial closure can produce a false
result that changes after more inference. The attestation pipeline must
distinguish exhaustion from a completed false result.

`L4Factoidal.RDFS.Checked.fullClosure` takes explicit `maxRounds` and
`maxTriples`, datatype map, finite `rdf:_n` vocabulary slice and input graph.
It uses the existing axiom seed and `fullStep`. A successful result has
passed a real final convergence check. That check counts against the round
budget; zero rounds refuse, including on an already saturated graph.

`L4Factoidal.SPARQLRL.Checked.evalGraph` takes `maxRoundsPerLayer`,
`maxTriples`, the parsed rule set, input graph and evaluation environment.
It preserves the existing imports/well-formedness/stratification checks,
data-block blank-node scope, run-once order and generalized evaluation
graph. It returns the RDF projection of the **full** evaluation graph,
including the base; it does not substitute the inferred-triples-only API.

Every general layer runs the real semi-naive rounds, reserving one round
for an actual naive full-rule convergence check. Only zero new triples
passes that check. The returned state is the actual semi-naive state; the
check does not replace it. Each layer has its own round budget. Run-once
rules run exactly once and are not given iterative fixed-point semantics.

The ordinary API remains unchanged. Its single-round body is extracted as
the inline `generalRound`, shared by the ordinary and checked paths. No
SPARQL, rule or RDFS semantics is reimplemented in a host language.

## Machine-checked results

There are 35 public theorem declarations in the three new theorem modules.
All were compiled under Lean 4.33.1; each emitted an actual `#print axioms`
report containing only `propext`, `Classical.choice` and `Quot.sound`.

- `RDFS.CheckedTheorems`: checked success equals the old explicit-fuel
  loop, is saturated under the actual full step and fits the retained
  triple cap. Input extensivity, soundness and completeness use the
  existing `DerivesFull` relation. The completeness theorem obtains
  saturation from the actual successful producer, rather than requiring
  the caller to assume it.
- `SPARQLRL.CheckedTheorems`: successful bounded progress equals the
  ordinary loop at exactly the supplied fuel. The actual final full-rule
  check establishes saturation. Retained graph bounds propagate through
  run-once rules, all stratification layers, the exported generalized
  result and its exact RDF projection.
- `SPARQLRL.CheckedSemanticTheorems`: actual round membership is linked
  to the existing declarative `NOut`/`Sem` semantics. For general rules
  and coherent input indexes, accepted output is closed under `NOut`.
  Index coherence and base-member preservation propagate through the
  actual exported producer; the RDF result retains every original input
  triple. The conditional least-fixed-point theorem reuses the existing
  `NegBlind` and general-rule hypotheses explicitly.

The existing `SPARQLRL.SemiNaiveTheorems` was rebuilt after the helper
extraction. It already proves conditional semi-naive/naive equivalence;
this change does not claim that work was absent. Its open obligations
remain the automatic term-universe fuel bound and `NegBlind` from the
general stratifier. The checked path establishes convergence by executing
the additional full-rule check. The separate ASK policy admission must
establish its own fragment restrictions.

## Tests and build evidence

The final targeted closure contained 94 modules. Unchanged dependencies
were reused only where source/dependency stamps matched the baseline
`e0666850902b16471c3299bde30944aa389604ec`; changed modules and their affected
dependency closure were rebuilt. This is not described as an entirely
cold repository build.

- 15 new RDFS guards passed: zero fuel, fixed-point checking at exactly
  one round, insufficient fuel, input/output caps, real transitive type
  inference, input retention and actual full-step stability.
- 24 new SPARQL-RL guards passed: a three-rule chain requires four
  productive rounds and its fifth final check (budget four refuses;
  five accepts), more-fuel stability, complete-graph parity with the
  ordinary evaluator, base preservation, duplicate input, import and
  malformed-rule rejection, empty rule sets and output caps.
- All 39 existing `SPARQLRL.Tests` guards passed after extraction.
- Source hygiene scanned 2,340 Lean files: zero forbidden proof/runtime
  escapes; the existing partial-definition count remained 163.
- A selected generated-C audit of the three changed production modules
  found zero surviving self-recursive calls or mutual recursion cycles;
  the tail-recursion and selected compiler-rewrite checks passed. This
  selected audit does not stand for all unbuilt modules.

The helper is inline so the ordinary evaluator does not acquire a new
round call. The ordinary `generalLoop` and its 12 generated wrapper/fold
functions match the baseline generated C after local-variable renaming.
A nine-sample `lean --run` check on a 25-edge transitive-closure fixture
returned the same 350 generalized triples in every sample. Before/after
p50 was 70.263/67.028 ms; nearest-rank p95, p99 and maximum were
102.686/153.481 ms; spread was 39.237/88.550 ms. These shared-machine,
interpreter measurements are noisy, including a slower final tail sample;
they do not establish a runtime speed improvement. No zkVM-cycle or
proving-time result is claimed by these measurements.

## Bounds and remaining obligations

The limits bound accepted retained graph sizes and inference rounds. They
do **not** cap intermediate join solutions, temporary allocation, term
byte lengths or VM cycles. Parsing/admission limits and fail-closed guest
execution limits remain necessary at the attestation boundary. Resource
errors carry no successful graph or normal Boolean verdict.

The intended phase order is RDFS followed by rules. Rules can introduce
new schema; this order does not claim the combined RDFS-and-rules least
fixed point. The caller selects and commits to that policy explicitly.

These proofs concern the actual Lean definitions and their stated
relations. Compiler/runtime/FFI correspondence and the cryptographic
zkVM proof system remain separate obligations. No native checker result
or generated-C comparison is labelled a zero-knowledge proof.
