---
name: capability-planner
description: The capability-aware, cost-based planner for data access, computation and service interaction (owner direction 2026-10-12) — the six questions the system answers explicitly, the objects (requirement, available information, capability with access pattern/location/cost/exactness, plan family, execution state), the structural and runtime planner layers, information acquisition as costed work, the Lean semantics and TLA+-style state-machine discipline, and the prior work (PDQ, Calcite, Comunica, SPARQL Anything, Veil). Use when designing or implementing anything that plans across SPARQL endpoints, SQL, REST, MCP or WebMCP tools, files, document transformations, LLM calls or Shardborough; when adding a source kind; or when someone proposes importing data into Shardborough first. Tracking https://github.com/danbri/factoidal/issues/800.
---

# Capability-aware planner

Record: [`docs/designissues/2026-10-12-capability-aware-planner.md`](../../docs/designissues/2026-10-12-capability-aware-planner.md)
(the owner's direction verbatim, the model, related work).
Epic: https://github.com/danbri/factoidal/issues/800.
OKR batch 2, objective O2: https://github.com/danbri/factoidal/issues/801.

Status 2026-10-13: KR 2.1 to 2.4 landed. KR 2.1 landed 2026-10-12. Lean definitions in
`formal/lean4/L4Factoidal/Planner/` (requirement, capability, mapping,
plan, `Plan.exec`, rewriting check) with the soundness theorem
`rewriting_sound`, the marker theorem `run_unmarked_of_allExact` and
`#guard` tests; record section 8 of the design record.

KR 2.2 landed 2026-10-12: the structural planner `Planner/Search.lean`
(`search`, `plan`: a plan family ordered by a cost estimate, or
`notAnswerable`) over exact-cover accesses, with `search_check` and
`search_sound` (each member is a rewriting, so `rewriting_sound` applies)
and `search_complete` (if a checked rewriting of exact covers with at most
`k` accesses exists, the search returns one), all proved;
`Requirement.ofQuery?` (`Planner/FromQuery.lean`). Test set:
`lake exe l4planner-test` (run in `formal/lean4/`), 25 pass, 0 fail,
7 expected-fail (out of 32); the expected failures name
https://github.com/danbri/factoidal/issues/801 and the run exits 1 on an
XPASS. Record section 9. Open, each with an expected-failure case: access
positions that no requirement pattern names, inclusion dependencies
(indirect plans through a binder access) and answer completeness, quotas
in admission, the execution state machine, named graphs, `RowFilter` from
a SPARQL `Expr`.

KR 2.3 landed 2026-10-12: six source kinds, each described from its
description document by a `describe` function in
`formal/lean4/L4Factoidal/Planner/Kinds/` (record section 10): `sbm11`
(the manifest and a PSO predicate probe; one capability per permutation
key prefix, all 8 input sets of `{S, P, O}`), `memory` (the dataset),
`sparql` (a SPARQL 1.1 Service Description with VoID property partitions;
calls go through SERVICE), `facadex` (a SPARQL Anything IRI and the CSV
header), `rest` (an OpenAPI-like document; the path parameter is the
required input), `mcp` (an MCP tool declaration; required properties are
required inputs; `_meta` gives the mapping and the exactness). Theorems
`graphSource_triples`, `graphSource_sound`, `graphSource_complete`
(`Kinds/Common.lean`). Tests in `Harness/PlannerKinds.lean`: at least two
requirements per kind, a mixed requirement over three kinds and one over
five, and an SBM11 differential test against the id path.
`l4planner-test`: 58 pass, 0 fail, 16 expected-fail (out of 74). Open,
each with an expected-failure case naming
https://github.com/danbri/factoidal/issues/801: source content constraints
(triple-form capabilities in a mixed catalog), SBM11 read at call time
through IO, Façade-X JSON, two required inputs (REST, MCP), tools with no
RDF mapping (MCP, WebMCP), SERVICE over HTTP, fetch of a service
description, SQL engines.

KR 2.4 landed 2026-10-13: the execution state machine in plain Lean,
`formal/lean4/L4Factoidal/Planner/Exec.lean` (record section 11). TLA+
form: `Init`, eight actions (`Call`, `Receive`, `Fail`, `Retry`,
`Advance`, `Adapt`, `Finish`, `Stop`) and `Next` as their disjunction.
Inductive invariant `Inv` with `init_inv` and `next_inv`; for every
reachable state (induction on traces) `reachable_sound` (I1: no unmarked
output row outside the requirement's answers, from `rewriting_sound`),
`reachable_quota` (I2: no call count above its call quota),
`reachable_output` (a `done` output is the `Plan.run` of a member of the
family). `next_wf`: every action decreases a lexicographic measure, so no
trace is infinite. The driver `Exec.run` (fault schedule for the
environment; retry, then switch to the next plan of the family, then
stop) ends `done` or `stopped` (`run_spec`). `#print axioms`: the three
standard axioms only (`Planner/ExecTests.lean`). `l4planner-test`:
67 pass, 0 fail, 17 expected-fail (out of 84); `runtime-quota-adaptation`
is an assertion now. Open, each with an expected-failure case naming
https://github.com/danbri/factoidal/issues/801: row quotas at run time,
reuse of call results after a switch.

KR 4.1 (batch 3, https://github.com/danbri/factoidal/issues/875) landed
2026-10-22: `Plan.execM` (`Planner/ExecM.lean`) runs a plan in a monad and
calls each source at run time; `execM_eq_exec` / `runM_sound`: when every
call returns `pure` of the pure implementation (`CallsDenote`), the result is
`pure` of `Plan.exec`, so `rewriting_sound` applies. SBM11 calls are keyed
id-path scans (`Harness/PlannerSbm11IO.lean`, `l4planner-test sbm11-query GEN
Q.rq [--check-pure]`); `tests/planner/sbm11_gate.sh` compares with `l4sbm11
query` (8 pass, 0 fail, out of 8 accepted gate queries). Query blank nodes are
variables now (`ofQuery?`). `l4planner-test`: 70 pass, 0 fail, 18
expected-fail (out of 88). Open: the `Exec.run` driver over IO calls
(https://github.com/danbri/factoidal/issues/933, xfail `exec-driver-io`).
Record section 12.

KR 4.2 (batch 3) landed 2026-10-22: run-time adaptation in `Exec.lean`.
Admission: `searchAdmitted` keeps the members of `search` whose estimated
calls and tuples are within every call and row quota (`CostModel.rowsPerCall`
is the source's statistic; without it the estimate uses the fanout, and a
plan can be refused). `Receive` enforces the row quota and updates an
observed-cost record and a cache of call results; the new action `Hit`
answers a known call from the cache. On a switch the driver ranks the
alternatives by `adaptScore` (measured rows per call, measured latency per
location, known calls, remaining quotas). Proved: I1 and I2 (calls and
rows) for the new machine, `reachable_cache_hit` (a cache hit gives the
rows of `Plan.exec`). `l4planner-test`: 77 pass, 0 fail, 16 expected-fail
(out of 93). Open: admission with no statistic refuses a plan within its
quota (https://github.com/danbri/factoidal/issues/937). Record section 13.

KR 4.3 (batch 3) landed 2026-10-22: probes (rule 6). `CostModel.probeCost`
is the cost of a count of one call's tuples. A tenth action `Probe` counts
one call within the call quota, records the count, and changes no plan,
row, output or cache (`probe_frame`). The driver `Exec.runProbed` starts
from the structural family (`search`), decides each candidate (a
constant-only access of a source with a probe and no statistic) by
`wantProbe`: probe when `c * |scenarios| + Σ costWith < Σ costWithout`
over `Config.scenarios` (uniform prior on the tuples per call; a plan over
a quota costs `Config.refuseCost`), then `chooseStart` takes the plan of
least score under the probe counts, or stops. Proved: `wantProbe_iff`,
`probe_inv`, `reachable_probes`, `runProbed_spec` (I1, I2 with probes).
Issue 937 closed: with a probe the plan is admitted. `l4planner-test`:
91 pass, 0 fail, 15 expected-fail (out of 106). Record section 14.

When you write a probe test: state the expected decision and give a
control (the same catalog with no probe operation, a statistic, or a
probe cost of `ceil(expSaving / |scenarios|)`); read the numbers with
`probeNumbers` in `Harness/PlannerTest.lean`.

When you add an IO source kind: give its calls as `Calls m`, keep a pure
`graphSource` (or other) implementation as the specification, and add a
differential test that each call equals it (the `CallsDenote` hypothesis).

Veil (rule 7) was evaluated for KR 2.4 (record section 11): Veil `main`
needs Lean v4.32.0 (this tree: v4.33.1; no v4.33 branch of Veil,
lean-smt or Loom), and with its default `veil.smt.trust true` an SMT goal
is closed by `sorryAx`. It is not a Lake dependency. Do not add it
without the owner's decision; if it is added, keep it out of the
`L4Factoidal` library and the wasm roots, set `veil.smt.trust false`, and
gate each theorem on `#print axioms`.

When you write a planner test that must leave a plan at run time, give
the source a statistic that is too low (`rowsPerCall`): without one the
estimate of the fanout refuses the plan at admission and there is no run.

When you change `Exec.lean`: a new action is a new disjunct of `Next`, a
new case of `next_inv` and of `next_measure_lt`, and a new branch of the
driver with its `stepExec_next` case. If a driver branch is not a `Next`
step, the proof of `stepExec_next` fails and `lake build` fails.

When you add a source kind: write `describe` from the kind's own
description document, attach the implementation separately, use the
predicate form when the document names predicates, and add the kind to a
mixed case in `Harness/PlannerKinds.lean`. A triple-form capability in a
mixed catalog gives plans that are sound and incomplete (open item above).

## Rules

1. SPARQL is one way to state a requirement. SQL engines, REST APIs, MCP
   tools, files and LLMs are ways to satisfy it. Shardborough is one
   execution and storage option. Do not design a path that must import data
   into Shardborough before the planner can use it.
2. The system keeps an explicit, inspectable description of: what is
   required; what is already available; which operations can produce the
   missing information; what inputs those operations require; where the work
   should execute; what it will cost.
3. Every capability states its access pattern (required inputs, outputs),
   location, cost model, quotas, and whether its result is exact or
   approximate. An LLM result is approximate. Answers that depend on it carry
   a marker, and theorems about exact answers do not apply to them.
4. The structural planner works backwards from the requirement and produces
   a parameterised plan family. Plans come from proofs of answerability over
   the access patterns and constraints (PDQ). Each plan region has an
   execution convention and a location, and a change of convention is an
   explicit conversion with a cost (Calcite).
5. The runtime planner chooses only inside the admitted plan family, using
   measurements: cardinalities, latency, cache hits, quotas, selectivity,
   memory. The correctness argument for the family covers each choice.
6. Discovery and probing (counts, schema inspection, endpoint samples, LLM
   interpretation of an operation description) are planned operations with a
   cost. Do one only when the expected saving from the better information is
   more than its cost.
7. Semantics are Lean definitions. The first theorem is soundness: each
   answer of an executed plan is an answer of the requirement over the
   declared relations. Completeness is stated per capability set. System
   behaviour (execution, adaptation, retries, quotas) is a Lean state machine
   with stated invariants, in the manner of TLA+ (`Planner/Exec.lean`).
   Candidate framework: Veil (Lean 4, CAV 2025,
   https://github.com/verse-lab/veil); evaluated 2026-10-13 and not adopted
   (toolchain v4.32.0; SMT goals trusted by default), decision with the
   owner (record section 11).

8. Service descriptions (SPARQL 1.1 Service Description, MCP and WebMCP tool
   schemas, REST API descriptions) are the source of capability
   descriptions. Plan probes where they are incomplete.
9. A proved Lean equivalence between two plan fragments is a rewrite the
   planner may apply. An unproved rewrite is not admitted, or only with a
   differential check.
10. Distributed strategies compose through temporal properties: each states
    what it guarantees under stated assumptions about its environment
    (assume-guarantee), checked over the execution state machine's traces.

## Existing parts to reuse

- `docs/designissues/2026-07-06-virtual-sources-design.md`: SERVICE-wrapped
  REST, MCP and CLI tools; virtual RML sources.
- SPARQL SERVICE client and service description records (2026-04-24/25).
- `docs/designissues/2026-09-06-planner-soundness-theorem.md` and the SBM11
  id planner (https://github.com/danbri/factoidal/issues/776).
- PushIR, for work placed next to the data: `docs/2026-08-blockengine.md`,
  https://github.com/danbri/factoidal/issues/799.
- Retaining data in Shardborough without a text file: the SBM11 packer takes RDF quads from
  any producer (`QuadSource`, `Sbm11Pack.packQuads`; `QuadSource.ofDataset` for a dataset in
  memory, `GraphStore.quadSource` for an HDT file). A plan step that holds a dataset, or reads
  a store whose reader gives RDF terms, can retain it without writing and parsing a document.
  `skills/shardborough-storage/SKILL.md`,
  https://github.com/danbri/factoidal/issues/866.
