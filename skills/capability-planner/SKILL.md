---
name: capability-planner
description: The capability-aware, cost-based planner for data access, computation and service interaction (owner direction 2026-10-12) — the six questions the system answers explicitly, the objects (requirement, available information, capability with access pattern/location/cost/exactness, plan family, execution state), the structural and runtime planner layers, information acquisition as costed work, the Lean semantics and TLA+-style state-machine discipline, and the prior work (PDQ, Calcite, Comunica, SPARQL Anything, Veil). Use when designing or implementing anything that plans across SPARQL endpoints, SQL, REST, MCP or WebMCP tools, files, document transformations, LLM calls or Shardborough; when adding a source kind; or when someone proposes importing data into Shardborough first. Tracking https://github.com/danbri/factoidal/issues/800.
---

# Capability-aware planner

Record: [`docs/designissues/2026-10-12-capability-aware-planner.md`](../../docs/designissues/2026-10-12-capability-aware-planner.md)
(the owner's direction verbatim, the model, related work).
Epic: https://github.com/danbri/factoidal/issues/800.
OKR batch 2, objective O2: https://github.com/danbri/factoidal/issues/801.

Status 2026-10-12: KR 2.1 landed. Lean definitions in
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
   with stated invariants, in the manner of TLA+. Candidate framework: Veil
   (Lean 4, CAV 2025, https://github.com/verse-lab/veil). Check toolchain
   compatibility and that its SMT-discharged goals pass this tree's axiom
   policy before adopting it.

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
