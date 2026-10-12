# Capability-aware, cost-based planner for data access, computation and service interaction

2026-10-12. Status: direction set by the owner. No code yet.

Tracking:
- Epic: https://github.com/danbri/factoidal/issues/800
- OKR batch 2, proposed and waiting for approval: https://github.com/danbri/factoidal/issues/801
- Related: https://github.com/danbri/factoidal/issues/799 (parallel block scans on SBM11, then PushIR)

## 1. Owner direction (2026-10-12, verbatim)

> "We also expect to use TLA+ -like discipline to integrate and dynamically
> plan use of REST, sparqlanything, mcp and webmcp services. capability-aware,
> cost-based planner for data access, computation and service interaction,
> with Lean-defined semantics and adaptive execution.
>
> SPARQL would be one way to express requirements. SQL, REST, MCP tools, file
> sources and LLMs would offer different ways of satisfying them. Shardborough
> would be an execution and storage option, not the place everything must
> first be imported.
>
> system maintains an explicit description of:
>
> What is required?
> What is already available?
> Which operations can produce the missing information?
> What inputs do those operations require?
> Where should the work execute?
> What will it cost?
>
> There is unusually relevant prior work in PDQ—Proof-Driven Query Answering.
> PDQ plans queries across web sources with different required arguments,
> overlapping information and access costs. It uses constraints to find
> cheaper plans, including plans that obtain an answer indirectly rather than
> accessing the relation named in the original query. Its defining idea is to
> generate plans from proofs of answerability.
>
> work can be avoided, combined, relocated or answered through a different
> route.
>
> Apache Calcite provides a useful architectural precedent: its planner
> represents different execution conventions, accounts for conversions, and
> pushes operations into sources that support them. Regions of a plan can
> execute in different engines.
>
> For Factoidal we extend that idea beyond relational engines to document
> transformations, service operations and explicitly approximate model
> computations.
>
> preparation produces a parameterised plan family, not necessarily one fixed
> route.
>
> structural planner would work backwards from the required result. It would
> use mappings and operation descriptions to discover viable paths, choose
> pushdowns and identify reusable subcomputations.
>
> runtime planner would work with measurements: actual cardinalities,
> latency, cache hits, service quotas, observed selectivity and available
> memory. It could alter batch sizes, choose another admitted access path,
> change placement or adjust concurrency.
>
> Comunica already demonstrates why this matters for remote data: it performs
> part of query planning during execution because relevant source information
> may not be available beforehand. Its join selection uses information
> obtained as execution develops.
>
> Discovery and probing are themselves work
>
> The planner should also choose which uncertainty is worth resolving.
>
> It might run a small count, inspect a schema, sample an endpoint, or ask an
> LLM to interpret an unfamiliar operation description. Each such step has a
> cost. A useful decision principle is:
>
> Expected saving from better information > Cost of obtaining that information
>
> This puts schema discovery, statistics acquisition and occasional LLM
> assistance inside the optimisation problem rather than treating them as
> free preliminaries."

Owner, 2026-10-12, second message, verbatim:

> "service descriptions and adaptive tool orchestration. Lean supplies
> knowledge the planner can exploit; Shardborough supplies one efficient
> place to retain and execute data; temporal reasoning makes the distributed
> strategies composable."

What this adds to the model below:
- **Service descriptions** are the source of capability descriptions. For
  SPARQL endpoints this is SPARQL 1.1 Service Description (records of
  2026-04-25); for MCP and WebMCP tools it is the tool's declared name,
  description and input schema; for REST it is an API description. The
  planner reads them and, where they are incomplete, plans probes (section 3,
  item 3).
- **Adaptive tool orchestration** is the runtime planner applied to tool and
  service calls: batching, retries, choice among admitted tools, placement and
  concurrency, inside the admitted plan family.
- **Lean supplies knowledge the planner can exploit.** Proved Lean theorems
  are planner rules: a proved equivalence between two plan fragments is a
  rewrite the planner may apply without a run-time check (for example the
  SBM11 lemmas on block skipping and merge joins, the `@[csimp]` equalities,
  and the RDFS and OWL entailment rules). A rewrite with no proof is not
  admitted, or is admitted only with a differential check.
- **Shardborough** is one place to retain data and execute work on it
  efficiently (SBM11 baseline). It is one of the capabilities.
- **Temporal reasoning makes the distributed strategies composable.** The
  execution state machine is specified with temporal properties (safety and
  liveness over its traces, as in TLA+). Each component strategy states the
  property it guarantees, given stated assumptions about its environment.
  Strategies are then composed by checking that each one's assumptions are
  met by the others' guarantees (assume-guarantee reasoning). Veil is the
  candidate framework.

## 2. Model

The planner works over five kinds of object. Each one gets a typed Lean
definition with a semantics (batch 2, KR 2.1).

| Object | Content |
|---|---|
| Requirement | The result that is needed. First form: a SPARQL query (BGP with filters). Other forms (SQL, a tool call result) can be added later. |
| Available information | Results that are already held: Shardborough generations, in-memory datasets, cached results of earlier operations, statistics. |
| Capability | A source or an operation: the relation it gives, its access pattern (the inputs it requires and the outputs it gives), its location, its cost model, its quotas, and whether its result is exact or approximate. |
| Plan family | A parameterised set of plans, made by the structural planner. Parameters are decided at run time. |
| Execution state | The plan in progress, the measurements, the quota use and the results received. |

Kinds of source and operation:
- SBM11 generations and in-memory datasets.
- SPARQL endpoints, through SERVICE.
- SQL engines.
- REST APIs.
- MCP tools, and WebMCP tools.
- Files read through a Façade-X style mapping (SPARQL Anything).
- Document transformations (XSLT, CSVW, RML).
- LLM calls, marked as approximate.

Shardborough is one execution and storage option among these. Data is not
imported into Shardborough before the planner can use it.

## 3. Planner layers

1. **Structural planner (preparation).** It works backwards from the
   requirement. It uses the mappings and the capability descriptions to find
   viable paths, and from them it chooses pushdowns and finds reusable
   subcomputations. As in PDQ, a plan comes from a proof that the
   requirement is answerable with the access patterns available. Constraints
   (mappings, inclusion dependencies) can give cheaper plans, including plans
   that get the answer from a relation other than the one that the
   requirement names. As in Calcite, each plan region has an execution
   convention and a location, and a change of convention is an explicit
   conversion with a cost.
2. **Runtime planner (execution).** It uses measurements: actual
   cardinalities, latency, cache hits, service quotas, observed selectivity
   and available memory. It can change batch sizes, choose another admitted
   access path, change placement, or change concurrency. It chooses only
   inside the plan family that preparation admitted, so the correctness
   argument for the family covers each choice.
3. **Information acquisition.** A count, a schema inspection, an endpoint
   sample and an LLM interpretation of an operation description are
   operations with a cost, and the planner plans them like other work. It
   does such a step only when the expected saving from the better information
   is more than the cost of getting it.

## 4. Specification discipline

- **Plan semantics:** Lean definitions. The first theorem is soundness: each
  answer of an executed plan is an answer of the requirement over the
  declared relations of the capabilities.
- **Completeness:** stated per capability set. A plan that uses an access
  pattern which cannot list a relation can be sound and still incomplete.
- **System behaviour (TLA+ discipline):** plan execution, adaptation, retries,
  quotas and service interaction form a state machine with stated invariants,
  written in Lean. First invariants: no answer outside the requirement, and no
  quota exceeded.
- **Veil** (owner, 2026-10-12: "Keep Veil on the relevant mentions lists
  too") is the candidate Lean 4 framework for this state machine: it states
  transition systems and their invariants in Lean, discharges verification
  conditions with SMT solvers, and falls back to interactive proof. Before
  adoption, check: compatibility with this tree's Lean toolchain (v4.33.1);
  whether goals that SMT discharges give kernel-checked proofs or rest on a
  trusted solver result (this tree allows no `sorry` and no user `axiom`, and
  `#print axioms` must show only `propext`, `Classical.choice`,
  `Quot.sound`); its dependencies (z3, cvc5, uv) in CI and in the wasm build,
  where it is a proof-time dependency only.
- **Approximate operations:** an LLM result carries an approximation marker
  through the plan. An answer that depends on it is marked, and a theorem
  about exact answers does not apply to it.

## 5. Existing parts in this repository

- `docs/designissues/2026-07-06-virtual-sources-design.md`: SERVICE-wrapped
  REST, MCP and CLI tools, and virtual RML sources (design only).
- The SPARQL SERVICE client and the service description records
  (2026-04-24/25).
- `docs/designissues/2026-09-06-planner-soundness-theorem.md`: block skipping
  cannot remove a row.
- The SBM11 id planner and the end-to-end theorem work
  (https://github.com/danbri/factoidal/issues/776).
- The PushIR design (`docs/2026-08-blockengine.md`), which places work next
  to the data (https://github.com/danbri/factoidal/issues/799).

## 6. Related work

- M. Benedikt, J. Leblay, E. Tsamoura, "PDQ: Proof-driven Query Answering
  over Web-based Data", PVLDB 7(13):1553–1556, 2014,
  https://doi.org/10.14778/2733004.2733017. Project:
  https://www.cs.ox.ac.uk/projects/pdq/
- M. Benedikt, J. Leblay, E. Tsamoura, "Querying with Access Patterns and
  Integrity Constraints", PVLDB 8(6), 2015.
- E. Begoli, J. Camacho-Rodríguez, J. Hyde, M. J. Mior, D. Lemire, "Apache
  Calcite: A Foundational Framework for Optimized Query Processing Over
  Heterogeneous Data Sources", SIGMOD 2018, pp. 221–230,
  https://doi.org/10.1145/3183713.3190662
- R. Taelman, J. Van Herwegen, M. Vander Sande, R. Verborgh, "Comunica: a
  Modular SPARQL Query Engine for the Web", ISWC 2018,
  https://comunica.github.io/Article-ISWC2018-Resource/
- L. Asprino, E. Daga, A. Gangemi, P. Mulholland, "Knowledge Graph
  Construction with a façade: a unified method to access heterogeneous data
  sources on the Web", ACM TOIT 23(1), 2022,
  https://doi.org/10.1145/3555312
- G. Pîrlea, V. Gladshtein, E. Kinsbruner, Q. Zhao, I. Sergey, "Veil: A
  Framework for Automated and Interactive Verification of Transition
  Systems", CAV 2025, https://doi.org/10.1007/978-3-031-98682-6_2. Code:
  https://github.com/verse-lab/veil
- L. Lamport, *Specifying Systems: The TLA+ Language and Tools for Hardware
  and Software Engineers*, Addison-Wesley, 2002.
- Model Context Protocol, https://modelcontextprotocol.io/. WebMCP: a Draft
  Community Group Report of the W3C Web Machine Learning Community Group,
  https://github.com/webmachinelearning/webmcp. Its browser API was still
  changing in 2026.

Bibliographic details checked 2026-10-12. The Comunica paper's DOI was not
confirmed.

## 7. First steps

OKR batch 2, objective O2 (https://github.com/danbri/factoidal/issues/801):
the Lean definitions with the soundness theorem, a structural planner over
access patterns with a test set of at least 20 requirements, six source kinds
described as capabilities, and the execution state machine with two
invariants. The runtime planner, information acquisition, WebMCP and LLM
operations come in batch 3.

## 8. KR 2.1: Lean definitions

Landed 2026-10-12 for OKR batch 2, KR 2.1
(https://github.com/danbri/factoidal/issues/801). Module tree
`formal/lean4/L4Factoidal/Planner/`. Every module is imported by
`L4Factoidal.lean`.

### Definitions

| Lean name | Module | What it is |
|---|---|---|
| `Requirement` | `Requirement.lean` | A BGP (`SPARQL.Bgp`), a list of `RowFilter`, a projection. No new term or solution type: it uses `TriplePattern`, `Binding`, `GraphPattern` of the reference evaluator. |
| `Requirement.answers r g` | `Requirement.lean` | `projectSolutions r.projection (r.pattern.eval g)`: the reference evaluator (`GraphPattern.eval`, filters as `GraphPattern.filter`), then the evaluator's `Project`. |
| `RowFilter` | `Requirement.lean` | A test on solution mappings with a proof field `respects`: the test gives the same result for two association lists that denote the same partial function. |
| `SolEquiv`, `SolLe` | `Requirement.lean` | Equality and extension of solution mappings as partial functions (SPARQL 1.1 section 18.1.8). The evaluator stores a mapping as an association list, so list equality is too strict. |
| `Capability` | `Capability.lean` | Name, arity, required input positions (`inputs`; outputs are the other positions), `location`, `CostModel` (per-call cost, per-row cost, optional call and row quotas, all `Nat`), `exactness : Exactness` (`exact` or `approximate`). |
| `CapSemantics` | `Capability.lean` | `ext` (the declared extension, a list of tuples) and `impl` (input binding to a list of tuples, a pure function). `Sound`: every returned tuple is in `ext`. `CompleteFor inp`: every `ext` tuple that matches `inp` is returned. |
| `Mapping`, `TripleTemplate`, `Slot` | `Mapping.lean` | View-style mapping: each tuple denotes the triples of a list of templates whose positions are tuple positions or constants. |
| `Source`, `Catalog`, `declaredGraph` | `Mapping.lean` | A source is a capability, a mapping and its semantics. The declared graph is the union of the templates applied to every extension tuple of every source (the default graph of the declared dataset). |
| `Arg`, `Access`, `Plan` | `Plan.lean` | Plan tree: `unit`, `access` (source index and one argument per position, each a constant or a variable), `join` (dependent join: the right side runs once per left row, with that row's bindings as inputs), `filter`, `project`, `union`. |
| `Plan.exec`, `Plan.run`, `Row` | `Plan.lean` | Executable semantics over the pure implementations. An access drops a tuple that does not bind consistently with the arguments or whose templates do not give triples. Each row carries `approx`, set when the row depends on an `approximate` source. |
| `Plan.wfBound`, `Plan.WellFormed` | `Plan.lean` | The access-pattern condition: every required input is a constant or a variable bound by an earlier step; arities agree. Decidable. |
| `Rewriting`, `Rewriting.check`, `Rewriting.toPlan`, `IsRewriting` | `Plan.lean` | A list of access steps. `check` (Boolean) requires: (1) each requirement triple pattern is equal to some template of some step's source with the step's arguments put in for the tuple positions; (2) each variable a step binds is a variable of the BGP; (3) the chain of steps is well-formed. `toPlan` is the chain of dependent joins, then the requirement's own filters and projection. `IsRewriting cat req p` is: some rewriting passes `check` and denotes `p`. |

### Theorems (`Soundness.lean`)

- `rewriting_sound`: if each `exact` source of the catalog is sound, and
  `p` is a rewriting of `req`, then each row of `p.run cat` that is not
  marked is, as a partial function, equal to an answer in
  `req.answers (declaredGraph cat)`.
- `run_unmarked_of_allExact`: if all sources are `exact`, no row of any
  plan is marked.
- `rewriting_sound_allExact`: if all sources are `exact` and sound, each
  row of a rewriting is an answer.
- `union_sound`: if two plans are sound for a requirement, their union is
  sound for it.
- `wellFormed_no_inputFailure`: in a well-formed plan, no access in the run
  finds a required input unbound (`Plan.inputFailure` is `false`).

Check against anti-pattern 29: the hypotheses are the soundness of each
source implementation against its own extension, and the Boolean check on
the access steps. Neither mentions the evaluator or `Requirement.answers`.
The proof builds a run of the evaluator's `evalBgpFrom`: for each triple
pattern it takes the triple that the covering template gives for the
returned tuple, shows that this triple is in the declared graph, and shows
that `tpMatch` accepts it from any restriction of the plan row.

All five theorems: `#print axioms` gives `propext`, `Classical.choice`,
`Quot.sound` only (`Planner/Tests.lean`). No `sorry`, no `native_decide`,
no `partial`, no raised heartbeats, no `import Std` in the planner modules.
`python3 tools/lean-tail-recursion-audit.py --gate` exits 0. `bindArgs` and
`inputsGo` are tail calls. `Plan.exec`, `Plan.wfBound` and
`Plan.inputFailure` recurse once per plan operator; they are in
`tools/lean-tail-recursion-allow.txt` with class (b), plan nesting.

### Tests (`Planner/Tests.lean`)

`#guard` cases over three mock sources: a REST-like lookup that requires
the subject, a free scan like a SPARQL endpoint, and an approximate source
whose implementation returns a value outside its declared extension. They
check: a plan with bound inputs is well-formed and passes `check`; the
reversed plan (first access has an unbound input) fails both and reports
`inputFailure`; a plan that covers only one triple pattern fails `check`;
the executed answers of the exact rewriting are the reference evaluator's
answers over the materialised declared graph (same multiset of projected
rows, with and without a filter); the approximate plan marks every row,
and its answer (99) differs from the evaluator's answer over the declared
graph (41).

### Limits of these definitions

- Only triple patterns whose positions are variables or constants can be
  covered. A triple-term pattern (RDF 1.2) is never covered.
- The rewriting shape is one chain of accesses under the requirement's
  filters and projection. Unions of rewritings are sound by
  `union_sound`. Other plan shapes need their own relation.
- The declared dataset has only a default graph; named graphs (quads) are
  not mapped yet.
- `RowFilter` is an abstract test. A constructor from the SPARQL `Expr`
  AST needs a proof that expression evaluation reads a mapping only
  through `Binding.lookup`.

### Open

- Completeness: for a given capability set, each answer of the
  requirement is found by some rewriting (needs `CompleteFor` on each
  access input, and the PDQ-style search that produces the rewritings).
- Costs: `CostModel` is recorded and not used. No cost function on plans
  and no theorem about cost.
- Adaptation: the runtime planner, retries, quotas and probing as costed
  work; the execution state machine with invariants (a later key result
  of https://github.com/danbri/factoidal/issues/801).
- IO: implementations are pure functions; an IO wrapper and its relation
  to `CapSemantics` are not defined.
