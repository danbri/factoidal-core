# Capability-aware, cost-based planner for data access, computation and service interaction

2026-10-12. Status: direction set by the owner. KR 2.1, 2.2, 2.3 and 2.4 landed (sections 8, 9, 10, 11); batch 3 KR 4.1 and 4.2 landed (sections 12, 13).

Tracking:
- Epic: https://github.com/danbri/factoidal/issues/800
- OKR batch 2, approved by the owner 2026-10-12: https://github.com/danbri/factoidal/issues/801
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
  Evaluated 2026-10-13 (section 11): Veil needs Lean v4.32.0, and its SMT
  goals rest on `sorryAx` unless `veil.smt.trust` is set to `false`; it
  is not added, and the choice is put to the owner. The KR 2.4 state
  machine is in plain Lean.
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

Section 9 (KR 2.2) gives the search with its completeness theorem
relative to exact covers, and a cost estimate that orders the plan
family. The other items stay open; section 9 lists their
expected-failure cases.

## 9. KR 2.2: structural planner

Landed 2026-10-12 for OKR batch 2, KR 2.2
(https://github.com/danbri/factoidal/issues/801). Modules
`formal/lean4/L4Factoidal/Planner/Search.lean` (search and theorems),
`Planner/FromQuery.lean` (a requirement from a parsed SPARQL query),
`Planner/SearchTests.lean` (`#guard` cases and the axiom audit), and the
executable `l4planner-test` (`Harness/PlannerTest.lean`, the test set).

### Algorithm

The search works backwards from the requirement: it uses only accesses
that put a requirement triple pattern in the declared graph, and it adds
an access only when the access's required inputs are bound (PDQ's
answerability under access patterns).

1. Pool: the variables and the constants of the requirement's BGP.
2. Candidates: for each source, each argument list over the pool, kept
   when the access is an exact cover (`Access.exactCover`): some template
   of the source, with the arguments put in, is a requirement triple
   pattern, and every argument position is used by such a template. An
   exact cover adds no join condition and no constant that the
   requirement does not state.
3. Depth-first search with fuel `k`, the bound on the number of accesses
   (`dfs`). A state is the accesses chosen so far, in execution order, and
   the variables they bind. A state whose accesses cover every triple
   pattern is a result. Otherwise each candidate that is executable (its
   required inputs are constants or bound variables) and useful (it binds
   a new variable or covers a pattern not yet covered) extends the state.
4. Admission: a result is kept when it passes `Rewriting.check` and is
   minimal: no single access can be removed with the check still passing
   (`familyAll`). When some kept rewriting is also irredundant in any
   order (`Rewriting.irredundant`: no access can be removed with the
   others in the greedy executable order), only those are kept.
5. Order: exact before approximate, then the cost estimate, then the
   number of accesses (`Ranked.le`). The estimate (`estCost`) charges
   `perCall` for each call and `perRow` for each row, with one call of an
   access per incoming row (the dependent join of `Plan.exec`) and
   `fanout` rows (default 10) for each variable that an access binds
   first. No theorem uses the order or the estimate.
6. Verdict (`plan`): `plans family`, or `notAnswerable` when the family
   is empty.

`dfs` recurses once per chosen access (at most `k`), `argLists` once per
argument position, `queryPatternBgp?` once per join of a WHERE clause;
the three are in `tools/lean-tail-recursion-allow.txt` with their bounds.
`chainOk`, `estCostGo`, `greedyGo` and `selectVarsGo` are tail calls. No
`partial`.

### Theorems (`Search.lean`)

| Theorem | Statement | Status |
|---|---|---|
| `search_check` | Each member of `search cat req k` passes `Rewriting.check`. | Proved. Admission (step 4) applies the check. |
| `search_isRewriting` | Each member's plan satisfies `IsRewriting`. | Proved. |
| `search_sound` | Under sound exact sources, each unmarked row of a member's plan is an answer of the requirement over the declared graph. | Proved: `rewriting_sound` applied to `search_isRewriting`. |
| `search_mem_of_minimal` | Each minimal rewriting of exact covers with at most `k` accesses that passes the check is in `familyAll`. | Proved. |
| `search_complete` | If some rewriting of exact covers with at most `k` accesses passes the check, then `search cat req k ≠ []`. | Proved. |
| `plan_notAnswerable_sound` | If the verdict is `notAnswerable`, no rewriting of exact covers with at most `k` accesses passes the check. | Proved, from `search_complete`. |
| `args_mem_pool_of_exactCover` | Each argument of an exact cover is in the pool, so step 2 lists every exact cover. | Proved. |

The completeness proof: a checked rewriting has a minimal sub-rewriting
(remove accesses one at a time; `exists_minimal`). For a minimal one, no
proper prefix covers the requirement (else the last access can be
removed), and each access is useful where it stands (else it can be
removed: it binds no new variable, so later inputs stay bound, and it
covers no new pattern). So `dfs` reaches it along its own prefixes
(`mem_dfs_of_minimal`). The irredundancy preference never empties a
non-empty family, and the sort keeps every member.

Check against anti-pattern 29: the hypotheses of `search_complete` are
the Boolean check, the length bound and the exact-cover property of each
access; none mentions `dfs` or `search`.

`#print axioms` for the seven theorems and for `mem_dfs_of_minimal`:
`propext`, `Classical.choice`, `Quot.sound` only
(`Planner/SearchTests.lean`).

### Tests (`lake exe l4planner-test`)

Each case: a requirement, mock sources with binding patterns, the bound
`k`, the expected verdict, and for most the expected first plan. For each
plan returned: the rewriting passes the check; its plan finds no input
unbound at run time; an exact plan's `Plan.exec` gives the reference
evaluator's answers over the materialised declared graph (multiset
equality of the projected rows; mode `subset`: a strictly smaller
sub-multiset); an approximate plan marks every row.

| Case | Sources (required inputs) | Verdict |
|---|---|---|
| `subject-lookup` | REST lookup by subject | plan: lookup with the subject constant |
| `object-lookup` | lookup by object | plan |
| `object-input-never-bound` | lookup by object; `?x name ?n` | not answerable |
| `two-sources-cheaper-first` | scan (500 per call) and lookup (50 per call) of the same relation | 2 plans, lookup first |
| `dependent-join` | scan `knows`, lookup `name` by subject | plan `[knows, name]` |
| `dependent-join-bound-too-small` | the same, `k = 1` | not answerable |
| `dependent-join-three` | two `knows` steps, then `name` | plan of 3 accesses |
| `input-never-bound` | sensor read needs its subject; a scan of another relation | not answerable |
| `no-source-for-predicate` | no template gives `worksIn` | not answerable |
| `binder-without-constraint-not-admitted` | lookup by subject; a scan of another relation that lists some people | not answerable |
| `source-not-complete-for-inputs` | lookup whose implementation returns part of its extension | plan; answers a strict sub-multiset |
| `indirect-through-mapping` | lookup by subject; an SQL table (person, name, department) whose mapping gives `name` and `worksIn` | plan through the table only |
| `approximate-marked` | scan; LLM-like age source (answers 99 where its extension says 41) | plan, every row marked |
| `exact-before-approximate` | scan; LLM age source (2000 per call); exact age source (5000 per call) | exact plan first |
| `filter` | dependent join with a `RowFilter` | plan |
| `constant-in-output` | scan with a constant subject | plan |
| `triple-scan-variable-predicate` | triple scan, predicate as a tuple position | plan |
| `mapping-constant` | unary relation mapped to `rdf:type :Member` | plan |
| `empty-bgp` | empty BGP | plan with no access |
| `dependent-join-email` | scan, email lookup by subject | plan |
| `all-constants` | scan; a pattern of three constants | plan |
| `from-sparql` | the requirement parsed from SPARQL by `Requirement.ofQuery?` | plan |
| `three-sources-ranked` | scan, lookup and scan of `name` | at least 2 plans, lookup first |
| `outside-constant-control` | control: the hand rewriting with key `"k1"` passes the check and gives the reference answers | (control) |
| `from-sparql-filter-rejected-today` | control: `ofQuery?` returns `none` for FILTER and GRAPH | (control) |

Result 2026-10-12: planner: 25 pass, 0 fail, 7 expected-fail (out of 32):
23 requirement cases, 2 controls, 7 expected failures.

### Open, with expected-failure cases

Each case is an `xfail` in `Harness/PlannerTest.lean` that names
https://github.com/danbri/factoidal/issues/801. It is counted in the
`expected-fail` bucket while it fails; when it passes, the run prints
`XPASS` and exits 1. Form: the Lean probe convention of
`skills/test-suites/SKILL.md` § Expected failures.

| xfail case | Open item | What the case asserts |
|---|---|---|
| `search-outside-constant` | Search completeness over all checked rewritings: an access with a required input that no requirement pattern names | the search finds a plan for `?s ?p ?o` over a scan that requires a key (the rewriting with key `"k1"` passes the check: control case) |
| `wide-relation-unnamed-output` | `Rewriting.check` admits no fresh variable, so a relation with a column that the requirement does not use gives no plan | the first plan for `?x name ?n` over the (person, name, department) table gives the reference answers |
| `indirect-binder-inclusion-dependency` | Inclusion dependencies (PDQ constraints) are not modelled, so an access that covers no pattern and only binds an input for a later access is not admitted. This is also the case for answer completeness (section 8, first item): the sources are complete and no plan gives every answer | the first plan for `?x name ?n` over a lookup by subject and a complete scan of members gives the reference answers |
| `quota-in-admission` | Costs and quotas are not used for admission; no theorem about cost. Flipped to an assertion by KR 4.2 (section 13): `searchAdmitted` | no plan in the admitted family exceeds a call quota |
| `runtime-quota-adaptation` | Adaptation: no execution state machine; quotas are not enforced at run time. Flipped to an assertion by KR 2.4 (section 11): the driver's run stays within each call quota and gives the reference answers | the run of the first plan stays within each call quota and gives the reference answers |
| `named-graph-requirement` | Named graphs: the declared dataset has a default graph only | `ofQuery?` accepts `GRAPH <g> { ... }` |
| `rowfilter-from-expr` | `RowFilter` from a SPARQL `Expr` | `ofQuery?` accepts a FILTER |

## 10. KR 2.3: source kinds

Landed 2026-10-12 for OKR batch 2, KR 2.3
(https://github.com/danbri/factoidal/issues/801). Owner, 2026-10-12,
verbatim: "service descriptions" are the source of capability
descriptions. Each source kind has a function `describe` from its
description document to a list of `Described` records (a `Capability`, its
`Mapping` to triples, the source kind and the predicate the mapping fixes).
One document gives a list because it declares several access shapes (the
permutations of a generation, the properties of a response). The
implementation is attached separately, from data or from a mock service.

Modules: `formal/lean4/L4Factoidal/Planner/Kinds/`: `Common.lean` (the two
mapping forms, `graphSource`, theorems), `Sbm11.lean`, `Memory.lean`,
`Sparql.lean`, `FacadeX.lean`, `JsonTerms.lean` (JSON values as terms,
shared by REST and MCP), `Rest.lean`, `Mcp.lean`, `Tests.lean` (`#guard`s,
axiom audit). Test set: `Harness/PlannerKinds.lean`, run by
`lake exe l4planner-test`. The case machinery moved from
`Harness/PlannerTest.lean` to `Harness/PlannerCheck.lean` with no change of
behaviour.

### Mapping forms

Every graph-backed kind uses one of two mappings:

- triple form: arity 3, template `(0, 1, 2)`; the predicate is a tuple
  position;
- predicate form: arity 2, template `(0, p, 1)` for one predicate `p`.

REST and MCP use the predicate form, with the subject (tuple position 0)
as the required input.

### The six kinds

| Kind | Description document | Capabilities (required inputs) | Cost model | Exactness | Implementation in tests |
|---|---|---|---|---|---|
| `sbm11` | the generation's `manifest.sbm11` (its PRM1/PRB1 roles give the permutations) and a predicate probe (the distinct first column of PSO, read through the id path) | per permutation and key length `k = 0..3`, inputs = the triple positions of the first `k` columns; PSO, POS, SPO, OSP give all 8 subsets of `{S, P, O}` (triple form); per predicate, the subsets that contain `P`, with `P` removed: `{}`, `{S}`, `{O}`, `{S, O}` (predicate form) | key length 0: the quad count; else 20 plus the quad count halved per key column (a proxy: no per-column statistics yet); 1 per row | exact | `graphSource` over the rows that a full SPO scan of the id path reads; a differential test against the keyed id-path scan of each capability's permutation |
| `memory` | the dataset (a `Graph`): its size and its distinct predicates | the 8 subsets (triple form); per predicate the 4 subsets of `{S, O}` | scan: the triple count; lookup: 1; 1 per row | exact | `graphSource` over the dataset |
| `sparql` | a SPARQL 1.1 Service Description in Turtle, parsed by `parseTurtle`: `sd:endpoint` (location), `sd:supportedLanguage` (a query language is required), `sd:resultFormat` (JSON, XML, CSV or TSV results are required), `sd:feature`, and on `sd:defaultDataset` / `sd:defaultGraph` the VoID `void:triples` and `void:propertyPartition` | one triple-form scan; per VoID property partition the predicate form with `{}`, `{S}`, `{O}` (a bound join sends one request per input row) | 200 per request, 1 per row | exact | `serviceImpl`: the query text `SELECT ... WHERE { SERVICE <e> { s p o } }` with the inputs as N-Triples terms, parsed by `parseSparql` and run by `evalSelect` with `EvalEnv.services` set to the mock endpoint map |
| `facadex` | a SPARQL Anything IRI (`x-sparql-anything:location=...,csv.headers=true`; options `location`, `media-type`, `csv.headers`, `csv.delimiter`, `namespace`, `root`) and, as a probe, the CSV header row | one triple-form free scan; per column a predicate-form free scan | the file size per call, 1 per row | exact | `graphSource` over the Façade-X triples of the CSV (`triplesOf`: `fx:root`, `rdf:_n` rows, `xyz:<column>` cells; the CSV read by `CSVW.read`) |
| `rest` | an OpenAPI-like JSON document: `servers`, `paths`, a GET with one path parameter, `x-rdf-subject` (subject IRI template), response schema properties with `x-rdf-predicate` (and `x-rdf-object: iri`), `x-cost` | per mapped response property, the predicate form with `{S}` (the path parameter) | `x-cost`; default 50 per call, 1 per row | exact | `restImpl`: a GET through a mock function from URL to body; the body parsed by `parseJson` |
| `mcp` | an MCP tool declaration (`name`, `inputSchema` with `required`, `outputSchema`, and `_meta."org.factoidal/rdf"`: `subject`, `subjectTemplate`, `predicates`, `objectIri`, `exactness`, `cost`); the required properties are the required inputs | per mapped output property, the predicate form with `{S}` | `_meta` cost; default 100 per call, 1 per row | `exact`, or `approximate` from `_meta` (a model's answer; its rows are marked) | `mcpImpl`: `tools/call` through a mock function; values from `structuredContent`; `isError: true` gives no tuple |

### Theorems (`Kinds/Common.lean`)

| Theorem | Statement | Status |
|---|---|---|
| `graphSource_triples` | A graph-backed source declares exactly the triples of the graph that its predicate allows: `t ∈ (graphSource d g).triples ↔ t ∈ g ∧ keeps d.partition t = true`. | Proved. |
| `lookupImpl_sound`, `graphSource_sound` | The lookup returns only extension tuples (`CapSemantics.Sound`), so `rewriting_sound` and `search_sound` apply to plans over `sbm11`, `memory` and `facadex` sources. | Proved. |
| `lookupImpl_complete`, `graphSource_complete` | The lookup returns every extension tuple that matches the input (`CompleteFor`). | Proved. |

`#print axioms` for the five: `propext`, `Classical.choice`, `Quot.sound`
only (`Kinds/Tests.lean`). For `sparql`, `rest` and `mcp` the
implementation is a call. For these, soundness is a test, not a theorem:
the test set compares `Plan.exec` with the reference evaluator over the
materialised declared graph.

SBM11: there is no end-to-end theorem between the id path and the
reference evaluator (https://github.com/danbri/factoidal/issues/776).
The test set has a differential test instead. For each of the 16
capabilities of the test generation (8 triple form; 4 per predicate for
`knows` and `manages`) and each input binding from the generation's terms
plus one term that is not in it, the keyed scan of the capability's
permutation equals the pure implementation (134 calls). The rows that the
id path reads equal the packed triples.

### Tests (`lake exe l4planner-test`)

| Case | Kinds in the catalog | Verdict and first plan |
|---|---|---|
| `sbm11-pack-read-round-trip` | sbm11 | the rows read through the id path are the packed triples |
| `sbm11-id-path-differential` | sbm11 | 134 keyed id-path scans equal the pure implementation |
| `describe-sbm11`, `describe-memory`, `describe-sparql`, `describe-facadex`, `describe-rest`, `describe-mcp` | each | the document parses; the expected capabilities (names, input sets, exactness, cost fields) |
| `describe-sparql-refuses-update-only` | sparql | a description with only `sd:SPARQL11Update` is refused |
| `describe-mcp-refuses-unmapped-required-input` | mcp | a tool with a second required input is refused |
| `sparql-service-query-text` | sparql | the query text of a bound call parses |
| `sbm11-predicate-scan` | sbm11 (predicate form) | `?x knows ?y`: `pso/1[knows]` |
| `sbm11-subject-then-lookup` | sbm11 | `alice knows ?y . ?y knows ?z`: `[pso/2[knows], pso/2[knows]]` (a dependent join on the PSO key) |
| `sbm11-object-key` | sbm11 | `?x knows carol`: `pos/2[knows]` before the PSO scan |
| `sbm11-variable-predicate` | sbm11 (triple form) | `?s ?p ?o`: `pso/0` |
| `memory-predicate-scan`, `memory-object-lookup`, `memory-variable-predicate` | memory | the scan; `memory:o[livesIn]`; `memory:s` |
| `sparql-partition-scan`, `sparql-subject-bound`, `sparql-triple-scan` | sparql | the partition scan; 2 plans (scan, bound); `sparql:triples` |
| `facadex-column`, `facadex-two-columns`, `facadex-triple-scan` | facadex | `facadex:name`; two columns joined on the row; `facadex:scan` |
| `rest-lookup`, `rest-two-properties` | rest | `rest:getPerson.name`; the name and the email of one subject |
| `rest-input-never-bound`, `mcp-input-never-bound` | rest; mcp | not answerable: no access binds the subject |
| `mcp-tool-call`, `mcp-approximate-marked` | mcp | `mcp:get_weather.temperature`; the rows of the approximate tool are marked |
| `mixed-sbm11-rest-facadex` | sbm11, rest, facadex | the first plan uses the three kinds: `[sbm11 pso/1[knows], rest name, facadex name, facadex team]` |
| `mixed-five-kinds` | sbm11, memory, sparql, mcp, rest | the first plan uses the five kinds |
| `mixed-approximate-marked` | memory, mcp (approximate) | marked |

For every plan of every family: the rewriting passes the check, no input
is unbound at run time, and the answers of an exact plan equal the
reference evaluator's answers over the materialised declared graph
(multiset equality).

Result 2026-10-12: planner: 58 pass, 0 fail, 16 expected-fail (out of
74). The KR 2.2 part is unchanged: 25 pass, 0 fail, 7 expected-fail (out
of 32). The KR 2.3 part: 33 pass, 0 fail, 9 expected-fail (out of 42).
Run time 0.4 s.

### Open, with expected-failure cases

Each is an `xfail` in `Harness/PlannerKinds.lean` that names
https://github.com/danbri/factoidal/issues/801; an XPASS makes the run
exit 1.

| xfail case | Open item | What the case asserts |
|---|---|---|
| `triple-form-in-mixed-catalog` | Source content constraints. A triple-form capability covers every triple pattern. In a catalog with other kinds, a plan that reads a pattern from a source that holds none of its triples is sound and gives fewer answers. The mixed cases use predicate-form capabilities only (`partitioned`). | with triple-form capabilities in a mixed catalog, every plan of the family gives the reference answers |
| `facadex-json` | Façade-X mapping of JSON (and of XML and other formats) | `describe` accepts a `.json` location |
| `rest-two-path-parameters` | A REST operation with two required inputs | `describe` accepts it |
| `mcp-two-required-inputs` | An MCP tool with two required inputs | `describe` accepts it |
| `tool-without-rdf-mapping` | MCP and WebMCP tool declarations with no `_meta` mapping: a mapping made from the output schema, Façade-X style | `describe` accepts a plain tool declaration |
| `sparql-endpoint-over-http` | A SERVICE call over HTTP (`SPARQL/ProtocolClient.lean`) | the call with no mock endpoint map answers |
| `service-description-fetch` | Fetch of the service description from the endpoint IRI | `describe` with no document text gives capabilities |
| `sql-source-kind` | SQL engines as a source kind | `sql` is an implemented kind |

Other limits, with no case yet: the cost models are fixed numbers or
proxies, not measurements; `perCall` of an SBM11 keyed scan does not come
from the block metadata; the test generation has the default graph only
(`named-graph-requirement` in section 9 covers requirements with GRAPH).

## 11. KR 2.4: execution state machine

Landed 2026-10-13 for OKR batch 2, KR 2.4
(https://github.com/danbri/factoidal/issues/801). Modules
`formal/lean4/L4Factoidal/Planner/Exec.lean` (the state machine, its
invariants, termination and the driver) and `Planner/ExecTests.lean`
(`#guard` cases and the axiom audit). Test cases in
`Harness/PlannerTest.lean`, run by `lake exe l4planner-test`. The KR asked
first for an evaluation of Veil as the framework (section 4); the state
machine is in plain Lean, so the KR does not wait on that decision.

### Veil evaluation

Checked 2026-10-13 against Veil `main` at commit `529eb3bd` (2026-10-12),
cloned with `git clone --depth 1 https://github.com/verse-lab/veil.git`,
and its pinned dependencies `lean-smt` (branch
`v4.32.0-veil-no-mathlib`, commit `922af463`) and `lean-cvc5` (commit
`a3ffc29a`). The clones and the cvc5 release probe below worked through
this container's proxy.

| Check | Evidence | Result |
|---|---|---|
| Toolchain | Veil's `lean-toolchain` is `leanprover/lean4:v4.32.0`; this tree's is `v4.33.1`. Every dependency in Veil's `lakefile.lean` is pinned for v4.32.0: `batteries` and `aesop` at tag `v4.32.0`, `lean-smt` at `v4.32.0-veil-no-mathlib`, `Loom` at `v4.32.0-for-veil`, plus `ProofWidgets4`, `VerifiedHAMT`, and inherited `Qq`, `lean-auto`, `lean-cvc5`. `git ls-remote --heads --tags`: no v4.33 branch or tag in `verse-lab/veil`, `verse-lab/lean-smt` or `verse-lab/loom` (only `v4.32.0-veil*` and `v4.32.0-for-veil*`); `batteries` and `aesop` have `v4.33.0`. Lake builds every package of the workspace with the root package's toolchain. | Fails. A Lake dependency on Veil needs this tree on v4.32.0, or a port of Veil, Loom and lean-smt to v4.33.1. A trial build of Veil under v4.33.1 was not run: it fetches and builds Veil and its nine dependencies, several GB on a disk shared by other sessions (4.4 GB free). |
| Proofs from SMT | `register_option veil.smt.trust` has `defValue := true` (`Veil/Base.lean:144`). With trust, lean-smt closes the goal with `mv.admit (synthetic := false)` (`Smt/Tactic/Smt.lean:246-251`), which is `sorryAx`; Veil counts such goals as `proofHasSorry` and warns "Trusting SMT solver for N goals" (`Veil/Frontend/DSL/Module/Elaborators/Verification.lean:160-166`). With `set_option veil.smt.trust false`, cvc5 produces a proof and lean-smt reconstructs a Lean term that the kernel checks, with three exceptions: a proof step with no reconstructor becomes a new goal (`addTrust`, `Smt/Reconstruct.lean:200`; `replaceMainGoal mvs`, `Smt/Tactic/Smt.lean:445`); the reconstruction lemma `geq_tighten` for rationals contains a `sorry` (`Smt/Reconstruct/Rat/Rewrites.lean:58-59`), so a proof that uses it depends on `sorryAx`; and `native := true` adds `Lean.ofReduceBool` (`Smt/Reconstruct/Builtin.lean:294`; Veil does not set it). Veil's check of a theory against its assumptions defaults to `first \| decide \| native_decide` (`Veil/Frontend/DSL/Module/Elaborators/Core.lean:623`). | Fails by default. With `veil.smt.trust false` a theorem can pass this tree's rule (`#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only), but only `#print axioms` on each theorem shows it; no goal was run here. |
| Dependencies | Veil 1.0 (tag `v1.0.0`, Lean v4.15.0; the CAV 2025 version) needed a `z3` binary, a `cvc5` binary and the Python packages `z3-solver`, `multiprocess`, `sexpdata` (its `README.md`, items 3-5). Current `main` needs no z3, no Python and no uv: `lean-cvc5` downloads static cvc5 1.3.2 libraries at build time from `https://github.com/abdoo8080/cvc5/releases/download/cvc5-1.3.2/cvc5-Linux-x86_64-static.zip` (its `lakefile.lean:21-75`; `curl -I -L` gives HTTP 200 here) and needs `clang`, `lld`, `libc++` (Veil `README.md`, "Build"); the `Veil` library target needs Node.js and npm (`needs := #[widgetJsAll]`, which runs `npm clean-install` and `npm run build`). | CI (danbri/factoidal-builds, GitHub-hosted runners with clang and Node) can install these, with network access to GitHub release assets. This tree has no Lake dependency today (`lake-manifest.json`: `"packages": []`). The wasm build compiles the modules its roots import; a Veil-based module would have to be in a separate Lake library that no wasm or executable root imports. |
| Network | `git clone` of the three repositories and the `curl -I` probe succeeded. | No block. |

Decision: Veil is not added to `lakefile.lean`. Two of the three checks
fail. The decision is for the owner. Options: (a) keep the planner's
state machines in plain Lean, as this landing does; (b) a separate
proof-only Lake project on v4.32.0, outside the library and the wasm
build, for Veil's model checking and SMT runs over a copy of the state
machine, with no theorem record entry unless `veil.smt.trust false` and
`#print axioms` pass; (c) wait for a Veil release on v4.33.

### State, actions, Next

TLA+ form: `Init`, one predicate per action on a pair of states, and
`Next`, the disjunction of the eight actions.

| Part | Lean | Content |
|---|---|---|
| State | `Exec.State` | current plan (a `Rewriting` of the family), the alternatives not yet tried, the step index, `pending` (rows of the plan prefix that still need a call of the current access), `next` (rows the access gave so far), the call phase (`idle`, `waiting`, `failed`), retries of the current call, `calls` (call count per catalog index), the output, the status (`running`, `done`, `stopped`), the number of switches. Rows carry the approximation marker of `Plan.exec`. |
| Init | `Init fam` | the first plan of the family, the others as alternatives, the empty solution mapping pending, no calls. |
| Call | `Call` | call the current access for the head pending row: only when every required input is bound in the row (`Access.inputs?` gives a value) and the source's call quota is not exhausted (`quotaOk`); the call is counted. |
| Receive | `Receive` | the call answers with the source implementation's tuples; the rows they give, exactly as `Plan.exec` gives them for the access, are added to `next`. |
| Fail | `Fail` | the call fails (environment action). |
| Retry | `Retry` | call again after a failure: at most `Config.maxRetries` times for one row, and only within the quota; counted. |
| Advance | `Advance` | no pending row is left: the next access runs over `next`. |
| Adapt | `Adapt` | choose any alternative of the family and start it from the empty mapping; the call counts are kept. |
| Finish | `Finish` | after the last access: the requirement's filters and projection (`finalRows`); status `done`. |
| Stop | `Stop` | status `stopped`, no output. |

`Adapt` and `Stop` are enabled in every running state: the invariants hold
for any choice inside the family. The driver `stepExec` chooses one
enabled action: it calls when it can, takes the fault schedule
(`faults i n`: call `n` of source `i` fails) for the environment, retries
within the bound, and switches to the first alternative, or stops, only
when the current call cannot be made (an input unbound, the quota used
up, the retries used up).

### Theorems (`Exec.lean`)

| Theorem | Statement | Status |
|---|---|---|
| `init_inv`, `next_inv`, `reachable_inv` | `Init → Inv`; `Inv ∧ Next → Inv'`; every state of a trace from `Init` by `Next` satisfies `Inv` (induction on traces, `Reachable`). | Proved. |
| `reachable_sound` (I1) | Under `ExactSourcesSound` and the rewriting check of each family member, every unmarked output row of a reachable state is, as a partial function, an answer of the requirement over the declared graph. From `rewriting_sound`. | Proved. |
| `reachable_quota` (I2) | In a reachable state, no source's call count exceeds its call quota. | Proved. |
| `reachable_output` | When the status is `done`, the output IS the run (`Plan.run`, as a list) of the current plan, and that plan is a member of the family. The machine loses no answer of the plan it finishes with, and adaptation stays inside the family. | Proved. |
| `reachable_unmarked_of_allExact` | With only exact sources, no output row is marked. | Proved. |
| `next_measure_lt`, `next_wf` | Every action decreases the measure (status, alternatives left, accesses left, pending rows, retries left, phase) in the lexicographic order, so `Next` has no infinite chain. | Proved. |
| `stepExec_next`, `runFrom_reachable`, `runFrom_final` | Each driver step is a `Next` step; the driver's states are reachable; the driver ends with `done` or `stopped`. `runFrom` is defined by well-founded recursion on the measure and compiles to a loop (`goto _start` in the emitted C). | Proved. |
| `run_spec` | For `run` over the family of `search`: the status is `done` or `stopped`, I2, I1, and a `done` output is the run of a member of `search`'s result. | Proved. |

The inductive invariant `Inv`: the plan and the alternatives are members
of the family; `Frontier` (the rows of the plan prefix before the
current access are the processed rows `P` followed by `pending`, and
`next` is what the access gave for `P`; after the last access, `pending`
is the whole run of the access chain); the output is the plan's run when
`done` and empty otherwise; I2; `retries ≤ maxRetries`; a call in flight
has every required input bound (`InflightOk`).

Check against anti-pattern 29: the hypotheses of `reachable_sound` are
the soundness of each exact source against its declared extension, the
Boolean rewriting check of each family member (`family_check` discharges
it from `search_check`), and reachability from `Init` by `Next`. None
mentions the output or `Requirement.answers`. `next_inv` takes `Inv` of
the earlier state, which is the induction step; `init_inv` is its base.

`#print axioms` for the thirteen theorems of `Planner/ExecTests.lean`:
`propext`, `Classical.choice`, `Quot.sound` only. No `sorry`, no
`native_decide`, no `partial`, no user `axiom`, no `import Std`, no raised
heartbeats. `lake build` of the module: 1.7 s.

### Tests

`#guard` (`Planner/ExecTests.lean`, over the catalog of
`Planner/Tests.lean`): the run gives the reference answers with 1 call of
the scan and 2 of the lookup; with a call quota of 1 it stops after 1
call with no output; a failed first call is retried (3 calls) and the
answers are the reference; with no retry allowed the failure stops the
run; approximate rows are marked.

`lake exe l4planner-test`, cases of KR 2.4:

| Case | Catalog | Checks |
|---|---|---|
| `exec-quota-stops` | scan, lookup with call quota 1 | the static first plan exceeds the quota; the run stops, 1 call of the lookup, no output |
| `runtime-quota-adaptation` | scan, lookup with call quota 1, name scan | the run switches plan and gives the reference answers within every quota (the KR 2.2 expected failure, now an assertion) |
| `exec-failure-adaptation` | scan, lookup whose every call fails, name scan | 2 calls of the lookup (call and retry), 1 switch, reference answers |
| `exec-retry-succeeds` | scan, lookup; call 1 fails | no switch, 4 calls of the lookup, reference answers |
| `exec-retry-bound-stops` | scan, lookup; call 1 fails; `maxRetries := 0` | stopped, no output |
| `exec-approximate-marked` | scan, LLM-like age source | every output row marked |
| `exec-exact-before-approximate` | scan, LLM-like and exact age sources | reference answers, unmarked |
| `exec-not-answerable` | object lookup only | no plan family, no run |
| `exec-equals-plan-run` | the 18 answerable KR 2.2 cases whose first plan is within the quotas | the output equals the first plan's `Plan.run` rows (same list), no switch |

Each case also checks that every call count is within its quota.

Result 2026-10-13: planner: 67 pass, 0 fail, 17 expected-fail (out of
84). KR 2.2 part: 25 pass, 0 fail, 6 expected-fail (out of 31); KR 2.3
part unchanged: 33 pass, 0 fail, 9 expected-fail (out of 42); KR 2.4
part: 9 pass, 0 fail, 2 expected-fail (out of 11).

### Open, with expected-failure cases

Each is an `xfail` in `Harness/PlannerTest.lean` that names
https://github.com/danbri/factoidal/issues/801; an XPASS makes the run
exit 1.

| xfail case | Open item | What the case asserts |
|---|---|---|
| `exec-row-quota` | `CostModel.rowQuota` is not enforced at run time. Assertion since KR 4.2 (section 13) | a scan with a row quota of 1 that answers 3 rows gives at most 1 row, or the run stops |
| `exec-reuse-after-adaptation` | After a switch the new plan makes again the calls whose answers are known (no cache of call results). Assertion since KR 4.2 | in the `runtime-quota-adaptation` run the scan is called once |
| `quota-in-admission` (section 9) | Quotas are not used for admission, so the first plan can be one that the run must leave. Assertion since KR 4.2 | no plan in the admitted family exceeds a call quota |
| `exec-driver-io` (section 12, https://github.com/danbri/factoidal/issues/933) | The driver `Exec.run` takes tuples from `Source.sem.impl` and failures from a fault schedule | `Exec.run` makes its calls through IO; a call error is a `Fail` step |

Other limits, with no case yet: the driver took the alternatives in
family order, without measurements, until KR 4.2 (section 13); there is no fairness condition and no temporal property beyond
termination (the assume-guarantee composition of skill rule 10).

## 12. KR 4.1: plans executed through IO

Landed 2026-10-22 for OKR batch 3, KR 4.1
(https://github.com/danbri/factoidal/issues/875). The case
`sbm11-io-at-call-time` (sections 10 and 11) is an assertion now.

### Definitions (`formal/lean4/L4Factoidal/Planner/ExecM.lean`)

| Name | Meaning |
|---|---|
| `Calls m` | `Nat → InputBinding → m (List Tuple)`: a call of catalog source `i` with an input binding, in monad `m` |
| `accessRows` | the rows of one access for the tuples a call returned; the access case of `Plan.exec` is `accessRows` over `s.sem.impl inp` (`exec_access_eq`, by `rfl`) |
| `Plan.execM`, `Plan.runM` | the plan run in `m`: each access calls `call`; joins run the right side once per left row (`flatMapRowsM`: core `List.mapM`, then `flatten`), then filters, projections, unions as in `Plan.exec`. The catalog gives the capability, the mapping and the tuple check; `sem` is not read. |
| `CallsDenote cat call` | every call of source `i` returns `pure (s.sem.impl inp)` for the catalog's source `i` |
| `pureCalls` | the calls that answer from the catalog's implementations |

`Plan.exec` stays the specification.

### Theorems

| Theorem | Statement |
|---|---|
| `execM_eq_exec` | In a lawful monad, `CallsDenote cat call → p.execM cat call r = pure (p.exec cat r)`, for every plan `p` and row `r` (induction on the plan) |
| `runM_eq_run` | the same for `runM` and `run` |
| `runM_sound` | with `CallsDenote`, `ExactSourcesSound` and `IsRewriting`: `runM` returns `pure (p.run cat)` and `SoundFor cat req p` (`rewriting_sound`) |
| `flatMapRowsM_pure` | the monadic `flatMap` returns `pure (xs.flatMap g)` when each `f x = pure (g x)` |
| `pureCalls_denote` | `pureCalls` satisfies `CallsDenote` |

The hypothesis `CallsDenote` is about one call of one source; the
conclusion is about every plan (hazard 29 checked: no premise contains the
conclusion). `#print axioms` for each: `propext`, `Classical.choice`,
`Quot.sound` at most (`Planner/ExecTests.lean`). `#guard`s there run the
KR 2.1 plan in `StateM Nat` (calls counted: 1 of `knows`, 2 of `people`;
rows equal to `Plan.run`) and in `Id` with `pureCalls`.

For `IO` the hypothesis is not a theorem: a call reads file bytes. It is
tested.

### SBM11 through IO (`formal/lean4/Harness/PlannerSbm11IO.lean`)

`idPathCalls ss m ds` gives the calls of a catalog made from the SBM11
capabilities `ds`, in `ExceptT String IO`. A call is the keyed scan of the
capability's permutation (key: the input values in the permutation's column
order, through `Session.idOf`; a value with no id gives no tuple), keeps the
default-graph rows (graph id 0), and returns them as tuples of the
capability's mapping. `runIO` runs a plan with these calls and reports the
PRB1 bytes read during the run (`Session.frameBytes`).

`l4planner-test sbm11-query GEN QUERY.rq [--check-pure]`: the query to a
requirement (`Requirement.ofQuery?`; exit 3 when refused or when there is no
plan), the triple-form catalog of the generation (no predicate probe, so no
bytes are read before the run), the first plan of `search`, the IO run,
SPARQL Results JSON on standard output. Literal constants of the BGP get
the store's language-tag folding (`normalizeTerm`), so a constant equals
the term the id path returns. Without `--check-pure` the catalog's `sem` is
the graph source over the empty graph: `search` and `execM` do not read it,
and the generation is not materialised. With `--check-pure` it is the
default graph read by a full SPO scan, and the run fails when the IO rows
differ from `Plan.run`.

Fix found by the gate: `Requirement.ofQuery?` kept a query blank node as a
constant, and a plan used it as a key (`ids-bnode.rq`: 0 rows; `l4sbm11
query`: 3). It now renames `_:b` to the variable `_:b` (SPARQL 1.1 Query
§4.1.4; no SPARQL variable name contains `:`), not projected by `SELECT *`.

### Tests

| Test | What it checks |
|---|---|
| `sbm11-io-at-call-time` (`l4planner-test`, `Harness/PlannerKinds.lean`) | the hypothesis of `execM_eq_exec` for the 16 capabilities of the test generation and every sampled input (34 calls: IO tuples equal the pure implementation); for 4 requirements, every plan of the family (15 plans) run through IO reads PRB1 bytes during the run and gives the rows of `Plan.run` (multisets) |
| `execm-io-large-join` (`l4planner-test`) | `Plan.execM` in `ExceptT String IO` over a join whose left side gives 1,000,000 rows completes with every row (stack use; `execM` is in `tools/lean-tail-recursion-allow.txt` as plan-tree nesting) |
| `tests/planner/sbm11_gate.sh` | `tests/sbm11/gate/gate.nq` packed and activated; each `tests/sbm11/gate/*.rq` the planner accepts run through IO with `--check-pure`, PRB1 bytes read during the run, answer equal to `l4sbm11 query` (`tests/sbm11/compare_answers.py`) |

Result 2026-10-22: planner: 70 pass, 0 fail, 18 expected-fail (out of 88);
planner-sbm11-gate: 8 pass, 0 fail (out of 8 accepted); 105 not accepted.
The gate queries that are not accepted use FILTER (`rowfilter-from-expr`),
GRAPH (`named-graph-requirement`), modifiers, aggregates, OPTIONAL or other
forms outside `ofQuery?` (section 9).

### Open, with expected-failure cases

| xfail case | Open item | Issue |
|---|---|---|
| `exec-driver-io` | The driver `Exec.run` (section 11) takes tuples from `Source.sem.impl` and failures from a fault schedule; a driver whose `Call`, `Receive` and `Fail` steps are IO calls is open | https://github.com/danbri/factoidal/issues/933 |
| `rowfilter-from-expr` (section 9) | FILTER is not accepted, so most gate queries are not run by the planner | https://github.com/danbri/factoidal/issues/801 |

## 13. KR 4.2: run-time adaptation

Landed 2026-10-22 for OKR batch 3, KR 4.2
(https://github.com/danbri/factoidal/issues/875). The cases
`exec-row-quota`, `exec-reuse-after-adaptation` (section 11) and
`quota-in-admission` (section 9) are assertions now.

### Admission (`Planner/Search.lean`)

`CostModel.rowsPerCall` is an optional statistic of a source (tuples per
call). `estUse cat em steps` walks a chain and gives, for each access, the
source, the estimated calls, tuples and cost; `EstModel` says how it counts
(`statModel fanout`: the statistic, or `fanout` per new variable, and
`perCall`). `estCost` is the total of `estUse` under `statModel` (the same
numbers as before when no source has a statistic). `admissible` holds when
the estimated calls and tuples of each source are within its call quota and
row quota (`withinQuotas`). `searchAdmitted` is `search` filtered by
`admissible`; `search` stays the structural family, so `search_complete`
keeps its statement. The driver runs `searchAdmitted`.

Effect: without a statistic the estimate is large (fanout 10 per new
variable), and a plan with a quota source after a scan can be refused. The
KR 2.2 case `approximate-marked` (LLM source, call quota 10, after a scan
with no statistic) has no admitted plan; `exec-equals-plan-run` now covers
17 cases, not 18. The run-time quota checks stay: a statistic that is too
low admits a plan that the run must leave. The refusal of a plan that fits its
quota is open: https://github.com/danbri/factoidal/issues/937, xfail
`admission-without-statistic`.

### State, actions (`Planner/Exec.lean`)

| Change | Content |
|---|---|
| State | the observed-cost record `answered`, `rows` (tuples received; the row-quota count), `latency` (sum of the latencies of answered calls), all by catalog index; `cache : List CacheEntry` (source, input binding, tuples); `hits` |
| `Receive` | enabled only when the tuples are within the row quota (`rowQuotaOk`); takes the latency `lat` from the environment; updates the record and adds the cache entry |
| `Hit` (new, ninth action) | the head pending row's call (source, input) is in the cache: its rows are added to `next` with no call |
| `Config` | `fanout` for the estimate |
| driver | a `Latency` schedule (`lat i n`) beside the fault schedule; a cache hit before a call; an answer over the row quota leads to a switch or a stop; a switch takes the alternative of least `adaptScore` |

`adaptScore` (no theorem uses it): `estUse` under `obsModel`, which takes
the measured tuples per call of a source that has answered, the measured
latency per answered call at the source's location as the call cost
(`perCall` before an answer there), zero calls for an access whose
constant-only call is in the cache, and one call for a constant-only access
(the later rows are hits). The score is (0 if the estimate added to the
calls and tuples already used is within every quota, else 1; the total
cost), compared lexicographically; ties keep the family order.

### Theorems

| Theorem | Statement |
|---|---|
| `reachable_sound` (I1), `reachable_quota` (I2) | as in section 11, for the new machine |
| `reachable_rowQuota` (I2, rows) | in a reachable state, no source's tuple count exceeds its row quota |
| `reachable_cache` | every cache entry of a reachable state is the call's result: `e.tuples = s.sem.impl e.inp` for the catalog's source `e.src` |
| `reachable_cache_hit` | the rows of a cache hit (`accessRows s a x e.tuples`) are `(Plan.access a).exec cat x`, the rows of the call: the cache never changes an answer |
| `cache_rows_eq`, `frontier_pop`, `exec_access_of`, `rowQuota_add` | lemmas of the above |
| `pickMin_mem`, `cacheFind_some` | the driver's choice is a member of the alternatives; a cache lookup returns a matching entry of the cache |
| `searchAdmitted_mem` | an admitted plan is a member of `search` and admissible |
| `run_spec` | now with the row quota, the cache, and the admitted family |

Hazard 29: the hypotheses of `reachable_cache_hit` are reachability and
that the entry, the access and the input match; none states that the
cache gives the rows of `Plan.exec`. The cache invariant is a field of
`Inv`, proved by induction on traces (`init_inv`, `receive_inv`,
`hit_inv`). `#print axioms` for each new theorem: `propext`,
`Classical.choice`, `Quot.sound` at most (`Planner/ExecTests.lean`).

### Tests

`lake exe l4planner-test`, new and changed cases:

| Case | Checks |
|---|---|
| `quota-in-admission` | `search` keeps the plan over the quota; `searchAdmitted` drops it; with a quota of 1000 it is admitted; no admitted plan, no run |
| `exec-quota-stops`, `runtime-quota-adaptation` | as in section 11, with a scan whose statistic is too low (1 tuple; it answers 3) so that the plan is admitted |
| `exec-row-quota` | a scan with a row quota of 1 answers 3 tuples: the run stops, no output, no tuple counted |
| `exec-row-quota-adaptation` | the same scan and another scan: one switch, the other scan, reference answers |
| `exec-reuse-after-adaptation` | after the switch the scan is not called again (1 call) and the new plan starts with a cache hit |
| `exec-cache-duplicate-input` | two rows need the same lookup: 1 call, 1 hit, reference answers |
| `exec-adapt-measured-rows` | a scan declares 1 tuple and answers 20; the quota lookup is left after 2 calls; the second admitted plan (control) uses the other lookup, but the driver, from the measured 20 tuples, takes a plan with the name scan: calls [1, 2, 0, 1] |
| `exec-adapt-measured-latency` | calls at `host-b` take 1000 units: the driver takes lookup C (`host-c`); with no latency it takes lookup B (`host-b`, lower static cost) |
| `exec-approximate-marked`, `exec-exact-before-approximate` | with the scan's true statistic (3 tuples), so that the LLM plan is admitted |

`#guard`s in `Planner/ExecTests.lean`: admission refuses the call-quota
plan with no statistic; with a statistic that is too low the run stops
after one call; the observed-cost record after a run.

Result 2026-10-22: planner: 77 pass, 0 fail, 16 expected-fail (out of 93).
`tests/planner/sbm11_gate.sh`: 8 pass, 0 fail (out of 8 accepted); 106 not
accepted (one gate query more than in section 12).

### Open

- Admission with no statistic refuses a plan within its quota
  (https://github.com/danbri/factoidal/issues/937, xfail
  `admission-without-statistic`).
- The driver over IO calls (https://github.com/danbri/factoidal/issues/933,
  xfail `exec-driver-io`): not in this landing. The cache and the
  observed-cost record are in the pure state, so an IO driver can keep them.
- No theorem about costs or about the choice of the alternative; the
  invariants hold for any choice inside the family.
