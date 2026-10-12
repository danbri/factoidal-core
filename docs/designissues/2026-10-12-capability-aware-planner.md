# Capability-aware, cost-based planner for data access, computation and service interaction

2026-10-12. Status: direction set by the owner. KR 2.1, 2.2 and 2.3 landed (sections 8, 9, 10).

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
| `quota-in-admission` | Costs and quotas are not used for admission; no theorem about cost | no plan in the family exceeds a call quota |
| `runtime-quota-adaptation` | Adaptation: no execution state machine; quotas are not enforced at run time | the run of the first plan stays within each call quota and gives the reference answers |
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
| `sbm11-io-at-call-time` | `CapSemantics.impl` is a pure function, so a plan over SBM11 reads rows that were decoded before the run. An IO implementation (the disk-resident id path at call time) is open. | `Plan.exec` reads PRB1 bytes during the run |
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
