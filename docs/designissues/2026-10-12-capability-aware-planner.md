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
