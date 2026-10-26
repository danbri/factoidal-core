> Provenance: a proposed revision of https://github.com/danbri/factoidal/issues/975, written in a ChatGPT conversation and supplied by the owner on 2026-10-23 as `factoidal-corpus-coherence-975.md`. It is input to issue 975, not adopted text. Owner statements in it other than the two quoted steers were not checked against a dated owner message.

# Corpus coherence: immutable artifacts and typed dataflow across the Lean system (before bridge work)

Proposed revision for [factoidal#975](https://github.com/danbri/factoidal/issues/975).

## Owner steers (verbatim)

2026-10-23: "I want this coherence before we start bridging to other definitions, or worry excessively about perf and API surfaces."

2026-10-23, later: "perhaps it is overly concerned with "storage"; the issue infests the whole system. We have a set of abstract spec-driven concepts but these are left disconnected from the realities of a software data system with real world information flowing through it. Some representation of that data flow and the integration of all the lean-powered parts is needed, parsers, stores, reasoners, whatever."

Further owner clarifications: think of a **corpus**, with hot/cold indexes and rich metadata relating files, documents and graphs through derivation patterns; take an **FP outlook in which artifacts never change as such**.

This issue comes BEFORE bridge work to external RDF Semantics formalisations (the Dickory clean room), and before new performance or API work. Performance work that does not change a component's contract is not blocked. Internal connections between Factoidal's own definitions and execution paths are the substance of this issue.

## Problem

The Lean tree has spec-level definitions (RDF Semantics, SPARQL algebra, RDFS/OWL/RIF rules, SHACL) and many working components (parsers, serializers, stores, dictionaries, the planner, reasoners, the proof checker, crypto). Each component has its own local theorems, against its own types. The existing connections do not yet form a common account of how data flows from bytes at the system boundary through these components to an answer, what each step guarantees about that data, and where the guarantee is only tested or assumed. A defect at a hand-over can therefore escape the local theorems of both components. Examples from 2026-10-21 to 2026-10-23:

- parsers kept a repeated triple although `Graph.add` had set semantics (fixed: https://github.com/danbri/factoidal-core/pull/26, https://github.com/danbri/factoidal-core/pull/28);
- `proofCheck` joins raw blank-node labels across two graph artifacts (https://github.com/danbri/factoidal/issues/976);
- dictionary representations disagree on language-tag case; the connection between representation equality, RDF identity, matching and deduplication must be explicit (https://github.com/danbri/factoidal/issues/977);
- `StoreCaps`, the interface the planner calls, has no denotation (details in Phase B).

## Corpus first: immutable artifacts, views and materialisations

The corpus organises files/documents, graph/dataset snapshots, programs, queries and derived artifacts, together with persistent metadata about their relationships. It need not fit into one resident database or be indexed in full.

**Artifacts are immutable values.** Editing a document, applying an update, changing a rule program or revising a derivation produces a new artifact/version. A name such as “latest”, a branch, a working view or a location may change what it refers to; proofs and reproducible computations pin the resolved artifact. Updating a corpus catalogue produces a new logical snapshot, even if its physical implementation uses mutable structures.

Keep content identity, scoped interpretation and observation identity distinguishable. The same bytes can be observed twice or parsed under different base IRIs or blank-node scopes. A canonical RDF digest identifies content modulo its canonicalisation relation; it does not supply a mapping between raw term coordinates.

A query dataset is an **explicit view** assembled from selected corpus snapshots under a declared interpretation, graph-selection and scope policy. Corpus membership does not implicitly assert all graphs or combine them into one global dataset. Whole named graphs and datasets are first-class flow values.

### Indexes and bounded working sets

- Artifact identity and meaning are independent of access state. Content may be local, remote, archived or temporarily unavailable; indexes may be hot, cold, partial, stale or absent.
- An index/materialisation records its input snapshots, semantic configuration, coverage and construction recipe. Where inputs and reconstruction are retained, it is rebuildable derived data. Incremental construction/update produces new index snapshots; mutable cache residency belongs to execution state.
- Loading, streaming, warming, cooling, eviction and rebuilding change access capabilities and cost; they preserve the meaning of the selected unchanged corpus view.
- Coverage is query-relative. A cold, missing, partial or stale index cannot establish that data is absent. Retrieve, scan or build the required coverage, or return an explicit refusal/qualified partial result.
- Evicting an index preserves corpus identity and derivation references. Reclaiming the last copy of an artifact or evidence is a separate retention action; unavailability must remain visible.
- A new source version can make an index unsuitable for a query requesting that version. It does not invalidate a correct historical proof about the old pinned snapshot.

These are lifecycle and semantic contracts for bounded working sets, not a requirement to build a new distributed performance engine in this issue.

### Derivation metadata

Distinguish a reusable **recipe/pattern**, a particular **run**, the **claim** about its inputs and outputs, and the **evidence** supporting that claim. A recipe has not necessarily run, and an execution record is not automatically a proof.

Record both prospective dependencies (“this view can be built from these inputs”) and historical derivations (“this output was produced from these exact versions”). Pure transformations take explicit input artifacts, parameters, implementation/profile versions and captured effect inputs. Reuse/memoisation must bind all semantic dependencies. Alternative derivations may support the same output without changing its content.

## The model: a dataflow of stages with contracts

1. **Typed values.** A small initial vocabulary: captured bytes/documents; graph/dataset snapshots and views; query solution bags/sequences; state transitions; derivations/evidence; validation reports. RDF representations share a common abstract dataset meaning. Other values have their own semantic domains; a query result or parse event is not another RDF dataset by default.

2. **Stages and concrete bindings.** A stage has typed input/output ports, context, outcomes and an independently stated semantic relation. Bind its contract to the implementation actually invoked. A parser relates a source document to its interpretation; normalisation preserves membership/names; a store refines a selected graph; a reasoner establishes entailment; a query establishes evaluation; an update establishes a transition; an encoder establishes the preservation/projection its format supports. A set-invariant theorem alone is not parser correctness.

3. **IO boundaries.** Capture file/socket/service observations and relevant clock/host inputs so the pure portion can be replayed. An observation records what was obtained, not the truth of every assertion obtained. Name environmental assumptions such as `ReadsWritten`, and separately identify unresolved IO-to-pure-model or FFI connections.

4. **Composition.** Compose stage contracts through the *same* intermediate artifacts and compatible context/scope. A schematic shape is:

   ```lean
   step_sound :
     Preconditions ctx input →
     run ctx input = .ok output →
     RepresentsIn ctx input a →
     ∃ b, RepresentsOut ctx output b ∧ StepMeaning ctx a b
   ```

   Prove the composite statement for actual call paths. Internal bridge obligations must be discharged for the claimed fragment; assumptions are exposed, not silently renamed “IO assumptions”. The declared contract must not merely restate the implementation's answer.

5. **Context, scope and outcomes.** Bind syntax, base IRI, semantic profile, graph selection, dictionary generation and evaluation environment. Preserve blank-node sharing across an entire dataset, including graph names and nested RDF 1.2 triple terms; separate independent input scopes. Decode errors, unsupported operations, incomplete searches and invalid certificates remain distinct outcomes. Equal raw IDs/labels/digests do not substitute for checked transport.

6. **Expandable structure.** A corpus-level operation can consume/produce whole graphs and expand into its exact rule applications and premises. Distinguish dataflow, execution history and proof dependencies. Iterative execution may have cycles; finite proof dependencies must be well founded. Multiple proofs of a triple must not inflate RDF membership or SPARQL multiplicity.

7. **Generated inventory.** Generate the inventory from checked stage declarations in the Lean sources (anti-pattern 30), rather than maintain a hand-written list. Include concrete entry function, typed values, abstract relation, context, theorem/checker, hypotheses, tests, supported fragment and gap. Track proved/tested/assumed/missing *per obligation*. A theorem-name string or adapter label alone is not a proof binding.

## Work, in phases (each step: tests first, one PR)

**Phase A: the frame.**

- A0. Corpus artifacts, versioned views, recipe/run/claim/evidence records, and index coverage/residency contracts. Include an immutable logical model with explicit mutable names and effect boundaries.
- A1. The common extensional dataset target and graph projections: triple membership, graph-name registry including empty graphs, unique names, and applicable finite-support conditions. Connect it to `Dataset.memQuad`, `Dataset.IsSet` and `CertifiedDataset`. State RDF term identity from the spec and connect `Term.eqb`/`Triple.eqb` and key-based invariants to it; distinguish datatype value equality and blank-node isomorphism. Preserve RDF 1.2 terms. **[Core PR #34](https://github.com/danbri/factoidal-core/pull/34) is now merged.** It introduces `DatasetDen`/`Dataset.den` and initial representation bridges; continue from that work. Its remaining `HeldFolded`, manifest/empty-graph and harness hypotheses are still explicit obligations.
- A2. Reuse `DictInjective` (merged: https://github.com/danbri/factoidal-core/pull/32, main `a3ccec60`). This proves representation-level round trips/injectivity for checked SBM11 base, the pure overlay dictionary model and IndexedBlock; SBM11 also has `cid_eq_iff_eqb`. Common RDF identity, other dictionaries and IO session correspondence remain obligations in A1/B4.
- A3. The stage/contract/composition types, and the inventory generator, with the first entries filled from what exists.

**Phase B: stores (the original scope of this issue).**

- **B1. Lawful graph and dataset capabilities.** `StoreCaps` is graph-scoped; give it a graph denotation/projection and `solveExact`: returned triples are exactly the denoted matching triples, with no duplicates under the selected RDF identity. `DatasetCaps` additionally needs exact default/named lookup and graph-name enumeration, including empty graphs. Declare the domain/adapter for its current IRI-only named interface so blank-node graph names do not silently disappear.
- Preserve the five existing `StoreCapsLawful` laws with their conditions. Exact estimates are required only when advertised; approximate estimates are hints. Predicate-presence `false` must prove absence; conservative `true` is allowed. Successful `distinctPredicates` enumeration is exact and duplicate-free for the selected graph; unsupported/failed enumeration requires fallback. Exact reads need a complete-read guarantee or explicit error outcome.
- **Union and overlay laws are different.** A graph union denotes set union even when inputs overlap; solve/count/LIMIT must agree on deduplication. A delta overlay denotes application of the ordered update log, including deletion, clear, drop and create. Preserve graph existence separately from triples. Reuse `StoreDeltaMerge.mergeOnRead_matches_applyEntries` and SBM11 overlay theorems.
- Concrete obligations at reviewed core `a3ccec607d1187077250f5fe79b075f169bceb3d`: `unionSolve` concatenates and `unionCountExact` sums counts; fix their set-union contract and overlap-aware LIMIT. `overlay` copies an indexed base's `estimateIsExact = true` while its deletion fixture has estimate 2/count 1; make the flag or estimator satisfy the actual law.
- Cover `capsOfIndexed`, `capsOfCottas`, `capsOfReadOps`, `capsOfList`, `capsOfBackend`, `capsOfBackendList`, `capsOfRmlSource`, unions and overlays. Connect SBM11's `Store Id` to this abstraction (its files → memory store → input-dataset chain has PRs 27/31, under `ReadsWritten`). Define denotation from the represented state/input; agreement defined solely from `solve` is insufficient. Conditional reader-contract theorems need separately discharged concrete adapters.
- **B2. Planner refinement.** Restate `Storage/PlannerSoundness.lean`/`SPARQL/StoreBackend.lean` against lawful graph/dataset records. Preserve SPARQL solution multiplicities. Use bag equality where order is unspecified and the appropriate sequence/slicing relation where it matters; an unordered dataset does not fix one arbitrary LIMIT/OFFSET result. Resolve current `hneE`/`hneS` assumptions excluding empty named graphs. Prove coverage sufficient for the selected query, independently of index residency.
- **B3. Identity transport.** Make scope part of A1/A3 from the start. At a representation boundary, preserve terms exactly or supply a consistent mapping, bijective on the occurring blank nodes. Apply it across graph names, contents, nested triple terms and affected bindings. Numeric encoding does not inherently require blank-node renaming.
- **B4. Dictionaries.** Continue https://github.com/danbri/factoidal/issues/977 and add the missing instances for IBK5, PTD, TLI, TermJson, QuadsBin, HDT and COTTAS. Cover all used IDs, decode validity, round trips and dictionary-generation identity. Several physical representations of one RDF term are permissible only with proved identity-aware matching/deduplication; ID-equality shortcuts require equality reflection. A pure dictionary theorem does not discharge the IO session implementation.

**Phase C: parsers and serializers.** Each reader's contract against the target (set; scoped blank nodes; RDF 1.2 terms), with streaming/batch and success/error guarantees stated separately; https://github.com/danbri/factoidal/issues/576. Each writer's round trip must name its representable domain or intentional projection: a triples-only format cannot preserve an arbitrary dataset's graph registry. Keep parsing correctness distinct from set normalisation. W3C syntax suites remain test evidence for grammar conformance.

**Phase D: query, update and reasoning.** SPARQL evaluation and update as stages over selected corpus views; RDFS/OWL/RIF as typed operations under explicit semantic profiles/fragments; SHACL validation as a stage. Separate entailment soundness, complete evaluation, consistency/model existence and refutation claims. Reuse completeness results where their hypotheses apply (including existing simple-entailment/ρdf results); record missing guarantees. Negation, negative ASK and aggregates need the required query-relative coverage. Update creates a new logical dataset version. Pure evaluation must include captured service/time/extension inputs in its context.

**Phase E: evidence.** The proof checker as a stage (fix https://github.com/danbri/factoidal/issues/976 first); derivations flow on the wires (https://github.com/danbri/factoidal/issues/615, https://github.com/danbri/factoidal/issues/632); RDFC-1.0 and VC Data Integrity as stages with their stated crypto assumptions.

## First connected demonstration

Implement one small path through actual entry points, using existing harnesses before a new API:

**Captured document → parse/scope/certify → selected dataset view → lawful store or scan → checked RDFS derivation → positive SPARQL answer → output artifact.**

Use an observation named graph (`ex:alice ex:worksFor ex:organisation`), a schema named graph (`ex:worksFor rdfs:subPropertyOf ex:affiliatedWith`) and an empty named graph. Select/combine the premises explicitly, derive `ex:alice ex:affiliatedWith ex:organisation` using `rdfs7`, and retain both source dependencies. The derived named graph is an artifact that expands to its proof.

Exercise two representations of the same view, including the connected SBM11 path. Let an index become cold/absent and use a supported scan or rebuild; complete answers retain the same meaning, while unavailable required coverage is reported explicitly. Preserve the graph registry and historical derivation when a source name advances to a new version.

Also keep the empty-input RDFS axiom → `rdfD2` → `rdfs6` example deriving `rdfs:subPropertyOf rdfs:subPropertyOf rdfs:subPropertyOf`. Verify profile licensing; an arbitrary artifact named “axioms” is insufficient.

## Acceptance

- Every inventoried stage has typed artifact/meaning contracts and per-obligation status (proved / tested / assumed / missing), generated from Lean declarations with actual implementation and theorem/checker bindings.
- At least one composition theorem connects the actual document → parse → store → reasoning/query path for its declared fragment. Construction invariants and internal bridges are discharged; remaining environmental assumptions and any unproved syntax/translation boundary are explicit. Such a boundary prevents a stronger end-to-end claim until it is closed.
- Corpus artifacts and logical snapshots are immutable; mutable names, residency and execution state are explicit. Eviction does not change the selected view's meaning or rewrite its derivation history.
- Complete query results agree under the declared query observation relation across supported hot-index, scan and rebuild access paths. Partial/stale/unavailable coverage cannot silently become absence, false, or a complete answer.
- Whole graph/dataset nodes expand to exact dependencies. A run, recipe, theorem citation or signature is not by itself a checked entailment proof.
- Every concrete store constructor/combinator must discharge the content laws to close Phase B; merely recording a missing adapter does not close it. The generic planner result uses the lawful abstraction.
- Regressions cover overlapping graph unions and LIMIT; CLEAR versus DROP/CREATE; empty named graphs; language-tag case versus numeric/XML lexical identity; nested triple terms; independent versus shared blank-node scopes; dictionary generations; #976's swapped-label composition; decode failures; and tampered/cyclic proof dependencies.
- New artifacts/contexts can supersede a current view while existing checked claims remain about their original pinned inputs. Availability of evidence for rechecking is tracked separately.
- No sorry, axiom, `native_decide` or `partial`; `#print axioms` only propext, Classical.choice, Quot.sound; no theorem whose hypothesis restates its conclusion (anti-pattern 29).
- Preserve the existing W3C/SBM11 gates and add focused regressions. Baselines reported in the original issue (not rerun by this editorial review): RDF 1.1 1041 pass, 0 fail / 1041; RDF 1.2 1358 pass, 0 fail / 1358; SPARQL 1.1 650 pass, 0 fail / 650; SPARQL 1.2 271 pass, 0 fail / 271; SHACL Core 98 pass, 0 fail / 98; SBM11 gate (`SBM11_OLYMPICS=0 tests/sbm11/run.sh`) 3257 pass, 0 fail, 28 expected-fail / 3285. Pin revisions, commands and manifests when updating results; added tests can increase totals.

## Out of scope here

- Bridges to external RDF Semantics formalisations come after this internal coherence. Graph entailment uses explicitly selected graph projections; corpus organisation and dataset-view construction retain their own contracts.
- New performance work and new API surface (owner priority above).

## Existing code and design reading

Reuse `RDF/Source.lean`, `DatasetSet.lean`, `CertifiedDataset.lean`, `Dataset.renameBnodes`, `SPARQL/Expr.lean`'s `EvalEnv`, `RDFS/Derivation.lean`/`DerivationCheck.lean`, and the existing proof artifact/checker structures. Keep their exact guarantee boundaries visible.

The earlier [GraphFlow design](https://github.com/danbri/factoidal-core/blob/a3ccec607d1187077250f5fe79b075f169bceb3d/docs/designissues/graphflow.md) is relevant historical input, to reconcile with the current Lean implementation.

[Anthropic's Scion design](https://www.anthropic.com/research/redesigning-source-control) (13 October 2026) separates immutable content-addressed data from derived structures, computes those structures eagerly or on demand, and bounds client caches. It credits [Mononoke](https://github.com/facebook/sapling/tree/main/eden/mononoke) and [Bonsai](https://github.com/facebook/sapling/blob/79071c2a3ea20c36ed71332608535e5801101bba/eden/mononoke/mononoke_types/serialization/bonsai.thrift). Study this as architectural prior art for the corpus; adopting its VCS or centralised deployment model is not a requirement.

Source review pinned to core [`a3ccec607d1187077250f5fe79b075f169bceb3d`](https://github.com/danbri/factoidal-core/commit/a3ccec607d1187077250f5fe79b075f169bceb3d): [capabilities/union](https://github.com/danbri/factoidal-core/blob/a3ccec607d1187077250f5fe79b075f169bceb3d/formal/lean4/L4Factoidal/RDF/StoreCapabilities.lean), [overlay](https://github.com/danbri/factoidal-core/blob/a3ccec607d1187077250f5fe79b075f169bceb3d/formal/lean4/L4Factoidal/RDF/StoreCapabilitiesDelta.lean), [planner](https://github.com/danbri/factoidal-core/blob/a3ccec607d1187077250f5fe79b075f169bceb3d/formal/lean4/L4Factoidal/Storage/PlannerSoundness.lean), [dictionary contract](https://github.com/danbri/factoidal-core/blob/a3ccec607d1187077250f5fe79b075f169bceb3d/formal/lean4/L4Factoidal/RDF/DictInjective.lean). Recheck the active branch before implementation.

## Related

https://github.com/danbri/factoidal/issues/776 (SBM11 end-to-end) · https://github.com/danbri/factoidal/issues/971 (unguarded `Graph` values) · https://github.com/danbri/factoidal/issues/970 (`datasetGraphNames`, empty named graphs) · https://github.com/danbri/factoidal/issues/880, https://github.com/danbri/factoidal/issues/876 (empty named graphs lost) · https://github.com/danbri/factoidal/issues/976 (proof checker blank nodes) · https://github.com/danbri/factoidal/issues/977 (language-tag case in dictionaries) · https://github.com/danbri/factoidal/issues/318 (review gate 5) · https://github.com/danbri/factoidal/issues/576 · https://github.com/danbri/factoidal/issues/484 · https://github.com/danbri/factoidal/issues/615 · https://github.com/danbri/factoidal/issues/800 · https://github.com/danbri/factoidal/issues/875 · https://github.com/danbri/factoidal/issues/404

