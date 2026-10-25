/-
L4Factoidal.Dataflow.Store — the interface type of data access
(https://github.com/danbri/factoidal/issues/975, "Architecture acceptance",
item 2, the second component kind).

## The interface types

`LawfulStore` is one graph of a store, as the SPARQL planner reads it:

* `backend`: the dispatch value the planner and the backend evaluator run
  (`SPARQL/StoreBackend.lean`); its `StoreCaps` record is
  `capsOfBackend backend` (`LawfulStore.caps`);
* `graph`: the denotation, one graph predicate `Triple → Prop`
  (`RDF/StoreCapsDenotation.lean`: a `StoreCaps` record reads one graph);
* `assumed_contracts`: the named assumptions the law rests on (`Assumption`), `[]`
  when the law is proved;
* `law`: under the assumptions, `BackendExact backend graph`, the law of the
  arm. From it, `LawfulStore.exact` gives `StoreCapsExact graph caps`: the
  five laws of `StoreCapsLawful`, `solveExact` (a search returns exactly the
  matching triples of the graph, up to RDF term equality), `solveNodupKeys`
  (no two rows RDF-term-equal) and `distinctPredicatesComplete`.

`LawfulDataset` is a dataset record (`DatasetBackend`): its denotation
`DatasetDen`, its named assumptions, and the law `DatasetBackendExact`
(`Storage/PlannerSoundness.lean`: each backend reads its graph of the
denotation, every graph name has a backend, no two backends share a name).

A value of either type cannot exist without its law. When the law rests on an
assumption, the assumption is a member of `assumed_contracts` with a name from
`AssumptionName`; it is visible in the value and counted by the ratchet
(`foundation/assumptions.txt`, `tools/assumption-gate.py`).

## `distinctPredicates` is complete, not exact

`StoreCapsExact` asks that a predicate list holds the predicate of every
triple of the graph and has no duplicate. It does not ask that every listed
predicate is used: the COTTAS reader enumerates the dictionary of the whole
file (`RDF/StoreCapsDenotation.lean`, header), and the one consumer drops a
predicate whose exact count is zero. So the interface keeps the complete law.

## Instances

| constructor | backend | named assumptions |
|---|---|---|
| `ofList g h` | `.list g` | none (`g.KeyNodup`) |
| `ofIndexed g h` | `.indexed (Index.ofGraph g)` | none (`g.KeyNodup`) |
| `ofCaps c G h` | `.caps c` | none (`StoreCapsExact G c`) |
| `ofGraph g`, `ofIndexedGraph g` | `.list g`, `.indexed (Index.ofGraph g)` | `datasetIsSet` (`g.KeyNodup`) |
| `hdt ops`, `cottasInMemory ops` | `.hdt ops`, `.cottasInMemory ops` | `backendReadOpsExact` |
| `cottasOnDisk ops scope` | `.cottasOnDisk ops scope` | `cottasReadOpsExact` |
| `cottasOnDiskDelta ops scope dr` | `.cottasOnDiskDelta ops scope dr` | `cottasReadOpsExact` |
| `overlay s dr` | `.caps (overlay s.caps dr)` | those of `s` |
| `union ss` | `.union (ss.map backend)` | those of the members |
| `virtualRml vs` | `.virtualRml vs` | `rmlPushdownInvisible`, `rmlVirtualIsMaterialised` |

| constructor | dataset record | named assumptions |
|---|---|---|
| `LawfulDataset.indexed d hset` | `indexedDatasetBackend d` | none |
| `LawfulDataset.ofCertified c` | `indexedDatasetBackend c.val` | none (IRI and blank-node graph names) |
| `LawfulDataset.ofDataset d` | `indexedDatasetBackend d` | `datasetIsSet` |
| `LawfulDataset.ofDefault s` | default `s.backend`, no named graph | those of `s` |

The SBM11 store (`Storage/Sbm11/IdQuery.lean`, `Store m`) is not an instance.
It is not a `StoreCaps`: it runs in a monad with a failure channel, gives
blocks and term ids, holds the whole dataset with the graph as a column, and
its engine evaluates whole patterns on ids without a per-pattern triple solve
(`Storage/Sbm11/StoreCapsConnection.lean`). The two meet at the denotation:
`sbm11_record_denotes` makes the dataset record of a set that denotes the
input of an SBM11 generation a `DatasetBackendExact` of the generation's
denotation, which is the law of `LawfulDataset.indexed`.

## The consumers

The query ops of the wasm dispatch, the dataset handles and the command line
reach the backend evaluator only through `LawfulDataset.runSelect` and
`LawfulDataset.runAsk` (`Wasm/Ops/Query.lean`, `queryParsedDatasetWith`), and
search a graph only through `LawfulStore.search`. `tools/assumption-gate.py`
fails when a file under `formal/lean4/Wasm/` or `formal/lean4/Harness/` calls
the evaluator over a bare `DatasetBackend`. The theorems over the interface
types are in `Dataflow/StoreTheorems.lean` (not imported by the wasm).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.PlannerSoundness
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.RDF.CertifiedDataset

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.RDF.CottasCaps
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.SPARQL.DatasetRestriction (indexedDatasetBackend_named)
open L4Factoidal.Storage.PlannerSoundness

/-! ## 1. Named assumptions -/

/-- The names of the assumptions that the law of an interface value may rest
on. Each constructor has one line in `foundation/assumptions.txt`, with the
reason it is not proved; `tools/assumption-gate.py` fails when a constructor
has no line. -/
inductive AssumptionName where
  /-- The HDT or in-memory COTTAS reader reads exactly its graph
  (`BackendReadOpsExact`): file access. -/
  | backendReadOpsExact
  /-- The COTTAS on-disk reader reads exactly its graph in its scope
  (`CottasReadOpsExact`): file access. -/
  | cottasReadOpsExact
  /-- The RML pushdown drops no matching triple (`RmlPushdownInvisible`). -/
  | rmlPushdownInvisible
  /-- The unbounded RML virtual solve holds the materialised default graph
  (`RmlVirtualIsMaterialised`). -/
  | rmlVirtualIsMaterialised
  /-- The dataset is a set of quads (`Dataset.IsSet`), or the graph a set of
  triples (`Graph.KeyNodup`), at a call site that does not carry the proof. -/
  | datasetIsSet
  /-- Each GET of a Linked Web Storage snapshot returned the representation
  its entity tag identifies at the snapshot instant, and the container
  listings were the storage's containment at that instant
  (`Dataflow/LwsSource.lean`, `ReadsAtSnapshot`): HTTP reads, outside Lean. -/
  | lwsReadsAtSnapshot
  deriving Repr, DecidableEq, Inhabited

/-- Every assumption name, in declaration order. -/
def AssumptionName.all : List AssumptionName :=
  [.backendReadOpsExact, .cottasReadOpsExact, .rmlPushdownInvisible, .rmlVirtualIsMaterialised,
   .datasetIsSet, .lwsReadsAtSnapshot]

theorem AssumptionName.mem_all (a : AssumptionName) : a ∈ AssumptionName.all := by
  cases a <;> simp [AssumptionName.all]

/-- A named assumption: its name and the proposition it assumes. -/
structure Assumption where
  name : AssumptionName
  holds : Prop

/-- Every assumption of the list holds. -/
def Assumed (as : List Assumption) : Prop := ∀ a ∈ as, a.holds

theorem Assumed.nil : Assumed [] := fun _ h => absurd h List.not_mem_nil

theorem Assumed.append {as bs : List Assumption} (ha : Assumed as) (hb : Assumed bs) :
    Assumed (as ++ bs) := by
  intro a h
  rcases List.mem_append.mp h with h | h
  · exact ha a h
  · exact hb a h

theorem Assumed.left {as bs : List Assumption} (h : Assumed (as ++ bs)) : Assumed as :=
  fun a ha => h a (List.mem_append_left _ ha)

theorem Assumed.right {as bs : List Assumption} (h : Assumed (as ++ bs)) : Assumed bs :=
  fun a ha => h a (List.mem_append_right _ ha)

/-! ## 2. The law of an arm is a law of its graph up to pointwise equivalence -/

theorem backendExact_congr {gb : GraphBackend} {G G' : Triple → Prop} (h : BackendExact gb G)
    (e : ∀ t, G t ↔ G' t) : BackendExact gb G' := by
  have : G = G' := funext fun t => propext (e t)
  subst this
  exact h

/-! ## 3. `LawfulStore` -/

/-- **One graph of a store, with its law as a field.** -/
structure LawfulStore where
  /-- The dispatch value the planner runs. -/
  backend : GraphBackend
  /-- The graph the store reads. -/
  graph : Triple → Prop
  /-- The named assumptions the law rests on; `[]` when it is proved. -/
  assumed_contracts : List Assumption := []
  /-- The law of the arm, under the assumptions. -/
  law : Assumed assumed_contracts → BackendExact backend graph

namespace LawfulStore

/-- The capability record of the store. -/
def caps (s : LawfulStore) : StoreCaps := capsOfBackend s.backend

/-- A search of the store. -/
def search (s : LawfulStore) (b : PatternBound) : List Triple := backendSearch s.backend b

/-- The law has no assumption. -/
def Proved (s : LawfulStore) : Prop := s.assumed_contracts = []

theorem assumed_of_proved {s : LawfulStore} (h : s.Proved) : Assumed s.assumed_contracts := by
  rw [h]; exact Assumed.nil

/-- **The capability record reads the graph exactly** (`StoreCapsExact`). -/
theorem exact (s : LawfulStore) (h : Assumed s.assumed_contracts) : StoreCapsExact s.graph s.caps :=
  capsOfBackend_exact s.backend s.graph (s.law h)

/-- A search returns the matching triples of the graph, up to RDF term
equality. -/
theorem search_exact (s : LawfulStore) (h : Assumed s.assumed_contracts) (b : PatternBound) (t : Triple) :
    KeyMem (s.search b) t ↔ s.graph t ∧ boundMatches b t = true :=
  backendSearch_exact (s.law h) b t

/-- No two rows of a search are RDF-term-equal. -/
theorem search_nodupKeys (s : LawfulStore) (h : Assumed s.assumed_contracts) (b : PatternBound) :
    ((s.search b).map Triple.key).Nodup :=
  backendSearch_nodupKeys (s.law h) b

/-! ### Instances from proofs -/

/-- The list store of a list with no two RDF-term-equal entries. -/
def ofList (g : Graph) (h : g.KeyNodup) : LawfulStore where
  backend := .list g
  graph := KeyMem g
  law := fun _ => ⟨h, fun _ => Iff.rfl⟩

/-- The in-memory index of a list with no two RDF-term-equal entries. -/
def ofIndexed (g : Graph) (h : g.KeyNodup) : LawfulStore where
  backend := indexedGraphBackend g
  graph := KeyMem g
  law := fun _ => ⟨g, OWL.RL.Index.Wf.ofGraph g, h, fun _ => Iff.rfl⟩

/-- Any capability record with its law. -/
def ofCaps (c : StoreCaps) (G : Triple → Prop) (h : StoreCapsExact G c) : LawfulStore where
  backend := .caps c
  graph := G
  law := fun _ => h

/-- The record of a store with a resolved delta laid over it reads the base
graph without the tombstoned triples and with the added ones
(`overlay_exact`). -/
def overlay (s : LawfulStore) (dr : DeltaResolved) : LawfulStore where
  backend := .caps (RDF.overlay s.caps dr)
  graph := overlayPred s.graph dr
  assumed_contracts := s.assumed_contracts
  law := fun h => overlay_exact dr (s.exact h)

/-- The members of a union, one graph each, in member order. -/
theorem backendsExact_map : ∀ (ss : List LawfulStore), Assumed (ss.flatMap (·.assumed_contracts)) →
    BackendsExact (ss.map (·.backend)) (ss.map (·.graph))
  | [], _ => by simp [BackendsExact]
  | s :: ss, h => by
    simp only [List.flatMap_cons] at h
    simp only [List.map_cons, BackendsExact]
    exact ⟨s.law h.left, backendsExact_map ss h.right⟩

/-- The union of stores reads the set union of their graphs
(`unionCaps_exact`); it rests on the assumptions of every member. -/
def union (ss : List LawfulStore) : LawfulStore where
  backend := .union (ss.map (·.backend))
  graph := unionPred (ss.map (·.graph))
  assumed_contracts := ss.flatMap (·.assumed_contracts)
  law := fun h => ⟨ss.map (·.graph), backendsExact_map ss h, fun _ => Iff.rfl⟩

/-! ### Instances that rest on a named assumption -/

/-- The graph a reader enumerates with the unbounded search. -/
def readOpsGraph (ops : BackendReadOps) (t : Triple) : Prop := KeyMem (ops.search patternBoundAll) t

/-- An HDT file through its reader. -/
def hdt (ops : BackendReadOps) : LawfulStore where
  backend := .hdt ops
  graph := readOpsGraph ops
  assumed_contracts := [⟨.backendReadOpsExact, BackendReadOpsExact (readOpsGraph ops) ops⟩]
  law := fun h => h _ List.mem_cons_self

/-- The in-memory COTTAS path through its reader. -/
def cottasInMemory (ops : BackendReadOps) : LawfulStore where
  backend := .cottasInMemory ops
  graph := readOpsGraph ops
  assumed_contracts := [⟨.backendReadOpsExact, BackendReadOpsExact (readOpsGraph ops) ops⟩]
  law := fun h => h _ List.mem_cons_self

/-- The graph the COTTAS reader enumerates in a scope. -/
def cottasGraph (ops : CottasReadOps) (scope : CottasScope) (t : Triple) : Prop :=
  KeyMem (ops.searchTok scope patternBoundAll) t

/-- A COTTAS file on disk, one graph scope. -/
def cottasOnDisk (ops : CottasReadOps) (scope : CottasScope) : LawfulStore where
  backend := .cottasOnDisk ops scope
  graph := cottasGraph ops scope
  assumed_contracts := [⟨.cottasReadOpsExact, CottasReadOpsExact (cottasGraph ops scope) ops scope⟩]
  law := fun h => h _ List.mem_cons_self

/-- A COTTAS file on disk with a resolved delta. -/
def cottasOnDiskDelta (ops : CottasReadOps) (scope : CottasScope) (dr : DeltaResolved) :
    LawfulStore where
  backend := .cottasOnDiskDelta ops scope dr
  graph := overlayPred (cottasGraph ops scope) dr
  assumed_contracts := [⟨.cottasReadOpsExact, CottasReadOpsExact (cottasGraph ops scope) ops scope⟩]
  law := fun h => ⟨cottasGraph ops scope, h _ List.mem_cons_self, fun _ => Iff.rfl⟩

/-- A virtual RML source: two open assumptions. -/
def virtualRml (vs : RML.VirtualSource) : LawfulStore where
  backend := .virtualRml vs
  graph := rmlGraph vs
  assumed_contracts := [⟨.rmlPushdownInvisible, RmlPushdownInvisible vs⟩,
    ⟨.rmlVirtualIsMaterialised, RmlVirtualIsMaterialised vs⟩]
  law := fun h => ⟨h _ List.mem_cons_self, h _ (List.mem_cons_of_mem _ List.mem_cons_self),
    fun _ => Iff.rfl⟩

/-- The list store of a list at a call site that carries no set proof: it
rests on `datasetIsSet` (here, no two RDF-term-equal entries). -/
def ofGraph (g : Graph) : LawfulStore where
  backend := .list g
  graph := KeyMem g
  assumed_contracts := [⟨.datasetIsSet, g.KeyNodup⟩]
  law := fun h => ⟨h _ List.mem_cons_self, fun _ => Iff.rfl⟩

/-- The in-memory index of a list at a call site that carries no set proof. -/
def ofIndexedGraph (g : Graph) : LawfulStore where
  backend := indexedGraphBackend g
  graph := KeyMem g
  assumed_contracts := [⟨.datasetIsSet, g.KeyNodup⟩]
  law := fun h => ⟨g, OWL.RL.Index.Wf.ofGraph g, h _ List.mem_cons_self, fun _ => Iff.rfl⟩

theorem ofList_proved (g : Graph) (h : g.KeyNodup) : (ofList g h).Proved := rfl
theorem ofIndexed_proved (g : Graph) (h : g.KeyNodup) : (ofIndexed g h).Proved := rfl
theorem ofCaps_proved (c : StoreCaps) (G : Triple → Prop) (h : StoreCapsExact G c) :
    (ofCaps c G h).Proved := rfl

/-- The record of the overlay is `RDF.overlay` of the store's record. -/
theorem overlay_caps (s : LawfulStore) (dr : DeltaResolved) :
    (s.overlay dr).caps = RDF.overlay s.caps dr := rfl

/-- The record of the union is `unionCaps` of the members' records. -/
theorem union_caps (ss : List LawfulStore) :
    (union ss).caps = unionCaps (ss.map (·.caps)) := by
  show capsOfBackend (.union _) = _
  rw [capsOfBackend_union, capsOfBackendList_map, List.map_map]
  rfl

end LawfulStore

/-! ## 4. `LawfulDataset` -/

/-- **A dataset record, with its law as a field.** -/
structure LawfulDataset where
  /-- The dataset record the evaluator runs. -/
  backend : DatasetBackend
  /-- The dataset the record reads. -/
  den : DatasetDen
  /-- The named assumptions the law rests on; `[]` when it is proved. -/
  assumed_contracts : List Assumption := []
  /-- The law, under the assumptions. -/
  law : Assumed assumed_contracts → DatasetBackendExact den backend

namespace LawfulDataset

/-- The law has no assumption. -/
def Proved (L : LawfulDataset) : Prop := L.assumed_contracts = []

/-- The default graph as a `LawfulStore`. -/
def default (L : LawfulDataset) : LawfulStore where
  backend := L.backend.default
  graph := L.den.graph none
  assumed_contracts := L.assumed_contracts
  law := fun h => (L.law h).default

/-- **SELECT through the backend evaluator.** `none` when the evaluator does
not take the query shape (the caller answers with the reference evaluator). -/
def runSelect (L : LawfulDataset) (env : EvalEnv) (q : Query) : Option SolutionSeq :=
  runSelectQueryBackendDataset env q L.backend

/-- **ASK through the backend evaluator.** -/
def runAsk (L : LawfulDataset) (env : EvalEnv) (q : Query) : Option Bool :=
  runAskQueryBackendDataset env q L.backend

/-- The dataset record of a dataset that is a set: proved
(`indexedDatasetBackend_exact`). -/
def indexed (d : Dataset) (hset : d.IsSet) : LawfulDataset where
  backend := indexedDatasetBackend d
  den := d.den
  law := fun _ => indexedDatasetBackend_exact hset

/-- The dataset record of a dataset that carries its set proof: proved, for
every graph name, an IRI or a blank node. Until 2026-10-25 a blank-node graph
name made it rest on the named assumption `graphNameKeysDistinct`: the record
spelled a graph name as a string, so an IRI and a blank-node label could name
one backend (https://github.com/danbri/factoidal/issues/975). -/
def ofCertified (c : CertifiedDataset) : LawfulDataset := indexed c.val c.property

/-- The dataset record of a dataset at a call site that carries no set proof:
it rests on `datasetIsSet`. -/
def ofDataset (d : Dataset) : LawfulDataset where
  backend := indexedDatasetBackend d
  den := d.den
  assumed_contracts := [⟨.datasetIsSet, d.IsSet⟩]
  law := fun h => indexedDatasetBackend_exact (h _ List.mem_cons_self)

theorem ofCertified_backend (c : CertifiedDataset) :
    (ofCertified c).backend = indexedDatasetBackend c.val := rfl

theorem ofCertified_den (c : CertifiedDataset) : (ofCertified c).den = c.val.den := rfl

/-- The record of a certified dataset rests on no named assumption, whatever
its graph names. -/
theorem ofCertified_proved (c : CertifiedDataset) : (ofCertified c).Proved := rfl

theorem ofDataset_backend (d : Dataset) : (ofDataset d).backend = indexedDatasetBackend d := rfl

/-- The default-graph denotation of a store: the triples RDF-term-equal to a
triple of its graph, and no named graph. -/
def defaultDen (G : Triple → Prop) : DatasetDen where
  graph gn t := gn = none ∧ ∃ u, G u ∧ u.key = t.key
  names _ := False
  graph_key := by
    rintro gn t u e ⟨hg, v, hv, ev⟩
    exact ⟨hg, v, hv, ev.trans e⟩
  named_mem := by
    rintro n t ⟨h, -⟩
    cases h

/-- A dataset of one store as its default graph and no named graph. -/
def ofDefault (s : LawfulStore) : LawfulDataset where
  backend := { default := s.backend, named := [] }
  den := defaultDen s.graph
  assumed_contracts := s.assumed_contracts
  law := fun h =>
    { default := backendExact_congr (s.law h) (fun t =>
        ⟨fun ht => ⟨rfl, t, ht, rfl⟩,
         fun ⟨_, _, hu, e⟩ => (s.exact h).graph_key e hu⟩)
      named := fun _ hn => absurd hn List.not_mem_nil
      names := fun _ hn => absurd hn id
      namesNodup := List.nodup_nil }

theorem ofDefault_backend (s : LawfulStore) :
    (ofDefault s).backend = { default := s.backend, named := [] } := rfl

end LawfulDataset

/-! ## 5. The named assumptions of the instances

The assumption names each constructor uses, as `#guard`s: a constructor that
starts to rest on a new assumption fails the build here. -/

section Guards

open LawfulStore

private def names (as : List Assumption) : List AssumptionName := as.map (·.name)

private def gNil : Graph := []
private def opsNil : BackendReadOps := { search := fun _ => [], estimate := fun _ => 0, predicatePresent := fun _ => false }

#guard names (ofList gNil Graph.keyNodup_nil).assumed_contracts = []
#guard names (ofIndexed gNil Graph.keyNodup_nil).assumed_contracts = []
#guard names (hdt opsNil).assumed_contracts = [.backendReadOpsExact]
#guard names (cottasInMemory opsNil).assumed_contracts = [.backendReadOpsExact]
#guard names (union [hdt opsNil, ofList gNil Graph.keyNodup_nil]).assumed_contracts = [.backendReadOpsExact]
#guard names (LawfulDataset.ofDataset Dataset.empty).assumed_contracts = [.datasetIsSet]
#guard names (LawfulDataset.ofDataset { default := [], named := [{ name := .bnode "g", graph := [] }] }).assumed_contracts
  = [.datasetIsSet]
#guard names (LawfulDataset.ofCertified ⟨Dataset.empty, Dataset.isSet_empty⟩).assumed_contracts = []
#guard names (LawfulDataset.ofDefault (hdt opsNil)).assumed_contracts = [.backendReadOpsExact]
#guard AssumptionName.all.length = 6

end Guards

#print axioms backendExact_congr
#print axioms LawfulStore.exact
#print axioms LawfulStore.search_exact
#print axioms LawfulStore.search_nodupKeys
#print axioms LawfulStore.backendsExact_map
#print axioms LawfulStore.union_caps
#print axioms LawfulDataset.ofCertified_backend
#print axioms LawfulDataset.ofCertified_proved
#print axioms LawfulDataset.ofDataset_backend

end L4Factoidal.Dataflow
