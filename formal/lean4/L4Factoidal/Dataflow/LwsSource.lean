/-
L4Factoidal.Dataflow.LwsSource — a Linked Web Storage snapshot as a source of
a `LawfulDataset` (https://github.com/danbri/factoidal/issues/1011, KR2).

The den of the source is the dataset view (`LWS/DatasetView.lean`, `view`) of
the storage AT THE SNAPSHOT INSTANT, over the resources the client read. The
record the evaluator runs is built from what the client read. The two agree
under one named assumption, `lwsReadsAtSnapshot` (`ReadsAtSnapshot`):

  each GET returned the representation that its entity tag identifies at the
  snapshot instant (LWS 1.0 Core, "Read Resource"; RFC 9110 §8.8.3), the
  graph is the graph that representation denotes, each linkset GET returned
  the linkset (RFC 9264) that its entity tag identifies at that instant, and
  the container listings (the containment and the listing members) and the
  storage description IRI were those of the storage at that instant.

The storage at an instant (`StorageAt`) is not observable by a client; it is
the object the assumption is about. HTTP gives no snapshot read of several
resources, so a crawl that interleaves with writes can break the assumption;
a check is to read each entity tag again after the crawl (not done here; see
`docs/designissues/2026-10-25-lws-dataset-view.md`).

With `Sourced.query_sound` (`Dataflow/Compose.lean`), a SPARQL query over the
source satisfies the evaluator contract over the view of the storage
(`lwsSource_query_sound`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Compose
import L4Factoidal.Dataflow.Sources
import L4Factoidal.LWS.DatasetView

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset
open L4Factoidal.Storage.PlannerSoundness
open L4Factoidal.LWS.DatasetView

/-- A storage at one instant: its storage description IRI; for each resource
IRI, the entity tag of its current representation and the RDF graph that
representation denotes (`none` for no resource or a non-RDF one); the
containment pairs and the listing members of its containers; and for each
resource IRI, the IRI, the entity tag and the links of its linkset (`none`
for no linkset). -/
structure StorageAt where
  storage : WfIri
  current : WfIri → Option (String × Graph)
  members : List (WfIri × WfIri)
  entries : List Entry
  linksetOf : WfIri → Option (WfIri × String × List Link)

/-- The snapshot the storage would have given for the resources of `s`: the
storage's description IRI, containment and listing members, each read with
the storage's entity tag and graph, and each linkset read with the storage's
linkset. -/
def StorageAt.at (st : StorageAt) (s : Snapshot) : Snapshot :=
  { storage := st.storage
    members := st.members
    entries := st.entries
    reads := s.reads.map (fun r => match st.current r.resource with
      | some (e, g) => { r with etag := e, graph := g }
      | none => r)
    linksets := s.linksets.map (fun l => match st.linksetOf l.resource with
      | some (li, e, ls) => { l with linkset := li, etag := e, links := ls }
      | none => l) }

/-- **The named assumption**: the reads are the storage at the instant. -/
def ReadsAtSnapshot (st : StorageAt) (s : Snapshot) : Prop :=
  st.storage = s.storage ∧ st.members = s.members ∧ st.entries = s.entries ∧
    (∀ r ∈ s.reads, st.current r.resource = some (r.etag, r.graph)) ∧
    (∀ l ∈ s.linksets, st.linksetOf l.resource = some (l.linkset, l.etag, l.links))

/-- Under the assumption the storage's snapshot is the read snapshot. -/
theorem StorageAt.at_eq {st : StorageAt} {s : Snapshot} (h : ReadsAtSnapshot st s) :
    st.at s = s := by
  obtain ⟨storage, members, entries, reads, linksets⟩ := s
  obtain ⟨hs, hm, he, hr, hl⟩ := h
  show Snapshot.mk st.storage st.members st.entries _ _ = _
  rw [hs, hm, he]
  congr 1
  · conv => rhs; rw [← List.map_id reads]
    apply List.map_congr_left
    intro r hr'
    rw [hr r hr']
    rfl
  · conv => rhs; rw [← List.map_id linksets]
    apply List.map_congr_left
    intro l hl'
    rw [hl l hl']
    rfl

/-- The record of a snapshot: the indexed record of the certified view of the
reads, with the den of the storage's view. -/
def lwsDataset (st : StorageAt) (s : Snapshot) : LawfulDataset where
  backend := indexedDatasetBackend (view s).certify.val
  den := (view (st.at s)).den
  assumed_contracts := [⟨.lwsReadsAtSnapshot, ReadsAtSnapshot st s⟩]
  law := fun h => by
    rw [StorageAt.at_eq (h _ List.mem_cons_self), ← Dataset.certify_den]
    exact indexedDatasetBackend_exact (view s).certify.property

/-- **The LWS source.** -/
def lwsSource (st : StorageAt) (s : Snapshot) : Sourced where
  store := lwsDataset st s
  ref := (view s).certify.val
  isSet := (view s).certify.property
  den_eq := fun h => by
    show _ = (view (st.at s)).den
    rw [StorageAt.at_eq (h _ List.mem_cons_self), Dataset.certify_den]

/-- **Source theorem, LWS**: the den is the dataset view of the storage at the
snapshot instant, over the resources read; the one named assumption is
`lwsReadsAtSnapshot`; under it the den is the view of the reads. -/
theorem lwsSource_spec (st : StorageAt) (s : Snapshot) :
    (lwsSource st s).den = (view (st.at s)).den ∧
      (lwsSource st s).assumptions.map (·.name) = [.lwsReadsAtSnapshot] ∧
      (ReadsAtSnapshot st s → (lwsSource st s).den = (view s).den) :=
  ⟨rfl, rfl, fun h => by show (view (st.at s)).den = _; rw [StorageAt.at_eq h]⟩

/-- **A query over an LWS snapshot**: the evaluator contract over a dataset
whose denotation is the view of the storage at the snapshot instant, and, for
an order-free query, agreement with the reference answer, under
`lwsReadsAtSnapshot` and the evaluator's named assumption. -/
theorem lwsSource_query_sound (st : StorageAt) (s : Snapshot) (ev : LawfulEvaluator)
    (hev : ev.AssumptionHolds) (h : ReadsAtSnapshot st s) (env : EvalEnv) (q : Query) :
    ((lwsSource st s).input env q).ds.den = (view (st.at s)).den ∧
      EvalContract ((lwsSource st s).input env q) (ev.run ((lwsSource st s).input env q)) ∧
      (OrderFree q → AnswerAgrees (ev.run ((lwsSource st s).input env q))
        (referenceAnswer ((lwsSource st s).input env q))) :=
  (lwsSource st s).query_sound ev hev
    (fun a ha => by
      rcases List.mem_singleton.mp ha with rfl
      exact h) env q

#print axioms StorageAt.at_eq
#print axioms lwsDataset
#print axioms lwsSource
#print axioms lwsSource_spec
#print axioms lwsSource_query_sound

end L4Factoidal.Dataflow
