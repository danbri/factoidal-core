/-
L4Factoidal.Storage.PackSet — the packers write a set of rows.

RDF 1.1 Concepts and Abstract Syntax, section 3: "An RDF graph is a set of RDF
triples." Section 4: a dataset is a default graph and named graphs, each a set.
https://github.com/danbri/factoidal/issues/1006: the streaming packer
(`Storage/PackStream.lean`) put every parsed triple into a block, so a document
that stated one triple two times gave a generation with two rows, and the IBK3
store answered `COUNT(*)` 2. The IBK4 and IBK5 packers wrote the repeated rows
too; their read path (`Storage.QuadDataset.datasetOfQuads`) removed them.

`packSeenStep` is the fold step both packer paths now use. It keeps every
distinct triple written so far in a `FastGraph` (bucketed `Triple.eqb`
membership: RDF term equality, language tags without case) and passes a triple
on only when no `Triple.eqb`-equal triple was written before. The first
occurrence fixes the place, so a source with no repeated triple gives exactly
the rows, and so the bytes, it gave before this module.

Memory: the `FastGraph` holds every distinct triple of the source (per graph
name on the quad path), so the packer's resident set grows with the number of
distinct triples, where the IBK3 path before held one publication batch. The
same trade was made for the streamed N-Quads writer (`RDF/StreamSet.lean`).

What is proved:
* `packSeenStep_fst`: the seen graph after a step is `FastGraph.add`.
* `dedupBatch_fst`: the seen graph after a batch is `FastGraph.addAll`.
* `dedupBatch_toGraph`: the seen graph after a batch is the seen graph before
  it followed by exactly the triples the batch passes on.
* `dedupBatch_written`: under the `FastGraph` invariant, the seen graph before
  a batch followed by the triples passed on is `graphAddAll` of the batch: the
  left fold of the set-semantics `Graph.add`. `Dataflow/PackSetStage.lean`
  lifts this over every cut of the source into batches and proves the written
  rows are a set (`Graph.KeyNodup`).
* `addFreshQuad_fresh`: on the quad path a quad passes when its graph's seen
  set has no `Triple.eqb`-equal triple, and is dropped otherwise.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.FastGraph

namespace L4Factoidal.Storage.PackSet

open L4Factoidal.RDF

/-- One triple: add it to the seen graph and, when it is new, to the
    triples to write (kept in reverse). The membership test is the one of
    `FastGraph.add`. -/
def packSeenStep (st : FastGraph × List Triple) (t : Triple) : FastGraph × List Triple :=
  let k := tripleKey t
  let bucket := st.1.buckets.getD k []
  if bucket.any (fun u => u.eqb t) then st
  else ({ rev := t :: st.1.rev, buckets := st.1.buckets.insert k (t :: bucket) }, t :: st.2)

/-- One publication batch: the new seen graph and the triples of the batch
    that were not written before, in source order. -/
def dedupBatch (seen : FastGraph) (ts : List Triple) : FastGraph × List Triple :=
  let r := ts.foldl packSeenStep (seen, [])
  (r.1, r.2.reverse)

theorem packSeenStep_fst (st : FastGraph × List Triple) (t : Triple) :
    (packSeenStep st t).1 = st.1.add t := by
  unfold packSeenStep FastGraph.add
  dsimp only
  by_cases h : ((st.1.buckets.getD (tripleKey t) []).any fun u => u.eqb t) = true
  · simp [h]
  · simp [h]

/-- The step keeps `seen.rev = acc ++ base` for a fixed `base`. -/
theorem packSeenStep_rev (base : List Triple) (st : FastGraph × List Triple) (t : Triple)
    (h : st.1.rev = st.2 ++ base) : (packSeenStep st t).1.rev = (packSeenStep st t).2 ++ base := by
  unfold packSeenStep
  dsimp only
  by_cases hb : ((st.1.buckets.getD (tripleKey t) []).any fun u => u.eqb t) = true
  · simp [hb, h]
  · simp [hb, h]

theorem foldl_packSeenStep_fst (ts : List Triple) :
    ∀ st : FastGraph × List Triple, (ts.foldl packSeenStep st).1 = st.1.addAll ts := by
  induction ts with
  | nil => intro st; rfl
  | cons t ts ih =>
      intro st
      simp only [List.foldl_cons]
      rw [ih, packSeenStep_fst]
      rfl

theorem foldl_packSeenStep_rev (base : List Triple) (ts : List Triple) :
    ∀ st : FastGraph × List Triple, st.1.rev = st.2 ++ base →
      (ts.foldl packSeenStep st).1.rev = (ts.foldl packSeenStep st).2 ++ base := by
  induction ts with
  | nil => intro st h; exact h
  | cons t ts ih =>
      intro st h
      simp only [List.foldl_cons]
      exact ih _ (packSeenStep_rev base st t h)

theorem dedupBatch_fst (seen : FastGraph) (ts : List Triple) :
    (dedupBatch seen ts).1 = seen.addAll ts := by
  unfold dedupBatch
  exact foldl_packSeenStep_fst ts (seen, [])

/-- The seen graph after a batch is the seen graph before it followed by the
    triples the batch passes on. -/
theorem dedupBatch_toGraph (seen : FastGraph) (ts : List Triple) :
    (dedupBatch seen ts).1.toGraph = seen.toGraph ++ (dedupBatch seen ts).2 := by
  unfold dedupBatch FastGraph.toGraph
  have h := foldl_packSeenStep_rev seen.rev ts (seen, []) (by simp)
  simp only
  rw [h, List.reverse_append]

/-- The triples a batch passes on, after the seen graph, are the left fold of
    `Graph.add` over the batch. -/
theorem dedupBatch_written (seen : FastGraph) (ts : List Triple) (h : seen.Inv) :
    seen.toGraph ++ (dedupBatch seen ts).2 = graphAddAll seen.toGraph ts := by
  rw [← dedupBatch_toGraph, dedupBatch_fst, FastGraph.addAll_toGraph ts seen h]

theorem dedupBatch_inv (seen : FastGraph) (ts : List Triple) (h : seen.Inv) :
    (dedupBatch seen ts).1.Inv := by
  rw [dedupBatch_fst]
  exact FastGraph.addAll_inv ts seen h

/-! ## The quad path: one seen graph per graph name -/

/-- The seen triples of each graph name of a quad source (`none` is the
    default graph). -/
abbrev QuadSeen := Std.HashMap (Option Subject) FastGraph

/-- One quad: `some` the new seen sets when no `Triple.eqb`-equal triple was
    seen in the same graph, `none` when the quad repeats one. -/
def addFreshQuad (seen : QuadSeen) (graph : Option Subject) (t : Triple) : Option QuadSeen :=
  let g := seen.getD graph {}
  let (g', fresh) := packSeenStep (g, []) t
  if fresh.isEmpty then none else some (seen.insert graph g')

theorem addFreshQuad_fresh (seen : QuadSeen) (graph : Option Subject) (t : Triple) :
    (addFreshQuad seen graph t).isSome =
      !((seen.getD graph {}).buckets.getD (tripleKey t) []).any (fun u => u.eqb t) := by
  unfold addFreshQuad packSeenStep
  by_cases hb : ((seen.getD graph {}).buckets.getD (tripleKey t) []).any (fun u => u.eqb t) = true
  · simp [hb]
  · simp [hb]

end L4Factoidal.Storage.PackSet
