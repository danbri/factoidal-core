/-
L4Factoidal.Dataflow.PackSetStage — the rows the streaming packer writes are a
set (https://github.com/danbri/factoidal/issues/1006).

`Storage/PackStream.lean` reads a source in publication batches (the IBK2/IBK3
path: 64 chunks of 64 KiB each) and, since issue 1006, passes each batch
through `PackSet.dedupBatch` with one seen graph for the whole source. This
module lifts the per-batch theorem of `Storage/PackSet.lean` over every cut of
the source into batches:

* `packedRows_eq`: the rows written, in order, are `graphAddAll [] ts` for the
  triples `ts` of the whole source: the left fold of the set-semantics
  `Graph.add` (RDF 1.1 Concepts section 3: an RDF graph is a set of triples).
  The cut does not change them.
* `packedRows_keyNodup`: no two rows have the same `Triple.key`, so no two are
  `Triple.eqb`-equal (RDF term equality, language tags without case).

`packSetStage` registers this in the dataflow registry. It covers the dedup
step of the pack operations, not their block encoding (the registry entries of
the block builders cover that) and not the grammar of the source.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Stage
import L4Factoidal.Storage.PackSet
import L4Factoidal.RDF.StreamSet

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF
open L4Factoidal.Storage.PackSet

/-- One publication batch of the packer: the seen graph and the rows written
    so far. -/
def packBatchStep (p : FastGraph × Graph) (batch : List Triple) : FastGraph × Graph :=
  let r := dedupBatch p.1 batch
  (r.1, p.2 ++ r.2)

/-- The rows the packer writes for a source cut into batches. -/
def packedRows (batches : List (List Triple)) : Graph :=
  (batches.foldl packBatchStep ({}, [])).2

theorem packBatchStep_spec (p : FastGraph × Graph) (batch : List Triple)
    (hinv : p.1.Inv) (hg : p.1.toGraph = p.2) :
    (packBatchStep p batch).1.Inv ∧
      (packBatchStep p batch).1.toGraph = (packBatchStep p batch).2 ∧
      (packBatchStep p batch).2 = graphAddAll p.2 batch := by
  refine ⟨dedupBatch_inv p.1 batch hinv, ?_, ?_⟩
  · show (dedupBatch p.1 batch).1.toGraph = p.2 ++ (dedupBatch p.1 batch).2
    rw [dedupBatch_toGraph, hg]
  · show p.2 ++ (dedupBatch p.1 batch).2 = graphAddAll p.2 batch
    rw [← hg, dedupBatch_written p.1 batch hinv]

theorem foldl_packBatchStep (batches : List (List Triple)) :
    ∀ p : FastGraph × Graph, p.1.Inv → p.1.toGraph = p.2 →
      (batches.foldl packBatchStep p).2 = graphAddAll p.2 batches.flatten := by
  induction batches with
  | nil => intro p _ _; rfl
  | cons b bs ih =>
      intro p hinv hg
      obtain ⟨hinv', hg', hrows⟩ := packBatchStep_spec p b hinv hg
      simp only [List.foldl_cons, List.flatten_cons]
      rw [ih (packBatchStep p b) hinv' hg', hrows, graphAddAll_append]

/-- **The rows written are the left fold of `Graph.add`** over the triples of
    the whole source, whatever the cut into batches. -/
theorem packedRows_eq (batches : List (List Triple)) :
    packedRows batches = graphAddAll [] batches.flatten :=
  foldl_packBatchStep batches ({}, []) FastGraph.inv_empty rfl

/-- **The rows written are a set.** -/
theorem packedRows_keyNodup (batches : List (List Triple)) :
    (packedRows batches).KeyNodup := by
  rw [packedRows_eq]
  exact graphAddAll_keyNodup _ [] Graph.keyNodup_nil

/-- The contract of the packer's dedup step: the rows are the set-semantics
    fold of the source's triples, and no two have the same `Triple.key`. -/
def PackSetContract (batches : List (List Triple)) (rows : Graph) : Prop :=
  rows = graphAddAll [] batches.flatten ∧ rows.KeyNodup

/-- The dedup step of the streaming packer, as a registered stage. -/
def packSetStage : Stage String (List (List Triple)) Graph :=
  Stage.ofFun packedRows PackSetContract
    (fun batches => ⟨packedRows_eq batches, packedRows_keyNodup batches⟩)

end L4Factoidal.Dataflow
