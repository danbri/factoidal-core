/-
L4Factoidal.RDF.QuadSourceTheorems — the dataset producer gives the quads of the
dataset, once each, in order (https://github.com/danbri/factoidal/issues/866).

`ofDataset_flatten`: the batches that `datasetPull` gives from the first position
of a dataset `ds`, taken together in order, are `ds.quadList`
(`RDF/DatasetNormalize.lean`). The number of steps needed is at most the number
of quads, `ds.quadList.length`. `datasetPull_batches_size`: each of those batches
has at least one quad and at most `max 1 batch` quads, so a consumer sees bounded
batches. `quadList_eq_foldDataset`: `ds.quadList` is the list of quads that the
source layer's `Source.foldDataset` gives, in the same order. So a `Dataset` that
a parser returns and the `QuadSource` of that `Dataset` present the same quads in
the same order as the reader of the source layer does for a document that it
parses as a whole.

The statements are about the pure form (`Pull`, `Cursor.take`). `ofPull` adds a
mutable reference around it; `l4sbm11-quad-source selftest`
(`tests/sbm11/quad_source.sh`) checks that the batches of `ofDataset` are the batches
of `Pull.batches`. No hypothesis states a
conclusion: the only hypotheses are the bound on the number of steps and, for
`take_short`, that the batch has fewer quads than the bound.

`#print axioms` at the end of the file.
-/
import L4Factoidal.RDF.QuadSource
import L4Factoidal.RDF.DatasetNormalize
import L4Factoidal.RDF.Source

namespace L4Factoidal.RDF.QuadSourceTheorems

open L4Factoidal.RDF
open L4Factoidal.RDF.QuadSource

/-! ## `Cursor.take`: one equation for each way it can stop or step -/

theorem take_of_le {n : Nat} {acc : Batch} (c : Cursor) (h : n ≤ acc.size) :
    c.take n acc = (acc, c) := by
  rcases c with ⟨g, ts, later⟩
  cases ts with
  | cons t ts => rw [Cursor.take.eq_1, if_pos h]
  | nil =>
      cases later with
      | cons ng rest => rw [Cursor.take.eq_2, if_pos h]
      | nil => rw [Cursor.take.eq_3, if_pos h]

theorem take_cons {n : Nat} {acc : Batch} (h : ¬ n ≤ acc.size) (g : Option Subject) (t : Triple)
    (ts : List Triple) (later : List NamedGraph) :
    Cursor.take n ⟨g, t :: ts, later⟩ acc = Cursor.take n ⟨g, ts, later⟩ (acc.push (t, g)) := by
  rw [Cursor.take.eq_1, if_neg h]

theorem take_next {n : Nat} {acc : Batch} (h : ¬ n ≤ acc.size) (g : Option Subject) (ng : NamedGraph)
    (rest : List NamedGraph) :
    Cursor.take n ⟨g, [], ng :: rest⟩ acc = Cursor.take n ⟨some ng.name, ng.graph, rest⟩ acc := by
  rw [Cursor.take.eq_2, if_neg h]

theorem take_end {n : Nat} {acc : Batch} (h : ¬ n ≤ acc.size) (g : Option Subject) :
    Cursor.take n ⟨g, [], []⟩ acc = (acc, ⟨g, [], []⟩) := by
  rw [Cursor.take.eq_3, if_neg h]

/-! ## `Cursor.take`: what it does to the quads -/

/-- The quads of the accumulator, then the quads of the start position, are the
    quads of the result, then the quads of the end position. -/
theorem take_quads (n : Nat) (c : Cursor) (acc : Batch) :
    acc.toList ++ c.quads = (c.take n acc).1.toList ++ (c.take n acc).2.quads := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc h => rw [take_of_le c h]
  | case2 acc h g t ts later ih =>
      rw [take_cons h, ← ih]
      simp [Cursor.quads, List.append_assoc]
  | case3 acc h g ng rest ih =>
      rw [take_next h, ← ih]
      simp [Cursor.quads]
  | case4 acc h g => rw [take_end h]

/-- The result holds at most `n` quads, or as many as the accumulator held
    when it was larger already. -/
theorem take_size_le (n : Nat) (c : Cursor) (acc : Batch) :
    (c.take n acc).1.size ≤ max n acc.size := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc h => rw [take_of_le c h]; exact Nat.le_max_right _ _
  | case2 acc h g t ts later ih =>
      rw [take_cons h]
      simp only [Array.size_push] at ih
      omega
  | case3 acc h g ng rest ih => rw [take_next h]; exact ih
  | case4 acc h g => rw [take_end h]; exact Nat.le_max_right _ _

/-- When the result holds fewer than `n` quads, the end position has no quad
    left. -/
theorem take_short (n : Nat) (c : Cursor) (acc : Batch)
    (h : (c.take n acc).1.size < n) : (c.take n acc).2.quads = [] := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc hle => rw [take_of_le c hle] at h; dsimp only at h; omega
  | case2 acc hle g t ts later ih => rw [take_cons hle] at h ⊢; exact ih h
  | case3 acc hle g ng rest ih => rw [take_next hle] at h ⊢; exact ih h
  | case4 acc hle g => rw [take_end hle]; simp [Cursor.quads]

/-! ## One step of the producer of a dataset -/

/-- One step of `datasetPull` either ends, with no quad left, or gives a batch
    of at least one and at most `max 1 batch` quads, which are the first quads
    of the position, and a position that holds the others. -/
theorem datasetPull_spec (batch : Nat) (c : Cursor) :
    (datasetPull batch c = none ∧ c.quads = []) ∨
    (∃ (b : Batch) (c' : Cursor), datasetPull batch c = some (b, c') ∧
        0 < b.size ∧ b.size ≤ max 1 batch ∧ c.quads = b.toList ++ c'.quads) := by
  have key := take_quads (max 1 batch) c #[]
  have hsz := take_size_le (max 1 batch) c #[]
  have short := take_short (max 1 batch) c #[]
  unfold datasetPull
  generalize c.take (max 1 batch) #[] = r at key hsz short ⊢
  obtain ⟨b, c'⟩ := r
  dsimp only at key hsz short ⊢
  simp only [List.nil_append, Array.size_empty] at key hsz
  by_cases hb : b.size = 0
  · left
    have hbe : b.isEmpty = true := by simp [Array.isEmpty, hb]
    refine ⟨by simp [hbe], ?_⟩
    have hc' : c'.quads = [] := short (by omega)
    have hbl : b.toList = [] := by simpa using hb
    rw [key, hbl, hc']
    rfl
  · right
    have hbe : b.isEmpty = false := by simp [Array.isEmpty, hb]
    exact ⟨b, c', by simp [hbe], by omega, by omega, key⟩

/-- The batches of `datasetPull` from a position, added to the batches `acc` (newest
    first), taken together in order, are the quads of `acc` and then the quads from the
    position to the end, when the number of steps allowed is at least the number of
    quads. -/
theorem datasetPull_flatten_acc (batch : Nat) :
    ∀ (fuel : Nat) (c : Cursor) (acc : List Batch), c.quads.length ≤ fuel →
      ((datasetPull batch).batchesAcc fuel c acc).reverse.flatMap Array.toList
        = acc.reverse.flatMap Array.toList ++ c.quads := by
  intro fuel
  induction fuel with
  | zero =>
      intro c acc hc
      have : c.quads = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hc)
      simp [Pull.batchesAcc, this]
  | succ fuel ih =>
      intro c acc hc
      rcases datasetPull_spec batch c with ⟨hn, hq⟩ | ⟨b, c', hs, hpos, _, hq⟩
      · simp [Pull.batchesAcc, hn, hq]
      · have hlen : c.quads.length = b.size + c'.quads.length := by
          have := congrArg List.length hq
          simpa using this
        have ih' := ih c' (b :: acc) (by omega)
        simp only [Pull.batchesAcc, hs]
        rw [ih', hq]
        simp [List.flatMap_append, List.append_assoc]

/-- The batches of `datasetPull`, taken together in order, are the quads from the
    position to the end, when the number of steps allowed is at least the number of
    quads. -/
theorem datasetPull_flatten (batch : Nat) (fuel : Nat) (c : Cursor) (hc : c.quads.length ≤ fuel) :
    ((datasetPull batch).batches fuel c).flatMap Array.toList = c.quads := by
  have := datasetPull_flatten_acc batch fuel c [] hc
  simpa [Pull.batches] using this

/-- Each batch of `datasetPull` after the batches `acc` is one of `acc` or has at least
    one quad and at most `max 1 batch` quads. -/
theorem datasetPull_batchesAcc_size (batch : Nat) :
    ∀ (fuel : Nat) (c : Cursor) (acc : List Batch) (b : Batch),
      b ∈ (datasetPull batch).batchesAcc fuel c acc → b ∈ acc ∨ (0 < b.size ∧ b.size ≤ max 1 batch) := by
  intro fuel
  induction fuel with
  | zero => intro c acc b hb; exact Or.inl (by simpa [Pull.batchesAcc] using hb)
  | succ fuel ih =>
      intro c acc b hb
      rcases datasetPull_spec batch c with ⟨hn, _⟩ | ⟨b0, c', hs, hpos, hle, _⟩
      · exact Or.inl (by simpa [Pull.batchesAcc, hn] using hb)
      · simp only [Pull.batchesAcc, hs] at hb
        rcases ih c' (b0 :: acc) b hb with hmem | hsize
        · rcases List.mem_cons.mp hmem with rfl | hmem
          · exact Or.inr ⟨hpos, hle⟩
          · exact Or.inl hmem
        · exact Or.inr hsize

/-- Each batch of the producer of a dataset has at least one quad and at most
    `max 1 batch` quads. -/
theorem datasetPull_batches_size (batch : Nat) (fuel : Nat) (c : Cursor) (b : Batch)
    (hb : b ∈ (datasetPull batch).batches fuel c) : 0 < b.size ∧ b.size ≤ max 1 batch := by
  have hb' : b ∈ (datasetPull batch).batchesAcc fuel c [] := by
    simpa [Pull.batches] using hb
  rcases datasetPull_batchesAcc_size batch fuel c [] b hb' with hmem | hsize
  · simp at hmem
  · exact hsize

/-- The producer of a dataset gives every quad of `ds.quadList`, once each, in
    order, in at most `ds.quadList.length` steps. -/
theorem ofDataset_flatten (ds : Dataset) (batch : Nat) :
    ((datasetPull batch).batches ds.quadList.length (Cursor.start ds)).flatMap Array.toList
      = ds.quadList := by
  have hq : (Cursor.start ds).quads = ds.quadList := by
    simp [Cursor.start, Cursor.quads, Dataset.quadList]
  have := datasetPull_flatten batch ds.quadList.length (Cursor.start ds) (by simp [hq])
  rw [this, hq]

/-! ## The order is the order of the source layer -/

/-- `List.foldl` with a cons step builds the reverse of the mapped list on top of
    the accumulator. -/
theorem foldl_cons_quads (g : Option Subject) (ts : List Triple) (acc : List Quad) :
    ts.foldl (fun (a : List Quad) t => (t, g) :: a) acc
      = (ts.map (fun t => (t, g))).reverse ++ acc := by
  induction ts generalizing acc with
  | nil => simp
  | cons t rest ih => simp [ih]

theorem foldNamed_quads (named : List NamedGraph) (acc : List Quad) :
    named.foldl (fun (a : List Quad) ng => ng.graph.foldl (fun a t => (t, some ng.name) :: a) a) acc
      = (named.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))).reverse ++ acc := by
  induction named generalizing acc with
  | nil => simp
  | cons ng rest ih =>
      simp only [List.foldl_cons]
      rw [foldl_cons_quads, ih, List.flatMap_cons, List.reverse_append, List.append_assoc]

/-- `Dataset.quadList` is the order in which `Source.foldDataset` gives the quads. -/
theorem quadList_eq_foldDataset (ds : Dataset) :
    ds.quadList = (Source.foldDataset (fun (a : List Quad) t g => (t, g) :: a) [] ds).reverse := by
  unfold Source.foldDataset Dataset.quadList
  rw [foldl_cons_quads none ds.default [], foldNamed_quads]
  simp

end L4Factoidal.RDF.QuadSourceTheorems

#print axioms L4Factoidal.RDF.QuadSourceTheorems.take_quads
#print axioms L4Factoidal.RDF.QuadSourceTheorems.take_size_le
#print axioms L4Factoidal.RDF.QuadSourceTheorems.take_short
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_spec
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_flatten_acc
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_flatten
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_batchesAcc_size
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_batches_size
#print axioms L4Factoidal.RDF.QuadSourceTheorems.ofDataset_flatten
#print axioms L4Factoidal.RDF.QuadSourceTheorems.quadList_eq_foldDataset
