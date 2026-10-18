/-
L4Factoidal.RDF.QuadSourceTheorems — the dataset producer gives the quads of the
dataset, once each, in order (https://github.com/danbri/factoidal/issues/866).

`ofDataset_flatten`: the quads of the batches that `datasetPull` gives from the
first position of a dataset `ds`, taken together in order, are `ds.quadList`
(`RDF/DatasetNormalize.lean`). `ofDataset_graphs`: their declared graph names,
taken together in order, are the names of `ds.named`, empty graphs included (RDF
1.1 Concepts section 4; https://github.com/danbri/factoidal/issues/855). The
number of steps needed is at most the number of quads and named graphs,
`ds.quadList.length + ds.named.length`. `datasetPull_batches_size`: each of those
batches has at least one quad or graph name and at most `max 1 batch` of them, so
a consumer sees bounded batches. `quadList_eq_foldDataset`: `ds.quadList` is the list of quads that the
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
    Cursor.take n ⟨g, t :: ts, later⟩ acc = Cursor.take n ⟨g, ts, later⟩ (acc.pushQuad (t, g)) := by
  rw [Cursor.take.eq_1, if_neg h]

theorem take_next {n : Nat} {acc : Batch} (h : ¬ n ≤ acc.size) (g : Option Subject) (ng : NamedGraph)
    (rest : List NamedGraph) :
    Cursor.take n ⟨g, [], ng :: rest⟩ acc =
      Cursor.take n ⟨some ng.name, ng.graph, rest⟩ (acc.pushGraph ng.name) := by
  rw [Cursor.take.eq_2, if_neg h]

theorem take_end {n : Nat} {acc : Batch} (h : ¬ n ≤ acc.size) (g : Option Subject) :
    Cursor.take n ⟨g, [], []⟩ acc = (acc, ⟨g, [], []⟩) := by
  rw [Cursor.take.eq_3, if_neg h]

/-! ## `Cursor.take`: what it does to the quads and to the graph names -/

/-- The quads of the accumulator, then the quads of the start position, are the
    quads of the result, then the quads of the end position. -/
theorem take_quads (n : Nat) (c : Cursor) (acc : Batch) :
    acc.quads.toList ++ c.quads = (c.take n acc).1.quads.toList ++ (c.take n acc).2.quads := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc h => rw [take_of_le c h]
  | case2 acc h g t ts later ih =>
      rw [take_cons h, ← ih]
      simp [Cursor.quads, Batch.pushQuad, List.append_assoc]
  | case3 acc h g ng rest ih =>
      rw [take_next h, ← ih]
      simp [Cursor.quads, Batch.pushGraph]
  | case4 acc h g => rw [take_end h]

/-- The declared names of the accumulator, then the names still to declare at the
    start position, are the declared names of the result, then the names still to
    declare at the end position. -/
theorem take_names (n : Nat) (c : Cursor) (acc : Batch) :
    acc.graphs.toList ++ c.names = (c.take n acc).1.graphs.toList ++ (c.take n acc).2.names := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc h => rw [take_of_le c h]
  | case2 acc h g t ts later ih =>
      rw [take_cons h, ← ih]
      simp [Cursor.names, Batch.pushQuad]
  | case3 acc h g ng rest ih =>
      rw [take_next h, ← ih]
      simp [Cursor.names, Batch.pushGraph]
  | case4 acc h g => rw [take_end h]

/-- The result holds at most `n` quads and names, or as many as the accumulator
    held when it was larger already. -/
theorem take_size_le (n : Nat) (c : Cursor) (acc : Batch) :
    (c.take n acc).1.size ≤ max n acc.size := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc h => rw [take_of_le c h]; exact Nat.le_max_right _ _
  | case2 acc h g t ts later ih =>
      rw [take_cons h]
      simp only [Batch.size, Batch.pushQuad, Array.size_push] at ih ⊢
      simp only [Batch.size] at h
      omega
  | case3 acc h g ng rest ih =>
      rw [take_next h]
      simp only [Batch.size, Batch.pushGraph, Array.size_push] at ih ⊢
      simp only [Batch.size] at h
      omega
  | case4 acc h g => rw [take_end h]; exact Nat.le_max_right _ _

/-- When the result holds fewer than `n` quads and names, the end position has no
    quad and no name left. -/
theorem take_short (n : Nat) (c : Cursor) (acc : Batch)
    (h : (c.take n acc).1.size < n) : (c.take n acc).2.quads = [] ∧ (c.take n acc).2.names = [] := by
  induction c, acc using Cursor.take.induct n with
  | case1 c acc hle => rw [take_of_le c hle] at h; dsimp only at h; omega
  | case2 acc hle g t ts later ih => rw [take_cons hle] at h ⊢; exact ih h
  | case3 acc hle g ng rest ih => rw [take_next hle] at h ⊢; exact ih h
  | case4 acc hle g => rw [take_end hle]; simp [Cursor.quads, Cursor.names]

/-! ## One step of the producer of a dataset -/

/-- One step of `datasetPull` either ends, with no quad and no name left, or gives
    a batch of at least one and at most `max 1 batch` quads and names, which are the
    first quads and names of the position, and a position that holds the others. -/
theorem datasetPull_spec (batch : Nat) (c : Cursor) :
    (datasetPull batch c = none ∧ c.quads = [] ∧ c.names = []) ∨
    (∃ (b : Batch) (c' : Cursor), datasetPull batch c = some (b, c') ∧
        0 < b.size ∧ b.size ≤ max 1 batch ∧ c.quads = b.quads.toList ++ c'.quads ∧
        c.names = b.graphs.toList ++ c'.names) := by
  have key := take_quads (max 1 batch) c {}
  have keyN := take_names (max 1 batch) c {}
  have hsz := take_size_le (max 1 batch) c {}
  have short := take_short (max 1 batch) c {}
  unfold datasetPull
  generalize c.take (max 1 batch) {} = r at key keyN hsz short ⊢
  obtain ⟨b, c'⟩ := r
  dsimp only at key keyN hsz short ⊢
  have he0 : ({} : Batch).size = 0 := rfl
  simp only [List.nil_append] at key keyN
  rw [he0] at hsz
  by_cases hb : b.size = 0
  · left
    have hbq : b.quads.size = 0 := by simp only [Batch.size] at hb; omega
    have hbg : b.graphs.size = 0 := by simp only [Batch.size] at hb; omega
    have hbe : b.isEmpty = true := by simp [Batch.isEmpty, Array.isEmpty, hbq, hbg]
    refine ⟨by simp [hbe], ?_, ?_⟩
    · have hc' := (short (by omega)).1
      have hbl : b.quads.toList = [] := by simpa using hbq
      rw [key, hbl, hc']
      rfl
    · have hc' := (short (by omega)).2
      have hbl : b.graphs.toList = [] := by simpa using hbg
      rw [keyN, hbl, hc']
      rfl
  · right
    have hbe : b.isEmpty = false := by
      simp only [Batch.size] at hb
      simp only [Batch.isEmpty, Bool.and_eq_false_iff]
      by_cases hq : b.quads.size = 0
      · right; simpa using (show b.graphs.size ≠ 0 by omega)
      · left; simpa using hq
    exact ⟨b, c', by simp [hbe], by omega, by omega, key, keyN⟩

/-- The batches of `datasetPull` from a position, added to the batches `acc` (newest
    first), taken together in order: their quads are the quads of `acc` and then the
    quads from the position to the end, and their graph names are those of `acc` and
    then the names still to declare, when the number of steps allowed is at least the
    number of quads and names. -/
theorem datasetPull_flatten_acc (batch : Nat) :
    ∀ (fuel : Nat) (c : Cursor) (acc : List Batch), c.quads.length + c.names.length ≤ fuel →
      ((datasetPull batch).batchesAcc fuel c acc).reverse.flatMap (·.quads.toList)
          = acc.reverse.flatMap (·.quads.toList) ++ c.quads ∧
        ((datasetPull batch).batchesAcc fuel c acc).reverse.flatMap (·.graphs.toList)
          = acc.reverse.flatMap (·.graphs.toList) ++ c.names := by
  intro fuel
  induction fuel with
  | zero =>
      intro c acc hc
      have hq : c.quads = [] := List.length_eq_zero_iff.mp (by omega)
      have hn : c.names = [] := List.length_eq_zero_iff.mp (by omega)
      simp [Pull.batchesAcc, hq, hn]
  | succ fuel ih =>
      intro c acc hc
      rcases datasetPull_spec batch c with ⟨hn, hq, hns⟩ | ⟨b, c', hs, hpos, _, hq, hns⟩
      · simp [Pull.batchesAcc, hn, hq, hns]
      · have hlen : c.quads.length + c.names.length = b.size + (c'.quads.length + c'.names.length) := by
          have h1 := congrArg List.length hq
          have h2 := congrArg List.length hns
          simp only [List.length_append, Array.length_toList] at h1 h2
          simp only [Batch.size]
          omega
        have ih' := ih c' (b :: acc) (by omega)
        simp only [Pull.batchesAcc, hs]
        rw [ih'.1, ih'.2, hq, hns]
        simp [List.flatMap_append, List.append_assoc]

/-- The quads and the graph names of the batches of `datasetPull`, taken together in
    order, are the quads and the names from the position to the end, when the number
    of steps allowed is at least the number of quads and names. -/
theorem datasetPull_flatten (batch : Nat) (fuel : Nat) (c : Cursor)
    (hc : c.quads.length + c.names.length ≤ fuel) :
    ((datasetPull batch).batches fuel c).flatMap (·.quads.toList) = c.quads ∧
      ((datasetPull batch).batches fuel c).flatMap (·.graphs.toList) = c.names := by
  have := datasetPull_flatten_acc batch fuel c [] hc
  simpa [Pull.batches] using this

/-- Each batch of `datasetPull` after the batches `acc` is one of `acc` or has at least
    one and at most `max 1 batch` quads and graph names. -/
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

/-- Each batch of the producer of a dataset has at least one and at most
    `max 1 batch` quads and graph names. -/
theorem datasetPull_batches_size (batch : Nat) (fuel : Nat) (c : Cursor) (b : Batch)
    (hb : b ∈ (datasetPull batch).batches fuel c) : 0 < b.size ∧ b.size ≤ max 1 batch := by
  have hb' : b ∈ (datasetPull batch).batchesAcc fuel c [] := by
    simpa [Pull.batches] using hb
  rcases datasetPull_batchesAcc_size batch fuel c [] b hb' with hmem | hsize
  · simp at hmem
  · exact hsize

theorem start_quads (ds : Dataset) : (Cursor.start ds).quads = ds.quadList := by
  simp [Cursor.start, Cursor.quads, Dataset.quadList]

theorem start_names (ds : Dataset) : (Cursor.start ds).names = ds.named.map (·.name) := rfl

/-- The producer of a dataset gives every quad of `ds.quadList`, once each, in
    order, in at most `ds.quadList.length + ds.named.length` steps. -/
theorem ofDataset_flatten (ds : Dataset) (batch : Nat) :
    ((datasetPull batch).batches (ds.quadList.length + ds.named.length) (Cursor.start ds)).flatMap
        (·.quads.toList) = ds.quadList := by
  have := datasetPull_flatten batch (ds.quadList.length + ds.named.length) (Cursor.start ds)
    (by simp [start_quads, start_names])
  rw [this.1, start_quads]

/-- The producer of a dataset declares the name of every named graph of `ds`, empty
    graphs included, once each, in the order of `ds.named`, in the same steps. -/
theorem ofDataset_graphs (ds : Dataset) (batch : Nat) :
    ((datasetPull batch).batches (ds.quadList.length + ds.named.length) (Cursor.start ds)).flatMap
        (·.graphs.toList) = ds.named.map (·.name) := by
  have := datasetPull_flatten batch (ds.quadList.length + ds.named.length) (Cursor.start ds)
    (by simp [start_quads, start_names])
  rw [this.2, start_names]

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
#print axioms L4Factoidal.RDF.QuadSourceTheorems.take_names
#print axioms L4Factoidal.RDF.QuadSourceTheorems.take_size_le
#print axioms L4Factoidal.RDF.QuadSourceTheorems.take_short
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_spec
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_flatten_acc
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_flatten
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_batchesAcc_size
#print axioms L4Factoidal.RDF.QuadSourceTheorems.datasetPull_batches_size
#print axioms L4Factoidal.RDF.QuadSourceTheorems.ofDataset_flatten
#print axioms L4Factoidal.RDF.QuadSourceTheorems.ofDataset_graphs
#print axioms L4Factoidal.RDF.QuadSourceTheorems.quadList_eq_foldDataset
