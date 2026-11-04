/- The compositor's concrete dataset-union projection. This preserves the
existing public adapter's first-occurrence order. Dropping graph names is an
explicit projection; it is not RDF merge and does not freshen blank nodes. -/
import L4Factoidal.RDF.DatasetDenotation
import L4Factoidal.RDF.CertifiedDataset
import L4Factoidal.Dataflow.Reasoner
import Std.Data.HashSet.Lemmas

namespace L4Factoidal.Dataflow
open RDF

private def distinctStep {α : Type} [BEq α] [Hashable α]
    (state : Std.HashSet α × List α) (value : α) : Std.HashSet α × List α :=
  if state.1.contains value then state else (state.1.insert value, value :: state.2)

/-- The existing public union adapter's exact fold, with first occurrences
retained in input order. It compares whole triples structurally here; handle
certification subsequently enforces the dataset's RDF term-equality sets. -/
def unionGraph (ds : Dataset) : Graph :=
  ((ds.default ++ ds.named.flatMap (·.graph)).foldl distinctStep
    ((∅ : Std.HashSet Triple), ([] : List Triple))).2.reverse

def unionDefault (ds : Dataset) : Dataset := { default := unionGraph ds, named := [] }

/-- Extraction preserves the old public fold definitionally, including order. -/
theorem unionGraph_original (ds : Dataset) : unionGraph ds =
    ((ds.default ++ ds.named.flatMap (·.graph)).foldl
      (fun (seen, acc) t => if seen.contains t then (seen, acc)
        else (seen.insert t, t :: acc))
      ((∅ : Std.HashSet Triple), ([] : List Triple))).2.reverse := rfl

private theorem fold_distinct_mem {α : Type} [BEq α] [Hashable α] [LawfulBEq α]
    (xs : List α) (seen : Std.HashSet α) (acc : List α)
    (sound : ∀ x, seen.contains x = true → x ∈ acc) (value : α) :
    value ∈ (xs.foldl distinctStep (seen, acc)).2 ↔ value ∈ xs ∨ value ∈ acc := by
  induction xs generalizing seen acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, distinctStep]
    split
    next hit =>
      rw [ih seen acc sound]
      have hx := sound x hit
      simp only [List.mem_cons]
      constructor
      · intro h; rcases h with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · intro h; rcases h with (rfl | h) | h
        · exact Or.inr hx
        · exact Or.inl h
        · exact Or.inr h
    next miss =>
      have nextSound : ∀ y, (seen.insert x).contains y = true → y ∈ x :: acc := by
        intro y hy
        rw [Std.HashSet.contains_insert, Bool.or_eq_true] at hy
        rcases hy with h | h
        · have e : x = y := by simpa using h
          simp [e]
        · exact List.mem_cons_of_mem x (sound y h)
      rw [ih (seen.insert x) (x :: acc) nextSound]
      simp only [List.mem_cons]
      simp [or_assoc, or_left_comm]

/-- No input triple is dropped and no new triple or blank-node label is
introduced. Membership is structural, hence stronger than key membership. -/
theorem unionGraph_mem (ds : Dataset) (t : Triple) :
    t ∈ unionGraph ds ↔ t ∈ ds.default ∨ ∃ ng ∈ ds.named, t ∈ ng.graph := by
  simp only [unionGraph, List.mem_reverse]
  rw [fold_distinct_mem _ _ _ (by simp) t]
  simp

/-- The projection's RDF membership is exactly membership in some input graph.
The result intentionally has no named graphs, including empty named graphs. -/
theorem unionDefault_graph (ds : Dataset) (t : Triple) :
    (unionDefault ds).den.graph none t ↔ ∃ gn, ds.den.graph gn t := by
  change (unionGraph ds).mem t = true ↔ ∃ gn, ds.memQuad t gn
  rw [Graph.mem_iff_key]
  constructor
  · rintro ⟨u, hu, key⟩
    rcases (unionGraph_mem ds u).mp hu with h | ⟨ng, hn, h⟩
    · exact ⟨none, (Graph.mem_iff_key t ds.default).mpr ⟨u, h, key⟩⟩
    · exact ⟨some ng.name, ng, hn, rfl, (Graph.mem_iff_key t ng.graph).mpr ⟨u, h, key⟩⟩
  · rintro ⟨gn, h⟩
    cases gn with
    | none =>
      obtain ⟨u, hu, key⟩ := (Graph.mem_iff_key t ds.default).mp h
      exact ⟨u, (unionGraph_mem ds u).mpr (Or.inl hu), key⟩
    | some n =>
      obtain ⟨ng, hn, _, hm⟩ := h
      obtain ⟨u, hu, key⟩ := (Graph.mem_iff_key t ng.graph).mp hm
      exact ⟨u, (unionGraph_mem ds u).mpr (Or.inr ⟨ng, hn, hu⟩), key⟩

/-- This is the value storeNewHandle certifies, not a duplicate model adapter. -/
theorem unionDefault_certified_graph (ds : Dataset) (t : Triple) :
    (unionDefault ds).certify.val.den.graph none t ↔ ∃ gn, ds.den.graph gn t := by
  change (unionDefault ds).certify.val.memQuad t none ↔ _
  rw [Dataset.certify_memQuad]
  exact unionDefault_graph ds t

theorem unionDefault_no_named (ds : Dataset) (n : Subject) :
    ¬ (unionDefault ds).den.names n := by
  simp [unionDefault, Dataset.den, Dataset.names]

/-- A reasoner supplied this exact certified projection receives all and only
source triples. Soundness is its record field; no completeness is claimed.
Public datasetClosure also normalizes its input: agreement of that separate
normalizer with this input is a further execution-boundary obligation. -/
theorem unionDefault_reasoner_handoff (ds : Dataset) (reasoner : SoundReasoner) :
    (∀ t, (unionDefault ds).certify.val.default.mem t = true ↔
      ∃ gn, ds.den.graph gn t) ∧
    reasoner.regime.Entails (unionDefault ds).certify.val.default
      (reasoner.run (unionDefault ds).certify.val.default) := by
  exact ⟨unionDefault_certified_graph ds, reasoner.sound _⟩

#print axioms unionGraph_mem
#print axioms unionDefault_graph
#print axioms unionDefault_certified_graph
#print axioms unionDefault_reasoner_handoff
end L4Factoidal.Dataflow
