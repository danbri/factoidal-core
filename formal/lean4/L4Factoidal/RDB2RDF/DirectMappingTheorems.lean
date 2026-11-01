/-
L4Factoidal.RDB2RDF.DirectMappingTheorems — properties of the Direct Mapping
(W3C Recommendation 27 September 2012) that its §2.2 states.

* `dm2012_rowNode_bnode_iff`: a row node is a blank node exactly when its
  table has no primary key; otherwise it is an IRI (§2.2, "row node").
* `dm2012_rowNode_iri_prefix`: the IRI of a row node starts with the table
  IRI and `/` (§2.2), so the row nodes of two tables with different
  percent-encoded names never meet.

Tracking: https://github.com/danbri/factoidal/issues/1165. The theorems that
relate DM 2012 to R2RML 2012 come with the R2RML step (design record §3).
-/
import L4Factoidal.RDB2RDF.DirectMapping

namespace L4Factoidal.RDB2RDF.DM2012

open L4Factoidal.SQL

theorem dm2012_rowNode_bnode_iff (base : String) (i : Nat) (t : Table) (j : Nat) (row : List L4Factoidal.SQL.Value) :
    (∃ b, rowNode base i t j row = .bnode b) ↔ t.primaryKey = [] := by
  unfold rowNode
  constructor
  · intro ⟨b, h⟩
    by_cases hk : t.primaryKey.isEmpty
    · exact List.isEmpty_iff.mp hk
    · simp [hk] at h
  · intro h
    exact ⟨s!"t{i}r{j}", by simp [h]⟩

theorem dm2012_rowNode_iri_prefix (base : String) (i : Nat) (t : Table) (j : Nat) (row : List L4Factoidal.SQL.Value)
    (h : t.primaryKey ≠ []) :
    ∃ rest, rowNode base i t j row = .iri (tableIri base t ++ "/" ++ rest) := by
  unfold rowNode tableIri
  have hk : t.primaryKey.isEmpty = false := by
    cases hp : t.primaryKey with
    | nil => exact absurd hp h
    | cons _ _ => rfl
  simp only [hk, Bool.false_eq_true, ↓reduceIte]
  exact ⟨_, rfl⟩

end L4Factoidal.RDB2RDF.DM2012
