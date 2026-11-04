/-
L4Factoidal.RDB2RDF.R2RMLTheorems — properties of R2RML 2012 (W3C
Recommendation 27 September 2012) as run over the RML evaluator, and its
relation to the Direct Mapping 2012.

* `r2rml2012_cell_natural`: every value of a logical row is the natural RDF
  literal (R2RML 2012 §10.2, `naturalRVal`) of a non-NULL SQL value. The
  Direct Mapping 2012 literal triples use the same function
  (`DM2012.rowTriples`, DM 2012 §2.3 refers to R2RML §10.2), so the two
  specifications give a SQL value the same literal.
* `r2rml2012_null_no_value`: a NULL cell gives no value, so a term map that
  references it generates no term (R2RML 2012 §7.4, §11).
* `r2rml2012_tableName_query`: the effective SQL query of `rr:tableName t`
  is `SELECT * FROM t` (R2RML 2012 §5.1); `translateTriple` reads both
  logical table forms through `effectiveQuery`.
* `r2rml2012_rejected_no_quads`: a run that has an error has no quads
  (R2RML 2012 §11: a data error or a mapping error rejects the mapping).

Open: `dm2012_as_r2rml2012` (the Direct Mapping graph equals the R2RML
result of the default mapping), https://github.com/danbri/factoidal/issues/1222.

Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.RDB2RDF.R2RML

namespace L4Factoidal.RDB2RDF.R2RML2012

open L4Factoidal.SQL
open L4Factoidal.RML
open L4Factoidal.RDF

theorem r2rml2012_null_no_value : naturalRVal .null = none := rfl

theorem r2rml2012_cell_natural (db : Database) (ls : LogicalSource) (recs : List Record)
    (h : sqlRecords db ls = .ok recs) (r : Record) (hr : r ∈ recs) :
    ∃ cells names, r = .table cells names ∧
      ∀ c ∈ cells, ∃ v : L4Factoidal.SQL.Value, v ≠ .null ∧ naturalRVal v = some c.2 := by
  unfold sqlRecords at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rw [List.mem_map] at hr
        obtain ⟨row, _, rfl⟩ := hr
        refine ⟨_, _, rfl, ?_⟩
        intro c hc
        rw [List.mem_filterMap] at hc
        obtain ⟨⟨⟨n?, _⟩, v⟩, _, hv⟩ := hc
        cases n? with
        | none => simp at hv
        | some n =>
          simp only [Option.bind_some] at hv
          cases hn : naturalRVal v with
          | none => simp [hn] at hv
          | some rv =>
            simp only [hn, Option.map_some, Option.some.injEq] at hv
            subst hv
            refine ⟨v, ?_, hn⟩
            intro hnull
            subst hnull
            simp [naturalRVal] at hn

theorem r2rml2012_tableName_query (t : String) :
    effectiveQuery "tableName" t = "SELECT * FROM " ++ t := rfl

theorem r2rml2012_rejected_no_quads (g : Graph) (db : Database) (base : String) :
    (runR2RML g db base).errors = [] ∨ (runR2RML g db base).quads = [] := by
  unfold runR2RML runMappingGraphWith
  dsimp only
  split
  · exact Or.inr rfl
  · split
    · exact Or.inr rfl
    · split
      · rename_i h; exact Or.inl (by simpa using h)
      · exact Or.inr rfl

end L4Factoidal.RDB2RDF.R2RML2012
