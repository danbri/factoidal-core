/-
L4Factoidal.SPARQL.UpdateStoreTheorems — what is proved about
`SPARQL/UpdateStore.lean` (https://github.com/danbri/factoidal/issues/849 and
https://github.com/danbri/factoidal/issues/850).

  * `chooseGo_spec`, `drawMany_spec`, `drawMany_nil`: the fresh blank node
    supply returns labels that the store does not hold and that differ from
    each other.
  * `renameTermGo_eq`, `renameTriple_eq`, `insertDataQuads_eq`,
    `applyInsertData_eq`: the INSERT DATA quads are the reference's, with the
    renaming a parameter.
  * `insertQuadsFor_eq`, `modifyInsertQuads_eq`, `applyModify_eq`,
    `applyDeleteWhere_eq`: `applyModify` and `applyDeleteWhere` of the reference
    semantics are the computation of `UpdateStore` with the reference's own
    blank node supply (`freshTemplateBnode`): the store instantiates the
    templates from a solution sequence by the same functions and differs from
    the reference only in the supply of fresh labels.
  * `changeEntries_*`: the entries of a DELETE/INSERT are the removes of the
    deletes followed by the adds of the inserts.

The replay of those entries over ids is proved in
`Storage/Sbm11/UpdateOverlayTheorems.lean`. No `sorry`, no `axiom`, no
`native_decide`.
-/
import L4Factoidal.SPARQL.UpdateStore

namespace L4Factoidal.SPARQL.UpdateStore

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## The fresh label supply -/

/-- The result of `chooseGo` is at or after the start and its label is not
    held. -/
theorem chooseGo_spec (taken : String → Bool) :
    ∀ (fuel n m : Nat), chooseGo taken fuel n = some m →
      n ≤ m ∧ taken (freshLabel m) = false := by
  intro fuel
  induction fuel with
  | zero => intro n m h; simp [chooseGo] at h
  | succ f ih =>
    intro n m h
    unfold chooseGo at h
    by_cases ht : taken (freshLabel n) = true
    · rw [if_pos ht] at h
      obtain ⟨h1, h2⟩ := ih (n + 1) m h
      exact ⟨by omega, h2⟩
    · rw [if_neg ht] at h
      cases h
      exact ⟨Nat.le_refl _, by simpa using ht⟩

/-- Reversing a list keeps it free of duplicates. -/
theorem nodup_rev {α : Type} {l : List α} (h : l.Nodup) : l.reverse.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_reverse]
  exact h.imp (fun h1 => h1.symm)

/-- `drawMany` draws `k` labels. Every label is not held, the labels differ
    from each other, and the labels already drawn (`acc`) are kept. -/
theorem drawMany_spec (taken : String → Bool) (fuel : Nat) :
    ∀ (k n : Nat) (acc out : List BNodeId),
      acc.Nodup → (∀ l ∈ acc, taken l = false) →
      drawMany taken fuel k n acc = some out →
      out.Nodup ∧ (∀ l ∈ out, taken l = false) ∧ out.length = acc.length + k := by
  intro k
  induction k with
  | zero =>
    intro n acc out hnd hfree h
    simp only [drawMany] at h
    cases h
    refine ⟨nodup_rev hnd, ?_, by simp⟩
    intro l hl
    exact hfree l (List.mem_reverse.mp hl)
  | succ k ih =>
    intro n acc out hnd hfree h
    unfold drawMany at h
    cases hc : chooseGo (fun l => taken l || acc.contains l) fuel n with
    | none => rw [hc] at h; simp at h
    | some m =>
      rw [hc] at h
      simp only at h
      obtain ⟨_, hm⟩ := chooseGo_spec _ fuel n m hc
      have hm' : taken (freshLabel m) = false ∧ acc.contains (freshLabel m) = false := by
        simpa [Bool.or_eq_false_iff] using hm
      have hnotmem : freshLabel m ∉ acc := by
        intro hmem
        have : acc.contains (freshLabel m) = true := List.contains_iff_mem.mpr hmem
        rw [hm'.2] at this
        cases this
      have hnd' : (freshLabel m :: acc).Nodup := List.nodup_cons.mpr ⟨hnotmem, hnd⟩
      have hfree' : ∀ l ∈ freshLabel m :: acc, taken l = false := by
        intro l hl
        rcases List.mem_cons.mp hl with h1 | h1
        · rw [h1]; exact hm'.1
        · exact hfree l h1
      obtain ⟨r1, r2, r3⟩ := ih (m + 1) (freshLabel m :: acc) out hnd' hfree' h
      exact ⟨r1, r2, by simpa [Nat.add_assoc, Nat.add_comm 1 k] using r3⟩

/-- Starting from nothing: `k` labels, none held, all different. -/
theorem drawMany_nil (taken : String → Bool) (fuel k n : Nat) (out : List BNodeId)
    (h : drawMany taken fuel k n [] = some out) :
    out.Nodup ∧ (∀ l ∈ out, taken l = false) ∧ out.length = k := by
  obtain ⟨a, b, c⟩ := drawMany_spec taken fuel k n [] out List.nodup_nil (by simp) h
  exact ⟨a, b, by simpa using c⟩

/-! ## INSERT DATA -/

/-- `wrapLevels` followed by one more level: the innermost level first. -/
theorem wrapLevels_cons (s : Subject) (p : WfIri) (rest : List (Subject × WfIri)) (t : Term) :
    wrapLevels ((s, p) :: rest) t = wrapLevels rest (.tripleTerm s p t) := rfl

/-- The loop over the nesting of a triple term renames as `Term.renameBnodes`
    does. -/
theorem renameTermGo_eq (f : BNodeId → BNodeId) :
    ∀ (t : Term) (levels : List (Subject × WfIri)),
      renameTermGo f levels t = wrapLevels levels (t.renameBnodes f) := by
  intro t
  induction t with
  | iri i => intro levels; simp [renameTermGo, Term.renameBnodes]
  | bnode b => intro levels; simp [renameTermGo, Term.renameBnodes]
  | literal l => intro levels; simp [renameTermGo, Term.renameBnodes]
  | tripleTerm s p o ih =>
    intro levels
    rw [renameTermGo, ih, Term.renameBnodes, wrapLevels_cons]

theorem renameTriple_eq (f : BNodeId → BNodeId) (t : Triple) :
    renameTriple f t = t.renameBnodes f := by
  simp [renameTriple, Triple.renameBnodes, renameTermGo_eq, wrapLevels]

theorem renameQuad_eq (f : BNodeId → BNodeId) (q : Quad) :
    renameQuad f q = Quad.renameBnodes f q := by
  obtain ⟨g, t⟩ := q
  simp [renameQuad, Quad.renameBnodes, renameTriple_eq]

/-- The quads of an INSERT DATA operation are those the reference builds,
    with the renaming `f`. -/
theorem insertDataQuads_eq (f : BNodeId → BNodeId) (quads : QueryPattern) :
    insertDataQuads f quads = (collectQuads none quads).map (Quad.renameBnodes f) := by
  simp only [insertDataQuads]
  congr 1
  funext q
  exact renameQuad_eq f q

/-- The reference INSERT DATA is the store's quads with the request's renaming
    (`freshDataBnode pre`). -/
theorem applyInsertData_eq (pre : String) (ds : Dataset) (quads : QueryPattern) :
    applyInsertData pre ds quads = ds.insertQuads (insertDataQuads (freshDataBnode pre) quads) := by
  simp only [applyInsertData, insertDataQuads_eq]

/-! ## DELETE/INSERT and DELETE WHERE -/

/-- The reference's recursion over the solutions is the indexed `flatMap` of
    `modifyInsertQuads`. -/
theorem insertQuadsFor_eq (pre : String) (opIx : Nat) (withIri : Option WfIri) (tmpl : QueryPattern) :
    ∀ (sols : SolutionSeq) (k : Nat),
      insertQuadsFor pre opIx withIri tmpl sols k =
        (sols.zipIdx k).flatMap fun (mu, ix) =>
          (instQuads (freshTemplateBnode pre opIx ix) mu none tmpl).map (redirectQuad withIri) := by
  intro sols
  induction sols with
  | nil => intro k; simp [insertQuadsFor]
  | cons mu rest ih =>
    intro k
    simp [insertQuadsFor, List.zipIdx_cons, ih]

theorem modifyInsertQuads_eq (pre : String) (opIx : Nat) (withIri : Option WfIri) (tmpl : QueryPattern)
    (sols : SolutionSeq) :
    modifyInsertQuads withIri (some tmpl) (fun ix => freshTemplateBnode pre opIx ix) sols =
      insertQuadsFor pre opIx withIri tmpl sols 0 := by
  rw [insertQuadsFor_eq]
  rfl

/-- `applyModify` of the reference semantics (section 3.1.3): the WHERE clause
    is evaluated once on the view; the quads of the DELETE template are removed,
    then the quads of the INSERT template, instantiated for the same solutions
    with the reference's blank node supply, are added. -/
theorem applyModify_eq (env : EvalEnv) (pre : String) (opIx : Nat) (ds : Dataset)
    (withIri : Option WfIri) (deleteTmpl insertTmpl : Option QueryPattern)
    (usingClauses : List DatasetClause) (wherePat : QueryPattern) :
    applyModify env pre opIx ds withIri deleteTmpl insertTmpl usingClauses wherePat =
      let sols := evalWhere env (whereDataset ds withIri usingClauses) wherePat
      (ds.deleteQuads (modifyDeleteQuads withIri deleteTmpl sols)).insertQuads
        (modifyInsertQuads withIri insertTmpl (fun ix => freshTemplateBnode pre opIx ix) sols) := by
  unfold applyModify
  cases deleteTmpl with
  | none =>
    cases insertTmpl with
    | none => simp [modifyDeleteQuads, modifyInsertQuads, Dataset.insertQuads, Dataset.deleteQuads]
    | some it => simp only [modifyDeleteQuads, modifyInsertQuads, insertQuadsFor_eq]
  | some dt =>
    cases insertTmpl with
    | none => simp [modifyDeleteQuads, modifyInsertQuads, Dataset.insertQuads]
    | some it => simp only [modifyDeleteQuads, modifyInsertQuads, insertQuadsFor_eq]

/-- `applyDeleteWhere` is the removal of `deleteWhereQuads`. -/
theorem applyDeleteWhere_eq (env : EvalEnv) (ds : Dataset) (p : QueryPattern) :
    applyDeleteWhere env ds p = ds.deleteQuads (deleteWhereQuads (evalWhere env ds p) p) := rfl

/-! ## The entries of a change -/

theorem changeEntries_length (dels adds : List Quad) :
    (changeEntries dels adds).length = dels.length + adds.length := by
  simp [changeEntries]

/-- The entries are the removes, then the adds. -/
theorem changeEntries_def (dels adds : List Quad) :
    changeEntries dels adds = dels.map removeEntry ++ adds.map addEntry := rfl

/-- A change with no deletes and no adds has no entries. -/
theorem changeEntries_nil : changeEntries [] [] = [] := rfl

#print axioms chooseGo_spec
#print axioms drawMany_spec
#print axioms drawMany_nil
#print axioms renameTermGo_eq
#print axioms renameTriple_eq
#print axioms insertDataQuads_eq
#print axioms applyInsertData_eq
#print axioms insertQuadsFor_eq
#print axioms modifyInsertQuads_eq
#print axioms applyModify_eq
#print axioms applyDeleteWhere_eq
#print axioms changeEntries_length

end L4Factoidal.SPARQL.UpdateStore
