/-
L4Factoidal.HDT.DictionaryTheorems — `RDF.DictInjective` for an HDT
dictionary role, with one id per RDF term
(https://github.com/danbri/factoidal/issues/977; issue 975 phase B4).

An HDT file comes from another tool, so its dictionary is not built here and
can hold two spellings of one RDF term (`"x"@en` and `"x"@EN`). The reader
folds every decoded term (`idToTerm`) and every looked-up term (`termToId`).
`hdt_dictInjective`: when `roundTripsAll` holds for a role (a `Bool` test
over every id of the role), the ids of the role and their decoded terms are a
`DictInjective` dictionary; `hdt_eq_iff_eqb`: two decoded terms have the
same id exactly when they are `Term.eqb`-equal. A file with two spellings of
one term fails the test.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.HDT.Dictionary
import L4Factoidal.Storage.TermFoldTheorems

namespace L4Factoidal.HDT

open L4Factoidal.RDF
open L4Factoidal.Storage.TermFold

/-- The ids of a role: `1` to `roleMaxId`. -/
def roleIdUsed (inv : Inventory) (role : Role) (n : Nat) : Prop := 1 ≤ n ∧ n ≤ roleMaxId inv role

theorem roundTripsAll_spec (a : Bytes) (inv : Inventory) (role : Role)
    (h : roundTripsAll a inv role = true) :
    ∀ n, roleIdUsed inv role n →
      ∃ t, idToTerm a inv role n = some t ∧ termToId a inv role t = some n := by
  intro n ⟨h1, h2⟩
  unfold roundTripsAll at h
  rw [List.all_eq_true] at h
  have := h (n - 1) (List.mem_range.mpr (by omega))
  rw [show n - 1 + 1 = n by omega] at this
  split at this
  · rename_i t ht
    exact ⟨t, ht, by simpa using this⟩
  · cases this

/-- Under `roundTripsAll`, the ids of a role are a `DictInjective` dictionary
    on their decoded terms. -/
theorem hdt_dictInjective (a : Bytes) (inv : Inventory) (role : Role)
    (h : roundTripsAll a inv role = true) :
    DictInjective (termToId a inv role) (idToTerm a inv role)
      (fun t => ∃ n, roleIdUsed inv role n ∧ idToTerm a inv role n = some t) (roleIdUsed inv role) :=
  DictInjective.ofDecodeCert (roundTripsAll_spec a inv role h)

/-- Every decoded term is folded. -/
theorem idToTerm_folded (a : Bytes) (inv : Inventory) (role : Role) (n : Nat) (t : Term)
    (h : idToTerm a inv role n = some t) : foldTerm t = t := by
  unfold idToTerm at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨u, _, rfl⟩ := h
  exact foldTerm_idem u

/-- Under `roundTripsAll`, two decoded terms have the same id exactly when they
    are the same RDF term under `Term.eqb`. -/
theorem hdt_eq_iff_eqb (a : Bytes) (inv : Inventory) (role : Role)
    (h : roundTripsAll a inv role = true) {t u : Term} {n m : Nat}
    (hn : roleIdUsed inv role n) (hm : roleIdUsed inv role m)
    (ht : idToTerm a inv role n = some t) (hu : idToTerm a inv role m = some u) :
    n = m ↔ t.eqb u = true := by
  have D := hdt_dictInjective a inv role h
  rw [← D.dec_eq_iff hn hm ht hu]
  constructor
  · intro e; subst e; exact Term.eqb_refl t
  · intro e
    rw [← normalizeTerm_eq_iff_eqb] at e
    rwa [idToTerm_folded a inv role n t ht, idToTerm_folded a inv role m u hu] at e

end L4Factoidal.HDT

#print axioms L4Factoidal.HDT.hdt_dictInjective
#print axioms L4Factoidal.HDT.hdt_eq_iff_eqb
