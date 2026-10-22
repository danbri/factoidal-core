/-
L4Factoidal.Storage.Sbm11.TypedCmpFilterTheorems — the `typedCmp` FILTER
conjunct of the id query path is the reference FILTER
(https://github.com/danbri/factoidal/issues/930).

* `typedCmpOf?_spec`: what `IdQuery.typedCmpOf?` builds: the constant `c`
  satisfies `typedConstOk`, the key prefix and lexical form are those of `c`,
  and the stored expression is the input expression, `?v OP c` or `c OP ?v`.
* `typedCmp_fast_eq_ref`: for such a conjunct, a dictionary key that
  `decodeKey?` reads as the term `t` and that `typedCmpKey?` decides gives the
  value `refFilter e [(v, t)]`, which is what `applyFilters` computes for a
  row whose id has the term `t` by the reference path.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.TypedCmpTheorems

namespace L4Factoidal.Storage.Sbm11.IdQuery

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Expr CompOp ebvOrFalse)
open L4Factoidal.Storage.Sbm11.TypedCmp

theorem typedCmpOf?_spec (e : Expr) (v : String) (op : CompOp) (swap : Bool) (pre : ByteArray)
    (cLex : String) (e' : Expr) (h : typedCmpOf? e = some (.typedCmp v op swap pre cLex e')) :
    ∃ c : WfLiteral, typedConstOk c = true ∧ pre = typedPre c ∧ cLex = c.val.lexicalForm ∧ e' = e ∧
      e = (if swap then Expr.compare op (.lit c) (.var v) else Expr.compare op (.var v) (.lit c)) := by
  unfold typedCmpOf? at h
  split at h
  · rename_i op0 v0 c0
    split at h
    · rename_i hok
      simp only [Option.some.injEq, FKind.typedCmp.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨c0, hok, rfl, rfl, rfl, rfl⟩
    · cases h
  · rename_i op0 c0 v0
    split at h
    · rename_i hok
      simp only [Option.some.injEq, FKind.typedCmp.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨c0, hok, rfl, rfl, rfl, rfl⟩
    · cases h
  · cases h

theorem typedCmp_fast_eq_ref (e : Expr) (v : String) (op : CompOp) (swap : Bool) (pre : ByteArray)
    (cLex : String) (e' : Expr) (h : typedCmpOf? e = some (.typedCmp v op swap pre cLex e'))
    (buf : ByteArray) (a b : Nat) (t : Term) (hdec : decodeKey? (sliceList buf a b) = some t)
    (r : Bool) (hr : typedCmpKey? op swap pre cLex buf a b = some r) :
    refFilter e' [(v, t)] = r := by
  obtain ⟨c, hc, hpre, hlex, he', he⟩ := typedCmpOf?_spec e v op swap pre cLex e' h
  subst hpre hlex he'
  rw [he]
  exact typedCmpKey_sound op swap c hc v buf a b t hdec r hr

#print axioms typedCmpOf?_spec
#print axioms typedCmp_fast_eq_ref

end L4Factoidal.Storage.Sbm11.IdQuery
