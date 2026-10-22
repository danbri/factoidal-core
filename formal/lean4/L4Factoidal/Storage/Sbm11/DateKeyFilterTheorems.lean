/-
L4Factoidal.Storage.Sbm11.DateKeyFilterTheorems — the `dateCmp` FILTER
conjunct of the id query path is the reference FILTER
(https://github.com/danbri/factoidal/issues/948).

* `dateCmpOf?_spec`: what `IdQuery.dateCmpOf?` builds: `OP` is one of `<`,
  `<=`, `>`, `>=` (`DateKey.relOp?`), the constant `c` is admitted
  (`DateKey.dateConst?`), and the stored expression is the input expression,
  `?v OP c` or `c OP ?v`.
* `refFilter_compare_var_lit`, `refFilter_compare_lit_var`: the reference
  FILTER value of such an expression on the binding `?v = t` is the value of
  `Fn.Comparison.termCompare` (false when it has none).
* `dateCmp_fast_eq_ref`: for a conjunct that `dateCmpOf?` built, a dictionary
  key that `decodeKey?` reads as the term `t` and that `dateCmpKey?` decides
  gives the value `refFilter e [(v, t)]`, the value `applyFilters` computes
  for a row whose id has the term `t` by the reference path.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.DateKeyTheorems

namespace L4Factoidal.Storage.Sbm11.IdQuery

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Expr CompOp ebvOrFalse)
open L4Factoidal.Storage.Sbm11.DateKey

theorem dateCmpOf?_spec (e : Expr) (v : String) (o : Fn.Comparison.Op) (swap : Bool) (pre : ByteArray)
    (kc : Nat) (e' : Expr) (h : dateCmpOf? e = some (.dateCmp v o swap pre kc e')) :
    ∃ (op : CompOp) (c : WfLiteral), relOp? op = some o ∧ dateConst? c = some (pre, kc) ∧ e' = e ∧
      e = (if swap then Expr.compare op (.lit c) (.var v) else Expr.compare op (.var v) (.lit c)) := by
  unfold dateCmpOf? at h
  split at h
  · rename_i op0 v0 c0
    split at h
    · rename_i o0 pre0 kc0 ho hc
      simp only [Option.some.injEq, FKind.dateCmp.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨op0, c0, ho, hc, rfl, rfl⟩
    · cases h
  · rename_i op0 c0 v0
    split at h
    · rename_i o0 pre0 kc0 ho hc
      simp only [Option.some.injEq, FKind.dateCmp.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      exact ⟨op0, c0, ho, hc, rfl, rfl⟩
    · cases h
  · cases h

theorem valueCompare_rel (op : CompOp) (o : Fn.Comparison.Op) (ho : relOp? op = some o) (a b : Term) :
    L4Factoidal.SPARQL.valueCompare (.term a) (.term b) op = Fn.Comparison.termCompare a b o := by
  cases op <;> simp [relOp?] at ho <;> subst ho <;>
    simp [L4Factoidal.SPARQL.valueCompare, L4Factoidal.SPARQL.relationalCompare,
      L4Factoidal.SPARQL.EvalResult.toTerm?]

theorem refFilter_compare_var_lit (op : CompOp) (o : Fn.Comparison.Op) (ho : relOp? op = some o)
    (v : String) (c : WfLiteral) (t : Term) :
    refFilter (Expr.compare op (.var v) (.lit c)) [(v, t)] =
      (Fn.Comparison.termCompare t (.literal c) o).getD false := by
  simp only [refFilter, L4Factoidal.SPARQL.Expr.evalIn, L4Factoidal.SPARQL.Binding.lookup]
  simp only [if_true, valueCompare_rel op o ho]
  cases Fn.Comparison.termCompare t (.literal c) o <;>
    simp [ebvOrFalse, L4Factoidal.SPARQL.ebv]

theorem refFilter_compare_lit_var (op : CompOp) (o : Fn.Comparison.Op) (ho : relOp? op = some o)
    (v : String) (c : WfLiteral) (t : Term) :
    refFilter (Expr.compare op (.lit c) (.var v)) [(v, t)] =
      (Fn.Comparison.termCompare (.literal c) t o).getD false := by
  simp only [refFilter, L4Factoidal.SPARQL.Expr.evalIn, L4Factoidal.SPARQL.Binding.lookup]
  simp only [if_true, valueCompare_rel op o ho]
  cases Fn.Comparison.termCompare (.literal c) t o <;>
    simp [ebvOrFalse, L4Factoidal.SPARQL.ebv]

/-- The key-byte answer of a `dateCmp` conjunct is the reference FILTER value
    on the decoded term. -/
theorem dateCmp_fast_eq_ref (e : Expr) (v : String) (o : Fn.Comparison.Op) (swap : Bool)
    (pre : ByteArray) (kc : Nat) (e' : Expr) (h : dateCmpOf? e = some (.dateCmp v o swap pre kc e'))
    (buf : ByteArray) (a b : Nat) (t : Term) (hdec : decodeKey? (sliceList buf a b) = some t)
    (r : Bool) (hr : dateCmpKey? o swap pre kc buf a b = some r) :
    refFilter e' [(v, t)] = r := by
  obtain ⟨op, c, ho, hc, rfl, he⟩ := dateCmpOf?_spec e v o swap pre kc e' h
  have ht := dateCmpKey_termCompare o swap c pre kc hc buf a b t hdec r hr
  subst he
  cases swap
  · simp only [Bool.false_eq_true, if_false] at ht ⊢
    rw [refFilter_compare_var_lit op o ho, ht]
    rfl
  · simp only [if_true] at ht ⊢
    rw [refFilter_compare_lit_var op o ho, ht]
    rfl

#print axioms dateCmpOf?_spec
#print axioms dateCmp_fast_eq_ref

end L4Factoidal.Storage.Sbm11.IdQuery
