/-
L4Factoidal.XSD.IntegerLexTheorems — the XSD integer lexical mapping reads
back the canonical form of every integer: `parseIntegerLex (toString v) =
some v`, and for an integer datatype `lexicalFor .xsd10 b (toString v)` is
`v` when `v` is in the type's bounds.

Use: an SBM11 inline integer id holds `v` and its datatype; its numeric
reading is `Dec.ofInt v` with no parse of `toString v`
(`Storage/Sbm11/IdAgg.lean`, https://github.com/danbri/factoidal/issues/862).

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.XSD.Lexical

namespace L4Factoidal.XSD.IntegerLexTheorems
open L4Factoidal.XSD

theorem natOfDigits_eq (l : List Char) (init : Nat) :
    l.foldl (fun acc c => acc * 10 + (c.toNat - 48)) init = Nat.ofDigitChars 10 l init := by
  induction l generalizing init with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.foldl_cons]
    rw [ih, Nat.ofDigitChars_cons, Nat.mul_comm]
    rfl

theorem allDigits_toDigits (n : Nat) : allDigitsL (Nat.toDigits 10 n) = true := by
  unfold allDigitsL
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true]
  refine ⟨Nat.toDigits_ne_nil, ?_⟩
  intro c hc
  have h := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : '0' ≤ c := h.1
  have h2 : c ≤ '9' := h.2
  simp [isDigitC, h1, h2]

theorem head_toDigits (n : Nat) : ∃ c cs, Nat.toDigits 10 n = c :: cs ∧ c ≠ '-' ∧ c ≠ '+' := by
  match h : Nat.toDigits 10 n with
  | [] => exact absurd h Nat.toDigits_ne_nil
  | c :: cs =>
    refine ⟨c, cs, rfl, ?_, ?_⟩ <;>
    · intro hc
      have := Nat.isDigit_of_mem_toDigits (b := 10) (n := n) (c := c) (by decide) (by decide) (by rw [h]; simp)
      subst hc; simp [Char.isDigit] at this

private theorem toString_ofNat (m : Nat) : toString (Int.ofNat m) = toString m := rfl
private theorem toString_negSucc (m : Nat) : toString (Int.negSucc m) = "-" ++ toString (m + 1) := rfl

theorem parseIntegerLex_toString (v : Int) : parseIntegerLex (toString v) = some v := by
  cases v with
  | ofNat m =>
    rw [toString_ofNat, Nat.toString_eq_ofList_toDigits]
    obtain ⟨c, cs, hcs, h1, h2⟩ := head_toDigits m
    have hd := allDigits_toDigits m
    unfold parseIntegerLex
    dsimp only
    rw [String.toList_ofList, hcs]
    rw [hcs] at hd
    split
    · rename_i r h; cases h; exact absurd rfl h1
    · rename_i r h; cases h; exact absurd rfl h2
    · rename_i x hx1 hx2
      simp only [hd, if_true, Bool.false_eq_true, if_false]
      rw [natOfDigits, natOfDigits_eq, ← hcs, Nat.ofDigitChars_ten_toDigits]
      rfl
  | negSucc m =>
    rw [toString_negSucc, Nat.toString_eq_ofList_toDigits]
    have hd := allDigits_toDigits (m + 1)
    unfold parseIntegerLex
    dsimp only
    have hm : "-".toList = ['-'] := by decide
    rw [String.toList_append, hm]
    simp only [String.toList_ofList, List.singleton_append, hd, if_true]
    rw [natOfDigits, natOfDigits_eq, Nat.ofDigitChars_ten_toDigits]
    rfl

/-- For an integer datatype the lexical mapping of the canonical form of `v`
is `v`, inside the type's bounds. -/
theorem lexicalFor_int (b : Builtin) (hb : (intBounds b).isSome = true) (v : Int) :
    lexicalFor .xsd10 b (toString v) =
      if inIntBounds b v then some (.dec (Dec.ofInt v)) else none := by
  have h : parseIntegerLex v.repr = some v := parseIntegerLex_toString v
  cases b <;> simp_all [intBounds, lexicalFor, dtKindOf?, lexicalMap, lexicalMapFuel]

#print axioms parseIntegerLex_toString
#print axioms lexicalFor_int

end L4Factoidal.XSD.IntegerLexTheorems
