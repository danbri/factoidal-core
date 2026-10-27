/-
L4Factoidal.XSD.CanonicalTheorems — the canonical mapping of XSD 1.1 Part 2
(§2.3.1, §3.3, §3.4) maps back to the value: the lexical mapping of the
canonical representation of a value is that value.

  * `floatingCanonical_roundTrip`, `float_canonical_roundTrip`,
    `double_canonical_roundTrip` — §3.3.4.2 / §3.3.5.2 (§E.1): when the
    search of `floatingCanonical?` answers (the `#guard`s of
    `DatatypesTests.lean` show that it does), its text maps back to the
    value under the lexical mapping every reader calls. The specials and the
    zeros are closed by cases.
  * `integer_canonical_roundTrip` — §3.3.13 and the §3.4 integer tower: for
    each integer datatype, an integer in the type's bounds.
  * `string_canonical_roundTrip` — §3.3.1.
  * `boolean_canonical_roundTrip` is in `DatatypesTheorems.lean`.

The round trip for `decimal`, the durations and the date/time types is
measured by the `#guard`s (`DatatypesTests.lean`,
`RDF/LiteralValue.lean`), not proved here.

Used by `RDF/LiteralValue.lean` (the `canonical` member of the literal-value
op, https://github.com/danbri/factoidal/issues/1051).

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.XSD.IntegerLexTheorems

namespace L4Factoidal.XSD.CanonicalTheorems
open L4Factoidal.XSD

theorem canonicalSearch_ok (ok : String → Bool) (neg : Bool) (c : Nat) (e : Int) :
    ∀ (l : Nat) (s : String), canonicalSearch ok neg c e l = some s → ok s = true
  | 0, s, h => by
      simp only [canonicalSearch] at h
      split at h
      · rename_i hok; simp at h; subst h; exact hok
      · simp at h
  | l + 1, s, h => by
      simp only [canonicalSearch] at h
      split at h
      · rename_i hok; simp at h; subst h
        simp only [Bool.and_eq_true] at hok; exact hok.2
      · exact canonicalSearch_ok ok neg c e l s h

theorem mapsBackTo_double {v : Fval} {s : String} (h : mapsBackTo true v s = true) :
    lexicalMap .double s = some (.dbl v) := by
  unfold mapsBackTo at h
  simp only [if_true] at h
  split at h
  · rename_i g hg; simp at h; rw [hg, h]
  · simp at h
  · simp at h

theorem mapsBackTo_float {v : Fval} {s : String} (h : mapsBackTo false v s = true) :
    lexicalMap .float s = some (.flt v) := by
  unfold mapsBackTo at h
  simp only [Bool.false_eq_true, if_false] at h
  split at h
  · simp at h
  · rename_i g hg; simp at h; rw [hg, h]
  · simp at h

theorem floatingCanonical?_ok {isDouble : Bool} {v : Fval} {s : String}
    (h : floatingCanonical? isDouble v = some s) : mapsBackTo isDouble v s = true := by
  unfold floatingCanonical? at h
  split at h
  · exact canonicalSearch_ok _ _ _ _ _ _ h
  · simp at h

/-- §3.3.5.2: the canonical representation the search finds maps back to the
value, and it is what `canonicalMap .double` answers. -/
theorem double_canonical_roundTrip {v : Fval} {s : String}
    (h : floatingCanonical? true v = some s) :
    canonicalMap .double (.dbl v) = s ∧ lexicalMap .double s = some (.dbl v) := by
  refine ⟨?_, mapsBackTo_double (floatingCanonical?_ok h)⟩
  show floatingCanonical true v = s
  simp [floatingCanonical, h]

/-- §3.3.4.2: the same for `float`. -/
theorem float_canonical_roundTrip {v : Fval} {s : String}
    (h : floatingCanonical? false v = some s) :
    canonicalMap .float (.flt v) = s ∧ lexicalMap .float s = some (.flt v) := by
  refine ⟨?_, mapsBackTo_float (floatingCanonical?_ok h)⟩
  show floatingCanonical false v = s
  simp [floatingCanonical, h]

/-- The specials and the signed zeros of `double` (§3.3.5.2) map back. -/
theorem double_special_roundTrip :
    lexicalMap .double (canonicalMap .double (.dbl ⟨false, .nan⟩)) = some (.dbl ⟨false, .nan⟩) ∧
    lexicalMap .double (canonicalMap .double (.dbl ⟨false, .inf⟩)) = some (.dbl ⟨false, .inf⟩) ∧
    lexicalMap .double (canonicalMap .double (.dbl ⟨true, .inf⟩)) = some (.dbl ⟨true, .inf⟩) ∧
    lexicalMap .double (canonicalMap .double (.dbl ⟨false, .zero⟩)) = some (.dbl ⟨false, .zero⟩) ∧
    lexicalMap .double (canonicalMap .double (.dbl ⟨true, .zero⟩)) = some (.dbl ⟨true, .zero⟩) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

private theorem norm_ofInt (v : Int) : Dec.norm (Dec.ofInt v) = Dec.ofInt v := by
  simp [Dec.norm, Dec.ofInt, Dec.normFuel]

/-- §3.3.13 / §3.4.13-§3.4.25: for every integer datatype, the canonical
representation of an integer in the type's bounds maps back to it. -/
theorem integer_canonical_roundTrip (b : Builtin) (hb : (intBounds b).isSome = true) (v : Int)
    (hin : inIntBounds b v = true) :
    lexicalMap b (canonicalMap b (.dec (Dec.ofInt v))) = some (.dec (Dec.ofInt v)) := by
  have hp : parseIntegerLex (toString v) = some v := IntegerLexTheorems.parseIntegerLex_toString v
  have hd : derivedFrom b .integer = true := by cases b <;> simp_all [intBounds] <;> decide
  have hc : canonicalMap b (.dec (Dec.ofInt v)) = toString v := by
    simp only [canonicalMap, canonicalMapFuel, hd, if_true, norm_ofInt]
    rfl
  rw [hc]
  cases b <;> simp_all [intBounds, lexicalMap, lexicalMapFuel] <;> rfl

/-- §3.3.1: `string` (whiteSpace `preserve`) — the value is the string. -/
theorem string_canonical_roundTrip (s : String) :
    lexicalMap .string (canonicalMap .string (.str .string s)) = some (.str .string s) := rfl

#print axioms canonicalSearch_ok
#print axioms double_canonical_roundTrip
#print axioms float_canonical_roundTrip
#print axioms double_special_roundTrip
#print axioms integer_canonical_roundTrip
#print axioms string_canonical_roundTrip

end L4Factoidal.XSD.CanonicalTheorems
