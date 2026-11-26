import EVMCleanroom.Core

/-!
# Executable ADDMOD and MULMOD semantics

Theorems were specified for the full-precision EVM operations before wiring
them into the guarded frame. An EVM word is a residue modulo 2^256. The
modulus operand belongs to the same word domain. Unlike ADD and MUL, these
instructions reduce the mathematical sum/product by that modulus *before*
word conversion. A zero modulus returns zero.

The Core.step_addMod and Core.step_mulMod theorems connect both Word helpers
to the actual executable dispatch, stack order and the eight-gas commit path.
This does not claim fork-complete interpreter correctness.
-/

namespace EVMCleanroom

/-- Kind: mathematical correspondence.
    ADDMOD observes the untruncated sum, with zero for a zero modulus. -/
theorem Word.addMod_correct (a b m : Word) :
    (a.addMod b m).val =
      if m.val = 0 then 0 else (a.val + b.val) % m.val := by
  by_cases hZero : m.val = 0
  · simp [Word.addMod, hZero, word]
  · have hPos : 0 < m.val := by omega
    have hSmall : (a.val + b.val) % m.val < modulus :=
      Nat.lt_trans (Nat.mod_lt _ hPos) m.isLt
    simp [Word.addMod, hZero, word, Nat.mod_eq_of_lt hSmall]

/-- Kind: mathematical correspondence.
    MULMOD observes the untruncated product, with zero for a zero modulus. -/
theorem Word.mulMod_correct (a b m : Word) :
    (a.mulMod b m).val =
      if m.val = 0 then 0 else (a.val * b.val) % m.val := by
  by_cases hZero : m.val = 0
  · simp [Word.mulMod, hZero, word]
  · have hPos : 0 < m.val := by omega
    have hSmall : (a.val * b.val) % m.val < modulus :=
      Nat.lt_trans (Nat.mod_lt _ hPos) m.isLt
    simp [Word.mulMod, hZero, word, Nat.mod_eq_of_lt hSmall]

#print axioms Word.addMod_correct
#print axioms Word.mulMod_correct

end EVMCleanroom
