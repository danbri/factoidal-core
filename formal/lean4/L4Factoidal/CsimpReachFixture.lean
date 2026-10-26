/-
L4Factoidal.CsimpReachFixture -- KNOWN-BAD EXAMPLES, KEPT ON PURPOSE
(https://github.com/danbri/factoidal/issues/871).

A `@[csimp]` theorem `@f = @g` makes the compiler emit `g` wherever the source
calls `f`. The replacement is made while a declaration is turned into the
compiler's intermediate form, and only for the declarations compiled after the
theorem. A call of `f` that reaches a caller through a definition compiled
BEFORE the theorem and inlined into the caller afterwards keeps calling `f` in
the emitted C. The first measured case was `Hashable Term` on 2026-10-15
(skills/lean4-proof-patterns/SKILL.md, section 9d): a `@[csimp]` theorem for the
derived hash built, and the C of `FastGraph` still called the recursive function.

This module reproduces the mechanism with the smallest functions that show it.
`tools/lean-csimp-reach.py` must report the callers marked BAD below and must
not report `callDirect`. The self-test `tools/test_lean_csimp_reach.py` asserts
both on the emitted C of this module. The bad callers are NOT repaired, because
the repair would remove the example. `tools/lean-csimp-reach-allow.txt` lists
them with this reason, so the gate of the whole tree stays green.

Callers, with the reason the replacement does not reach them:

* `callBefore` is compiled before the theorem.
* `callViaInstance` calls `Weigh.weigh`; the compiler inlines the instance
  `instWeighList`, compiled before the theorem, and its body names `weightSpec`.
* `callViaInline` calls `weightInline`, an `@[inline]` definition compiled before
  the theorem; the compiler inlines its body, which names `weightSpec`.
* `callDirect` is compiled after the theorem and names the specification: the
  compiler replaces it, and the emitted C calls `weightFast`. It is the control.

`#guard` and `#eval` code is not emitted into the C of a module, so the `#guard`
lines at the end cannot be seen by the tool and need no rule of their own; the
self-test checks that no extra function appears for them.
-/

namespace L4Factoidal.CsimpReachFixture

/-- The specification: one native frame for each element of the list. -/
def weightSpec : List Nat → Nat
  | [] => 0
  | x :: xs => x + weightSpec xs

/-- A class through which a caller reaches the specification. -/
class Weigh (α : Type) where
  weigh : α → Nat

/-- An instance compiled before the theorem. Its method is the specification. -/
instance instWeighList : Weigh (List Nat) := ⟨weightSpec⟩

/-- An inline definition compiled before the theorem. -/
@[inline] def weightInline (xs : List Nat) : Nat := weightSpec xs

/-- BAD: compiled before the theorem. -/
def callBefore (xs : List Nat) : Nat := weightSpec xs

/-- The tail-recursive twin: the sum so far, then the rest of the list. -/
def weightLoop : List Nat → Nat → Nat
  | [], acc => acc
  | x :: xs, acc => weightLoop xs (acc + x)

/-- The twin, with the empty list as the start. -/
def weightFast (xs : List Nat) : Nat := weightLoop xs 0

theorem weightLoop_eq : ∀ (xs : List Nat) (acc : Nat),
    weightLoop xs acc = acc + weightSpec xs
  | [], acc => by simp [weightLoop, weightSpec]
  | x :: xs, acc => by
      simp only [weightLoop, weightSpec]
      rw [weightLoop_eq xs (acc + x)]
      omega

theorem weightFast_eq (xs : List Nat) : weightFast xs = weightSpec xs := by
  simp [weightFast, weightLoop_eq]

/-- The compiler emits `weightFast` for the code compiled after this line that names
`weightSpec` itself. -/
@[csimp] theorem weightSpec_eq_weightFast : @weightSpec = @weightFast :=
  funext fun xs => (weightFast_eq xs).symm

/-- Control: names the specification after the theorem. The emitted C calls `weightFast`. -/
def callDirect (xs : List Nat) : Nat := weightSpec xs

/-- BAD: reaches `weightSpec` through the inlined instance `instWeighList`. -/
def callViaInstance (xs : List Nat) : Nat := Weigh.weigh xs

/-- BAD: reaches `weightSpec` through the inlined body of `weightInline`. -/
def callViaInline (xs : List Nat) : Nat := weightInline xs

#guard callDirect [1, 2, 3] == 6
#guard callViaInstance [1, 2, 3] == 6
#guard callViaInline [4, 5] == 9
#guard callBefore [] == 0

#print axioms weightFast_eq
#print axioms weightSpec_eq_weightFast

end L4Factoidal.CsimpReachFixture
