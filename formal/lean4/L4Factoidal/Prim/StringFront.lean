/-!
# L4Factoidal.Prim.StringFront — `String.front` compiled as one read

`String.front` is defined through a slice of the string and the optional character at its start.
Compiled by Lean 4.33.1 that is a `String.Slice` record and an `Option` cell for each call (read
from the generated code: `ctor String.Slice.mk`, then `String.Slice.Pos.get?`). BubblePopJS asks
for the first character of a property key on nearly every property access: is it a Symbol's key
(`isSymKey`), a private name's (`isPrivKey`), a digit (`getV`, before it looks for an array index).

`String.frontFast` is the first character by the string's own read at byte 0
(`String.Pos.Raw.get`, one runtime call, nothing allocated). `String.front_eq_frontFast` proves
it equal to `String.front` for every string, and is registered with `@[csimp]`: in every module
that imports this one, directly or through another, the compiled program runs `frontFast` where
the source says `front`. No definition changes, so no theorem about `front` changes.
-/

/-- The first character, or `default` for the empty string: `String.front`, by one read. -/
@[inline] def String.frontFast (s : String) : Char := String.Pos.Raw.get s 0

theorem String.front_eq_get_zero (s : String) : s.front = String.Pos.Raw.get s 0 := by
  rw [String.front_eq, String.front?_eq]
  unfold String.Pos.Raw.get
  cases s.toList with
  | nil => rfl
  | cons c cs => simp [String.Pos.Raw.utf8GetAux]

/-- **Kind: refinement.** `frontFast` is `front`, for every string (the empty one and strings
that start with a character of several bytes included). Does not say anything about speed. -/
@[csimp] theorem String.front_eq_frontFast : @String.front = @String.frontFast := by
  funext s; exact String.front_eq_get_zero s

#print axioms String.front_eq_frontFast

#guard "".front == "".frontFast && "abc".front == "abc".frontFast && "∃x".front == "∃x".frontFast
#guard (String.singleton (Char.ofNat 0x10FFFF) ++ "7").frontFast == Char.ofNat 0x10FFFF
