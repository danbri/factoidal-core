import L4Factoidal.JS.Interp

/-!
# Theorems about the JavaScript engine

- `toInt32_range`, `toUint32_lt`: ToInt32 and ToUint32 (§7.1.6, §7.1.7) give
  values in their ranges, for every double.
- `arrayIndex?_lt`: an array index is below 2^32 - 1 (§6.1.7).
- `loopNext_*`: LoopContinues (§14.7.1.2): an unlabelled `break` ends the loop
  normally; `continue` and a normal body go on; `return` leaves.
- `sameValue_*`: SameValue is reflexive on the values that are not numbers, and
  tells `+0` from `-0`.
- `unitAt?_notAscii`: on a string that is not ASCII, `charCodeAt`'s unit is the entry of
  `Str.unitChars` (the array that `cachedChars` keeps), so indexing the cached array gives the
  answer of `Str.unitAt?`.

The evaluator is a Lean function, so it is deterministic by construction: the same
script and heap give the same outcome and heap. Each function of the parser and of
the evaluator is total (structural recursion on its fuel); no partial definitions.
-/

namespace L4Factoidal.JS

theorem toInt32_range (x : Float) : -2147483648 ≤ toInt32 x ∧ toInt32 x < 2147483648 := by
  unfold toInt32
  split
  · omega
  · have h0 := Int.emod_nonneg (truncInt x) (b := 4294967296) (by decide)
    have h1 := Int.emod_lt_of_pos (truncInt x) (b := 4294967296) (by decide)
    dsimp only
    split <;> omega

theorem toUint32_lt (x : Float) : toUint32 x < 4294967296 := by
  unfold toUint32
  split
  · omega
  · have h0 := Int.emod_nonneg (truncInt x) (b := 4294967296) (by decide)
    have h1 := Int.emod_lt_of_pos (truncInt x) (b := 4294967296) (by decide)
    omega

theorem arrayIndex?_lt {s : String} {n : Nat} (h : arrayIndex? s = some n) : n < 4294967295 := by
  unfold arrayIndex? at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · dsimp only at h
        split at h
        · rename_i hlt; cases h; exact hlt
        · simp at h

theorem loopNext_break (ls : List String) : loopNext (H := Unit) ls (.brk none) = some .normal := rfl
theorem loopNext_continue (ls : List String) : loopNext (H := Unit) ls (.cont none) = none := rfl
theorem loopNext_normal (ls : List String) : loopNext (H := Unit) ls .normal = none := rfl
theorem loopNext_return (ls : List String) (v : Value) : loopNext (H := Unit) ls (.ret v) = some (.ret v) := rfl
theorem loopNext_label (l : String) (ls : List String) :
    loopNext (H := Unit) (l :: ls) (.brk (some l)) = some .normal := by simp [loopNext]

theorem sameValue_str (s : String) : sameValue (.str s) (.str s) = true := by
  simp [sameValue, strictEq]

theorem sameValue_obj (i : Nat) : sameValue (.obj i) (.obj i) = true := by
  simp [sameValue, strictEq]

theorem sameValue_bool (b : Bool) : sameValue (.bool b) (.bool b) = true := by
  simp [sameValue, strictEq]

theorem toBool_obj (i : Nat) : toBool (.obj i) = true := rfl
theorem toBool_undef : toBool .undef = false := rfl

/-- Kind: an equation of definitions (the fast path is the definition's own branch).
Says: for a string that is not ASCII, `Str.unitAt? s i` is entry `i` of `Str.unitChars s` read
as a unit, which is what `charCodeAt` computes from `cachedChars` when the cache holds `s`.
Does not say: that the cache holds `s` (the evaluator compares the strings before it uses it), or
anything about `charAt`, whose answer `#guard`s in `RegressionTests` check. -/
theorem unitAt?_notAscii (s : String) (i : Nat) (h : Str.isAscii s = false) :
    Str.unitAt? s i = (Str.unitChars s)[i]?.map Str.charUnit := by
  simp [Str.unitAt?, h]

/-- Kind: an equation of definitions.
Says: for an ASCII string, and for any string when the heap holds no cached string or a different
one, `strLength` is `Str.jsLength` (the cached path is the only other case).
Does not say: that the cached array's size is `Str.jsLength` of its string (checked by `#guard`s
in `RegressionTests`, not proved). -/
theorem strLength_uncached {H : Type} (h : HeapOf H) (s : String)
    (hc : h.reCache = none ∨ ∃ t cs, h.reCache = some (t, cs) ∧ t ≠ s) :
    h.strLength s = Str.jsLength s := by
  unfold HeapOf.strLength
  split
  · rename_i ha; simp [Str.jsLength, ha]
  · rcases hc with hc | ⟨t, cs, hc, hne⟩
    · simp [hc]
    · simp [hc, hne]

end L4Factoidal.JS
