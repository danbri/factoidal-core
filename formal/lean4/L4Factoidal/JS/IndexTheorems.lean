import L4Factoidal.JS.Syntax

namespace L4Factoidal.JS

/-- Invariant: a fold that retains existing entries.
Says: lookup keeps an existing value or takes the first new matching pair.
Does not say: a hash map must be built by this fold. -/
private theorem firstInsert_lookup (xs : List (String × Nat))
    (m : Std.HashMap String Nat) (x : String) :
    (xs.foldl (fun acc (k, i) => if acc.contains k then acc else acc.insert k i) m).get? x =
      (m.get? x).orElse (fun _ => (xs.find? (fun p => p.1 == x)).map Prod.snd) := by
  induction xs generalizing m with
  | nil => simp
  | cons p xs ih =>
    rcases p with ⟨k, i⟩
    simp only [List.foldl_cons]
    rw [ih]
    by_cases hk : k = x
    · subst k
      rw [Std.HashMap.contains_eq_isSome_getElem?]
      cases hg : m[x]? <;> simp [hg]
    · split <;> simp [hk, Std.HashMap.getElem?_insert]

/-- Invariant: the index built by `FunInfo.indexOf`.
Says: its lookup returns the slot of the first matching layout entry, including duplicates.
Does not say: layouts must have distinct names or must use an index. -/
theorem FunInfo.indexOf_lookup (layout : Array String) (m : Std.HashMap String Nat)
    (h : FunInfo.indexOf layout = some m) (x : String) :
    m.get? x = ((layout.toList.zipIdx).find? (fun p => p.1 == x)).map Prod.snd := by
  unfold FunInfo.indexOf at h
  split at h
  · cases h
    rw [← Array.foldl_toList, Array.toList_zipIdx, firstInsert_lookup]
    simp
  · cases h

#print axioms FunInfo.indexOf_lookup

end L4Factoidal.JS
