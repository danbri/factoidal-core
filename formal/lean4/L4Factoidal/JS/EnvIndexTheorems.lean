import L4Factoidal.JS.Value
import L4Factoidal.JS.IndexTheorems

namespace L4Factoidal.JS

/-- Bridge: the recursive scan and Lean core's suffix search.
Says: a scan at an in-range offset returns that offset plus the first suffix match.
Does not say: the offset can exceed the array size. -/
private theorem scan_eq_findIdx (names : Array String) (x : String) (i : Nat)
    (hi : i ≤ names.size) :
    Env.scan names x i = i + (names.toList.drop i).findIdx (· == x) := by
  rw [Env.scan]
  split
  · rename_i hlt
    rw [List.drop_eq_getElem_cons (by simpa using hlt), List.findIdx_cons]
    simp only [Array.getElem_toList]
    cases (names[i] == x)
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.cond_false]
      rw [scan_eq_findIdx names x (i + 1) (by omega)]
      omega
    · simp
  · have heq : i = names.size := by omega
    simp [heq, List.drop_eq_nil_of_le (show names.toList.length ≤ names.size by simp)]
termination_by names.size - i

/-- Bridge: the environment scan and Lean core's first-match search.
Says: scanning from zero returns the first matching slot, or the array size when absent.
Does not say: names must be distinct or that lookup validates a JavaScript program. -/
theorem Env.scan_eq_firstMatch (names : Array String) (x : String) :
    Env.scan names x 0 =
      (((names.toList.zipIdx).find? (fun p => p.1 == x)).map Prod.snd).getD names.size := by
  simpa only [Nat.zero_add, List.drop_zero, List.findIdx_eq_getD_findIdx?,
    List.findIdx?_eq_fst_find?_zipIdx, Array.length_toList]
    using scan_eq_findIdx names x 0 (Nat.zero_le _)

/-- Refinement: the function-layout index against the reference environment scan.
Says: an index built from the environment's names returns exactly the scan's slot or absence.
Does not say: an arbitrary hand-built index is correct or the entire evaluator is verified. -/
theorem Env.slotN_eq_scan_of_indexOf (e : Env)
    (h : e.index = FunInfo.indexOf e.names) (x : String) :
    e.slotN x = Env.scan e.names x 0 := by
  cases hm : FunInfo.indexOf e.names with
  | none => simp [Env.slotN, h, hm]
  | some m =>
    simp only [Env.slotN, h, hm]
    rw [FunInfo.indexOf_lookup e.names m hm x, Env.scan_eq_firstMatch]

/-- Refinement: indexed binding lookup against the same environment without an index.
Says: adding the layout index preserves the complete optional binding, including its flags.
Does not say: every producer or later mutation of an environment keeps its index consistent. -/
theorem Env.get?_with_indexOf (e : Env) (x : String) :
    ({ e with index := FunInfo.indexOf e.names } : Env).get? x =
      ({ e with index := none } : Env).get? x := by
  have hs := Env.slotN_eq_scan_of_indexOf
    ({ e with index := FunInfo.indexOf e.names } : Env) rfl x
  simp only [Env.get?, Env.slot?]
  rw [hs]
  rfl

#print axioms Env.scan_eq_firstMatch
#print axioms Env.slotN_eq_scan_of_indexOf
#print axioms Env.get?_with_indexOf

-- Non-vacuous witnesses: small layouts use the scan; large layouts use the
-- index, including duplicate names, absence and an uninitialised first slot.
private def duplicateLayout : Array String := #[("duplicate" : String)] ++ Array.replicate 24 "duplicate"

#guard (FunInfo.indexOf (Array.replicate 24 "duplicate")).isNone
#guard (FunInfo.indexOf duplicateLayout).isSome
#guard
    let e : Env := { names := duplicateLayout, index := FunInfo.indexOf duplicateLayout }
    e.slotN "duplicate" == 0 && e.slotN "absent" == 25
#guard
    let e : Env := {
      names := duplicateLayout
      vals := #[.hole]
      immut := #[0]
      index := FunInfo.indexOf duplicateLayout }
    (e.get? "duplicate").map (fun b => (b.init, b.mutable)) == some (false, false)

end L4Factoidal.JS
