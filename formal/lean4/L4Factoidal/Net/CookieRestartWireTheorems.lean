/-
Copyright (c) 2026 Dan Brickley. Released under the Apache 2.0 license.
Persistence of navigation cookies admitted by the executable wire reader.
-/
import L4Factoidal.Net.CookieWireTheorems

namespace L4Factoidal.Net.Cookies

/-- Kind: counter invariant.
Says: folding creation numbers keeps the initial counter and exceeds each number visited.
Does not say: the creation numbers are distinct. -/
private theorem foldCreatedBounds (cs : List Cookie) (start : Nat) :
    start ≤ cs.foldl (fun n c => max n (c.created + 1)) start ∧
    ∀ c ∈ cs, c.created < cs.foldl (fun n c => max n (c.created + 1)) start := by
  induction cs generalizing start with
  | nil => exact ⟨Nat.le_refl _, fun _ h => nomatch h⟩
  | cons x rest ih =>
    obtain ⟨bound, every⟩ := ih (max start (x.created + 1))
    constructor
    · exact Nat.le_trans (Nat.le_max_left _ _) bound
    · intro c h
      rcases List.mem_cons.mp h with eq | tail
      · subst c
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_trans (Nat.le_max_right _ _) bound)
      · exact every c tail

/-- Kind: wire admission and counter invariant.
Says: each cookie the reader accepts passes storage validation, and its creation number
is strictly below the restored counter, even when the input counter is stale.
Does not say: every input row is accepted or every creation number is unique. -/
theorem Jar.ofWire_storage_invariants (s : String) (c : Cookie)
    (present : c ∈ (Jar.ofWire s).cookies) :
    c.storageOK = true ∧ c.created < (Jar.ofWire s).next := by
  change c ∈ (Jar.wireRows s).2.filterMap Cookie.fromFields at present
  constructor
  · obtain ⟨fs, _, found⟩ := List.mem_filterMap.mp present
    unfold Cookie.fromFields at found
    exact (Option.filter_eq_some_iff.mp found).2
  · exact (foldCreatedBounds ((Jar.wireRows s).2.filterMap Cookie.fromFields)
      ((Jar.wireRows s).1.toNat?.getD 0)).2 c present

/-- Kind: restart round trip.
Says: saving the persistent cookies from any decoded wire input and reloading them
reconstructs that persistent jar exactly, including list order and its next counter.
Does not say: a host writes the jar or keeps it between processes. -/
theorem Jar.restart_ofWire (s : String) (savedAt : Nat) :
    Jar.ofWire (((Jar.ofWire s).persistent savedAt).wire) = (Jar.ofWire s).persistent savedAt := by
  apply Jar.ofWire_wire
  · intro c present
    unfold Jar.persistent at present
    exact (Jar.ofWire_storage_invariants s c (List.mem_filter.mp present).1).1
  · intro c present
    unfold Jar.persistent at present
    exact (Jar.ofWire_storage_invariants s c (List.mem_filter.mp present).1).2

#print axioms Jar.ofWire_storage_invariants
#print axioms Jar.restart_ofWire

end L4Factoidal.Net.Cookies
