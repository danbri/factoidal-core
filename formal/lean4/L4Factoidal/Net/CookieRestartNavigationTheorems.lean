/-
Copyright (c) 2026 Dan Brickley. Released under the Apache 2.0 license.
The ordered navigation cookie list after an executable persistence round trip.
-/
import L4Factoidal.Net.CookieRestartWireTheorems

namespace L4Factoidal.Net.Cookies

/-- Kind: stable sorting lemma.
Says: the new head precedes all tied elements and separates strictly earlier elements
from the rest of the sorted tail.
Does not say: different elements have different sorting keys. -/
private theorem insertionParts {α : Type} (le : α → α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (a : α) (xs : List α) :
    ∃ front back, (a :: xs).mergeSort le = front ++ a :: back ∧
      xs.mergeSort le = front ++ back ∧ (∀ b ∈ front, !le a b) ∧ (∀ b ∈ back, le a b) := by
  obtain ⟨front, back, whole, tail, earlier⟩ := List.mergeSort_cons trans total a xs
  have sorted := List.pairwise_mergeSort trans total (a :: xs)
  rw [whole, List.pairwise_append] at sorted
  exact ⟨front, back, whole, tail, earlier, (List.pairwise_cons.mp sorted.2.1).1⟩

/-- Kind: list partition lemma.
Says: the strict comparison recovers the earlier block of an insertion split.
Does not say: the two blocks have distinct elements. -/
private theorem recoverFront {α : Type} (le : α → Bool) (front back : List α)
    (earlier : ∀ x ∈ front, !le x) (later : ∀ x ∈ back, le x) :
    (front ++ back).filter (fun x => !le x) = front := by
  have removed : back.filter (fun x => !le x) = [] :=
    List.filter_eq_nil_iff.mpr (fun x hx => by simp [later x hx])
  rw [List.filter_append, List.filter_eq_self.mpr earlier, removed, List.append_nil]

/-- Kind: stable sorting lemma.
Says: selecting a subsequence before a stable merge sort yields exactly the same list
as selecting that subsequence from the sorted output.
Does not say: this holds for an unstable sorting implementation. -/
private theorem filterMergeSort {α : Type} (le : α → α → Bool) (keep : α → Bool)
    (trans : ∀ a b c, le a b → le b c → le a c) (total : ∀ a b, le a b || le b a)
    (xs : List α) : (xs.filter keep).mergeSort le = (xs.mergeSort le).filter keep := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨front, back, whole, tail, earlier, later⟩ := insertionParts le trans total a xs
    rw [whole, List.filter_append]
    by_cases ha : keep a
    · rw [List.filter_cons_of_pos ha, List.filter_cons_of_pos ha]
      obtain ⟨front', back', whole', tail', earlier', later'⟩ :=
        insertionParts le trans total a (xs.filter keep)
      have parts : front' ++ back' = front.filter keep ++ back.filter keep := by
        rw [← tail', ih, tail, List.filter_append]
      have frontEq : front' = front.filter keep := by
        calc
          front' = (front' ++ back').filter (fun b => !le a b) :=
            (recoverFront (le a) front' back' earlier' later').symm
          _ = (front.filter keep ++ back.filter keep).filter (fun b => !le a b) :=
            congrArg (fun l : List α => l.filter (fun b => !le a b)) parts
          _ = front.filter keep := recoverFront (le a) _ _
            (fun b hb => earlier b (List.mem_filter.mp hb).1)
            (fun b hb => later b (List.mem_filter.mp hb).1)
      have backEq : back' = back.filter keep := by
        rw [frontEq] at parts
        exact List.append_cancel_left parts
      rw [whole', frontEq, backEq]
    · rw [List.filter_cons_of_neg ha, List.filter_cons_of_neg ha, ih, tail, List.filter_append]

/-- Kind: restart navigation refinement.
Says: after saving and reloading the wire jar, the requested cookies are the original
ordered navigation list filtered by expiry presence and liveness at save time. Ties
and repeated cookies retain their positions relative to every other surviving cookie.
Does not say: the host actually issued a request or transmitted the header. -/
theorem navCookies_restart_filter (s : String) (site : Site) (initiator : String)
    (savedAt sendAt : Nat) (method : String) :
    navCookies (Jar.ofWire (((Jar.ofWire s).persistent savedAt).wire)) site initiator sendAt method =
      (navCookies (Jar.ofWire s) site initiator sendAt method).filter
        (fun c => c.expires.isSome && !expired c savedAt) := by
  rw [Jar.restart_ofWire]
  let keep := fun c : Cookie => c.expires.isSome && !expired c savedAt
  let nav := sentNav site sendAt (navSameSite site initiator) (method == "GET")
  let cmp := fun a b : Cookie => a.path.length > b.path.length ||
    (a.path.length == b.path.length && a.created ≤ b.created)
  change (((Jar.ofWire s).cookies.filter keep).filter nav).mergeSort cmp =
    (((Jar.ofWire s).cookies.filter nav).mergeSort cmp).filter keep
  have commute : ((Jar.ofWire s).cookies.filter keep).filter nav =
      ((Jar.ofWire s).cookies.filter nav).filter keep := by
    simp only [List.filter_filter]
    apply List.filter_congr
    exact fun c _ => Bool.and_comm (nav c) (keep c)
  rw [commute]
  apply filterMergeSort
  · intro a b c ab bc
    simp only [cmp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ab bc ⊢
    omega
  · intro a b
    simp only [cmp, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    omega

/-- Kind: forward-clock navigation refinement.
Says: when the save precedes the request, restart retains exactly the original navigation
cookies with an expiry, in order. The request's own expiry check accounts for the save time.
Does not say: this simplification holds if the clock moves backwards. -/
theorem navCookies_restart_forward (s : String) (site : Site) (initiator : String)
    (savedAt sendAt : Nat) (method : String) (clock : savedAt ≤ sendAt) :
    navCookies (Jar.ofWire (((Jar.ofWire s).persistent savedAt).wire)) site initiator sendAt method =
      (navCookies (Jar.ofWire s) site initiator sendAt method).filter (fun c => c.expires.isSome) := by
  rw [navCookies_restart_filter]
  apply List.filter_congr
  intro c hc
  have selected := (List.mem_filter.mp (List.mem_mergeSort.mp hc)).2
  unfold sentNav at selected
  simp only [Bool.and_eq_true] at selected
  have live : expired c sendAt = false := by
    simpa only [Bool.not_eq_true'] using selected.1.2
  have savedLive : expired c savedAt = false := by
    cases expiration : c.expires with
    | none => simp [expired, expiration]
    | some t =>
      simp only [expired, expiration, decide_eq_false_iff_not] at live ⊢
      omega
  simp [savedLive]

#print axioms navCookies_restart_filter
#print axioms navCookies_restart_forward

end L4Factoidal.Net.Cookies
