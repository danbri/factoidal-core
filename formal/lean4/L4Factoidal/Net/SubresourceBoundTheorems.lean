import L4Factoidal.Net.Subresource

namespace L4Factoidal.Net.Subresource

open L4Factoidal.Net.PageFetch

/-- Kind: table-size invariant.
Says: the underlying step transition adds at most one live entry.
Does not say: that the caller has space for that entry. -/
private theorem after_live_length_le (tab : Table) (id : Nat) (last : Option Answer) (st : Step) :
    (after tab id last st).1.live.length ≤ tab.live.length + 1 := by
  cases st with
  | send t w => exact Nat.le_refl _
  | fail why => exact Nat.le_succ _
  | deliver t r =>
    cases last with
    | none => exact Nat.le_succ _
    | some a =>
      simp only [after]
      split
      · exact Nat.le_succ _
      · split <;> exact Nat.le_succ _

/-- Kind: list cardinality lemma.
Says: a filter that rejects one member strictly shortens the list.
Does not say: that the rejected member occurred only once. -/
private theorem filter_length_lt_of_rejected {α : Type} (keep : α → Bool)
    (xs : List α) (x : α) (hx : x ∈ xs) (hreject : keep x = false) :
    (xs.filter keep).length < xs.length := by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    by_cases hy : keep y = true
    · have hyx : x ≠ y := by
        intro he
        subst x
        simp [hreject] at hy
      have htail := ih ((List.mem_cons.mp hx).resolve_left hyx)
      simp only [List.filter_cons_of_pos hy, List.length_cons]
      exact Nat.succ_lt_succ htail
    · rw [List.filter_cons_of_neg hy, List.length_cons]
      exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- Kind: subresource table bound.
Says: starting a request on a table within its cap preserves that cap, including
when the first step tells the host to send.
Does not say: that the request succeeds or that it allocates a bounded number of bytes. -/
theorem start_live_bound (tab : Table) (page : Page) (kind url referrer : String)
    (policy : ReferrerPolicy.Policy) (cors : Option Bool) (h : tab.live.length ≤ maxLive) :
    (start tab page kind url referrer policy cors).1.live.length ≤ maxLive := by
  simp only [start]
  split
  · exact h
  · split
    · exact h
    · rename_i hroom
      split
      · exact h
      · refine Nat.le_trans (after_live_length_le _ _ _ _) ?_
        change tab.live.length + 1 ≤ maxLive
        omega

/-- Kind: subresource table bound.
Says: answering a request never increases the live transfer count. A send step
can reinsert one entry only after the matching entry has been removed, including
when a reply advances a redirect or a preflight.
Does not say: that there is only one entry per identifier, or that a host reply
finishes the transfer. -/
theorem answer_live_nonincrease (tab : Table) (id : Nat) (a : Answer) :
    (answer tab id a).1.live.length ≤ tab.live.length := by
  unfold answer
  split
  · exact Nat.le_refl _
  · rename_i i t hfind
    have hmem : (i, t) ∈ tab.live := List.mem_of_find?_eq_some hfind
    have hid : i = id := by simpa using List.find?_some hfind
    have hreject : ((i, t).1 != id) = false := by simp [hid]
    have hlt := filter_length_lt_of_rejected (·.1 != id) tab.live (i, t) hmem hreject
    exact Nat.le_trans (after_live_length_le _ _ _ _) (Nat.succ_le_of_lt hlt)

/-- Kind: subresource table bound.
Says: cancelling any identifier can only reduce or preserve the live transfer count.
Does not say: how many entries the cancellation removes. -/
theorem cancel_live_nonincrease (tab : Table) (id : Nat) :
    (cancel tab id).live.length ≤ tab.live.length :=
  List.length_filter_le _ _

/-- Kind: subresource transition invariant.
Says: a table within the live transfer cap remains within it after any one of
the three public transitions. The default table satisfies the initial bound
because its live list is empty.
Does not say: that an externally supplied over-cap table is restored to the cap. -/
theorem live_bound_preserved (tab : Table) (h : tab.live.length ≤ maxLive) :
    (∀ (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy) (cors : Option Bool),
      (start tab page kind url referrer policy cors).1.live.length ≤ maxLive) ∧
    (∀ (id : Nat) (a : Answer), (answer tab id a).1.live.length ≤ maxLive) ∧
    (∀ id : Nat, (cancel tab id).live.length ≤ maxLive) :=
  ⟨fun page kind url referrer policy cors => start_live_bound tab page kind url referrer policy cors h,
   fun id a => Nat.le_trans (answer_live_nonincrease tab id a) h,
   fun id => Nat.le_trans (cancel_live_nonincrease tab id) h⟩

#print axioms start_live_bound
#print axioms answer_live_nonincrease
#print axioms cancel_live_nonincrease
#print axioms live_bound_preserved

end L4Factoidal.Net.Subresource
