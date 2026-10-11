import L4Factoidal.Storage.SubjectPageSelection

namespace L4Factoidal.Storage.SubjectRowIndexWireV2

theorem pagesForArray_eq (refs : List PageRef) (subject : Nat) :
    pagesForArray refs.toArray subject = pagesFor refs subject := rfl

private theorem distinctPageRefsGo_eq_loop (pages : List (Nat × PageRef))
    (seen : Std.HashSet (Nat × PageRef)) (reversed : List (Nat × PageRef))
    (agreement : ∀ value, seen.contains value = reversed.any (fun previous => value == previous)) :
    distinctPageRefsGo pages seen reversed = List.eraseDupsBy.loop (· == ·) pages reversed := by
  induction pages generalizing seen reversed with
  | nil => rfl
  | cons current rest inductionHypothesis =>
      cases present : seen.contains current with
      | false =>
          have previous : reversed.any (fun value => current == value) = false :=
            (agreement current).symm.trans present
          simp only [distinctPageRefsGo, present, Bool.false_eq_true, if_false,
            List.eraseDupsBy.loop, previous]
          apply inductionHypothesis
          intro value
          simp only [Std.HashSet.contains_insert, List.any_cons, agreement value]
          rw [BEq.comm]
      | true =>
          have previous : reversed.any (fun value => current == value) = true :=
            (agreement current).symm.trans present
          simp only [distinctPageRefsGo, present, if_true, List.eraseDupsBy.loop, previous]
          exact inductionHypothesis seen reversed agreement

theorem distinctPageRefs_eq_eraseDups (pages : List (Nat × PageRef)) :
    distinctPageRefs pages = pages.eraseDups := by
  apply distinctPageRefsGo_eq_loop
  intro value
  simp

/-- Exact page identities, duplicate removal and read order for every
    directory and requested ID list. No sortedness or admission premise is
    needed: callers retain their existing validation obligations. -/
theorem candidatePages_eq_reference (refs : List PageRef) (ids : List Nat) :
    candidatePages refs ids =
      ((ids.flatMap (pagesFor refs)).eraseDups.toArray.qsort
        (fun left right => left.1 < right.1)).toList := by
  unfold candidatePages
  dsimp only
  rw [distinctPageRefs_eq_eraseDups]
  rfl

#print axioms candidatePages_eq_reference

end L4Factoidal.Storage.SubjectRowIndexWireV2
