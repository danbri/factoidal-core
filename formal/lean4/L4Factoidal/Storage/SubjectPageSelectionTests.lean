import L4Factoidal.Storage.SubjectPageSelection

namespace L4Factoidal.Storage.SubjectRowIndexWireV2

private def ref0 : PageRef := ⟨1, 7, 0, 2048⟩
private def ref1 : PageRef := ⟨7, 7, 2048, 2048⟩
private def ref2 : PageRef := ⟨7, 12, 4096, 2048⟩
private def ref3 : PageRef := ⟨20, 30, 6144, 2048⟩
private def refs : List PageRef := [ref0, ref1, ref2, ref3]

-- Exact page identity and order, including a posting spanning three pages.
#guard candidatePages refs [7] == [(0, ref0), (1, ref1), (2, ref2)]
#guard candidatePages refs [30, 7, 1, 7, 20] ==
  [(0, ref0), (1, ref1), (2, ref2), (3, ref3)]
#guard candidatePages refs [0, 13, 19, 31] == []
#guard candidatePages refs [] == []
#guard candidatePages [] [1, 1] == []

-- Keep the old algorithm as an independent regression oracle.
private def reference (directory : List PageRef) (ids : List Nat) :=
  ((ids.flatMap (pagesFor directory)).eraseDups.toArray.qsort
    (fun left right => left.1 < right.1)).toList

#guard (List.range 35).all fun subject =>
  pagesForArray refs.toArray subject == pagesFor refs subject
#guard (List.range 35).all fun subject =>
  candidatePages refs [subject, 7, subject, 30] == reference refs [subject, 7, subject, 30]

-- Exact equivalence also applies to malformed directories: admission is
-- a separate contract, and this optimization must not weaken it.
#guard candidatePages refs.reverse [7, 1, 7, 30] == reference refs.reverse [7, 1, 7, 30]
#guard distinctPageRefs [(0, ref0), (0, ref1), (0, ref0)] ==
  [(0, ref0), (0, ref1)]

end L4Factoidal.Storage.SubjectRowIndexWireV2
