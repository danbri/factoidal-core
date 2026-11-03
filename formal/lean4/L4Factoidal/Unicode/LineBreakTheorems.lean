/-
L4Factoidal.Unicode.LineBreakTheorems — two facts about
`L4Factoidal.Unicode.LineBreak.breaks` (UAX #14 rules LB2 and LB3,
https://github.com/danbri/factoidal/issues/1167, milestone 4): for a
non-empty text the end of the text is a break position (LB3), and position 0
never is (LB2).
-/
import L4Factoidal.Unicode.LineBreak

namespace L4Factoidal.Unicode.LineBreak

/-- LB3: the end of a non-empty text is always a break position. -/
theorem breaks_contains_end (cs : Array Char) (h : 0 < cs.size) :
    cs.size ∈ breaks cs := by
  simp [breaks, Nat.ne_of_gt h]

/-- LB2: never a break at the start of text. -/
theorem breaks_not_zero (cs : Array Char) (h : 0 < cs.size) : 0 ∉ breaks cs := by
  unfold breaks
  rw [if_neg (Nat.ne_of_gt h)]
  intro hm
  rcases Array.mem_push.mp hm with hm | hm
  · have := (Array.mem_filter.mp hm).2
    simp at this
  · omega

#print axioms breaks_contains_end
#print axioms breaks_not_zero

end L4Factoidal.Unicode.LineBreak
