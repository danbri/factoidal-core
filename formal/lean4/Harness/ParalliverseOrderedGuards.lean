import L4Factoidal.Paralliverse.Ordered

open L4Factoidal.Paralliverse.Ordered

-- Executable examples of the collector, independent of the general proofs.
#guard collect? (α := Nat) 0 [] == some []
#guard collect? 0 [(0, 23)] == none
#guard collect? 1 [(0, 23)] == some [23]
#guard collect? 2 [(1, 23)] == none
#guard collect? 2 [(0, 23), (0, 23)] == none
#guard collect? 2 [(2, 99), (0, 23)] == none
#guard collect? 3 [(2, [7]), (0, [7]), (1, [])] == some [[7], [], [7]]
