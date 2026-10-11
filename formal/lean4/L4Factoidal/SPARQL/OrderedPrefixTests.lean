import L4Factoidal.SPARQL.OrderedPrefix

namespace L4Factoidal.SPARQL.OrderedPrefixTests

/-- Ties retain payload order, and even non-transitive comparators agree with
    the existing merge sort. The optimization requires no comparator laws. -/
private def rows : List (Nat × Nat) :=
  [(2, 0), (1, 1), (2, 2), (0, 3), (1, 4), (2, 5), (0, 6)]
private def comparators : List ((Nat × Nat) → (Nat × Nat) → Bool) :=
  [fun a b => a.1 ≤ b.1, fun a b => a.1 ≥ b.1,
   fun _ _ => true, fun _ _ => false,
   fun a b => (a.1 + 1) % 3 == b.1 % 3]
#guard comparators.all fun le =>
  (List.range 12).all fun k =>
    mergeSortPrefix rows le k == (rows.mergeSort le).take k
#guard mergeSortPrefix ([] : List Nat) (· ≤ ·) 4 == []
#guard mergeSortPrefix [7] (· ≤ ·) 0 == []
#guard mergeSortPrefix [7] (· ≤ ·) 1 == [7]
#guard mergeSortPrefix [3, 2, 1] (· ≤ ·) 2 == [1, 2]
#guard mergeSortPrefix rows (fun a b => a.1 ≤ b.1) 4
  == [(0, 3), (0, 6), (1, 1), (1, 4)]

end L4Factoidal.SPARQL.OrderedPrefixTests
