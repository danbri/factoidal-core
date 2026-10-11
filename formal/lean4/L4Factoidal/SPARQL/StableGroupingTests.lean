import L4Factoidal.SPARQL.StableGrouping

namespace L4Factoidal.SPARQL.StableGroupingTests

open StableGrouping

private def rows : List (Nat × String) :=
  [(2, "first"), (1, "second"), (2, "third"), (3, "fourth"), (1, "fifth")]
private def expected : List (Group Nat String) :=
  [⟨2, ["first", "third"]⟩, ⟨1, ["second", "fifth"]⟩, ⟨3, ["fourth"]⟩]
private def encode (n : Nat) : Option Nat := if n < 10 then some n else none

#guard reference (· == ·) Prod.fst Prod.snd rows == expected
#guard fast (· == ·) encode Prod.fst Prod.snd rows == expected
#guard fast (· == ·) encode Prod.fst Prod.snd ([] : List (Nat × String)) == []
#guard fast (· == ·) encode Prod.fst Prod.snd [(2, "one")] == [⟨2, ["one"]⟩]
#guard fast (· == ·) encode Prod.fst Prod.snd [(2, "one"), (2, "one")] == [⟨2, ["one", "one"]⟩]
#guard fast (· == ·) encode Prod.fst Prod.snd
  [(2, "before"), (20, "fallback"), (2, "after"), (20, "last")] ==
    [⟨2, ["before", "after"]⟩, ⟨20, ["fallback", "last"]⟩]
#guard fast (· == ·) encode Prod.fst Prod.snd
  [(20, "fallback"), (2, "after"), (20, "last")] ==
    [⟨20, ["fallback", "last"]⟩, ⟨2, ["after"]⟩]

-- The fallback must retain even a non-transitive relation that updates
-- multiple existing groups. No equality assumption is needed there.
private def near (a b : Nat) : Bool := a + 1 == b || b + 1 == a || a == b
private def awkward : List (Nat × String) := [(0, "a"), (2, "b"), (1, "c")]
#guard reference near Prod.fst Prod.snd awkward == [⟨0, ["a", "c"]⟩, ⟨2, ["b", "c"]⟩]
#guard fast near (fun _ => (none : Option Nat)) Prod.fst Prod.snd awkward ==
  reference near Prod.fst Prod.snd awkward

#guard fast (· == ·) (some : Nat → Option Nat) Prod.fst Prod.snd rows == expected
#guard fast (· == ·) (some : Nat → Option Nat) Prod.fst Prod.snd
  (List.range 100 |>.map fun n => (n % 7, toString n)) ==
  reference (· == ·) Prod.fst Prod.snd (List.range 100 |>.map fun n => (n % 7, toString n))

end L4Factoidal.SPARQL.StableGroupingTests
