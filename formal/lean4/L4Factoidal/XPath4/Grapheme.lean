/-
L4Factoidal.XPath4.Grapheme — extended grapheme cluster segmentation
(UAX #29, Unicode 15.1.0, rules GB3–GB999 including GB9c), for
F&O 4.0 `fn:graphemes`.
-/
import L4Factoidal.XPath4.GraphemeData

namespace L4Factoidal.XPath4.Grapheme

open GraphemeData

/-- Binary search a sorted range table; 0 when absent. -/
def lookup (t : Array (Nat × Nat × Nat)) (c : Nat) : Nat :=
  let rec go (lo hi : Nat) (fuel : Nat) : Nat :=
    match fuel with
    | 0 => 0
    | f + 1 =>
      if lo ≥ hi then 0
      else
        let mid := (lo + hi) / 2
        let (a, b, v) := t.getD mid (0, 0, 0)
        if c < a then go lo mid f
        else if c > b then go (mid + 1) hi f
        else v
  go 0 t.size 64

structure St where
  prev : Nat := 0          -- Grapheme_Cluster_Break of the previous char
  ri : Nat := 0            -- consecutive Regional_Indicators ending at prev
  pict : Bool := false     -- ExtPict Extend* ends at prev
  pictZwj : Bool := false  -- ExtPict Extend* ZWJ ends at prev
  incb : Nat := 0          -- 1: Consonant [Extend|Linker]*; 2: … with a Linker
  first : Bool := true

/-- Is there a break between the previous character (state) and `c`? -/
def breakBefore (s : St) (g : Nat) (ep : Bool) (ic : Nat) : Bool :=
  if s.first then true
  else
  let p := s.prev
  if p == 1 && g == 2 then false                          -- GB3
  else if p == 1 || p == 2 || p == 3 then true            -- GB4
  else if g == 1 || g == 2 || g == 3 then true            -- GB5
  else if p == 9 && (g == 9 || g == 10 || g == 12 || g == 13) then false -- GB6
  else if (p == 12 || p == 10) && (g == 10 || g == 11) then false        -- GB7
  else if (p == 13 || p == 11) && g == 11 then false      -- GB8
  else if g == 4 || g == 5 then false                     -- GB9
  else if g == 8 then false                               -- GB9a
  else if p == 7 then false                               -- GB9b
  else if s.incb == 2 && ic == 2 then false               -- GB9c
  else if s.pictZwj && ep then false                      -- GB11
  else if p == 6 && g == 6 && s.ri % 2 == 1 then false    -- GB12/13
  else true

def step (s : St) (g : Nat) (ep : Bool) (ic : Nat) : St :=
  { prev := g,
    ri := if g == 6 then s.ri + 1 else 0,
    pict := ep || (s.pict && g == 4),
    pictZwj := s.pict && g == 5,
    incb := if ic == 2 then 1
            else if (s.incb == 1 || s.incb == 2) && ic == 1 then 2
            else if (s.incb == 1 || s.incb == 2) && ic == 3 then s.incb
            else 0,
    first := false }

/-- The extended grapheme clusters of a string. -/
def graphemes (str : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array Char := #[]
  let mut st : St := {}
  for c in str.toList do
    let n := c.toNat
    let g := lookup gcb n
    let ep := lookup extPict n == 1
    let ic := lookup incb n
    if breakBefore st g ep ic && !cur.isEmpty then
      out := out.push (String.ofList cur.toList)
      cur := #[]
    cur := cur.push c
    st := step st g ep ic
  if !cur.isEmpty then out := out.push (String.ofList cur.toList)
  pure out.toList

#guard graphemes "abc" == ["a", "b", "c"]
#guard graphemes "\r\n" == ["\r\n"]
#guard graphemes "éx" == ["é", "x"]

end L4Factoidal.XPath4.Grapheme
