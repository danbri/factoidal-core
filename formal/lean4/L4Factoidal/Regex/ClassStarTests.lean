/- The loop for `.star` over one character class (`cmatchE`) against the general
   case, which `.cat .eps` forces. A finite differential corpus, not a proof.
   The last check runs a capture over a long text, the shape that overflowed
   the stack in a phone browser. -/
import L4Factoidal.Regex.XPath

namespace L4Factoidal.Regex.ClassStarTests

private def classes : List (List (Nat × Nat)) :=
  [[(97, 97)], [(97, 98)], [(98, 99)], [(0, 0x10FFFF)], []]

private def viaLoop (greedy : Bool) (rs : List (Nat × Nat)) : CRe :=
  .star greedy (.leaf (.ranges rs))

private def viaGeneral (greedy : Bool) (rs : List (Nat × Nat)) : CRe :=
  .star greedy (.cat .eps (.leaf (.ranges rs)))

private def tails : List CRe :=
  [.eps, .leaf (.ranges [(98, 98)]), .leaf (.ranges [(99, 99)]), .anchorEnd,
   .cat (viaGeneral true [(98, 99)]) (.leaf (.ranges [(99, 99)]))]

private def grow (ws : List (List Nat)) : List (List Nat) :=
  [] :: ws.flatMap fun w => [97 :: w, 98 :: w, 99 :: w]

/-- Words over a, b and c, up to five letters. -/
private def words : List (List Nat) := grow (grow (grow (grow (grow [[]]))))

/-- `some`, and an accept that takes odd end positions only, which forces backtracking. -/
private def accepts : List (COut → Option COut) :=
  [some, fun o => if o.endPos % 2 == 1 then some o else none]

private def outcome (r : Option COut) : Option (List Nat × Nat × Nat) :=
  r.map fun o => (o.rest, o.endPos, o.caps.length)

private def agree (greedy : Bool) (rs : List (Nat × Nat)) (tail : CRe) (w : List Nat)
    (accept : COut → Option COut) : Bool :=
  let run (star : CRe) := outcome (cmatch w false 200 (.cat star tail) w 0 accept)
  run (viaLoop greedy rs) == run (viaGeneral greedy rs)

#guard [true, false].all fun greedy => classes.all fun rs => tails.all fun tail =>
  words.all fun w => accepts.all fun accept => agree greedy rs tail w accept

private def longRule : String :=
  String.ofList (List.replicate 20000 'a') ++ " $this ex:field ?value " ++ String.ofList (List.replicate 20000 'b')

#guard regexReplace longRule "^.*?\\$this\\s+(\\S+)\\s+\\?value.*$" "$1" "s" == "ex:field"

end L4Factoidal.Regex.ClassStarTests
