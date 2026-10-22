/- Operational matching for the Core engine, without equality-producing heads.
   `no` means no match in this engine's free-symbol model, not a RIF assertion
   that different IRIs must denote different objects in every interpretation.
   Datatype values use the same decoder/identity as the built-in predicates. -/
import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF

def matchConjunction : Ans → Ans → Ans
  | .no, _ | _, .no => .no
  | .yes, .yes => .yes
  | _, _ => .unknown

private def freeSymbol (sp : String) : Bool := sp == iriSpace || sp == localSpace

mutual
def groundMatch (a b : GTerm) : Ans :=
  if a == b then .yes
  else match a, b with
  | .const _ sa, .const _ sb =>
      match literalValue? a, literalValue? b with
      | some x, some y => if x.identical y then .yes else .no
      | some _, none => if freeSymbol sb then .no else .unknown
      | none, some _ => if freeSymbol sa then .no else .unknown
      | none, none => if freeSymbol sa && freeSymbol sb then .no else .unknown
  | .list xs, .list ys => groundMatches xs ys
  | .fapp f sp xs, .fapp g sq ys =>
      if f == g && sp == sq then groundMatches xs ys else .no
  | .list _, .const _ sp =>
      if (literalValue? b).isSome || freeSymbol sp then .no else .unknown
  | .const _ sp, .list _ =>
      if (literalValue? a).isSome || freeSymbol sp then .no else .unknown
  | _, _ => .unknown

def groundMatches : List GTerm → List GTerm → Ans
  | [], [] => .yes
  | x :: xs, y :: ys => matchConjunction (groundMatch x y) (groundMatches xs ys)
  | _, _ => .no
end

/-- Preserve the unresolved status alongside an optional successful match. -/
def matchResult (value : α) : Ans → Option α × Bool
  | .yes => (some value, false)
  | .no => (none, false)
  | .unknown => (none, true)

end L4Factoidal.RIF
