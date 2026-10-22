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

/- Executable matcher: list width is handled by a tail accumulator. -/
mutual
def groundMatchTR (a b : GTerm) : Ans :=
  if a == b then .yes
  else match a, b with
  | .const _ sa, .const _ sb =>
      match literalValue? a, literalValue? b with
      | some x, some y => if x.identical y then .yes else .no
      | some _, none => if freeSymbol sb then .no else .unknown
      | none, some _ => if freeSymbol sa then .no else .unknown
      | none, none => if freeSymbol sa && freeSymbol sb then .no else .unknown
  | .list xs, .list ys => groundMatchesAcc xs ys .yes
  | .fapp f sp xs, .fapp g sq ys =>
      if f == g && sp == sq then groundMatchesAcc xs ys .yes else .no
  | .list _, .const _ sp =>
      if (literalValue? b).isSome || freeSymbol sp then .no else .unknown
  | .const _ sp, .list _ =>
      if (literalValue? a).isSome || freeSymbol sp then .no else .unknown
  | _, _ => .unknown


def groundMatchesAcc : List GTerm → List GTerm → Ans → Ans
  | [], [], acc => acc
  | x :: xs, y :: ys, acc =>
      groundMatchesAcc xs ys (matchConjunction acc (groundMatchTR x y))
  | _, _, _ => .no
end

private theorem matchConjunction_yes_left (a : Ans) : matchConjunction .yes a = a := by
  cases a <;> rfl
private theorem matchConjunction_yes_right (a : Ans) : matchConjunction a .yes = a := by
  cases a <;> rfl
private theorem matchConjunction_no_right (a : Ans) : matchConjunction a .no = .no := by
  cases a <;> rfl
private theorem matchConjunction_assoc (a b c : Ans) :
    matchConjunction (matchConjunction a b) c = matchConjunction a (matchConjunction b c) := by
  cases a <;> cases b <;> cases c <;> rfl

private theorem groundMatchTR_correct :
    (∀ a b, groundMatchTR a b = groundMatch a b) ∧
    (∀ xs ys acc, groundMatchesAcc xs ys acc = matchConjunction acc (groundMatches xs ys)) := by
  apply groundMatch.mutual_induct
    (motive_1 := fun a b => groundMatchTR a b = groundMatch a b)
    (motive_2 := fun xs ys => ∀ acc,
      groundMatchesAcc xs ys acc = matchConjunction acc (groundMatches xs ys))
  all_goals intros
  all_goals simp_all [groundMatchTR, groundMatchesAcc, groundMatch, groundMatches,
    matchConjunction_yes_left, matchConjunction_yes_right, matchConjunction_no_right,
    matchConjunction_assoc]
  case case1 t b h => cases b <;> simp [groundMatchTR, groundMatch]
  case case12 => grind

def groundMatchesTR (xs ys : List GTerm) : Ans := groundMatchesAcc xs ys .yes

@[csimp] theorem groundMatch_eq_groundMatchTR : @groundMatch = @groundMatchTR := by
  funext a b
  exact (groundMatchTR_correct.1 a b).symm

@[csimp] theorem groundMatches_eq_groundMatchesTR : @groundMatches = @groundMatchesTR := by
  funext xs ys
  simp [groundMatchesTR, groundMatchTR_correct.2, matchConjunction_yes_left]


/-- Preserve the unresolved status alongside an optional successful match. -/
def matchResult (value : α) : Ans → Option α × Bool
  | .yes => (some value, false)
  | .no => (none, false)
  | .unknown => (none, true)

end L4Factoidal.RIF
