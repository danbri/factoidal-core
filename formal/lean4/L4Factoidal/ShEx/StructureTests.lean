/-
ShEx/StructureTests — the ShEx 2.1 §5.7 schema requirements, pinned
in both directions (`ShEx/Structure.lean`).

Each violating schema is the shape of one shexTest
`negativeStructure` fixture; each conforming one is the nearest legal
schema, so a check that rejected everything fails half the guards.
-/
import L4Factoidal.ShEx.Structure
import L4Factoidal.ShEx.Compact

namespace L4Factoidal.ShEx.Structure

private def errs (text : String) : Option (List String) :=
  match Compact.parseShExC text with
  | .ok sch  => some (structureErrors sch)
  | .error _ => none

private def violates (text : String) : Bool :=
  match errs text with
  | some (_ :: _) => true
  | _             => false

private def conforms (text : String) : Bool := errs text == some []

private def pfx : String := "PREFIX : <http://example.org/> "

/-! ### §5.7.2 shape expression references -/

-- `1MissingRef`, and the same schema with the shape declared.
#guard violates (pfx ++ ":S1 { :p1 @:S2 }")
#guard conforms (pfx ++ ":S1 { :p1 @:S2 } :S2 { :p2 . }")
-- An unresolved label is not reported when the schema IMPORTs: the
-- import may declare it.
#guard conforms (pfx ++ "IMPORT <other> :S1 { :p1 @:S2 }")
-- `1focusRefANDSelfdot`: a label in its own shapeExprRef closure.
#guard violates (pfx ++ ":S1 @:S2 AND @:S1 AND { } :S2 { }")
-- A reference THROUGH a triple constraint is not in the closure.
#guard conforms (pfx ++ ":S1 { :p @:S1 }")

/-! ### §5.7.3 triple expression references -/

-- `includeExpressionNotFound`, `includeSimpleShape`.
#guard violates (pfx ++ ":S { &:T ; :p . }")
#guard violates (pfx ++ ":S { &:S1 ; :p1 . } :S1 { :p2 . }")
#guard conforms (pfx ++ ":S { &:T ; :p . } :U { $:T :q . }")
-- `1ShapeProductionCollision`: one label for a shape and a triple expression.
#guard violates (pfx ++ ":S1 { $:S1 :p1 . } :S2 [1]")

/-! ### §5.7.4 the negation requirement -/

-- `Cycle2Negation`, `Cycle1Negation2`, `Cycle2Extra`, `TwoNegation`.
#guard violates (pfx ++ ":S NOT { :a @:S }")
#guard violates (pfx ++ ":S { :a { :b NOT @:S } }")
#guard violates (pfx ++ ":S EXTRA :a { :a @:S }")
#guard violates (pfx ++ ":S ( (NOT @:T) AND (NOT @:U) ) :T { :a @:S } :U { :b . }")
-- `Cycle2ExtendsNegation`: an EXTENDS edge.
#guard violates (pfx ++ ":S EXTENDS @:T { } :T NOT @:S")
-- Recursion without negation, and negation without recursion, conform.
#guard conforms (pfx ++ ":S { :a @:S }")
#guard conforms (pfx ++ ":S { :a NOT @:T } :T { :b . }")
#guard conforms (pfx ++ ":S EXTRA :a { :a @:T } :T { :b . }")
-- Two negations cancel: `NOT NOT @:S` is a positive reference.
#guard conforms (pfx ++ ":S { :a NOT NOT @:S }")

end L4Factoidal.ShEx.Structure
