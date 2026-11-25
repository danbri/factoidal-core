/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/

/-!
Typed, static programs for pure total operations. A language author supplies the scalar
types, primitive symbols and their interpretations. The program constructors contain
no Lean function literals. Each extension is responsible for its own symbol encoding
and supported lowering. The generic language has no dependency on a particular workload.
-/

namespace L4Factoidal.Paralliverse

/-- A program's input or output, built from domain-specific scalar names. -/
inductive Shape (Atom : Type) where
  | scalar (name : Atom)
  | pair (left right : Shape Atom)
  | list (element : Shape Atom)
  deriving DecidableEq, Repr

/-- Interpret the scalar names and the two structural types. -/
def Shape.Value {Atom : Type} (base : Atom → Type) : Shape Atom → Type
  | .scalar a => base a
  | .pair a b => Value base a × Value base b
  | .list a => List (Value base a)

/-- A stage symbol is indexed by its permitted input and output. -/
abbrev Signature (Atom : Type) := Shape Atom → Shape Atom → Type

/-- Primitive semantics are supplied to the interpreter, separately from the program. -/
abbrev PrimitiveEval {Atom : Type} (base : Atom → Type) (sig : Signature Atom) :=
  ∀ {a b}, sig a b → Shape.Value base a → Shape.Value base b

/-- A finite expression built from primitive symbols and structural combinators. -/
inductive Program {Atom : Type} (sig : Signature Atom) : Shape Atom → Shape Atom → Type where
  | identity : Program sig a a
  | prim (op : sig a b) : Program sig a b
  | seq (first : Program sig a b) (next : Program sig b c) : Program sig a c
  | prod (left : Program sig a b) (right : Program sig c d) :
      Program sig (.pair a c) (.pair b d)
  | fanout (left : Program sig a b) (right : Program sig a c) :
      Program sig a (.pair b c)
  | map (body : Program sig a b) : Program sig (.list a) (.list b)

namespace Program

variable {Atom : Type} {sig : Signature Atom} {a b c : Shape Atom}

/-- Sequential denotation. A list map preserves order, empties and multiplicity. -/
def eval (base : Atom → Type) (ops : PrimitiveEval base sig) {a b : Shape Atom} :
    Program sig a b → Shape.Value base a → Shape.Value base b
  | .identity, x => x
  | .prim op, x => ops op x
  | .seq f g, x => eval base ops g (eval base ops f x)
  | .prod f g, x => (eval base ops f x.1, eval base ops g x.2)
  | .fanout f g, x => (eval base ops f x, eval base ops g x)
  | .map f, xs => xs.map (eval base ops f)

/-- Compose two stages, fusing two adjacent maps into a single traversal. -/
private def fusePair (f : Program sig a b) (g : Program sig b c) : Program sig a c :=
  match f, g with
  | .map p, .map q => .map (.seq p q)
  | p, q => .seq p q

/-- A bottom-up map-fusion pass. It revisits neither the input values nor a generated node. -/
def fuseMaps {a b : Shape Atom} : Program sig a b → Program sig a b
  | .identity => .identity
  | .prim op => .prim op
  | .seq f g => fusePair (fuseMaps f) (fuseMaps g)
  | .prod f g => .prod (fuseMaps f) (fuseMaps g)
  | .fanout f g => .fanout (fuseMaps f) (fuseMaps g)
  | .map f => .map (fuseMaps f)

/-- Kind: rewrite correctness.
Says: replacing two adjacent pure maps by a map of the composed element computations
preserves every returned element and its position.
Does not say: that fusing effectful traversals preserves their first error. -/
private theorem eval_fusePair (base : Atom → Type) (ops : PrimitiveEval base sig)
    (f : Program sig a b) (g : Program sig b c) :
    eval base ops (fusePair f g) = eval base ops (.seq f g) := by
  funext x
  cases f <;> cases g <;> first | rfl | exact List.map_map.symm

/-- Kind: whole-program preservation.
Says: the recursive map-fusion pass preserves the sequential meaning of every
well-typed program for every pure interpretation of its primitives.
Does not say: that this pass produces a normal form for all program equations,
reduces execution time, or preserves the error order of an effectful interpreter. -/
theorem eval_fuseMaps (base : Atom → Type) (ops : PrimitiveEval base sig)
    (p : Program sig a b) : eval base ops (fuseMaps p) = eval base ops p := by
  induction p with
  | identity => rfl
  | prim => rfl
  | seq f g hf hg =>
    funext x
    simp only [fuseMaps, eval_fusePair, eval, hf, hg]
  | prod f g hf hg =>
    funext x
    simp only [fuseMaps, eval, hf, hg]
    rfl
  | fanout f g hf hg =>
    funext x
    simp only [fuseMaps, eval, hf, hg]
    rfl
  | map f hf =>
    funext x
    simp only [fuseMaps, eval, hf]
    rfl

#print axioms eval_fuseMaps

end Program

end L4Factoidal.Paralliverse
