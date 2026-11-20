import L4Factoidal.Paralliverse.Life
import L4Factoidal.Paralliverse.ProgramCPU

/-!
# Paralliverse Life as an actual typed-program extension

The primitive is a complete synchronous grid generation, not a GPU shader.
Programs may compose, fan out or map the primitive over lists of grids using
the same polymorphic syntax as the Word Studio. The implementation of the
primitive uses Life.stepCPU; the reference uses Life.step.

The generic Program.runCPU_eq_eval theorem lifts their pointwise agreement
to all well-typed programs, without introducing another graph formalism.
The host remains responsible for actual physical task scheduling.
-/

namespace L4Factoidal.Paralliverse.LifeProgram

inductive Atom where
  | grid
  deriving DecidableEq, Repr

abbrev board : Shape Atom := .scalar .grid

def base : Atom → Type
  | .grid => Life.Grid

inductive Op : Shape Atom → Shape Atom → Type where
  | tick : Op board board

def reference {a b : Shape Atom} : Op a b → Shape.Value base a → Shape.Value base b
  | .tick, g => Life.step g

def implementation (workers : Nat) {a b : Shape Atom} :
    Op a b → Shape.Value base a → Shape.Value base b
  | .tick, g => Life.stepCPU workers g

/-- Each primitive implementation equals its independent sequential meaning. -/
theorem primitive_agrees (workers : Nat) {a b : Shape Atom}
    (op : Op a b) (x : Shape.Value base a) :
    implementation workers op x = reference op x := by
  cases op with
  | tick => exact Life.stepCPU_eq_step workers x

/-- Every typed Life program is equivalent to its sequential denotation. -/
theorem runCPU_eq_reference (workers : Nat) {a b : Shape Atom}
    (p : Program Op a b) :
    Program.runCPU base (implementation workers) workers p =
      Program.eval base (@reference) p :=
  Program.runCPU_eq_eval base (@reference) (implementation workers)
    (primitive_agrees workers) workers p

def tick : Program Op board board := .prim .tick
def twice : Program Op board board := .seq tick tick

/-- An example composed program computes exactly two completed generations. -/
theorem twice_eq_two_generations (workers : Nat) (g : Life.Grid) :
    Program.runCPU base (implementation workers) workers twice g =
      Life.generations 2 g := by
  simpa [twice, tick, Program.eval, reference, Life.generations] using
    congrFun (runCPU_eq_reference workers twice) g

private def oscillator : Life.Grid := Life.fromLive 5 5 [(1, 2), (2, 2), (3, 2)]
#guard (Program.runCPU base (implementation 4) 4 twice oscillator).cells == oscillator.cells
#guard (Program.runCPU base (implementation 2) 2 tick oscillator).cells ==
  (Life.step oscillator).cells

#print axioms primitive_agrees
#print axioms runCPU_eq_reference
#print axioms twice_eq_two_generations

end L4Factoidal.Paralliverse.LifeProgram
