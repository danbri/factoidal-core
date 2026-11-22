/-
Checked full-RDFS saturation for bounded computations.
Issue: https://github.com/danbri/factoidal-core/issues/745.

Every successful result has passed a final real `fullStep` convergence
check. Fuel counts all such steps, including that check: zero fuel always
refuses. The retained triple limit is checked before each step and after
its output. This is not a peak-allocation, term-byte, join or VM-cycle bound.
The ordinary closure API and its automatic fuel remain unchanged.
-/
import L4Factoidal.RDFS.FullClosure

namespace L4Factoidal.RDFS.Checked

open L4Factoidal.RDF

structure Limits where
  maxRounds : Nat
  maxTriples : Nat
  deriving Repr, DecidableEq

inductive Error where
  | exhausted
  | tripleLimit
  deriving Repr, DecidableEq

/-- Checked closure of an already seeded graph. The final convergence
check uses one round. No incomplete graph is returned by an error. -/
def loop (maxTriples : Nat) : Nat → Graph → Except Error Graph
  | 0, _ => .error .exhausted
  | fuel + 1, g =>
    if g.length > maxTriples then .error .tripleLimit
    else
      let next := fullStep g
      if next.length > maxTriples then .error .tripleLimit
      else if next.length = g.length then .ok g
      else loop maxTriples fuel next

/-- The actual full-RDFS axiom seed followed by checked saturation.
Callers select the datatype map and finite `rdf:_n` vocabulary explicitly.
This is one entailment phase; it does not rerun RDFS after later rules. -/
def fullClosure (limits : Limits) (D cmps : List WfIri) (g : Graph) :
    Except Error Graph :=
  if g.length > limits.maxTriples then .error .tripleLimit
  else loop limits.maxTriples limits.maxRounds (addAll g (axiomaticTriples D cmps))

end L4Factoidal.RDFS.Checked
