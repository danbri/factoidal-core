/-
Capability-aware planner, KR 2.3: an in-memory dataset as capabilities.

https://github.com/danbri/factoidal/issues/801. Description document: the
dataset itself (the reference evaluator's `Graph`, the default graph of a
`Dataset`); `describe` reads its size and its distinct predicates (a
statistics pass over data that is already held, so it is not a costed
probe).

Capabilities: the free scan and the bound-position lookups, in both
mapping forms of `Kinds/Common.lean`: the triple form for each of the
eight subsets of `{S, P, O}`, and for each predicate `p` the predicate form
for each subset of `{S, O}`. Cost model: `perCall` is the triple count for
a call with no input (a scan) and 1 for a lookup; `perRow` is 1. Exact.
Location `memory`.

The implementation is `graphSource` over the same graph:
`graphSource_triples`, `graphSource_sound` and `graphSource_complete`
hold for it, and `Plan.exec` over these sources reads the same triples
that the reference evaluator reads.
-/
import L4Factoidal.Planner.Kinds.Common

namespace L4Factoidal.Planner.Kinds.Memory

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Kinds

/-- The subsets of `{S, P, O}` and of `{S, O}` (tuple positions of the
predicate form). -/
def subsets3 : List (List Nat) := [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]
def subsets2 : List (List Nat) := [[], [0], [1], [0, 1]]

/-- The distinct predicates of a graph, in first-occurrence order. -/
def predicates (g : Graph) : List WfIri := (g.map (·.p)).eraseDups

def posName : Nat → String
  | 0 => "s" | 1 => "p" | _ => "o"

def shapeName (inputs : List Nat) : String :=
  "memory:" ++ (if inputs.isEmpty then "scan" else String.join (inputs.map posName))

def cost (size : Nat) (inputs : List Nat) : CostModel :=
  { perCall := if inputs.isEmpty then max 1 size else 1, perRow := 1 }

def describe (g : Graph) : Except String (List Described) :=
  let triple := subsets3.map (fun ins =>
    { kind := "memory", partition := none, mapping := graphMapping none,
      cap := { name := shapeName ins, arity := 3, inputs := ins, location := "memory",
               cost := cost g.length ins, exactness := .exact } : Described })
  let byPred := (predicates g).flatMap (fun p =>
    let n := (g.filter (fun t => t.p == p)).length
    subsets2.map (fun ins =>
      { kind := "memory", partition := some p, mapping := graphMapping (some p),
        cap := { name := s!"{shapeName (ins.map (fun i => if i == 0 then 0 else 2))}[{localName p}]",
                 arity := 2, inputs := ins, location := "memory", cost := cost n ins,
                 exactness := .exact } : Described }))
  .ok (triple ++ byPred)

end L4Factoidal.Planner.Kinds.Memory
