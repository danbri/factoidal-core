/-
Capability-aware planner, KR 2.1: capabilities.

https://github.com/danbri/factoidal/issues/801. A capability is a named
relation of fixed arity with an access pattern (required input positions
and output positions), a location tag, a cost model and an exactness
class. Its semantics is a pair: a declared extension (a finite list of
tuples) and an implementation (a function from input bindings to a finite
list of tuples). The implementation is a pure function here; an IO
wrapper is later work.
-/
import L4Factoidal.Planner.Requirement

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-- Whether a capability's answers are exact. An LLM answer is
`approximate`; results that depend on one carry a marker. -/
inductive Exactness where
  | exact
  | approximate
  deriving DecidableEq, Repr

def Exactness.isApprox : Exactness → Bool
  | .exact       => false
  | .approximate => true

/-- An abstract cost model: cost per call, cost per returned row,
optional quotas, and an optional statistic. Units are left to the source
kind. `callQuota` bounds the calls of the source in one run; `rowQuota`
bounds the tuples that the source returns in one run (the driver
`Planner.Exec` enforces both). `rowsPerCall` is an estimate of the tuples
one call returns (a statistic of the source, as in a service
description); without it the estimate of `Planner.Search` uses its
`fanout`. -/
structure CostModel where
  perCall : Nat
  perRow : Nat
  callQuota : Option Nat := none
  rowQuota : Option Nat := none
  rowsPerCall : Option Nat := none
  deriving DecidableEq, Repr

/-- A tuple of the capability's relation, one term per position. -/
abbrev Tuple := List Term

/-- An input binding: values for some argument positions. -/
abbrev InputBinding := List (Nat × Term)

structure Capability where
  name : String
  arity : Nat
  /-- Positions that are required inputs. -/
  inputs : List Nat
  /-- Where the work runs (a host, an endpoint, a process). -/
  location : String
  cost : CostModel
  exactness : Exactness
  deriving DecidableEq, Repr

/-- The output positions: every position that is not a required input. -/
def Capability.outputs (c : Capability) : List Nat :=
  (List.range c.arity).filter (fun i => !c.inputs.contains i)

/-- The tuple agrees with every given input value. -/
def tupleMatchesInput (inp : InputBinding) (tup : Tuple) : Bool :=
  inp.all (fun p => tup[p.1]? == some p.2)

/-- The semantics of a capability: its declared extension and its
implementation. -/
structure CapSemantics where
  ext : List Tuple
  impl : InputBinding → List Tuple

/-- Sound: every tuple the implementation returns is in the extension. -/
def CapSemantics.Sound (s : CapSemantics) : Prop :=
  ∀ inp tup, tup ∈ s.impl inp → tup ∈ s.ext

/-- Complete for an input: the implementation returns every extension
tuple that matches the input. -/
def CapSemantics.CompleteFor (s : CapSemantics) (inp : InputBinding) : Prop :=
  ∀ tup ∈ s.ext, tupleMatchesInput inp tup = true → tup ∈ s.impl inp

end L4Factoidal.Planner
