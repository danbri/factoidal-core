/-
Checked SPARQL-RL evaluation, reusing the actual general-rule rounds.
Issue: https://github.com/danbri/factoidal-core/issues/745.

The public result includes the base graph and all RDF projections of the
generalized evaluation graph, not only the newly inferred triples.
Every general layer reserves one round for a naive full-rule check: success
requires that this check produces no new triple. An exhausted computation
cannot become a normal ASK false. `maxTriples` caps retained evaluation
graphs; it does not cap intermediate bindings, allocation or VM cycles.
Policy admission (including deterministic functions) belongs to callers.
-/
import L4Factoidal.SPARQLRL.Eval

namespace L4Factoidal.SPARQLRL.Checked

open L4Factoidal.RDF
open L4Factoidal.SPARQL

structure Limits where
  maxRoundsPerLayer : Nat
  maxTriples : Nat
  deriving Repr, DecidableEq

inductive Error where
  | infer (reason : InferError)
  | exhausted
  | tripleLimit
  deriving Repr, DecidableEq

/-- Internal bounded progress, exactly the old loop at the supplied fuel
when no retained-graph limit is reached. A successful progress result is
not a saturation claim; only `generalLoop` below checks saturation. -/
def progress (maxTriples : Nat) (cx : Ctx) (pfx : String) (rules : List Rule) :
    Nat → Bool → IGraph → IGraph → Nat → Except Error (IGraph × Nat)
  | 0, _, ge, _, ctr =>
      if ge.size > maxTriples then .error .tripleLimit else .ok (ge, ctr)
  | fuel + 1, first, ge, delta, ctr =>
      if ge.size > maxTriples then .error .tripleLimit
      else
        let (delta', ctr') := generalRound cx pfx rules first ge delta ctr
        if delta'.size == 0 then .ok (ge, ctr')
        else
          let next := ge.insertAll delta'.all
          if next.size > maxTriples then .error .tripleLimit
          else progress maxTriples cx pfx rules fuel false next delta' ctr'

/-- Actual full-rule saturation, stated without trusting the semi-naive
algorithm's early stopping condition. The counter is part of the state. -/
def Saturated (cx : Ctx) (pfx : String) (rules : List Rule) (state : IGraph × Nat) : Prop :=
  (generalRound cx pfx rules true state.1 {} state.2).1.size = 0

/-- A bounded semi-naive computation followed by a full-rule saturation
check. The total is at most `maxRoundsPerLayer` rounds. Zero refuses.
The last check is observational: it does not replace the accepted state. -/
def generalLoop (limits : Limits) (cx : Ctx) (pfx : String) (rules : List Rule)
    (ge : IGraph) (ctr : Nat) : Except Error (IGraph × Nat) :=
  match limits.maxRoundsPerLayer with
  | 0 => .error .exhausted
  | fuel + 1 => do
      let state ← progress limits.maxTriples cx pfx rules fuel true ge {} ctr
      if (generalRound cx pfx rules true state.1 {} state.2).1.size = 0
      then .ok state else .error .exhausted

/-- One run-once rule, with a retained graph cap before and after. -/
def onceRule (maxTriples : Nat) (cx : Ctx) (pfx : String) (rules : List Rule)
    (state : IGraph × Nat) (index : Nat) : Except Error (IGraph × Nat) :=
  let (ge, ctr) := state
  if ge.size > maxTriples then .error .tripleLimit
  else
    let r := rules.getD index default
    let (ts, ctr') := instHead r pfx ctr (evalBody cx r ge (fun _ => ⟨ge, none⟩))
    let next := ge.insertAll ts
    if next.size > maxTriples then .error .tripleLimit else .ok (next, ctr')

/-- Run-once rules retain their existing sequence and counter semantics.
There are exactly as many calls as the selected layer contains indices. -/
def onceRules (maxTriples : Nat) (cx : Ctx) (pfx : String) (rules : List Rule)
    (indices : List Nat) (state : IGraph × Nat) : Except Error (IGraph × Nat) :=
  indices.foldlM (onceRule maxTriples cx pfx rules) state

/-- One checked stratification layer in its specified run-once/general order. -/
def evalLayer (limits : Limits) (cx : Ctx) (pfx : String) (rules : List Rule)
    (state : IGraph × Nat) (layer : Layer) : Except Error (IGraph × Nat) := do
  let (ge, ctr) ← onceRules limits.maxTriples cx pfx rules layer.once state
  let gen := layer.general.map (fun i => rules.getD i default)
  if gen.isEmpty then .ok (ge, ctr) else generalLoop limits cx pfx gen ge ctr

/-- Layer order and run-once/general classification are the existing
stratifier's. Each general layer has its own explicit round budget. -/
def evalLayers (limits : Limits) (cx : Ctx) (pfx : String) (rules : List Rule)
    (layers : List Layer) (state : IGraph × Nat) : Except Error (IGraph × Nat) :=
  layers.foldlM (evalLayer limits cx pfx rules) state

/-- Checked full generalized evaluation graph, retaining the ordinary
validation and initial data-block blank-node scope. -/
def evalIGraph (limits : Limits) (rs : RuleSet) (base : Graph) (env : EvalEnv := {}) :
    Except Error IGraph :=
  if !rs.imports.isEmpty then .error (.infer (.imports rs.imports))
  else if !rs.wellFormed then .error (.infer .notWellFormed)
  else if base.length > limits.maxTriples then .error .tripleLimit
  else match stratify rs.rules with
    | none => .error (.infer .notStratifiable)
    | some layers => do
      let g0 := IGraph.ofGraph base
      let pfx := freshPrefix (base.flatMap fun t =>
        (match t.s with | .bnode b => [b] | _ => []) ++ termBnodeIds t.o)
      let (d, ctr) := dataTriples rs pfx 0
      let ge := g0.insertAll d
      if ge.size > limits.maxTriples then .error .tripleLimit
      else
        let (result, _) ← evalLayers limits { env, g0 } pfx rs.rules layers (ge, ctr)
        .ok result

/-- The RDF projection of the full checked evaluation graph, base included.
Generalized triples stay available to rules but are not RDF query input. -/
def evalGraph (limits : Limits) (rs : RuleSet) (base : Graph) (env : EvalEnv := {}) :
    Except Error Graph := do
  let ge ← evalIGraph limits rs base env
  return ge.all.toList.filterMap t3ToTriple?

end L4Factoidal.SPARQLRL.Checked
