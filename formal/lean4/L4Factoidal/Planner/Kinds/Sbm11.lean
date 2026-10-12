/-
Capability-aware planner, KR 2.3: an SBM11 generation as capabilities.

https://github.com/danbri/factoidal/issues/801. Description document: the
generation's manifest (`manifest.sbm11`, `Storage/Sbm11/Manifest.lean`),
which lists one PRM1/PRB1 pair per sorted quad permutation, and, when a
probe has read it, the list of predicates of the generation (the distinct
first column of the PSO permutation).

Access shapes. A scan of permutation `XYZ` with a key of length `k`
returns the rows whose first `k` columns have the given values. So the
required inputs of the shape are the triple positions of the first `k`
columns, for `k = 0..3`. The four permutations PSO, POS, SPO and OSP give
all eight subsets of `{S, P, O}` (`permShapes`). One capability is made
for each subset, from the first permutation in manifest order that gives
it:

* triple form (arity 3, template `(0, 1, 2)`): every subset;
* predicate form, one per predicate `p` of the probe (arity 2, template
  `(0, p, 1)`): the subsets that contain `P`, with `P` taken out: `{}`
  (PSO, key `p`), `{S}` (PSO, key `p s`), `{O}` (POS, key `p o`), `{S, O}`
  (PSO, key `p s o`).

Cost model (`costOf`): `perCall` is the manifest's quad count for a scan
with an empty key (every block is read); for a keyed scan, 20 (a binary
search of the block metadata) plus the quad count halved for each key
column (a proxy: there are no per-column statistics yet); `perRow` is 1.
Exact.

Location: `sbm11:<layout>`; the harness opens the generation directory.
The implementation in tests is `graphSource` over the rows decoded
through the id query path, with a differential test against that path
(`Harness/PlannerKinds.lean`): there is no end-to-end theorem between
the id path and the reference evaluator
(https://github.com/danbri/factoidal/issues/776). Named graphs are not
modelled: a generation whose quads are all in the default graph is the
supported case.
-/
import L4Factoidal.Planner.Kinds.Common
import L4Factoidal.Storage.Sbm11.Manifest

namespace L4Factoidal.Planner.Kinds.Sbm11

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Kinds
open L4Factoidal.Storage.Sbm11.Manifest (Manifest sbm11Layout)

/-- The triple positions of the first three columns of a permutation
(0 = S, 1 = P, 2 = O); the same order as `IdQuery.permOrder`. -/
def permOrder? : String → Option (List Nat)
  | "pso" => some [1, 0, 2]
  | "pos" => some [1, 2, 0]
  | "spo" => some [0, 1, 2]
  | "osp" => some [2, 0, 1]
  | _     => none

/-- The permutation index of the id query path (`IdQuery.permNames`). -/
def permIndex? : String → Option Nat
  | "pso" => some 0
  | "pos" => some 1
  | "spo" => some 2
  | "osp" => some 3
  | _     => none

/-- The permutations a manifest lists, in manifest order: each role
`PRM1-XYZ` that has a `PRB1-XYZ`. -/
def manifestPerms (m : Manifest) : List String :=
  let roles := m.artifacts.map (·.role)
  roles.filterMap (fun r =>
    if r.startsWith "PRM1-" then
      let p := (r.drop 5).toString
      if roles.contains ("PRB1-" ++ p) then some p.toLower else none
    else none)

/-- One access shape: the permutation, the key length and the required
triple positions (sorted). -/
structure Shape where
  perm : String
  keyLen : Nat
  inputs : List Nat
  deriving Repr, DecidableEq

/-- Every (permutation, key length) of the listed permutations; the first
shape for each input set is kept. -/
def permShapes (perms : List String) : List Shape :=
  dedupBy (·.inputs) (perms.flatMap (fun p =>
    match permOrder? p with
    | none => []
    | some ord => (List.range 4).map (fun k => { perm := p, keyLen := k, inputs := sortPositions (ord.take k) })))

/-- The cost of one call: a scan with an empty key reads every row; a
keyed scan pays a seek (20, the binary search of the block metadata)
and the rows it reads, estimated as the quad count halved for each key
column. The halving is a proxy, not a statistic: the planner has no
per-column distinct counts yet. -/
def costOf (m : Manifest) (sh : Shape) : CostModel :=
  { perCall := if sh.keyLen == 0 then max 1 m.quads else 20 + max 1 (m.quads / 2 ^ sh.keyLen),
    perRow := 1 }

/-- Positions of the predicate form: S is tuple position 0, O is 1. -/
def predInputs (inputs : List Nat) : List Nat :=
  sortPositions (inputs.filterMap (fun i => if i == 0 then some 0 else if i == 2 then some 1 else none))

def shapeName (sh : Shape) : String := s!"sbm11:{sh.perm}/{sh.keyLen}"

/-- The capabilities of a generation. `preds` is the predicate probe;
`none` gives the triple form only. -/
def describe (m : Manifest) (preds : Option (List WfIri) := none) : Except String (List Described) :=
  if m.layout != sbm11Layout then .error s!"manifest layout {m.layout}, want {sbm11Layout}" else
  let perms := manifestPerms m
  if perms.isEmpty then .error "the manifest lists no permutation" else
  let shapes := permShapes perms
  let loc := s!"sbm11:{m.layout}"
  let triple := shapes.map (fun sh =>
    { kind := "sbm11", partition := none, mapping := graphMapping none,
      cap := { name := shapeName sh, arity := 3, inputs := sh.inputs, location := loc,
               cost := costOf m sh, exactness := .exact } : Described })
  let predShapes := shapes.filter (fun sh => sh.inputs.contains 1)
  let byPred := (preds.getD []).flatMap (fun p => predShapes.map (fun sh =>
    { kind := "sbm11", partition := some p, mapping := graphMapping (some p),
      cap := { name := s!"{shapeName sh}[{localName p}]", arity := 2, inputs := predInputs sh.inputs,
               location := loc, cost := costOf m sh, exactness := .exact } :
      Described }))
  .ok (triple ++ byPred)

/-- The shape a capability came from (by name), for the differential
test against the id path. -/
def shapeOf? (m : Manifest) (d : Described) : Option Shape :=
  (permShapes (manifestPerms m)).find? (fun sh =>
    d.cap.name == shapeName sh || d.cap.name.startsWith (shapeName sh ++ "["))

end L4Factoidal.Planner.Kinds.Sbm11
