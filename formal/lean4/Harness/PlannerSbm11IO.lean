/-
Harness/PlannerSbm11IO — OKR batch 3 KR 4.1
(https://github.com/danbri/factoidal/issues/875): a planner plan executed
against an SBM11 generation through IO. Each access of the plan is a keyed
scan of the id path (`Harness.Sbm11Query`) made when `Plan.execM` calls it,
so the PRB1 bytes are read during the run.

`idPathCalls` gives the calls of a catalog of SBM11 capabilities
(`Kinds.Sbm11.describe`). A call of capability `i` with input binding `inp`
scans the permutation of the capability's shape with the key made of the
input values (in the permutation's column order), keeps the default-graph
rows (graph id 0) and gives them as tuples of the capability's mapping.
`execM_eq_exec` (`Planner/ExecM.lean`) states the relation to `Plan.exec`
when each call answers as the pure implementation; the test set checks that
hypothesis and the result for the test generation
(`Harness/PlannerKinds.lean`).

`runQuery` is `l4planner-test sbm11-query GEN QUERY.rq [--check-pure]`: the
planner's first plan for the query, run through IO, printed as SPARQL
Results JSON. `tests/planner/sbm11_gate.sh` compares it with `l4sbm11 query`.
Exit 3: the planner does not accept the query (`Requirement.ofQuery?` gives
`none`, or the search finds no plan).
-/
import Harness.Sbm11Query
import L4Factoidal.Planner.ExecM
import L4Factoidal.Planner.FromQuery
import L4Factoidal.Planner.Kinds.Sbm11
import L4Factoidal.SPARQL.ResultsJsonFast
import L4Factoidal.SPARQL.Parser

namespace PlannerSbm11IO

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Kinds
open Harness.Sbm11Query

def subjectOfTerm (t : Term) : IO Subject :=
  match t.toSubject? with
  | some s => pure s
  | none => throw (IO.userError "a subject that is not an IRI or a blank node")

/-- The default-graph rows (graph id 0) of permutation `perm` with key
prefix `key`, as triples. -/
def scanDefault (ss : Session) (perm : Nat) (key : Array UInt64) : IO (List Triple) := do
  let acc ← IO.mkRef (#[] : Array (UInt64 × UInt64 × UInt64))
  scanAll ss perm key (fun cols n => do
    for i in [0:n] do
      if L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[3]! i == 0 then
        acc.modify (·.push (L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[0]! i,
          L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[1]! i,
          L4Factoidal.Storage.Sbm11.IdQuery.at64 cols[2]! i)))
  let ord := L4Factoidal.Storage.Sbm11.IdQuery.permOrder[perm]!
  let mut out : Array Triple := #[]
  for (a, b, c) in ← acc.get do
    let cols := #[a, b, c]
    let pick (pos : Nat) : UInt64 := cols[((List.range 3).find? (fun j => ord[j]! == pos)).getD 0]!
    let s ← subjectOfTerm (← ss.termOf (pick 0))
    let p ← match ← ss.termOf (pick 1) with
      | .iri i => pure i
      | _ => throw (IO.userError "a predicate that is not an IRI")
    let o ← ss.termOf (pick 2)
    out := out.push { s := s, p := p, o := o }
  pure out.toList

/-- One call of capability `d`: the keyed scan of its permutation. -/
def idPathCall (ss : Session) (m : L4Factoidal.Storage.Sbm11.Manifest.Manifest) (d : Described)
    (inp : InputBinding) : ExceptT String IO (List Tuple) := do
  let some sh := Sbm11.shapeOf? m d | throw s!"{d.cap.name}: no permutation shape"
  let some perm := Sbm11.permIndex? sh.perm | throw s!"{sh.perm}: no permutation index"
  let some ord := Sbm11.permOrder? sh.perm | throw s!"{sh.perm}: no column order"
  let mut key : Array UInt64 := #[]
  for c in [0:sh.keyLen] do
    let pos := ord[c]!
    let val? : Option Term := match d.partition with
      | none => inp.lookup pos
      | some p => if pos == 1 then some (.iri p) else inp.lookup (if pos == 0 then 0 else 1)
    let some val := val? | throw s!"{d.cap.name}: input for position {pos} missing"
    match ← (ss.idOf val : IO _) with
    | some x => key := key.push x
    | none => return []
  let rows ← (scanDefault ss perm key : IO _)
  return (rows.filter (keeps d.partition)).map (tupleOf d.partition)

/-- The calls of a catalog made from `ds`, in the same order. -/
def idPathCalls (ss : Session) (m : L4Factoidal.Storage.Sbm11.Manifest.Manifest) (ds : List Described) :
    Calls (ExceptT String IO) :=
  fun i inp => match ds[i]? with
    | some d => idPathCall ss m d inp
    | none => throw s!"no source {i}"

/-- Run `p` through IO: the rows, and the PRB1 bytes read during the run. -/
def runIO (ss : Session) (m : L4Factoidal.Storage.Sbm11.Manifest.Manifest) (ds : List Described)
    (cat : Catalog) (p : Plan) : IO (List Row × Nat) := do
  let before ← ss.frameBytes.get
  match ← (p.runM cat (idPathCalls ss m ds)).run with
  | .ok rows => pure (rows, (← ss.frameBytes.get) - before)
  | .error e => throw (IO.userError s!"planner IO run: {e}")

/-- The language tags of literal constants folded to lower case, as the
store keeps them (`normalizeTerm`), so a constant compares equal to the
term the id path returns. -/
def normPT : PatternTerm → PatternTerm
  | .literal l =>
    match L4Factoidal.Storage.Sbm11.normalizeTerm (.literal l) with
    | .literal l' => .literal l'
    | _ => .literal l
  | t => t

def normReq (r : Requirement) : Requirement :=
  { r with bgp := r.bgp.map (fun tp => { tp with p := normPT tp.p, o := normPT tp.o }) }

/-- Projected rows as lists of values, for a multiset comparison. -/
def canonRows (vs : List VarName) (rows : List Row) : List (List (Option Term)) :=
  rows.map (fun x => vs.map (fun v => x.binding.lookup v))

def sameMultiset (a b : List (List (Option Term))) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

/-- `l4planner-test sbm11-query GEN QUERY.rq [--check-pure]`. -/
def runQuery (gen rq : String) (checkPure : Bool) : IO UInt32 := do
  let text ← IO.FS.readFile rq
  let base := "file://" ++ (← IO.FS.realPath rq).toString
  let q ← match parseSparql text (some base) with
    | .ok q => pure q
    | .error e => do IO.eprintln s!"planner: parse error {repr e}"; return 2
  let some req0 := Requirement.ofQuery? q
    | do IO.eprintln "planner: not accepted (Requirement.ofQuery? gives none)"; return 3
  let req := normReq req0
  let ss ← openSession .merkle gen
  let m := ss.g.manifest
  -- the triple form only: no predicate probe, so no bytes are read before the run
  let ds ← match Sbm11.describe m none with
    | .ok ds => pure ds
    | .error e => throw (IO.userError s!"sbm11 describe: {e}")
  -- `search` and `execM` read the capability and the mapping of each source,
  -- not its `sem`; the generation is not materialised here, so `sem` is
  -- the graph source over the empty graph unless --check-pure is given
  let pureGraph ← if checkPure then scanDefault ss 2 #[] else pure []
  let cat : Catalog := ds.map (graphSource · pureGraph)
  let some first := (search cat req req.bgp.length).head?
    | do IO.eprintln "planner: not accepted (no plan)"; return 3
  let p := first.rewriting.toPlan req
  let (rows, bytes) ← runIO ss m ds cat p
  let names := first.rewriting.steps.map (fun a => (cat[a.src]?.map (·.cap.name)).getD "?")
  IO.eprintln s!"planner: plan={names} rows={rows.length} prb1-bytes-in-run={bytes}"
  IO.println (QueryResult.bindings req.projection (rows.map (·.binding))).toSrjFast
  if checkPure then
    let pureRows := p.run cat
    if !sameMultiset (canonRows req.projection rows) (canonRows req.projection pureRows) then
      IO.eprintln s!"planner: IO run {rows.length} rows, pure run {pureRows.length} rows: different"
      return 1
    IO.eprintln s!"planner: IO run equals the pure run ({pureRows.length} rows)"
  return 0

end PlannerSbm11IO
