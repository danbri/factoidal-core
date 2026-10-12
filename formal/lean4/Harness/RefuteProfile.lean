/-
Harness.RefuteProfile — where the OWL DL tableau refuter spends its work.

    l4refute-profile FILE.nt [--budget N] [--trace] [--check]

Reads one N-Triples or N-Quads file, takes the OWL 2 RL closure of its
default graph (`OWL.RL.closureFix`, as `l4factoidal owl-consistent` does),
and runs the refuter's search (`OWL.Refute.search`) with counters and
timers on every phase. It prints one block of `key value` lines: the
closure hand-off, the TBox read, the initial state, the number of
expansion steps (calls of `search`), saturation passes, union and merge
branch points and branches, the state size (nodes, labels, edges), and
the time and call count of each phase of a step.

This file holds no OWL logic of its own. It calls the library's phase
functions in the order `OWL.Refute.search` calls them, with the same
threaded budget, so that each phase can be timed: `--check` also runs
`OWL.Refute.tableauConsistent` on the same closure and exits 1 when the
two verdicts differ. Each timed value is consumed by a counter before the
second clock read (skills/measuring-inference, sections 9 and 11), and
the parts are printed beside the step total they must sum to.

`--trace` prints one line per expansion step: depth, nodes, labels, the
largest label set, expansion edges, and the step's time.

Record: docs/designissues/2026-10-10-owl-real-ontologies.md § 9
(https://github.com/danbri/factoidal/issues/760, OKR batch 1 KR 3.3).
-/
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.RLClosure
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.Syntax.NQuadsFast

namespace RefuteProfile

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.OWL
open L4Factoidal.OWL.Refute

/-- Counters: call count and nanoseconds per phase, and the totals. -/
structure Prof where
  calls : Std.HashMap String Nat := {}
  nanos : Std.HashMap String Nat := {}
  count : Std.HashMap String Nat := {}

def bump (r : IO.Ref Prof) (key : String) (n : Nat) : IO Unit :=
  r.modify (fun p => { p with count := p.count.insert key (p.count.getD key 0 + n) })

def setMax (r : IO.Ref Prof) (key : String) (n : Nat) : IO Unit :=
  r.modify (fun p => { p with count := p.count.insert key (max (p.count.getD key 0) n) })

/-- Run `f`, charge its time to `key`, and consume `obs` of its value
    before the second clock read, so the value is computed between the
    two reads. Not inlined, so the caller cannot move work into or out
    of the timed region. -/
@[noinline] def timed {α : Type} (r : IO.Ref Prof) (sink : IO.Ref Nat) (key : String)
    (obs : α → Nat) (f : Unit → α) : IO α := do
  let t0 ← IO.monoNanosNow
  let v := f ()
  sink.modify (· + obs v)
  let t1 ← IO.monoNanosNow
  r.modify (fun p => { p with
    calls := p.calls.insert key (p.calls.getD key 0 + 1),
    nanos := p.nanos.insert key (p.nanos.getD key 0 + (t1 - t0)) })
  pure v

def obsSt (p : RState × Bool) : Nat := p.1.nodes.size + (if p.2 then 1 else 0)
def obsB (b : Bool) : Nat := if b then 1 else 0

def labelCount (st : RState) : Nat := st.nodes.foldl (fun a n => a + n.labels.length) 0
def maxLabels (st : RState) : Nat := st.nodes.foldl (fun a n => max a n.labels.length) 0

/-- The library's `clashNodes`, its parts timed apart. -/
def clashNodesP (r : IO.Ref Prof) (sink : IO.Ref Nat) (g : Graph) (st : RState) : IO Bool := do
  if ← timed r sink "clash.inverseFunctional" obsB (fun _ => inverseFunctionalClash g st) then
    return true
  let leaders ← timed r sink "clash.groupLeaders" (·.length) (fun _ => groupLeaders st)
  for n in leaders do
    let ls := labelsOf st n.id
    bump r "clash.labelVisits" ls.length
    if ← timed r sink "clash.labels" obsB (fun _ => ls.any (clashForLabel g st n.id ls)) then
      return true
    if ← timed r sink "clash.datatypeRange" obsB (fun _ => datatypeRangeClash g st n.id ls) then
      return true
    if ← timed r sink "clash.datatypeCard" obsB
        (fun _ => datatypeCardinalityClash g st n.id ls) then
      return true
    if ← timed r sink "clash.counting" obsB (fun _ => countingClash st ls) then
      return true
  pure false

/-- The library's `onePass`, its parts timed apart. -/
def onePassP (r : IO.Ref Prof) (sink : IO.Ref Nat) (tb : List (ClassExpr × ClassExpr))
    (g : Graph) (st : RState) : IO (RState × Bool) := do
  let ix ← timed r sink "pass.tboxIndex" (fun (ix : TBoxIndex) => ix.top.length)
    (fun _ => TBoxIndex.build tb)
  let (st0, ch0) ← timed r sink "pass.injectFunctional" obsSt (fun _ => injectFunctional st)
  let (st1, chG) ← timed r sink "pass.injectGlobal" obsSt (fun _ => injectGlobalAxioms ix.top st0)
  let mut acc : RState × Bool := (st1, ch0 || chG)
  let leaders ← timed r sink "pass.groupLeaders" (·.length) (fun _ => groupLeaders st1)
  for n in leaders do
    bump r "pass.nodeVisits" 1
    let ls ← timed r sink "pass.labelsOf" (·.length) (fun _ => labelsOf acc.1 n.id)
    let mut a2 := acc
    for l in ls do
      bump r "pass.labelVisits" 1
      let kind := match l with
        | .allOf _ _ => "allOf" | .someOf _ _ => "someOf" | .intersection _ => "intersection"
        | .minCard _ _ | .minQualCard _ _ _ => "min" | .hasValue _ _ => "hasValue"
        | _ => "other"
      let (s1, c1) ← timed r sink s!"pass.labelRules.{kind}" obsSt
        (fun _ => applyLabelRules g a2.1 n.id l)
      let bucket := ix.byKey.getD (ceIndexKey l) []
      bump r "pass.axiomTests" bucket.length
      let (s2, c2) ← timed r sink "pass.applyAxioms" obsSt (fun _ => applyAxioms bucket s1 n.id l)
      if c1 then bump r "pass.labelRulesChanged" 1
      if c2 then bump r "pass.applyAxiomsChanged" 1
      a2 := (s2, a2.2 || c1 || c2)
    let (s3, c3) ← timed r sink "pass.applyAxiomsEdges" obsSt
      (fun _ => applyAxiomsEdges ix g a2.1 n.id)
    let (s4, c4) ← timed r sink "pass.applyAxiomsConj" obsSt (fun _ => applyAxiomsConj ix s3 n.id)
    acc := (s4, a2.2 || c3 || c4)
  pure acc

/-- The search of `OWL.Refute.search`, phase for phase, with the budget in
    a reference. `fuel` is the structural bound of the recursion; it is
    the budget at the call, so it is never the bound that stops it. -/
def searchP (r : IO.Ref Prof) (sink : IO.Ref Nat) (budget : IO.Ref Nat) (trace : Bool)
    (tb : List (ClassExpr × ClassExpr)) (g : Graph) :
    Nat → Nat → RState → IO Verdict
  | 0, _, _ => pure .out
  | fuel + 1, depth, st => do
    let b ← budget.get
    if b == 0 then return .out
    budget.set (b - 1)
    bump r "search.steps" 1
    setMax r "search.maxDepth" depth
    let t0 ← IO.monoNanosNow
    let stepDone (what : String) : IO Unit := do
      let t1 ← IO.monoNanosNow
      let add (p : Prof) : Prof :=
        let v := p.nanos.getD "step.total" 0 + (t1 - t0)
        { p with nanos := p.nanos.insert "step.total" v }
      r.modify add
      if trace then
        IO.println s!"step depth={depth} nodes={st.nodes.size} labels={labelCount st} \
          maxLabels={maxLabels st} edges={st.extra.size} ident={st.ident.length} \
          ms={(t1 - t0) / 1000000} {what}"
    setMax r "state.nodes" st.nodes.size
    setMax r "state.maxLabels" (maxLabels st)
    if ← timed r sink "step.clashNodes" obsB (fun _ => clashNodes g st) then
      stepDone "clash"; return .clash
    let (st', changed) ← do
      let t0 ← IO.monoNanosNow
      let v ← onePassP r sink tb g st
      let t1 ← IO.monoNanosNow
      r.modify (fun p => { p with
        calls := p.calls.insert "step.onePass" (p.calls.getD "step.onePass" 0 + 1),
        nanos := p.nanos.insert "step.onePass" (p.nanos.getD "step.onePass" 0 + (t1 - t0)) })
      pure v
    if changed then
      bump r "search.passChanged" 1
      stepDone "changed"
      return ← searchP r sink budget trace tb g fuel depth st'
    if ← do
        let t0 ← IO.monoNanosNow
        let v ← clashNodesP r sink g st'
        let t1 ← IO.monoNanosNow
        r.modify (fun p => { p with
          calls := p.calls.insert "step.clashNodes2" (p.calls.getD "step.clashNodes2" 0 + 1),
          nanos := p.nanos.insert "step.clashNodes2"
            (p.nanos.getD "step.clashNodes2" 0 + (t1 - t0)) })
        pure v then
      stepDone "clash"; return .clash
    let (stF, forced) ← timed r sink "step.forcedIdentifications" obsSt
      (fun _ => forcedIdentifications g st')
    if forced then
      bump r "search.forced" 1
      stepDone "forced"
      return ← searchP r sink budget trace tb g fuel depth stF
    if ← timed r sink "step.propositionalClash" obsB (fun _ => propositionalClash st') then
      stepDone "clash"; return .clash
    if ← timed r sink "step.nominalClash" obsB (fun _ => nominalClash g st') then
      stepDone "clash"; return .clash
    match ← timed r sink "step.pendingUnion" (fun o => if o.isSome then 1 else 0)
        (fun _ => pendingUnion st') with
    | some (i, cs) =>
      bump r "search.unionPoints" 1
      stepDone s!"union {cs.length}"
      let mut out : Option Verdict := none
      for c in cs do
        bump r "search.unionBranches" 1
        let (sb, _) ← timed r sink "step.unionCopy" obsSt (fun _ => addLabel { st' with
          nodes := st'.nodes.map (fun m =>
            if m.id == i then
              RNode.ofLabels m.id (m.labels.filter (fun l =>
                  match l with
                  | .union es => !(ClassExpr.beqList es cs)
                  | _         => true))
            else m) } i c)
        match ← searchP r sink budget trace tb g fuel (depth + 1) sb with
        | .clash => pure ()
        | v => out := some v; break
      pure (out.getD .clash)
    | none =>
      let pairsM ← timed r sink "step.pendingMerge" (fun o => if o.isSome then 1 else 0)
        (fun _ => pendingMerge g st')
      let obsO (o : Option (List (Term × Term))) : Nat := if o.isSome then 1 else 0
      let pairsN ← if pairsM.isSome then pure none
        else timed r sink "step.pendingNominal" obsO (fun _ => pendingNominal g st')
      match pairsM <|> pairsN with
      | some pairs =>
        bump r "search.mergePoints" 1
        stepDone s!"merge {pairs.length}"
        let mut out : Option Verdict := none
        for (x, y) in pairs do
          bump r "search.mergeBranches" 1
          match ← searchP r sink budget trace tb g fuel (depth + 1) (mergeInto st' x y) with
          | .clash => pure ()
          | v => out := some v; break
        pure (out.getD .clash)
      | none => stepDone "open"; pure .open'

def flagValue (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

def ms (n : Nat) : String :=
  let m := n / 1000000
  let frac := (n / 1000) % 1000
  s!"{m}.{(toString (frac + 1000)).drop 1}"

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4refute-profile FILE.nt [--budget N] [--trace] [--check]"
      pure 2
  | file :: rest =>
    let budget := ((flagValue rest "--budget").bind String.toNat?).getD 20000
    let trace := rest.contains "--trace"
    let r ← IO.mkRef ({} : Prof)
    let sink ← IO.mkRef 0
    let text ← IO.FS.readFile file
    let ds ← match parseNQuadsFast text with
      | .ok ds => pure ds
      | .error e => throw (IO.userError s!"{file}: parse error at {e.pos}: {e.msg}")
    let input := ds.default
    let closure ← timed r sink "handoff.closure" (·.length)
      (fun _ => L4Factoidal.OWL.RL.closureFix input)
    let immediate ← timed r sink "handoff.immediate" obsB (fun _ => immediateInconsistency closure)
    let counting ← timed r sink "handoff.counting" obsB (fun _ => countingRefutes closure)
    let tb ← timed r sink "handoff.collectAxioms" (·.length) (fun _ => collectAxioms closure)
    let st0 ← timed r sink "handoff.initState" (·.nodes.size) (fun _ => initState closure)
    let st0 := { st0 with tbox := tb }
    IO.println s!"input.triples {input.length}"
    IO.println s!"closure.triples {closure.length}"
    IO.println s!"tbox.axioms {tb.length}"
    IO.println s!"state0.nodes {st0.nodes.size}"
    IO.println s!"state0.labels {labelCount st0}"
    IO.println s!"state0.maxLabels {maxLabels st0}"
    let verdict ←
      if immediate || counting then pure Verdict.clash
      else do
        let bref ← IO.mkRef budget
        let t0 ← IO.monoNanosNow
        let v ← searchP r sink bref trace tb closure (budget + 1) 0 st0
        let t1 ← IO.monoNanosNow
        IO.println s!"search.ms {ms (t1 - t0)}"
        IO.println s!"search.budgetLeft {← bref.get}"
        pure v
    let vs := match verdict with
      | .clash => "false" | .open' => "true" | .out => "unknown"
    IO.println s!"verdict {vs}"
    let p ← r.get
    for (k, v) in p.count.toList.mergeSort (fun a b => a.1 ≤ b.1) do
      IO.println s!"count {k} {v}"
    for (k, v) in p.nanos.toList.mergeSort (fun a b => a.1 ≤ b.1) do
      IO.println s!"time {k} {ms v} ms, {p.calls.getD k 0} calls"
    IO.eprintln s!"(sink {← sink.get})"
    if rest.contains "--check" then
      let lib := tableauConsistent closure budget
      let ls := match lib with
        | some false => "false" | some true => "true" | none => "unknown"
      IO.println s!"library.verdict {ls}"
      if ls != vs then
        IO.eprintln "l4refute-profile: the profiled search and tableauConsistent disagree"
        return 1
    pure 0

end RefuteProfile

def main (args : List String) : IO UInt32 := RefuteProfile.main args
