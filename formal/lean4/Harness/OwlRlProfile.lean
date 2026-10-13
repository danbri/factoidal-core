/-
Harness.OwlRlProfile — where the OWL 2 RL closure spends its rounds.

    l4owl-rl-profile FILE.nt [--rows] [--fuel N]

Reads one N-Triples or N-Quads file and runs the indexed OWL 2 RL closure
(`OWL.RL.stepI`, the loop `OWL.RL.closureI` runs) round by round. For each
round it prints the input size, the conclusions emitted before
deduplication, the new triples, and the time of the conclusion list and of
the insertion. With `--rows` it also evaluates each of the 74 rows of
`conclusionsListS` on its own over every driving triple of the round, and
prints per row: the conclusions it emits, how many of them are new (not in
the round's input), how many come from driving triples added by the
previous round (the delta), and its time. Every timed value is consumed by
a counter before the second clock read (skills/measuring-inference,
sections 9 and 11), and the row times are printed beside the round total.

This file holds no OWL logic. Issue
https://github.com/danbri/factoidal/issues/756 item 2.
-/
import L4Factoidal.OWL.RLClosureIndexed
import L4Factoidal.Syntax.NQuadsFast

namespace OwlRlProfile

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.OWL.RL

def rows : List (String × (Store → Triple → List Triple)) := [
  ("eqRefS", eqRefSForS),
  ("eqRefP", eqRefPForS),
  ("eqRefO", eqRefOForS),
  ("eqSym", eqSymForS),
  ("eqTrans", eqTransForS),
  ("eqRepS", eqRepSForS),
  ("eqRepP", eqRepPForS),
  ("eqRepO", eqRepOForS),
  ("prpDom", prpDomForS),
  ("prpRng", prpRngForS),
  ("prpFp", prpFpForS),
  ("prpIfp", prpIfpForS),
  ("prpSymp", prpSympForS),
  ("prpTrp", prpTrpForS),
  ("prpSpo1", prpSpo1ForS),
  ("prpSpo2", prpSpo2ForS),
  ("prpEqp1", prpEqp1ForS),
  ("prpEqp2", prpEqp2ForS),
  ("prpInv1", prpInv1ForS),
  ("prpInv2", prpInv2ForS),
  ("invFpIfp", invFpIfpForS),
  ("invIfpFp", invIfpFpForS),
  ("invFpIfpRev", invFpIfpRevForS),
  ("invIfpFpRev", invIfpFpRevForS),
  ("prpKey", prpKeyForS),
  ("clsInt1", clsInt1ForS),
  ("clsInt2", clsInt2ForS),
  ("clsUni", clsUniForS),
  ("clsSvf1", clsSvf1ForS),
  ("clsSvf2", clsSvf2ForS),
  ("clsAvf", clsAvfForS),
  ("clsHv1", clsHv1ForS),
  ("clsHv2", clsHv2ForS),
  ("clsHs1", clsHs1ForS),
  ("clsHs2", clsHs2ForS),
  ("clsMaxc2", clsMaxc2ForS),
  ("clsOo", clsOoForS),
  ("caxSco", caxScoForS),
  ("caxEqc1", caxEqc1ForS),
  ("caxEqc2", caxEqc2ForS),
  ("scmCls", scmClsForS),
  ("scmSco", scmScoForS),
  ("scmEqc1", scmEqc1ForS),
  ("scmEqc2", scmEqc2ForS),
  ("scmSpo", scmSpoForS),
  ("scmEqp1", scmEqp1ForS),
  ("scmEqp2", scmEqp2ForS),
  ("scmDom1", scmDom1ForS),
  ("scmDom2", scmDom2ForS),
  ("scmRng1", scmRng1ForS),
  ("scmRng2", scmRng2ForS),
  ("scmOp", scmOpForS),
  ("scmDp", scmDpForS),
  ("scmSvf1", scmSvf1ForS),
  ("scmSvf2", scmSvf2ForS),
  ("scmAvf1", scmAvf1ForS),
  ("scmAvf2", scmAvf2ForS),
  ("scmHv", scmHvForS),
  ("scmInt", scmIntForS),
  ("scmUni", scmUniForS),
  ("eqDiffSym", eqDiffSymForS),
  ("pdwToDiff", pdwToDiffForS),
  ("caxDwToDiff", caxDwToDiffForS),
  ("fpDiffToDiff", fpDiffToDiffForS),
  ("ifpDiffToDiff", ifpDiffToDiffForS),
  ("chainToTrans", chainToTransForS),
  ("prpRfl", prpRflForS),
  ("xsdAxioms", xsdAxiomsForS),
  ("dtRangeIntersect", dtRangeIntersectForS),
  ("caxDwToComplement", caxDwToComplementForS),
  ("clsMaxqc1ToComplement", clsMaxqc1ToComplementForS),
  ("minCard1Comprehension", minCard1ComprehensionForS),
  ("caxAdcToDw", caxAdcToDwForS),
  ("inverseOfDomRngFlip", inverseOfDomRngFlipForS)
]

def ms (n : Nat) : String :=
  let m := n / 1000000
  let f := (n % 1000000) / 1000
  s!"{m}.{if f < 10 then "00" else if f < 100 then "0" else ""}{f}"

def flagValue (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

/-- Emitted, new, from-delta emitted, from-delta new, for one row over a
round. `lo` is the first position of the delta in `i.all`. -/
@[noinline] def rowStats (i : Index) (lo : Nat) (f : Store → Triple → List Triple) :
    Nat × Nat × Nat × Nat := Id.run do
  let s := Store.ofIndex i
  let mut e := 0
  let mut n := 0
  let mut ed := 0
  let mut nd := 0
  for h : j in [0:i.all.size] do
    let d := i.all[j]
    let out := f s d
    let k := out.length
    let kn := out.foldl (fun a t => if i.memB t then a else a + 1) 0
    e := e + k
    n := n + kn
    if j ≥ lo then
      ed := ed + k
      nd := nd + kn
  return (e, n, ed, nd)

def main (args : List String) : IO UInt32 := do
  match args with
  | [] =>
      IO.eprintln "usage: l4owl-rl-profile FILE.nt [--rows] [--fuel N]"
      pure 2
  | file :: rest =>
    let fuel := ((flagValue rest "--fuel").bind String.toNat?).getD 1000
    let withRows := rest.contains "--rows"
    let text ← IO.FS.readFile file
    let ds ← match parseNQuadsFast text with
      | .ok ds => pure ds
      | .error e => throw (IO.userError s!"{file}: parse error at {e.pos}: {e.msg}")
    let g := ds.default
    let sink ← IO.mkRef 0
    let t0 ← IO.monoNanosNow
    let i0 := Index.ofGraph g
    sink.modify (· + i0.all.size)
    let t1 ← IO.monoNanosNow
    IO.println s!"input.triples {g.length}"
    IO.println s!"index.ms {ms (t1 - t0)}"
    let mut cur := i0
    let mut lo := 0
    let mut totStep := 0
    let mut totIns := 0
    let mut totRows : Std.HashMap String (Nat × Nat × Nat × Nat × Nat) := {}
    for k in [0:fuel] do
      if withRows then
        let mut rowSum := 0
        for (name, f) in rows do
          let a ← IO.monoNanosNow
          let st := rowStats cur lo f
          sink.modify (· + st.1)
          let b ← IO.monoNanosNow
          rowSum := rowSum + (b - a)
          let (e, n, ed, nd) := st
          if e > 0 then
            IO.println s!"row {k + 1} {name} emitted {e} new {n} deltaEmitted {ed} deltaNew {nd} ms {ms (b - a)}"
          let (pe, pn, ped, pnd, pt) := totRows.getD name (0, 0, 0, 0, 0)
          totRows := totRows.insert name (pe + e, pn + n, ped + ed, pnd + nd, pt + (b - a))
        IO.println s!"rows.sum {k + 1} ms {ms rowSum}"
      let a ← IO.monoNanosNow
      let concl := stepConclusionsS (Store.ofIndex cur)
      sink.modify (· + concl.length)
      let b ← IO.monoNanosNow
      let next := cur.insertAll concl
      sink.modify (· + next.all.size)
      let c ← IO.monoNanosNow
      totStep := totStep + (b - a)
      totIns := totIns + (c - b)
      let added := next.all.size - cur.all.size
      IO.println s!"round {k + 1} input {cur.all.size} delta {cur.all.size - lo} emitted {concl.length} new {added} conclusions.ms {ms (b - a)} insert.ms {ms (c - b)}"
      if added = 0 then
        IO.println s!"rounds {k + 1}"
        break
      lo := cur.all.size
      cur := next
    IO.println s!"closure.triples {cur.all.size}"
    IO.println s!"total.conclusions.ms {ms totStep}"
    IO.println s!"total.insert.ms {ms totIns}"
    if withRows then
      for (name, (e, n, ed, nd, t)) in totRows.toList.mergeSort (fun a b => a.2.2.2.2.2 ≥ b.2.2.2.2.2) do
        IO.println s!"rowtotal {name} emitted {e} new {n} deltaEmitted {ed} deltaNew {nd} ms {ms t}"
    IO.eprintln s!"(sink {← sink.get})"
    pure 0

end OwlRlProfile

def main (args : List String) : IO UInt32 := OwlRlProfile.main args
