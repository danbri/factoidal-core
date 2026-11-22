import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder

/-!
Measure the added translation-validation cost on the same source tree.

The two paths are candidate emission and the public checked compiler. Each
sample checks that both returned the same complete plan. Raw nanosecond samples
preserve the distribution; alternating order reduces order bias. This is a Lean
command-line measurement, not a browser, WebGPU or end-to-end application timing.
JSON serialisation and the equality check are outside the timed interval.

Run with `lake env lean --run Harness/PVGraphPlanTiming.lean` from formal/lean4,
under the shared build/timing locks. Tracking:
https://github.com/danbri/factoidal-core/issues/802.
-/

open Lean
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

private def chain (count : Nat) : M Unit := do
  let mut x ← input "words"
  for i in [:count] do
    let value := UInt32.ofNat (i * 23 + 1)
    x ← if i % 3 == 0 then mapAdd x value
      else if i % 3 == 1 then mapMul x value
      else mapXor x value
  output "answer" x (some "result")

private def measured (compiler : Json → Json → Except String Json)
    (graph sizes : Json) : IO (Nat × Json) := do
  let start ← IO.monoNanosNow
  let result ← IO.lazyPure fun _ => compiler graph sizes
  let elapsed := (← IO.monoNanosNow) - start
  match result with
  | .error error => throw (IO.userError s!"planning timing refused: {error}")
  | .ok plan => return (elapsed,plan)

def main : IO Unit := do
  for count in [0,1,32,120] do
    let graph := build (chain count)
    -- Warm both code paths before retaining samples, including the zero-map
    -- graph so that callers can inspect the cost outside the covered fragment.
    let warmSizes := Json.mkObj [("words",toJson (65 : Nat))]
    let _ ← measured GpuPlan.compileCandidate? graph warmSizes
    let _ ← measured GpuPlan.compile? graph warmSizes
    let mut samples : Array Json := #[]
    let mut planBytes := 0
    for i in [:31] do
      let sizes := Json.mkObj [("words",toJson (64 + i % 2))]
      let (candidate,checked) ← if i % 2 == 0 then do
        let candidate ← measured GpuPlan.compileCandidate? graph sizes
        let checked ← measured GpuPlan.compile? graph sizes
        pure (candidate,checked)
      else do
        let checked ← measured GpuPlan.compile? graph sizes
        let candidate ← measured GpuPlan.compileCandidate? graph sizes
        pure (candidate,checked)
      let expected := candidate.2.compress
      if expected != checked.2.compress then
        throw (IO.userError "candidate and checked compiler returned different plans")
      planBytes := expected.utf8ByteSize
      samples := samples.push (Json.mkObj [
        ("candidateNs",toJson candidate.1),("checkedNs",toJson checked.1)])
    IO.println ((Json.mkObj [
      ("schema",toJson ("pvgraph-mapzip-plan-timing-v1" : String)),
      ("mapNodes",toJson count),("graphNodes",toJson (count + 2)),
      ("samples",toJson samples),("lastPlanBytes",toJson planBytes)]).compress)
