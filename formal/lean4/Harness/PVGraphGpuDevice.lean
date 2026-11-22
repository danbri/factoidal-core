import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
import L4Factoidal.GpuDomainSpecificLanguage.PVGraphBuilder

/-!
Native Lean emits plans and reference answers for the actual device lane.
The output is JSONL, one line per case; the GPU runner executes the
Lean-generated WGSL and compares complete output bytes with Lean results.
No JS PVGraph interpreter is involved.
-/

open Lean
open L4Factoidal.GpuDomainSpecificLanguage
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph.Builder

private def mapWords : M Unit := do
  let x ← input "words"
  let m ← mapMul x 257 (some "multiply")
  let y ← mapXor m 2147483648 (some "mask")
  output "answer" y (some "result")

private def fanout : M Unit := do
  let x ← input "words"
  let a ← mapMul x 3 (some "multiply")
  let b ← mapAdd x 5 (some "offset")
  let zipped ← zipAdd a b (some "combine")
  output "sum" zipped (some "result")

private def scalarShape : M Unit := do
  let x ← input "template"
  let one ← scalarConst 4294967295 (some "constant")
  let y ← broadcast one x (some "fill")
  let z ← zipXor x y (some "mask")
  output "inverted" z (some "result")

private def scalarPair : M Unit := do
  let a ← input "a" .scalar
  let b ← input "b" .scalar
  let s ← scalarAdd a b (some "sum")
  output "answer" s (some "result")

private def scanCpu : M Unit := do
  let x ← input "words"
  let positions ← scanSum x (some "scan")
  output "out" positions (some "result")

private def caseData : List (String × M Unit × Json × Json) := [
  ("map-highbits", mapWords,
    Json.mkObj [("words", toJson ([0,1,4294967295,2147483648,7,99] : List Nat))],
    Json.mkObj [("words", toJson (6 : Nat))]),
  ("fanout-zip", fanout,
    Json.mkObj [("words", toJson ([0,1,2,5,13,4294967295] : List Nat))],
    Json.mkObj [("words", toJson (6 : Nat))]),
  ("broadcast", scalarShape,
    Json.mkObj [("template", toJson ([0,1,2,5,4294967295] : List Nat))],
    Json.mkObj [("template", toJson (5 : Nat))]),
  ("scalar", scalarPair,
    Json.mkObj [("a", toJson (4294967295 : Nat)), ("b", toJson (3 : Nat))],
    Json.mkObj [("a", toJson (1 : Nat)), ("b", toJson (1 : Nat))]),
  ("empty", fanout,
    Json.mkObj [("words", toJson ([] : List Nat))],
    Json.mkObj [("words", toJson (0 : Nat))]),
  ("large-8192", mapWords,
    Json.mkObj [("words", toJson ((List.range 8192).map (fun n => (n*11939) % 4294967296)))],
    Json.mkObj [("words", toJson (8192 : Nat))]),
  ("scan-cpu-only", scanCpu,
    Json.mkObj [("words", toJson ([1,2,3,4,5] : List Nat))],
    Json.mkObj [("words", toJson (5 : Nat))])
]

def main : IO Unit := do
  for (name, program, bindings, shapes) in caseData do
    let pv := build program
    let expected ← match PVGraph.evaluate? pv bindings with
      | .ok output => pure output
      | .error e => throw (IO.userError s!"{name}: Lean reference: {e}")
    let (plan,eligible) ← match GpuPlan.compile? pv shapes with
      | .ok output => pure (output,true)
      | .error _ => pure (Json.null,false)
    if name == "scan-cpu-only" && eligible then
      throw (IO.userError "scan incorrectly admitted to GPU direct fragment")
    if name != "scan-cpu-only" && !eligible then
      throw (IO.userError s!"{name}: GPU plan unexpectedly refused")
    IO.println ((Json.mkObj [
      ("case",toJson name),("pvgraph",pv),("input",bindings),
      ("plan",plan),("eligible",toJson eligible),("expected",expected)]).compress)
