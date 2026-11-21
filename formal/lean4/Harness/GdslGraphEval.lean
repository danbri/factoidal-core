import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.PVGraph

/-!
Executable independent Lean CPU result oracle for the same actual
GDSL 0.2 JSON graph and bound u32 inputs the JS runCPU() receives.
One output line for each corpus case; semantic mismatch or differing
admission is a failed build in the Node comparison driver.
-/
namespace Harness.GdslGraphEval

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph

private def evalCase (request : Json) : Except String Json := do
  let id ← (← request.getObjVal? "case").getStr?
  let pvgraph ← request.getObjVal? "pvgraph"
  let bindings ← request.getObjVal? "bindings"
  match PVGraph.evaluate? pvgraph bindings with
  | .ok outputs =>
      return Json.mkObj [("case",toJson id),
        ("accepted",toJson true),("outputs",outputs)]
  | .error _ =>
      return Json.mkObj [("case",toJson id),
        ("accepted",toJson false)]

def main (args : List String) : IO UInt32 := do
  let [path] := args | do
    IO.eprintln "usage: lake env lean --run Harness/GdslGraphEval.lean cases.jsonl"
    return 2
  let source ← IO.FS.readFile path
  let mut count := 0
  for line in source.splitOn "\n" do
    if !line.isEmpty then
      match Json.parse line >>= evalCase with
      | .error msg => IO.eprintln s!"bad evaluator corpus: {msg}"; return 2
      | .ok result => IO.println result.compress; count := count + 1
  if count == 0 then
    IO.eprintln "empty GDSL semantic corpus"
    return 2
  return 0

end Harness.GdslGraphEval

def main (args : List String) : IO UInt32 :=
  Harness.GdslGraphEval.main args
