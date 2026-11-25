import Lean.Data.Json
import L4Factoidal.GpuDomainSpecificLanguage.PVGraph

/-!
# Cross-language GDSL 0.2 admission checker

Input is a JSONL file written by the real JS GDSL graph API, each line:
  {"case":"name","graph":{...canonical gdsl/0.2 JSON...}}

Output is one JSONL line per case:
  {"case":"name","admitted":true|false}

The user-facing JS and the Lean checker independently parse and check
the SAME unmodified JSON graph document. The Node CI driver compares
their accept/refuse verdicts, including adversarial mutations.

This is executable differential evidence, not a theorem that the two
parsers agree for every input string.
-/

namespace Harness.GdslGraphCheck

open Lean
open L4Factoidal.GpuDomainSpecificLanguage.PVGraph

private def runCase (j : Json) : Except String Json := do
  let caseId ← (← j.getObjVal? "case").getStr?
  let pvgraph ← j.getObjVal? "pvgraph"
  let admitted := (admit? pvgraph).isOk
  return Json.mkObj [("case", toJson caseId),
    ("admitted", toJson admitted)]

def main (args : List String) : IO UInt32 := do
  let [inputPath] := args | do
    IO.eprintln "usage: lake env lean --run Harness/GdslGraphCheck.lean cases.jsonl"
    return 2
  let source ← IO.FS.readFile inputPath
  let mut n := 0
  for line in source.splitOn "\n" do
    if !line.isEmpty then
      match Json.parse line >>= runCase with
      | .error e =>
          IO.eprintln s!"bad GDSL JSONL fixture: {e}"
          return 2
      | .ok report =>
          IO.println report.compress
          n := n + 1
  if n == 0 then
    IO.eprintln "GDSL corpus empty"
    return 2
  return 0

end Harness.GdslGraphCheck

def main (args : List String) : IO UInt32 :=
  Harness.GdslGraphCheck.main args
