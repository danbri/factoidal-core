import Harness.PVGraphTestDispatch

/-! Native JSON-lines transport for the explicitly labeled test-only
core-plus-registry profile. Query operations use shipping Core.callIO. -/
open Lean

private def fail (message : String) : String :=
  (Json.mkObj [("ok", toJson false), ("error", toJson message)]).compress

private def request (line : String) : Except String (String × String) := do
  if line.utf8ByteSize > 67108864 then .error "test transport request exceeds 64 MiB"
  else
    let value ← Json.parse line
    let op ← (← value.getObjVal? "op").getStr?
    let args ← (← value.getObjVal? "args").getArr?
    let strings ← args.mapM Json.getStr?
    pure (op, (toJson strings).compress)

def main : IO UInt32 := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  for _ in [:100000] do
    let line ← input.getLine
    if line.isEmpty then return 0
    let result ← match request line with
      | .error message => pure (fail message)
      | .ok (op,args) => L4Wasm.PVGraphTest.callIO op args
    output.putStrLn result
    output.flush
  output.putStrLn (fail "test transport request limit reached")
  output.flush
  return 1
