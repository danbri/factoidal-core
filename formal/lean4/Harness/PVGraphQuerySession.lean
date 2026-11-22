import Wasm.CoreDispatch

/-!
Native JSON-lines transport for the same `L4Wasm.Core.callIO` dispatcher
used by the core Wasm engine. This is a test executable, with no alternate
SPARQL parser, planner, join evaluator or dataset-handle implementation.
The parent sends `{ "op": string, "args": string[] }` and receives the
engine's own JSON envelope on one flushed line. State persists between calls.
-/

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
  -- An explicit request bound prevents an accidentally detached test worker
  -- from waiting indefinitely after a malformed caller keeps writing.
  for _ in [:100000] do
    let line ← input.getLine
    if line.isEmpty then return 0
    let result ← match request line with
      | .error message => pure (fail message)
      | .ok (op,args) => L4Wasm.Core.callIO op args
    output.putStrLn result
    output.flush
  output.putStrLn (fail "test transport request limit reached")
  output.flush
  return 1
