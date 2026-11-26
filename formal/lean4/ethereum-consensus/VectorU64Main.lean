import EthereumConsensus.SSZ.VectorU64
import Lean

/-! Minimal transport interface. Protocol encoding and Merkleisation run only
    in Lean. Input line-size refusal is after stdin allocation: this is not a
    network-safe streaming input cap. The pinned source is Lean 4.33.1. -/

open Lean EthereumConsensus.SSZ

private def failure (name : String) : Json :=
  Json.mkObj [("status", .str "error"), ("error", .str name)]

private def dispatch (request : Json) : Except String Json := do
  let object ← request.getObj?
  if object.size != 3 || !(object.keys.all (["op", "length", "values"].contains)) then
    throw "parse_error"
  let operation ← request.getObjValAs? String "op"
  if operation != "vector_u64" then throw "unknown_operation"
  let declared ← request.getObjValAs? Nat "length"
  if declared = 0 || declared > 64 then throw "resource_limit"
  let rawValues ← request.getObjValAs? (List Nat) "values"
  if rawValues.length != declared then throw "invalid_length"
  if rawValues.any (fun n => n ≥ 18446744073709551616) then
    throw "out_of_range"
  let values := rawValues.map UInt64.ofNat
  match checkedVectorU64 declared values with
  | .ok (wire, root) =>
      return Json.mkObj [("status", .str "ok"),
        ("bytes", .str (L4Factoidal.Crypto.bytesToHex wire)),
        ("root", .str (L4Factoidal.Crypto.bytesToHex root.bytes))]
  | .error .resourceLimit => throw "resource_limit"
  | .error .wrongLength => throw "invalid_length"
  | .error .invalidChunk => throw "invalid_chunk"
  | .error .incompleteTree => throw "incomplete_tree"

private def handle (line : String) : Json :=
  if line.utf8ByteSize > 4096 then failure "resource_limit"
  else
    match Json.parse line with
    | .error _ => failure "parse_error"
    | .ok request =>
        match dispatch request with
        | .ok output => output
        | .error reason => failure reason

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    output.putStrLn (handle line).compress
    output.flush
