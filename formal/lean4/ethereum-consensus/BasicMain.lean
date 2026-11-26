import EthereumConsensus.SSZ.BasicTypes
import Lean

/-! Transport-only JSONL interface to independently implemented SSZ basic codecs.
    Input is restricted to flat objects with a scalar or a byte array.
    The host does not implement SSZ or supply hash results. -/

open Lean EthereumConsensus.SSZ

private def errorResponse (code : String) : Json :=
  Json.mkObj [("status", .str "error"), ("error", .str code)]

private def goodWire (wire root : ByteArray) : Json :=
  Json.mkObj [("status", .str "ok"),
    ("bytes", .str (L4Factoidal.Crypto.bytesToHex wire)),
    ("root", .str (L4Factoidal.Crypto.bytesToHex root))]

private def getBytes (request : Json) : Except String ByteArray := do
  let numbers ← request.getObjValAs? (List Nat) "bytes"
  if numbers.length > 64 then throw "resource_limit"
  if numbers.any (fun n => n > 255) then throw "invalid_byte"
  return numbers.foldl (fun out n => out.push (UInt8.ofNat n)) ByteArray.empty

private def checkKeys (request : Json) (expected : List String) : Except String Unit := do
  let obj ← request.getObj?
  if obj.size != expected.length || !(obj.keys.all expected.contains) then
    throw "parse_error"

private def dispatch (request : Json) : Except String Json := do
  let op ← request.getObjValAs? String "op"
  match op with
  | "encode_u64" =>
    checkKeys request ["op", "value"]
    let value ← request.getObjValAs? Nat "value"
    if value ≥ 18446744073709551616 then throw "out_of_range"
    let n := UInt64.ofNat value
    let wire := encodeUInt64 n
    match uint64Root n with
    | .ok root => return goodWire wire root.bytes
    | .error _ => throw "internal_root_error"
  | "decode_u64" =>
    checkKeys request ["op", "bytes"]
    let bytes ← getBytes request
    match decodeUInt64 bytes with
    | .ok value =>
      return Json.mkObj [("status", .str "ok"),
        ("value", .str (toString value.toNat))]
    | .error .invalidLength => throw "invalid_length"
    | .error _ => throw "invalid_encoding"
  | "encode_bool" =>
    checkKeys request ["op", "value"]
    let value ← request.getObjValAs? Bool "value"
    let wire := encodeBool value
    match boolRoot value with
    | .ok root => return goodWire wire root.bytes
    | .error _ => throw "internal_root_error"
  | "decode_bool" =>
    checkKeys request ["op", "bytes"]
    let bytes ← getBytes request
    match decodeBool bytes with
    | .ok value =>
      return Json.mkObj [("status", .str "ok"), ("value", .bool value)]
    | .error .invalidLength => throw "invalid_length"
    | .error .noncanonicalBoolean => throw "noncanonical_boolean"
    | .error _ => throw "invalid_encoding"
  | _ => throw "unknown_operation"

private def handle (line : String) : Json :=
  if line.utf8ByteSize > 4096 then errorResponse "resource_limit"
  else
    match Json.parse line with
    | .error _ => errorResponse "parse_error"
    | .ok request =>
      match dispatch request with
      | .ok json => json
      | .error err => errorResponse err

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    output.putStrLn (handle line).compress
    output.flush
