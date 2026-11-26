import EthereumConsensus.SSZ.ByteProof
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

/-! JSON Lines driver for the concrete SSZ proof and SHA-256 test interface. -/

open Lean EthereumConsensus.SSZ

private def errorCode : ByteProofError → String
  | .resourceLimit => "resource_limit"
  | .invalidIndex => "invalid_index"
  | .invalidClaims => "invalid_claims"
  | .leafCount => "leaf_count"
  | .proofLength => "proof_length"
  | .chunkWidth => "chunk_width"
  | .incompleteProof => "incomplete_proof"
  | .conflictingNode => "conflicting_node"
  | .parseError => "parse_error"

private def hexNibble (byte : UInt8) : Except ByteProofError UInt8 :=
  if 48 ≤ byte && byte ≤ 57 then .ok (byte - 48)
  else if 65 ≤ byte && byte ≤ 70 then .ok (byte - 65 + 10)
  else if 97 ≤ byte && byte ≤ 102 then .ok (byte - 97 + 10)
  else .error .parseError

private def decodeHex (value : String) : Except ByteProofError ByteArray := do
  let encoded := value.toUTF8
  if encoded.size % 2 ≠ 0 then throw .parseError
  let byteCount := encoded.size / 2
  let mut decoded := ByteArray.emptyWithCapacity byteCount
  for offset in [:byteCount] do
    let high ← hexNibble encoded[2 * offset]!
    let low ← hexNibble encoded[2 * offset + 1]!
    decoded := decoded.push (16 * high + low)
  return decoded

private def fromJsonResult (result : Except String α) : Except ByteProofError α :=
  result.mapError (fun _ => .parseError)

private def optionalNat (request : Json) (key : String) (fallback : Nat) :
    Except ByteProofError Nat :=
  match request.getObjVal? key with
  | .ok value => fromJsonResult value.getNat?
  | .error _ => .ok fallback

private def checkKeys (request : Json) (keys : List String) : Except ByteProofError Unit := do
  let members ← fromJsonResult request.getObj?
  if !(members.keys.all keys.contains) then throw .parseError

private def okDigest (digest : ByteArray) : Json :=
  Json.mkObj [("status", .str "ok"), ("digest", .str (L4Factoidal.Crypto.bytesToHex digest))]

private def okProof (result : ByteProofResult) : Json :=
  Json.mkObj [("status", .str "ok"),
    ("root", .str (L4Factoidal.Crypto.bytesToHex result.root.bytes)),
    ("matches", .bool result.matchesRoot)]

private def dispatch (request : Json) : Except ByteProofError Json := do
  let op ← fromJsonResult (request.getObjValAs? String "op")
  match op with
  | "hash" =>
    checkKeys request ["op", "data"]
    let data ← fromJsonResult (request.getObjValAs? String "data")
    if data.utf8ByteSize > 2 * 65536 then throw .resourceLimit
    let bytes ← decodeHex data
    return okDigest (L4Factoidal.Crypto.sha256 bytes)
  | "branch" =>
    checkKeys request ["op", "index", "leaf", "proof", "root", "maxDepth"]
    let index ← fromJsonResult (request.getObjValAs? Nat "index")
    let maxDepth ← optionalNat request "maxDepth" maxByteProofDepth
    let leafHex ← fromJsonResult (request.getObjValAs? String "leaf")
    let proofHex ← fromJsonResult (request.getObjValAs? (List String) "proof")
    let rootHex ← fromJsonResult (request.getObjValAs? String "root")
    let leaf ← decodeHex leafHex
    let proof ← proofHex.mapM decodeHex
    let root ← decodeHex rootHex
    return okProof (← verifyByteBranch maxDepth index leaf proof root)
  | "multi" =>
    checkKeys request ["op", "indices", "leaves", "proof", "root", "maxClaims", "maxDepth"]
    let indices ← fromJsonResult (request.getObjValAs? (List Nat) "indices")
    let maxClaims ← optionalNat request "maxClaims" maxByteProofClaims
    let maxDepth ← optionalNat request "maxDepth" maxByteProofDepth
    let leavesHex ← fromJsonResult (request.getObjValAs? (List String) "leaves")
    let proofHex ← fromJsonResult (request.getObjValAs? (List String) "proof")
    let rootHex ← fromJsonResult (request.getObjValAs? String "root")
    let leaves ← leavesHex.mapM decodeHex
    let proof ← proofHex.mapM decodeHex
    let root ← decodeHex rootHex
    return okProof (← verifyByteMulti maxClaims maxDepth indices leaves proof root)
  | _ => throw .parseError

/-- The wire schema uses an object and optional arrays of scalars. Check
    nesting and cap decimal digit runs before invoking Lean's JSON parser.
    Integer tokens have neither a decimal point nor an exponent. Count
    unquoted field separators to detect duplicate decoded keys. -/
private def checkJsonShape (line : String) : Except ByteProofError Nat := do
  let mut nesting := 0
  let mut quoted := false
  let mut escaped := false
  let mut digits := 0
  let mut fieldCount := 0
  for char in line do
    if quoted then
      if escaped then escaped := false
      else if char == '\\' then escaped := true
      else if char == '"' then quoted := false
    else if '0' ≤ char && char ≤ '9' then
      digits := digits + 1
      if digits > 128 then throw .resourceLimit
    else
      if char == '.' || ((char == 'e' || char == 'E') && digits != 0) then
        throw .parseError
      digits := 0
      match char with
      | '"' => quoted := true
      | '{' | '[' =>
        nesting := nesting + 1
        if nesting > 2 then throw .parseError
      | '}' | ']' => nesting := nesting - 1
      | ':' => fieldCount := fieldCount + 1
      | _ => pure ()
  return fieldCount

private def handleLine (line : String) : Except ByteProofError Json := do
  let newlineBytes := if line.endsWith "\r\n" then 2 else if line.endsWith "\n" then 1 else 0
  if line.utf8ByteSize - newlineBytes > 1024 * 1024 then throw .resourceLimit
  let fieldCount ← checkJsonShape line
  let request ← fromJsonResult (Json.parse line)
  let members ← fromJsonResult request.getObj?
  if members.size ≠ fieldCount then throw .parseError
  dispatch request

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    -- getLine allocates the complete line before the payload size check.
    let line ← input.getLine
    if line.isEmpty then break
    let response := match handleLine line with
      | .ok json => json
      | .error err => Json.mkObj [("status", .str "error"), ("error", .str (errorCode err))]
    output.putStrLn response.compress
    output.flush
