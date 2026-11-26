import EthereumConsensus.SSZ.AttesterSlashing
import Lean

/-! JSONL transport for four concrete fixed-shape SSZ beacon containers.
    The supplied fields are validated and hashed in pure Lean. The JSON
    parser's input line is allocated by stdin before this layer's cap. -/

open Lean EthereumConsensus.SSZ

private def failure (name : String) : Json :=
  Json.mkObj [("status", .str "error"), ("error", .str name)]

private def success (wire root : ByteArray) : Json :=
  Json.mkObj [("status", .str "ok"),
    ("bytes", .str (L4Factoidal.Crypto.bytesToHex wire)),
    ("root", .str (L4Factoidal.Crypto.bytesToHex root))]

private def checkKeys (request : Json) (expected : List String) :
    Except String Unit := do
  let obj ← request.getObj?
  if obj.size != expected.length || !(obj.keys.all expected.contains) then
    throw "parse_error"

private def nibble (byte : UInt8) : Except String UInt8 :=
  if 48 ≤ byte && byte ≤ 57 then .ok (byte - 48)
  else if 65 ≤ byte && byte ≤ 70 then .ok (byte - 65 + 10)
  else if 97 ≤ byte && byte ≤ 102 then .ok (byte - 97 + 10)
  else .error "invalid_hex"

private def decodeHex (value : String) (count : Nat) : Except String ByteArray := do
  let encoded := value.toUTF8
  if encoded.size != 2 * count then throw "invalid_width"
  let mut decoded := ByteArray.emptyWithCapacity count
  for i in [:count] do
    let high ← nibble encoded[2 * i]!
    let low ← nibble encoded[2 * i + 1]!
    decoded := decoded.push (16 * high + low)
  return decoded

private def getHex (request : Json) (key : String) (count : Nat) :
    Except String ByteArray := do
  let value ← request.getObjValAs? String key
  decodeHex value count

private def getUInt64 (request : Json) (key : String) : Except String UInt64 := do
  let value ← request.getObjValAs? Nat key
  if value ≥ 18446744073709551616 then throw "out_of_range"
  return UInt64.ofNat value

private def fromContainer {α : Type} (result : Except ContainerError α) :
    Except String α :=
  result.mapError (fun error =>
    match error with
    | .rootWidth => "root_width"
    | .versionWidth => "version_width"
    | .basicRoot => "basic_root_error")

private def getForkContext (request : Json) : Except String ForkContext := do
  let previous ← getHex request "previous_version" 4
  let current ← getHex request "current_version" 4
  let activation ← getUInt64 request "activation_epoch"
  let genesis ← getHex request "genesis_validators_root" 32
  return ⟨previous, current, activation, genesis⟩

private def fromDomain {α : Type} (result : Except DomainError α) :
    Except String α :=
  result.mapError (fun error =>
    match error with
    | .domainTypeWidth => "domain_type_width"
    | .versionWidth => "version_width"
    | .container _ => "container_error")

private def getSlashingData (request : Json) (keyPrefix : String) : Except String AttestationData := do
  let slot ← getUInt64 request (keyPrefix ++ "slot")
  let index ← getUInt64 request (keyPrefix ++ "committee_index")
  let beacon ← getHex request (keyPrefix ++ "beacon_block_root") 32
  let se ← getUInt64 request (keyPrefix ++ "source_epoch")
  let sr ← getHex request (keyPrefix ++ "source_root") 32
  let te ← getUInt64 request (keyPrefix ++ "target_epoch")
  let tr ← getHex request (keyPrefix ++ "target_root") 32
  fromContainer (checkedAttestationData slot index beacon se sr te tr)

private def getSlashingIndices (request : Json) (key : String) : Except String (List UInt64) := do
  let values ← request.getObjValAs? (Array Nat) key
  if values.size > slashingIndexLimit then throw "resource_limit"
  let mut indices : Array UInt64 := #[]
  for value in values do
    if value ≥ 18446744073709551616 then throw "out_of_range"
    indices := indices.push (UInt64.ofNat value)
  return indices.toList

private def slashingKeys (keyPrefix : String) : List String :=
  ["slot", "committee_index", "beacon_block_root", "source_epoch",
    "source_root", "target_epoch", "target_root"].map (keyPrefix ++ ·)

private def dispatch (request : Json) : Except String Json := do
  let op ← request.getObjValAs? String "op"
  match op with
  | "beacon_header" =>
    checkKeys request ["op", "slot", "proposer_index",
      "parent_root", "state_root", "body_root"]
    let slot ← getUInt64 request "slot"
    let proposer ← getUInt64 request "proposer_index"
    let parent ← getHex request "parent_root" 32
    let state ← getHex request "state_root" 32
    let body ← getHex request "body_root" 32
    let header ← fromContainer (checkedBeaconBlockHeader slot proposer parent state body)
    let root ← fromContainer (beaconBlockHeaderRoot header)
    return success (beaconBlockHeaderWire header) root.bytes
  | "checkpoint" =>
    checkKeys request ["op", "epoch", "root"]
    let epoch ← getUInt64 request "epoch"
    let rootBytes ← getHex request "root" 32
    let checkpoint ← fromContainer (checkedCheckpoint epoch rootBytes)
    let root ← fromContainer (checkpointRoot checkpoint)
    return success (checkpointWire checkpoint) root.bytes
  | "fork_data" =>
    checkKeys request ["op", "current_version", "genesis_validators_root"]
    let version ← getHex request "current_version" 4
    let genesis ← getHex request "genesis_validators_root" 32
    let data ← fromContainer (checkedForkData version genesis)
    return success (forkDataWire data) (forkDataRoot data).bytes
  | "signing_data" =>
    checkKeys request ["op", "object_root", "domain"]
    let object ← getHex request "object_root" 32
    let domain ← getHex request "domain" 32
    let data ← fromContainer (checkedSigningData object domain)
    return success (signingDataWire data) (signingDataRoot data).bytes
  | "signing_domain" =>
    checkKeys request ["op", "domain_type", "epoch", "previous_version",
      "current_version", "activation_epoch", "genesis_validators_root"]
    let context ← getForkContext request
    let t ← getHex request "domain_type" 4
    let epoch ← getUInt64 request "epoch"
    let domain ← fromDomain (getSigningDomain context t epoch)
    return Json.mkObj [("status", .str "ok"),
      ("domain", .str (L4Factoidal.Crypto.bytesToHex domain.bytes))]
  | "proposer_header_signing" =>
    checkKeys request ["op", "slot", "proposer_index", "parent_root",
      "state_root", "body_root", "previous_version", "current_version",
      "activation_epoch", "genesis_validators_root"]
    let context ← getForkContext request
    let slot ← getUInt64 request "slot"
    let proposer ← getUInt64 request "proposer_index"
    let parent ← getHex request "parent_root" 32
    let state ← getHex request "state_root" 32
    let body ← getHex request "body_root" 32
    let header ← fromContainer (checkedBeaconBlockHeader slot proposer parent state body)
    let result ← fromDomain (headerProposerSigningRoot context header)
    return Json.mkObj [("status", .str "ok"),
      ("object_root", .str (L4Factoidal.Crypto.bytesToHex result.objectRoot.bytes)),
      ("domain", .str (L4Factoidal.Crypto.bytesToHex result.domain.bytes)),
      ("signing_root", .str (L4Factoidal.Crypto.bytesToHex result.signingRoot.bytes))]
  | "attester_signing" =>
    checkKeys request ["op", "slot", "committee_index", "beacon_block_root",
      "source_epoch", "source_root", "target_epoch", "target_root",
      "previous_version", "current_version", "activation_epoch", "genesis_validators_root"]
    let context ← getForkContext request
    let slot ← getUInt64 request "slot"
    let index ← getUInt64 request "committee_index"
    let beacon ← getHex request "beacon_block_root" 32
    let se ← getUInt64 request "source_epoch"
    let sr ← getHex request "source_root" 32
    let te ← getUInt64 request "target_epoch"
    let tr ← getHex request "target_root" 32
    let data ← fromContainer (checkedAttestationData slot index beacon se sr te tr)
    let result ← fromDomain (attesterSigningRoot context data)
    return Json.mkObj [("status", .str "ok"),
      ("bytes", .str (L4Factoidal.Crypto.bytesToHex (attestationDataWire data))),
      ("object_root", .str (L4Factoidal.Crypto.bytesToHex result.objectRoot.bytes)),
      ("domain", .str (L4Factoidal.Crypto.bytesToHex result.domain.bytes)),
      ("signing_root", .str (L4Factoidal.Crypto.bytesToHex result.signingRoot.bytes))]
  | "attester_slashing_preflight" =>
    checkKeys request (["op", "previous_version", "current_version", "activation_epoch",
      "genesis_validators_root", "a_indices", "b_indices"] ++
      slashingKeys "a_" ++ slashingKeys "b_")
    let context ← getForkContext request
    let a ← getSlashingData request "a_"
    let b ← getSlashingData request "b_"
    let left ← getSlashingIndices request "a_indices"
    let right ← getSlashingIndices request "b_indices"
    match prepareAttesterSlashing context a b left right with
    | .error .resourceLimit => throw "resource_limit"
    | .error .badIndices => throw "bad_indices"
    | .error .notConflicting => throw "not_conflicting"
    | .error .noCommonIndices => throw "no_common_indices"
    | .error (.signing _) => throw "signing_error"
    | .ok evidence =>
      return Json.mkObj [("status", .str "prepared_not_authenticated"),
        ("common_indices", toJson (evidence.commonIndices.map UInt64.toNat)),
        ("first_signing_root", .str (L4Factoidal.Crypto.bytesToHex evidence.firstSigningRoot.bytes)),
        ("second_signing_root", .str (L4Factoidal.Crypto.bytesToHex evidence.secondSigningRoot.bytes))]
  | _ => throw "unknown_operation"

/-- Compare raw, unquoted field separators with the parser's final key
    count. Thus duplicate JSON fields, including escaped spellings, refuse. -/
private def rawFieldCount (line : String) : Nat := Id.run do
  let mut quoted := false
  let mut escaped := false
  let mut fields := 0
  for char in line do
    if quoted then
      if escaped then escaped := false
      else if char == '\\' then escaped := true
      else if char == '"' then quoted := false
    else if char == '"' then
      quoted := true
    else if char == ':' then
      fields := fields + 1
  return fields

private def handle (line : String) : Json :=
  if line.utf8ByteSize > 2048 then failure "resource_limit"
  else
    match Json.parse line with
    | .error _ => failure "parse_error"
    | .ok request =>
      match request.getObj? with
      | .error _ => failure "parse_error"
      | .ok object =>
        if object.size != rawFieldCount line then failure "parse_error"
        else
          match dispatch request with
          | .ok result => result
          | .error error => failure error

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    output.putStrLn (handle line).compress
    output.flush
