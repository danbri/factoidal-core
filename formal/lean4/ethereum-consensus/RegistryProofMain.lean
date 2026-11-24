import EthereumConsensus.SSZ.ValidatorRegistry
import Lean

/-! Bounded line transport for registry proof differential tests.
    Fields are space separated, with the 40 sibling hex strings last.
    The common-index flag constructs a synthetic prepared record for
    testing the candidate adapter, not for authenticating signatures. -/
open Lean EthereumConsensus.SSZ

private def readNat (s : String) : Except String Nat :=
  if s.length > 20 then .error "parse_error"
  else match s.toNat? with
    | some n => .ok n
    | none => .error "parse_error"

private def readU64 (s : String) : Except String UInt64 := do
  let n ← readNat s
  if n ≥ 2 ^ 64 then throw "out_of_range"
  return UInt64.ofNat n

private def nibble (b : UInt8) : Except String UInt8 :=
  if 48 ≤ b && b ≤ 57 then .ok (b - 48)
  else if 97 ≤ b && b ≤ 102 then .ok (b - 97 + 10)
  else .error "invalid_hex"

private def readHex (s : String) : Except String ByteArray := do
  let bytes := s.toUTF8
  if bytes.size % 2 != 0 || bytes.size > 128 then throw "invalid_hex"
  let mut out := ByteArray.empty
  for i in [:bytes.size / 2] do
    let high ← nibble bytes[2*i]!
    let low ← nibble bytes[2*i+1]!
    out := out.push (16 * high + low)
  return out

private def readFlag : String → Except String Bool
  | "0" => .ok false
  | "1" => .ok true
  | _ => .error "parse_error"

private def errorName : RegistryError → String
  | .publicKeyWidth => "public_key_width"
  | .credentialsWidth => "credentials_width"
  | .basicRoot => "basic_root"
  | .registryLength => "registry_length"
  | .indexOutside => "index_outside"
  | .branchLength => "branch_length"
  | .proof .chunkWidth => "chunk_width"
  | .proof _ => "proof_error"
  | .notCommon => "not_common"

private def dispatch : List String → Except String String
  | op :: count :: idx :: ep :: common :: key :: cred :: balance :: slashed ::
      eligible :: activation :: exit :: withdrawable :: root :: rest => do
    let length ← readNat count
    let index ← readU64 idx
    let epoch ← readU64 ep
    let included ← readFlag common
    let publicKey ← readHex key
    let credentials ← readHex cred
    let effectiveBalance ← readU64 balance
    let isSlashed ← readFlag slashed
    let eligibilityEpoch ← readU64 eligible
    let activationEpoch ← readU64 activation
    let exitEpoch ← readU64 exit
    let withdrawableEpoch ← readU64 withdrawable
    let v : RegistryValidator := {
      publicKey := publicKey
      withdrawalCredentials := credentials
      effectiveBalance := effectiveBalance
      slashed := isSlashed
      activationEligibilityEpoch := eligibilityEpoch
      activationEpoch := activationEpoch
      exitEpoch := exitEpoch
      withdrawableEpoch := withdrawableEpoch }
    let expected ← readHex root
    let siblings ← rest.mapM readHex
    if op == "root" then
      let leaf ← (validatorRoot v).mapError errorName
      return L4Factoidal.Crypto.bytesToHex leaf.bytes
    else if op == "proof" then
      let proof ← (verifyValidatorAt length index.toNat v siblings expected).mapError errorName
      return (if proof.matchesRoot then "match " else "mismatch ") ++
        L4Factoidal.Crypto.bytesToHex proof.root.bytes
    else if op == "candidate" then
      let zero ← (containerZeroRoot).mapError (fun _ => "basic_root")
      let prepared : PreparedAttesterSlashing := {
        commonIndices := if included then [index] else []
        firstSigningRoot := zero
        secondSigningRoot := zero }
      let verdict ← (checkCommonValidator prepared epoch index length v siblings expected).mapError errorName
      return match verdict with
        | .rootMismatch => "root_mismatch"
        | .notSlashable => "not_slashable"
        | .candidateNotAuthenticated => "candidate_not_authenticated"
    else throw "unknown_operation"
  | _ => .error "parse_error"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 4096 then .error "resource_limit"
      else dispatch (line.trimAscii.toString.splitOn " ")
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
