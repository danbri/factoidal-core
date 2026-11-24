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

private def signingErrorName : StateSigningError → String
  | .forkWidth => "fork_width"
  | .basicRoot => "basic_root"
  | .branchLength => "branch_length"
  | .proof .chunkWidth => "chunk_width"
  | .proof _ => "proof_error"
  | .forkMismatch => "fork_mismatch"
  | .genesisMismatch => "genesis_mismatch"
  | .preparation .resourceLimit => "resource_limit"
  | .preparation .badIndices => "bad_indices"
  | .preparation .notConflicting => "not_conflicting"
  | .preparation .noCommonIndices => "no_common_indices"
  | .preparation .signing _ => "signing_error"
  | .registry e => errorName e

private def slotVerdictName : MainnetSlotCandidateVerdict → String
  | .slotRootMismatch => "slot_root_mismatch"
  | .stateVerdict .stateRootMismatch => "state_root_mismatch"
  | .stateVerdict (.registryVerdict .rootMismatch) => "root_mismatch"
  | .stateVerdict (.registryVerdict .notSlashable) => "not_slashable"
  | .stateVerdict (.registryVerdict .candidateNotAuthenticated) => "candidate_not_authenticated"

private def readVote : List String → Except String AttestationData
  | [slot, idx, beacon, sourceEp, source, targetEp, target] => do
    let s ← readU64 slot
    let i ← readU64 idx
    let b ← readHex beacon
    let se ← readU64 sourceEp
    let sr ← readHex source
    let te ← readU64 targetEp
    let tr ← readHex target
    (checkedAttestationData s i b se sr te tr).mapError (fun _ => "vote_width")
  | _ => .error "parse_error"

private def readIndices (s : String) : Except String (List UInt64) :=
  if s == "-" then .ok [] else (s.splitOn ",").mapM readU64

private def dispatchStateVotes (slot index : UInt64) (length : Nat)
    (v : RegistryValidator) (registryRoot : ByteArray) (rest : List String) :
    Except String String := do
  let depth := registryStateDepth (mainnetRegistryLayout slot)
  let proofCount := 41 + 4 * depth
  if rest.length ≠ proofCount + 20 then throw "branch_length"
  let siblings ← (rest.take proofCount).mapM readHex
  let stateRoot ← match siblings.drop 40 with
    | root :: _ => .ok root
    | [] => .error "branch_length"
  match rest.drop proofCount with
  | prev :: curr :: activation :: genesis :: tail => do
    let prevVersion ← readHex prev
    let currVersion ← readHex curr
    let activationEpoch ← readU64 activation
    let genesisRoot ← readHex genesis
    let context : ForkContext := {
      previousVersion := prevVersion
      currentVersion := currVersion
      activationEpoch := activationEpoch
      genesisValidatorsRoot := genesisRoot }
    let a ← readVote (tail.take 7)
    let b ← readVote ((tail.drop 7).take 7)
    match tail.drop 14 with
    | [leftText, rightText] => do
      let left ← readIndices leftText
      let right ← readIndices rightText
      let result ← (checkStateVotes slot context a b left right index length v
        (siblings.take 40) registryRoot ((siblings.drop 41).take depth)
        ((siblings.drop (41 + depth)).take depth)
        ((siblings.drop (41 + 2 * depth)).take depth)
        (siblings.drop (41 + 3 * depth)) stateRoot).mapError signingErrorName
      return slotVerdictName result.2 ++ " " ++
        L4Factoidal.Crypto.bytesToHex result.1.firstSigningRoot.bytes ++ " " ++
        L4Factoidal.Crypto.bytesToHex result.1.secondSigningRoot.bytes
    | _ => throw "parse_error"
  | _ => throw "parse_error"

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
    if op == "fullstate" then
      if included then throw "parse_error"
      let value ← dispatchStateVotes epoch index length v expected rest
      return value
    let siblings ← rest.mapM readHex
    if op == "root" then
      let leaf ← (validatorRoot v).mapError errorName
      return L4Factoidal.Crypto.bytesToHex leaf.bytes
    else if op == "proof" then
      let proof ← (verifyValidatorAt length index.toNat v siblings expected).mapError errorName
      return (if proof.matchesRoot then "match " else "mismatch ") ++
        L4Factoidal.Crypto.bytesToHex proof.root.bytes
    else if op == "slotstate" then
      -- For this operation the wire's ep field is a slot, not an epoch.
      let depth := registryStateDepth (mainnetRegistryLayout epoch)
      if siblings.length ≠ 41 + 2 * depth then throw "branch_length"
      let stateRoot ← match siblings.drop 40 with
        | root :: _ => .ok root
        | [] => .error "branch_length"
      let zero ← containerZeroRoot.mapError (fun _ => "basic_root")
      let prepared : PreparedAttesterSlashing := {
        commonIndices := if included then [index] else []
        firstSigningRoot := zero
        secondSigningRoot := zero }
      let verdict ← (checkMainnetSlotCommonValidator epoch prepared index length v
        (siblings.take 40) expected ((siblings.drop 41).take depth)
        (siblings.drop (41 + depth)) stateRoot).mapError errorName
      return match verdict with
        | .slotRootMismatch => "slot_root_mismatch"
        | .stateVerdict .stateRootMismatch => "state_root_mismatch"
        | .stateVerdict (.registryVerdict .rootMismatch) => "root_mismatch"
        | .stateVerdict (.registryVerdict .notSlashable) => "not_slashable"
        | .stateVerdict (.registryVerdict .candidateNotAuthenticated) => "candidate_not_authenticated"
    else if op == "state32" || op == "state64" then
      let layout : RegistryStateLayout := if op == "state32" then .phase0Deneb else .electraFulu
      if siblings.length ≠ 41 + registryStateDepth layout then throw "branch_length"
      let stateRoot ← match siblings.drop 40 with
        | root :: _ => .ok root
        | [] => .error "branch_length"
      let zero ← (containerZeroRoot).mapError (fun _ => "basic_root")
      let prepared : PreparedAttesterSlashing := {
        commonIndices := if included then [index] else []
        firstSigningRoot := zero
        secondSigningRoot := zero }
      let verdict ← (checkStateCommonValidator layout prepared epoch index length v
        (siblings.take 40) expected (siblings.drop 41) stateRoot).mapError errorName
      return match verdict with
        | .stateRootMismatch => "state_root_mismatch"
        | .registryVerdict .rootMismatch => "root_mismatch"
        | .registryVerdict .notSlashable => "not_slashable"
        | .registryVerdict .candidateNotAuthenticated => "candidate_not_authenticated"
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
    let limit := if line.startsWith "fullstate " then 8192 else 4096
    let result := if line.utf8ByteSize > limit then .error "resource_limit"
      else dispatch (line.trimAscii.toString.splitOn " ")
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
