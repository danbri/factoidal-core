import ProposerProjection
import Lean

/-! Bounded test transport. The protocol decision is in checkProposerState.
    Output is authenticated relative to the supplied commitment, never a canonical-state verdict. -/
open Lean EthereumConsensus.SSZ
open EthereumConsensus.SSZ.AuthenticatedProposer
open EthereumConsensus.BLS EthereumConsensus.BLS.Verify

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
  if bytes.size % 2 != 0 || bytes.size > 192 then throw "invalid_hex"
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
  | .preparation (.signing _) => "signing_error"
  | .registry e => errorName e

-- Check the nested error transport directly, including the defensive
-- signing-error arm that valid context admission normally prevents.
#guard signingErrorName (.preparation .resourceLimit) == "resource_limit"
#guard signingErrorName (.preparation .badIndices) == "bad_indices"
#guard signingErrorName (.preparation .notConflicting) == "not_conflicting"
#guard signingErrorName (.preparation .noCommonIndices) == "no_common_indices"
#guard signingErrorName (.preparation (.signing .domainTypeWidth)) == "signing_error"
#guard signingErrorName (.preparation (.signing .versionWidth)) == "signing_error"
#guard signingErrorName (.preparation (.signing (.container .rootWidth))) == "signing_error"


private def proposerErrorName : ProposerEvidenceError → String
  | .differentSlot => "different_slot"
  | .differentProposer => "different_proposer"
  | .identicalHeaders => "identical_headers"
  | .context e => signingErrorName e
  | .registry e => errorName e
  | .slotMismatch => "slot_mismatch"
  | .registryMismatch => "registry_mismatch"
  | .validatorMismatch => "validator_mismatch"
  | .notSlashable => "not_slashable"
  | .signing _ => "signing_error"

private def keyName : KeyError → String
  | .width => "key_width"
  | .notCompressed => "key_not_compressed"
  | .infinityKey => "key_infinity"
  | .nonCanonicalX => "key_noncanonical"
  | .notOnCurve => "key_curve"
  | .notSubgroup => "key_subgroup"

private def signatureName : G2.SignatureError → String
  | .width => "signature_width"
  | .notCompressed => "signature_not_compressed"
  | .infinitySignature => "signature_infinity"
  | .nonCanonicalX => "signature_noncanonical"
  | .notOnCurve => "signature_curve"
  | .notSubgroup => "signature_subgroup"

private def blsErrorName : VerifyError → String
  | .keyAdmission .resourceLimit => "resource_limit"
  | .keyAdmission .emptyKeys => "empty_keys"
  | .keyAdmission (.invalidKey e) => keyName e
  | .keyAdmission .infinitySum => "infinity_sum"
  | .keyAdmission .invalidSum => "internal_key_sum"
  | .signatureAdmission e => signatureName e
  | .hashFailure (.hashError .signingRootWidth) => "root_width"
  | .hashFailure _ => "hash_failure"
  | .hashInfinity => "hash_infinity"
  | .pairingFailure e => "pairing_failure " ++ e

private def authErrorName : AuthError → String
  | .preparation e => proposerErrorName e
  | .firstFailure e => "first_" ++ blsErrorName e
  | .secondFailure e => "second_" ++ blsErrorName e
  | .firstMismatch => "first_mismatch"
  | .secondMismatch => "second_mismatch"

private def readHeader : List String → Except String BeaconBlockHeader
  | [slot, index, parent, state, body] => do
    let s ← readU64 slot
    let i ← readU64 index
    let p ← readHex parent
    let t ← readHex state
    let b ← readHex body
    (checkedBeaconBlockHeader s i p t b).mapError (fun _ => "header_width")
  | _ => .error "parse_error"

private def dispatch (project : Bool) : List String → Except String String
  | sigA :: sigB :: slot :: count :: key :: cred :: balance :: slashed :: eligible :: activation ::
      exit :: withdrawable :: prev :: curr :: forkEpoch :: genesis :: registry ::
      state :: rest => do
    let sa ← readHex sigA
    let sb ← readHex sigB
    let currentSlot ← readU64 slot
    let length ← readNat count
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
    let previousVersion ← readHex prev
    let currentVersion ← readHex curr
    let forkActivation ← readU64 forkEpoch
    let genesisRoot ← readHex genesis
    let context : ForkContext := {
      previousVersion := previousVersion
      currentVersion := currentVersion
      activationEpoch := forkActivation
      genesisValidatorsRoot := genesisRoot }
    let registryRoot ← readHex registry
    let stateRoot ← readHex state
    let depth := registryStateDepth (mainnetRegistryLayout currentSlot)
    if rest.length ≠ 50 + 4 * depth then throw "branch_length"
    let a ← readHeader (rest.take 5)
    let b ← readHeader ((rest.drop 5).take 5)
    let siblings ← (rest.drop 10).mapM readHex
    if project then
      let q : EthereumConsensus.SSZ.ProposerProjection.ProjectionRequest := {
        slot := currentSlot, first := a, second := b, context := context
        length := length, validator := v, member := siblings.take 40
        registryRoot := registryRoot, registrySiblings := (siblings.drop 40).take depth
        slotSiblings := (siblings.drop (40 + depth)).take depth
        forkSiblings := (siblings.drop (40 + 2 * depth)).take depth
        genesisSiblings := siblings.drop (40 + 3 * depth)
        stateRoot := stateRoot, sigA := sa, sigB := sb }
      let projection ← (EthereumConsensus.SSZ.ProposerProjection.authenticateAndProject q).mapError
        (fun e => match e with
          | .authentication reason => authErrorName reason
          | .epochOverflow => "epoch_overflow"
          | .registry reason => errorName reason
          | .proof _ => "projection_proof_error")
      return "partial_validator_projection " ++
        toString projection.validator.withdrawableEpoch.toNat ++ " " ++
        L4Factoidal.Crypto.bytesToHex projection.projectedRegistryRoot.bytes ++ " " ++
        L4Factoidal.Crypto.bytesToHex projection.projectedStateRoot.bytes
    let result ← (authenticateState currentSlot a b context length v
      (siblings.take 40) registryRoot ((siblings.drop 40).take depth)
      ((siblings.drop (40 + depth)).take depth)
      ((siblings.drop (40 + 2 * depth)).take depth)
      (siblings.drop (40 + 3 * depth)) stateRoot sa sb).mapError authErrorName
    return "authenticated_relative_to_commitment " ++
      L4Factoidal.Crypto.bytesToHex result.publicKey ++ " " ++
      L4Factoidal.Crypto.bytesToHex result.firstSigningRoot.bytes ++ " " ++
      L4Factoidal.Crypto.bytesToHex result.secondSigningRoot.bytes
  | _ => .error "parse_error"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 8704 then .error "resource_limit"
      else match line.trimAscii.toString.splitOn " " with
        | "project" :: rest => dispatch true rest
        | rest => dispatch false rest
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
