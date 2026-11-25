import AuthenticatedAttester
import Lean

/-! Bounded line transport for registry proof differential tests.
    Fields are space separated, with the 40 sibling hex strings last.
    The common-index flag constructs a synthetic prepared record for
    testing the candidate adapter, not for authenticating signatures. -/
open Lean EthereumConsensus.SSZ
open EthereumConsensus.SSZ.AuthenticatedAttester
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


private def allSignerErrorName : SignerError → String
  | .resourceLimit => "resource_limit"
  | .indexMismatch => "index_mismatch"
  | .rootMismatch => "signer_root_mismatch"
  | .registry e => errorName e
  | .context e => signingErrorName e
  | .preparation e => signingErrorName (.preparation e)
  | .slotMismatch => "slot_root_mismatch"
  | .stateMismatch => "state_root_mismatch"

private def readSignerRow : List String → Except String SignerWitness
  | idx :: key :: cred :: balance :: slashed :: eligible :: activation :: exit ::
      withdrawable :: tail => do
    if tail.length ≠ 40 then throw "branch_length"
    let i ← readU64 idx
    let k ← readHex key
    let c ← readHex cred
    let b ← readU64 balance
    let s ← readFlag slashed
    let e ← readU64 eligible
    let a ← readU64 activation
    let x ← readU64 exit
    let w ← readU64 withdrawable
    let ss ← tail.mapM readHex
    let v : RegistryValidator := {
      publicKey := k, withdrawalCredentials := c, effectiveBalance := b, slashed := s,
      activationEligibilityEpoch := e, activationEpoch := a, exitEpoch := x,
      withdrawableEpoch := w }
    return ⟨i, v, ss⟩
  | _ => .error "parse_error"

private def readSignerRows (n : Nat) (tokens : List String) : Except String (List SignerWitness) :=
  if n > slashingIndexLimit then .error "resource_limit"
  else if tokens.length ≠ n * 49 then .error "branch_length"
  else (List.range n).mapM (fun i => readSignerRow ((tokens.drop (i*49)).take 49))

private def keyListText (keys : List ByteArray) : String :=
  if keys.isEmpty then "-" else String.intercalate "," (keys.map L4Factoidal.Crypto.bytesToHex)

private def indexListText (indices : List UInt64) : String :=
  if indices.isEmpty then "-" else String.intercalate "," (indices.map (fun i => toString i.toNat))

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
  | .preparation e => allSignerErrorName e
  | .firstFailure e => "first_" ++ blsErrorName e
  | .secondFailure e => "second_" ++ blsErrorName e
  | .noEligible => "no_eligible"
  | .firstMismatch => "first_mismatch"
  | .secondMismatch => "second_mismatch"

private def dispatch : List String → Except String String
  | sigA :: sigB :: slotText :: countText :: rrText :: rootText :: rest => do
    let sa ← readHex sigA
    let sb ← readHex sigB
    let slot ← readU64 slotText
    let length ← readNat countText
    let rr ← readHex rrText
    let root ← readHex rootText
    let depth := registryStateDepth (mainnetRegistryLayout slot)
    let proofCount := 4 * depth
    if rest.length < proofCount + 22 then throw "branch_length"
    let ss ← (rest.take proofCount).mapM readHex
    match rest.drop proofCount with
    | prev :: curr :: activation :: genesis :: tail => do
      let pv ← readHex prev
      let cv ← readHex curr
      let ae ← readU64 activation
      let gr ← readHex genesis
      let c : ForkContext := {
        previousVersion := pv, currentVersion := cv, activationEpoch := ae,
        genesisValidatorsRoot := gr }
      let a ← readVote (tail.take 7)
      let b ← readVote ((tail.drop 7).take 7)
      match tail.drop 14 with
      | lt :: rt :: lc :: rc :: rows => do
        let left ← readIndices lt
        let right ← readIndices rt
        let ln ← readNat lc
        let rn ← readNat rc
        if ln > slashingIndexLimit ∨ rn > slashingIndexLimit then throw "resource_limit"
        let lw ← readSignerRows ln (rows.take (ln*49))
        let rw ← readSignerRows rn (rows.drop (ln*49))
        let result ← (authenticateState slot c a b left right lw rw length rr
          (ss.take depth) ((ss.drop depth).take depth)
          ((ss.drop (2*depth)).take depth) (ss.drop (3*depth)) root sa sb).mapError authErrorName
        return "authenticated_relative_to_commitment " ++
          L4Factoidal.Crypto.bytesToHex result.1.firstSigningRoot.bytes ++ " " ++
          L4Factoidal.Crypto.bytesToHex result.1.secondSigningRoot.bytes ++ " " ++
          keyListText result.2.firstKeys ++ " " ++ keyListText result.2.secondKeys ++ " " ++
          indexListText result.2.eligibleCommon
      | _ => throw "parse_error"
    | _ => throw "parse_error"
  | _ => .error "parse_error"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 263168 then .error "resource_limit"
      else dispatch (line.trimAscii.toString.splitOn " ")
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
