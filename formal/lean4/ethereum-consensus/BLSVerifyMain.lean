import BLSVerify

open EthereumConsensus.BLS
open EthereumConsensus.BLS.Verify

private def nibble (b : UInt8) : Except String UInt8 :=
  if 48 ≤ b && b ≤ 57 then .ok (b-48)
  else if 97 ≤ b && b ≤ 102 then .ok (b-97+10)
  else .error "invalid_hex"

private def readHex (s : String) : Except String ByteArray := do
  if s = "-" then return ByteArray.empty
  let bytes := s.toUTF8
  if bytes.size % 2 != 0 || bytes.size > 256 then throw "invalid_hex"
  let mut out := ByteArray.empty
  for i in [:bytes.size / 2] do
    let hi ← nibble bytes[2*i]!
    let lo ← nibble bytes[2*i+1]!
    out := out.push (16*hi+lo)
  return out

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

private def errorName : VerifyError → String
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

private def dispatch (s : String) : Except String Bool := do
  match s.splitOn " " with
  | "verify" :: root :: sig :: keys =>
    if keys.length > maxAggregateKeys then throw "resource_limit"
    let rootBytes ← readHex root
    let sigBytes ← readHex sig
    let mut keyBytes : List ByteArray := []
    for key in keys do
      keyBytes := (← readHex key) :: keyBytes
    (verifySigningRoot keyBytes.reverse rootBytes sigBytes).mapError errorName
  | _ => throw "operation"

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 201000 then .error "resource_limit"
                  else dispatch line.trimAscii.toString
    output.putStrLn (match result with
      | .ok true => "ok true"
      | .ok false => "ok false"
      | .error error => "error " ++ error)
    output.flush
