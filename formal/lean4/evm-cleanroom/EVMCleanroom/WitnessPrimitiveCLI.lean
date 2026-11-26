import EVMCleanroom.MPT
import EVMCleanroom.TransactionCodec
import EVMCleanroom.WitnessJSON

/-!
Bounded native transport for direct RLP and secure-trie checks. This executable
exercises the same parser/verifier used by authenticated transaction admission;
it does not provide a JavaScript or external-client implementation fallback.
-/
namespace EVMCleanroom.WitnessPrimitiveCLI

open Lean (Json toJson)
open TransactionCodec
open CLI (hexBytes parseBytecode)

def maxFileBytes : Nat := 2 * 1024 * 1024

private def report (status : String) (fields : List (String × Json)) (optIn : Bool) : Json :=
  Json.mkObj ([("schemaVersion", toJson (1 : Nat)), ("status", .str status),
    ("keccakOptIn", .bool optIn)] ++ fields)

private def refused (classification reason : String) (optIn : Bool) : Json :=
  report "refused" [("classification", .str classification), ("reason", .str reason)] optIn

private def rlpError (error : CanonicalRLP.Error) (optIn : Bool) : Json :=
  match error with
  | .malformed why => refused "invalid" why optIn
  | .resourceLimit => refused "resource" "rlp-resource-limit" optIn

private def fieldsOnly (value : Json) (allowed : List String) : Except String Unit := do
  let object ← value.getObj?
  for (name, _) in object.toList do
    if !allowed.contains name then throw ("unexpected field: " ++ name)

private def version (value : Json) : Except String Unit := do
  if (← (← value.getObjVal? "schemaVersion").getNat?) != 1 then
    throw "expected witness schema version 1"

private def rlpCheck (value : Json) (optIn : Bool) : Except String Json := do
  fieldsOnly value ["schemaVersion", "encoding", "integerBytes"]
  version value
  let encoded ← hexField value "encoding"
  let integerBytes ← match (value.getObjVal? "integerBytes").toOption with
    | none => pure none
    | some limit => some <$> limit.getNat?
  match CanonicalRLP.decode encoded with
  | .error error => return rlpError error optIn
  | .ok item =>
    let mut fields := [("isList", .bool item.isList), ("payloadHex", .str (hexBytes item.payload))]
    if item.isList then
      match CanonicalRLP.children item with
      | .error error => return rlpError error optIn
      | .ok items => fields := fields ++ [("children", .arr (items.map (fun i => .str (hexBytes i.encoded))))]
    match integerBytes with
    | none => pure ()
    | some width =>
      match CanonicalRLP.scalar item width with
      | .error error => return rlpError error optIn
      | .ok integer => fields := fields ++ [("integer", decimal integer)]
    return report "decoded" fields optIn

private def mptCheck (value : Json) (a : Keccak.Acceptance) : Except String Json := do
  fieldsOnly value ["schemaVersion", "root", "key", "proof"]
  version value
  let root ← hexField value "root"
  let key ← hexField value "key"
  let proofJSON ← (← value.getObjVal? "proof").getArr?
  -- The public verifier classifies count/node-size refusals. The entire file
  -- is already byte-bounded before parsing these strings into arrays.
  let proof ← proofJSON.mapM fun node => do parseBytecode (← node.getStr?)
  match MPT.lookup a root key proof with
  | .error .resourceLimit => return refused "resource" "mpt-resource-limit" true
  | .error (.invalidProof why) => return refused "invalid" why true
  | .ok none => return report "absent" [] true
  | .ok (some bytes) => return report "present" [("valueHex", .str (hexBytes bytes))] true

private def readFile (path : String) : IO (Except String String) := do
  try
    let file ← IO.FS.Handle.mk path .read
    let bytes ← file.read (USize.ofNat (maxFileBytes + 1))
    if bytes.size > maxFileBytes || !(← file.read 1).isEmpty then
      return .error "witness input exceeds the byte limit"
    match String.fromUTF8? bytes with
    | none => return .error "witness input must be UTF-8"
    | some text => return .ok text
  catch error => return .error error.toString

private def process (path : String) (optIn : Bool) (run : Json → Except String Json) : IO UInt32 := do
  let input ← readFile path
  match input >>= WitnessJSON.parse >>= run with
  | .error why =>
    IO.println (report "inputError" [("reason", .str why)] optIn).compress
    return 2
  | .ok result =>
    IO.println result.compress
    return 0

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--rlp", path] => process path false (fun input => rlpCheck input false)
  | ["--dangerously-enable-unverified-keccak", "--rlp", path] =>
      process path true (fun input => rlpCheck input true)
  | ["--dangerously-enable-unverified-keccak", "--mpt-proof", path] =>
      process path true (fun input => mptCheck input Keccak.dangerouslyAcceptUnverified)
  | ["--mpt-proof", _] =>
      IO.println (report "inputError" [("reason", .str "experimental Keccak opt-in required")] false).compress
      return 2
  | _ =>
      IO.println (report "inputError" [("reason", .str
        "usage: evm-witness-proof [--dangerously-enable-unverified-keccak] --rlp|--mpt-proof FILE")]
        (args.contains "--dangerously-enable-unverified-keccak")).compress
      return 2

end EVMCleanroom.WitnessPrimitiveCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.WitnessPrimitiveCLI.cliMain args
