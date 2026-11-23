import EVMCleanroom.HeaderRLP
import EVMCleanroom.CLIEncoding

namespace EVMCleanroom.HeaderRLPCLI
open EVMCleanroom.HeaderRLP

private def reason : Error → String
  | .unsupportedLayout => "unsupported-layout"
  | .invalidShape => "invalid-shape"
  | .laterFork => "later-fork"
  | .wrongForkShape => "wrong-fork-shape"
  | .chain .earlierFork => "earlier-fork"
  | .chain .resourceLimit => "resource-limit"
  | .chain .numberMismatch => "number-mismatch"
  | .chain .timestampMismatch => "timestamp-mismatch"
  | .chain .parentHashMismatch => "parent-hash-mismatch"
  | .chain (.fee _) => "fee-check"

private def indeterminate : Error → Bool
  | .unsupportedLayout | .laterFork | .chain .earlierFork | .chain .resourceLimit
  | .chain (.fee .resourceLimit) | .chain (.fee .missingParentFee) => true
  | _ => false

private def errorJson (e : Error) : String :=
  "{\"status\":\"" ++ (if indeterminate e then "indeterminate" else "error") ++
    "\",\"reason\":\"" ++ reason e ++ "\"}"

private def parseFields (fields : List String) : Except String Fields := do
  if fields.length > 24 then throw "too-many-fields"
  let bytes ← fields.mapM fun f =>
    if f.length > 514 then .error "field-limit"
    else EVMCleanroom.CLI.parseBytecode f
  return bytes.toArray

private def emit (a : EVMCleanroom.Keccak.Acceptance) (line : String) :
    Except String String := do
  match line.splitOn "|" with
  | [one] =>
    match one.splitOn "\t" with
    | "H" :: fields =>
      let h ← parseFields fields
      match hash a h with
      | .error e => return errorJson e
      | .ok (bytes, digest) =>
        return "{\"status\":\"ok\",\"wire\":\"" ++ EVMCleanroom.CLI.hexBytes bytes ++
          "\",\"hash\":\"" ++ toString digest ++ "\"}"
    | _ => throw "expected-hash-request"
  | [first, second] =>
    match first.splitOn "\t" with
    | "P" :: fields =>
      let p ← parseFields fields
      let c ← parseFields (second.splitOn "\t")
      match checkPair a p c with
      | .error e => return errorJson e
      | .ok fee => return "{\"status\":\"ok\",\"fee\":\"" ++ toString fee ++ "\"}"
    | _ => throw "expected-pair-request"
  | _ => throw "expected-one-or-two-headers"

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--dangerously-enable-unverified-keccak", "--batch", path] =>
    let input ← IO.FS.readFile path
    let mut count := 0
    let mut bad := false
    for line in input.splitOn "\n" do
      if !line.isEmpty then
        count := count + 1
        if count > 10000 || line.length > 8192 then
          IO.println "{\"status\":\"inputError\"}"
          bad := true
          break
        match emit EVMCleanroom.Keccak.dangerouslyAcceptUnverified line with
        | .ok out => IO.println out
        | .error _ => IO.println "{\"status\":\"inputError\"}"; bad := true
    return if bad || count == 0 then 2 else 0
  | _ => return 2

end EVMCleanroom.HeaderRLPCLI

def main (args : List String) : IO UInt32 := EVMCleanroom.HeaderRLPCLI.run args
