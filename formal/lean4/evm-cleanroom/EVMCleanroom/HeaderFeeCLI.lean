import EVMCleanroom.HeaderFees

/-! Minimal byte-transport CLI for actual independent Lean header admission.
Record format: FIRST(0/1) TAB PARENT_LIMIT TAB PARENT_USED TAB PARENT_FEE(or -)
 TAB CHILD_LIMIT TAB CHILD_USED TAB CLAIMED_FEE.
All numbers are unsigned decimal. The host does not calculate fees.
-/

namespace EVMCleanroom.HeaderFeeCLI

open EVMCleanroom.HeaderFees

private def reason : Error → String
  | .resourceLimit => "resource-limit"
  | .parentGasOverLimit => "parent-gas-exceeds-limit"
  | .childGasOverLimit => "child-gas-exceeds-limit"
  | .invalidGasLimit => "invalid-gas-limit"
  | .unexpectedParentFee => "unexpected-parent-fee"
  | .missingParentFee => "missing-parent-fee"
  | .incorrectBaseFee => "incorrect-base-fee"

private def parseNat (text : String) : Except String Nat :=
  if text.isEmpty || text.length > 79 then .error "invalid-decimal"
  else if !text.toList.all (fun c => c >= '0' && c <= '9') then .error "invalid-decimal"
  else match text.toNat? with
    | some n => .ok n
    | none => .error "invalid-decimal"

private def parseParentFee (text : String) : Except String (Option Nat) :=
  if text == "-" then .ok none
  else do
    let n ← parseNat text
    return some n

private def parseLine (line : String) : Except String Input := do
  match line.splitOn "\t" with
  | [mode, parentLimit, parentUsed, parentFee, childLimit, childUsed, childFee] =>
    if mode != "0" && mode != "1" then
      throw "invalid-mode"
    let parentGasLimit ← parseNat parentLimit
    let parentGasUsed ← parseNat parentUsed
    let parentBaseFee ← parseParentFee parentFee
    let childGasLimit ← parseNat childLimit
    let childGasUsed ← parseNat childUsed
    let childBaseFee ← parseNat childFee
    return {
      firstLondon := mode == "1"
      parentGasLimit := parentGasLimit
      parentGasUsed := parentGasUsed
      parentBaseFee := parentBaseFee
      childGasLimit := childGasLimit
      childGasUsed := childGasUsed
      childBaseFee := childBaseFee
    }
  | _ => throw "expected-seven-fields"

private def emit (input : Input) : IO Unit :=
  match checkHeader input with
  | .ok expected =>
      IO.println ("{\"status\":\"ok\",\"expectedBaseFee\":\"" ++ toString expected ++ "\"}")
  | .error reasonCode =>
      let status := if reasonCode == .resourceLimit || reasonCode == .missingParentFee
        then "indeterminate" else "error"
      IO.println ("{\"status\":\"" ++ status ++ "\",\"reason\":\"" ++
        reason reasonCode ++ "\"}")

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--batch", path] =>
    let source ← IO.FS.readFile path
    let mut count : Nat := 0
    let mut malformed := false
    for line in source.splitOn "\n" do
      if !line.isEmpty then
        count := count + 1
        if count > 10000 || line.length > 512 then
          IO.println "{\"status\":\"inputError\",\"reason\":\"resource-limit\"}"
          malformed := true
        else
          match parseLine line with
          | .error error =>
              IO.println ("{\"status\":\"inputError\",\"reason\":\"" ++ error ++ "\"}")
              malformed := true
          | .ok input => emit input
    if malformed || count == 0 then return 2 else return 0
  | fields =>
    match parseLine (String.intercalate "\t" fields) with
    | .ok input => emit input; return 0
    | .error error =>
        IO.println ("{\"status\":\"inputError\",\"reason\":\"" ++ error ++ "\"}")
        return 2

end EVMCleanroom.HeaderFeeCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.HeaderFeeCLI.run args
