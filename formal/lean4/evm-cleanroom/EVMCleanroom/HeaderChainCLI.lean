import EVMCleanroom.HeaderChain

namespace EVMCleanroom.HeaderChainCLI
open EVMCleanroom.HeaderChain

private def reason : Error → String
  | .earlierFork => "earlier-fork"
  | .resourceLimit => "resource-limit"
  | .numberMismatch => "number-mismatch"
  | .timestampMismatch => "timestamp-mismatch"
  | .parentHashMismatch => "parent-hash-mismatch"
  | .fee .resourceLimit => "resource-limit"
  | .fee .parentGasOverLimit => "parent-gas-exceeds-limit"
  | .fee .childGasOverLimit => "child-gas-exceeds-limit"
  | .fee .invalidGasLimit => "invalid-gas-limit"
  | .fee .unexpectedParentFee => "unexpected-parent-fee"
  | .fee .missingParentFee => "missing-parent-fee"
  | .fee .incorrectBaseFee => "incorrect-base-fee"

private def indeterminate : Error → Bool
  | .earlierFork | .resourceLimit | .fee .resourceLimit | .fee .missingParentFee => true
  | _ => false

private def parseNat (s : String) : Except String Nat :=
  if s.isEmpty || s.length > 79 then .error "invalid-decimal"
  else if !s.toList.all (fun c => c >= '0' && c <= '9') then .error "invalid-decimal"
  else match s.toNat? with
    | none => .error "invalid-decimal"
    | some n => .ok n

private def parseFee (s : String) : Except String (Option Nat) :=
  if s == "-" then .ok none else do return some (← parseNat s)

private def parse (line : String) : Except String Pair := do
  match line.splitOn "\t" with
  | [pn, pt, ph, pl, pu, pf, cn, ct, ch, cl, cu, cf] =>
    return { parentNumber := ← parseNat pn, parentTimestamp := ← parseNat pt,
      parentHash := ← parseNat ph, parentGasLimit := ← parseNat pl,
      parentGasUsed := ← parseNat pu, parentBaseFee := ← parseFee pf,
      childNumber := ← parseNat cn, childTimestamp := ← parseNat ct,
      childParentHash := ← parseNat ch, childGasLimit := ← parseNat cl,
      childGasUsed := ← parseNat cu, childBaseFee := ← parseNat cf }
  | _ => throw "expected-twelve-fields"

private def emit (p : Pair) : IO Unit :=
  match check p with
  | .ok fee => IO.println ("{\"status\":\"ok\",\"expectedBaseFee\":\"" ++ toString fee ++ "\"}")
  | .error e =>
    IO.println ("{\"status\":\"" ++ (if indeterminate e then "indeterminate" else "error") ++
      "\",\"reason\":\"" ++ reason e ++ "\"}")

def run (args : List String) : IO UInt32 := do
  match args with
  | ["--batch", path] =>
    let input ← IO.FS.readFile path
    let mut count := 0
    let mut bad := false
    for line in input.splitOn "\n" do
      if !line.isEmpty then
        count := count + 1
        if count > 10000 || line.length > 1024 then
          IO.println "{\"status\":\"inputError\",\"reason\":\"resource-limit\"}"
          bad := true
          break
        match parse line with
        | .ok p => emit p
        | .error e =>
          IO.println ("{\"status\":\"inputError\",\"reason\":\"" ++ e ++ "\"}")
          bad := true
    return if bad || count == 0 then 2 else 0
  | fields =>
    match parse (String.intercalate "\t" fields) with
    | .ok p => emit p; return 0
    | .error e =>
      IO.println ("{\"status\":\"inputError\",\"reason\":\"" ++ e ++ "\"}")
      return 2

end EVMCleanroom.HeaderChainCLI

def main (args : List String) : IO UInt32 := EVMCleanroom.HeaderChainCLI.run args
