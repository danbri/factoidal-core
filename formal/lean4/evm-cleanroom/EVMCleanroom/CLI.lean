import EVMCleanroom.Core

/-!
A minimal machine-readable entry point for the *restricted* EVM model.

Usage:
  lake exe evm-subset 600260030100 100 10

Arguments: hex bytecode (optional 0x prefix), initial gas, step fuel.
Successful execution prints one JSON line. Execution errors also print
JSON and exit zero; malformed invocation exits with code 2.

This is deliberately NOT a transaction replay API, and it does not validate
or interpret Ethereum transaction envelopes, account state, or post-state roots.
-/

namespace EVMCleanroom.CLI

private def nibble (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 65 + 10)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 97 + 10)
  else none

private def decodePairs : List Char → Array UInt8 → Except String (Array UInt8)
  | [], acc => .ok acc
  | [_], _ => .error "odd-length hex bytecode"
  | hi :: lo :: rest, acc =>
    match nibble hi, nibble lo with
    | some a, some b =>
      decodePairs rest (acc.push (UInt8.ofNat (16 * a + b)))
    | _, _ => .error "invalid hex bytecode"

def parseBytecode (s : String) : Except String (Array UInt8) :=
  match s.toList with
  | '0' :: 'x' :: cs => decodePairs cs #[]
  | '0' :: 'X' :: cs => decodePairs cs #[]
  | cs => decodePairs cs #[]

private def errorCode : EVMCleanroom.Error → String
  | .stackUnderflow => "stackUnderflow"
  | .stackOverflow => "stackOverflow"
  | .outOfGas => "outOfGas"
  | .invalidOpcode _ => "invalidOpcode"
  | .invalidJump _ => "invalidJump"
  | .alreadyHalted => "alreadyHalted"
  | .stepLimit => "stepLimit"

private def successJSON (s : EVMCleanroom.State) : String :=
  -- Decimal STRING encoding is essential: a JSON number would silently
  -- lose precision in JavaScript for EVM words above 2^53 - 1.
  let items := String.intercalate "," (s.stack.items.map (fun w => "\"" ++ toString w.val ++ "\""))
  "{\"schemaVersion\":2,\"status\":\"ok\",\"gasRemaining\":\"" ++ toString s.gas ++
  "\",\"pc\":\"" ++ toString s.pc ++
  "\",\"halted\":" ++ (if s.halted then "true" else "false") ++
  ",\"stack\":[" ++ items ++ "]" ++
  ",\"memorySizeBytes\":\"" ++ toString (32 * s.memory.words) ++
  "\",\"memoryWord0\":\"" ++ toString (s.memory.readWord 0) ++ "\"}"

private def errorJSON (e : EVMCleanroom.Error) : String :=
  "{\"status\":\"error\",\"error\":\"" ++ errorCode e ++ "\"}"

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, gasStr, fuelStr] =>
    match parseBytecode hex, gasStr.toNat?, fuelStr.toNat? with
    | .ok code, some gas, some fuel =>
      let s : EVMCleanroom.State := { code := code, gas := gas }
      match EVMCleanroom.run fuel s with
      | .ok out =>
        IO.println (successJSON out)
        return 0
      | .error e =>
        IO.println (errorJSON e)
        return 0
    | .error why, _, _ =>
      IO.println ("{\"status\":\"inputError\",\"message\":\"" ++ why ++ "\"}")
      return 2
    | _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"gas and fuel must be nonnegative integers\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"usage: evm-subset HEX GAS FUEL\"}"
    return 2

end EVMCleanroom.CLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.CLI.cliMain args
