import EVMCleanroom.IdentityPrecompile
import EVMCleanroom.CLIEncoding

/-!
# Direct identity-precompile test executable

`evm-identity-precompile HEX GAS MAX_BYTES` or
`evm-identity-precompile --batch RECORDS.tsv`.
Each batch record is HEX<TAB>GAS<TAB>MAX_BYTES and produces one JSON line.
All semantic decisions and output bytes come from Lean. The host only
transports text. MAX_BYTES is an explicit experimental resource budget.
This is not the CALL-family EVM dispatcher or a transaction simulator.
-/

namespace EVMCleanroom.IdentityCLI

open EVMCleanroom.CLI

private def render (fields : List String) : Option String :=
  match fields with
  | [hex, gasText, maxText] =>
    match parseBytecode hex, gasText.toNat?, maxText.toNat? with
    | .ok input, some gas, some maxBytes =>
      match IdentityPrecompile.execute maxBytes gas input with
      | .ok (output, remaining) =>
        some ("{\"status\":\"ok\",\"dataHex\":\"" ++ hexBytes output ++
          "\",\"gasRemaining\":\"" ++ toString remaining ++
          "\",\"gasUsed\":\"" ++ toString (IdentityPrecompile.gasCost input.size) ++ "\"}")
      | .error .resourceLimit =>
        some "{\"status\":\"indeterminate\",\"reason\":\"resourceLimit\"}"
      | .error .outOfGas =>
        some "{\"status\":\"exceptional\",\"reason\":\"outOfGas\"}"
      | .error _ =>
        some "{\"status\":\"indeterminate\",\"reason\":\"unhandledError\"}"
    | _, _, _ => none
  | _ => none

private def inputError : String :=
  "{\"status\":\"inputError\",\"reason\":\"expected HEX GAS MAX_BYTES\"}"

/-- Native independent precompile test and batch interface.
    A malformed batch row is not counted as a successful execution result. -/
def cliMain (args : List String) : IO UInt32 := do
  match args with
  | ["--batch", path] =>
    let source ← IO.FS.readFile path
    let mut count : Nat := 0
    let mut malformed : Nat := 0
    for line in source.splitOn "\n" do
      if line != "" then
        count := count + 1
        match render (line.splitOn "\t") with
        | some json => IO.println json
        | none =>
          malformed := malformed + 1
          IO.println inputError
    if count == 0 || malformed > 0 then return 2 else return 0
  | _ =>
    match render args with
    | some json =>
      IO.println json
      return 0
    | none =>
      IO.println inputError
      return 2

end EVMCleanroom.IdentityCLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.IdentityCLI.cliMain args
