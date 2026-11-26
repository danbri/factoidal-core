import EVMCleanroom.TransactionCodec

/-!
Machine-readable entry point for call transactions with a decoded envelope
and state witness already authenticated by a host. The shared JSON codec is
imported only by transaction executables, preserving lightweight bytecode startup.
-/

namespace EVMCleanroom.CLITransaction

open Lean (Json toJson)
open EVMCleanroom.TransactionCodec

private def callTransactionMain (path : String) (acceptance : Option Keccak.Acceptance := none) : IO UInt32 := do
  let inputError := fun message => Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("status", .str "inputError"),
    ("reason", .str message), ("keccakOptIn", .bool acceptance.isSome)]
  let input ← try
      let file ← IO.FS.Handle.mk path .read
      let cap := USize.ofNat (CallTransaction.maxDataBytes + 1)
      let bytes ← file.read cap
      if bytes.size > CallTransaction.maxDataBytes || !(← file.read 1).isEmpty then
        pure (.error "transaction input exceeds the observation limit")
      else
        match String.fromUTF8? bytes with
        | some text => pure (.ok text)
        | none => pure (.error "transaction input must be UTF-8")
    catch error => pure (.error error.toString)
  match input >>= parseJSON >>= (parseCallTransaction · acceptance) with
  | .ok request =>
    IO.println (transactionResponse request (CallTransaction.run request)).compress
    return 0
  | .error why =>
    IO.println (inputError why).compress
    return 2

def cliMain (args : List String) : IO UInt32 := do
  let (args, acceptance) := match args with
    | "--dangerously-enable-unverified-keccak" :: rest =>
      (rest, some Keccak.dangerouslyAcceptUnverified)
    | _ => (args, none)
  let args := match args with
    | "--observe-logs" :: rest => rest
    | _ => args
  match args with
  | ["--call-transaction", path] => callTransactionMain path acceptance
  | _ =>
    IO.println (Json.mkObj [("schemaVersion", toJson (1 : Nat)), ("status", .str "inputError"),
      ("reason", .str "usage: evm-call-transaction --call-transaction FILE"),
      ("keccakOptIn", .bool acceptance.isSome)]).compress
    return 2

end EVMCleanroom.CLITransaction

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.CLITransaction.cliMain args
