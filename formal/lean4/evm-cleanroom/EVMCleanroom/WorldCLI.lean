import EVMCleanroom.CallOpcode
import EVMCleanroom.CLIEncoding

/-!
# Multi-account world entry point for differential tests

`evm-subset --world ARGS` and `evm-subset --world-batch FILE` run one entry
frame through the actual world-aware dispatcher (`CallOpcode.executeAtDepth`
and `CallOpcode.settle`) over a small, explicitly listed account set, and
print one JSON object per case. This is a test adapter: it authenticates no
state, and every unlisted account is the empty account.

Arguments, separated by single spaces (a batch file has one case per line):

    PROFILE GAS FUEL FLAGS BLOCKNUMBER BLOCKHASHES ENTRY PREWARM OBSERVE ACCOUNT...

* `PROFILE`: `shanghaiPlus`, `cancunPlus` or `osaka`.
* `FLAGS`: 1 for a static entry frame, plus 2 to apply the transaction-end
  deletion of SELFDESTRUCT-registered accounts (`SelfDestruct.destroyRegistered`,
  the function `CallTransaction.settleFrame` applies) to a successful outcome.
* `BLOCKHASHES`: comma-separated hex hashes, oldest first (or `-`).
* `ENTRY`: hex address of the executing account, optionally `ADDR@DEPTH` with a
  decimal entry call depth (default 0, at most 1024); the caller and origin are 0xc2.
* `PREWARM`, `OBSERVE`: comma-separated hex addresses (or `-`).
* `ACCOUNT`: `ADDR:BALANCE:NONCE:CODE[:HASSTORAGE[:K=V;K=V...[:CREATED]]]`, with
  hex address, code, keys and values, decimal balance and nonce. `CREATED` 1
  marks the account as created in this transaction (EIP-6780) for tests.

For every observed address the output gives balance, nonce, code, the first
four storage slots, the first two transient slots, warmth, the EIP-6780
created flag and whether SELFDESTRUCT registered it for deletion (as it was
before any requested transaction-end deletion).
-/

namespace EVMCleanroom.WorldCLI

open EVMCleanroom.World
open EVMCleanroom.CLI

private def hexNat? (s : String) : Option Nat :=
  let cs := match s.toList with
    | '0' :: 'x' :: rest => rest
    | other => other
  if cs.isEmpty then none
  else cs.foldl (fun acc c => acc.bind fun n =>
    let d := c.toNat
    if 48 ≤ d ∧ d ≤ 57 then some (16 * n + (d - 48))
    else if 97 ≤ d ∧ d ≤ 102 then some (16 * n + (d - 87))
    else if 65 ≤ d ∧ d ≤ 70 then some (16 * n + (d - 55))
    else none) (some 0)

private def hexList? (s : String) : Option (List Nat) :=
  if s == "-" then some [] else (s.splitOn ",").mapM hexNat?

private def parseProfile : String → Option Profile
  | "shanghaiPlus" => some .shanghaiPlus
  | "cancunPlus" => some .cancunPlus
  | "osaka" => some .osaka
  | _ => none

private def parseEntry (s : String) : Option (Nat × Nat) :=
  match s.splitOn "@" with
  | [a] => (hexNat? a).map (·, 0)
  | [a, d] => do
    let address ← hexNat? a
    let depth ← d.toNat?
    if depth > CallOpcode.maxDepth then none else pure (address, depth)
  | _ => none

private structure Spec where
  address : Nat
  account : Account
  created : Bool := false

private def parseSlots (s : String) : Option (List (Nat × Nat)) :=
  if s.isEmpty || s == "-" then some []
  else (s.splitOn ";").mapM fun entry =>
    match entry.splitOn "=" with
    | [k, v] => do let key ← hexNat? k; let value ← hexNat? v; pure (key, value)
    | _ => none

private def parseAccount (s : String) : Option Spec := do
  let fields := s.splitOn ":"
  let address ← hexNat? (fields.getD 0 "")
  let balance ← (fields.getD 1 "").toNat?
  let nonce ← (fields.getD 2 "").toNat?
  let code ← match parseBytecode (fields.getD 3 "") with
    | .ok c => some c
    | .error _ => none
  let hasStorage := fields.getD 4 "0" == "1"
  let slots ← parseSlots (fields.getD 5 "")
  if address ≥ addressBound || balance ≥ modulus || nonce ≥ 2 ^ 64 then none
  else
    let storage := fun key => ((slots.find? (·.1 == key)).map (·.2)).getD 0
    pure ⟨address, { balance, nonce, code, storage, hasStorage := hasStorage || slots.any (·.2 != 0) },
      fields.getD 6 "0" == "1"⟩

private def boolJSON (b : Bool) : String := if b then "true" else "false"

private def accountJSON (registered : List Nat) (w : TxWorld) (address : Nat) : String :=
  let a := w.accounts address
  "{\"address\":\"" ++ toString address ++
  "\",\"balance\":\"" ++ toString a.balance ++
  "\",\"nonce\":\"" ++ toString a.nonce ++
  "\",\"codeHex\":\"" ++ hexBytes (a.code.extract 0 4096) ++
  "\",\"codeSize\":\"" ++ toString a.code.size ++
  "\",\"storage\":[" ++ String.intercalate "," ((List.range 4).map fun k => "\"" ++ toString (a.storage k) ++ "\"") ++
  "],\"transient\":[" ++ String.intercalate "," ((List.range 2).map fun k => "\"" ++ toString (w.transient address k) ++ "\"") ++
  "],\"warm\":" ++ boolJSON (w.warmAddresses address) ++
  ",\"created\":" ++ boolJSON (w.created address) ++
  ",\"selfDestructed\":" ++ boolJSON (registered.contains address) ++ "}"

private def stackJSON (s : State) : String :=
  "[" ++ String.intercalate "," (s.stack.items.map (fun w => "\"" ++ toString w.val ++ "\"")) ++ "]"

private def viewHex (v : ByteView) : String :=
  exactViewHex { v with size := min v.size 4096 }

private def outcomeJSON (observe : List Nat) (status : String) (frameWorld : TxWorld) (s : State)
    (reason : Option Error) (destroy : Bool := false) : String :=
  let w := if destroy then SelfDestruct.destroyRegistered frameWorld else frameWorld
  "{\"schemaVersion\":1,\"status\":\"" ++ status ++
  "\",\"gasRemaining\":\"" ++ toString s.gas ++
  "\",\"stack\":" ++ stackJSON s ++
  ",\"returnDataHex\":\"" ++ viewHex s.returnData ++
  "\",\"returnBytesHex\":\"" ++ viewHex s.outputData ++
  "\",\"memorySize\":\"" ++ toString (32 * s.memory.words) ++
  "\",\"memoryHex\":\"" ++ viewHex (ByteView.ofMemory s.memory 0 (32 * s.memory.words)) ++
  "\",\"refund\":\"" ++ toString w.refund ++
  "\",\"logs\":\"" ++ toString w.logsRev.length ++
  "\"" ++ (match reason with | some e => ",\"reason\":\"" ++ errorCode e ++ "\"" | none => "") ++
  ",\"accounts\":[" ++ String.intercalate "," (observe.map (accountJSON frameWorld.toDelete w)) ++ "]}"

def runCase (acceptance : Option Keccak.Acceptance) (args : List String) : String :=
  match args with
  | profileStr :: gasStr :: fuelStr :: readOnlyStr :: numberStr :: hashesStr :: entryStr ::
      prewarmStr :: observeStr :: accountStrs =>
    match parseProfile profileStr, gasStr.toNat?, fuelStr.toNat?, readOnlyStr.toNat?,
      numberStr.toNat?, hexList? hashesStr, parseEntry entryStr, hexList? prewarmStr,
      hexList? observeStr, accountStrs.mapM parseAccount with
    | some profile, some gas, some fuel, some flags, some number, some hashes, some (entry, depth),
        some prewarm, some observe, some specs =>
      if fuel > 1000000 || gas > 1000000000 || flags > 3 || specs.length > 64 || hashes.length > 256 then
        "{\"status\":\"inputError\",\"reason\":\"world-case-out-of-range\"}"
      else
        let accounts : Nat → Account := fun address =>
          ((specs.find? (·.address == address)).map (·.account)).getD {}
        let base := beginTransaction accounts
        let world : TxWorld := { base with
          keccakAcceptance := acceptance
          blockNumber := number
          blockHashes := hashes.toArray
          warmAddresses := fun a => base.warmAddresses a || prewarm.contains a
          created := fun a => specs.any (fun spec => spec.created && spec.address == a) }
        let initial := { frameInput world entry gas (flags % 2 == 1) profile 0xc2 0xc2 with
          blockNumber := number }
        match CallOpcode.settle world initial (CallOpcode.executeAtDepth fuel world entry depth initial) with
        | .stopped w s => outcomeJSON observe "stopped" w s none (flags / 2 % 2 == 1)
        | .returned w s => outcomeJSON observe "returned" w s none (flags / 2 % 2 == 1)
        | .reverted w s => outcomeJSON observe "reverted" w s none
        | .exceptional w s e => outcomeJSON observe "exceptional" w s (some e)
        | .indeterminate e => "{\"status\":\"indeterminate\",\"reason\":\"" ++ errorCode e ++ "\"}"
    | _, _, _, _, _, _, _, _, _, _ => "{\"status\":\"inputError\",\"reason\":\"bad-world-field\"}"
  | _ => "{\"status\":\"inputError\",\"reason\":\"expected PROFILE GAS FUEL READONLY BLOCKNUMBER BLOCKHASHES ENTRY PREWARM OBSERVE ACCOUNT...\"}"

def worldMain (acceptance : Option Keccak.Acceptance) (args : List String) : IO UInt32 := do
  IO.println (runCase acceptance args)
  return 0

def worldBatchMain (acceptance : Option Keccak.Acceptance) (path : String) : IO UInt32 := do
  let text ← IO.FS.readFile path
  for line in text.splitOn "\n" do
    let fields := (line.splitOn " ").filter (· ≠ "")
    unless fields.isEmpty do
      IO.println (runCase acceptance fields)
  return 0

end EVMCleanroom.WorldCLI
