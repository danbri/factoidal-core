import EVMCleanroom.Core
import EVMCleanroom.Frame
import EVMCleanroom.Call
import EVMCleanroom.CallOpcode
import EVMCleanroom.TxAccounting
import EVMCleanroom.PragueEnvelope

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
  | .writeProtection => "writeProtection"
  | .unsupportedFork => "unsupportedFork"
  | .stepLimit => "stepLimit"

/-- Bounded, lossless memory snapshot. The result records whether the snapshot
    covers ALL allocated memory, so callers cannot silently count truncated
    observations as a complete memory comparison. -/
private def hexDigit (n : Nat) : Char :=
  Char.ofNat (if n < 10 then 48 + n else 87 + n)

private def memoryHex (s : EVMCleanroom.State) (limit : Nat) : String :=
  let observed := min (32 * s.memory.words) limit
  String.ofList ((List.range observed).flatMap (fun address =>
    let b := (s.memory.readByte address).toNat
    [hexDigit (b / 16), hexDigit (b % 16)]))

private def successJSON (s : EVMCleanroom.State) : String :=
  -- Decimal STRING encoding is essential: a JSON number would silently
  -- lose precision in JavaScript for EVM words above 2^53 - 1.
  let items := String.intercalate "," (s.stack.items.map (fun w => "\"" ++ toString w.val ++ "\""))
  "{\"schemaVersion\":2,\"status\":\"ok\",\"gasRemaining\":\"" ++ toString s.gas ++
  "\",\"pc\":\"" ++ toString s.pc ++
  "\",\"halted\":" ++ (if s.halted then "true" else "false") ++
  ",\"stack\":[" ++ items ++ "]" ++
  ",\"memorySizeBytes\":\"" ++ toString (32 * s.memory.words) ++
  "\",\"memoryWord0\":\"" ++ toString (s.memory.readWord 0) ++
  "\",\"memoryObservedBytes\":\"" ++ toString (min (32 * s.memory.words) 4096) ++
  "\",\"memoryTruncated\":" ++ (if 4096 < 32 * s.memory.words then "true" else "false") ++
  ",\"memoryHex\":\"" ++ memoryHex s 4096 ++ "\"}"

private def errorJSON (e : EVMCleanroom.Error) : String :=
  "{\"status\":\"error\",\"error\":\"" ++ errorCode e ++ "\"}"

/-- Execute multiple independent cases in one Lean process. Each nonempty
    input line contains HEX, GAS, FUEL separated by TABs. The output has
    exactly one JSON result per input record, preserving input order. -/
private def runBatchFile (path : String) (profile : Profile := .shanghaiPlus) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let mut count : Nat := 0
  let mut malformed : Nat := 0
  for line in source.splitOn "\n" do
    if line != "" then
      count := count + 1
      let fields := line.splitOn "\t"
      match fields with
      | [hex, gasStr, fuelStr] =>
        match parseBytecode hex, gasStr.toNat?, fuelStr.toNat? with
        | .ok code, some gas, some fuel =>
          let s : EVMCleanroom.State := { code := code, gas := gas, profile := profile }
          match EVMCleanroom.run fuel s with
          | .ok out => IO.println (successJSON out)
          | .error e => IO.println (errorJSON e)
        | _, _, _ =>
          malformed := malformed + 1
          IO.println "{\"status\":\"inputError\",\"message\":\"invalid batch record\"}"
      | _ =>
        malformed := malformed + 1
        IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX<TAB>GAS<TAB>FUEL\"}"
  if count == 0 || malformed > 0 then return 2 else return 0

/-- Transaction fee and nonce results for the explicitly restricted
    EIP-7623 host. Numeric fields are decimal strings, not JS floats. -/
private def txFeeJSON (p : TxAccounting.Settlement) : String :=
  "{\"schemaVersion\":1,\"status\":\"ok\",\"intrinsicGas\":\"" ++
  toString p.intrinsic ++ "\",\"floorGas\":\"" ++ toString p.floor ++
  "\",\"chargedGas\":\"" ++ toString p.charged ++
  "\",\"effectivePrice\":\"" ++ toString p.price ++
  "\",\"senderAfterBalance\":\"" ++ toString p.senderAfterBalance ++
  "\",\"senderAfterNonce\":\"" ++ toString p.senderAfterNonce ++
  "\",\"minerReward\":\"" ++ toString p.minerReward ++
  "\",\"baseFeeBurn\":\"" ++ toString p.baseFeeBurn ++ "\"}"

/-- All arguments must be decimal nonnegative integers except MODE: 0
    means legacy/access-list gas price, 1 means EIP-1559 fee market. -/
private def txFeeMain (args : List String) : IO UInt32 := do
  match args with
  | [z, nz, a, keys, limit, cap, priority, base, balance, nonce, used, mode] =>
    if mode != "0" && mode != "1" then
      IO.println "{\"status\":\"inputError\",\"message\":\"mode must be 0 or 1\"}"
      return 2
    match z.toNat?, nz.toNat?, a.toNat?, keys.toNat?,
          limit.toNat?, cap.toNat?, priority.toNat?, base.toNat?,
          balance.toNat?, nonce.toNat?, used.toNat? with
    | some z, some nz, some a, some keys, some limit, some cap,
      some priority, some base, some balance, some nonce, some used =>
      let p : TxAccounting.Input := {
        zeros := z, nonzeros := nz, accessAddresses := a,
        accessKeys := keys, gasLimit := limit, gasPriceCap := cap,
        priorityCap := priority, baseFee := base,
        senderBalance := balance, senderNonce := nonce,
        executionUsed := used, feeMarket := mode == "1"
      }
      match TxAccounting.settle p with
      | .ok result =>
        IO.println (txFeeJSON result)
        return 0
      | .error reason =>
        IO.println ("{\"status\":\"error\",\"reason\":\"" ++ reason ++ "\"}")
        return 0
    | _, _, _, _, _, _, _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"invalid decimal fee parameter\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected 12 transaction parameters\"}"
    return 2

/-- Explicitly scoped, single-account storage execution mode.
    No transaction fees, receipts, prestate trie or rollback are implied.
    Syntax: --storage HEX GAS FUEL KEY ORIGINAL_VALUE. -/
private def storageJSON (s : State) (key : Nat) : String :=
  "{\"schemaVersion\":1,\"status\":\"ok\",\"gasRemaining\":\"" ++ toString s.gas ++
  "\",\"halted\":" ++ (if s.halted then "true" else "false") ++
  ",\"slot\":\"" ++ toString key ++
  "\",\"original\":\"" ++ toString (s.storage.original key) ++
  "\",\"current\":\"" ++ toString (s.storage.current key) ++
  "\",\"warm\":" ++ (if s.storage.warm key then "true" else "false") ++
  ",\"refund\":\"" ++ toString s.storage.refund ++ "\"}"

private def storageMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, gasStr, fuelStr, keyStr, originalStr] =>
    match parseBytecode hex, gasStr.toNat?, fuelStr.toNat?,
          keyStr.toNat?, originalStr.toNat? with
    | .ok code, some gas, some fuel, some key, some original =>
      if key ≥ modulus || original ≥ modulus then
        IO.println "{\"status\":\"inputError\",\"message\":\"storage words must be below 2^256\"}"
        return 2
      let s : State :=
        { code := code, gas := gas,
          storage := Storage.withInitial key original }
      match run fuel s with
      | .ok out => IO.println (storageJSON out key)
      | .error e => IO.println (errorJSON e)
      return 0
    | _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX GAS FUEL KEY ORIGINAL_VALUE\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"usage: --storage HEX GAS FUEL KEY ORIGINAL_VALUE\"}"
    return 2

/-- Independently execute TAB-separated storage fixtures in a single Lean process.
    Reject any invalid row rather than counting it as an execution result. -/
private def storageBatchMain (path : String) : IO UInt32 := do
  let source ← IO.FS.readFile path
  let mut count : Nat := 0
  let mut malformed : Nat := 0
  for line in source.splitOn "\n" do
    if line != "" then
      count := count + 1
      let result ← storageMain (line.splitOn "\t")
      if result != 0 then malformed := malformed + 1
  if count == 0 || malformed > 0 then return 2 else return 0

/-- Frame CLI additionally reports RETURN/REVERT and restored storage.
    Return data above 4096 bytes is an explicit unsupported observation. -/
private def frameDataHex (s : State) (offset length : Nat) : String :=
  String.ofList ((List.range length).flatMap (fun i =>
    let b := (s.memory.readByte (offset + i)).toNat
    [hexDigit (b / 16), hexDigit (b % 16)]))

private def frameStateJSON (kind : String) (s : State) (key : Nat)
    (extra : String := "") : String :=
  "{\"schemaVersion\":1,\"status\":\"" ++ kind ++
  "\",\"gasRemaining\":\"" ++ toString s.gas ++
  "\",\"original\":\"" ++ toString (s.storage.original key) ++
  "\",\"current\":\"" ++ toString (s.storage.current key) ++
  "\",\"refund\":\"" ++ toString s.storage.refund ++
  "\",\"warm\":" ++ (if s.storage.warm key then "true" else "false") ++
  extra ++ "}"

private def frameOutcomeJSON (o : Frame.Outcome) (key : Nat) : String :=
  match o with
  | .stopped s => frameStateJSON "stopped" s key
  | .returned s offset length =>
    if length > 4096 then
      "{\"status\":\"unsupported\",\"reason\":\"return-data-observation-limit\"}"
    else
      frameStateJSON "returned" s key
        (",\"returnDataHex\":\"" ++ frameDataHex s offset length ++ "\"")
  | .reverted s offset length =>
    if length > 4096 then
      "{\"status\":\"unsupported\",\"reason\":\"revert-data-observation-limit\"}"
    else
      frameStateJSON "reverted" s key
        (",\"returnDataHex\":\"" ++ frameDataHex s offset length ++ "\"")
  | .exceptional s e =>
    frameStateJSON "exceptional" s key
      (",\"error\":\"" ++ errorCode e ++ "\"")
  | .unsupported e =>
    "{\"status\":\"unsupported\",\"error\":\"" ++ errorCode e ++ "\"}"

private def frameStorageMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, gasStr, fuelStr, keyStr, originalStr] =>
    match parseBytecode hex, gasStr.toNat?, fuelStr.toNat?,
          keyStr.toNat?, originalStr.toNat? with
    | .ok code, some gas, some fuel, some key, some original =>
      if key ≥ modulus || original ≥ modulus then
        IO.println "{\"status\":\"inputError\",\"message\":\"storage words must be below 2^256\"}"
        return 2
      let s : State :=
        { code := code, gas := gas,
          storage := Storage.withInitial key original }
      IO.println (frameOutcomeJSON (Frame.run fuel s) key)
      return 0
    | _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX GAS FUEL KEY ORIGINAL_VALUE\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"usage: --frame-storage HEX GAS FUEL KEY ORIGINAL_VALUE\"}"
    return 2

/-- Zero-value child-call slice, *not* actual CALL opcode dispatch. The
    input gas is the parent's balance after the gas spent on CALL arguments.
    Usage: --call-slice HEX TARGET PARENT_GAS REQUESTED_GAS FUEL -/
private def callSliceMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, targetStr, parentStr, requestedStr, fuelStr] =>
    match parseBytecode hex, targetStr.toNat?, parentStr.toNat?,
      requestedStr.toNat?, fuelStr.toNat? with
    | .ok childCode, some target, some parentGas, some requested, some fuel =>
      if target ≥ World.addressBound then
        IO.println "{\"status\":\"inputError\",\"reason\":\"bad-address\"}"
        return 2
      let accounts : Nat → World.Account := fun addr =>
        if addr == target then { code := childCode } else {}
      let w := World.beginTransaction accounts
      let outcome := WorldCall.callZeroValue fuel w target parentGas requested
      let observable : String → World.TxWorld → Nat → String := fun status world gas =>
        "{\"schemaVersion\":1,\"status\":\"" ++ status ++
        "\",\"gasRemaining\":\"" ++ toString gas ++
        "\",\"slot0\":\"" ++ toString ((world.accounts target).storage 0) ++
        "\",\"warmAddress\":" ++
        (if world.warmAddresses target then "true" else "false") ++
        ",\"warmSlot\":" ++ (if world.warmSlots target 0 then "true" else "false") ++
        ",\"refund\":\"" ++ toString world.refund ++ "\"}"
      match outcome with
      | .childSuccess world gas => IO.println (observable "success" world gas)
      | .childReverted world gas => IO.println (observable "revert" world gas)
      | .childExceptional world gas reason =>
        IO.println (observable "exception" world gas)
        -- Exception reason is reported separately from the contract's
        -- returned CALL success flag; execution remains a legitimate case.
      | .callerOutOfGas => IO.println "{\"status\":\"callerOutOfGas\"}"
      | .invalidAddress => IO.println "{\"status\":\"inputError\",\"reason\":\"bad-address\"}"
      | .invalidChildGas => IO.println "{\"status\":\"unsupported\",\"reason\":\"bad-child-gas\"}"
      | .unsupported _ => IO.println "{\"status\":\"unsupported\",\"reason\":\"unimplemented-child-opcode\"}"
      return 0
    | _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"reason\":\"expected HEX TARGET PARENT_GAS REQUESTED_GAS FUEL\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"reason\":\"usage: --call-slice HEX TARGET PARENT_GAS REQUESTED_GAS FUEL\"}"
    return 2

/-- Minimal whole-word Osaka opcode probe. This is an explicit profile
    selection for a small verified subset, NOT a whole-fork transaction runner.
    The batch variant is used to compare every selected input with a real
    independently executed Osaka EVM using a single Lean process. -/
private def opcodeMain (profile : Profile) (hex gasStr fuelStr : String) : IO UInt32 := do
  match parseBytecode hex, gasStr.toNat?, fuelStr.toNat? with
  | .ok code, some gas, some fuel =>
    let s : EVMCleanroom.State := { code := code, gas := gas, profile := profile }
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

/-- Explicit Prague envelope: type 0..4, blob fee at header excess=0,
    and EIP-7702 authorization count. All big integers are decimal strings.
    This does not read RLP or verify secp256k1, which are host boundaries. -/
private def pragueFeeJSON (p : PragueEnvelope.Settlement) : String :=
  "{\"schemaVersion\":1,\"status\":\"ok\",\"intrinsicGas\":\"" ++
  toString p.intrinsic ++ "\",\"floorGas\":\"" ++ toString p.floor ++
  "\",\"chargedGas\":\"" ++ toString p.charged ++
  "\",\"effectivePrice\":\"" ++ toString p.price ++
  "\",\"blobGasUsed\":\"" ++ toString p.blobGasUsed ++
  "\",\"blobFeeBurn\":\"" ++ toString p.blobFeeBurn ++
  "\",\"senderAfterBalance\":\"" ++ toString p.senderAfterBalance ++
  "\",\"senderAfterNonce\":\"" ++ toString p.senderAfterNonce ++
  "\",\"minerReward\":\"" ++ toString p.minerReward ++
  "\",\"baseFeeBurn\":\"" ++ toString p.baseFeeBurn ++
  "\",\"authorizationRefundGas\":\"" ++ toString p.authorizationRefundGas ++ "\"}"

private def pragueFeeMain (args : List String) : IO UInt32 := do
  let decoded := args.map String.toNat?
  match decoded with
  | [some z, some nz, some a, some k, some lim, some cap,
     some tip, some base, some bal, some nonce, some used,
     some txType, some blobs, some blobCap, some excess,
     some auth, some existing] =>
    let p : PragueEnvelope.Input := {
      zeros := z, nonzeros := nz, accessAddresses := a, accessKeys := k,
      gasLimit := lim, gasPriceCap := cap, priorityCap := tip,
      baseFee := base, senderBalance := bal, senderNonce := nonce,
      executionUsed := used, txType := txType, blobCount := blobs,
      maxFeePerBlobGas := blobCap, excessBlobGas := excess,
      authorizationCount := auth, existingAuthorizations := existing }
    match PragueEnvelope.settle p with
    | .ok result => IO.println (pragueFeeJSON result)
    | .error reason =>
      IO.println ("{\"status\":\"error\",\"reason\":\"" ++ reason ++ "\"}")
    return 0
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected 17 decimal Prague envelope fields\"}"
    return 2

private def hexBytes (bs : Array UInt8) : String :=
  String.ofList ((bs.toList).flatMap (fun byte =>
    [hexDigit (byte.toNat / 16), hexDigit (byte.toNat % 16)]))

/-- A distinct Lean authority state transition: the JS host must recover
    and authenticate the EIP-7702 signer before setting signatureVerified.
    No external signed bytes or 'expected' post-state are trusted as code. -/
private def pragueAuthorizeMain (args : List String) : IO UInt32 := do
  let decoded := args.map String.toNat?
  match decoded with
  | [some chain, some network, some signedNonce, some currentNonce,
     some delegate, some signature, some codePermitted, some accountPresent] =>
    if signature > 1 || codePermitted > 1 || accountPresent > 1 then
      IO.println "{\"status\":\"inputError\",\"reason\":\"flags-must-be-0-or-1\"}"
      return 2
    let a : PragueEnvelope.AuthorizationInput := {
      signedChainId := chain, networkChainId := network,
      signedNonce := signedNonce, currentNonce := currentNonce,
      delegateAddress := delegate,
      signatureVerified := signature == 1,
      codeIsPermitted := codePermitted == 1,
      accountExists := accountPresent == 1 }
    match PragueEnvelope.authorize a with
    | .error reason =>
      IO.println ("{\"status\":\"error\",\"reason\":\"" ++ reason ++ "\"}")
    | .ok result =>
      IO.println ("{\"schemaVersion\":1,\"status\":\"ok\",\"nonce\":\"" ++
        toString result.nonce ++ "\",\"codeHex\":\"0x" ++
        hexBytes result.code ++ "\",\"alreadyExisted\":" ++
        (if result.alreadyExisted then "true" else "false") ++
        ",\"refundGas\":\"" ++ toString result.refundGas ++ "\"}")
    return 0
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected 8 Prague authorization fields\"}"
    return 2

/-- Run the actual 0xf1 instruction in parent bytecode under a scoped Cancun
    frame model; no arbitrary transaction envelope/receipt is inferred.
    Usage: --call-opcode PARENT_HEX CHILD_HEX GAS FUEL.
    Parent address = 0xc1, child address = 0xc3, no initial storage. -/
private def callOpcodeMain (args : List String) : IO UInt32 := do
  match args with
  | [parentHex, childHex, gasStr, fuelStr] =>
    match parseBytecode parentHex, parseBytecode childHex,
      gasStr.toNat?, fuelStr.toNat? with
    | .ok parentCode, .ok childCode, some gas, some fuel =>
      let parentAddress : Nat := 0xc1
      let childAddress : Nat := 0xc3
      let accounts : Nat → World.Account := fun address =>
        if address == parentAddress then { code := parentCode }
        else if address == childAddress then { code := childCode }
        else {}
      let world := World.beginTransaction accounts
      let serialize : String → World.TxWorld → State → String := fun status outcome s =>
        let stack := String.intercalate ","
          (s.stack.items.map (fun w => "\"" ++ toString w.val ++ "\""))
        "{\"schemaVersion\":1,\"status\":\"" ++ status ++
        "\",\"gasRemaining\":\"" ++ toString s.gas ++
        "\",\"pc\":\"" ++ toString s.pc ++
        "\",\"stack\":[" ++ stack ++
        "],\"slot0\":\"" ++ toString ((outcome.accounts childAddress).storage 0) ++
        "\",\"warmAddress\":" ++
        (if outcome.warmAddresses childAddress then "true" else "false") ++
        ",\"warmSlot\":" ++
        (if outcome.warmSlots childAddress 0 then "true" else "false") ++
        ",\"refund\":\"" ++ toString outcome.refund ++ "\"}"
      match CallOpcode.run fuel world parentAddress gas with
      | .stopped final s => IO.println (serialize "stopped" final s)
      | .returned final s => IO.println (serialize "returned" final s)
      | .reverted final s => IO.println (serialize "reverted" final s)
      | .exceptional final s reason =>
        let state := serialize "exceptional" final s
        IO.println ((state.dropEnd 1).toString ++ ",\"reason\":\"" ++ errorCode reason ++ "\"}")
      | .indeterminate reason =>
        IO.println ("{\"status\":\"indeterminate\",\"reason\":\"" ++ errorCode reason ++ "\"}")
      return 0
    | _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"reason\":\"expected PARENT_HEX CHILD_HEX GAS FUEL\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"reason\":\"usage: --call-opcode PARENT_HEX CHILD_HEX GAS FUEL\"}"
    return 2

def cliMain (args : List String) : IO UInt32 := do
  match args with
  | "--prague-tx-fee" :: rest => pragueFeeMain rest
  | "--prague-authorize" :: rest => pragueAuthorizeMain rest
  | "--tx-fee" :: rest => txFeeMain rest
  | "--storage" :: rest => storageMain rest
  | "--frame-storage" :: rest => frameStorageMain rest
  | "--call-opcode" :: rest => callOpcodeMain rest
  | "--call-slice" :: rest => callSliceMain rest
  | ["--storage-batch", path] => storageBatchMain path
  | ["--batch", path] => runBatchFile path
  | ["--osaka-batch", path] => runBatchFile path .osaka
  | ["--osaka", hex, gasStr, fuelStr] => opcodeMain .osaka hex gasStr fuelStr
  | [hex, gasStr, fuelStr] => opcodeMain .shanghaiPlus hex gasStr fuelStr
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"usage: evm-subset HEX GAS FUEL\"}"
    return 2

end EVMCleanroom.CLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.CLI.cliMain args
