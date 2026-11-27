import EVMCleanroom.Core
import EVMCleanroom.Frame
import EVMCleanroom.Call
import EVMCleanroom.CallOpcode
import EVMCleanroom.CallTransaction
import EVMCleanroom.CLIEncoding
import EVMCleanroom.TxAccounting
import EVMCleanroom.PragueEnvelope
import EVMCleanroom.FrontierTransfer
import EVMCleanroom.WorldCLI

/-!
A minimal machine-readable entry point for the *restricted* EVM model.

Usage:
  lake exe evm-subset 600260030100 100 10

Arguments: hex bytecode (optional 0x prefix), initial gas, step fuel.
Successful execution prints one JSON line. Execution errors also print
JSON and exit zero; malformed invocation exits with code 2.

The ordinary call-transaction entry point forwards to the sibling
`evm-call-transaction` executable, which consumes decoded envelopes and
state witnesses already authenticated by a host.
-/

namespace EVMCleanroom.CLI

private def observedLogJSON (entry : LogEntry) : String :=
  -- The only payload strings are decimal words and hex bytes.
  let topics := String.intercalate "," (entry.topics.map (fun topic => "\"" ++ toString topic.val ++ "\""))
  "{\"address\":\"" ++ toString entry.address ++ "\",\"dataHex\":\"" ++ exactViewHex entry.data ++
    "\",\"topics\":[" ++ topics ++ "]}"

private def appendObservations (json : String) (logsRev : List LogEntry)
    (observeLogs : Bool) (acceptance : Option Keccak.Acceptance) : String :=
  let keccak := if acceptance.isSome then ",\"keccakOptIn\":true" else ""
  let logsBytes := if observeLogs then logsRev.foldl
    (fun n entry => n + entry.data.size + 32 * entry.topics.length + 20) 0 else 0
  if logsBytes > CallTransaction.maxDataBytes then
    "{\"status\":\"indeterminate\",\"reason\":\"resourceLimit\"" ++ keccak ++ "}"
  else if !observeLogs && !acceptance.isSome then json
  else
    let logs := if observeLogs then
      ",\"logs\":[" ++ String.intercalate "," (logsRev.reverse.map observedLogJSON) ++
      "],\"logsTruncated\":false"
      else ""
    (json.dropEnd 1).toString ++ keccak ++ logs ++ "}"

private def byteObservationLimit : Nat := 4096

private def memoryHex (s : EVMCleanroom.State) (limit : Nat) : String :=
  let observed := min (32 * s.memory.words) limit
  String.ofList ((List.range observed).flatMap (fun address =>
    let b := (s.memory.readByte address).toNat
    [hexDigit (b / 16), hexDigit (b % 16)]))

private def stackJSON (s : EVMCleanroom.State) : String :=
  -- Decimal STRING encoding is essential: a JSON number would silently
  -- lose precision in JavaScript for EVM words above 2^53 - 1.
  "[" ++ String.intercalate "," (s.stack.items.map (fun w => "\"" ++ toString w.val ++ "\"")) ++ "]"

private def memoryFieldsJSON (s : State) : String :=
  ",\"memorySizeBytes\":\"" ++ toString (32 * s.memory.words) ++
  "\",\"memoryWord0\":\"" ++ toString (s.memory.readWord 0) ++
  "\",\"memoryObservedBytes\":\"" ++ toString (min (32 * s.memory.words) byteObservationLimit) ++
  "\",\"memoryTruncated\":" ++ (if byteObservationLimit < 32 * s.memory.words then "true" else "false") ++
  ",\"memoryHex\":\"" ++ memoryHex s byteObservationLimit ++ "\""

private def successJSON (s : EVMCleanroom.State) : String :=
  "{\"schemaVersion\":2,\"status\":\"ok\",\"gasRemaining\":\"" ++ toString s.gas ++
  "\",\"pc\":\"" ++ toString s.pc ++
  "\",\"halted\":" ++ (if s.halted then "true" else "false") ++
  ",\"stack\":" ++ stackJSON s ++ memoryFieldsJSON s ++ "}"

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
    if length > byteObservationLimit then
      "{\"status\":\"unsupported\",\"reason\":\"return-data-observation-limit\"}"
    else
      frameStateJSON "returned" s key
        (",\"returnDataHex\":\"" ++ frameDataHex s offset length ++ "\"")
  | .reverted s offset length =>
    if length > byteObservationLimit then
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

/-- Frame-call snapshot with explicit total return length and bounded byte output. -/
private def frameCallJSON (outcome : Frame.Outcome) (guarded observeLogs : Bool)
    (acceptance : Option Keccak.Acceptance) : String :=
  let context := if guarded then ",\"comparisonContext\":\"zero-value-context-free-v1\"" else ""
  let report (status : String) (s : State) (offset length : Nat) (extra : String := "") :=
    let json := frameStateJSON status s 0
      (",\"stack\":" ++ stackJSON s ++ memoryFieldsJSON s ++
        ",\"returnDataHex\":\"" ++ frameDataHex s offset (min length byteObservationLimit) ++
        "\",\"returnDataLength\":\"" ++ toString length ++
        "\",\"returnDataTruncated\":" ++ (if length > byteObservationLimit then "true" else "false") ++
        extra ++ context)
    appendObservations json s.logsRev observeLogs acceptance
  match outcome with
  | .stopped s => report "stopped" s 0 0
  | .returned s offset length => report "returned" s offset length
  | .reverted s offset length => report "reverted" s offset length
  | .exceptional s e => report "exceptional" s 0 0 (",\"error\":\"" ++ errorCode e ++ "\"")
  | .unsupported e =>
    let json := "{\"status\":\"unsupported\",\"error\":\"" ++ errorCode e ++ "\"" ++ context ++ "}"
    appendObservations json [] observeLogs acceptance

private def frameCallMain (args : List String) (guarded observeLogs : Bool)
    (acceptance : Option Keccak.Acceptance) : IO UInt32 := do
  match args with
  | [hex, dataHex, gasStr, fuelStr] =>
    match parseBytecode hex, parseBytecode dataHex, gasStr.toNat?, fuelStr.toNat? with
    | .ok code, .ok callData, some gas, some fuel =>
      let input : State := {
        code := code, gas := gas, callData := ByteView.ofArray callData
        callValue := 0, readOnly := guarded, keccakAcceptance := acceptance }
      let outcome := if guarded then Frame.runWithPolicy Frame.zeroValueContextFree fuel input
        else Frame.run fuel input
      IO.println (frameCallJSON outcome guarded observeLogs acceptance)
      return 0
    | _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX CALLDATA_HEX GAS FUEL\"}"
      return 2
  | _ =>
    let command := if guarded then "--pure-frame-call" else "--frame-call"
    IO.println ("{\"status\":\"inputError\",\"message\":\"usage: " ++ command ++ " HEX CALLDATA_HEX GAS FUEL\"}")
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
private def opcodeMain (profile : Profile) (hex gasStr fuelStr : String)
    (observeLogs : Bool := false) (acceptance : Option Keccak.Acceptance := none) : IO UInt32 := do
  match parseBytecode hex, gasStr.toNat?, fuelStr.toNat? with
  | .ok code, some gas, some fuel =>
    let s : EVMCleanroom.State := { code := code, gas := gas, profile := profile, keccakAcceptance := acceptance }
    match EVMCleanroom.run fuel s with
    | .ok out =>
      IO.println (appendObservations (successJSON out) out.logsRev observeLogs acceptance)
      return 0
    | .error e =>
      IO.println (appendObservations (errorJSON e) [] observeLogs acceptance)
      return 0
  | .error why, _, _ =>
    IO.println ("{\"status\":\"inputError\",\"message\":\"" ++ why ++ "\"}")
    return 2
  | _, _, _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"gas and fuel must be nonnegative integers\"}"
    return 2

/-- Deliberately synthetic chain-context probe; only the caller supplies the
    chain ID. No transaction signature, block header or consensus validation
    occurs here. The supported instruction profile is post-Istanbul. -/
private def chainIdMain (hex gasStr fuelStr idStr : String) : IO UInt32 := do
  match parseBytecode hex, gasStr.toNat?, fuelStr.toNat?, idStr.toNat? with
  | .ok code, some gas, some fuel, some selectedId =>
    let s : State := {
      code := code, gas := gas, profile := .shanghaiPlus,
      chainId := selectedId }
    match EVMCleanroom.run fuel s with
    | .ok out =>
      IO.println (successJSON out)
      return 0
    | .error e =>
      IO.println (errorJSON e)
      return 0
  | _, _, _, _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX GAS FUEL CHAIN_ID\"}"
    return 2

/-- Synthetic opcode-level fee and randomness context. The effective gas
    price is not recovered from a signature and the randao mix is not derived
    from an authenticated header or beacon state. -/
private def txEnvironmentMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, gasStr, fuelStr, priceStr, randaoStr] =>
    match parseBytecode hex, gasStr.toNat?, fuelStr.toNat?, priceStr.toNat?,
          randaoStr.toNat? with
    | .ok code, some gas, some fuel, some price, some randao =>
      if price ≥ modulus ∨ randao ≥ modulus then
        IO.println "{\"status\":\"inputError\",\"message\":\"fee or randao out of range\"}"
        return 2
      let s : State := {
        code := code, gas := gas, profile := .shanghaiPlus,
        effectiveGasPrice := price, blockPrevRandao := randao }
      match EVMCleanroom.run fuel s with
      | .ok out => IO.println (successJSON out); return 0
      | .error e => IO.println (errorJSON e); return 0
    | _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX GAS FUEL EFFECTIVE_GAS_PRICE PREVRANDAO\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected 5 transaction environment arguments\"}"
    return 2

/-- Synthetic EIP-7516 probe: price is supplied, not recomputed from a header. -/
private def blobBaseFeeMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, gasStr, fuelStr, feeStr, profileName] =>
    let selected : Option Profile :=
      match profileName with
      | "cancun" => some .cancunPlus
      | "osaka" => some .osaka
      | "shanghai" => some .shanghaiPlus
      | "preShanghai" => some .preShanghai
      | _ => none
    match parseBytecode hex, gasStr.toNat?, fuelStr.toNat?, feeStr.toNat?, selected with
    | .ok code, some gas, some fuel, some fee, some profile =>
      if fee = 0 ∨ fee ≥ modulus then
        IO.println "{\"status\":\"inputError\",\"message\":\"blob base fee out of range\"}"
        return 2
      let s : State := { code := code, gas := gas, profile := profile, blockBlobBaseFee := fee }
      match EVMCleanroom.run fuel s with
      | .ok out => IO.println (successJSON out); return 0
      | .error e => IO.println (errorJSON e); return 0
    | _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX GAS FUEL BLOB_BASE_FEE PROFILE\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected 5 blob fee arguments\"}"
    return 2

/-- Explicit synthetic block environment for opcode-level comparisons. These
    values are supplied by the caller and are not authenticated block fields. -/
private def blockEnvironmentMain (args : List String) : IO UInt32 := do
  match args with
  | [hex, gasStr, fuelStr, coinbaseStr, timestampStr, numberStr, limitStr, baseFeeStr] =>
    match parseBytecode hex, gasStr.toNat?, fuelStr.toNat?, coinbaseStr.toNat?,
          timestampStr.toNat?, numberStr.toNat?, limitStr.toNat?, baseFeeStr.toNat? with
    | .ok code, some gas, some fuel, some coinbase, some timestamp,
      some number, some limit, some baseFee =>
      if coinbase ≥ 2 ^ 160 ∨ timestamp ≥ modulus ∨ number ≥ modulus ∨
          limit ≥ modulus ∨ baseFee ≥ modulus then
        IO.println "{\"status\":\"inputError\",\"message\":\"block fields out of range\"}"
        return 2
      let s : State := {
        code := code, gas := gas, profile := .shanghaiPlus
        blockCoinbase := coinbase, blockTimestamp := timestamp,
        blockNumber := number, blockGasLimit := limit, blockBaseFee := baseFee }
      match EVMCleanroom.run fuel s with
      | .ok out => IO.println (successJSON out); return 0
      | .error e => IO.println (errorJSON e); return 0
    | _, _, _, _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"message\":\"expected HEX GAS FUEL COINBASE TIMESTAMP NUMBER GASLIMIT BASEFEE\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"expected 8 block environment arguments\"}"
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

private def byteViewFieldsJSON (name : String) (view : ByteView) : String :=
  let count := min view.size byteObservationLimit
  let hex := String.ofList ((List.range count).flatMap (fun i =>
    let byte := (view.readByte i).toNat
    [hexDigit (byte / 16), hexDigit (byte % 16)]))
  ",\"" ++ name ++ "Hex\":\"" ++ hex ++
  "\",\"" ++ name ++ "Size\":\"" ++ toString view.size ++
  "\",\"" ++ name ++ "Truncated\":" ++ (if count < view.size then "true" else "false")

private def parseProfile : String → Option Profile
  | "preShanghai" => some .preShanghai
  | "shanghaiPlus" => some .shanghaiPlus
  | "cancunPlus" => some .cancunPlus
  | "osaka" => some .osaka
  | _ => none

/-- Run call-family instructions under a scoped EVM frame model. Parent
    address = 0xc1, child = 0xc3, third account = 0xc4. The prestate has
    zero storage and starts cold by default. The optional context controls
    the entry frame's read-only flag, opcode profile, depth, address warmth,
    caller address and transaction origin. -/
private def callOpcodeMain (args : List String) (observeLogs : Bool)
    (acceptance : Option Keccak.Acceptance) : IO UInt32 := do
  let basic := match args with
    | [p, c, g, f] => [p, c, g, f, "0", "0", "0"]
    | otherwise => otherwise
  let expanded := match basic.length with
    | 7 => basic ++ ["0", "shanghaiPlus", "0", "", "0", "0", "0"]
    | 10 => basic ++ ["", "0", "0", "0"]
    | 11 => basic ++ ["0", "0", "0"]
    | 12 => basic ++ ["0", "0"]
    | 13 => basic ++ ["0"]
    | _ => basic
  match expanded with
  | [parentHex, childHex, gasStr, fuelStr, parentBalanceStr, childBalanceStr, childNonceStr,
     readOnlyStr, profileStr, depthStr, grandchildHex, prewarmParentStr, entryCallerStr, txOriginStr] =>
    match parseBytecode parentHex, parseBytecode childHex, parseBytecode grandchildHex,
      gasStr.toNat?, fuelStr.toNat?, parentBalanceStr.toNat?, childBalanceStr.toNat?,
      childNonceStr.toNat?, readOnlyStr.toNat?, parseProfile profileStr, depthStr.toNat?,
      prewarmParentStr.toNat?, entryCallerStr.toNat?, txOriginStr.toNat? with
    | .ok parentCode, .ok childCode, .ok grandchildCode, some gas, some fuel,
        some parentBalance, some childBalance, some childNonce, some readOnly, some profile,
        some depth, some prewarmParent, some entryCaller, some txOrigin =>
      if parentBalance ≥ modulus || childBalance ≥ modulus || childNonce ≥ 2 ^ 64 then
        IO.println "{\"status\":\"inputError\",\"reason\":\"account-values-out-of-range\"}"
        return 2
      if readOnly > 1 || depth > CallOpcode.maxDepth || prewarmParent > 1 ||
          entryCaller ≥ World.addressBound || txOrigin ≥ World.addressBound then
        IO.println "{\"status\":\"inputError\",\"reason\":\"call-context-out-of-range\"}"
        return 2
      let parentAddress : Nat := 0xc1
      let childAddress : Nat := 0xc3
      let grandchildAddress : Nat := 0xc4
      let accounts : Nat → World.Account := fun address =>
        if address == parentAddress then
          { code := parentCode, balance := parentBalance }
        else if address == childAddress then
          { code := childCode, balance := childBalance, nonce := childNonce }
        else if address == grandchildAddress then { code := grandchildCode }
        else {}
      let entry := { World.beginTransaction accounts with keccakAcceptance := acceptance }
      let world := if prewarmParent == 1 then WorldCall.warmTarget entry parentAddress else entry
      let serialize : String → World.TxWorld → State → String := fun status outcome s =>
        "{\"schemaVersion\":2,\"status\":\"" ++ status ++
        "\",\"gasRemaining\":\"" ++ toString s.gas ++
        "\",\"pc\":\"" ++ toString s.pc ++
        "\",\"stack\":" ++ stackJSON s ++
        ",\"slot0\":\"" ++ toString ((outcome.accounts childAddress).storage 0) ++
        "\",\"parentSlot0\":\"" ++ toString ((outcome.accounts parentAddress).storage 0) ++
        "\",\"grandchildSlot0\":\"" ++ toString ((outcome.accounts grandchildAddress).storage 0) ++
        "\",\"parentBalance\":\"" ++ toString ((outcome.accounts parentAddress).balance) ++
        "\",\"childBalance\":\"" ++ toString ((outcome.accounts childAddress).balance) ++
        "\",\"childNonce\":\"" ++ toString ((outcome.accounts childAddress).nonce) ++
        "\",\"warmAddress\":" ++ (if outcome.warmAddresses childAddress then "true" else "false") ++
        ",\"warmSlot\":" ++ (if outcome.warmSlots childAddress 0 then "true" else "false") ++
        ",\"warmGrandchildAddress\":" ++ (if outcome.warmAddresses grandchildAddress then "true" else "false") ++
        ",\"warmGrandchildSlot\":" ++ (if outcome.warmSlots grandchildAddress 0 then "true" else "false") ++
        ",\"entryParentWarm\":" ++ (if prewarmParent == 1 then "true" else "false") ++
        ",\"refund\":\"" ++ toString outcome.refund ++ "\"" ++
        byteViewFieldsJSON "parentMemory" (ByteView.ofMemory s.memory 0 (32 * s.memory.words)) ++
        byteViewFieldsJSON "returnData" s.returnData ++
        byteViewFieldsJSON "returnBytes" s.outputData ++ "}"
      let initial := World.frameInput world parentAddress gas (readOnly == 1) profile txOrigin entryCaller
      match CallOpcode.settle world initial (CallOpcode.executeAtDepth fuel world parentAddress depth initial) with
      | .stopped final st =>
        IO.println (appendObservations (serialize "stopped" final st) final.logsRev observeLogs acceptance)
      | .returned final st =>
        IO.println (appendObservations (serialize "returned" final st) final.logsRev observeLogs acceptance)
      | .reverted final st =>
        IO.println (appendObservations (serialize "reverted" final st) final.logsRev observeLogs acceptance)
      | .exceptional final st reason =>
        let state := serialize "exceptional" final st
        let json := (state.dropEnd 1).toString ++ ",\"reason\":\"" ++ errorCode reason ++ "\"}"
        IO.println (appendObservations json final.logsRev observeLogs acceptance)
      | .indeterminate reason =>
        let json := "{\"status\":\"indeterminate\",\"reason\":\"" ++ errorCode reason ++ "\"}"
        IO.println (appendObservations json [] observeLogs acceptance)
      return 0
    | _, _, _, _, _, _, _, _, _, _, _, _, _, _ =>
      IO.println "{\"status\":\"inputError\",\"reason\":\"bad CALL bytecode, gas or account fields\"}"
      return 2
  | _ =>
    IO.println "{\"status\":\"inputError\",\"reason\":\"expected PARENT_HEX CHILD_HEX GAS FUEL [PARENT_BALANCE CHILD_BALANCE CHILD_NONCE [READ_ONLY PROFILE DEPTH [GRANDCHILD_HEX [PREWARM_PARENT [ENTRY_CALLER [TX_ORIGIN]]]]]]\"}"
    return 2

/-- Fork-scoped pre-EIP-155 Frontier account transfer. The host supplies
    true pre-transaction balances/nonce and must authenticate them if
    historical state-root replay is claimed. Every integer is decimal;
    this function does NOT assume the illustrative CI prebalances were
    Ethereum's real 2015 balances. -/
private def frontierTransferJSON (o : FrontierTransfer.Outcome) : String :=
  "{\"schemaVersion\":1,\"status\":\"ok\",\"gasUsed\":\"" ++
  toString o.gasUsed ++ "\",\"gasRemaining\":\"" ++
  toString o.gasRemaining ++ "\",\"chargedFee\":\"" ++
  toString o.chargedFee ++ "\",\"valueTransferred\":\"" ++
  toString o.valueTransferred ++ "\",\"senderAfterBalance\":\"" ++
  toString o.senderBalance ++ "\",\"receiverAfterBalance\":\"" ++
  toString o.receiverBalance ++ "\",\"minerAfterBalance\":\"" ++
  toString o.minerBalance ++ "\",\"senderAfterNonce\":\"" ++
  toString o.senderNonce ++ "\"}"

/-- Input order:
    GAS_LIMIT BLOCK_GAS_REMAINING GAS_PRICE VALUE ZERO_BYTES NONZERO_BYTES
    SENDER_BALANCE RECEIVER_BALANCE MINER_BALANCE SENDER_NONCE SIGNED_NONCE
    RECIPIENT_CODE_EMPTY_FLAG (0/1). -/
private def frontierTransferMain (args : List String) : IO UInt32 := do
  match args.map String.toNat? with
  | [some limit, some remaining, some price, some value, some zeros,
     some nonzeros, some senderBalance, some receiverBalance, some minerBalance,
     some senderNonce, some signedNonce, some empty] =>
    if empty > 1 then
      IO.println "{\"status\":\"inputError\",\"reason\":\"empty-code-flag-not-boolean\"}"
      return 2
    let input : FrontierTransfer.Input := {
      gasLimit := limit, blockGasRemaining := remaining,
      gasPrice := price, transferredValue := value,
      zeros := zeros, nonzeros := nonzeros,
      senderBalance := senderBalance, receiverBalance := receiverBalance,
      minerBalance := minerBalance, senderNonce := senderNonce,
      signedNonce := signedNonce, recipientHasNoCode := empty == 1 }
    match FrontierTransfer.settle input with
    | .ok result => IO.println (frontierTransferJSON result)
    | .error reason =>
      IO.println ("{\"status\":\"error\",\"reason\":\"" ++ reason ++ "\"}")
    return 0
  | _ =>
    IO.println "{\"status\":\"inputError\",\"reason\":\"expected 12 decimal Frontier transfer fields\"}"
    return 2

private def forwardCallTransaction (path : String) (acceptance : Option Keccak.Acceptance) : IO UInt32 := do
  let unavailable := do
    let keccak := if acceptance.isSome then "true" else "false"
    IO.println ("{\"keccakOptIn\":" ++ keccak ++
      ",\"reason\":\"transactionCompanionUnavailable\",\"schemaVersion\":1,\"status\":\"inputError\"}")
    return 2
  try
    let some directory := (← IO.appPath).parent | unavailable
    let companion := (directory / "evm-call-transaction").addExtension System.FilePath.exeExtension
    unless ← companion.pathExists do
      return ← unavailable
    let args := if acceptance.isSome then
      #["--dangerously-enable-unverified-keccak", "--call-transaction", path]
    else #["--call-transaction", path]
    let child ← IO.Process.spawn { cmd := companion.toString, args }
    child.wait
  catch _ => unavailable

def cliMain (args : List String) : IO UInt32 := do
  let (args, acceptance) := match args with
    | "--dangerously-enable-unverified-keccak" :: rest =>
      (rest, some Keccak.dangerouslyAcceptUnverified)
    | _ => (args, none)
  let (args, observeLogs) := match args with
    | "--observe-logs" :: rest => (rest, true)
    | _ => (args, false)
  match args with
  | ["--call-transaction", path] => forwardCallTransaction path acceptance
  | "--frontier-transfer" :: rest => frontierTransferMain rest
  | "--prague-tx-fee" :: rest => pragueFeeMain rest
  | "--prague-authorize" :: rest => pragueAuthorizeMain rest
  | "--tx-fee" :: rest => txFeeMain rest
  | "--storage" :: rest => storageMain rest
  | "--frame-storage" :: rest => frameStorageMain rest
  | "--frame-call" :: rest => frameCallMain rest false observeLogs acceptance
  | "--pure-frame-call" :: rest => frameCallMain rest true observeLogs acceptance
  | "--call-opcode" :: rest => callOpcodeMain rest observeLogs acceptance
  | "--call-slice" :: rest => callSliceMain rest
  | "--world" :: rest => WorldCLI.worldMain acceptance rest
  | ["--world-batch", path] => WorldCLI.worldBatchMain acceptance path
  | ["--storage-batch", path] => storageBatchMain path
  | ["--batch", path] => runBatchFile path
  | ["--osaka-batch", path] => runBatchFile path .osaka
  | ["--chainid", hex, gasStr, fuelStr, idStr] => chainIdMain hex gasStr fuelStr idStr
  | "--block-env" :: rest => blockEnvironmentMain rest
  | "--tx-env" :: rest => txEnvironmentMain rest
  | "--blobbasefee" :: rest => blobBaseFeeMain rest
  | ["--osaka", hex, gasStr, fuelStr] => opcodeMain .osaka hex gasStr fuelStr observeLogs acceptance
  | [hex, gasStr, fuelStr] => opcodeMain .shanghaiPlus hex gasStr fuelStr observeLogs acceptance
  | _ =>
    IO.println "{\"status\":\"inputError\",\"message\":\"usage: evm-subset HEX GAS FUEL\"}"
    return 2

end EVMCleanroom.CLI

def main (args : List String) : IO UInt32 :=
  EVMCleanroom.CLI.cliMain args
