import EVMCleanroom.CallOpcode

/-! Executable regression guards for the world-aware call-family dispatcher. -/

namespace EVMCleanroom.CallFamilyTests

open World CallOpcode

private def fixtureWorld (code : Array UInt8) (balance : Nat := 11) : TxWorld :=
  { beginTransaction (fun a =>
      if a == 0xc1 then { balance, storage := fun k => if k = 0 then 7 else 0 }
      else if a == 0xc3 then { code, balance := 23, storage := fun k => if k = 0 then 13 else 0 }
      else {}) with chainId := 3, blockNumber := 0x55 }

private def callStack (kind : CallVariant) (ranges : Windows) (requested target value : Nat) : Stack :=
  match kind with
  | .callCode => ⟨[word requested, word target, word value, word ranges.inputOffset,
      word ranges.inputSize, word ranges.outputOffset, word ranges.outputSize, word 0xdd], by simp⟩
  | .delegateCall | .staticCall => ⟨[word requested, word target, word ranges.inputOffset,
      word ranges.inputSize, word ranges.outputOffset, word ranges.outputSize, word 0xdd], by simp⟩

private def parentFrame (w : TxWorld) (kind : CallVariant) (ranges : Windows := ⟨0, 0, 0, 0⟩)
    (gas : Nat := 100000) (requested : Nat := 30000) (target : Nat := 0xc3)
    (value : Nat := 5) : State :=
  { frameInput w 0xc1 gas false .shanghaiPlus 0x77 0x42 with
    code := #[UInt8.ofNat kind.opcode, 0x00]
    stack := callStack kind ranges requested target value
    callValue := 5 }

private def executeParent (w : TxWorld) (s : State) (depth : Nat := 0) (fuel : Nat := 96) :
    CallOpcode.Outcome :=
  settle w s (executeAtDepth fuel w 0xc1 depth s)

private def bufferBytes (view : ByteView) : List UInt8 :=
  (List.range view.size).map view.readByte

private def contextCode : Array UInt8 :=
  -- Return one byte each for ADDRESS, CALLER, CALLVALUE, SELFBALANCE,
  -- ORIGIN, SLOAD(0), CHAINID and NUMBER.
  #[0x30, 0x5f, 0x53, 0x33, 0x60, 1, 0x53, 0x34, 0x60, 2, 0x53,
    0x47, 0x60, 3, 0x53, 0x32, 0x60, 4, 0x53, 0x5f, 0x54, 0x60, 5, 0x53,
    0x46, 0x60, 6, 0x53, 0x43, 0x60, 7, 0x53, 0x60, 8, 0x5f, 0xf3]

private def checkContext (kind : CallVariant) (bytes : List UInt8) (slotAddress : Nat)
    (balance : Nat := 11) : Bool :=
  let w := fixtureWorld contextCode balance
  let parent := parentFrame w kind ⟨0, 0, 0, 8⟩ (target := addressBound + 0xc3)
  match executeParent w parent with
  | .stopped out s =>
      s.stack.items.map (·.val) == [1, 0xdd] && bufferBytes s.returnData == bytes &&
      out.warmAddresses 0xc3 && !out.warmAddresses 0xc1 &&
      out.warmSlots slotAddress 0 && !out.warmSlots (if slotAddress == 0xc1 then 0xc3 else 0xc1) 0 &&
      (out.accounts 0xc1).balance == balance && (out.accounts 0xc3).balance == 23
  | _ => false

#guard checkContext .callCode [0xc1, 0xc1, 5, 11, 0x77, 7, 3, 0x55] 0xc1
#guard checkContext .delegateCall [0xc1, 0x42, 5, 0, 0x77, 7, 3, 0x55] 0xc1 0
#guard checkContext .staticCall [0xc3, 0xc1, 0, 23, 0x77, 13, 3, 0x55] 0xc3

private def nestedDelegate : Bool :=
  let start := fixtureWorld #[0x34, 0x33, 0x55, 0x00]
  let middle := putAccount start 0xc2 { code := #[0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0xc3, 0x61, 0x75, 0x30, 0xf4, 0x00] }
  let w := putAccount middle 0xc1 { middle.accounts 0xc1 with
    code := #[0x5f, 0x5f, 0x5f, 0x5f, 0x60, 7, 0x60, 0xc2, 0x61, 0xea, 0x60, 0xf1, 0x00] }
  match CallOpcode.run 96 w 0xc1 100000 with
  | .stopped out s =>
      s.stack.items.map (·.val) == [1] && ((out.accounts 0xc2).storage 0xc1) == 7 &&
      (out.accounts 0xc2).balance == 7 && (out.accounts 0xc1).balance == 4 &&
      (out.accounts 0xc3).balance == 23 && ((out.accounts 0xc3).storage 0xc1) == 0
  | _ => false

#guard nestedDelegate

private def writeCode : Array UInt8 := #[0x60, 42, 0x5f, 0x55, 0x00]

private def mutableWrite (kind : CallVariant) : Bool :=
  let w := fixtureWorld writeCode
  match executeParent w (parentFrame w kind) with
  | .stopped out s =>
      s.stack.items.map (·.val) == [1, 0xdd] && ((out.accounts 0xc1).storage 0) == 42 &&
      s.storage.current 0 == 42 && (out.original 0xc1 0) == 7 && ((out.accounts 0xc3).storage 0) == 13
  | _ => false

#guard mutableWrite .callCode
#guard mutableWrite .delegateCall

private def softStaticFailure (kind : CallVariant) (childCode : Array UInt8) (readOnly : Bool) : Bool :=
  let w := fixtureWorld childCode
  -- Supply enough gas for the value CALL, including its new-account cost,
  -- so its static failure cannot be explained by an unaffordable schedule.
  match executeParent w { parentFrame w kind (requested := 60000) with readOnly } with
  | .stopped out s =>
      s.stack.items.map (·.val) == [0, 0xdd] && s.returnData.size == 0 && out.logsRev.isEmpty &&
      ((out.accounts 0xc1).storage 0) == 7 && ((out.accounts 0xc3).storage 0) == 13 &&
      out.warmAddresses 0xc3 && !out.warmAddresses 0xc4
  | _ => false

#guard softStaticFailure .staticCall writeCode false
#guard softStaticFailure .staticCall #[0x5f, 0x5f, 0xa0, 0x00] false
#guard softStaticFailure .staticCall #[0x5f, 0x5f, 0x5f, 0x5f, 0x60, 1, 0x60, 0xc4, 0x5f, 0xf1, 0x00] false
#guard softStaticFailure .callCode writeCode true
#guard softStaticFailure .delegateCall writeCode true

private def checkCallCodeValue (balance expectedBit expectedGas : Nat) : Bool :=
  -- The code account has no code, nonce or balance. The test owes the
  -- value surcharge and receives the unused stipend even at zero request.
  let w := putAccount (fixtureWorld #[] balance) 0xc3 {}
  let parent := { parentFrame w .callCode (gas := 11600) (requested := 0) with readOnly := true }
  match executeParent w parent with
  | .stopped out s =>
    s.stack.items.map (·.val) == [expectedBit, 0xdd] && s.gas == expectedGas &&
    (out.accounts 0xc1).balance == balance && (out.accounts 0xc3).balance == 0 && out.warmAddresses 0xc3
  | _ => false

#guard checkCallCodeValue 11 1 2300
#guard checkCallCodeValue 4 0 2300

private def outcomeError (outcome : CallOpcode.Outcome) (exceptional : Bool) (e : Error) : Bool :=
  match outcome with
  | .exceptional _ _ reason => exceptional && decide (reason = e)
  | .indeterminate reason => !exceptional && decide (reason = e)
  | _ => false

private def checkDelegateCharge (warmAddress gas : Nat) : Bool :=
  let w := { fixtureWorld #[0x00] 0 with warmAddresses := (· == warmAddress) }
  let s := parentFrame w .delegateCall (gas := gas) (requested := 0)
  match executeParent w s with
  | .stopped _ out => out.stack.items.map (·.val) == [1, 0xdd] && out.gas == 0
  | _ => false

-- The nonzero incoming value needs neither funds nor additional gas. The
-- charged access is to the code account, even when the caller is already warm.
#guard checkDelegateCharge 0xc1 2600
#guard checkDelegateCharge 0xc3 100
#guard let w := { fixtureWorld #[0x00] 0 with warmAddresses := (· == 0xc1) }
  outcomeError (executeParent w (parentFrame w .delegateCall (gas := 100))) true .outOfGas

private def checkWitnesses (kind : CallVariant) (accounts slots : Nat → Bool)
    (expected : Option Error) : Bool :=
  let start := fixtureWorld #[0x5f, 0x54, 0x00]
  let w := { start with witnessed := some ⟨accounts, fun a k => slots a && k == 0⟩ }
  let s := parentFrame w kind (target := addressBound + 0xc3)
  match expected, executeParent w s with
  | some reason, .indeterminate actual => decide (reason = actual)
  | none, .stopped _ out => out.stack.items.map (·.val) == [1, 0xdd]
  | _, _ => false

#guard checkWitnesses .delegateCall (· == 0xc1) (fun _ => false) (some (.incompleteState 0xc3 none))
#guard checkWitnesses .callCode (· == 0xc3) (fun _ => false) (some (.incompleteState 0xc1 none))
#guard checkWitnesses .delegateCall (fun _ => true) (· == 0xc3) (some (.incompleteState 0xc1 (some 0)))
#guard checkWitnesses .delegateCall (fun _ => true) (· == 0xc1) none
#guard checkWitnesses .staticCall (fun _ => true) (· == 0xc1) (some (.incompleteState 0xc3 (some 0)))
#guard checkWitnesses .staticCall (fun _ => true) (· == 0xc3) none

private def copyRoundTrip : Bool :=
  let w := fixtureWorld #[0x60, 2, 0x5f, 0x5f, 0x37, 0x60, 2, 0x5f, 0xf3]
  let memory := (((Memory.empty.expand 1).writeByte 4 0x7a).writeByte 5 0x7b).writeByte 9 0xee
  let parent := { parentFrame w .staticCall ⟨4, 2, 8, 1⟩ with memory }
  match executeParent w parent with
  | .stopped _ s =>
      s.stack.items.map (·.val) == [1, 0xdd] && bufferBytes s.returnData == [0x7a, 0x7b] &&
      s.memory.readByte 8 == 0x7a && s.memory.readByte 9 == 0xee
  | _ => false

#guard copyRoundTrip

private def childFailure (kind : CallVariant) (halt : UInt8) (data : List UInt8) (byte : UInt8) : Bool :=
  let w := fixtureWorld #[0x60, 42, 0x5f, 0x55, 0x60, 0x78, 0x5f, 0x53, 0x60, 1, 0x5f, halt]
  let memory := (Memory.empty.expand 1).writeByte 8 0xee
  let parent := { parentFrame w kind ⟨0, 0, 8, 1⟩ with
    memory := memory
    returnData := ByteView.ofArray #[0xab, 0xcd] }
  match executeParent w parent with
  | .stopped out s =>
      s.stack.items.map (·.val) == [0, 0xdd] && bufferBytes s.returnData == data &&
      s.memory.readByte 8 == byte && !out.warmSlots 0xc1 0 && out.warmAddresses 0xc3 &&
      ((out.accounts 0xc1).storage 0) == 7 && ((out.accounts 0xc3).storage 0) == 13
  | _ => false

#guard childFailure .delegateCall 0xfd [0x78] 0x78
#guard childFailure .callCode 0xfe [] 0xee

private def revertingParent : Bool :=
  let w := fixtureWorld writeCode
  let s := { parentFrame w .delegateCall with code := #[0xf4, 0x5f, 0x5f, 0xfd] }
  match executeParent w s with
  | .reverted out parent =>
      ((out.accounts 0xc1).storage 0) == 7 && parent.storage.current 0 == 7 &&
      !out.warmAddresses 0xc3 && !out.warmSlots 0xc1 0
  | _ => false

#guard revertingParent

private def checkDepth (depth expectedBit : Nat) : Bool :=
  let w := fixtureWorld #[0x00]
  let s := parentFrame w .delegateCall ⟨0, 0, 64, 1⟩ 2609
  match executeParent w s depth with
  | .stopped out parent =>
      parent.stack.items.map (·.val) == [expectedBit, 0xdd] && parent.gas == 0 &&
      parent.memory.words == 3 && out.warmAddresses 0xc3
  | _ => false

#guard checkDepth 1023 1
#guard checkDepth 1024 0
#guard let w := fixtureWorld #[0x00]
  outcomeError (executeParent w (parentFrame w .delegateCall ⟨0, 0, 64, 1⟩ 2608) 1024) true .outOfGas

private def capAfterExpansion : Bool :=
  let w := fixtureWorld #[0x5a, 0x5f, 0x53, 0x60, 1, 0x5f, 0xf3]
  let s := parentFrame w .delegateCall ⟨0, 0, 64, 1⟩ 10000
  -- 10000 - 9 (expansion) - 2600 (cold access) = 7391.
  -- The cap forwards 7276. GAS then observes 7274, whose low byte is 106.
  match executeParent w s with
  | .stopped _ parent => parent.memory.readByte 64 == 106 && bufferBytes parent.returnData == [106]
  | _ => false

#guard capAfterExpansion

private def profileBoundary (kind : CallVariant) : Bool :=
  let w := fixtureWorld #[]
  let s := { parentFrame w kind with profile := .preShanghai }
  outcomeError (executeParent w s) false .unsupportedFork

#guard profileBoundary .callCode && profileBoundary .delegateCall && profileBoundary .staticCall
#guard let w := fixtureWorld #[]
  outcomeError (executeParent w (parentFrame w .callCode (target := 4))) false .unsupportedFork
#guard let w := fixtureWorld #[]
  outcomeError (executeParent w (parentFrame w .staticCall) (fuel := 0)) false .stepLimit

end EVMCleanroom.CallFamilyTests
