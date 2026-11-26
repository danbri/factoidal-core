import EVMCleanroom.CallOpcode
import Lean.Data.Json

/-! Regression fixtures for caller resumption, precompile dispatch and the
static execution context across CALL. The differential probe below the Lean
project's scripts directory reads observations from these same runs. -/

namespace EVMCleanroom.CallBoundaryTests

open World

private def selfCallCode : Array UInt8 :=
  -- CALLVALUE selects the child's store-and-stop branch during self-CALL.
  #[0x34, 0x60, 0x11, 0x57, 0x5f, 0x5f, 0x5f, 0x5f,
    0x60, 0x01, 0x60, 0xc1, 0x61, 0x75, 0x30, 0xf1, 0x00,
    0x5b, 0x60, 0x2a, 0x5f, 0x55, 0x00]

private def zeroCallCode : Array UInt8 :=
  #[0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0xc3, 0x61, 0x75, 0x30, 0xf1, 0x00]

private def valueCallCode : Array UInt8 :=
  #[0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x01, 0x60, 0xc3, 0x61, 0x75, 0x30, 0xf1, 0x00]

private def identityCallCode : Array UInt8 :=
  #[0x5f, 0x5f, 0x5f, 0x5f, 0x5f, 0x60, 0x04, 0x5f, 0xf1, 0x00]

private def writeCode : Array UInt8 := #[0x60, 0x01, 0x60, 0x00, 0x55, 0x00]

private def clzWriteCode : Array UInt8 := #[0x5f, 0x1e, 0x5f, 0x55, 0x00]

private def testWorld (parentCode : Array UInt8) (balance : Nat)
    (childCode : Array UInt8 := #[]) : TxWorld :=
  beginTransaction fun addr =>
    if addr == 0xc1 then { code := parentCode, balance := balance }
    else if addr == 0xc3 then { code := childCode }
    else {}

private def runInContext (world : TxWorld) (readOnly : Bool) (profile : Profile) :
    CallOpcode.Outcome :=
  let parent := { frameInput world 0xc1 100000 with readOnly, profile }
  CallOpcode.settle world parent (CallOpcode.execute 100 world 0xc1 parent)

private def selfCall :=
  CallOpcode.run 100 (testWorld selfCallCode 1) 0xc1 100000

private def identityCall :=
  CallOpcode.run 100 (testWorld identityCallCode 0) 0xc1 100000

private def staticCall :=
  runInContext (testWorld zeroCallCode 0 writeCode) true .shanghaiPlus

private def mutableCall :=
  runInContext (testWorld zeroCallCode 0 writeCode) false .shanghaiPlus

private def staticValueCall :=
  runInContext (testWorld valueCallCode 1 writeCode) true .shanghaiPlus

private def osakaCall :=
  runInContext (testWorld zeroCallCode 0 clzWriteCode) false .osaka

private def osakaValueCall :=
  runInContext (testWorld valueCallCode 1 clzWriteCode) false .osaka

private def outcomeJSON (address : Nat) : CallOpcode.Outcome → Lean.Json
  | .stopped w s => Lean.Json.mkObj [
      ("status", .str "stopped"),
      ("stack", Lean.toJson (s.stack.items.map (fun word => toString word.val))),
      ("gasRemaining", .str (toString s.gas)),
      ("slot0", .str (toString ((w.accounts address).storage 0))),
      ("parentBalance", .str (toString (w.accounts 0xc1).balance))]
  | .indeterminate reason =>
    Lean.Json.mkObj [("status", .str "indeterminate"), ("reason", .str (reprStr reason))]
  | .exceptional _ _ reason =>
    Lean.Json.mkObj [("status", .str "exceptional"), ("reason", .str (reprStr reason))]
  | .reverted _ _ => Lean.Json.mkObj [("status", .str "reverted")]
  | .returned _ _ => Lean.Json.mkObj [("status", .str "returned")]

def observations : Lean.Json :=
  Lean.Json.mkObj [
    ("self-call", outcomeJSON 0xc1 selfCall),
    ("identity-zero-gas", outcomeJSON 0x04 identityCall),
    ("static-parent", outcomeJSON 0xc3 staticCall),
    ("mutable-parent", outcomeJSON 0xc3 mutableCall),
    ("osaka-child", outcomeJSON 0xc3 osakaCall),
    ("osaka-child-with-value", outcomeJSON 0xc3 osakaValueCall)]

-- Guards for the exact reproducers and adjacent supported paths.
private def stoppedWith (result : CallOpcode.Outcome) (address bit value : Nat)
    (isWarm : Bool) : Bool :=
  match result with
  | .stopped w s =>
    s.stack.items.map (·.val) == [bit] &&
      ((w.accounts address).storage 0 == value) &&
      (w.warmSlots address 0 == isWarm) && (w.original address 0 == 0)
  | _ => false

#guard stoppedWith selfCall 0xc1 1 42 true
#guard stoppedWith staticCall 0xc3 0 0 false
#guard stoppedWith mutableCall 0xc3 1 1 true
#guard stoppedWith osakaCall 0xc3 1 256 true
#guard stoppedWith osakaValueCall 0xc3 1 256 true
#guard match staticValueCall with
  | .exceptional w s .writeProtection =>
    s.gas == 0 && (w.accounts 0xc1).balance == 1 && (w.accounts 0xc3).balance == 0
  | _ => false
-- Zero forwarded gas reaches the precompile, whose 15-gas base cost
-- produces a soft CALL failure, not an unsupported-operation refusal.
#guard match identityCall with
  | .stopped w s =>
    s.stack.items.map (·.val) == [0] && s.returnData.size == 0 &&
    w.warmAddresses 4 && (w.accounts 0xc1).balance == 0
  | _ => false

private def fundedWorld := testWorld #[] 1

#guard match WorldCall.callZeroValue 100 fundedWorld 0x04 100000 0 with
  | .unsupported .unsupportedFork => true
  | _ => false
#guard match WorldCall.callWithValue 100 fundedWorld 0xc1 0x04 100000 0 1 with
  | .indeterminate .unsupportedFork => true
  | _ => false

#guard WorldCall.unsupportedPrecompile .preShanghai 0x09
#guard !WorldCall.unsupportedPrecompile .preShanghai 0x0a
#guard WorldCall.unsupportedPrecompile .shanghaiPlus 0x11
#guard !WorldCall.unsupportedPrecompile .shanghaiPlus 0x12
#guard !WorldCall.unsupportedPrecompile .shanghaiPlus 0x100
#guard WorldCall.unsupportedPrecompile .osaka 0x100
#guard !WorldCall.unsupportedPrecompile .osaka 0x101

end EVMCleanroom.CallBoundaryTests
