import EVMCleanroom.Frame

/-!
Executable single-frame outcome regressions. These #guard statements are
checked by Lean, but are not external EELS conformance fixtures.
-/

namespace EVMCleanroom.FrameTests

private def initial (code : Array UInt8) (gas : Nat := 30000)
    (original : Nat := 0) : State :=
  { code := code, gas := gas, storage := Storage.withInitial 0 original }

private def revertedValue (outcome : Frame.Outcome) : Option Nat :=
  match outcome with
  | .reverted s _ _ => some (s.storage.current 0)
  | _ => none

private def revertedRefund (outcome : Frame.Outcome) : Option Int :=
  match outcome with
  | .reverted s _ _ => some s.storage.refund
  | _ => none

private def revertedGas (outcome : Frame.Outcome) : Option Nat :=
  match outcome with
  | .reverted s _ _ => some s.gas
  | _ => none

private def returnedValue (outcome : Frame.Outcome) : Option Nat :=
  match outcome with
  | .returned s _ _ => some (s.storage.current 0)
  | _ => none

private def returnedByte (outcome : Frame.Outcome) : Option Nat :=
  match outcome with
  | .returned s offset length =>
    if length == 1 then some (s.memory.readByte offset).toNat else none
  | _ => none

private def exceptionalGas (outcome : Frame.Outcome) : Option Nat :=
  match outcome with
  | .exceptional s _ => some s.gas
  | _ => none

private def exceptionalValue (outcome : Frame.Outcome) : Option Nat :=
  match outcome with
  | .exceptional s _ => some (s.storage.current 0)
  | _ => none

private def isUnsupported (outcome : Frame.Outcome) : Bool :=
  match outcome with
  | .unsupported _ => true
  | _ => false

-- Two successful writes in the same frame are visible to RETURN.
private def returnAfterWrite :=
  Frame.run 12 (initial #[0x60,0x01,0x60,0x00,0x55,
                          0x60,0x00,0x60,0x00,0xf3])
#guard returnedValue returnAfterWrite == some 1

-- Exactly the same bytecode prefix with REVERT leaves *no* stored change.
private def revertAfterWrite :=
  Frame.run 12 (initial #[0x60,0x01,0x60,0x00,0x55,
                          0x60,0x00,0x60,0x00,0xfd])
#guard revertedValue revertAfterWrite == some 0
#guard revertedRefund revertAfterWrite == some 0
#guard revertedGas revertAfterWrite == some 7888

-- Reverting a clear restores the previous nonzero value and counter.
private def revertAfterClear :=
  Frame.run 12 (initial #[0x60,0x00,0x60,0x00,0x55,
                          0x60,0x00,0x60,0x00,0xfd] 30000 7)
#guard revertedValue revertAfterClear == some 7
#guard revertedRefund revertAfterClear == some 0

-- RETURN returns the supplied memory byte after an MSTORE8.
private def returnOneByte :=
  Frame.run 12 (initial #[0x60,0x2a,0x60,0x00,0x53,
                          0x60,0x01,0x60,0x00,0xf3])
#guard returnedByte returnOneByte == some 42

-- Failed execution after a successful SSTORE consumes remaining gas and
-- cannot commit the first write.
private def outOfGasAfterWrite :=
  Frame.run 12 (initial #[0x60,0x01,0x60,0x00,0x55,
                          0x60,0x01,0x60,0x00,0x55] 23000)
#guard exceptionalGas outOfGasAfterWrite == some 0
#guard exceptionalValue outOfGasAfterWrite == some 0

-- Exhausted simulation fuel and unknown valid opcodes never masquerade
-- as Ethereum consensus-invalid outcomes.
#guard isUnsupported (Frame.run 1 (initial #[0x60,0x01,0x00]))
#guard isUnsupported (Frame.run 1 (initial #[0xf1,0x00]))

end EVMCleanroom.FrameTests
