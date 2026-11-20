import EVMCleanroom.Call
import EVMCleanroom.ReturnData

/-!
# CALL with a first-class EIP-211 return-data buffer

An extension of the established zero-value CALL scheduler, retaining the
child's byte-addressed memory long enough to extract its actual RETURN or
REVERT bytes. Storage and refunds commit only on successful child completion.
RETURN/REVERT both refund the child's remaining gas to its parent; an
exception returns zero remaining gas and no return data.

This module is still a one-level, zero-value, no-input call engine. It does
not implement ordinary CALL's output-memory copy arguments, value stipends,
precompiles, or nested/reentrant depth. Oversized returned data is UNSUPPORTED.
-/

namespace EVMCleanroom.WorldCallData

open EVMCleanroom.World

inductive Outcome where
  | childSuccess (world : TxWorld) (parentGasRemaining : Nat)
      (returnData : Array UInt8)
  | childReverted (world : TxWorld) (parentGasRemaining : Nat)
      (returnData : Array UInt8)
  | childExceptional (world : TxWorld) (parentGasRemaining : Nat)
      (reason : Error)
  | callerOutOfGas
  | invalidAddress
  | invalidChildGas
  | unsupported (why : String)

def callZeroValue (fuel : Nat) (w : TxWorld)
    (target parentGas requestedGas : Nat) : Outcome :=
  if target ≥ addressBound then .invalidAddress
  else
    match CallGas.schedule parentGas requestedGas (w.warmAddresses target) with
    | .error .outOfGas => .callerOutOfGas
    | .error _ => .unsupported "unimplemented-address-price"
    | .ok b =>
      let warmed := WorldCall.warmTarget w target
      match Frame.run fuel (frameInput warmed target b.forwarded) with
      | .stopped out =>
        if out.gas ≤ b.forwarded then
          .childSuccess (commitFrame warmed target out)
            (b.reserve + out.gas) #[]
        else .invalidChildGas
      | .returned out offset length =>
        if out.gas > b.forwarded then .invalidChildGas
        else
          match ReturnData.capture out offset length with
          | none => .unsupported "return-data-over-4096"
          | some bytes =>
            .childSuccess (commitFrame warmed target out)
              (b.reserve + out.gas) bytes
      | .reverted out offset length =>
        if out.gas > b.forwarded then .invalidChildGas
        else
          match ReturnData.capture out offset length with
          | none => .unsupported "revert-data-over-4096"
          | some bytes => .childReverted warmed (b.reserve + out.gas) bytes
      | .exceptional out error =>
        if out.gas ≤ b.forwarded then
          .childExceptional warmed (b.reserve + out.gas) error
        else .invalidChildGas
      | .unsupported _ => .unsupported "unimplemented-child-opcode"

end EVMCleanroom.WorldCallData
