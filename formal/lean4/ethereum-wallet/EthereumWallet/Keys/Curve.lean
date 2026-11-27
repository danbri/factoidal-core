import EVMCleanroom.SecpRecovery
import EthereumWallet.Keys.Bytes

/-
The one place the key modules reach secp256k1 point arithmetic: secret to public
point, point addition (public child derivation) and SEC 1 point encodings.

Today this is the affine arithmetic of `EVMCleanroom.SecpRecovery` (pure Lean,
experimental, no group-law proofs, variable-time `Nat`). When the shared fast
secp256k1 module lands, only this file changes.

Not constant-time: `pubOfSecret` runs a double-and-add loop on a `Nat` scalar whose
branches and big-number timings depend on the secret.
-/

namespace EthereumWallet.Keys.Secp

open EVMCleanroom

/-- The group order. -/
def n : Nat := SecpRecovery.n

/-- An affine public point; the point at infinity has no value of this type. -/
structure Pub where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def ofPoint : SecpRecovery.Point → Option Pub
  | .infinity => none
  | .affine x y => some ⟨x, y⟩

/-- `k·G` for a secret scalar `0 < k < n`; `none` outside that range or on an
arithmetic refusal of the underlying module. -/
def pubOfSecret (k : Nat) : Option Pub :=
  if k = 0 ∨ n ≤ k then none
  else (SecpRecovery.mul k SecpRecovery.generator).bind ofPoint

/-- Point addition; `none` when the sum is the point at infinity. -/
def add (a b : Pub) : Option Pub :=
  (SecpRecovery.add (.affine a.x a.y) (.affine b.x b.y)).bind ofPoint

def onCurve (a : Pub) : Bool := SecpRecovery.onCurve (.affine a.x a.y)

/-- SEC 1 compressed encoding: 0x02 or 0x03, then `x` as 32 bytes. -/
def compress (a : Pub) : ByteArray :=
  (ByteArray.empty.push (if a.y % 2 = 0 then 2 else 3)) ++ natToBytesBE a.x 32

/-- `x ‖ y`, 64 bytes: the input of the Ethereum address hash. -/
def xyBytes (a : Pub) : ByteArray := natToBytesBE a.x 32 ++ natToBytesBE a.y 32

/-- Read a SEC 1 compressed point, checking it is on the curve. -/
def decompress? (b : ByteArray) : Option Pub :=
  if b.size ≠ 33 then none
  else
    let tag := b.get! 0
    if tag ≠ 2 ∧ tag ≠ 3 then none
    else
      match SecpRecovery.recoveryPoint (bytesToNatBE (b.extract 1 33)) (tag.toNat - 2) with
      | .ok (.affine x y) => some ⟨x, y⟩
      | _ => none

/-- Kind: refusal.
    Says: a zero scalar or one at or above the group order has no public key here.
    Does not say: that every scalar in range yields a point (the arithmetic may refuse). -/
theorem pubOfSecret_out_of_range (k : Nat) (h : k = 0 ∨ n ≤ k) : pubOfSecret k = none := by
  simp [pubOfSecret, h]

end EthereumWallet.Keys.Secp
