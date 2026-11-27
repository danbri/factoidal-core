import EVMCleanroom.Precompiles.Secp256k1
import EthereumWallet.Keys.Bytes
import EthereumWallet.Keys.Risk

/-
The one place the key modules reach secp256k1 point arithmetic: secret to public
point, `[k]G + Q` (public child derivation) and SEC 1 point encodings.

The arithmetic is the repository's shared module `EVMCleanroom.Precompiles.Secp256k1`
(pure Lean, Jacobian coordinates, every returned point checked against the curve
equation at run time; no group-law proofs; closure: `Precompiles.Curve`, `Field`,
`Basic`). Only this file changes if the curve module changes.

Not constant-time: the scalar multiplication works on `Nat`s, with branches and
big-number timings that depend on the scalar. `pubOfSecret` is that on a secret key,
so it takes the risk token (`Keys/Risk.lean`); `mulBase` and `baseMulAdd` without a
token are for scalars that are public by the protocol (the `I_L` of public child
derivation).
-/

namespace EthereumWallet.Keys.Secp

open EVMCleanroom.Precompiles

/-- The group order. -/
def n : Nat := Secp256k1.n

/-- An affine public point; the point at infinity has no value of this type. -/
structure Pub where
  x : Nat
  y : Nat
  deriving DecidableEq, Repr

def ofPair (q : Nat × Nat) : Pub := ⟨q.1, q.2⟩

/-- `k·G` for a scalar `0 < k < n` that is public by the protocol; `none` outside that
range or when the curve module refuses. Variable-time. -/
def mulBase (k : Nat) : Option Pub :=
  if k = 0 ∨ n ≤ k then none
  else (Secp256k1.mulBase k).map ofPair

/-- The public point of a secret key `0 < k < n`. Variable-time in the key: the caller
accepts that by passing the token. -/
def pubOfSecret (_ : SecretRisk) (k : Nat) : Option Pub := mulBase k

/-- `k·G + q` for a public scalar `0 < k < n`; `none` when the sum is the point at
infinity or `k` is out of range. -/
def baseMulAdd (k : Nat) (q : Pub) : Option Pub :=
  if k = 0 ∨ n ≤ k then none
  else (Secp256k1.mulAdd k 1 (q.x, q.y)).map ofPair

def onCurve (a : Pub) : Bool := Secp256k1.onCurve a.x a.y

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
    else (Secp256k1.liftX (bytesToNatBE (b.extract 1 33)) (tag.toNat - 2)).map ofPair

/-- Kind: refusal.
    Says: a zero scalar or one at or above the group order has no public key here.
    Does not say: that every scalar in range yields a point (the arithmetic may refuse). -/
theorem mulBase_out_of_range (k : Nat) (h : k = 0 ∨ n ≤ k) : mulBase k = none := by
  unfold mulBase
  rw [if_pos h]

/-- Kind: refusal. Says: the same for a secret key. -/
theorem pubOfSecret_out_of_range (risk : SecretRisk) (k : Nat) (h : k = 0 ∨ n ≤ k) :
    pubOfSecret risk k = none := mulBase_out_of_range k h

/-- Kind: on-curve (checked at run time by the curve module).
    Says: a public point derived from a key satisfies the curve equation with canonical
    coordinates.
    Does not say: that it is `k·G` in the group (no group law is proved; vectors test it). -/
theorem mulBase_onCurve (k : Nat) (q : Pub) (h : mulBase k = some q) : onCurve q = true := by
  unfold mulBase at h
  by_cases hk : k = 0 ∨ n ≤ k
  · rw [if_pos hk] at h; cases h
  · rw [if_neg hk] at h
    cases hm : Secp256k1.mulBase k with
    | none => rw [hm] at h; cases h
    | some pair =>
      rw [hm] at h
      cases pair with
      | mk x y =>
        have hq : q = ⟨x, y⟩ := by injection h with h; exact h.symm
        subst hq
        exact Secp256k1.mulBase_onCurve k x y hm

end EthereumWallet.Keys.Secp

open EthereumWallet.Keys in
#print axioms Secp.mulBase_out_of_range
open EthereumWallet.Keys in
#print axioms Secp.mulBase_onCurve
