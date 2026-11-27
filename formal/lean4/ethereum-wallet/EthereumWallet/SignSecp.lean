import EVMCleanroom.Precompiles.Secp256k1
import EVMCleanroom.Keccak

/-!
# secp256k1 for signing: secret-scalar base multiplication, verification, addresses

Point arithmetic is the shared module `EVMCleanroom.Precompiles.Secp256k1`
(with `Curve`, `Field`, `Basic`), owned by the precompile work; nothing here
is a second implementation of point addition. This module adds what a signer
needs on top of it:

* `BaseTable` and `mulBaseSecret`: `[k]G` for a secret `k` on a fixed schedule
  of 64 point additions from a precomputed table (a comb with 4-bit windows),
  starting from a fixed public point. There is no doubling chain and no branch
  on a bit of `k` in this module; the digits are recoded so that no table entry
  is the point at infinity, and the public starting point keeps the running
  sum away from the entry being added (they coincide, and the shared `add`
  takes its doubling branch, only for scalars whose recoded value matches one
  exact number of about 250 bits);
* `invFixed`: modular inverse by a fixed public exponent (Fermat), in place of
  Euclid's algorithm whose step count depends on the secret operand;
* `verify`: ECDSA verification on public data;
* `keccak256`, `addressOf`: the Ethereum address of a public key.

**Not constant-time.** Field elements are Lean `Nat` (GMP numbers): the time
of a multiplication or reduction depends on the operands, small values take a
different representation, the shared `Curve.add` branches on special cases,
and the table lookup indexes memory by a secret digit. The fixed schedule
removes the largest leak (the bit pattern and bit length of the nonce) and no
more than that. The analysis is in
`docs/designissues/2026-11-27-ethereum-wallet-signing.md`; callers accept the
risk by name (`Risk.dangerouslyAccept`).

Proved here: range and on-curve facts that hold by a run-time check. Not
proved: any group law, or that `mulBaseSecret` returns the multiple (tested
against the shared double-and-add `mulBase` and published vectors).
-/

namespace EthereumWallet

/-- Risks a caller of this package accepts by name (skills/lean-risk-flags). -/
inductive Risk where
  /-- Signing whose running time and memory access depend on the secret key and nonce. -/
  | variableTimeSigning
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`; only `Risk.dangerouslyAccept` makes one. -/
structure Risk.Accepted (r : Risk) : Type where
  private mk ::

def Risk.dangerouslyAccept (r : Risk) : Risk.Accepted r := ⟨⟩

namespace Secp

open EVMCleanroom
open EVMCleanroom.Precompiles
open EVMCleanroom.Precompiles.Secp256k1 (p n field generator)

/-- Big-endian value of a byte string. -/
def bytesToNat (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Keccak-256 (the evm-cleanroom implementation: tested against published vectors, not proved). -/
def keccak256 (b : ByteArray) : ByteArray :=
  ⟨(Keccak.digest (ByteView.ofArray b.data)).toArray⟩

/-- The address of a public key: the low 160 bits of Keccak-256 of `x ‖ y`. -/
def addressOf (x y : Nat) : Nat :=
  bytesToNat (keccak256 (natToBE 32 x ++ natToBE 32 y)) % 2 ^ 160

/-- Inverse modulo a prime `m` by the fixed public exponent `m - 2`. Zero maps to zero. -/
def invFixed (m a : Nat) : Nat := Fp.pow m a (m - 2)

/-- One row of the comb table: `B, 2B, …, 16B` appended to `acc`. -/
def combRow (base : JPoint Nat) : Nat → JPoint Nat → Array (JPoint Nat) → Array (JPoint Nat)
  | 0, _, acc => acc
  | k+1, cur, acc => combRow base k (Curve.add field cur base) (acc.push cur)

/-- Rows for the bases `G, 16G, 16²G, …`: the last entry of a row is the next base. -/
def combBuild : Nat → JPoint Nat → Array (JPoint Nat) → Array (JPoint Nat)
  | 0, _, acc => acc
  | w+1, base, acc =>
    let row := combRow base 16 base acc
    combBuild w (row.getD (row.size - 1) base) row

/-- The precomputed multiples of the generator: entry `16·i + d` is `(d+1)·16^i·G`.
    Public data. Built once by the caller (about a thousand point additions). -/
structure BaseTable where
  entries : Array (JPoint Nat)
  /-- `[combStart]G`, the public point every multiplication starts from. -/
  start : JPoint Nat

/-- The public scalar of the starting point. With the running sum always above `2^255`
    and every table entry's scalar at most `2^256`, the sum and the entry added to it can
    only coincide (up to sign) for one exact value of the digits consumed so far. -/
def combStart : Nat := 2 ^ 255

def BaseTable.build (_ : Unit) : BaseTable :=
  ⟨combBuild 64 generator (Array.mkEmpty 1024), Curve.mul field combStart generator⟩

/-- `combStart + Σ 16^i` for `i < 64`, reduced: what the recoded digits and the starting
    point add to the scalar. -/
def combOffset : Nat := (combStart + (16 ^ 64 - 1) / 15) % n

def combLoop (t : BaseTable) (k : Nat) : Nat → Nat → JPoint Nat → JPoint Nat
  | 0, _, acc => acc
  | rem+1, i, acc =>
    combLoop t k rem (i + 1)
      (Curve.add field acc (t.entries.getD (16 * i + (k >>> (4 * i)) % 16) generator))

/-- `[k]G` in Jacobian form by 64 additions of table entries to the starting point. With
    `k' = k − combOffset (mod n)` and base-16 digits `d_i` of `k'`, the start and the
    entries `(d_i + 1)·16^i·G` sum to `(k' + combOffset)·G = k·G`. -/
def mulBaseComb (t : BaseTable) (k : Nat) : JPoint Nat :=
  combLoop t ((k % n + n - combOffset) % n) 64 0 t.start

/-- An affine pair, kept only if it satisfies the curve equation. -/
def keepOnCurve (x y : Nat) : Option (Nat × Nat) :=
  if Secp256k1.onCurve x y then some (x, y) else none

theorem keepOnCurve_some (a b x y : Nat) (h : keepOnCurve a b = some (x, y)) :
    Secp256k1.onCurve x y = true := by
  unfold keepOnCurve at h
  split at h
  · rename_i hCurve
    cases h
    exact hCurve
  · cases h

/-- Affine coordinates with the inverse taken by fixed exponent; kept only if on the curve. -/
def toAffineFixed (point : JPoint Nat) : Option (Nat × Nat) :=
  if point.z = 0 then none
  else
    let zi := invFixed p point.z
    let zi2 := zi * zi % p
    let x := point.x * zi2 % p
    let y := point.y * (zi2 * zi % p) % p
    keepOnCurve x y

/-- `[k]G` for a secret scalar, affine; `none` for the point at infinity or a failed curve check. -/
def mulBaseSecret (t : BaseTable) (k : Nat) : Option (Nat × Nat) :=
  toAffineFixed (mulBaseComb t k)

/-- ECDSA verification (SEC 1, section 4.1.4) of `(r, s)` on message hash `z` for public key `q`. -/
def verify (z r s : Nat) (q : Nat × Nat) : Bool :=
  if r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s then false
  else if !Secp256k1.onCurve q.1 q.2 then false
  else
    let w := Secp256k1.scalarInv s
    match Secp256k1.mulAdd (z % n * w % n) (r * w % n) q with
    | none => false
    | some point => point.1 % n == r

/-- Kind: on-curve preservation (checked at run time).
    Says: a point returned by `mulBaseSecret` has canonical coordinates and satisfies the
    curve equation, whatever table was supplied.
    Does not say: it is `[k]G` (tested against the shared `mulBase`, not proved). -/
theorem mulBaseSecret_onCurve (t : BaseTable) (k x y : Nat)
    (h : mulBaseSecret t k = some (x, y)) : Secp256k1.onCurve x y = true := by
  unfold mulBaseSecret toAffineFixed at h
  split at h
  · cases h
  · exact keepOnCurve_some _ _ _ _ h

/-- Kind: range check.
    Says: verification refuses `r` or `s` outside `[1, n-1]`.
    Does not say: in-range signatures verify. -/
theorem verify_range (z r s : Nat) (q : Nat × Nat) (h : r = 0 ∨ n ≤ r ∨ s = 0 ∨ n ≤ s) :
    verify z r s q = false := by
  simp [verify, h]

#print axioms mulBaseSecret_onCurve
#print axioms verify_range

end Secp

end EthereumWallet
