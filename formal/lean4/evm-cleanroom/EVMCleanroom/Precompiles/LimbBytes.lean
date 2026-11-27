import EVMCleanroom.Precompiles.Limb
import EVMCleanroom.Precompiles.Basic

/-!
# Limbs from and to big-endian bytes

The fast precompile paths read field elements straight into 64-bit limbs and
write results from limbs, without a `Nat` in between. Reads use `byteAt`, so
bytes beyond the end of the input count as zero, as in `beNat`.

Proved here: output lengths. The values are tested against `beNat` and
`natToBE` by the guards below and by the differential runs of `evm-blsops`.
-/

namespace EVMCleanroom.Precompiles

/-- Eight bytes at `off` as one big-endian limb. -/
@[inline] def be64 (b : ByteArray) (off : Nat) : UInt64 :=
  ((byteAt b off).toUInt64 <<< 56) ||| ((byteAt b (off + 1)).toUInt64 <<< 48) |||
  ((byteAt b (off + 2)).toUInt64 <<< 40) ||| ((byteAt b (off + 3)).toUInt64 <<< 32) |||
  ((byteAt b (off + 4)).toUInt64 <<< 24) ||| ((byteAt b (off + 5)).toUInt64 <<< 16) |||
  ((byteAt b (off + 6)).toUInt64 <<< 8) ||| (byteAt b (off + 7)).toUInt64

/-- Append one limb as eight big-endian bytes. -/
def pushBE64 (acc : ByteArray) (x : UInt64) : ByteArray :=
  ((((((((acc.push (x >>> 56).toUInt8).push (x >>> 48).toUInt8).push (x >>> 40).toUInt8).push
    (x >>> 32).toUInt8).push (x >>> 24).toUInt8).push (x >>> 16).toUInt8).push (x >>> 8).toUInt8).push
    x.toUInt8)

/-- Kind: length.
    Says: appending a limb adds exactly eight bytes.
    Does not say: which bytes. -/
theorem pushBE64_size (acc : ByteArray) (x : UInt64) : (pushBE64 acc x).size = acc.size + 8 := by
  simp only [pushBE64, ByteArray.size_push] <;> omega

/-- 32 big-endian bytes at `off` as four limbs. -/
@[inline] def U256.ofBE (b : ByteArray) (off : Nat) : U256 :=
  ⟨be64 b (off + 24), be64 b (off + 16), be64 b (off + 8), be64 b off⟩

/-- 48 big-endian bytes at `off` as six limbs. -/
@[inline] def U384.ofBE (b : ByteArray) (off : Nat) : U384 :=
  ⟨be64 b (off + 40), be64 b (off + 32), be64 b (off + 24), be64 b (off + 16), be64 b (off + 8), be64 b off⟩

/-- Append four limbs as 32 big-endian bytes. -/
def U256.pushBE (acc : ByteArray) (a : U256) : ByteArray :=
  pushBE64 (pushBE64 (pushBE64 (pushBE64 acc a.l3) a.l2) a.l1) a.l0

/-- Append six limbs as 48 big-endian bytes. -/
def U384.pushBE (acc : ByteArray) (a : U384) : ByteArray :=
  pushBE64 (pushBE64 (pushBE64 (pushBE64 (pushBE64 (pushBE64 acc a.l5) a.l4) a.l3) a.l2) a.l1) a.l0

/-- Kind: length.
    Says: four limbs are written as exactly 32 bytes, six limbs as exactly 48.
    Does not say: which bytes. -/
theorem U256.pushBE_size (acc : ByteArray) (a : U256) : (U256.pushBE acc a).size = acc.size + 32 := by
  simp only [U256.pushBE, pushBE64_size] <;> omega

theorem U384.pushBE_size (acc : ByteArray) (a : U384) : (U384.pushBE acc a).size = acc.size + 48 := by
  simp only [U384.pushBE, pushBE64_size] <;> omega

/-- `a < b` as unsigned 256-bit numbers: the borrow of `a − b`. -/
@[inline] def U256.lt (a b : U256) : Bool := (U256.subBorrow a b).1 != 0

/-- `a < b` as unsigned 384-bit numbers. -/
@[inline] def U384.lt (a b : U384) : Bool := (U384.subBorrow a b).1 != 0

/-- Equality of two precompile bodies, bytes included (test helper). -/
def Body.same : Body → Body → Bool
  | .output a, .output b => a.data == b.data
  | .invalid, .invalid => true
  | .refuse, .refuse => true
  | _, _ => false

/-- Equality of two precompile results, bytes and gas included (test helper). -/
def Result.same : Result → Result → Bool
  | .success a g, .success b h => a.data == b.data && g == h
  | .failure, .failure => true
  | .refusal, .refusal => true
  | _, _ => false

private def sample : ByteArray := hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f3031"

#guard (U256.ofBE sample 0).toNat == beNat sample 0 32 && (U256.ofBE sample 7).toNat == beNat sample 7 32
#guard (U256.ofBE sample 30).toNat == beNat sample 30 32 && (U384.ofBE sample 2).toNat == beNat sample 2 48
#guard (U384.ofBE sample 40).toNat == beNat sample 40 48
#guard (U256.pushBE ByteArray.empty (U256.ofBE sample 3)).data == (natToBE 32 (beNat sample 3 32)).data
#guard (U384.pushBE ByteArray.empty (U384.ofBE sample 1)).data == (natToBE 48 (beNat sample 1 48)).data
#guard U256.lt (U256.ofNat 5) (U256.ofNat 6) && !U256.lt (U256.ofNat 6) (U256.ofNat 6) &&
  !U256.lt (U256.ofNat (2 ^ 200)) (U256.ofNat 6) && U256.lt (U256.ofNat (2 ^ 200)) (U256.ofNat (2 ^ 200 + 1))
#guard U384.lt (U384.ofNat (2 ^ 380)) (U384.ofNat (2 ^ 380 + 2 ^ 64)) && !U384.lt (U384.ofNat (2 ^ 383)) (U384.ofNat 1)

#print axioms pushBE64_size
#print axioms U256.pushBE_size
#print axioms U384.pushBE_size

end EVMCleanroom.Precompiles
