/-
L4Factoidal.Crypto.DhNative — finite-field Diffie-Hellman arithmetic through
HACL* (`Hacl_Bignum64_mod_exp_consttime`, `ffi/hacl_rsa.c`
`l4_hacl_dh_modexp`), for XML Encryption 1.1 §5.6.3 (`xmlenc11#dh-es`).

`modExp p x y` is `y^x mod p` as `|p|` big-endian octets (RFC 2631 §2.1.1:
`ZZ = g^(xb*xa) mod p`, the length of `p`), constant time over `x`. The
same C entry is in the native library and in the Wasm build (the file
`ffi/hacl_rsa.c` is linked in both), so the arithmetic is HACL*'s on every
target.

`modExpSpec` is the specification: the same value from Lean's `Nat`. It is
a definition for theorems only; it is never run (`y ^ x` of a 1024-bit `x`
has no representation). `ModExpAgrees` states, as a hypothesis, HACL*'s
functional correctness for this entry, in the same way as
`WebHacl.HashAgrees` does for the hashes.

No `sorry`, no `axiom`, no `partial`.
-/

namespace L4Factoidal.Crypto.Dh

/-- `y^x mod p` (HACL*), or the empty array for every refusal: `|p|` not 128
to 512 octets or not a multiple of 8, `|y| ≠ |p|`, `x` empty or longer than
`p`, an even `p`, `y ≥ p`, an allocation failure. -/
@[extern "l4_hacl_dh_modexp"]
opaque modExpRaw (p : @& ByteArray) (x : @& ByteArray) (y : @& ByteArray) : ByteArray

/-- `modExpRaw` with the empty-means-refusal convention read into `Option`. -/
def modExp (p x y : ByteArray) : Option ByteArray :=
  let r := modExpRaw p x y
  if r.size == 0 then none else some r

/-- Big-endian octets to a number (OS2IP, RFC 8017 §4.2). -/
def natOfBytes (b : ByteArray) : Nat := b.foldl (fun acc v => acc * 256 + v.toNat) 0

/-- The `k` low octets of `n`, big-endian (I2OSP, RFC 8017 §4.1, without
the length check); a tail call per octet. -/
def bytesOfNatLoop (n : Nat) : (fuel : Nat) → List UInt8 → List UInt8
  | 0, acc => acc
  | f + 1, acc => bytesOfNatLoop (n / 256) f ((n % 256).toUInt8 :: acc)

def bytesOfNat (k n : Nat) : ByteArray := ⟨(bytesOfNatLoop n k []).toArray⟩

theorem bytesOfNatLoop_length (n f : Nat) (acc : List UInt8) :
    (bytesOfNatLoop n f acc).length = f + acc.length := by
  induction f generalizing n acc with
  | zero => simp [bytesOfNatLoop]
  | succ f ih => simp [bytesOfNatLoop, ih]; omega

/-- I2OSP gives `k` octets. -/
theorem bytesOfNat_size (k n : Nat) : (bytesOfNat k n).size = k := by
  simp [bytesOfNat, ByteArray.size, bytesOfNatLoop_length]

/-- The specification of `modExp`: `y^x mod p` as `|p|` octets. For theorems
only; never evaluated. -/
def modExpSpec (p x y : ByteArray) : ByteArray :=
  bytesOfNat p.size (natOfBytes y ^ natOfBytes x % natOfBytes p)

/-- HACL*'s functional correctness for `l4_hacl_dh_modexp`, as a hypothesis:
when the entry answers, its answer is the specification. -/
def ModExpAgrees : Prop := ∀ p x y r, modExp p x y = some r → r = modExpSpec p x y

end L4Factoidal.Crypto.Dh
