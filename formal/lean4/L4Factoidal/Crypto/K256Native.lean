/-
L4Factoidal.Crypto.K256Native — ECDSA over secp256k1 (SEC 2 section 2.4.1)
bound to HACL* through Lean's C FFI: key check, public key, recoverable
signing with an RFC 6979 nonce and low-S normalisation (EIP-2), and low-S
verification. For Ethereum transaction and message signing.

## Decision

Owner, 2026-11-27, verbatim: "HACL* is both approved and PREFERED over our own
(crazy yolo roll your own etc.) Lean hackery." and, on a HACL* secp256k1 signer
for Ethereum, "Do it." Recorded in CLAUDE.md. Design record:
`docs/designissues/2026-11-27-bignum-timing-and-aes.md`.

## Secret keys are an opaque type (layer 1 of that record, section 6)

`SecretKey` has a private constructor and a private field. Outside this file no
code can read its bytes, build one except through `SecretKey.ofBytes?`, or
compare, print or hash one: it has no `DecidableEq`, `BEq`, `Repr`, `ToString`
or `Hashable` instance, and the `#check_failure` lines at the end of this file
fail the build if one appears. So the only operations on a key are the HACL*
calls below, and Lean `Nat` arithmetic can never be applied to it.
`tools/secret-type-gate.py` checks the same rules from the source text.

Does not say: that the compiled code is constant time. The HACL* functions carry
that property from their F*/Low* proofs (secret integer types: no branch and no
memory address depends on a secret), with the C compiler trusted. The shim
`ffi/hacl_k256.c` is checked by the Valgrind test `tests/ct/run.sh valgrind`.
Copies of key bytes in the Lean heap are not erased.

## Trust statement

The four externs are `opaque`: no theorem in this tree depends on what they
compute. What is trusted: HACL* `Hacl_K256_ECDSA.c`, `Hacl_EC_K256.c`,
`Hacl_HMAC_DRBG.c` (vendored unmodified, hacl-star commit
f557259007db9933442dde10aa995c1b00bd3446, `third_party/hacl/PROVENANCE.md`), and
`ffi/hacl_k256.c` (length checks, the RFC 6979 retry loop, the recovery id from
the parity of y(R)). Run-time vectors: `lake exe l4k256-probe` (the EIP-155
example, the generator, verification and refusals).

## Contract

  * `SecretKey.ofBytes? b`: `some` exactly when `b` is 32 bytes and
    0 < b < n (big-endian); HACL* decides.
  * `SecretKey.publicKey k`: `x || y`, 64 bytes.
  * `signHash k h`: for a 32-byte hash `h`, the signature of `h mod n` with
    the RFC 6979 nonce, `s` in the low half, and the recovery id (the parity of
    y(R) after normalisation). `none` for a hash of another length, and when
    x(R) is not less than n (probability about 2^-128).
  * `verifyLowS h pub sig`: HACL*'s verification; refuses a high-S signature.
-/
namespace L4Factoidal.Crypto.K256

/-- The order of the secp256k1 group (SEC 2 section 2.4.1). Public. -/
def n : Nat := 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141

/-- A secp256k1 private key. Opaque: see the module comment. -/
structure SecretKey where
  private mk ::
  private bytes : ByteArray

@[extern "l4_hacl_k256_private_key_valid"]
private opaque privateKeyValid (sk : @& ByteArray) : Bool

@[extern "l4_hacl_k256_secret_to_public"]
private opaque secretToPublic (sk : @& ByteArray) : ByteArray

@[extern "l4_hacl_k256_sign_recoverable"]
private opaque signRecoverable (z : @& ByteArray) (sk : @& ByteArray) : ByteArray

/-- HACL* `secp256k1_ecdsa_verify_hashed_msg`: `true` only for a 32-byte hash, a
64-byte valid public key `x || y`, and a 64-byte low-S signature `r || s` that
verifies. Public inputs only. -/
@[extern "l4_hacl_k256_verify"]
opaque verifyLowS (z : @& ByteArray) (pub : @& ByteArray) (sig : @& ByteArray) : Bool

/-- The only way to make a `SecretKey`. -/
def SecretKey.ofBytes? (b : ByteArray) : Option SecretKey :=
  if b.size == 32 && privateKeyValid b then some ⟨b⟩ else none

/-- The public key `x || y` (64 bytes). -/
def SecretKey.publicKey (k : SecretKey) : ByteArray := secretToPublic k.bytes

/-- A recoverable signature. All fields are public. -/
structure RecoverableSig where
  r : ByteArray
  s : ByteArray
  recid : UInt8

/-- Big-endian bytes to a number. For PUBLIC data only (a hash). -/
def beToNat (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- A number below 2^256 as 32 big-endian bytes. For PUBLIC data only. -/
def natTo32 (v : Nat) : ByteArray :=
  ByteArray.mk ((List.range 32).map (fun i => UInt8.ofNat (v / 256 ^ (31 - i) % 256))).toArray

/-- `h1 mod n` as 32 bytes: bits2octets of RFC 6979 section 2.3.4, and the
integer that ECDSA signs. The hash is public, so `Nat` arithmetic is allowed. -/
def reduceHash (h : ByteArray) : ByteArray := natTo32 (beToNat h % n)

/-- Sign a 32-byte hash. See the contract in the module comment. -/
def signHash (k : SecretKey) (h : ByteArray) : Option RecoverableSig :=
  if h.size != 32 then none else
  let out := signRecoverable (reduceHash h) k.bytes
  if out.size != 65 then none else
  some { r := out.extract 0 32, s := out.extract 32 64, recid := out.get! 64 }

/-- The 64-byte `r || s` form. -/
def RecoverableSig.compact (sig : RecoverableSig) : ByteArray := sig.r ++ sig.s

/-- Ethereum `v` before EIP-155: 27 + recovery id. -/
def RecoverableSig.vLegacy (sig : RecoverableSig) : Nat := 27 + sig.recid.toNat

/-- Ethereum `v` of EIP-155: chain id * 2 + 35 + recovery id. -/
def RecoverableSig.vEip155 (sig : RecoverableSig) (chainId : Nat) : Nat :=
  chainId * 2 + 35 + sig.recid.toNat

#guard natTo32 0x0102 == ByteArray.mk (Array.replicate 30 0 ++ #[1, 2])
#guard beToNat (natTo32 n) == n
#guard reduceHash (natTo32 (n + 5)) == natTo32 5
#guard ({ r := .empty, s := .empty, recid := 0 } : RecoverableSig).vEip155 1 == 37

/-! Build-time checks that `SecretKey` cannot be compared, printed or hashed.
`#check_failure` fails the build when the term elaborates; `#guard_msgs (drop info)`
keeps its report out of the build log. -/
#guard_msgs (drop info) in
#check_failure (fun (a b : SecretKey) => decide (a = b))
#guard_msgs (drop info) in
#check_failure (fun (a b : SecretKey) => a == b)
#guard_msgs (drop info) in
#check_failure (fun (a : SecretKey) => toString a)
#guard_msgs (drop info) in
#check_failure (fun (a : SecretKey) => repr a)
#guard_msgs (drop info) in
#check_failure (fun (a : SecretKey) => hash a)
#guard_msgs (drop info) in
#check_failure (fun (a b : SecretKey) => compare a b)

end L4Factoidal.Crypto.K256
