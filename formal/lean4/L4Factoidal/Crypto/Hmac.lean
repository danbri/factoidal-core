/-
L4Factoidal.Crypto.Hmac — HMAC-SHA-256 and HMAC-SHA-512 (RFC 2104, FIPS 198-1) and
PBKDF2-HMAC-SHA-256 (RFC 8018 section 5.2), in pure Lean over the
existing `L4Factoidal.Crypto.sha256`.

WHY THIS IS NOT "ROLLING OUR OWN CRYPTO": `skills/crypto-policy/SKILL.md`
forbids writing new PRIMITIVES. HMAC is not a primitive: RFC 2104 defines
it as two calls to an unmodified hash over a keyed prefix, and PBKDF2 is
an iterated XOR fold of HMAC calls. Neither has any internal state of its
own. The hash under both is `Crypto.sha256`, the existing FIPS 180-4
implementation, whose native HACL* twin `Crypto.sha256Hacl` is checked
against it by `l4vc-probe`. `L4Factoidal/XMPP/README.md` names exactly
this route: "HMAC's construction doesn't need its own native primitive —
add it to `L4Factoidal/Crypto/`, not as an XMPP-local crypto boundary."

The pure hash is used rather than the extern so that the RFC test vectors
at the end of this file are `#guard`s: an `@[extern]` opaque cannot run in
the Lean interpreter, so a vector checked against it would only be a
runtime test, not a build-time one.

Test vectors:
  * HMAC-SHA-256: RFC 4231 section 4 cases 1, 2, 3, 6 and 7.
  * PBKDF2-HMAC-SHA-256: RFC 7914 section 11 and the SCRAM-SHA-256
    worked example of RFC 7677 section 3.

No `sorry`, no `axiom`, no `native_decide`, no `partial`. Every loop is
bounded by an explicit `Nat` count.
-/
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Crypto

/-- The SHA-256 block size in bytes (FIPS 180-4 section 5.1.1). -/
def hmacBlockBytes : Nat := 64

/-- The SHA-256 digest size in bytes. -/
def sha256DigestBytes : Nat := 32

/-- Pad a key to one hash block, hashing it first when it is longer than
a block — RFC 2104's `K0` derivation. -/
def hmacKey0 (key : ByteArray) : ByteArray :=
  let k := if key.size > hmacBlockBytes then sha256 key else key
  let need := hmacBlockBytes - k.size
  k ++ ByteArray.mk (Array.replicate need (0 : UInt8))

private def xorPad (k : ByteArray) (b : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity hmacBlockBytes
  for i in [0:hmacBlockBytes] do
    out := out.push ((k.get! i) ^^^ b)
  return out

/-- HMAC-SHA-256 (RFC 2104): `H((K0 ^ opad) ++ H((K0 ^ ipad) ++ msg))`. -/
def hmacSha256 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacKey0 key
  let inner := sha256 (xorPad k0 0x36 ++ msg)
  sha256 (xorPad k0 0x5c ++ inner)

/-- Byte-wise exclusive-or of two equal-length arrays. A length mismatch
truncates to the shorter, which never happens here: every argument is a
SHA-256 digest. -/
def xorBytes (a b : ByteArray) : ByteArray := Id.run do
  let n := min a.size b.size
  let mut out := ByteArray.emptyWithCapacity n
  for i in [0:n] do
    out := out.push ((a.get! i) ^^^ (b.get! i))
  return out

/-- The four-byte big-endian block index RFC 8018 section 5.2 appends to
the salt (`INT (i)`). -/
def int32BE (n : Nat) : ByteArray :=
  ByteArray.mk #[
    UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat (n % 256)]

/-- The `U_1 xor U_2 xor ... xor U_c` fold for one PBKDF2 output block.
`count` is the remaining iteration count, so the recursion is structural
and no `partial` is needed. -/
def pbkdf2Fold (password : ByteArray) (u acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | count + 1 =>
    let u' := hmacSha256 password u
    pbkdf2Fold password u' (xorBytes acc u') count

/-- One PBKDF2 output block: `F (P, S, c, i)` of RFC 8018 section 5.2. -/
def pbkdf2Block (password salt : ByteArray) (iterations index : Nat) : ByteArray :=
  let u1 := hmacSha256 password (salt ++ int32BE index)
  pbkdf2Fold password u1 u1 (iterations - 1)

/-- PBKDF2-HMAC-SHA-256 (RFC 8018 section 5.2) truncated to `dkLen`
bytes. `iterations` of zero is treated as one, so the result is always a
derived key and never the empty array — SCRAM's `i=0` is rejected by the
caller in `L4Factoidal.XMPP.Scram`, not silently turned into a weak key
here. -/
def pbkdf2Sha256 (password salt : ByteArray) (iterations dkLen : Nat) : ByteArray :=
  let iters := max iterations 1
  let blocks := (dkLen + sha256DigestBytes - 1) / sha256DigestBytes
  let full := (List.range blocks).foldl
    (fun acc i => acc ++ pbkdf2Block password salt iters (i + 1)) ByteArray.empty
  full.extract 0 dkLen

/-! ## HMAC-SHA-512 (RFC 2104 over FIPS 180-4 SHA-512)

JWE `A256CBC-HS512` (RFC 7518 §5.2.5) authenticates with HMAC-SHA-512. The
construction is the one above with SHA-512's 128-byte block. -/

/-- The SHA-512 block size in bytes (FIPS 180-4 section 5.1.2). -/
def hmacSha512BlockBytes : Nat := 128

/-- `K0` for SHA-512: hash a key longer than one block, then pad with zeros
to 128 bytes. -/
def hmacSha512Key0 (key : ByteArray) : ByteArray :=
  let k := if key.size > hmacSha512BlockBytes then sha512 key else key
  k ++ ByteArray.mk (Array.replicate (hmacSha512BlockBytes - k.size) (0 : UInt8))

private def xorPad512 (k : ByteArray) (b : UInt8) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity hmacSha512BlockBytes
  for i in [0:hmacSha512BlockBytes] do
    out := out.push ((k.get! i) ^^^ b)
  return out

/-- HMAC-SHA-512 (RFC 2104): `H((K0 ^ opad) ++ H((K0 ^ ipad) ++ msg))`. -/
def hmacSha512 (key msg : ByteArray) : ByteArray :=
  let k0 := hmacSha512Key0 key
  let inner := sha512 (xorPad512 k0 0x36 ++ msg)
  sha512 (xorPad512 k0 0x5c ++ inner)

/-- The OR of the byte-wise XOR of `a` and `b` from index `i` on: zero exactly
when the two agree there. Every byte is visited whatever the earlier bytes
were, so the time does not depend on where the first difference is.
Structural tail recursion on the count `n`. -/
def ctDiffFrom (a b : ByteArray) : (n i : Nat) → UInt8 → UInt8
  | 0, _, acc => acc
  | n + 1, i, acc => ctDiffFrom a b n (i + 1) (acc ||| ((a.get! i) ^^^ (b.get! i)))

/-- Compare two byte strings in time that depends only on their length (a
MAC tag check, RFC 7518 §5.2.2.2 step 4 and §11.5). Lengths are public, so a
length difference answers at once. -/
def ctEqBytes (a b : ByteArray) : Bool :=
  a.size == b.size && ctDiffFrom a b a.size 0 0 == 0

/-! ## Test vectors -/

private def hexOf (b : ByteArray) : String := bytesToHex b

private def bytesOfStr (s : String) : ByteArray := s.toUTF8

private def repeatByte (b : UInt8) (n : Nat) : ByteArray :=
  ByteArray.mk (Array.replicate n b)

-- RFC 4231 section 4.2, case 1.
#guard hexOf (hmacSha256 (repeatByte 0x0b 20) (bytesOfStr "Hi There"))
  == "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7"

-- RFC 4231 section 4.3, case 2 (a key shorter than one block).
#guard hexOf (hmacSha256 (bytesOfStr "Jefe") (bytesOfStr "what do ya want for nothing?"))
  == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"

-- RFC 4231 section 4.4, case 3.
#guard hexOf (hmacSha256 (repeatByte 0xaa 20) (repeatByte 0xdd 50))
  == "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe"

-- RFC 4231 section 4.7, case 6 — a 131-byte key, so `hmacKey0` hashes it.
#guard hexOf (hmacSha256 (repeatByte 0xaa 131)
    (bytesOfStr "Test Using Larger Than Block-Size Key - Hash Key First"))
  == "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54"

-- RFC 4231 section 4.8, case 7 — the same long key over a long message.
#guard hexOf (hmacSha256 (repeatByte 0xaa 131)
    (bytesOfStr ("This is a test using a larger than block-size key and a larger " ++
      "than block-size data. The key needs to be hashed before being used" ++
      " by the HMAC algorithm.")))
  == "9b09ffa71b942fcb27635fbcd5b0e944bfdc63644f0713938a7f51535c3a35e2"

-- RFC 7914 section 11, the PBKDF2-HMAC-SHA-256 vector with c=1.
#guard hexOf (pbkdf2Sha256 (bytesOfStr "passwd") (bytesOfStr "salt") 1 64)
  == ("55ac046e56e3089fec1691c22544b605f94185216dde0465e68b9d57c20dacbc" ++
      "49ca9cccf179b645991664b39d77ef317c71b845b1e30bd509112041d3a19783")

-- RFC 4231 section 4.2, case 1, HMAC-SHA-512.
#guard hexOf (hmacSha512 (repeatByte 0x0b 20) (bytesOfStr "Hi There"))
  == ("87aa7cdea5ef619d4ff0b4241a1d6cb02379f4e2ce4ec2787ad0b30545e17cde" ++
      "daa833b7d6b8a702038b274eaea3f4e4be9d914eeb61f1702e696c203a126854")

-- RFC 4231 section 4.3, case 2, HMAC-SHA-512.
#guard hexOf (hmacSha512 (bytesOfStr "Jefe") (bytesOfStr "what do ya want for nothing?"))
  == ("164b7a7bfcf819e2e395fbe73b56e0a387bd64222e831fd610270cd7ea250554" ++
      "9758bf75c05a994a6d034f65f8f0e6fdcaeab1a34d4a6b4b636e070a38bce737")

-- RFC 4231 section 4.7, case 6, HMAC-SHA-512: the 131-byte key is longer than
-- the 128-byte block, so `hmacSha512Key0` hashes it.
#guard hexOf (hmacSha512 (repeatByte 0xaa 131)
    (bytesOfStr "Test Using Larger Than Block-Size Key - Hash Key First"))
  == ("80b24263c7c1a3ebb71493c1dd7be8b49b46d1f41b4aeec1121b013783f8f352" ++
      "6b56d037e05f2598bd0fd2215d6a1e5295e64f73f63f0aec8b915a985d786598")

-- The constant-time comparison.
#guard ctEqBytes (repeatByte 7 16) (repeatByte 7 16)
#guard !ctEqBytes (repeatByte 7 16) ((repeatByte 7 15).push 6)
#guard !ctEqBytes (repeatByte 7 16) (repeatByte 7 15)
#guard ctEqBytes ByteArray.empty ByteArray.empty

end L4Factoidal.Crypto
