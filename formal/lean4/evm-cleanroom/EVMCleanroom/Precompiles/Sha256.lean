import EVMCleanroom.Precompiles.Basic

/-!
# SHA-256 (precompile 0x02)

Written from FIPS 180-4 (sections 4.1.2, 4.2.2, 5.1.1, 5.3.3 and 6.2). The
round constants and the initial hash value are checked at build time against
their definition: the first 32 fractional bits of the cube roots (square
roots) of the first 64 (8) primes, by exact integer comparison.

The EVM package keeps its import closure inside `EVMCleanroom` (its source
gates require that), so this is a local module and not an import of the
repository's `L4Factoidal.Crypto.SHA2`. Digest values are tested against the
FIPS examples and, in CI, an independent oracle. No cryptographic property is
proved.

Gas (Yellow Paper appendix E, EELS `sha256`): 60 + 12 per 32-byte word.
-/

namespace EVMCleanroom.Precompiles.Sha256

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initialHash : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

private def primes : Array Nat := #[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311]

-- k is the 32 fractional bits of the cube root of p: (i·2³² + k)³ ≤ p·2⁹⁶ < (i·2³² + k + 1)³.
#guard (List.range 64).all fun n =>
  let prime := primes[n]!
  let k := roundConstants[n]!.toNat
  (List.range 8).any fun whole =>
    let x := whole * 2 ^ 32 + k
    x ^ 3 ≤ prime * 2 ^ 96 && prime * 2 ^ 96 < (x + 1) ^ 3
#guard (List.range 8).all fun n =>
  let prime := primes[n]!
  let h := initialHash[n]!.toNat
  (List.range 8).any fun whole =>
    let x := whole * 2 ^ 32 + h
    x ^ 2 ≤ prime * 2 ^ 64 && prime * 2 ^ 64 < (x + 1) ^ 2

@[inline] private def rotr (x n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

@[inline] private def word (data : ByteArray) (off : Nat) : UInt32 :=
  ((byteAt data off).toUInt32 <<< 24) ||| ((byteAt data (off + 1)).toUInt32 <<< 16) |||
    ((byteAt data (off + 2)).toUInt32 <<< 8) ||| (byteAt data (off + 3)).toUInt32

/-- Extend the 16 block words to the 64-word message schedule. -/
private def schedule : Nat → Array UInt32 → Array UInt32
  | 0, w => w
  | n+1, w =>
    let t := w.size
    let w15 := w[t - 15]!
    let w2 := w[t - 2]!
    let s0 := rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)
    let s1 := rotr w2 17 ^^^ rotr w2 19 ^^^ (w2 >>> 10)
    schedule n (w.push (w[t - 16]! + s0 + w[t - 7]! + s1))

private def rounds (w : Array UInt32) : Nat → State → State
  | 0, s => s
  | n+1, s =>
    let t := 63 - n
    let s1 := rotr s.e 6 ^^^ rotr s.e 11 ^^^ rotr s.e 25
    let ch := (s.e &&& s.f) ^^^ (~~~s.e &&& s.g)
    let t1 := s.h + s1 + ch + roundConstants[t]! + w[t]!
    let s0 := rotr s.a 2 ^^^ rotr s.a 13 ^^^ rotr s.a 22
    let maj := (s.a &&& s.b) ^^^ (s.a &&& s.c) ^^^ (s.b &&& s.c)
    rounds w n ⟨t1 + s0 + maj, s.a, s.b, s.c, s.d + t1, s.e, s.f, s.g⟩

private def compress (s : State) (data : ByteArray) (base : Nat) : State :=
  let first := (Array.range 16).map fun i => word data (base + 4 * i)
  let r := rounds (schedule 48 first) 64 s
  ⟨s.a + r.a, s.b + r.b, s.c + r.c, s.d + r.d, s.e + r.e, s.f + r.f, s.g + r.g, s.h + r.h⟩

private def blocks (data : ByteArray) : Nat → Nat → State → State
  | 0, _, s => s
  | n+1, base, s => blocks data n (base + 64) (compress s data base)

/-- Number of zero bytes between the 0x80 marker and the 8 length bytes. -/
def zeroPad (size : Nat) : Nat := (119 - size % 64) % 64

/-- Kind: padding.
    Says: message, marker, zero padding and length field fill whole 64-byte blocks.
    Does not say: the digest has a particular value. -/
theorem padded_blocks (size : Nat) : (size + 1 + zeroPad size + 8) % 64 = 0 := by
  simp only [zeroPad]
  omega

private def pad (m : ByteArray) : ByteArray :=
  m.push 0x80 ++ readPadded ByteArray.empty 0 (zeroPad m.size) ++ natToBE 8 (8 * m.size)

private def putWord (acc : ByteArray) (w : UInt32) : ByteArray :=
  (((acc.push (w >>> 24).toUInt8).push (w >>> 16).toUInt8).push (w >>> 8).toUInt8).push w.toUInt8

private theorem putWord_size (acc : ByteArray) (w : UInt32) : (putWord acc w).size = acc.size + 4 := by
  simp [putWord, ByteArray.size_push]

/-- The 32-byte SHA-256 digest. -/
def digest (m : ByteArray) : ByteArray :=
  let padded := pad m
  let i := initialHash
  let s := blocks padded (padded.size / 64) 0 ⟨i[0]!, i[1]!, i[2]!, i[3]!, i[4]!, i[5]!, i[6]!, i[7]!⟩
  putWord (putWord (putWord (putWord (putWord (putWord (putWord (putWord ByteArray.empty
    s.a) s.b) s.c) s.d) s.e) s.f) s.g) s.h

/-- Kind: length.
    Says: the digest is 32 bytes for every input.
    Does not say: the digest has a particular value. -/
theorem digest_size (m : ByteArray) : (digest m).size = 32 := by
  simp [digest, putWord_size]

def gasCost (size : Nat) : Nat := 60 + 12 * words32 size

/-- Precompile 0x02. -/
def run (gas : Nat) (input : ByteArray) : Result :=
  charge gas (gasCost input.size) fun _ => .output (digest input)

/-- Kind: output contract.
    Says: every successful call returns exactly 32 bytes and the exact unspent gas.
    Does not say: the bytes are the SHA-256 of the input (tested, not proved). -/
theorem run_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run gas input = .success out left) :
    out.size = 32 ∧ left + gasCost input.size = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  exact ⟨Body.output.inj hBody ▸ digest_size input, hGas⟩

/-- Kind: gas admission.
    Says: the call fails exactly when the forwarded gas is below 60 + 12 per word;
    otherwise it succeeds. There is no invalid input.
    Does not say: anything about the digest. -/
theorem run_total (gas : Nat) (input : ByteArray) :
    (gas < gasCost input.size → run gas input = .failure) ∧
    (gasCost input.size ≤ gas → ∃ out, run gas input = .success out (gas - gasCost input.size)) := by
  constructor
  · intro h; exact charge_underfunded _ _ _ h
  · intro h; exact ⟨_, charge_funded _ _ _ _ h rfl⟩

private def hexOf (s : String) : String := toHex (digest s.toUTF8)

#guard hexOf "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
#guard hexOf "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard hexOf "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq" ==
  "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"
#guard gasCost 0 == 60 && gasCost 1 == 72 && gasCost 32 == 72 && gasCost 33 == 84
#guard (match run 60 ByteArray.empty with | .success out 0 => out.size == 32 | _ => false)
#guard (match run 59 ByteArray.empty with | .failure => true | _ => false)

#print axioms padded_blocks
#print axioms putWord_size
#print axioms digest_size
#print axioms run_success
#print axioms run_total

end EVMCleanroom.Precompiles.Sha256
