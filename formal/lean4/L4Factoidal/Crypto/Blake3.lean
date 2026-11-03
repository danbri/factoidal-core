/-
L4Factoidal.Crypto.Blake3 — the BLAKE3 hash (the default `hash` mode,
32-byte output), in pure Lean, for `fn:hash($value, "BLAKE3")` of F&O 4.0
§5.3.18.

WHY A HAND-WRITTEN DIGEST IS ALLOWED HERE: tier 1 of
`skills/crypto-policy/SKILL.md`, as for `Crypto.MD5` — a hash over PUBLIC
data (the argument of `fn:hash`, which the expression itself names). No
secret, no key, no signature: a codec, not a security boundary. The keyed
and key-derivation modes and extended output are not implemented.

Spec: the BLAKE3 paper (O'Connor, Aumasson, Neves, Wilcox-O'Hearn,
"BLAKE3: one function, fast everywhere", 2021), §2.2 the compression
function, §2.3 chunks (1024 bytes, 64-byte blocks, flags CHUNK_START,
CHUNK_END), §2.4 the binary tree (the left subtree holds the largest
power of two of chunks that leaves the right subtree non-empty; PARENT),
§2.5 the ROOT flag on the root compression.

Test vectors: the reference implementation's output for "", "abc",
"jamboree", 0xCAFEBABE, and the official test-vector inputs (byte i is
i mod 251) of lengths 1025 and 3000, as `#guard`s at the end.
-/
namespace L4Factoidal.Crypto.Blake3

def iv : Array UInt32 :=
  #[0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A, 0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19]

def msgPerm : Array Nat := #[2, 6, 3, 10, 7, 0, 4, 13, 1, 11, 12, 5, 9, 14, 15, 8]

def chunkStart : UInt32 := 1
def chunkEnd : UInt32 := 2
def parentF : UInt32 := 4
def rootF : UInt32 := 8

def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

def g (s : Array UInt32) (a b c d : Nat) (mx my : UInt32) : Array UInt32 := Id.run do
  let mut s := s
  s := s.set! a (s[a]! + s[b]! + mx)
  s := s.set! d (rotr (s[d]! ^^^ s[a]!) 16)
  s := s.set! c (s[c]! + s[d]!)
  s := s.set! b (rotr (s[b]! ^^^ s[c]!) 12)
  s := s.set! a (s[a]! + s[b]! + my)
  s := s.set! d (rotr (s[d]! ^^^ s[a]!) 8)
  s := s.set! c (s[c]! + s[d]!)
  s := s.set! b (rotr (s[b]! ^^^ s[c]!) 7)
  return s

def round (s : Array UInt32) (m : Array UInt32) : Array UInt32 :=
  let s := g s 0 4 8 12 m[0]! m[1]!
  let s := g s 1 5 9 13 m[2]! m[3]!
  let s := g s 2 6 10 14 m[4]! m[5]!
  let s := g s 3 7 11 15 m[6]! m[7]!
  let s := g s 0 5 10 15 m[8]! m[9]!
  let s := g s 1 6 11 12 m[10]! m[11]!
  let s := g s 2 7 8 13 m[12]! m[13]!
  g s 3 4 9 14 m[14]! m[15]!

/-- The compression function (§2.2): the 16 output words. -/
def compress (cv : Array UInt32) (m : Array UInt32) (counter : UInt64) (blockLen flags : UInt32) :
    Array UInt32 := Id.run do
  let mut s : Array UInt32 := cv ++ #[iv[0]!, iv[1]!, iv[2]!, iv[3]!,
    counter.toUInt32, (counter >>> 32).toUInt32, blockLen, flags]
  let mut m := m
  for r in [0:7] do
    s := round s m
    if r < 6 then m := msgPerm.map (fun i => m[i]!)
  let mut out := s
  for i in [0:8] do
    out := out.set! i (s[i]! ^^^ s[i + 8]!)
    out := out.set! (i + 8) (s[i + 8]! ^^^ cv[i]!)
  return out

/-- The 16 little-endian words of a block, zero-padded to 64 bytes. -/
def words (b : ByteArray) (off len : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.replicate 16 0
  for i in [0:16] do
    let mut x : UInt32 := 0
    for k in [0:4] do
      let j := i * 4 + k
      let byte : UInt32 := if j < len then (b.get! (off + j)).toUInt32 else 0
      x := x ||| (byte <<< (8 * k).toUInt32)
    w := w.set! i x
  return w

/-- The chaining value (or, with `root`, the output words) of chunk
    `ci` of `b`. -/
def chunk (b : ByteArray) (ci : Nat) (root : Bool) : Array UInt32 := Id.run do
  let start := ci * 1024
  let len := min 1024 (b.size - start)
  let nBlocks := if len == 0 then 1 else (len + 63) / 64
  let mut cv := iv
  let mut out := iv
  for j in [0:nBlocks] do
    let off := start + j * 64
    let bl := min 64 (len - j * 64)
    let last := j + 1 == nBlocks
    let flags := (if j == 0 then chunkStart else 0) ||| (if last then chunkEnd else 0) |||
      (if last && root then rootF else 0)
    out := compress cv (words b off bl) ci.toUInt64 bl.toUInt32 flags
    cv := out.extract 0 8
  return if root then out else cv

/-- The largest power of two strictly below `n` (for `n ≥ 2`). -/
def leftCount (n : Nat) : Nat := Id.run do
  let mut p := 1
  for _ in [0:64] do
    if p * 2 < n then p := p * 2
  return p

/-- The chaining value of the subtree over chunks `[lo, lo + n)`; with
    `root`, the root output words. -/
def subtree (b : ByteArray) : Nat → Nat → Nat → Bool → Array UInt32
  | 0, lo, _, root => chunk b lo root
  | f + 1, lo, n, root =>
    if n ≤ 1 then chunk b lo root
    else
      let l := leftCount n
      let left := subtree b f lo l false
      let right := subtree b f (lo + l) (n - l) false
      let out := compress iv (left ++ right) 0 64 (parentF ||| (if root then rootF else 0))
      if root then out else out.extract 0 8

def hash (b : ByteArray) : ByteArray :=
  let n := if b.size == 0 then 1 else (b.size + 1023) / 1024
  let out := subtree b 64 0 n true
  ByteArray.mk ((List.range 32).map (fun i => ((out[i / 4]! >>> (8 * (i % 4)).toUInt32) &&& 0xFF).toUInt8)).toArray

def hexLower (b : ByteArray) : String :=
  String.join (b.toList.map (fun x =>
    let s := String.ofList (Nat.toDigits 16 x.toNat)
    if s.length == 1 then "0" ++ s else s))

def vector (n : Nat) : ByteArray := ByteArray.mk ((List.range n).map (fun i => (i % 251).toUInt8)).toArray

#guard hexLower (hash ByteArray.empty) == "af1349b9f5f9a1a6a0404dea36dcc9499bcb25c9adc112b7cc9a93cae41f3262"
#guard hexLower (hash "abc".toUTF8) == "6437b3ac38465133ffb63b75273a8db548c558465d79db03fd359c6cd5bd9d85"
#guard hexLower (hash "jamboree".toUTF8) == "12089b2f37afb7fded7dd038d06e0fe647bd7e41bcebb688b5abecf6a13489c0"
#guard hexLower (hash (ByteArray.mk #[0xCA, 0xFE, 0xBA, 0xBE])) == "00f55b814f907a53f1c725c57f16e7d842ec8493aab078f8b6cda1768d248173"
#guard hexLower (hash (vector 1025)) == "d00278ae47eb27b34faecf67b4fe263f82d5412916c1ffd97c8cb7fb814b8444"
#guard hexLower (hash (vector 3000)) == "5fade288bf27444bee55ba2babb98c3c922c1e84c2e445e7d1f6da24756f5060"

end L4Factoidal.Crypto.Blake3
