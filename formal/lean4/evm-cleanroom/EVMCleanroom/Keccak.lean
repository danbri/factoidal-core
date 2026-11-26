import EVMCleanroom.Memory

/-!
# Ethereum Keccak-256

The sponge absorbs 136-byte blocks into Keccak-f[1600] using Ethereum's
delimited suffix 0x01. The lane convention is little-endian. The EVM
interprets the 32 digest bytes as a big-endian word.

The round equations and constants follow the independently published
specification at https://keccak.team/keccak_specs_summary.html. The loop
never constructs the padded message. A block stores 25 fixed-width lanes
and reads at most 136 input bytes. The proof boundary is the algorithm's
local representation and padding. Digest values are checked independently
against published reference vectors. Constant-time execution is open.
-/

namespace EVMCleanroom.Keccak

def rate : Nat := 136

/-- Per-instruction host work limit for the experimental interpreter. -/
def maxInputBytes : Nat := 16 * 1024 * 1024

/-- One final block is necessary even when the input fills whole rate blocks. -/
def paddedBlocks (size : Nat) : Nat := size / rate + 1

/-- Read a byte from the mathematical Ethereum padding without materialising it. -/
def paddedByte (input : ByteView) (index : Nat) : UInt8 :=
  if index < input.size then input.readByte index
  else
    let suffix : UInt8 := if index = input.size then 1 else 0
    if index + 1 = rate * paddedBlocks input.size then suffix ||| 0x80 else suffix

private abbrev Lanes := Vector UInt64 25

private def rotationOffsets : Vector UInt64 25 :=
  #v[ 0,  1, 62, 28, 27,
     36, 44,  6, 55, 20,
      3, 10, 43, 25, 39,
     41, 45, 15, 21,  8,
     18,  2, 61, 56, 14]

private def roundConstants : Vector UInt64 24 :=
  #v[0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
     0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
     0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
     0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
     0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
     0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

@[inline] private def rotl (lane shift : UInt64) : UInt64 :=
  if shift == 0 then lane else (lane <<< shift) ||| (lane >>> (64 - shift))

@[inline] private def laneAt (lanes : Lanes) (x y : Nat) : UInt64 :=
  lanes[(x % 5) + 5 * (y % 5)]'(by omega)

private def round (lanes : Lanes) (constant : UInt64) : Lanes :=
  let columns : Vector UInt64 5 := Vector.ofFn fun column =>
    let x := column.val
    laneAt lanes x 0 ^^^ laneAt lanes x 1 ^^^ laneAt lanes x 2 ^^^
      laneAt lanes x 3 ^^^ laneAt lanes x 4
  let moved : Lanes := Vector.ofFn fun i =>
    -- For destination (u, v), invert (x, y) ↦ (y, (2*x + 3*y) % 5).
    let y := i.val % 5
    let x := (y + 3 * (i.val / 5)) % 5
    let left := columns[(x + 4) % 5]'(by omega)
    let right := columns[(x + 1) % 5]'(by omega)
    let correction := left ^^^ rotl right 1
    let offset := rotationOffsets[x + 5 * y]'(by omega)
    rotl (laneAt lanes x y ^^^ correction) offset
  Vector.ofFn fun i =>
    let x := i.val % 5
    let y := i.val / 5
    let updated := laneAt moved x y ^^^ ((~~~(laneAt moved (x + 1) y)) &&& laneAt moved (x + 2) y)
    if i.val = 0 then updated ^^^ constant else updated

private def byteIndices : Array Nat := Array.range 8

private def absorbBlock (read : Nat → UInt8) (start : Nat) (lanes : Lanes) : Lanes :=
  let mixed : Lanes := Vector.ofFn fun lane =>
    if lane.val < 17 then
      let wordStart := start + 8 * lane.val
      let word := byteIndices.foldl (fun acc i =>
        acc ||| (UInt64.ofNat (read (wordStart + i)).toNat <<< UInt64.ofNat (8 * i))) 0
      lanes[lane] ^^^ word
    else lanes[lane]
  roundConstants.toArray.foldl round mixed

private def absorbFull (input : ByteView) : Nat → Nat → Lanes → Lanes
  | 0, _, lanes => lanes
  | remaining + 1, start, lanes =>
    absorbFull input remaining (start + rate) (absorbBlock input.readByte start lanes)

/-- Four little-endian lanes produce the first 32 bytes of the sponge output. -/
def digest (input : ByteView) : Vector UInt8 32 :=
  let fullBlocks := input.size / rate
  let absorbed := absorbFull input fullBlocks 0 (Vector.replicate 25 0)
  let final := absorbBlock (paddedByte input) (fullBlocks * rate) absorbed
  Vector.ofFn fun i =>
    (final[i.val / 8]'(by omega) >>> UInt64.ofNat (8 * (i.val % 8))).toUInt8

def digestWord (input : ByteView) : Nat :=
  (digest input).toArray.foldl (fun acc byte => acc * 256 + byte.toNat) 0

/-- Explicit opt-in to running the independently unverified experimental hash. -/
structure Acceptance where
  private mk ::

/-- The executable enables this only on its named experimental opt-in. -/
def dangerouslyAcceptUnverified : Acceptance := ⟨⟩

def experimentalDigestWord (_ : Acceptance) (input : ByteView) : Nat :=
  digestWord input

/-- Kind: boundary.
    Says: the padded byte source agrees with the input at every valid index.
    Does not say: the resulting digest refines an independent cryptographic model. -/
theorem paddedByte_input (input : ByteView) (index : Nat) (h : index < input.size) :
    paddedByte input index = input.readByte index := by
  simp [paddedByte, h]

/-- Kind: boundary.
    Says: when the Ethereum suffix fits in the last rate byte, it also carries the final bit.
    Does not say: the result is a SHA3-256 padding byte. -/
theorem paddedByte_combined (input : ByteView) (h : input.size % rate = 135) :
    paddedByte input input.size = 0x81 := by
  have hEnd : input.size + 1 = rate * paddedBlocks input.size := by
    simp only [rate, paddedBlocks] at h ⊢
    omega
  simp [paddedByte, hEnd]
  decide

/-- Kind: boundary.
    Says: starting at a rate boundary allocates a full padding-only block.
    Does not say: the padding block is materialised in host memory. -/
theorem padded_size_aligned (size : Nat) (h : size % rate = 0) :
    rate * paddedBlocks size = size + rate := by
  simp only [rate, paddedBlocks] at h ⊢
  omega

/-- Kind: padding bound.
    Says: the input has at least one padding byte and at most one extra rate block of bytes.
    Does not say: each access to the backing byte view has constant host cost. -/
theorem padded_size_bounds (size : Nat) :
    size < rate * paddedBlocks size ∧ rate * paddedBlocks size ≤ size + rate := by
  simp only [rate, paddedBlocks]
  omega

/-- Kind: work bound.
    Says: the specified KECCAK256 price pays for the number of absorbed blocks.
    Does not say: each abstract block has the same host execution time. -/
theorem paddedBlocks_paid (words offset length gas : Nat)
    (h : MemoryGas.keccakCost words offset length ≤ gas) :
    paddedBlocks length ≤ gas / 6 + 1 := by
  simp only [MemoryGas.keccakCost] at h
  simp only [paddedBlocks, rate]
  omega

private theorem absorbFull_congr (a b : ByteView) (hRead : a.readByte = b.readByte)
    (blocks start : Nat) (lanes : Lanes) :
    absorbFull a blocks start lanes = absorbFull b blocks start lanes := by
  induction blocks generalizing start lanes with
  | zero => rfl
  | succ blocks ih => simp only [absorbFull, hRead, ih]

/-- Kind: noninterference.
    Says: two byte views with equal sizes and equal bytes in range give the same digest.
    Does not say: the digest uniquely determines those bytes. -/
theorem digest_reads_only_window (a b : ByteView) (hSize : a.size = b.size)
    (hBytes : ∀ index, index < a.size → a.readByte index = b.readByte index) :
    digest a = digest b := by
  have hRead : a.readByte = b.readByte := by
    funext index
    by_cases h : index < a.size
    · exact hBytes index h
    · simp [ByteView.readByte, ← hSize, h]
  have hPad : paddedByte a = paddedByte b := by
    funext index
    simp only [paddedByte, hSize, hRead]
  simp only [digest, hSize, absorbFull_congr a b hRead, hPad]

/-- Kind: range.
    Says: the digest exposes exactly 32 bytes for every input.
    Does not say: the digest has a particular value. -/
theorem digest_width (input : ByteView) : (digest input).toArray.size = 32 :=
  (digest input).size_toArray

#print axioms paddedByte_input
#print axioms paddedByte_combined
#print axioms padded_size_aligned
#print axioms padded_size_bounds
#print axioms paddedBlocks_paid
#print axioms digest_reads_only_window
#print axioms digest_width

end EVMCleanroom.Keccak
