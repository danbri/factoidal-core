/-
Harness/QlvrKernel — the hot kernel of query q07 (scan two permutation
ranges, merge join on one Id column), written several ways in Lean, for the
Lean-against-C measurement of https://github.com/danbri/factoidal/issues/778.
Record: docs/designissues/2026-10-11-qlvr-performance.md.

This is a HARNESS, not part of the verified library. The input is a file
that `l4qlvr kernel-dump` writes from the QLever instance (decoded columns of
the POS blocks for `wso:medal` `Gold` and of the PSO blocks for
`wso:athlete`); the same file is read by the C reference
`tools/qlvr/bench/kernel.c`. All implementations run the same algorithm:

  1. A: keep the rows of A with col0 = kA0 and col1 = kA1; output col2 (?i).
  2. B: keep the rows of B with col0 = kB0; output col1 (?i) and col2 (?a).
  3. Merge join of the two on ?i (both are in ascending Id order); runs of
     equal ?i give their cross product. Output (?i, ?a).

Each prints the output row count and a checksum (wrapping sum over output
rows of `i * 0x9E3779B97F4A7C15 + a`), so the implementations can be checked
against each other.

Implementations:

  current    `selectRows` (a test per row, as the stage 4 scan did) then
             `mergeJoin` of `L4Factoidal.Qlvr.Bgp` on `Table`s (columns are
             ByteArrays of 8-byte Ids, appended by `Side.put64`, read by
             `word64`). Same algorithm as the C reference.
  production the scan of `Bgp.scanFoldM` since 2026-10-11 (`keyRange`: two
             binary searches and a copy, no test per row) then `mergeJoin`.
             A different algorithm: it isolates the design change.
  bytes-push, bytes-set  see below.
  bytes      ByteArray columns, read through `ld64` (one bounds test, then
             eight unchecked byte reads), written by `put64` into arrays of
             known capacity; loops are tail calls over `Nat` indices with no
             allocation per row.
  floats     the same algorithm over `FloatArray` columns: one 8-byte slot
             per Id, read with `FloatArray.get` and `Float.toBits` (a bit
             copy), written with `Float.ofBits` and `push`.
  native     the same algorithm over `Array UInt64` (each element is a
             boxed object in Lean's runtime).
-/
import L4Factoidal.Qlvr.Bgp

open L4Factoidal.Qlvr
open L4Factoidal.Codec.Zstd (word64)

namespace QlvrKernel

/-- The magic of a kernel input file. -/
def magic : String := "QLVRKRN1"

structure Input where
  kA0 : UInt64
  kA1 : UInt64
  kB0 : UInt64
  nA : Nat
  nB : Nat
  a0 : ByteArray
  a1 : ByteArray
  a2 : ByteArray
  b0 : ByteArray
  b1 : ByteArray
  b2 : ByteArray

def Input.encode (x : Input) : ByteArray :=
  let h := magic.toUTF8
  let h := Side.put64 h x.kA0
  let h := Side.put64 h x.kA1
  let h := Side.put64 h x.nA.toUInt64
  let h := Side.put64 h x.kB0
  let h := Side.put64 h x.nB.toUInt64
  h ++ x.a0 ++ x.a1 ++ x.a2 ++ x.b0 ++ x.b1 ++ x.b2

def Input.parse (d : ByteArray) : Except String Input := do
  if d.size < 48 || (d.extract 0 8).data != magic.toUTF8.data then throw "kernel input: bad magic"
  let kA0 := word64 d 8
  let kA1 := word64 d 16
  let nA := (word64 d 24).toNat
  let kB0 := word64 d 32
  let nB := (word64 d 40).toNat
  if d.size != 48 + 24 * nA + 24 * nB then throw "kernel input: size does not match the counts"
  let col (k : Nat) (base n : Nat) := d.extract (base + 8 * n * k) (base + 8 * n * (k + 1))
  let bb := 48 + 24 * nA
  return { kA0, kA1, kB0, nA, nB, a0 := col 0 48 nA, a1 := col 1 48 nA, a2 := col 2 48 nA,
           b0 := col 0 bb nB, b1 := col 1 bb nB, b2 := col 2 bb nB }

def mixK : UInt64 := 0x9E3779B97F4A7C15

/-! ## current: the production code -/

def runCurrent (x : Input) : Nat × UInt64 := Id.run do
  let (ca, na) := selectRows #[x.a0, x.a1, x.a2] #[(0, x.kA0), (1, x.kA1)] #[] #[2] x.nA (x.nA + 1) 0
    #[ByteArray.emptyWithCapacity (8 * x.nA)] 0
  let (cb, nb) := selectRows #[x.b0, x.b1, x.b2] #[(0, x.kB0)] #[] #[1, 2] x.nB (x.nB + 1) 0
    #[ByteArray.emptyWithCapacity (8 * x.nB), ByteArray.emptyWithCapacity (8 * x.nB)] 0
  let ta : Table := { vars := #["i"], cols := ca, rows := na, sortVar := some "i" }
  let tb : Table := { vars := #["i", "a"], cols := cb, rows := nb, sortVar := some "i" }
  let j := mergeJoin ta tb "i"
  let mut s : UInt64 := 0
  for r in [0:j.rows] do
    s := s + j.at 0 r * mixK + j.at 1 r
  return (j.rows, s)

/-! ## production: the scan and join of `L4Factoidal.Qlvr.Bgp` after this change

A different algorithm for step 1 and 2: the rows with a key prefix are one
range of the sorted input, found by two binary searches (`keyRange`) and
copied with `extract`; then the production `mergeJoin`. -/

def runProduction (x : Input) : Nat × UInt64 := Id.run do
  let (la, ha) := keyRange #[x.a0, x.a1, x.a2] #[x.kA0, x.kA1] x.nA
  let (lb, hb) := keyRange #[x.b0, x.b1, x.b2] #[x.kB0] x.nB
  let ta : Table := { vars := #["i"], cols := #[x.a2.extract (8 * la) (8 * ha)], rows := ha - la, sortVar := some "i" }
  let tb : Table := { vars := #["i", "a"], cols := #[x.b1.extract (8 * lb) (8 * hb), x.b2.extract (8 * lb) (8 * hb)],
                      rows := hb - lb, sortVar := some "i" }
  let j := mergeJoin ta tb "i"
  let mut s : UInt64 := 0
  for r in [0:j.rows] do
    s := s + j.at 0 r * mixK + j.at 1 r
  return (j.rows, s)

/-! ## bytes: ByteArray columns, no allocation per row -/

/-- The little-endian `u64` at byte `p`: one bounds test, eight reads. -/
@[inline] def ld64 (d : ByteArray) (p : Nat) : UInt64 :=
  if h : p + 8 ≤ d.size then
    (d[p]'(by omega)).toUInt64 |||
    ((d[p+1]'(by omega)).toUInt64 <<< 8) |||
    ((d[p+2]'(by omega)).toUInt64 <<< 16) |||
    ((d[p+3]'(by omega)).toUInt64 <<< 24) |||
    ((d[p+4]'(by omega)).toUInt64 <<< 32) |||
    ((d[p+5]'(by omega)).toUInt64 <<< 40) |||
    ((d[p+6]'(by omega)).toUInt64 <<< 48) |||
    ((d[p+7]'(by omega)).toUInt64 <<< 56)
  else 0

@[inline] def put64 (b : ByteArray) (x : UInt64) : ByteArray :=
  b.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8
   |>.push (x >>> 32).toUInt8 |>.push (x >>> 40).toUInt8 |>.push (x >>> 48).toUInt8
   |>.push (x >>> 56).toUInt8

def filterA (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : Nat) : Nat → ByteArray → ByteArray
  | i, out =>
    if i < n then
      let p := 8 * i
      if ld64 c0 p == k0 && ld64 c1 p == k1 then filterA c0 c1 c2 k0 k1 n (i + 1) (put64 out (ld64 c2 p))
      else filterA c0 c1 c2 k0 k1 n (i + 1) out
    else out
termination_by i => n - i

def filterB (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : Nat) : Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | i, o1, o2 =>
    if i < n then
      let p := 8 * i
      if ld64 c0 p == k0 then filterB c0 c1 c2 k0 n (i + 1) (put64 o1 (ld64 c1 p)) (put64 o2 (ld64 c2 p))
      else filterB c0 c1 c2 k0 n (i + 1) o1 o2
    else (o1, o2)
termination_by i => n - i

/-- End of the run of `v` in `c` starting at row `i` (rows `< n`). -/
def runEnd (c : ByteArray) (v : UInt64) (n : Nat) : Nat → Nat
  | i => if i < n then (if ld64 c (8 * i) == v then runEnd c v n (i + 1) else i) else i
termination_by i => n - i

/-- Emit the cross product of rows `[i, ie)` of the left `?i` column with
    rows `[j0, je)` of the right `(?i, ?a)` columns. -/
def crossRight (bi ba : ByteArray) (iv : UInt64) (je : Nat) : Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | j, oi, oa =>
    if j < je then crossRight bi ba iv je (j + 1) (put64 oi iv) (put64 oa (ld64 ba (8 * j)))
    else (oi, oa)
termination_by j => je - j

def crossLeft (bi ba : ByteArray) (iv : UInt64) (j0 je : Nat) (ie : Nat) : Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | i, oi, oa =>
    if i < ie then
      let (oi, oa) := crossRight bi ba iv je j0 oi oa
      crossLeft bi ba iv j0 je ie (i + 1) oi oa
    else (oi, oa)
termination_by i => ie - i

def mergeLoop (ai : ByteArray) (na : Nat) (bi ba : ByteArray) (nb : Nat) :
    Nat → Nat → Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | 0, _, _, oi, oa => (oi, oa)
  | fuel+1, i, j, oi, oa =>
    if i < na && j < nb then
      let x := ld64 ai (8 * i)
      let y := ld64 bi (8 * j)
      if x < y then mergeLoop ai na bi ba nb fuel (i + 1) j oi oa
      else if y < x then mergeLoop ai na bi ba nb fuel i (j + 1) oi oa
      else
        let ie := runEnd ai x na (i + 1)
        let je := runEnd bi x nb (j + 1)
        let (oi, oa) := crossLeft bi ba x j je ie i oi oa
        mergeLoop ai na bi ba nb fuel ie je oi oa
    else (oi, oa)

def sumLoop (oi oa : ByteArray) (n : Nat) : Nat → UInt64 → UInt64
  | i, s => if i < n then sumLoop oi oa n (i + 1) (s + ld64 oi (8 * i) * mixK + ld64 oa (8 * i)) else s
termination_by i => n - i

def runBytes (x : Input) : Nat × UInt64 :=
  let ai := filterA x.a0 x.a1 x.a2 x.kA0 x.kA1 x.nA 0 (ByteArray.emptyWithCapacity (8 * x.nA))
  let (bi, ba) := filterB x.b0 x.b1 x.b2 x.kB0 x.nB 0
    (ByteArray.emptyWithCapacity (8 * x.nB)) (ByteArray.emptyWithCapacity (8 * x.nB))
  let na := ai.size / 8
  let nb := bi.size / 8
  let (oi, oa) := mergeLoop ai na bi ba nb (na + nb + 1) 0 0
    (ByteArray.emptyWithCapacity (8 * nb)) (ByteArray.emptyWithCapacity (8 * nb))
  let n := oi.size / 8
  (n, sumLoop oi oa n 0 0)


/-! ## bytes-set: ByteArray columns written in place into buffers of known size -/

/-- Write `x` little-endian at byte `p` (in place when `b` is unique). -/
@[inline] def set64 (b : ByteArray) (p : Nat) (x : UInt64) : ByteArray :=
  b.set! p x.toUInt8 |>.set! (p+1) (x >>> 8).toUInt8 |>.set! (p+2) (x >>> 16).toUInt8
   |>.set! (p+3) (x >>> 24).toUInt8 |>.set! (p+4) (x >>> 32).toUInt8 |>.set! (p+5) (x >>> 40).toUInt8
   |>.set! (p+6) (x >>> 48).toUInt8 |>.set! (p+7) (x >>> 56).toUInt8

def filterAS (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : Nat) : Nat → Nat → ByteArray → ByteArray × Nat
  | i, m, out =>
    if i < n then
      let p := 8 * i
      if ld64 c0 p == k0 && ld64 c1 p == k1 then filterAS c0 c1 c2 k0 k1 n (i + 1) (m + 1) (set64 out (8 * m) (ld64 c2 p))
      else filterAS c0 c1 c2 k0 k1 n (i + 1) m out
    else (out, m)
termination_by i => n - i

def filterBS (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : Nat) : Nat → Nat → ByteArray → ByteArray → ByteArray × ByteArray × Nat
  | i, m, o1, o2 =>
    if i < n then
      let p := 8 * i
      if ld64 c0 p == k0 then filterBS c0 c1 c2 k0 n (i + 1) (m + 1) (set64 o1 (8 * m) (ld64 c1 p)) (set64 o2 (8 * m) (ld64 c2 p))
      else filterBS c0 c1 c2 k0 n (i + 1) m o1 o2
    else (o1, o2, m)
termination_by i => n - i

def crossRightS (ba : ByteArray) (iv : UInt64) (je : Nat) : Nat → Nat → ByteArray → ByteArray → ByteArray × ByteArray × Nat
  | j, m, oi, oa =>
    if j < je then crossRightS ba iv je (j + 1) (m + 1) (set64 oi (8 * m) iv) (set64 oa (8 * m) (ld64 ba (8 * j)))
    else (oi, oa, m)
termination_by j => je - j

def crossLeftS (ba : ByteArray) (iv : UInt64) (j0 je ie : Nat) : Nat → Nat → ByteArray → ByteArray → ByteArray × ByteArray × Nat
  | i, m, oi, oa =>
    if i < ie then
      let (oi, oa, m) := crossRightS ba iv je j0 m oi oa
      crossLeftS ba iv j0 je ie (i + 1) m oi oa
    else (oi, oa, m)
termination_by i => ie - i

/-- Output buffers hold at most `na * nb` rows; the kernel input gives at most
    `nb` (each right row joins at most one left run here, the left `?i` are
    distinct), and the caller sizes them. -/
def mergeLoopS (ai : ByteArray) (na : Nat) (bi ba : ByteArray) (nb : Nat) :
    Nat → Nat → Nat → Nat → ByteArray → ByteArray → ByteArray × ByteArray × Nat
  | 0, _, _, m, oi, oa => (oi, oa, m)
  | fuel+1, i, j, m, oi, oa =>
    if i < na && j < nb then
      let x := ld64 ai (8 * i)
      let y := ld64 bi (8 * j)
      if x < y then mergeLoopS ai na bi ba nb fuel (i + 1) j m oi oa
      else if y < x then mergeLoopS ai na bi ba nb fuel i (j + 1) m oi oa
      else
        let ie := runEnd ai x na (i + 1)
        let je := runEnd bi x nb (j + 1)
        let (oi, oa, m) := crossLeftS ba x j je ie i m oi oa
        mergeLoopS ai na bi ba nb fuel ie je m oi oa
    else (oi, oa, m)

/-- A buffer of `n` bytes to overwrite: a copy of a prefix of `src`, or of
    zeros past its end. -/
def scratch (src : ByteArray) (n : Nat) : ByteArray :=
  if n ≤ src.size then src.extract 0 n
  else src ++ ByteArray.mk (Array.replicate (n - src.size) 0)

def runBytesSet (x : Input) : Nat × UInt64 :=
  let (ai, na) := filterAS x.a0 x.a1 x.a2 x.kA0 x.kA1 x.nA 0 0 (scratch x.a2 (8 * x.nA))
  let (bi, ba, nb) := filterBS x.b0 x.b1 x.b2 x.kB0 x.nB 0 0 (scratch x.b1 (8 * x.nB)) (scratch x.b2 (8 * x.nB))
  let (oi, oa, n) := mergeLoopS ai na bi ba nb (na + nb + 1) 0 0 0
    (scratch x.b1 (8 * x.nB)) (scratch x.b2 (8 * x.nB))
  (n, sumLoop oi oa n 0 0)

/-! ## usize and usize-cstore: the bytes-set algorithm with `USize` indices

Added 2026-10-12 for the Lean-to-C audit
(docs/designissues/2026-10-12-lean-to-c-performance.md). Same loops as
bytes-set, but every row index, byte position and counter is a `USize` and
every byte read is `ByteArray.uget` with a proof, so the generated C has no
`Nat` operation, no `lean_dec` and no boxing in the loops. The load `ldU`
compiles (clang -O3, x86-64) to ONE 8-byte `movq` after two compares.

`usize` writes each Id with eight `ByteArray.uset` (`setU`, pure Lean);
`usize-cstore` writes it with `setC`, an `@[extern c inline]` 8-byte store
whose Lean body is `setU` (the reference). `setC` exists only in this
harness, to measure what an unboxed store primitive would give; the
checksum comparison of `l4qlvr kernel` and `tests/qlvr/kernel.sh` is its
differential test. It assumes a little-endian host (x86-64, wasm32); on a
big-endian host the C expression swaps the bytes. -/

theorem usize_succ_toNat {i n : USize} (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  have h2 := n.toNat_lt_size
  rw [USize.toNat_add, USize.toNat_one]
  apply Nat.mod_eq_of_lt
  simp only [USize.size] at h2
  omega

theorem usize_pred_toNat {k : USize} (h : 0 < k) : (k - 1).toNat = k.toNat - 1 := by
  have h1 : (1 : USize) ≤ k := by
    have := USize.lt_iff_toNat_lt.mp h
    apply USize.le_iff_toNat_le.mpr
    simp only [USize.toNat_one]
    simp only [USize.toNat_zero] at this
    omega
  rw [USize.toNat_sub_of_le _ _ h1, USize.toNat_one]

theorem ldU_bound {d : ByteArray} {p : USize} (h1 : p + 8 ≤ d.usize) (h2 : p < p + 8)
    (k : USize) (hk : k.toNat < 8) : (p + k).toNat < d.size := by
  have a1 := USize.le_iff_toNat_le.mp h1
  have a2 := USize.lt_iff_toNat_lt.mp h2
  have hs := p.toNat_lt_size
  simp only [USize.size] at hs
  simp only [ByteArray.usize, USize.toNat_add, USize.toNat_ofNat', Nat.toUSize] at a1 a2 ⊢
  have e8 : (8 : USize).toNat = 8 := by simp
  rw [e8] at a1 a2
  have h8 : 8 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have m1 : d.size % 2 ^ System.Platform.numBits ≤ d.size := Nat.mod_le _ _
  have hw : p.toNat + 8 < 2 ^ System.Platform.numBits := by
    rcases Nat.lt_or_ge (p.toNat + 8) (2 ^ System.Platform.numBits) with h | h
    · exact h
    · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at a2; omega
  rw [Nat.mod_eq_of_lt (by omega : p.toNat + 8 < _)] at a1
  rw [Nat.mod_eq_of_lt (by omega : p.toNat + k.toNat < _)]
  omega

/-- The little-endian `u64` at byte `p` (0 when the eight bytes are not all
    inside `d`): one bounds test, eight `uget`. -/
@[inline] def ldU (d : ByteArray) (p : USize) : UInt64 :=
  if h : p + 8 ≤ d.usize ∧ p < p + 8 then
    (d.uget p (by have := ldU_bound h.1 h.2 0 (by simp); simpa using this)).toUInt64 |||
    ((d.uget (p+1) (ldU_bound h.1 h.2 1 (by simp))).toUInt64 <<< 8) |||
    ((d.uget (p+2) (ldU_bound h.1 h.2 2 (by simp))).toUInt64 <<< 16) |||
    ((d.uget (p+3) (ldU_bound h.1 h.2 3 (by simp))).toUInt64 <<< 24) |||
    ((d.uget (p+4) (ldU_bound h.1 h.2 4 (by simp))).toUInt64 <<< 32) |||
    ((d.uget (p+5) (ldU_bound h.1 h.2 5 (by simp))).toUInt64 <<< 40) |||
    ((d.uget (p+6) (ldU_bound h.1 h.2 6 (by simp))).toUInt64 <<< 48) |||
    ((d.uget (p+7) (ldU_bound h.1 h.2 7 (by simp))).toUInt64 <<< 56)
  else 0

theorem usize_lt_size {a : ByteArray} {i : USize} (h : i < a.usize) : i.toNat < a.size := by
  have h1 := USize.lt_iff_toNat_lt.mp h
  simp only [ByteArray.usize, USize.toNat_ofNat', Nat.toUSize] at h1
  have := Nat.mod_le a.size (2 ^ System.Platform.numBits)
  omega

/-- Byte `i` set to `v`; `a` unchanged when `i` is out of range. The test is
    on `USize` (`i < a.usize`): `i.toNat < a.size` would compile to `Nat`
    operations. -/
@[inline] def set1 (a : ByteArray) (i : USize) (v : UInt8) : ByteArray :=
  if h : i < a.usize then a.uset i v (usize_lt_size h) else a

/-- Write `x` little-endian at byte `p` when the eight bytes are inside `b`
    (in place when `b` is unique); otherwise `b` unchanged. -/
@[inline] def setU (b : ByteArray) (p : USize) (x : UInt64) : ByteArray :=
  if p + 8 ≤ b.usize ∧ p < p + 8 then
    set1 b p x.toUInt8 |> (set1 · (p+1) (x >>> 8).toUInt8) |> (set1 · (p+2) (x >>> 16).toUInt8)
     |> (set1 · (p+3) (x >>> 24).toUInt8) |> (set1 · (p+4) (x >>> 32).toUInt8)
     |> (set1 · (p+5) (x >>> 40).toUInt8) |> (set1 · (p+6) (x >>> 48).toUInt8)
     |> (set1 · (p+7) (x >>> 56).toUInt8)
  else b

/-- `setU` as one 8-byte store (harness only; see the section comment). -/
@[extern c inline "({ lean_object* _a = #1; size_t _p = #2; uint64_t _x = #3; if (_p + 8 <= lean_sarray_size(_a) && _p + 8 > _p) { if (!lean_is_exclusive(_a)) _a = lean_copy_byte_array(_a); if (__BYTE_ORDER__ != __ORDER_LITTLE_ENDIAN__) _x = __builtin_bswap64(_x); __builtin_memcpy(lean_sarray_cptr(_a) + _p, &_x, 8); } _a; })"]
def setC (b : ByteArray) (p : USize) (x : UInt64) : ByteArray := setU b p x

section UsizeLoops
variable (st : ByteArray → USize → UInt64 → ByteArray)

@[specialize] def filterAU (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : USize) (i m : USize) (out : ByteArray) :
    ByteArray × USize :=
  if h : i < n then
    let p := 8 * i
    if ldU c0 p == k0 && ldU c1 p == k1 then filterAU c0 c1 c2 k0 k1 n (i + 1) (m + 1) (st out (8 * m) (ldU c2 p))
    else filterAU c0 c1 c2 k0 k1 n (i + 1) m out
  else (out, m)
termination_by n.toNat - i.toNat
decreasing_by all_goals (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

@[specialize] def filterBU (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : USize) (i m : USize) (o1 o2 : ByteArray) :
    ByteArray × ByteArray × USize :=
  if h : i < n then
    let p := 8 * i
    if ldU c0 p == k0 then filterBU c0 c1 c2 k0 n (i + 1) (m + 1) (st o1 (8 * m) (ldU c1 p)) (st o2 (8 * m) (ldU c2 p))
    else filterBU c0 c1 c2 k0 n (i + 1) m o1 o2
  else (o1, o2, m)
termination_by n.toNat - i.toNat
decreasing_by all_goals (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

def runEndU (c : ByteArray) (v : UInt64) (n : USize) (i : USize) : USize :=
  if h : i < n then (if ldU c (8 * i) == v then runEndU c v n (i + 1) else i) else i
termination_by n.toNat - i.toNat
decreasing_by (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

@[specialize] def crossRightU (ba : ByteArray) (iv : UInt64) (je : USize) (j m : USize) (oi oa : ByteArray) :
    ByteArray × ByteArray × USize :=
  if h : j < je then crossRightU ba iv je (j + 1) (m + 1) (st oi (8 * m) iv) (st oa (8 * m) (ldU ba (8 * j)))
  else (oi, oa, m)
termination_by je.toNat - j.toNat
decreasing_by (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

@[specialize] def crossLeftU (ba : ByteArray) (iv : UInt64) (j0 je ie : USize) (i m : USize) (oi oa : ByteArray) :
    ByteArray × ByteArray × USize :=
  if _h : i < ie then
    let (oi, oa, m) := crossRightU st ba iv je j0 m oi oa
    crossLeftU ba iv j0 je ie (i + 1) m oi oa
  else (oi, oa, m)
termination_by ie.toNat - i.toNat
decreasing_by (have := usize_succ_toNat _h; have := USize.lt_iff_toNat_lt.mp _h; omega)

@[specialize] def mergeLoopU (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (fuel i j m : USize) (oi oa : ByteArray) : ByteArray × ByteArray × USize :=
  if _hf : 0 < fuel then
    if i < na && j < nb then
      let x := ldU ai (8 * i)
      let y := ldU bi (8 * j)
      if x < y then mergeLoopU ai na bi ba nb (fuel - 1) (i + 1) j m oi oa
      else if y < x then mergeLoopU ai na bi ba nb (fuel - 1) i (j + 1) m oi oa
      else
        let ie := runEndU ai x na (i + 1)
        let je := runEndU bi x nb (j + 1)
        let (oi, oa, m) := crossLeftU st ba x j je ie i m oi oa
        mergeLoopU ai na bi ba nb (fuel - 1) ie je m oi oa
    else (oi, oa, m)
  else (oi, oa, m)
termination_by fuel.toNat
decreasing_by all_goals (have := usize_pred_toNat _hf; have := USize.lt_iff_toNat_lt.mp _hf; simp only [USize.toNat_zero] at *; omega)

end UsizeLoops

def sumLoopU (oi oa : ByteArray) (n : USize) (i : USize) (s : UInt64) : UInt64 :=
  if _h : i < n then sumLoopU oi oa n (i + 1) (s + ldU oi (8 * i) * mixK + ldU oa (8 * i)) else s
termination_by n.toNat - i.toNat
decreasing_by (have := usize_succ_toNat _h; have := USize.lt_iff_toNat_lt.mp _h; omega)

@[inline] def runUsizeWith (st : ByteArray → USize → UInt64 → ByteArray) (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAU st x.a0 x.a1 x.a2 x.kA0 x.kA1 nA 0 0 (scratch x.a2 (8 * x.nA))
  let (bi, ba, nb) := filterBU st x.b0 x.b1 x.b2 x.kB0 nB 0 0 (scratch x.b1 (8 * x.nB)) (scratch x.b2 (8 * x.nB))
  let (oi, oa, n) := mergeLoopU st ai na bi ba nb (na + nb + 1) 0 0 0
    (scratch x.b1 (8 * x.nB)) (scratch x.b2 (8 * x.nB))
  (n.toNat, sumLoopU oi oa n 0 0)

def runUsize (x : Input) : Nat × UInt64 := runUsizeWith setU x

def runUsizeCStore (x : Input) : Nat × UInt64 := runUsizeWith setC x

/-! ## floats: FloatArray columns (one 8-byte slot per Id) -/

def toFloats (b : ByteArray) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity (b.size / 8)
  for i in [0:b.size / 8] do
    out := out.push (Float.ofBits (word64 b (8 * i)))
  return out

@[inline] def fl (c : FloatArray) (i : Nat) : UInt64 :=
  if h : i < c.size then (c[i]'h).toBits else 0

def filterAF (c0 c1 c2 : FloatArray) (k0 k1 : UInt64) (n : Nat) : Nat → FloatArray → FloatArray
  | i, out =>
    if i < n then
      if fl c0 i == k0 && fl c1 i == k1 then filterAF c0 c1 c2 k0 k1 n (i + 1) (out.push (Float.ofBits (fl c2 i)))
      else filterAF c0 c1 c2 k0 k1 n (i + 1) out
    else out
termination_by i => n - i

def filterBF (c0 c1 c2 : FloatArray) (k0 : UInt64) (n : Nat) : Nat → FloatArray → FloatArray → FloatArray × FloatArray
  | i, o1, o2 =>
    if i < n then
      if fl c0 i == k0 then filterBF c0 c1 c2 k0 n (i + 1) (o1.push (Float.ofBits (fl c1 i))) (o2.push (Float.ofBits (fl c2 i)))
      else filterBF c0 c1 c2 k0 n (i + 1) o1 o2
    else (o1, o2)
termination_by i => n - i

def runEndF (c : FloatArray) (v : UInt64) (n : Nat) : Nat → Nat
  | i => if i < n then (if fl c i == v then runEndF c v n (i + 1) else i) else i
termination_by i => n - i

def crossRightF (ba : FloatArray) (iv : UInt64) (je : Nat) : Nat → FloatArray → FloatArray → FloatArray × FloatArray
  | j, oi, oa =>
    if j < je then crossRightF ba iv je (j + 1) (oi.push (Float.ofBits iv)) (oa.push (Float.ofBits (fl ba j)))
    else (oi, oa)
termination_by j => je - j

def crossLeftF (ba : FloatArray) (iv : UInt64) (j0 je ie : Nat) : Nat → FloatArray → FloatArray → FloatArray × FloatArray
  | i, oi, oa =>
    if i < ie then
      let (oi, oa) := crossRightF ba iv je j0 oi oa
      crossLeftF ba iv j0 je ie (i + 1) oi oa
    else (oi, oa)
termination_by i => ie - i

def mergeLoopF (ai : FloatArray) (bi ba : FloatArray) :
    Nat → Nat → Nat → FloatArray → FloatArray → FloatArray × FloatArray
  | 0, _, _, oi, oa => (oi, oa)
  | fuel+1, i, j, oi, oa =>
    if i < ai.size && j < bi.size then
      let x := fl ai i
      let y := fl bi j
      if x < y then mergeLoopF ai bi ba fuel (i + 1) j oi oa
      else if y < x then mergeLoopF ai bi ba fuel i (j + 1) oi oa
      else
        let ie := runEndF ai x ai.size (i + 1)
        let je := runEndF bi x bi.size (j + 1)
        let (oi, oa) := crossLeftF ba x j je ie i oi oa
        mergeLoopF ai bi ba fuel ie je oi oa
    else (oi, oa)

def sumLoopF (oi oa : FloatArray) : Nat → UInt64 → UInt64
  | i, s => if i < oi.size then sumLoopF oi oa (i + 1) (s + fl oi i * mixK + fl oa i) else s
termination_by i => oi.size - i

structure FInput where
  kA0 : UInt64
  kA1 : UInt64
  kB0 : UInt64
  a0 : FloatArray
  a1 : FloatArray
  a2 : FloatArray
  b0 : FloatArray
  b1 : FloatArray
  b2 : FloatArray

def FInput.ofInput (x : Input) : FInput :=
  { kA0 := x.kA0, kA1 := x.kA1, kB0 := x.kB0, a0 := toFloats x.a0, a1 := toFloats x.a1,
    a2 := toFloats x.a2, b0 := toFloats x.b0, b1 := toFloats x.b1, b2 := toFloats x.b2 }

def runFloats (x : FInput) : Nat × UInt64 :=
  let ai := filterAF x.a0 x.a1 x.a2 x.kA0 x.kA1 x.a0.size 0 (FloatArray.emptyWithCapacity x.a0.size)
  let (bi, ba) := filterBF x.b0 x.b1 x.b2 x.kB0 x.b0.size 0
    (FloatArray.emptyWithCapacity x.b0.size) (FloatArray.emptyWithCapacity x.b0.size)
  let (oi, oa) := mergeLoopF ai bi ba (ai.size + bi.size + 1) 0 0
    (FloatArray.emptyWithCapacity bi.size) (FloatArray.emptyWithCapacity bi.size)
  (oi.size, sumLoopF oi oa 0 0)

/-! ## native: Array UInt64 (boxed elements) -/

def toU64s (b : ByteArray) : Array UInt64 := Id.run do
  let mut out := Array.mkEmpty (b.size / 8)
  for i in [0:b.size / 8] do
    out := out.push (word64 b (8 * i))
  return out

structure UInput where
  kA0 : UInt64
  kA1 : UInt64
  kB0 : UInt64
  a0 : Array UInt64
  a1 : Array UInt64
  a2 : Array UInt64
  b0 : Array UInt64
  b1 : Array UInt64
  b2 : Array UInt64

def UInput.ofInput (x : Input) : UInput :=
  { kA0 := x.kA0, kA1 := x.kA1, kB0 := x.kB0, a0 := toU64s x.a0, a1 := toU64s x.a1,
    a2 := toU64s x.a2, b0 := toU64s x.b0, b1 := toU64s x.b1, b2 := toU64s x.b2 }

def runNative (x : UInput) : Nat × UInt64 := Id.run do
  let mut ai : Array UInt64 := Array.mkEmpty x.a0.size
  for i in [0:x.a0.size] do
    if x.a0[i]! == x.kA0 && x.a1[i]! == x.kA1 then ai := ai.push x.a2[i]!
  let mut bi : Array UInt64 := Array.mkEmpty x.b0.size
  let mut ba : Array UInt64 := Array.mkEmpty x.b0.size
  for j in [0:x.b0.size] do
    if x.b0[j]! == x.kB0 then
      bi := bi.push x.b1[j]!
      ba := ba.push x.b2[j]!
  let mut oi : Array UInt64 := #[]
  let mut oa : Array UInt64 := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:ai.size + bi.size + 1] do
    if i ≥ ai.size || j ≥ bi.size then break
    let a := ai[i]!
    let b := bi[j]!
    if a < b then i := i + 1
    else if b < a then j := j + 1
    else
      let mut ie := i + 1
      for _ in [0:ai.size] do
        if ie < ai.size && ai[ie]! == a then ie := ie + 1 else break
      let mut je := j + 1
      for _ in [0:bi.size] do
        if je < bi.size && bi[je]! == a then je := je + 1 else break
      for _ in [i:ie] do
        for y in [j:je] do
          oi := oi.push a
          oa := oa.push ba[y]!
      i := ie
      j := je
  let mut s : UInt64 := 0
  for k in [0:oi.size] do
    s := s + oi[k]! * mixK + oa[k]!
  return (oi.size, s)

end QlvrKernel
