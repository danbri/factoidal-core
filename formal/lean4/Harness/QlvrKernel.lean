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
import L4Factoidal.Qlvr.Sort

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
`Nat` operation, no `lean_dec` and no boxing in the loops. The load is
`L4Factoidal.Prim.Bytes.ldU64LE`, which clang -O3 compiles (x86-64) to ONE
8-byte `movq` after two compares.

`usize` writes each Id with `Prim.Bytes.stU64LERef` (eight `ByteArray.uset`,
pure Lean); `usize-cstore` writes it with `Prim.Bytes.stU64LE`, the library's
`@[extern c inline]` 8-byte store whose Lean meaning is `stU64LERef`. The
library's differential test is `tests/prim/run.sh`; the checksum comparison
of `l4qlvr kernel` and `tests/qlvr/kernel.sh` checks the two here too. -/

open L4Factoidal.Prim.Bytes

section UsizeLoops
variable (st : ByteArray → USize → UInt64 → ByteArray)

@[specialize] def filterAU (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : USize) (i m : USize) (out : ByteArray) :
    ByteArray × USize :=
  if h : i < n then
    let p := 8 * i
    if ldU64LE c0 p == k0 && ldU64LE c1 p == k1 then filterAU c0 c1 c2 k0 k1 n (i + 1) (m + 1) (st out (8 * m) (ldU64LE c2 p))
    else filterAU c0 c1 c2 k0 k1 n (i + 1) m out
  else (out, m)
termination_by n.toNat - i.toNat
decreasing_by all_goals (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

@[specialize] def filterBU (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : USize) (i m : USize) (o1 o2 : ByteArray) :
    ByteArray × ByteArray × USize :=
  if h : i < n then
    let p := 8 * i
    if ldU64LE c0 p == k0 then filterBU c0 c1 c2 k0 n (i + 1) (m + 1) (st o1 (8 * m) (ldU64LE c1 p)) (st o2 (8 * m) (ldU64LE c2 p))
    else filterBU c0 c1 c2 k0 n (i + 1) m o1 o2
  else (o1, o2, m)
termination_by n.toNat - i.toNat
decreasing_by all_goals (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

def runEndU (c : ByteArray) (v : UInt64) (n : USize) (i : USize) : USize :=
  if h : i < n then (if ldU64LE c (8 * i) == v then runEndU c v n (i + 1) else i) else i
termination_by n.toNat - i.toNat
decreasing_by (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

@[specialize] def crossRightU (ba : ByteArray) (iv : UInt64) (je : USize) (j m : USize) (oi oa : ByteArray) :
    ByteArray × ByteArray × USize :=
  if h : j < je then crossRightU ba iv je (j + 1) (m + 1) (st oi (8 * m) iv) (st oa (8 * m) (ldU64LE ba (8 * j)))
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
      let x := ldU64LE ai (8 * i)
      let y := ldU64LE bi (8 * j)
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

/-- `mergeLoopU` with `crossLeftU` and `crossRightU` fused into ONE loop
    (record section 8, step B). `mergeLoopU` calls `crossLeftU` once per run
    of equal join keys (13,369 times per q07 run), and each call returns a
    tuple `(oi, oa, m)`: in the generated C, three allocations and three
    frees per call. Here the cross product is a state of the same loop: when
    `ci < ie`, the loop emits left row `ci` with right rows `cj` to `je`
    (`cj` restarts at `j0`), then returns to the merge. Every call is a self
    tail call, so the C is one loop with no allocation; the tuple is made
    once, at the end. `mergeFlatU_eq` proves it equal to `mergeLoopU` when
    started outside a run (`ci = ie`). -/
@[specialize] def mergeFlatU (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (fuel i j : USize) (iv : UInt64) (ci ie j0 cj je m : USize) (oi oa : ByteArray) :
    ByteArray × ByteArray × USize :=
  if hc : ci < ie then
    if hj : cj < je then
      mergeFlatU ai na bi ba nb fuel i j iv ci ie j0 (cj + 1) je (m + 1)
        (st oi (8 * m) iv) (st oa (8 * m) (ldU64LE ba (8 * cj)))
    else mergeFlatU ai na bi ba nb fuel i j iv (ci + 1) ie j0 j0 je m oi oa
  else if hf : 0 < fuel then
    if i < na && j < nb then
      let x := ldU64LE ai (8 * i)
      let y := ldU64LE bi (8 * j)
      if x < y then mergeFlatU ai na bi ba nb (fuel - 1) (i + 1) j iv ci ie j0 cj je m oi oa
      else if y < x then mergeFlatU ai na bi ba nb (fuel - 1) i (j + 1) iv ci ie j0 cj je m oi oa
      else
        let ie' := runEndU ai x na (i + 1)
        let je' := runEndU bi x nb (j + 1)
        mergeFlatU ai na bi ba nb (fuel - 1) ie' je' x i ie' j j je' m oi oa
    else (oi, oa, m)
  else (oi, oa, m)
termination_by (fuel.toNat, ie.toNat - ci.toNat, je.toNat - cj.toNat)
decreasing_by
  · have := usize_succ_toNat hj; have := USize.lt_iff_toNat_lt.mp hj
    apply Prod.Lex.right; apply Prod.Lex.right; omega
  · have := usize_succ_toNat hc; have := USize.lt_iff_toNat_lt.mp hc
    apply Prod.Lex.right; apply Prod.Lex.left; omega
  all_goals (have := usize_pred_toNat hf; have := USize.lt_iff_toNat_lt.mp hf;
             simp only [USize.toNat_zero] at *; apply Prod.Lex.left; omega)

/-- `mergeFlatU` in any state equals the nested loops: finish the current
    run (the rest of `crossRightU` for left row `ci`, then `crossLeftU` from
    `ci + 1`), then `mergeLoopU`. -/
theorem mergeFlatU_spec (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (fuel i j : USize) (iv : UInt64) (ci ie j0 cj je m : USize) (oi oa : ByteArray) :
    mergeFlatU st ai na bi ba nb fuel i j iv ci ie j0 cj je m oi oa =
      if ci < ie then
        (match crossRightU st ba iv je cj m oi oa with
         | (oi, oa, m) =>
           match crossLeftU st ba iv j0 je ie (ci + 1) m oi oa with
           | (oi, oa, m) => mergeLoopU st ai na bi ba nb fuel i j m oi oa)
      else mergeLoopU st ai na bi ba nb fuel i j m oi oa := by
  fun_induction mergeFlatU st ai na bi ba nb fuel i j iv ci ie j0 cj je m oi oa with
  | case1 fuel i j iv ci ie j0 cj je m oi oa hc hj ih =>
    rw [ih, if_pos hc, if_pos hc]
    conv => rhs; rw [crossRightU, dif_pos hj]
  | case2 fuel i j iv ci ie j0 cj je m oi oa hc hj ih =>
    rw [ih, if_pos hc]
    conv => rhs; rw [crossRightU, dif_neg hj]
    simp only
    conv => rhs; rw [crossLeftU]
    by_cases h1 : ci + 1 < ie
    · rw [if_pos h1, dif_pos h1]
    · rw [if_neg h1, dif_neg h1]
  | case3 fuel i j iv ci ie j0 cj je m oi oa hc hf hb x y hxy ih =>
    rw [ih, if_neg hc, if_neg hc]
    conv => rhs; rw [mergeLoopU, dif_pos hf, if_pos hb]
    simp only
    rw [if_pos hxy]
  | case4 fuel i j iv ci ie j0 cj je m oi oa hc hf hb x y hxy hyx ih =>
    rw [ih, if_neg hc, if_neg hc]
    conv => rhs; rw [mergeLoopU, dif_pos hf, if_pos hb]
    simp only
    rw [if_neg hxy, if_pos hyx]
  | case5 fuel i j iv ci ie j0 cj je m oi oa hc hf hb x y hxy hyx ie' je' ih =>
    rw [ih, if_neg hc]
    conv => rhs; rw [mergeLoopU, dif_pos hf, if_pos hb]
    simp only
    rw [if_neg hxy, if_neg hyx]
    conv => rhs; rw [crossLeftU]
    by_cases h : i < ie'
    · rw [if_pos h, dif_pos h]
    · rw [if_neg h, dif_neg h]
  | case6 fuel i j iv ci ie j0 cj je m oi oa hc hf hb =>
    rw [if_neg hc, mergeLoopU, dif_pos hf, if_neg hb]
  | case7 fuel i j iv ci ie j0 cj je m oi oa hc hf =>
    rw [if_neg hc, mergeLoopU, dif_neg hf]

/-- Step B of the record, section 8: the fused loop, started outside a run,
    equals `mergeLoopU`. -/
theorem mergeFlatU_eq (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (fuel i j m : USize) (oi oa : ByteArray) :
    mergeFlatU st ai na bi ba nb fuel i j 0 0 0 0 0 0 m oi oa = mergeLoopU st ai na bi ba nb fuel i j m oi oa := by
  rw [mergeFlatU_spec, if_neg (by decide)]

/-- `runEndU` does not pass `n`. -/
theorem runEndU_le (c : ByteArray) (v : UInt64) (n i : USize) (h : i.toNat ≤ n.toNat) :
    (runEndU c v n i).toNat ≤ n.toNat := by
  fun_induction runEndU c v n i with
  | case1 i hi _ ih => exact ih (by have := usize_succ_toNat hi; have := USize.lt_iff_toNat_lt.mp hi; omega)
  | case2 i hi _ => exact h
  | case3 i hi => exact h

/-- `mergeFlatU` with the bounds tests of its loads proved away (record
    section 8, step B, the bounds test per step). The four loads of the loop
    (`ai` and `bi` at the merge step, `ba` in the cross product) are
    `ldU64LEIn`: eight `uget`, no test. The proofs come from `hA`, `hB`,
    `hBa` (the columns hold `na` and `nb` rows, tested once by the caller,
    `mergeFlatIn`), the loop tests `i < na`, `j < nb`, `cj < je`, and the
    invariant `hje : je ≤ nb` (from `runEndU_le`). `mergeFlatP_eq`: equal to
    `mergeFlatU`. -/
@[specialize] def mergeFlatP (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (hA : 8 * na.toNat ≤ ai.usize.toNat) (hB : 8 * nb.toNat ≤ bi.usize.toNat)
    (hBa : 8 * nb.toNat ≤ ba.usize.toNat)
    (fuel i j : USize) (iv : UInt64) (ci ie j0 cj je m : USize) (hje : je.toNat ≤ nb.toNat)
    (oi oa : ByteArray) : ByteArray × ByteArray × USize :=
  if hc : ci < ie then
    if hj : cj < je then
      mergeFlatP ai na bi ba nb hA hB hBa fuel i j iv ci ie j0 (cj + 1) je (m + 1) hje
        (st oi (8 * m) iv)
        (st oa (8 * m) (ldU64LEIn ba (8 * cj) (idx8_window (by have := USize.lt_iff_toNat_lt.mp hj; omega) hBa)))
    else mergeFlatP ai na bi ba nb hA hB hBa fuel i j iv (ci + 1) ie j0 j0 je m hje oi oa
  else if hf : 0 < fuel then
    if hb : i < na ∧ j < nb then
      let x := ldU64LEIn ai (8 * i) (idx8_window (USize.lt_iff_toNat_lt.mp hb.1) hA)
      let y := ldU64LEIn bi (8 * j) (idx8_window (USize.lt_iff_toNat_lt.mp hb.2) hB)
      if x < y then mergeFlatP ai na bi ba nb hA hB hBa (fuel - 1) (i + 1) j iv ci ie j0 cj je m hje oi oa
      else if y < x then mergeFlatP ai na bi ba nb hA hB hBa (fuel - 1) i (j + 1) iv ci ie j0 cj je m hje oi oa
      else
        let ie' := runEndU ai x na (i + 1)
        let je' := runEndU bi x nb (j + 1)
        mergeFlatP ai na bi ba nb hA hB hBa (fuel - 1) ie' je' x i ie' j j je'  m
          (runEndU_le bi x nb (j + 1) (by have := usize_succ_toNat hb.2; have := USize.lt_iff_toNat_lt.mp hb.2; omega))
          oi oa
    else (oi, oa, m)
  else (oi, oa, m)
termination_by (fuel.toNat, ie.toNat - ci.toNat, je.toNat - cj.toNat)
decreasing_by
  · have := usize_succ_toNat hj; have := USize.lt_iff_toNat_lt.mp hj
    apply Prod.Lex.right; apply Prod.Lex.right; omega
  · have := usize_succ_toNat hc; have := USize.lt_iff_toNat_lt.mp hc
    apply Prod.Lex.right; apply Prod.Lex.left; omega
  all_goals (have := usize_pred_toNat hf; have := USize.lt_iff_toNat_lt.mp hf;
             simp only [USize.toNat_zero] at *; apply Prod.Lex.left; omega)

theorem mergeFlatP_eq (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (hA : 8 * na.toNat ≤ ai.usize.toNat) (hB : 8 * nb.toNat ≤ bi.usize.toNat)
    (hBa : 8 * nb.toNat ≤ ba.usize.toNat)
    (fuel i j : USize) (iv : UInt64) (ci ie j0 cj je m : USize) (hje : je.toNat ≤ nb.toNat)
    (oi oa : ByteArray) :
    mergeFlatP st ai na bi ba nb hA hB hBa fuel i j iv ci ie j0 cj je m hje oi oa =
      mergeFlatU st ai na bi ba nb fuel i j iv ci ie j0 cj je m oi oa := by
  fun_induction mergeFlatP st ai na bi ba nb hA hB hBa fuel i j iv ci ie j0 cj je m hje oi oa with
  | case1 fuel i j iv ci ie j0 cj je m hje oi oa hc hj ih =>
    rw [ih]
    conv => rhs; rw [mergeFlatU, dif_pos hc, dif_pos hj]
    rw [ldU64LE_eq_in]
  | case2 fuel i j iv ci ie j0 cj je m hje oi oa hc hj ih =>
    rw [ih]
    conv => rhs; rw [mergeFlatU, dif_pos hc, dif_neg hj]
  | case3 fuel i j iv ci ie j0 cj je m hje oi oa hc hf hb x y hxy ih =>
    rw [ih]
    conv => rhs; rw [mergeFlatU, dif_neg hc, dif_pos hf]
    have hb' : (decide (i < na) && decide (j < nb)) = true := by simp [hb.1, hb.2]
    rw [if_pos hb']
    simp only
    rw [ldU64LE_eq_in ai _ (idx8_window (USize.lt_iff_toNat_lt.mp hb.1) hA),
      ldU64LE_eq_in bi _ (idx8_window (USize.lt_iff_toNat_lt.mp hb.2) hB), if_pos hxy]
  | case4 fuel i j iv ci ie j0 cj je m hje oi oa hc hf hb x y hxy hyx ih =>
    rw [ih]
    conv => rhs; rw [mergeFlatU, dif_neg hc, dif_pos hf]
    have hb' : (decide (i < na) && decide (j < nb)) = true := by simp [hb.1, hb.2]
    rw [if_pos hb']
    simp only
    rw [ldU64LE_eq_in ai _ (idx8_window (USize.lt_iff_toNat_lt.mp hb.1) hA),
      ldU64LE_eq_in bi _ (idx8_window (USize.lt_iff_toNat_lt.mp hb.2) hB), if_neg hxy, if_pos hyx]
  | case5 fuel i j iv ci ie j0 cj je m hje oi oa hc hf hb x y hxy hyx ie' je' ih =>
    rw [ih]
    conv => rhs; rw [mergeFlatU, dif_neg hc, dif_pos hf]
    have hb' : (decide (i < na) && decide (j < nb)) = true := by simp [hb.1, hb.2]
    rw [if_pos hb']
    simp only
    rw [ldU64LE_eq_in ai _ (idx8_window (USize.lt_iff_toNat_lt.mp hb.1) hA),
      ldU64LE_eq_in bi _ (idx8_window (USize.lt_iff_toNat_lt.mp hb.2) hB), if_neg hxy, if_neg hyx]
  | case6 fuel i j iv ci ie j0 cj je m hje oi oa hc hf hb =>
    have hb' : ¬ (decide (i < na) && decide (j < nb)) = true := by
      intro h; apply hb; simpa using h
    rw [mergeFlatU, dif_neg hc, dif_pos hf, if_neg hb']
  | case7 fuel i j iv ci ie j0 cj je m hje oi oa hc hf =>
    rw [mergeFlatU, dif_neg hc, dif_neg hf]

/-- The caller of `mergeFlatP`: ONE test, before the loop, that the three
    columns hold `na` and `nb` rows (`USize` arithmetic only), then the loop
    with no bounds test per load; otherwise `mergeFlatU`. Equal to
    `mergeLoopU` from the start state (`mergeFlatIn_eq`). -/
@[inline] def mergeFlatIn (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (fuel : USize) (oi oa : ByteArray) : ByteArray × ByteArray × USize :=
  if h : na ≤ ai.usize / 8 ∧ nb ≤ bi.usize / 8 ∧ nb ≤ ba.usize / 8 then
    mergeFlatP st ai na bi ba nb (le_div8_toNat h.1) (le_div8_toNat h.2.1) (le_div8_toNat h.2.2)
      fuel 0 0 0 0 0 0 0 0 0 (by simp) oi oa
  else mergeFlatU st ai na bi ba nb fuel 0 0 0 0 0 0 0 0 0 oi oa

theorem mergeFlatIn_eq (ai : ByteArray) (na : USize) (bi ba : ByteArray) (nb : USize)
    (fuel : USize) (oi oa : ByteArray) :
    mergeFlatIn st ai na bi ba nb fuel oi oa = mergeLoopU st ai na bi ba nb fuel 0 0 0 oi oa := by
  unfold mergeFlatIn
  split
  · rw [mergeFlatP_eq, mergeFlatU_eq]
  · rw [mergeFlatU_eq]

/-! ### Step C: the scan filters with the bounds tests of their loads proved away

`filterBU` and `filterAU` test the window of each load (`ldU64LE`: two
compares, then eight `uget`). `filterBP` and `filterAP` take the facts
`8 * n <= c.usize` for the columns they read and use `ldU64LEIn`, as
`mergeFlatP` does. The callers `filterBIn` and `filterAIn` test the facts once
(`n <= c.usize / 8` in `USize`) and otherwise run the tested loop.
`filterBP_eq` and `filterAP_eq`: equal to `filterBU` and `filterAU`;
`filterBIn_eq` and `filterAIn_eq`: the same for the callers. -/

@[specialize] def filterBP (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : USize)
    (h0 : 8 * n.toNat ≤ c0.usize.toNat) (h1 : 8 * n.toNat ≤ c1.usize.toNat)
    (h2 : 8 * n.toNat ≤ c2.usize.toNat) (i m : USize) (o1 o2 : ByteArray) :
    ByteArray × ByteArray × USize :=
  if h : i < n then
    let hi := USize.lt_iff_toNat_lt.mp h
    if ldU64LEIn c0 (8 * i) (idx8_window hi h0) == k0 then
      filterBP c0 c1 c2 k0 n h0 h1 h2 (i + 1) (m + 1)
        (st o1 (8 * m) (ldU64LEIn c1 (8 * i) (idx8_window hi h1)))
        (st o2 (8 * m) (ldU64LEIn c2 (8 * i) (idx8_window hi h2)))
    else filterBP c0 c1 c2 k0 n h0 h1 h2 (i + 1) m o1 o2
  else (o1, o2, m)
termination_by n.toNat - i.toNat
decreasing_by all_goals (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

theorem filterBP_eq (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : USize)
    (h0 : 8 * n.toNat ≤ c0.usize.toNat) (h1 : 8 * n.toNat ≤ c1.usize.toNat)
    (h2 : 8 * n.toNat ≤ c2.usize.toNat) (i m : USize) (o1 o2 : ByteArray) :
    filterBP st c0 c1 c2 k0 n h0 h1 h2 i m o1 o2 = filterBU st c0 c1 c2 k0 n i m o1 o2 := by
  fun_induction filterBP st c0 c1 c2 k0 n h0 h1 h2 i m o1 o2 with
  | case1 i m o1 o2 h hi hk ih =>
    rw [ih]
    conv => rhs; rw [filterBU, dif_pos h]
    simp only
    rw [ldU64LE_eq_in c0 _ (idx8_window hi h0), ldU64LE_eq_in c1 _ (idx8_window hi h1),
      ldU64LE_eq_in c2 _ (idx8_window hi h2), if_pos hk]
  | case2 i m o1 o2 h hi hk ih =>
    rw [ih]
    conv => rhs; rw [filterBU, dif_pos h]
    simp only
    rw [ldU64LE_eq_in c0 _ (idx8_window hi h0), if_neg hk]
  | case3 i m o1 o2 h =>
    conv => rhs; rw [filterBU, dif_neg h]

@[inline] def filterBIn (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : USize) (o1 o2 : ByteArray) :
    ByteArray × ByteArray × USize :=
  if h : n ≤ c0.usize / 8 ∧ n ≤ c1.usize / 8 ∧ n ≤ c2.usize / 8 then
    filterBP st c0 c1 c2 k0 n (le_div8_toNat h.1) (le_div8_toNat h.2.1) (le_div8_toNat h.2.2) 0 0 o1 o2
  else filterBU st c0 c1 c2 k0 n 0 0 o1 o2

theorem filterBIn_eq (c0 c1 c2 : ByteArray) (k0 : UInt64) (n : USize) (o1 o2 : ByteArray) :
    filterBIn st c0 c1 c2 k0 n o1 o2 = filterBU st c0 c1 c2 k0 n 0 0 o1 o2 := by
  unfold filterBIn
  split
  · rw [filterBP_eq]
  · rfl

@[specialize] def filterAP (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : USize)
    (h0 : 8 * n.toNat ≤ c0.usize.toNat) (h1 : 8 * n.toNat ≤ c1.usize.toNat)
    (h2 : 8 * n.toNat ≤ c2.usize.toNat) (i m : USize) (out : ByteArray) :
    ByteArray × USize :=
  if h : i < n then
    let hi := USize.lt_iff_toNat_lt.mp h
    if ldU64LEIn c0 (8 * i) (idx8_window hi h0) == k0 && ldU64LEIn c1 (8 * i) (idx8_window hi h1) == k1 then
      filterAP c0 c1 c2 k0 k1 n h0 h1 h2 (i + 1) (m + 1)
        (st out (8 * m) (ldU64LEIn c2 (8 * i) (idx8_window hi h2)))
    else filterAP c0 c1 c2 k0 k1 n h0 h1 h2 (i + 1) m out
  else (out, m)
termination_by n.toNat - i.toNat
decreasing_by all_goals (have := usize_succ_toNat h; have := USize.lt_iff_toNat_lt.mp h; omega)

theorem filterAP_eq (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : USize)
    (h0 : 8 * n.toNat ≤ c0.usize.toNat) (h1 : 8 * n.toNat ≤ c1.usize.toNat)
    (h2 : 8 * n.toNat ≤ c2.usize.toNat) (i m : USize) (out : ByteArray) :
    filterAP st c0 c1 c2 k0 k1 n h0 h1 h2 i m out = filterAU st c0 c1 c2 k0 k1 n i m out := by
  fun_induction filterAP st c0 c1 c2 k0 k1 n h0 h1 h2 i m out with
  | case1 i m out h hi hk ih =>
    rw [ih]
    conv => rhs; rw [filterAU, dif_pos h]
    simp only
    rw [ldU64LE_eq_in c0 _ (idx8_window hi h0), ldU64LE_eq_in c1 _ (idx8_window hi h1),
      ldU64LE_eq_in c2 _ (idx8_window hi h2), if_pos hk]
  | case2 i m out h hi hk ih =>
    rw [ih]
    conv => rhs; rw [filterAU, dif_pos h]
    simp only
    rw [ldU64LE_eq_in c0 _ (idx8_window hi h0), ldU64LE_eq_in c1 _ (idx8_window hi h1), if_neg hk]
  | case3 i m out h =>
    conv => rhs; rw [filterAU, dif_neg h]

@[inline] def filterAIn (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : USize) (out : ByteArray) :
    ByteArray × USize :=
  if h : n ≤ c0.usize / 8 ∧ n ≤ c1.usize / 8 ∧ n ≤ c2.usize / 8 then
    filterAP st c0 c1 c2 k0 k1 n (le_div8_toNat h.1) (le_div8_toNat h.2.1) (le_div8_toNat h.2.2) 0 0 out
  else filterAU st c0 c1 c2 k0 k1 n 0 0 out

theorem filterAIn_eq (c0 c1 c2 : ByteArray) (k0 k1 : UInt64) (n : USize) (out : ByteArray) :
    filterAIn st c0 c1 c2 k0 k1 n out = filterAU st c0 c1 c2 k0 k1 n 0 0 out := by
  unfold filterAIn
  split
  · rw [filterAP_eq]
  · rfl

end UsizeLoops

def sumLoopU (oi oa : ByteArray) (n : USize) (i : USize) (s : UInt64) : UInt64 :=
  if _h : i < n then sumLoopU oi oa n (i + 1) (s + ldU64LE oi (8 * i) * mixK + ldU64LE oa (8 * i)) else s
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

def runUsize (x : Input) : Nat × UInt64 := runUsizeWith stU64LERef x

def runUsizeCStore (x : Input) : Nat × UInt64 := runUsizeWith stU64LE x

/-! ## Record section 8: no buffer copies (step A), no tuple per run (step B)

`usize-cstore-flat`: `usize-cstore` with `mergeFlatU` in place of
`mergeLoopU` (step B alone; `mergeFlatU_eq`).

`usize-cpush`: the output buffers start EMPTY (`ByteArray.emptyWithCapacity`,
an allocation and no copy) and each Id is appended with
`Prim.Bytes.pushU64LE`, the library's `@[extern c inline]` append (step A
alone). The store argument `st` of the loops ignores the position:
`pushAt b _ x = pushU64LE b x`. The `scratch` copies of `usize-cstore` (five
per run, four of 2.16 MB: three `scratch` calls, and two copies on the first
store into the two `scratch` buffers that the compiler shares) go away. A
buffer that is too small grows (`pushU64LE` falls back to the runtime's
`lean_byte_array_push`), so this variant is correct for any input; the
`stU64LE` variants drop a row that does not fit their buffer.

`usize-cpush-flat`: both.

`usize-cpush-in`: `usize-cpush-flat` with `mergeFlatIn`: one test before the
merge loop that the columns hold `na` and `nb` rows, then no bounds test in
the loads of the loop (`mergeFlatP`; `mergeFlatIn_eq`). -/

/-- The store argument of the loops for the append variants: append `x`; the
    position is not used. -/
@[inline] def pushAt (b : ByteArray) (_ : USize) (x : UInt64) : ByteArray := pushU64LE b x

/-- Push without tests; used only on arrays returned by `reserveU64` (record section 9, step D). -/
@[inline] def pushAtU (b : ByteArray) (_ : USize) (x : UInt64) : ByteArray := pushU64LEUnchecked b x

/-- A new empty buffer of capacity at least `n` (`n + tag`). Distinct tags
    keep the compiler from making equal calls one shared object: it does so
    for equal pure expressions (seen in the generated C: the four
    `ByteArray.emptyWithCapacity (8 * x.nB)` of `runUsizeCPush` became one
    object with four references, and the first append to each buffer then
    took the slow path and a new allocation). A tag that is not used does not
    help: the compiler removes the unused parameter (`newBuf___redArg`) and
    shares the calls again. The capacity is not observable in Lean. -/
@[inline] def newBuf (n : Nat) (tag : Nat) : ByteArray := ByteArray.emptyWithCapacity (n + tag)

def runUsizeCStoreFlat (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAU stU64LE x.a0 x.a1 x.a2 x.kA0 x.kA1 nA 0 0 (scratch x.a2 (8 * x.nA))
  let (bi, ba, nb) := filterBU stU64LE x.b0 x.b1 x.b2 x.kB0 nB 0 0 (scratch x.b1 (8 * x.nB)) (scratch x.b2 (8 * x.nB))
  let (oi, oa, n) := mergeFlatU stU64LE ai na bi ba nb (na + nb + 1) 0 0 0 0 0 0 0 0 0
    (scratch x.b1 (8 * x.nB)) (scratch x.b2 (8 * x.nB))
  (n.toNat, sumLoopU oi oa n 0 0)

def runUsizeCPush (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAU pushAt x.a0 x.a1 x.a2 x.kA0 x.kA1 nA 0 0 (newBuf (8 * x.nA) 1)
  let (bi, ba, nb) := filterBU pushAt x.b0 x.b1 x.b2 x.kB0 nB 0 0
    (newBuf (8 * x.nB) 2) (newBuf (8 * x.nB) 3)
  let (oi, oa, n) := mergeLoopU pushAt ai na bi ba nb (na + nb + 1) 0 0 0
    (newBuf (8 * x.nB) 4) (newBuf (8 * x.nB) 5)
  (n.toNat, sumLoopU oi oa n 0 0)

def runUsizeCPushFlat (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAU pushAt x.a0 x.a1 x.a2 x.kA0 x.kA1 nA 0 0 (newBuf (8 * x.nA) 1)
  let (bi, ba, nb) := filterBU pushAt x.b0 x.b1 x.b2 x.kB0 nB 0 0
    (newBuf (8 * x.nB) 2) (newBuf (8 * x.nB) 3)
  let (oi, oa, n) := mergeFlatU pushAt ai na bi ba nb (na + nb + 1) 0 0 0 0 0 0 0 0 0
    (newBuf (8 * x.nB) 4) (newBuf (8 * x.nB) 5)
  (n.toNat, sumLoopU oi oa n 0 0)

def runUsizeCPushIn (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAU pushAt x.a0 x.a1 x.a2 x.kA0 x.kA1 nA 0 0 (newBuf (8 * x.nA) 1)
  let (bi, ba, nb) := filterBU pushAt x.b0 x.b1 x.b2 x.kB0 nB 0 0
    (newBuf (8 * x.nB) 2) (newBuf (8 * x.nB) 3)
  let (oi, oa, n) := mergeFlatIn pushAt ai na bi ba nb (na + nb + 1)
    (newBuf (8 * x.nB) 4) (newBuf (8 * x.nB) 5)
  (n.toNat, sumLoopU oi oa n 0 0)

/-- `usize-cpush-filt` with the output buffers of the B filter reserved once:
    `n` rows of 8 bytes, at most `n` pushes (`m <= i <= n`), then no test per push. -/
def runUsizeCPushRes (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAIn pushAtU x.a0 x.a1 x.a2 x.kA0 x.kA1 nA (reserveU64 (newBuf (8 * x.nA) 1) nA)
  let (bi, ba, nb) := filterBIn pushAtU x.b0 x.b1 x.b2 x.kB0 nB
    (reserveU64 (newBuf (8 * x.nB) 2) nB) (reserveU64 (newBuf (8 * x.nB) 3) nB)
  let (oi, oa, n) := mergeFlatIn pushAt ai na bi ba nb (na + nb + 1)
    (newBuf (8 * x.nB) 4) (newBuf (8 * x.nB) 5)
  (n.toNat, sumLoopU oi oa n 0 0)

def runUsizeCPushFilt (x : Input) : Nat × UInt64 :=
  let nA := x.nA.toUSize
  let nB := x.nB.toUSize
  let (ai, na) := filterAIn pushAt x.a0 x.a1 x.a2 x.kA0 x.kA1 nA (newBuf (8 * x.nA) 1)
  let (bi, ba, nb) := filterBIn pushAt x.b0 x.b1 x.b2 x.kB0 nB
    (newBuf (8 * x.nB) 2) (newBuf (8 * x.nB) 3)
  let (oi, oa, n) := mergeFlatIn pushAt ai na bi ba nb (na + nb + 1)
    (newBuf (8 * x.nB) 4) (newBuf (8 * x.nB) 5)
  (n.toNat, sumLoopU oi oa n 0 0)

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

/-! ## The timing loop

Shared by `l4qlvr kernel` (Harness/Qlvr.lean) and `l4qlvr-kernel`
(Harness/QlvrKernelBench.lean, which builds for wasm32 with
tools/lean-wasm-exe.sh: its import closure has no FFI). -/

@[noinline] def kernelOnce (impl : Nat) (x : Input) (fx : FInput) (ux : UInput) : IO (Nat × UInt64) :=
  pure (match impl with
    | 0 => runCurrent x
    | 1 => runBytes x
    | 2 => runBytesSet x
    | 3 => runFloats fx
    | 4 => runProduction x
    | 5 => runNative ux
    | 6 => runUsize x
    | 7 => runUsizeCStore x
    | 8 => runUsizeCStoreFlat x
    | 9 => runUsizeCPush x
    | 10 => runUsizeCPushFlat x
    | 11 => runUsizeCPushIn x
    | 12 => runUsizeCPushFilt x
    | _ => runUsizeCPushRes x)

def medianNat (xs : Array Nat) : Nat :=
  let s := mergeSortBy xs (· ≤ ·)
  if s.isEmpty then 0 else s[(s.size - 1) / 2]!

/-- Run every Lean implementation of the kernel on the input file contents
    `data`, `iters` times; print the
    median and minimum time of one run, the output rows and the checksum.
    Exit code 1 when the implementations disagree. -/
def runKernel (data : ByteArray) (iters : Nat) : IO UInt32 := do
  let x ← match Input.parse data with
    | .ok x => pure x
    | .error e => throw (IO.userError s!"kernel: {e}")
  let fx := FInput.ofInput x
  let ux := UInput.ofInput x
  let names := #["current", "bytes-push", "bytes-set", "floats", "production", "native", "usize", "usize-cstore",
    "usize-cstore-flat", "usize-cpush", "usize-cpush-flat", "usize-cpush-in", "usize-cpush-filt", "usize-cpush-res"]
  let mut sums : Array (Nat × UInt64) := #[]
  for impl in [0:names.size] do
    let mut ts : Array Nat := #[]
    let mut r : Nat × UInt64 := (0, 0)
    for _ in [0:max iters 1] do
      let a ← IO.monoNanosNow
      r ← kernelOnce impl x fx ux
      let b ← IO.monoNanosNow
      ts := ts.push (b - a)
    sums := sums.push r
    let us := ts.map (· / 1000)
    IO.println s!"kernel lean-{names[impl]!}: A {x.nA} rows, B {x.nB} rows; output {r.1} rows, checksum {r.2}; us median {medianNat us} min {us.foldl min (us.getD 0 0)} ({ts.size} runs)"
  let agree := sums.all (· == sums[0]!)
  IO.println s!"kernel: implementations {if agree then "agree" else "DISAGREE"}"
  return (if agree then 0 else 1)

end QlvrKernel
