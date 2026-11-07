/-
L4Factoidal.WasmVM.Bench.Repr: measures candidate representations of the operand
stack of the interpreter (issue https://github.com/danbri/factoidal/issues/1244).
Each variant runs the same stack program, n times:
  push i; push acc; add; pop into acc.
-/
namespace L4Factoidal.WasmVM.Bench.Repr

/-- Variant A: unboxed 64-bit slots in a `FloatArray`, read and written as bits. -/
def loopFA (n : Nat) (i acc sp : Nat) (st : FloatArray) : UInt64 :=
  match n with
  | 0 => (st.get! 0).toBits + acc.toUInt64
  | n + 1 =>
    let st := st.set! sp (Float.ofBits i.toUInt64)
    let st := st.set! (sp + 1) (Float.ofBits acc.toUInt64)
    let a := (st.get! sp).toBits
    let b := (st.get! (sp + 1)).toBits
    let st := st.set! sp (Float.ofBits (a + b))
    loopFA n (i + 1) (st.get! sp).toBits.toNat sp st

/-- Variant B: `Array UInt64` slots (each slot a boxed object). -/
def loopAU (n : Nat) (i acc sp : Nat) (st : Array UInt64) : UInt64 :=
  match n with
  | 0 => st[0]! + acc.toUInt64
  | n + 1 =>
    let st := st.set! sp i.toUInt64
    let st := st.set! (sp + 1) acc.toUInt64
    let a := st[sp]!
    let b := st[sp + 1]!
    let st := st.set! sp (a + b)
    loopAU n (i + 1) st[sp]!.toNat sp st

/-- Variant C: a `ByteArray` with 8 bytes per slot, little-endian. -/
@[inline] def rd (b : ByteArray) (i : Nat) : UInt64 :=
  let o := i * 8
  (b.get! o).toUInt64 ||| ((b.get! (o+1)).toUInt64 <<< 8) ||| ((b.get! (o+2)).toUInt64 <<< 16)
  ||| ((b.get! (o+3)).toUInt64 <<< 24) ||| ((b.get! (o+4)).toUInt64 <<< 32)
  ||| ((b.get! (o+5)).toUInt64 <<< 40) ||| ((b.get! (o+6)).toUInt64 <<< 48)
  ||| ((b.get! (o+7)).toUInt64 <<< 56)
@[inline] def wr (b : ByteArray) (i : Nat) (v : UInt64) : ByteArray :=
  let o := i * 8
  let b := b.set! o v.toUInt8
  let b := b.set! (o+1) (v >>> 8).toUInt8
  let b := b.set! (o+2) (v >>> 16).toUInt8
  let b := b.set! (o+3) (v >>> 24).toUInt8
  let b := b.set! (o+4) (v >>> 32).toUInt8
  let b := b.set! (o+5) (v >>> 40).toUInt8
  let b := b.set! (o+6) (v >>> 48).toUInt8
  b.set! (o+7) (v >>> 56).toUInt8
def loopBA (n : Nat) (i acc sp : Nat) (st : ByteArray) : UInt64 :=
  match n with
  | 0 => rd st 0 + acc.toUInt64
  | n + 1 =>
    let st := wr st sp i.toUInt64
    let st := wr st (sp + 1) acc.toUInt64
    let a := rd st sp
    let b := rd st (sp + 1)
    let st := wr st sp (a + b)
    loopBA n (i + 1) (rd st sp).toNat sp st

/-- Variant E: variant C with one bounds check per access; the 8 byte reads use
proved indices (`b[o+k]'h`), so the C compiler sees plain loads. -/
@[inline] def rdP (b : ByteArray) (i : Nat) : UInt64 :=
  let o := i * 8
  if h : o + 8 ≤ b.size then
    b[o].toUInt64 ||| (b[o+1].toUInt64 <<< 8) ||| (b[o+2].toUInt64 <<< 16)
    ||| (b[o+3].toUInt64 <<< 24) ||| (b[o+4].toUInt64 <<< 32)
    ||| (b[o+5].toUInt64 <<< 40) ||| (b[o+6].toUInt64 <<< 48)
    ||| (b[o+7].toUInt64 <<< 56)
  else 0
@[inline] def wrP (b : ByteArray) (i : Nat) (v : UInt64) : ByteArray :=
  let o := i * 8
  if o + 8 ≤ b.size then
    let b := b.set! (o) v.toUInt8
    let b := b.set! (o+1) (v >>> 8).toUInt8
    let b := b.set! (o+2) (v >>> 16).toUInt8
    let b := b.set! (o+3) (v >>> 24).toUInt8
    let b := b.set! (o+4) (v >>> 32).toUInt8
    let b := b.set! (o+5) (v >>> 40).toUInt8
    let b := b.set! (o+6) (v >>> 48).toUInt8
    b.set! (o+7) (v >>> 56).toUInt8
  else b
def loopBP (n : Nat) (i acc sp : Nat) (st : ByteArray) : UInt64 :=
  match n with
  | 0 => rdP st 0 + acc.toUInt64
  | n + 1 =>
    let st := wrP st sp i.toUInt64
    let st := wrP st (sp + 1) acc.toUInt64
    let a := rdP st sp
    let b := rdP st (sp + 1)
    let st := wrP st sp (a + b)
    loopBP n (i + 1) (rdP st sp).toNat sp st


/-- Variant F: a `ByteArray` with `USize` slot indices and ONE check per access
(`i < s.usize / 8`); the 8 byte indices are proved in range from it
(`slot_byte`), so the reads are `uget` and the writes `uset`. -/
theorem usize_le (s : ByteArray) : s.usize.toNat ≤ s.size ∧ s.usize.toNat < USize.size := by
  simp only [ByteArray.usize]
  constructor
  · simp [Nat.toUSize]; exact Nat.mod_le _ _
  · exact USize.toNat_lt_size _

theorem slot_byte (s : ByteArray) (i : USize) (h : i < s.usize / 8) (k : USize) (hk : k.toNat < 8) :
    (i * 8 + k).toNat < s.size := by
  have ⟨h1, h2⟩ := usize_le s
  rw [USize.lt_iff_toNat_lt, USize.toNat_div] at h
  have h8 : (8 : USize).toNat = 8 := by simp
  rw [h8] at h
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, USize.toNat_mul, h8]
  rw [Nat.mod_eq_of_lt (a := i.toNat * 8) (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem uset_usize (s : ByteArray) (i : USize) (v : UInt8) (h) : (s.uset i v h).usize = s.usize := by
  cases s; simp only [ByteArray.uset, ByteArray.usize, ByteArray.size, Array.size_uset]

@[inline] def rdF (s : ByteArray) (i : USize) : UInt64 :=
  if h : i < s.usize / 8 then
    let o := i * 8
    (s.uget (o+0) (slot_byte s i h 0 (by simp))).toUInt64
    ||| ((s.uget (o+1) (slot_byte s i h 1 (by simp))).toUInt64 <<< 8)
    ||| ((s.uget (o+2) (slot_byte s i h 2 (by simp))).toUInt64 <<< 16)
    ||| ((s.uget (o+3) (slot_byte s i h 3 (by simp))).toUInt64 <<< 24)
    ||| ((s.uget (o+4) (slot_byte s i h 4 (by simp))).toUInt64 <<< 32)
    ||| ((s.uget (o+5) (slot_byte s i h 5 (by simp))).toUInt64 <<< 40)
    ||| ((s.uget (o+6) (slot_byte s i h 6 (by simp))).toUInt64 <<< 48)
    ||| ((s.uget (o+7) (slot_byte s i h 7 (by simp))).toUInt64 <<< 56)
  else 0

@[inline] def wrF (s : ByteArray) (i : USize) (v : UInt64) : ByteArray :=
  if h : i < s.usize / 8 then
    let o := i * 8
    let s1 := s.uset (o+0) v.toUInt8 (slot_byte s i h 0 (by simp))
    have h1 : i < s1.usize / 8 := by rw [uset_usize]; exact h
    let s2 := s1.uset (o+1) (v >>> 8).toUInt8 (slot_byte s1 i h1 1 (by simp))
    have h2 : i < s2.usize / 8 := by rw [uset_usize]; exact h1
    let s3 := s2.uset (o+2) (v >>> 16).toUInt8 (slot_byte s2 i h2 2 (by simp))
    have h3 : i < s3.usize / 8 := by rw [uset_usize]; exact h2
    let s4 := s3.uset (o+3) (v >>> 24).toUInt8 (slot_byte s3 i h3 3 (by simp))
    have h4 : i < s4.usize / 8 := by rw [uset_usize]; exact h3
    let s5 := s4.uset (o+4) (v >>> 32).toUInt8 (slot_byte s4 i h4 4 (by simp))
    have h5 : i < s5.usize / 8 := by rw [uset_usize]; exact h4
    let s6 := s5.uset (o+5) (v >>> 40).toUInt8 (slot_byte s5 i h5 5 (by simp))
    have h6 : i < s6.usize / 8 := by rw [uset_usize]; exact h5
    let s7 := s6.uset (o+6) (v >>> 48).toUInt8 (slot_byte s6 i h6 6 (by simp))
    have h7 : i < s7.usize / 8 := by rw [uset_usize]; exact h6
    s7.uset (o+7) (v >>> 56).toUInt8 (slot_byte s7 i h7 7 (by simp))
  else s

def loopBF (n : Nat) (i acc : UInt64) (sp : USize) (st : ByteArray) : UInt64 :=
  match n with
  | 0 => rdF st 0 + acc
  | n + 1 =>
    let st := wrF st sp i
    let st := wrF st (sp + 1) acc
    let a := rdF st sp
    let b := rdF st (sp + 1)
    let st := wrF st sp (a + b)
    loopBF n (i + 1) (rdF st sp) sp st

/-- Variant G: variant F without the stores' byte-by-byte form: reads only, to
separate read cost from write cost. -/
def loopRF (n : Nat) (acc : UInt64) (sp : USize) (st : ByteArray) : UInt64 :=
  match n with
  | 0 => acc
  | n + 1 => loopRF n (acc + rdF st sp + rdF st (sp + 1)) sp st


/-- Variant X (measurement only): one 8-byte load and store in inline C. -/
@[extern c inline "({ uint64_t v_; __builtin_memcpy(&v_, lean_sarray_cptr(#1) + (#2) * 8, 8); v_; })"]
def rdX (s : @& ByteArray) (i : USize) (h : i < s.usize / 8) : UInt64 := rdF s i
@[extern c inline "({ lean_object * r_ = lean_is_exclusive(#1) ? #1 : lean_copy_byte_array(#1); uint64_t v_ = #3; __builtin_memcpy(lean_sarray_cptr(r_) + (#2) * 8, &v_, 8); r_; })"]
def wrX (s : ByteArray) (i : USize) (v : UInt64) (h : i < s.usize / 8) : ByteArray := wrF s i v
@[inline] def rdXc (s : ByteArray) (i : USize) : UInt64 := if h : i < s.usize / 8 then rdX s i h else 0
@[inline] def wrXc (s : ByteArray) (i : USize) (v : UInt64) : ByteArray := if h : i < s.usize / 8 then wrX s i v h else s
def loopBX (n : Nat) (i acc : UInt64) (sp : USize) (st : ByteArray) : UInt64 :=
  match n with
  | 0 => rdXc st 0 + acc
  | n + 1 =>
    let st := wrXc st sp i
    let st := wrXc st (sp + 1) acc
    let a := rdXc st sp
    let b := rdXc st (sp + 1)
    let st := wrXc st sp (a + b)
    loopBX n (i + 1) (rdXc st sp) sp st

/-- Variant D: variant A, with the stack inside a machine structure updated by
`{ m with .. }` (tests whether field updates stay in place). -/
structure M where
  st : FloatArray
  sp : Nat
  acc : UInt64
  pc : Nat

def loopM (n : Nat) (i : Nat) (m : M) : UInt64 :=
  match n with
  | 0 => (m.st.get! 0).toBits + m.acc
  | n + 1 =>
    let m := { m with st := m.st.set! m.sp (Float.ofBits i.toUInt64) }
    let m := { m with st := m.st.set! (m.sp + 1) (Float.ofBits m.acc) }
    let a := (m.st.get! m.sp).toBits
    let b := (m.st.get! (m.sp + 1)).toBits
    let m := { m with st := m.st.set! m.sp (Float.ofBits (a + b)), pc := m.pc + 1 }
    loopM n (i + 1) { m with acc := (m.st.get! m.sp).toBits }

def time (label : String) (n : Nat) (f : Unit → UInt64) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← IO.lazyPure f
  let t1 ← IO.monoNanosNow
  let ns := t1 - t0
  IO.println s!"{label}: {n} iterations, {ns / 1000000} ms, {ns / n} ns/iter (result {r})"

def run (n : Nat) : IO Unit := do
  let fa : FloatArray := ⟨Array.replicate 1024 0.0⟩
  time "A FloatArray bits, loop args" n fun _ => loopFA n 0 0 16 fa
  time "B Array UInt64, loop args" n fun _ => loopAU n 0 0 16 (Array.replicate 1024 0)
  time "C ByteArray 8 bytes/slot" n fun _ => loopBA n 0 0 16 (ByteArray.mk (Array.replicate 8192 0))
  time "E ByteArray, proved byte indices" n fun _ => loopBP n 0 0 16 (ByteArray.mk (Array.replicate 8192 0))
  time "F ByteArray, USize index, one check" n fun _ => loopBF n 0 0 16 (ByteArray.mk (Array.replicate 8192 0))
  time "X inline C 8-byte load/store, one check" n fun _ => loopBX n 0 0 16 (ByteArray.mk (Array.replicate 8192 0))
  time "G reads only (F form)" n fun _ => loopRF n 0 16 (ByteArray.mk (Array.replicate 8192 1))
  time "D FloatArray in structure" n fun _ => loopM n 0 { st := fa, sp := 16, acc := 0, pc := 0 }

end L4Factoidal.WasmVM.Bench.Repr
