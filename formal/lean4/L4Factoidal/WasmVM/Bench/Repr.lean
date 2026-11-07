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
  time "D FloatArray in structure" n fun _ => loopM n 0 { st := fa, sp := 16, acc := 0, pc := 0 }

end L4Factoidal.WasmVM.Bench.Repr
