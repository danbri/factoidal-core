/-! Register-file representations compared (standalone; Init only).
A: NaN-boxed UInt64 words in a ByteArray (8 byte loads, Float.ofBits / toBits).
B: struct of arrays: tag ByteArray + FloatArray numbers + ByteArray 32-bit references.
C: 32-bit tagged words in a ByteArray (small integers inline, a double is a reference to a number cell).
R: today's shape: Array of a boxed inductive + FloatArray. -/

@[inline] def rd64 (b : ByteArray) (i : Nat) : UInt64 :=
  let o := 8 * i
  (b.get! o).toUInt64 ||| ((b.get! (o+1)).toUInt64 <<< 8) ||| ((b.get! (o+2)).toUInt64 <<< 16) ||| ((b.get! (o+3)).toUInt64 <<< 24) |||
  ((b.get! (o+4)).toUInt64 <<< 32) ||| ((b.get! (o+5)).toUInt64 <<< 40) ||| ((b.get! (o+6)).toUInt64 <<< 48) ||| ((b.get! (o+7)).toUInt64 <<< 56)

@[inline] def wr64 (b : ByteArray) (i : Nat) (w : UInt64) : ByteArray :=
  let o := 8 * i
  ((((((((b.set! o w.toUInt8).set! (o+1) (w >>> 8).toUInt8).set! (o+2) (w >>> 16).toUInt8).set! (o+3) (w >>> 24).toUInt8).set! (o+4) (w >>> 32).toUInt8).set! (o+5) (w >>> 40).toUInt8).set! (o+6) (w >>> 48).toUInt8).set! (o+7) (w >>> 56).toUInt8)

@[inline] def rd32 (b : ByteArray) (i : Nat) : UInt32 :=
  let o := 4 * i
  (b.get! o).toUInt32 ||| ((b.get! (o+1)).toUInt32 <<< 8) ||| ((b.get! (o+2)).toUInt32 <<< 16) ||| ((b.get! (o+3)).toUInt32 <<< 24)

@[inline] def wr32 (b : ByteArray) (i : Nat) (w : UInt32) : ByteArray :=
  let o := 4 * i
  ((((b.set! o w.toUInt8).set! (o+1) (w >>> 8).toUInt8).set! (o+2) (w >>> 16).toUInt8).set! (o+3) (w >>> 24).toUInt8)

/-- A: a word is a double unless its top 16 bits are 0xFFF9..0xFFFF (tags). -/
@[inline] def isNumA (w : UInt64) : Bool := w < 0xFFF9000000000000

def loopA (n : Nat) (r : ByteArray) : ByteArray :=
  match n with
  | 0 => r
  | n + 1 =>
    let a := rd64 r 1; let b := rd64 r 2
    if isNumA a && isNumA b then
      loopA n (wr64 r 1 (Float.toBits (Float.ofBits a + Float.ofBits b)))
    else loopA n r

structure RegsB where
  tag : ByteArray
  num : FloatArray
  ref : ByteArray

def loopB (n : Nat) (r : RegsB) : RegsB :=
  match n with
  | 0 => r
  | n + 1 =>
    if r.tag.get! 1 == 0 && r.tag.get! 2 == 0 then
      let x := r.num.get! 1 + r.num.get! 2
      loopB n { r with tag := r.tag.set! 1 0, num := r.num.set! 1 x }
    else loopB n r

/-- C: bit 0 set: a 31-bit integer; else a reference. Overflow goes to a number cell (not modelled: counted). -/
def loopC (n : Nat) (r : ByteArray) (slow : Nat) : ByteArray × Nat :=
  match n with
  | 0 => (r, slow)
  | n + 1 =>
    let a := rd32 r 1; let b := rd32 r 2
    if a &&& 1 == 1 && b &&& 1 == 1 then
      let s := (a >>> 1).toUInt64 + (b >>> 1).toUInt64
      if s < 0x40000000 then loopC n (wr32 r 1 ((s.toUInt32 <<< 1) ||| 1)) slow
      else loopC n (wr32 r 1 1) (slow + 1)
    else loopC n r slow

inductive V where
  | undef | fl | obj (i : Nat)

def loopR (n : Nat) (regs : Array V) (f : FloatArray) : Array V × FloatArray :=
  match n with
  | 0 => (regs, f)
  | n + 1 =>
    match regs[1]!, regs[2]! with
    | .fl, .fl => loopR n (regs.set! 1 .fl) (f.set! 1 (f.get! 1 + f.get! 2))
    | _, _ => loopR n regs f

/-- A move of a reference between slots (object handles): the other common instruction. -/
def moveA (n : Nat) (r : ByteArray) : ByteArray :=
  match n with
  | 0 => r
  | n + 1 => moveA n (wr64 r 3 (rd64 r 4))

def moveB (n : Nat) (r : RegsB) : RegsB :=
  match n with
  | 0 => r
  | n + 1 =>
    let t := r.tag.get! 4
    if t == 0 then moveB n { r with tag := r.tag.set! 3 0, num := r.num.set! 3 (r.num.get! 4) }
    else moveB n { r with tag := r.tag.set! 3 t, ref := wr32 r.ref 3 (rd32 r.ref 4) }

def moveR (n : Nat) (regs : Array V) : Array V :=
  match n with
  | 0 => regs
  | n + 1 => moveR n (regs.set! 3 regs[4]!)

def timeIt (name : String) (f : Unit → UInt64) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := f ()
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {(t1 - t0) / 1000000} ms (check {r})"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 100000000
  let ba : ByteArray := ByteArray.mk (Array.replicate 128 0)
  let a0 := wr64 (wr64 ba 1 (Float.toBits 0.5)) 2 (Float.toBits 1.25)
  let a0 := wr64 a0 4 0xFFFA000000001234
  timeIt "A add  (NaN-boxed words in ByteArray)" fun _ => rd64 (loopA n a0) 1
  timeIt "A move" fun _ => rd64 (moveA n a0) 3
  let fb : FloatArray := FloatArray.mk (Array.replicate 16 0.0)
  let b0 : RegsB := { tag := (ba.extract 0 16).set! 4 5, num := (fb.set! 1 0.5).set! 2 1.25, ref := wr32 (ba.extract 0 64) 4 0x1234 }
  timeIt "B add  (tag bytes + FloatArray + 32-bit refs)" fun _ => Float.toBits ((loopB n b0).num.get! 1)
  timeIt "B move" fun _ => (rd32 (moveB n b0).ref 3).toUInt64
  let c0 := wr32 (wr32 (ba.extract 0 64) 1 1) 2 ((7 <<< 1) ||| 1)
  timeIt "C add  (32-bit tagged words, int31 inline)" fun _ => let (r, s) := loopC n c0 0; (rd32 r 1).toUInt64 + s.toUInt64
  let r0 : Array V := (Array.replicate 16 V.undef |>.set! 1 .fl |>.set! 2 .fl |>.set! 4 (.obj 0x1234))
  timeIt "R add  (Array of boxed inductive + FloatArray: today)" fun _ => let (_, f) := loopR n r0 ((fb.set! 1 0.5).set! 2 1.25); Float.toBits (f.get! 1)
  timeIt "R move" fun _ => match (moveR n r0)[3]! with | .obj i => i.toUInt64 | _ => 0
