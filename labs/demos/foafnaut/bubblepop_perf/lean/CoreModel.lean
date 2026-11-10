/-!
# CoreModel — what the proposed BubblePopJS core costs in compiled Lean

A measurement program, not engine code. Record: `docs/designissues/2026-11-09-bubblepopjs-plan.md`.
Run: `labs/demos/foafnaut/bubblepop_perf/lean/run.sh` (it prints this file's table last).

The machine here has the data layout that the plan proposes, and nothing else of a JavaScript
engine:

- a value is one 64-bit word. A number is its IEEE 754 bits. Every other value is a word above
  `0xFFF8000000000000` (a bit pattern that no arithmetic result has): a tag in the top 16 bits
  and a payload below. `Float.ofBits` is applied only to a word that is a number, so the fact
  that Lean 4.33 makes every NaN the canonical NaN does not lose a tag (the WasmVM record,
  "Operand-stack representation", has the case where it did);
- registers are 8-byte words of one `ByteArray` that the loop owns. No value is a Lean object, so
  a register read or write changes no reference count and allocates nothing;
- code is 32-bit words (`op | a << 8 | b << 16 | c << 24`). The inline cache of a property access
  is the two words after the instruction;
- objects are words of a second `ByteArray`: the shape number, then the property slots.
  Allocation moves a top-of-heap index. There is no collector in this model;
- a call moves the register base. The return address, the caller's base and the destination
  register are three words below the new base. No Lean call and no frame object;
- one tail-recursive function with a step budget, `USize` indices, one bounds test for each
  access, and one exit function.

It has the checks that JavaScript needs on these paths: a number test before arithmetic, an
object test and a shape test before a property access. It has no strings, no property addition,
no prototype chain and no exceptions: those are slow paths in an engine, off the paths measured.

The 8-byte load and store are copies of `ld64` and `st64` of
`formal/lean4/L4Factoidal/WasmVM/Exec/Bytes.lean` (the store is inline C, with the Lean `uset`
chain as its reference body), so that this file compiles with no import.

Operations: 0 HALT. 1 ADD a b c. 2 LT a b c. 3 JMPF a t. 4 JMP t. 5 MOVE a b. 6 LOADK a k.
7 GETPROP a b key, then two cache words. 8 SETPROP a key c, then two cache words.
9 NEWOBJ a b c, then the shape word. 10 CALL a _ base, then the entry pc. 11 RET a.
12 SUB a b c. (`t` and `k` are `b + 256 c`.)
-/

namespace CoreModel

/-! ## 8-byte words in a `ByteArray` (after `WasmVM/Exec/Bytes.lean`) -/

theorem usize_le (s : ByteArray) : s.usize.toNat ≤ s.size := by
  simp only [ByteArray.usize]; simp [Nat.toUSize]; exact Nat.mod_le _ _

theorem byte_ok {s : ByteArray} {o : USize} {w : Nat} (h : o.toNat + w ≤ s.usize.toNat)
    (k : USize) (hk : k.toNat < w) : (o + k).toNat < s.size := by
  have h1 := usize_le s
  have h2 := USize.toNat_lt_size s.usize
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, Nat.mod_eq_of_lt (by omega)]
  omega

theorem uset_usize (s : ByteArray) (i : USize) (v : UInt8) (h) : (s.uset i v h).usize = s.usize := by
  cases s; simp only [ByteArray.uset, ByteArray.usize, ByteArray.size, Array.size_uset]

theorem keep {s : ByteArray} {o : USize} {w : Nat} {i : USize} {b : UInt8} {hi}
    (h : o.toNat + w ≤ s.usize.toNat) : o.toNat + w ≤ (s.uset i b hi).usize.toNat := by
  rw [uset_usize]; exact h

@[inline] def ld64 (s : ByteArray) (o : USize) (h : o.toNat + 8 ≤ s.usize.toNat) : UInt64 :=
  (s.uget (o+0) (byte_ok h 0 (by simp))).toUInt64
  ||| ((s.uget (o+1) (byte_ok h 1 (by simp))).toUInt64 <<< 8)
  ||| ((s.uget (o+2) (byte_ok h 2 (by simp))).toUInt64 <<< 16)
  ||| ((s.uget (o+3) (byte_ok h 3 (by simp))).toUInt64 <<< 24)
  ||| ((s.uget (o+4) (byte_ok h 4 (by simp))).toUInt64 <<< 32)
  ||| ((s.uget (o+5) (byte_ok h 5 (by simp))).toUInt64 <<< 40)
  ||| ((s.uget (o+6) (byte_ok h 6 (by simp))).toUInt64 <<< 48)
  ||| ((s.uget (o+7) (byte_ok h 7 (by simp))).toUInt64 <<< 56)

@[extern c inline "({ lean_object * r_ = lean_is_exclusive(#1) ? #1 : lean_copy_byte_array(#1); uint64_t v_ = (#3); if (__BYTE_ORDER__ == __ORDER_BIG_ENDIAN__) v_ = __builtin_bswap64(v_); __builtin_memcpy(lean_sarray_cptr(r_) + (#2), &v_, 8); r_; })"]
def st64 (s : ByteArray) (o : USize) (v : UInt64) (h : o.toNat + 8 ≤ s.usize.toNat) : ByteArray :=
  let s1 := s.uset (o+0) v.toUInt8 (byte_ok h 0 (by simp))
  let s2 := s1.uset (o+1) (v >>> 8).toUInt8 (byte_ok (keep h) 1 (by simp))
  let s3 := s2.uset (o+2) (v >>> 16).toUInt8 (byte_ok (keep (keep h)) 2 (by simp))
  let s4 := s3.uset (o+3) (v >>> 24).toUInt8 (byte_ok (keep (keep (keep h))) 3 (by simp))
  let s5 := s4.uset (o+4) (v >>> 32).toUInt8 (byte_ok (keep (keep (keep (keep h)))) 4 (by simp))
  let s6 := s5.uset (o+5) (v >>> 40).toUInt8 (byte_ok (keep (keep (keep (keep (keep h))))) 5 (by simp))
  let s7 := s6.uset (o+6) (v >>> 48).toUInt8 (byte_ok (keep (keep (keep (keep (keep (keep h)))))) 6 (by simp))
  s7.uset (o+7) (v >>> 56).toUInt8 (byte_ok (keep (keep (keep (keep (keep (keep (keep h))))))) 7 (by simp))

/-- After `Slots.slot_ok` of `WasmVM/Exec/Code.lean`: one machine comparison puts the eight
bytes of word `i` in range. -/
theorem slot_ok {s : ByteArray} {i : USize} (h : i < s.usize / 8) : (i * 8).toNat + 8 ≤ s.usize.toNat := by
  rw [USize.lt_iff_toNat_lt, USize.toNat_div] at h
  have h8 : (8 : USize).toNat = 8 := by simp
  rw [h8] at h
  have h2 := USize.toNat_lt_size s.usize
  have hs : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_mul, h8, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Word `i` of `s`, or 0 when it is out of range: one test, one 8-byte load. -/
@[inline] def rd (s : ByteArray) (i : USize) : UInt64 :=
  if h : i < s.usize / 8 then ld64 s (i * 8) (slot_ok h) else 0

/-- Write word `i` of `s`; no change when it is out of range: one test, one 8-byte store. -/
@[inline] def wr (s : ByteArray) (i : USize) (v : UInt64) : ByteArray :=
  if h : i < s.usize / 8 then st64 s (i * 8) v (slot_ok h) else s

/-! ## Values -/

/-- The largest word that is a number (the x86-64 default NaN). -/
def numMax : UInt64 := 0xFFF8000000000000
def tagObj : UInt64 := 0xFFFC000000000000
def tagBool : UInt64 := 0xFFFD000000000000
def undef : UInt64 := 0xFFFE000000000000
def payloadMask : UInt64 := 0x0000FFFFFFFFFFFF

@[inline] def isNum (w : UInt64) : Bool := w ≤ numMax

/-- The bits of a number, and the number of a word that is a number. In Lean 4.33.1
`Float.toBits` and `Float.ofBits` are calls into the runtime (they make every NaN the canonical
NaN): 5 calls for one loop iteration here, about two thirds of its instructions. The inline C
below is one register move. It differs from the reference body only on a NaN: it keeps the
payload. No arithmetic on x86-64 or ARM64 makes a NaN above `numMax` from operands that are
numbers, so a number never reads as a tag; an engine must make a NaN canonical where bytes
become numbers (typed arrays, `DataView`). Measured both ways: the table of the record. -/
@[extern c inline "({ double d_ = (#1); uint64_t b_; __builtin_memcpy(&b_, &d_, 8); b_; })"]
def num (x : Float) : UInt64 := x.toBits

@[extern c inline "({ uint64_t b_ = (#1); double d_; __builtin_memcpy(&d_, &b_, 8); d_; })"]
def float (w : UInt64) : Float := Float.ofBits w

def ins (op a b c : UInt32) : UInt32 := op ||| (a <<< 8) ||| (b <<< 16) ||| (c <<< 24)

/-- The slot of a key in an object of a shape: the slow path of a property access. Shape 1 has
the keys 0 and 1 in slots 1 and 2 (slot 0 is the shape word). 0 means the key is absent. -/
def shapeSlot (shape : UInt64) (key : USize) : UInt32 :=
  if shape == 1 then (if key == 0 then 1 else if key == 1 then 2 else 0) else 0

structure Out where
  regs : ByteArray
  heapWords : USize
  ok : Bool

/-- Every exit of `exec`. Not inlined, so that the loop keeps its registers (the WasmVM record,
"Register spills at the dispatch head"). -/
@[noinline] def stop (regs : ByteArray) (hTop : USize) (ok : Bool) : Out := ⟨regs, hTop, ok⟩

theorem code_ok {code : Array UInt32} {pc : USize} (h : pc < code.usize) : pc.toNat < code.size := by
  have h1 : code.usize.toNat ≤ code.size := by
    simp only [Array.usize]; simp [Nat.toUSize]; exact Nat.mod_le _ _
  have h2 := USize.lt_iff_toNat_lt.mp h
  omega

@[inline] def fetch (code : Array UInt32) (pc : USize) : UInt32 :=
  if h : pc < code.usize then code.uget pc (code_ok h) else 0

def exec (code : Array UInt32) (pc bp : USize) (regs heap : ByteArray) (hTop : USize) (steps : UInt64) : Out :=
  if _hs : steps = 0 then stop regs hTop false else
  let w := fetch code pc
  let op := w &&& 0xFF
  let a := ((w >>> 8) &&& 0xFF).toUSize
  let b := ((w >>> 16) &&& 0xFF).toUSize
  let c := ((w >>> 24) &&& 0xFF).toUSize
  match op with
  | 1 =>
    let x := rd regs (bp + b)
    let y := rd regs (bp + c)
    if isNum x && isNum y then exec code (pc + 1) bp (wr regs (bp + a) (num (float x + float y))) heap hTop (steps - 1)
    else stop regs hTop false
  | 2 =>
    let x := rd regs (bp + b)
    let y := rd regs (bp + c)
    if isNum x && isNum y then
      exec code (pc + 1) bp (wr regs (bp + a) (tagBool ||| (if float x < float y then 1 else 0))) heap hTop (steps - 1)
    else stop regs hTop false
  | 3 =>
    if rd regs (bp + a) == tagBool then exec code (b + 256 * c) bp regs heap hTop (steps - 1)
    else exec code (pc + 1) bp regs heap hTop (steps - 1)
  | 4 => exec code (b + 256 * c) bp regs heap hTop (steps - 1)
  | 5 => exec code (pc + 1) bp (wr regs (bp + a) (rd regs (bp + b))) heap hTop (steps - 1)
  | 6 => exec code (pc + 1) bp (wr regs (bp + a) (num (b + 256 * c).toUInt64.toFloat)) heap hTop (steps - 1)
  | 7 =>
    -- r[a] = r[b].key(c)
    let o := rd regs (bp + b)
    if o &&& 0xFFFF000000000000 == tagObj then
      let base := (o &&& payloadMask).toUSize
      let shape := rd heap base
      if shape == (fetch code (pc + 1)).toUInt64 then
        exec code (pc + 3) bp (wr regs (bp + a) (rd heap (base + (fetch code (pc + 2)).toUSize))) heap hTop (steps - 1)
      else
        let slot := shapeSlot shape c
        if slot == 0 then stop regs hTop false else
        -- fill the cache and run the instruction again
        exec ((code.set! (pc + 1).toNat shape.toUInt32).set! (pc + 2).toNat slot) pc bp regs heap hTop (steps - 1)
    else stop regs hTop false
  | 8 =>
    -- r[a].key(b) = r[c]
    let o := rd regs (bp + a)
    if o &&& 0xFFFF000000000000 == tagObj then
      let base := (o &&& payloadMask).toUSize
      let shape := rd heap base
      if shape == (fetch code (pc + 1)).toUInt64 then
        exec code (pc + 3) bp regs (wr heap (base + (fetch code (pc + 2)).toUSize) (rd regs (bp + c))) hTop (steps - 1)
      else
        let slot := shapeSlot shape b
        if slot == 0 then stop regs hTop false else
        exec ((code.set! (pc + 1).toNat shape.toUInt32).set! (pc + 2).toNat slot) pc bp regs heap hTop (steps - 1)
    else stop regs hTop false
  | 9 =>
    -- r[a] = { key0: r[b], key1: r[c] } with the shape of the next word; the heap has room or the run stops
    if (hTop + 3) <<< 3 ≤ heap.usize then
      let heap := wr (wr (wr heap hTop (fetch code (pc + 1)).toUInt64) (hTop + 1) (rd regs (bp + b))) (hTop + 2) (rd regs (bp + c))
      exec code (pc + 2) bp (wr regs (bp + a) (tagObj ||| hTop.toUInt64)) heap (hTop + 3) (steps - 1)
    else stop regs hTop false
  | 10 =>
    -- r[a] = f(r[c], ...): the callee's registers start at bp + c; three words below hold the return data
    let nb := bp + c
    let regs := wr (wr (wr regs (nb - 3) (pc + 2).toUInt64) (nb - 2) bp.toUInt64) (nb - 1) a.toUInt64
    exec code (fetch code (pc + 1)).toUSize nb regs heap hTop (steps - 1)
  | 11 =>
    let obp := (rd regs (bp - 2)).toUSize
    exec code (rd regs (bp - 3)).toUSize obp (wr regs (obp + (rd regs (bp - 1)).toUSize) (rd regs (bp + a))) heap hTop (steps - 1)
  | 12 =>
    let x := rd regs (bp + b)
    let y := rd regs (bp + c)
    if isNum x && isNum y then exec code (pc + 1) bp (wr regs (bp + a) (num (float x - float y))) heap hTop (steps - 1)
    else stop regs hTop false
  | _ => stop regs hTop (op == 0)
termination_by steps.toNat
decreasing_by
  all_goals
    have h1 : steps.toNat ≠ 0 := fun h => _hs (UInt64.toNat_inj.mp (by simpa using h))
    have h2 : (steps - 1).toNat = steps.toNat - 1 := by
      rw [UInt64.toNat_sub_of_le]
      · rfl
      · exact UInt64.le_iff_toNat_le.mpr (by simp; omega)
    omega

def words (n : Nat) : ByteArray := ByteArray.mk (Array.replicate (8 * n) 0)

/-- The frame of every loop program: 0 s, 1 i, 2 n, 3 one, 4 t, 5 k, 6 o; the registers 7, 8, 9
hold the return data of a call, and the callee's registers start at 10. -/
def frame (n : Nat) : ByteArray :=
  [(0, num 0), (1, num 0), (2, num n.toUInt64.toFloat), (3, num 1), (5, num 3), (6, tagObj ||| 0)].foldl
    (fun r (i, w) => wr r i w) (words 64)

/-- `for (i = 0; i < n; i++) BODY`, with BODY from pc 2. -/
def loop (body : Array UInt32) : Array UInt32 :=
  let done := (4 + body.size).toUInt32
  #[ins 2 4 1 2, ins 3 4 (done &&& 0xFF) (done >>> 8)] ++ body ++ #[ins 1 1 1 3, ins 4 0 0 0, ins 0 0 0 0]

def result (o : Out) : String :=
  if o.ok then
    let w := rd o.regs 0
    s!"{if isNum w then toString (float w) else "an object"}, {o.heapWords} heap words"
  else "FAILED"

/-- A heap of `cap` words that starts with one object `{ key0: 7, key1: 9 }` of shape 1. -/
def heapWith (cap : Nat) : ByteArray := wr (wr (wr (words cap) 0 1) 1 (num 7)) 2 (num 9)

/-- The registers and the heap of a loop program, made before the clock starts. -/
def setup (n : Nat) (heapCap : Nat := 8) : ByteArray × ByteArray := (frame n, heapWith heapCap)

def runLoop (st : ByteArray × ByteArray) (body : Array UInt32) (extra : Array UInt32 := #[]) : String :=
  result (exec (loop body ++ extra) 0 0 st.1 st.2 3 1000000000000)

/-- `function fib(n) { if (n < 2) return n; return fib(n - 1) + fib(n - 2); }` at pc 3; the main
program calls it with the argument in register 10 and halts. Registers of `fib`: 0 n, 1 and 3
constants, 2 the test, 4 and 5 the results; return data in 6 to 8, the callee from 9. -/
def fibProgram : Array UInt32 :=
  #[ins 10 0 0 10, 3, ins 0 0 0 0,
    ins 6 1 2 0, ins 2 2 0 1, ins 3 2 7 0, ins 11 0 0 0,
    ins 6 3 1 0, ins 12 9 0 3, ins 10 4 0 9, 3, ins 6 3 2 0, ins 12 9 0 3, ins 10 5 0 9, 3, ins 1 4 4 5, ins 11 4 0 0]

def setupFib (n : Nat) : ByteArray × ByteArray := (wr (words 4096) 10 (num n.toUInt64.toFloat), words 1)

def runFib (st : ByteArray × ByteArray) : String :=
  result (exec fibProgram 0 0 st.1 st.2 0 1000000000000)

end CoreModel

def timeIt (name : String) (n : Nat) (st : ByteArray × ByteArray) (act : ByteArray × ByteArray → String) : IO Float := do
  -- the arrays exist (and their pages are touched) before the clock starts
  let touched := st.1.size + st.2.size
  let t0 ← (if touched == 12345678 then pure 0 else IO.monoNanosNow)
  let r := act st
  let t1 ← (if r.length == 12345678 then pure 0 else IO.monoNanosNow)
  let ns := (t1 - t0).toFloat / n.toFloat
  IO.println s!"{name}: {(ns * 10).round / 10} ns   (result {r})"
  return ns

/-- `CoreModel [ITERATIONS]` prints the table. `CoreModel ITERATIONS NAME` runs one program
(`loop`, `add`, `get`, `set`, `call`, `object`, `fib`) and prints its result: for an instruction
count by `valgrind --tool=callgrind` at two sizes. -/
def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 3000000
  let ins := CoreModel.ins
  let setup (n : Nat) (cap : Nat := 8) := CoreModel.setup n cap
  if let some which := args[1]? then
    let body : Array UInt32 := match which with
      | "add" => #[ins 1 0 0 5]
      | "get" => #[ins 7 0 6 0, 0, 0]
      | "set" => #[ins 8 6 0 1, 0, 0]
      | "call" => #[ins 5 10 1 0, ins 10 0 0 10, 8]
      | "object" => #[ins 9 0 1 5, 1]
      | _ => #[]
    if which == "fib" then IO.println (CoreModel.runFib (CoreModel.setupFib n))
    else IO.println (CoreModel.runLoop (setup n (if which == "object" then 3 * n + 8 else 8)) body
      (if which == "call" then #[ins 11 0 0 0] else #[]))
    return
  IO.println s!"CoreModel, {n} iterations: ns for one loop iteration"
  let base ← timeIt "the loop itself (i < n; i++)" n (setup n) fun st => CoreModel.runLoop st #[]
  let add ← timeIt "s = s + k" n (setup n) fun st => CoreModel.runLoop st #[ins 1 0 0 5]
  let get ← timeIt "s = o.x (inline cache)" n (setup n) fun st => CoreModel.runLoop st #[ins 7 0 6 0, 0, 0]
  let set ← timeIt "o.x = i (inline cache)" n (setup n) fun st => CoreModel.runLoop st #[ins 8 6 0 1, 0, 0]
  let call ← timeIt "s = g1(i) (call and return)" n (setup n) fun st =>
    -- the body is 3 words, so the loop is 8 words and g1 starts at pc 8
    CoreModel.runLoop st #[ins 5 10 1 0, ins 10 0 0 10, 8] #[ins 11 0 0 0]
  let obj ← timeIt "s = { x: i, y: k } (no collector)" n (setup n (3 * n + 8)) fun st => CoreModel.runLoop st #[ins 9 0 1 5, 1]
  let r1 (x : Float) : Float := (x * 10).round / 10
  IO.println s!"less the loop: add {r1 (add - base)}, property read {r1 (get - base)}, property write {r1 (set - base)}, call {r1 (call - base)}, object {r1 (obj - base)} ns"
  let calls := 2692537
  let _ ← timeIt "fib(30), for one call of fib (2,692,537 calls)" calls (CoreModel.setupFib 30) CoreModel.runFib
