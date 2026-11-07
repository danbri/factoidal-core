/-
L4Factoidal.WasmVM.Binary.Leb: LEB128 integers of the WebAssembly binary format
(https://github.com/danbri/factoidal/issues/1244).

`uSpec` transcribes the grammar of the specification, section 5.2.2 (Integers):

  u(N) ::= n:byte              => n               if n < 2^7 ∧ n < 2^N
         | n:byte m:u(N-7)     => 2^7·m + (n-2^7) if n ≥ 2^7 ∧ N > 7

It recurses before it adds, so it is not a loop. `uFast` is a loop with an
accumulator and a shift. `uSpec_eq_fast` proves them equal, and `@[csimp]` makes
compiled code run `uFast` wherever the source calls `uSpec`: the decoder is written
against the grammar and runs the loop. This is the first instance of the pattern in
docs/designissues/2026-11-07-wasmvm-engine.md ("Proof plan", item 1).

Each function returns the value and the position after the last byte, or `none`
when the bytes end early, the number has too many bytes, or the unused bits of the
last byte are not zero (signed: not the sign extension).
-/
namespace L4Factoidal.WasmVM.Binary.Leb

/-- The grammar `u(N)`, read at position `p`. -/
def uSpec (b : ByteArray) (p N : Nat) : Option (Nat × Nat) :=
  if h : p < b.size then
    let n := b[p].toNat
    if n < 128 then
      if n < 2 ^ N then some (n, p + 1) else none
    else if 7 < N then
      match uSpec b (p + 1) (N - 7) with
      | some (m, q) => some (2 ^ 7 * m + (n - 2 ^ 7), q)
      | none => none
    else none
  else none
termination_by N
decreasing_by omega

/-- The loop: `acc` holds the bits read so far, `sh` the shift of the next group. -/
def uLoop (b : ByteArray) (p N acc sh : Nat) : Option (Nat × Nat) :=
  if h : p < b.size then
    let n := b[p].toNat
    if n < 128 then
      if n >>> N = 0 then some (acc + (n <<< sh), p + 1) else none
    else if 7 < N then
      uLoop b (p + 1) (N - 7) (acc + ((n - 128) <<< sh)) (sh + 7)
    else none
  else none
termination_by N
decreasing_by omega

def uFast (b : ByteArray) (p N : Nat) : Option (Nat × Nat) := uLoop b p N 0 0

private theorem lt_pow_iff_shift (n N : Nat) : n >>> N = 0 ↔ n < 2 ^ N := by
  rw [Nat.shiftRight_eq_div_pow]
  constructor
  · intro h
    have := Nat.div_add_mod n (2 ^ N)
    have hm := Nat.mod_lt n (Nat.two_pow_pos N)
    rw [h, Nat.mul_zero, Nat.zero_add] at this
    omega
  · intro h
    exact Nat.div_eq_of_lt h

private theorem step_arith (acc x m sh : Nat) :
    acc + x * 2 ^ sh + m * 2 ^ (sh + 7) = acc + (2 ^ 7 * m + x) * 2 ^ sh := by
  rw [Nat.pow_add, Nat.add_mul, Nat.mul_comm (2 ^ 7) m, Nat.mul_assoc,
    Nat.mul_comm (2 ^ 7) (2 ^ sh)]
  omega

theorem uLoop_eq (b : ByteArray) : ∀ (N p acc sh : Nat),
    uLoop b p N acc sh = (uSpec b p N).map (fun r => (acc + r.1 * 2 ^ sh, r.2)) := by
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
    intro p acc sh
    rw [uLoop, uSpec]
    by_cases h : p < b.size
    · simp only [h, dite_true]
      by_cases h1 : b[p].toNat < 128
      · simp only [h1, if_true]
        by_cases h2 : b[p].toNat < 2 ^ N
        · simp [h2, (lt_pow_iff_shift _ _).mpr h2, Nat.shiftLeft_eq]
        · have h3 : ¬ (b[p].toNat >>> N = 0) := fun e => h2 ((lt_pow_iff_shift _ _).mp e)
          simp [h2, h3]
      · simp only [h1, if_false]
        by_cases h3 : 7 < N
        · simp only [h3, if_true]
          rw [ih (N - 7) (by omega)]
          cases hs : uSpec b (p + 1) (N - 7) with
          | none => rfl
          | some r =>
            obtain ⟨m, q⟩ := r
            have e := step_arith acc (b[p].toNat - 2 ^ 7) m sh
            simp only [Option.map_some, Nat.shiftLeft_eq, Option.some.injEq, Prod.mk.injEq,
              and_true]
            exact e
        · simp [h3]
    · simp [h]

/-- The grammar and the loop are the same function; compiled code runs the loop. -/
@[csimp] theorem uSpec_eq_fast : @uSpec = @uFast := by
  funext b p N
  rw [uFast, uLoop_eq]
  cases uSpec b p N with
  | none => rfl
  | some r => simp

/-- Signed `s(N)`, as a loop. The last byte gives a 7-bit group read as signed; its
value must lie in the range that the remaining `N` bits allow. -/
def sLoop (b : ByteArray) (p N : Nat) (acc : Int) (sh : Nat) : Option (Int × Nat) :=
  if h : p < b.size then
    let n := b[p].toNat
    if n < 128 then
      if n < 64 then
        if n < 2 ^ (N - 1) then some (acc + ((n : Int) <<< sh), p + 1) else none
      else
        if 128 - 2 ^ (N - 1) ≤ n then some (acc + (((n : Int) - 128) * (2 ^ sh : Nat)), p + 1)
        else none
    else if 7 < N then
      sLoop b (p + 1) (N - 7) (acc + (((n - 128 : Nat) : Int) <<< sh)) (sh + 7)
    else none
  else none
termination_by N
decreasing_by omega

def sFast (b : ByteArray) (p N : Nat) : Option (Int × Nat) := sLoop b p N 0 0

def u32 (b : ByteArray) (p : Nat) : Option (Nat × Nat) := uSpec b p 32
def u64 (b : ByteArray) (p : Nat) : Option (Nat × Nat) := uSpec b p 64
def s32 (b : ByteArray) (p : Nat) : Option (Int × Nat) := sFast b p 32
def s33 (b : ByteArray) (p : Nat) : Option (Int × Nat) := sFast b p 33
def s64 (b : ByteArray) (p : Nat) : Option (Int × Nat) := sFast b p 64

end L4Factoidal.WasmVM.Binary.Leb
