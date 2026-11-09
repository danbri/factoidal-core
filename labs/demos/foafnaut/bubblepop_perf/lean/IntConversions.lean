/-!
# The cost of integer to `Float` conversions and of ToInt32 in compiled Lean

Record: docs/designissues/2026-11-09-foafnaut-perf-exploration.md, section 7. Run it with
`labs/demos/foafnaut/bubblepop_perf/lean/run.sh` (not part of the Lake project).

In Lean 4.33.1 `Float.ofNat` and `Float.ofInt` read the number 2^53 from decimal text at each
call, and an `Int` above 31 bits is a GMP number. The loops are tail calls with unboxed
accumulators; the size comes from the command line, so nothing is computed at compile time.
-/

@[noinline] def viaOfNat (n : Nat) : Float := Float.ofNat n
@[noinline] def viaUInt64 (n : Nat) : Float := n.toUInt64.toFloat
@[noinline] def viaGuard (n : Nat) : Float := if n ≤ 4294967295 then n.toUInt64.toFloat else Float.ofNat n
@[noinline] def viaOfInt (i : Int) : Float := Float.ofInt i
@[noinline] def intFast (i : Int) : Float :=
  match i with
  | .ofNat n => if n ≤ 4294967295 then n.toUInt64.toFloat else Float.ofNat n
  | .negSucc n => if n < 4294967295 then -((n + 1).toUInt64.toFloat) else Float.ofInt i

/-- ToInt32 as `JS/Number.lean` writes it (exact, on `Int`). -/
@[noinline] def toInt32Ref (x : Float) : Int :=
  if !x.isFinite || x == 0 then 0 else
  let t : Int := x.toInt64.toInt
  let m := t % 4294967296
  if m ≥ 2147483648 then m - 4294967296 else m
/-- ToInt32 on machine integers, for |x| < 2^63. -/
@[noinline] def toInt32Fast (x : Float) : Int32 := x.toInt64.toInt32
@[noinline] def litNat53 (n : Nat) : Bool := n < 9007199254740992

def loopNF (f : Nat → Float) (n : Nat) (i : Nat) (acc : Float) : Float :=
  if i < n then loopNF f n (i + 1) (acc + f i) else acc
termination_by n - i
def loopIF (f : Int → Float) (n : Nat) (i : Nat) (acc : Float) : Float :=
  if i < n then loopIF f n (i + 1) (acc + f (Int.ofNat i - 7)) else acc
termination_by n - i
def loopRef (n : Nat) (i : Nat) (x : Float) (acc : UInt64) : UInt64 :=
  if i < n then loopRef n (i + 1) (x + 1) (acc + (toInt32Ref x).toNat.toUInt64) else acc
termination_by n - i
def loopFast (n : Nat) (i : Nat) (x : Float) (acc : UInt64) : UInt64 :=
  if i < n then loopFast n (i + 1) (x + 1) (acc + (toInt32Fast x).toUInt32.toUInt64) else acc
termination_by n - i
def loopNone (n : Nat) (i : Nat) (x : Float) (acc : UInt64) : UInt64 :=
  if i < n then loopNone n (i + 1) (x + 1) (acc + x.toUInt64) else acc
termination_by n - i
def loopLit (n : Nat) (i : Nat) (acc : UInt64) : UInt64 :=
  if i < n then loopLit n (i + 1) (if litNat53 i then acc + 1 else acc) else acc
termination_by n - i
def loopNoneN (n : Nat) (i : Nat) (acc : Float) : Float :=
  if i < n then loopNoneN n (i + 1) (acc + 1) else acc
termination_by n - i

def time (name : String) (n : Nat) (act : Unit → String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r := act ()
  let t1 ← (if r.length == 12345678 then pure 0 else IO.monoNanosNow)
  let ps := (t1 - t0) * 1000 / n
  IO.println s!"{name}: {ps / 1000}.{(ps % 1000) / 100} ns per iteration   (check {r})"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 1000000
  time "loop only (Nat counter, Float acc)" n fun _ => toString (loopNoneN n 0 0)
  time "Float.ofNat n" n fun _ => toString (loopNF viaOfNat n 0 0)
  time "n.toUInt64.toFloat" n fun _ => toString (loopNF viaUInt64 n 0 0)
  time "if n <= 2^32-1 then n.toUInt64.toFloat else Float.ofNat n" n fun _ => toString (loopNF viaGuard n 0 0)
  time "Float.ofInt i" n fun _ => toString (loopIF viaOfInt n 0 0)
  time "Int fast path" n fun _ => toString (loopIF intFast n 0 0)
  time "loop only (Float x, UInt64 acc)" n fun _ => toString (loopNone n 0 0 0)
  time "ToInt32 on Int (as JS/Number.lean)" n fun _ => toString (loopRef n 0 0 0)
  time "ToInt32 on machine integers" n fun _ => toString (loopFast n 0 0 0)
  time "Nat n < 9007199254740992 (bare literal)" n fun _ => toString (loopLit n 0 0)
