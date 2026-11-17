/-! IdiomBench: what one call of a small helper costs in compiled Lean, by the way it returns its result.
A measurement program (Init only). Each case runs a loop of N iterations; the helper is `@[noinline]` unless the
case says otherwise, does one array read and an add, and can fail (never does). -/

structure St where
  steps : Nat
  regs  : Array UInt64
  acc   : UInt64      -- result register for the result-in-state style
  err   : UInt8       -- pending-exception flag for the result-in-state style

abbrev M := EStateM Unit St

-- 1. monadic helper, not inlined: one EStateM.Result.ok cell per call
@[noinline] def getM (i : USize) : M UInt64 := fun s =>
  if h : i.toNat < s.regs.size then .ok (s.regs[i.toNat]) s else .error () s
-- 2. the same, inlined
@[inline] def getMI (i : USize) : M UInt64 := fun s =>
  if h : i.toNat < s.regs.size then .ok (s.regs[i.toNat]) s else .error () s
-- 3. pure helper returning Option
@[noinline] def getOpt (s : @& St) (i : USize) : Option UInt64 :=
  if h : i.toNat < s.regs.size then some (s.regs[i.toNat]) else none
-- 4. pure helper returning a pair (value, ok flag)
@[noinline] def getPair (s : @& St) (i : USize) : UInt64 × Bool :=
  if h : i.toNat < s.regs.size then (s.regs[i.toNat], true) else (0, false)
-- 5. pure helper returning a scalar with a sentinel
@[noinline] def getSent (s : @& St) (i : USize) : UInt64 :=
  if h : i.toNat < s.regs.size then s.regs[i.toNat] else 0xFFFFFFFFFFFFFFFF
-- 6. result-in-state: St -> St, value in `acc`, failure in `err`
@[noinline] def getAcc (i : USize) (s : St) : St :=
  if h : i.toNat < s.regs.size then { s with acc := s.regs[i.toNat] } else { s with err := 1 }
-- 7. state-passing returning (value × state)
@[noinline] def getSP (i : USize) (s : St) : UInt64 × St :=
  if h : i.toNat < s.regs.size then (s.regs[i.toNat], s) else (0, s)

partial def loopM (n : Nat) (i : USize) (sum : UInt64) : M UInt64 := do
  if n == 0 then return sum
  let v ← getM (i &&& 7)
  loopM (n - 1) (i + 1) (sum + v)
partial def loopMI (n : Nat) (i : USize) (sum : UInt64) : M UInt64 := do
  if n == 0 then return sum
  let v ← getMI (i &&& 7)
  loopMI (n - 1) (i + 1) (sum + v)
partial def loopOpt (s : St) (n : Nat) (i : USize) (sum : UInt64) : UInt64 :=
  if n == 0 then sum else
  match getOpt s (i &&& 7) with
  | some v => loopOpt s (n - 1) (i + 1) (sum + v)
  | none => 0
partial def loopPair (s : St) (n : Nat) (i : USize) (sum : UInt64) : UInt64 :=
  if n == 0 then sum else
  let (v, ok) := getPair s (i &&& 7)
  if ok then loopPair s (n - 1) (i + 1) (sum + v) else 0
partial def loopSent (s : St) (n : Nat) (i : USize) (sum : UInt64) : UInt64 :=
  if n == 0 then sum else
  let v := getSent s (i &&& 7)
  if v == 0xFFFFFFFFFFFFFFFF then 0 else loopSent s (n - 1) (i + 1) (sum + v)
partial def loopAcc (s : St) (n : Nat) (i : USize) (sum : UInt64) : UInt64 :=
  if n == 0 then sum else
  let s := getAcc (i &&& 7) s
  if s.err != 0 then 0 else loopAcc s (n - 1) (i + 1) (sum + s.acc)
partial def loopSP (s : St) (n : Nat) (i : USize) (sum : UInt64) : UInt64 :=
  if n == 0 then sum else
  let (v, s) := getSP (i &&& 7) s
  loopSP s (n - 1) (i + 1) (sum + v)

-- 8. ST with the state in a reference: does a non-inlined ST helper allocate a result?
@[noinline] def getST (r : ST.Ref σ (Array UInt64)) (i : USize) : ST σ UInt64 := do
  let a ← r.get
  return a.getD i.toNat 0
partial def loopST (r : ST.Ref σ (Array UInt64)) (n : Nat) (i : USize) (sum : UInt64) : ST σ UInt64 := do
  if n == 0 then return sum
  let v ← getST r (i &&& 7)
  loopST r (n - 1) (i + 1) (sum + v)
-- 9. EST (exceptions, state in a reference)
@[noinline] def getEST (r : ST.Ref σ (Array UInt64)) (i : USize) : EST Unit σ UInt64 := do
  let a ← r.get
  if h : i.toNat < a.size then return a[i.toNat] else throw ()
partial def loopEST (r : ST.Ref σ (Array UInt64)) (n : Nat) (i : USize) (sum : UInt64) : EST Unit σ UInt64 := do
  if n == 0 then return sum
  let v ← getEST r (i &&& 7)
  loopEST r (n - 1) (i + 1) (sum + v)

-- 10. a boxed sum type as the result (like Value.num) against a Float
inductive V where | undef | num (x : Float) | str (s : String)
@[noinline] def addV (a b : @& V) : V := match a, b with | .num x, .num y => .num (x + y) | _, _ => .undef
@[noinline] def addF (a b : Float) : Float := a + b
partial def loopV (n : Nat) (acc : V) (one : V) : V := if n == 0 then acc else loopV (n - 1) (addV acc one) one
partial def loopF (n : Nat) (acc : Float) : Float := if n == 0 then acc else loopF (n - 1) (addF acc 1.0)

-- 11. the monadic helper with a state update each call (a step counter), as `tick` does
@[noinline] def tickM : M Unit := fun s => if s.steps == 0 then .error () s else .ok () { s with steps := s.steps - 1 }
partial def loopTick (n : Nat) : M Unit := do
  if n == 0 then return
  tickM; loopTick (n - 1)
@[noinline] def tickS (s : St) : St := if s.steps == 0 then { s with err := 1 } else { s with steps := s.steps - 1 }
partial def loopTickS (s : St) (n : Nat) : St := if n == 0 then s else
  let s := tickS s; if s.err != 0 then s else loopTickS s (n - 1)

@[noinline] def force (f : Unit → UInt64) : IO UInt64 := pure (f ())
def time (name : String) (n : Nat) (act : IO UInt64) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}\t{(t1 - t0).toFloat / n.toFloat} ns/iter\t(result {r})"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 50000000
  let s : St := { steps := 4 * n, regs := #[1,2,3,4,5,6,7,8], acc := 0, err := 0 }
  for _ in [0:2] do
    time "01 EStateM helper, call      " n (force fun _ => (match loopM n 0 0 s with | .ok v _ => v | .error _ _ => 0))
    time "02 EStateM helper, inlined   " n (force fun _ => (match loopMI n 0 0 s with | .ok v _ => v | .error _ _ => 0))
    time "03 Option result             " n (force fun _ => (loopOpt s n 0 0))
    time "04 pair result               " n (force fun _ => (loopPair s n 0 0))
    time "05 scalar + sentinel         " n (force fun _ => (loopSent s n 0 0))
    time "06 result in state (St -> St)" n (force fun _ => (loopAcc s n 0 0))
    time "07 (value x state) result    " n (force fun _ => (loopSP s n 0 0))
    time "08 ST helper, state in a Ref " n (do let r ← (ST.mkRef s.regs : BaseIO _); (loopST r n 0 0 : BaseIO _))
    time "09 EST helper, state in a Ref" n (do
      let r ← (ST.mkRef s.regs : BaseIO _)
      let x : EIO Unit UInt64 := loopEST r n 0 0
      match ← x.toBaseIO with | Except.ok v => pure v | Except.error _ => pure 0)
    time "10 boxed sum result (V.num)  " n (force fun _ => (match loopV n (.num 0) (.num 1) with | .num x => x.toUInt64 | _ => 0))
    time "11 Float result              " n (force fun _ => (loopF n 0).toUInt64)
    time "12 tick: EStateM, state write" n (force fun _ => (match loopTick n s with | .ok _ s => s.steps.toUInt64 | .error _ _ => 0))
    time "13 tick: St -> St            " n (pure (loopTickS s n).steps.toUInt64)
