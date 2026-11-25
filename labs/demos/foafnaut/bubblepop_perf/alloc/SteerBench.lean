/-! SteerBench: what can be steered per definition in the compiler (borrow annotations, specialisation, closed terms). -/
structure Big where
  a : Array UInt64
  b : Array UInt64

-- 1. borrow: inferred, annotated, and a case where inference gives up (the parameter is stored)
@[noinline] def sumInferred (s : Big) (i : USize) : UInt64 := s.a.getD i.toNat 0 + s.b.getD i.toNat 0
@[noinline] def sumBorrowed (s : @& Big) (i : USize) : UInt64 := s.a.getD i.toNat 0 + s.b.getD i.toNat 0
partial def loopInferred (s : Big) (n : Nat) (i : USize) (acc : UInt64) : UInt64 :=
  if n == 0 then acc else loopInferred s (n - 1) (i + 1) (acc + sumInferred s (i &&& 7))
partial def loopBorrowed (s : Big) (n : Nat) (i : USize) (acc : UInt64) : UInt64 :=
  if n == 0 then acc else loopBorrowed s (n - 1) (i + 1) (acc + sumBorrowed s (i &&& 7))

-- 2. specialisation of a higher-order helper
@[noinline] def foldPlain (f : UInt64 → UInt64 → UInt64) (a : Array UInt64) (init : UInt64) : UInt64 := a.foldl f init
@[specialize] def foldSpec (f : UInt64 → UInt64 → UInt64) (a : Array UInt64) (init : UInt64) : UInt64 := a.foldl f init
partial def loopPlain (a : Array UInt64) (n : Nat) (k acc : UInt64) : UInt64 :=
  if n == 0 then acc else loopPlain a (n - 1) (k + 1) (acc + foldPlain (fun x y => x + y + k) a 0)
partial def loopSpec (a : Array UInt64) (n : Nat) (k acc : UInt64) : UInt64 :=
  if n == 0 then acc else loopSpec a (n - 1) (k + 1) (acc + foldSpec (fun x y => x + y + k) a 0)

-- 3. closed terms: a constant table inside a function
@[noinline] def tableGet (i : USize) : UInt64 := (#[3, 1, 4, 1, 5, 9, 2, 6] : Array UInt64).getD i.toNat 0
set_option compiler.extract_closed false in
@[noinline] def tableGetNoExtract (i : USize) : UInt64 := (#[3, 1, 4, 1, 5, 9, 2, 6] : Array UInt64).getD i.toNat 0
partial def loopTable (n : Nat) (i : USize) (acc : UInt64) : UInt64 :=
  if n == 0 then acc else loopTable (n - 1) (i + 1) (acc + tableGet (i &&& 7))
partial def loopTableNo (n : Nat) (i : USize) (acc : UInt64) : UInt64 :=
  if n == 0 then acc else loopTableNo (n - 1) (i + 1) (acc + tableGetNoExtract (i &&& 7))

@[noinline] def force (f : Unit → UInt64) : IO UInt64 := pure (f ())
def time (name : String) (n : Nat) (act : IO UInt64) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let r ← act
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}\t{(t1 - t0).toFloat / n.toFloat} ns/iter\t(result {r})"

def main (args : List String) : IO Unit := do
  let n := (args.head? >>= String.toNat?).getD 20000000
  let s : Big := { a := #[1,2,3,4,5,6,7,8], b := #[8,7,6,5,4,3,2,1] }
  time "borrow inferred          " n (force fun _ => loopInferred s n 0 0)
  time "borrow annotated (@&)    " n (force fun _ => loopBorrowed s n 0 0)
  time "fold, closure, no spec   " n (force fun _ => loopPlain s.a n 0 0)
  time "fold, @[specialize]      " n (force fun _ => loopSpec s.a n 0 0)
  time "constant table, extracted" n (force fun _ => loopTable n 0 0)
  time "constant table, rebuilt  " n (force fun _ => loopTableNo n 0 0)
