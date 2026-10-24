/-
Harness.IterPhases — `l4iter-phases`: the phases of the Dataset iteration
ops of `Wasm/Ops/Handles.lean`, timed natively one at a time
(https://github.com/danbri/factoidal/issues/900).

    l4iter-phases N [REPEATS]

builds the N-quad dataset of `npm/factoidal/test/dataset-iterate-speed.test.mjs`
(the same subjects, predicates, objects and graphs), parses it with the
handle ops' N-Quads reader, and prints one line per phase

    n=N phase=NAME ms=T value=V

where V is a number computed from the phase's result, so that the phase is
evaluated before its time is read, and T is the median of REPEATS runs
(default 5).
-/
import Wasm.Ops.Handles

namespace Harness.IterPhases

open L4Factoidal.RDF
open L4Wasm.Ops

def sourceText (n : Nat) : String := Id.run do
  let mut s := ""
  for i in [0:n] do
    let g := if i % 3 == 0 then s!" <http://e/g{i % 7}>" else ""
    let o := if i % 2 == 0 then s!"\"value {i}\"@en" else s!"<http://e/o{i % 1000}>"
    s := s ++ s!"<http://e/s{i % 5000}> <http://e/p{i % 13}> {o}{g} .\n"
  return s

def median (xs : Array Nat) : Nat :=
  let s := xs.qsort (· < ·)
  s[s.size / 2]!

/-- Time `f` REPEATS times; `f` answers a number computed from its result. -/
def timed (reps : Nat) (f : Unit → IO Nat) : IO (Nat × Nat) := do
  let mut ts : Array Nat := #[]
  let mut v := 0
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    v ← f ()
    let t1 ← IO.monoNanosNow
    ts := ts.push ((t1 - t0) / 1000)
  pure (median ts, v)

def report (n : Nat) (name : String) (r : Nat × Nat) : IO Unit :=
  IO.println s!"n={n} phase={name} ms={r.1 / 1000}.{(r.1 % 1000) / 100} value={r.2}"

/-- `l4iter-phases N REPEATS bin` times only the op `datasetQuadsBin`, for a
profiler run. -/
def onlyBin (n reps : Nat) (h : String) : IO UInt32 := do
  report n "op datasetQuadsBin" (← timed reps fun _ => do
    pure (← datasetQuadsBin h "").2.size)
  pure 0

def main (args : List String) : IO UInt32 := do
  let n := (args.head?.bind String.toNat?).getD 60000
  let reps := ((args.drop 1).head?.bind String.toNat?).getD 5
  let text := sourceText n
  let opened ← datasetOpenBy noExtraReader text "nquads" ""
  let some j := L4Factoidal.JSON.parseJson? opened | IO.eprintln opened; pure 1
  let some (.string h) := j.field? "handle" | IO.eprintln opened; pure 1
  let some (ds, _) ← lookupHandleDataset h | pure 1
  if (args.drop 2).head? == some "bin" then return (← onlyBin n reps h)
  let qs := TermJson.Dataset.quadList ds
  report n "quadList" (← timed reps fun _ => pure (TermJson.Dataset.quadList ds).length)
  report n "compactFast" (← timed reps fun _ => pure (TermJson.compactFast qs).1.size)
  let c := TermJson.compactFast qs
  report n "checkCompact" (← timed reps fun _ =>
    pure (if TermJson.checkCompact c.1 qs c.2 then 1 else 0))
  report n "termsText" (← timed reps fun _ =>
    pure (c.1.foldl (fun (acc : String) t =>
      (if acc.isEmpty then acc else acc ++ ",") ++ TermJson.termText t) "").utf8ByteSize)
  report n "ixsText" (← timed reps fun _ =>
    pure (c.2.foldl (fun (acc : String) ix =>
      (if acc.isEmpty then acc else acc ++ ",") ++ "[" ++
        (ix.foldl (fun (a : String) i => (if a.isEmpty then a else a ++ ",") ++ toString i) "") ++ "]") "").utf8ByteSize)
  report n "op datasetQuadsJson compact" (← timed reps fun _ => do
    pure (← datasetQuadsJson h "{\"compact\":true}").utf8ByteSize)
  report n "op datasetQuadsBin" (← timed reps fun _ => do
    pure (← datasetQuadsBin h "").2.size)
  report n "op datasetSerialize nquads" (← timed reps fun _ => do
    pure (← datasetSerialize h "nquads").utf8ByteSize)
  report n "toCanonicalNQuads" (← timed reps fun _ =>
    pure (L4Factoidal.Syntax.Dataset.toCanonicalNQuads ds).utf8ByteSize)
  pure 0

end Harness.IterPhases

def main (args : List String) : IO UInt32 := Harness.IterPhases.main args
