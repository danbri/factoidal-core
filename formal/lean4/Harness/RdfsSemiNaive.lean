/-
Harness.RdfsSemiNaive — `l4rdfs-semi`: does the delta closure agree
with the naive one, and how long does each take?

Not part of the verified library: it reads files and prints scores.

## Two modes

    lake exe l4rdfs-semi [maxChainLength]
    l4rdfs-semi --time [--runs N] FILE...

The first mode generates subclass chains and property hierarchies and
reports AGREEMENT only (`delta vs naive closure: ...`, read by
`tools/lean-scoreboard.sh`).

The second mode (added 2026-10-12, issue
https://github.com/danbri/factoidal/issues/756) reads each FILE as
Turtle (N-Triples is a subset) and reports, per file, the minimum over
N runs of the time of `closureFix` (the naive loop, which the compiler
replaces by the indexed `closureFast`), `semiNaive`, the run-time check
`isNaiveFixpoint (semiNaive g)`, and the checked entry
`closureSemiNaiveChecked`, with agreement of the checked entry and
`closureFix` as sets.

## How the timing forces the computation

Three earlier versions of the timing in this harness reported 0 ms
while the process spent 90 seconds of CPU (issue
https://github.com/danbri/factoidal/issues/554). `timed` below makes
the INPUT depend on the first clock read (`if t0 == 0 then [] else g`),
so the computation cannot move before it, and writes the result's
length to an `IO.Ref` before the second clock read, so it cannot move
after it. Check of the method, 2026-10-12: the per-call times printed
by `--time` add up to within a few percent of the user CPU time
`/usr/bin/time` reports for the whole process (numbers in
`docs/designissues/2026-10-10-rdfs-seminaive.md`).

The agreement result stands on its own: `closureSemiNaiveChecked`
returns the naive answer whenever the delta loop is not a fixed point,
so a hole in the delta reasoning costs a slow run, never a wrong one.
`L4Factoidal/RDFS/SemiNaiveTheorems.lean` now proves the delta loop
sound, saturated when it stops by a test, and equal to `closureFix` as
a set when both are saturated.
-/
import L4Factoidal.RDFS.SemiNaiveTheorems
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.Turtle

open L4Factoidal.RDF L4Factoidal.RDFS

namespace Harness.RdfsSemiNaive

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

def iri (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩

/-- `a rdf:type C1`, `C1 ⊑ C2`, …, `C(n-1) ⊑ Cn`. The closure holds
    n `rdf:type` triples and n(n-1)/2 transitive `rdfs:subClassOf`
    triples, so the naive loop's re-derivation cost grows fast. -/
def chainOf (n : Nat) : Graph :=
  ⟨.iri (iri "a"), rdfType, .iri (iri "C1")⟩ ::
  (List.range (n - 1)).map (fun k =>
    (⟨.iri (iri s!"C{k+1}"), rdfsSubClassOf, .iri (iri s!"C{k+2}")⟩ : Triple))

/-- A property hierarchy with a domain and a range, so rows rdfs7,
    rdfs2, rdfs3 and rdfs5 fire as well as rdfs9 and rdfs11. -/
def schemaOf (n : Nat) : Graph :=
  (List.range (n - 1)).map (fun k =>
    (⟨.iri (iri s!"p{k+1}"), rdfsSubPropertyOf, .iri (iri s!"p{k+2}")⟩ : Triple)) ++
  [ ⟨.iri (iri s!"p{n}"), rdfsDomain, .iri (iri "D")⟩,
    ⟨.iri (iri s!"p{n}"), rdfsRange, .iri (iri "R")⟩,
    ⟨.iri (iri "x"), iri "p1", .iri (iri "y")⟩,
    ⟨.iri (iri "D"), rdfsSubClassOf, .iri (iri "DSuper")⟩ ]

/-- Set equality of two graphs. The obvious `a.all (· ∈ b) && b.all (· ∈ a)`
    is O(n²) and, at 5000 triples, costs minutes — more than the closures
    it is checking, which is how the first version of this harness came
    to time out before it measured anything. This sorts both sides'
    canonical N-Triples renderings instead, which is O(n log n). -/
def sameGraph (a b : Graph) : Bool :=
  let key (g : Graph) : List String :=
    (g.map L4Factoidal.Syntax.Triple.toCanonicalNTriples).eraseDups.mergeSort
      (fun x y => decide (x ≤ y))
  key a == key b

/-! ## Measuring -/

structure Row where
  label   : String
  size    : Nat
  outSize : Nat
  agree   : Bool
  ownFix  : Bool   -- the delta loop reached the fixpoint without the fallback


def measure (label : String) (g : Graph) : IO Row := do
  let naive := closureFix g
  let fast := semiNaive g
  let ownFix := isNaiveFixpoint fast
  let checked := if ownFix then fast else naive
  return { label := label, size := g.length, outSize := naive.length,
           agree := sameGraph checked naive, ownFix := ownFix }

def render (r : Row) : String :=
  s!"  {r.label} in={r.size} out={r.outSize} agree={r.agree} " ++
  s!"delta-reached-fixpoint={r.ownFix}"

/-! ## Timing mode -/

/-- Run `f` on `g`; return the result and the elapsed nanoseconds. The
input depends on the first clock read and the result's length is
written to `sink` before the second, so the computation sits between
the two reads. -/
def timed (sink : IO.Ref Nat) (g : Graph) (f : Graph → Graph) : IO (Graph × Nat) := do
  let t0 ← IO.monoNanosNow
  let g' := if t0 == 0 then [] else g
  let r := f g'
  sink.set r.length
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- `timed` for a Boolean test of a graph. -/
def timedBool (sink : IO.Ref Nat) (g : Graph) (f : Graph → Bool) : IO (Bool × Nat) := do
  let t0 ← IO.monoNanosNow
  let g' := if t0 == 0 then [] else g
  let r := f g'
  sink.set (if r then 1 else 0)
  let t1 ← IO.monoNanosNow
  return (r, t1 - t0)

/-- The minimum over `runs` runs, and the last result. -/
def minTimed (runs : Nat) (act : IO (α × Nat)) : IO (α × Nat) := do
  let (r0, t0) ← act
  let mut best := t0
  let mut res := r0
  for _ in [1:runs] do
    let (r, t) ← act
    res := r
    if t < best then best := t
  return (res, best)

def ms (ns : Nat) : String :=
  let tenths := (ns + 50000) / 100000
  s!"{tenths / 10}.{tenths % 10}"

structure TimeRow where
  label    : String
  size     : Nat
  outSize  : Nat
  naiveNs  : Nat
  deltaNs  : Nat
  checkNs  : Nat
  checkedNs : Nat
  agree    : Bool
  ownFix   : Bool

def timeFile (runs : Nat) (path : String) : IO (Option TimeRow) := do
  let text ← IO.FS.readFile path
  match L4Factoidal.Syntax.parseTurtle text (some ("file://" ++ path)) with
  | .error e =>
      IO.println s!"  {path}: parse error {e}"
      return none
  | .ok g =>
      let sink ← IO.mkRef 0
      let (naive, tn) ← minTimed runs (timed sink g closureFix)
      let (fast, td) ← minTimed runs (timed sink g semiNaive)
      let (own, tc) ← minTimed runs (timedBool sink fast isNaiveFixpoint)
      let (checked, tk) ← minTimed runs (timed sink g closureSemiNaiveChecked)
      return some { label := path, size := g.length, outSize := naive.length,
                    naiveNs := tn, deltaNs := td, checkNs := tc, checkedNs := tk,
                    agree := sameGraph checked naive, ownFix := own }

def renderTime (r : TimeRow) : String :=
  s!"  {r.label} in={r.size} out={r.outSize} naive_ms={ms r.naiveNs} " ++
  s!"delta_ms={ms r.deltaNs} check_ms={ms r.checkNs} checked_ms={ms r.checkedNs} " ++
  s!"agree={r.agree} delta-reached-fixpoint={r.ownFix}"

def timeMain (args : List String) : IO UInt32 := do
  let (runs, files) :=
    match args with
    | "--runs" :: n :: rest => ((n.toNat?).getD 3, rest)
    | rest => (3, rest)
  let mut rows : List TimeRow := []
  IO.println s!"--- closureFix against closureSemiNaiveChecked, minimum of {runs} runs, ms ---"
  for f in files do
    match ← timeFile runs f with
    | some r =>
        IO.println (renderTime r)
        rows := r :: rows
    | none => pure ()
  let agree := rows.countP (·.agree)
  let own := rows.countP (·.ownFix)
  let total := rows.length
  let sum (f : TimeRow → Nat) : Nat := rows.foldl (fun a r => a + f r) 0
  IO.println ""
  IO.println s!"delta vs naive closure: {agree} agree, {total - agree} differ (out of {total})"
  IO.println s!"delta loop reached the fixpoint without the fallback: {own} of {total}"
  IO.println (s!"total ms: naive {ms (sum (·.naiveNs))}, delta {ms (sum (·.deltaNs))}, " ++
    s!"check {ms (sum (·.checkNs))}, checked {ms (sum (·.checkedNs))}")
  return (if agree == total then 0 else 1)

def main (args : List String) : IO UInt32 := do
  if args.head? == some "--time" then return (← timeMain args.tail) else
  let maxN := (args.head?.bind String.toNat?).getD 100
  let sizes := [20, 50, 100, maxN].filter (· ≤ maxN) |>.eraseDups
  let mut rows : List Row := []
  IO.println "--- subclass chain (issue #340 shape) ---"
  for n in sizes do
    let r ← measure s!"chain{n}" (chainOf n)
    IO.println (render r)
    rows := r :: rows
  IO.println ""
  IO.println "--- property hierarchy with domain and range ---"
  for n in sizes do
    let r ← measure s!"schema{n}" (schemaOf n)
    IO.println (render r)
    rows := r :: rows
  let agree := rows.countP (·.agree)
  let own := rows.countP (·.ownFix)
  let total := rows.length
  IO.println ""
  IO.println s!"delta vs naive closure: {agree} agree, {total - agree} differ (out of {total})"
  IO.println s!"delta loop reached the fixpoint without the fallback: {own} of {total}"
  IO.println "A case where the fallback fired still AGREES -- it returns the naive answer."
  IO.println "The second line is what says the delta loop did the work."
  IO.println "Speed: run with --time FILE... (module header)."
  return (if agree == total then 0 else 1)

end Harness.RdfsSemiNaive

def main (args : List String) : IO UInt32 := Harness.RdfsSemiNaive.main args
