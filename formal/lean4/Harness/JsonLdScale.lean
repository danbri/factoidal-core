/-
Harness/JsonLdScale — scaling measurement for the JSON-LD pipeline.

Run through the API probe (from the REPOSITORY ROOT):

    formal/lean4/.lake/build/bin/l4jsonld-api --scale [base [reps]]

For each document shape it builds the document at n, 2n, 4n, 8n and 16n
(n = `base`, default 250), and for each size prints the wall time of
each phase:

  * expand        — `expandDocument` (parse + API §5.1 expansion);
  * node map      — `generateNodeMap` (API §7.1 / §7.2) on the expanded form;
  * flatten       — `flattenExpanded` (node map + §6.1 emission);
  * flatten+ctx   — `flattenDocument` with a context (expand, flatten,
                    compact);
  * frame         — `frameDocument` (expand, node map, framing, compact).

Each time is the minimum of `reps` runs (default 3). Then it checks the
SCALING ASSERTION of skills/danbri-function-precrime-checkers: for every
shape, phase and size pair (x, 4x), time(4x) must stay under `bound`
(9.0) times max(time(x), `floorMs`). A linear-times-log phase gives a
ratio of about 4 to 6; a quadratic phase gives about 16. The floor keeps a
sub-millisecond baseline from turning timer noise into a failure. The
exit code is 1 when any pair fails.

This is a HARNESS: it reads the clock and prints. It is not part of the
verified library, and it is not a `#guard` because a wall-clock bound
cannot be decided at elaboration time.

## Document shapes

  * hub     — n flat typed nodes that each link to one shared hub node;
  * fanout  — one node with n distinct node references under one property;
  * bnode   — a chain of n blank nodes (n entries in the relabelling map);
  * graphs  — n named graphs of one node each;
  * wide    — one node with n distinct properties.
-/
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSONLD.Compact
import L4Factoidal.JSONLD.Flatten
import L4Factoidal.JSONLD.Frame

open L4Factoidal.JSON
open L4Factoidal.JSONLD

namespace JsonLdScale

/-- Differential-testing hook. When the environment variable
`L4_JSONLD_DUMP` names a file, append one line per call: `tag`, a tab, and
the output rendered with `Json.toStringCompact` (object member order
included, which the suites' JCS comparison ignores) or `ERROR code`.
Running the same suites with two builds and comparing the two files shows
whether a change altered any output byte. -/
def rawDump (tag : String) (r : Res Json) : IO Unit := do
  match ← IO.getEnv "L4_JSONLD_DUMP" with
  | none => pure ()
  | some path =>
    let line := match r with
                | .ok j => toStringCompact j
                | .error e => "ERROR " ++ e.code
    IO.FS.withFile path .append (fun h => h.putStrLn (tag ++ "\t" ++ line))

def ex (s : String) : String := "http://example.org/" ++ s

def q (s : String) : String := "\"" ++ s ++ "\""

def joinWith (sep : String) (xs : List String) : String :=
  match xs with
  | [] => ""
  | x :: rest => rest.foldl (fun a b => a ++ sep ++ b) x

def range (n : Nat) : List Nat := List.range n

structure Shape where
  name  : String
  /-- The input document of size `n`. -/
  doc   : Nat → String
  /-- The frame document used for the frame phase. -/
  frame : Nat → String

def ctxText : String :=
  "{\"@context\": {\"ex\": \"http://example.org/\", \"link\": {\"@id\": \"ex:link\", \"@type\": \"@id\"}, \"p\": \"ex:p\", \"T\": \"ex:T\"}}"

def hubShape : Shape where
  name := "hub"
  doc n :=
    let node (i : Nat) : String :=
      "{\"@id\": " ++ q (ex s!"n{i}") ++ ", \"@type\": " ++ q (ex "T") ++
      ", " ++ q (ex "p") ++ ": " ++ q s!"value {i}" ++
      ", " ++ q (ex "link") ++ ": {\"@id\": " ++ q (ex "hub") ++ "}}"
    let hub := "{\"@id\": " ++ q (ex "hub") ++ ", " ++ q (ex "p") ++ ": \"hub\"}"
    "[" ++ joinWith ", " ((range n).map node ++ [hub]) ++ "]"
  frame _ := "{\"@context\": " ++ "{\"ex\": \"http://example.org/\"}" ++
             ", \"@type\": " ++ q (ex "T") ++ "}"

def fanoutShape : Shape where
  name := "fanout"
  doc n :=
    let refs := (range n).map (fun i => "{\"@id\": " ++ q (ex s!"o{i}") ++ "}")
    "{\"@id\": " ++ q (ex "s") ++ ", " ++ q (ex "link") ++ ": [" ++ joinWith ", " refs ++ "]}"
  frame _ := "{\"@context\": {\"ex\": \"http://example.org/\"}, \"@id\": " ++ q (ex "s") ++ "}"

def bnodeShape : Shape where
  name := "bnode"
  doc n :=
    let node (i : Nat) : String :=
      "{\"@id\": " ++ q s!"_:x{i}" ++ ", " ++ q (ex "p") ++ ": " ++ q s!"{i}" ++
      ", " ++ q (ex "link") ++ ": {\"@id\": " ++ q s!"_:x{i + 1}" ++ "}}"
    "[" ++ joinWith ", " ((range n).map node) ++ "]"
  frame _ := "{\"@context\": {\"ex\": \"http://example.org/\"}, \"@embed\": \"@never\"}"

def graphsShape : Shape where
  name := "graphs"
  doc n :=
    let g (i : Nat) : String :=
      "{\"@id\": " ++ q (ex s!"g{i}") ++ ", \"@graph\": [{\"@id\": " ++ q (ex s!"n{i}") ++
      ", " ++ q (ex "p") ++ ": \"v\"}]}"
    "[" ++ joinWith ", " ((range n).map g) ++ "]"
  frame _ := "{\"@context\": {\"ex\": \"http://example.org/\"}}"

def wideShape : Shape where
  name := "wide"
  doc n :=
    let props := (range n).map (fun i => q (ex s!"p{i}") ++ ": " ++ q s!"v{i}")
    "{\"@id\": " ++ q (ex "s") ++ ", " ++ joinWith ", " props ++ "}"
  frame _ := "{\"@context\": {\"ex\": \"http://example.org/\"}, \"@id\": " ++ q (ex "s") ++ "}"

def shapes : List Shape := [hubShape, fanoutShape, bnodeShape, graphsShape, wideShape]

/-- The phases, in the order they are printed. -/
def phaseNames : List String :=
  ["expand", "node map", "flatten", "flatten+ctx", "frame"]

/-- Size of a result, used so the computation cannot be dropped. -/
def resSize (r : Res Json) : Nat :=
  match r with
  | .ok j => Json.size j
  | .error _ => 0

/-- Run `f` `reps` times; return the minimum wall time in microseconds and
the checksum of the last run. The branch on the checksum makes the
computation happen before the second clock read: without a use between
the two reads, the compiler floats the pure `let` past the clock. -/
@[noinline] def timed (reps : Nat) (f : Unit → Nat) : IO (Nat × Nat) := do
  let mut best : Nat := 0
  let mut seen := false
  let mut sum : Nat := 0
  for _ in [0:reps] do
    let t0 ← IO.monoNanosNow
    let r := f ()
    if r == 0xFFFFFFFFFFFFFFF then IO.eprintln "checksum collision"
    let t1 ← IO.monoNanosNow
    let us := (t1 - t0) / 1000
    if !seen || us < best then best := us
    seen := true
    sum := r
  return (best, sum)

/-- Times of the five phases at one size, in microseconds, and a checksum
of the results. -/
def measure (sh : Shape) (n reps : Nat) : IO (List Nat × Nat) := do
  let loader : Loader := fun _ => none
  let doc := sh.doc n
  let frameDoc := sh.frame n
  let (tExp, cExp) ← timed reps (fun _ =>
    resSize (expandDocument loader doc none none none))
  let ej : Json := match expandDocument loader doc none none none with
                   | .ok j => j | .error _ => .null
  let (tNm, nm) ← timed reps (fun _ =>
    match generateNodeMap ej with | .ok st => st.nodeCount | .error _ => 0)
  let (tFl, fl) ← timed reps (fun _ =>
    match flattenExpanded ej with | .ok xs => xs.length | .error _ => 0)
  let (tFc, fc) ← timed reps (fun _ =>
    resSize (flattenDocument loader doc (some ctxText) none none true none))
  let (tFr, fr) ← timed reps (fun _ => resSize (frameDocument loader doc frameDoc none none))
  return ([tExp, tNm, tFl, tFc, tFr], cExp + nm + fl + fc + fr)

def fmtMs (us : Nat) : String :=
  let whole := us / 1000
  let frac := (us % 1000) / 100
  s!"{whole}.{frac}"

def padLeft (s : String) (w : Nat) : String :=
  String.ofList (List.replicate (w - s.length) ' ') ++ s

structure Row where
  shape : String
  n     : Nat
  times : List Nat
  sum   : Nat

def run (base reps : Nat) (bound : Nat) (floorMs : Nat) : IO UInt32 := do
  let sizes := [base, 2 * base, 4 * base, 8 * base, 16 * base]
  IO.println s!"JSON-LD scaling measurement: base n = {base}, {reps} run(s) per point, minimum reported"
  IO.println s!"times are wall-clock milliseconds; assertion: time(4x) <= {bound}/10 * max(time(x), {floorMs} ms)"
  let mut rows : List Row := []
  for sh in shapes do
    IO.println ""
    IO.println s!"shape {sh.name}"
    IO.println ("        n" ++ String.join (phaseNames.map (fun p => padLeft p 14)))
    for n in sizes do
      let (ts, sum) ← measure sh n reps
      rows := rows ++ [{ shape := sh.name, n := n, times := ts, sum := sum }]
      IO.println (padLeft (toString n) 9 ++ String.join (ts.map (fun t => padLeft (fmtMs t) 14)))
  IO.println ""
  IO.println "scaling assertion"
  let mut pass := 0
  let mut fail := 0
  for sh in shapes do
    let shRows := rows.filter (fun r => r.shape == sh.name)
    for pi in [0:phaseNames.length] do
      for x in [0:sizes.length - 2] do
        match shRows[x]?, shRows[x + 2]? with
        | some r1, some r4 =>
          let t1 := r1.times[pi]!
          let t4 := r4.times[pi]!
          let base1 := Nat.max t1 (floorMs * 1000)
          -- t4 <= (bound / 10) * base1, in integers
          if t4 * 10 <= bound * base1 then pass := pass + 1
          else
            fail := fail + 1
            IO.println s!"  FAIL {sh.name} / {phaseNames[pi]!}: n={r1.n} {fmtMs t1} ms -> n={r4.n} {fmtMs t4} ms (ratio {(t4 * 10 / (Nat.max t1 1)) / 10}.{(t4 * 10 / (Nat.max t1 1)) % 10} for 4x input)"
        | _, _ => pure ()
  IO.println s!"scaling: {pass} pass, {fail} fail (out of {pass + fail}) size pairs; checksum {rows.foldl (fun a r => a + r.sum) 0}"
  return (if fail == 0 then 0 else 1)

/-- `--dump-shapes`: write the raw output of the flatten and frame
algorithms for every shape at a few small sizes through `rawDump`, for a
byte-level comparison of two builds. -/
def dumpShapes : IO UInt32 := do
  let loader : Loader := fun _ => none
  for sh in shapes do
    for n in [1, 2, 5, 40, 150] do
      let doc := sh.doc n
      rawDump s!"shape {sh.name} {n} flatten" (flattenDocument loader doc none none none true none)
      rawDump s!"shape {sh.name} {n} flatten+ctx"
        (flattenDocument loader doc (some ctxText) none none true none)
      rawDump s!"shape {sh.name} {n} frame" (frameDocument loader doc (sh.frame n) none none)
  return 0

/-- Entry: `args` follow `--scale`: optional base size, optional repetitions. -/
def main (args : List String) : IO UInt32 := do
  if args.head? == some "--dump-shapes" then return (← dumpShapes)
  let base := (args[0]?.bind String.toNat?).getD 250
  let reps := (args[1]?.bind String.toNat?).getD 3
  run base reps 90 20

end JsonLdScale
