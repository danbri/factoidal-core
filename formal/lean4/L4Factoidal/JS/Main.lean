import L4Factoidal.JS
import L4Factoidal.JS.Test262

/-!
# `lake exe leanjs` — run scripts, Test262 files and the benchmarks

- `leanjs run FILE`: run a script, print what it prints and the outcome.
- `leanjs eval SOURCE`: the same for a source text on the command line.
- `leanjs test262 ROOT DIR... [--list OUT]`: run every `.js` test under each `DIR`
  (paths relative to `ROOT`, the Test262 checkout or the vendored subset), with
  `ROOT/harness/assert.js` and `sta.js` and the `includes:` the test names.
  Prints the counts by directory; `--list` writes `PASS`/`FAIL`/`SKIP` per file.
- `leanjs bench`: `fib(24)` and a loop with string and object work, timed.

The Test262 rules (`INTERPRETING.md` of Test262): `flags: [onlyStrict]` runs strict
only, `noStrict` and `raw` sloppy only, others once in sloppy mode (the upstream
runner runs both modes; `test262-files` does, `test262` runs one mode, as
`WasmVM/Bench/Test262.lean` does for QuickJS). `raw` gets no harness. `module` tests run
as a module graph loaded from the files they name. A `negative:` test passes when the
named error is the outcome in the named phase (`parse`: a `SyntaxError` before any
statement runs; `resolution`: loading or linking a module graph). `async` tests pass
when `$DONE` prints `Test262:AsyncTestComplete`.
-/

namespace L4Factoidal.JS.Main
open L4Factoidal.JS L4Factoidal.JS.Test262

def jsFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let all ← dir.walkDir
  let fs := all.filter fun p =>
    let n := p.fileName.getD ""
    n.endsWith ".js" && !n.endsWith "_FIXTURE.js"
  return fs.qsort (fun a b => a.toString < b.toString)

def test262 [Mode] (fresh : Heap) (root : System.FilePath) (dirs : List String) (listOut : Option String) : IO Unit := do
  let base ← harnessHeap root fresh false
  let mut lines : Array String := #[]
  let mut tp := 0; let mut tf := 0; let mut ts := 0; let mut tneg := 0
  let t0 ← IO.monoMsNow
  for d in dirs do
    let files ← jsFiles (root / d)
    let mut p := 0; let mut f := 0; let mut s := 0; let mut neg := 0
    for file in files do
      let v ← runTest root fresh base false file
      let rel := (file.toString.drop (root.toString.length + 1)).toString
      match v with
      | .pass ng =>
        p := p + 1
        if ng then neg := neg + 1
        lines := lines.push s!"PASS {rel}"
      | .fail why => f := f + 1; lines := lines.push s!"FAIL {rel} {(why.replace "\n" " ").take 160}"
      | .skip why => s := s + 1; lines := lines.push s!"SKIP {rel} {why}"
    IO.println s!"{d}: {p} pass ({neg} negative), {f} fail, {s} skip (of {files.size})"
    tp := tp + p; tf := tf + f; ts := ts + s; tneg := tneg + neg
  let t1 ← IO.monoMsNow
  IO.println s!"total: {tp} pass ({tneg} of them negative tests), {tf} fail, {ts} skip; run {tp + tf}, {if tp + tf == 0 then 0 else tp * 1000 / (tp + tf)} per mille pass; {t1 - t0} ms"
  if let some out := listOut then IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\n")

def fibSrc : String := "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); } print(fib(24));"

/-- The loop benchmark of `WasmVM/Bench/QuickJS.lean` (`speed: loop and JSON`), the same text. -/
def loopSrc : String :=
  "print((() => { let s = 0; for (let i = 0; i < 200000; i++) s = (s + i * i) % 1000003; " ++
  "const o = []; for (let i = 0; i < 2000; i++) o.push({ k: 'k' + i, v: i }); " ++
  "return s + ' ' + JSON.stringify(o).length })())"

def timeIt [Mode] (name src : String) : IO Unit := do
  let t0 ← IO.monoNanosNow
  let (o, out) := run src
  let t1 ← IO.monoNanosNow
  let res := match o with
    | .ok => " ".intercalate out.toList
    | .threw _ m => s!"threw {m}"
    | .syntaxError m => m
    | .halted w => s!"halted {w}"
  IO.println s!"{name}: {res}; {(t1 - t0) / 1000000} ms"

def main (args : List String) : IO UInt32 := do
  -- `BUBBLEPOP_VM=off`: the register machine is off for the run (the heap's `useVm`)
  let vm := (← IO.getEnv "BUBBLEPOP_VM") != some "off"
  let fresh : Heap := { freshHeap with useVm := vm }
  -- `BUBBLEPOP_TIER1=off`: the reference run, the evaluator with tier 1 off (`Mode.ref`)
  let md : Mode := ⟨(← IO.getEnv "BUBBLEPOP_TIER1") != some "off"⟩
  match args with
  | ["run", file] =>
    let (o, h) := runScript fresh (← IO.FS.readFile file)
    let out := h.out
    for l in out do IO.println l
    match o with
    | .ok => pure 0
    | .threw _ m => IO.eprintln s!"Uncaught {m}"; pure 1
    | .syntaxError m => IO.eprintln m; pure 1
    | .halted w => IO.eprintln s!"halted: {w}"; pure 2
  | ["eval", src] =>
    let (o, h) := runScript fresh src
    let out := h.out
    for l in out do IO.println l
    match o with
    | .ok => pure 0
    | .threw _ m => IO.eprintln s!"Uncaught {m}"; pure 1
    | .syntaxError m => IO.eprintln m; pure 1
    | .halted w => IO.eprintln s!"halted: {w}"; pure 2
  | "test262" :: root :: rest =>
    let (dirs, listOut) := match rest.reverse with
      | out :: "--list" :: ds => (ds.reverse, some out)
      | _ => (rest, none)
    test262 fresh root dirs listOut
    pure 0
  | ["test262-files", root, list] =>
    test262Files root list fresh
    pure 0
  | ["compile-stats", file] =>
    match parseScript (← IO.FS.readFile file) false with
    | .error e => IO.eprintln e; pure 1
    | .ok sc =>
      let (f, c) := Resolve.stats sc
      IO.println s!"functions {f}, compiled {c}"
      pure 0
  | ["bench"] =>
    timeIt "fib(24)" fibSrc
    timeIt "loop" loopSrc
    pure 0
  | _ =>
    IO.eprintln "usage: [BUBBLEPOP_VM=off] [BUBBLEPOP_TIER1=off] leanjs run FILE | eval SRC | test262 ROOT DIR... [--list OUT] | test262-files ROOT LIST | bench"
    pure 64

end L4Factoidal.JS.Main

def main (args : List String) : IO UInt32 := L4Factoidal.JS.Main.main args
