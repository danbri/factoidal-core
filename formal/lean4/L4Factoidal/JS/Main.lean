import L4Factoidal.JS

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
runner runs both modes; one mode here, as `WasmVM/Bench/Test262.lean` does for
QuickJS). `raw` gets no harness. A `negative:` test passes when the named error is
the outcome in the named phase (`parse`: a `SyntaxError` before any statement
runs). Not run, counted as skipped: `module` and `async` flags, `resolution`
phase.
-/

namespace L4Factoidal.JS.Main
open L4Factoidal.JS

structure Meta where
  flags : List String := []
  includes : List String := []
  features : List String := []
  negPhase : Option String := none
  negType : Option String := none

/-- The YAML front matter between `/*---` and `---*/`, read for the four keys. -/
def parseMeta (src : String) : Meta := Id.run do
  let some start := (src.splitOn "/*---")[1]? | return {}
  let body := (start.splitOn "---*/").headD ""
  let lines := body.splitOn "\n"
  let listOf (s : String) : List String :=
    let s := s.trimAscii.toString
    if s.startsWith "[" then
      ((s.drop 1).dropEnd 1).toString.splitOn "," |>.map (·.trimAscii.toString) |>.filter (· != "")
    else []
  let mut m : Meta := {}
  let mut cur := ""
  for l in lines do
    let t := l.trimAscii.toString
    if l.startsWith "flags:" then m := { m with flags := listOf (l.drop 6).toString }; cur := ""
    else if l.startsWith "includes:" then
      m := { m with includes := listOf (l.drop 9).toString }; cur := "includes"
    else if l.startsWith "features:" then
      m := { m with features := listOf (l.drop 9).toString }; cur := "features"
    else if l.startsWith "negative:" then cur := "negative"
    else if t.startsWith "- " && cur == "includes" then
      m := { m with includes := m.includes ++ [(t.drop 2).trimAscii.toString] }
    else if t.startsWith "- " && cur == "features" then
      m := { m with features := m.features ++ [(t.drop 2).trimAscii.toString] }
    else if cur == "negative" && t.startsWith "phase:" then
      m := { m with negPhase := some (t.drop 6).trimAscii.toString }
    else if cur == "negative" && t.startsWith "type:" then
      m := { m with negType := some (t.drop 5).trimAscii.toString }
    else if !l.startsWith " " && !l.startsWith "\t" && t != "" then cur := ""
  return m

inductive Verdict where
  /-- `neg`: a negative test (an expected error). -/
  | pass (neg : Bool) | fail (why : String) | skip (why : String)

/-- The heap after the default harness, computed once per run. -/
def harnessHeap (root : System.FilePath) : IO Heap := do
  let a ← IO.FS.readFile (root / "harness" / "assert.js")
  let s ← IO.FS.readFile (root / "harness" / "sta.js")
  match runScript freshHeap (a ++ "\n" ++ s) with
  | (.ok, h) => pure h
  | (o, _) =>
    let why := match o with
      | .syntaxError m => m | .threw _ m => m | .halted w => w | .ok => ""
    throw (IO.userError s!"harness failed: {why}")

/-- `force`: `some true` runs the test as strict code, `some false` as sloppy code, `none` by its
flags (strict only for `onlyStrict`). -/
def runTest (root : System.FilePath) (base : Heap) (path : System.FilePath) (force : Option Bool := none) : IO Verdict := do
  let src ← IO.FS.readFile path
  let m := parseMeta src
  if m.flags.contains "module" then return .skip "module"
  let isAsync := m.flags.contains "async"
  if m.negPhase == some "resolution" then return .skip "resolution"
  let strict := force.getD (m.flags.contains "onlyStrict")
  let raw := m.flags.contains "raw"
  let mut h := if raw then freshHeap else base
  if !raw then
    for inc in (if isAsync then ["doneprintHandle.js"] else []) ++ m.includes do
      let p := root / "harness" / inc
      if !(← p.pathExists) then return .skip s!"include {inc}"
      match runScript h (← IO.FS.readFile p) with
      | (.ok, h') => h := h'
      | _ => return .skip s!"include {inc} failed"
  let hRun := { h with steps := 20000000 }
  let (o, hOut) := runScript hRun src strict
  if isAsync && m.negPhase.isNone then
    match o with
    | .ok =>
      if hOut.out.contains "Test262:AsyncTestComplete" then return .pass false
      else return .fail ("async: " ++ (" ".intercalate hOut.out.toList).take 160)
    | _ => pure ()
  match m.negPhase, m.negType, o with
  | none, _, .ok => pure (.pass false)
  | none, _, .syntaxError e => pure (.fail e)
  | none, _, .threw _ e => pure (.fail e)
  | none, _, .halted w => pure (.fail s!"halted: {w}")
  | some "parse", some t, .syntaxError _ => pure (if t == "SyntaxError" then .pass true else .fail "wrong error")
  | some "parse", _, _ => pure (.fail "expected a SyntaxError at parse time")
  | some "runtime", some t, .threw _ e =>
    pure (if e.startsWith (t ++ ":") || e == t then .pass true else .fail s!"expected {t}, got {e}")
  | some _, _, _ => pure (.fail "expected an error")

def jsFiles (dir : System.FilePath) : IO (Array System.FilePath) := do
  let all ← dir.walkDir
  let fs := all.filter fun p =>
    let n := p.fileName.getD ""
    n.endsWith ".js" && !n.endsWith "_FIXTURE.js"
  return fs.qsort (fun a b => a.toString < b.toString)

def test262 (root : System.FilePath) (dirs : List String) (listOut : Option String) : IO Unit := do
  let base ← harnessHeap root
  let mut lines : Array String := #[]
  let mut tp := 0; let mut tf := 0; let mut ts := 0; let mut tneg := 0
  let t0 ← IO.monoMsNow
  for d in dirs do
    let files ← jsFiles (root / d)
    let mut p := 0; let mut f := 0; let mut s := 0; let mut neg := 0
    for file in files do
      let v ← runTest root base file
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

/-- The modes Test262 runs a file in (INTERPRETING.md, "Strict Mode"): `onlyStrict` strict,
`noStrict` and `raw` sloppy, `module` once (as a module), any other file twice, sloppy and strict. -/
def modesOf (flags : List String) : List Bool :=
  if flags.contains "onlyStrict" || flags.contains "module" then [true]
  else if flags.contains "noStrict" || flags.contains "raw" then [false]
  else [false, true]

#guard modesOf [] = [false, true]
#guard modesOf ["onlyStrict"] = [true]
#guard modesOf ["noStrict"] = [false]
#guard modesOf ["raw"] = [false]
#guard modesOf ["async"] = [false, true]
#guard modesOf ["module"] = [true]

/-- `leanjs test262-files ROOT LIST`: each test named in LIST (paths relative to ROOT, one a
line) in every mode Test262 runs it in; one line a run on stdout as soon as it ends, flushed:
`PASS|FAIL|SKIP <path> <strict|sloppy> [why]`. A driver that sees the process end before the
last line knows which test it was on. -/
def test262Files (root : System.FilePath) (list : String) : IO Unit := do
  let base ← harnessHeap root
  let out ← IO.getStdout
  for rel in ((← IO.FS.readFile list).splitOn "\n").filter (· != "") do
    let path := root / rel
    let flags := (parseMeta (← IO.FS.readFile path)).flags
    for strict in modesOf flags do
      let mode := if strict then "strict" else "sloppy"
      out.putStrLn s!"START {rel} {mode}"
      out.flush
      let v ← runTest root base path (some strict)
      let line := match v with
        | .pass _ => s!"PASS {rel} {mode}"
        | .fail why => s!"FAIL {rel} {mode} {(why.replace "\n" " ").take 160}"
        | .skip why => s!"SKIP {rel} {mode} {why}"
      out.putStrLn line
      out.flush

def fibSrc : String := "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2); } print(fib(24));"

/-- The loop benchmark of `WasmVM/Bench/QuickJS.lean` (`speed: loop and JSON`), the same text. -/
def loopSrc : String :=
  "print((() => { let s = 0; for (let i = 0; i < 200000; i++) s = (s + i * i) % 1000003; " ++
  "const o = []; for (let i = 0; i < 2000; i++) o.push({ k: 'k' + i, v: i }); " ++
  "return s + ' ' + JSON.stringify(o).length })())"

def timeIt (name src : String) : IO Unit := do
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
  match args with
  | ["run", file] =>
    let (o, out) := run (← IO.FS.readFile file)
    for l in out do IO.println l
    match o with
    | .ok => pure 0
    | .threw _ m => IO.eprintln s!"Uncaught {m}"; pure 1
    | .syntaxError m => IO.eprintln m; pure 1
    | .halted w => IO.eprintln s!"halted: {w}"; pure 2
  | ["eval", src] =>
    let (o, out) := run src
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
    test262 root dirs listOut
    pure 0
  | ["test262-files", root, list] =>
    test262Files root list
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
    IO.eprintln "usage: leanjs run FILE | eval SRC | test262 ROOT DIR... [--list OUT] | test262-files ROOT LIST | bench"
    pure 64

end L4Factoidal.JS.Main

def main (args : List String) : IO UInt32 := L4Factoidal.JS.Main.main args
