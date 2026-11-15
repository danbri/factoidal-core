import L4Factoidal.JS

/-!
# L4Factoidal.JS.Test262 — running Test262 files by Test262's rules

The runner of `leanjs test262-files` (the realm of the engine alone) and of `bubblepop-test262`
(`WasmVM/Hosts/Test262Page.lean`: the page realm, as the browser runs page scripts), on any
realm `HeapOf H`. Rules (`INTERPRETING.md` of Test262): each file in the modes Test262 runs it
in (`modesOf`); `raw` gets no harness; `module` tests run as a module graph loaded from the
files they name; a `negative:` test passes when the named error is the outcome in the named
phase (`parse`, `resolution`: loading or linking a module graph, `runtime`); `async` tests pass
when `$DONE` prints `Test262:AsyncTestComplete`.
-/

namespace L4Factoidal.JS.Test262
open L4Factoidal.JS

variable {H : Type}

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

/-- The host-defined `$262` object (Test262 `INTERPRETING.md`, "Host-Defined Functions"), as
far as this runner can give it without a way back into the interpreter: `global`, and
`detachArrayBuffer` by `ArrayBuffer.prototype.transfer` (which detaches its receiver,
§25.1.6.9 ArrayBufferCopyAndDetach), taken before any test code runs. Not given, so the
tests that call them fail: `createRealm`, `evalScript`, `gc`, `agent`, `IsHTMLDDA`. -/
def host262 : String :=
  "var $262 = (function () { var t = ArrayBuffer.prototype.transfer; var call = Function.prototype.call; " ++
  "return { global: globalThis, detachArrayBuffer: function (b) { call.call(t, b); return null; } }; })();"

/-- On the page realm `print` is the window's (it prints nothing, HTML §8.8.1): Test262's
`print` (what `$DONE` reports with) then appends to `$262.out`, read back by `printed`. -/
def pagePrint : String :=
  "(function () { var out = ''; Object.defineProperty($262, 'out', { get: function () { return out; } }); " ++
  "globalThis.print = function (m) { out = out + String(m) + '\\n'; }; })();"

/-- What the test printed: the engine's own `print` lines, and on the page realm `$262.out`. -/
def printed (h : HeapOf H) (page : Bool) : Array String :=
  if !page then h.out else
  match evalValue h "$262.out" with
  | ((.ok, .str s), _) => h.out ++ (s.splitOn "\n").toArray
  | _ => h.out

/-- A realm with `$262`: what a `raw` test runs on. -/
def withHost262 (fresh : HeapOf H) (page : Bool) : IO (HeapOf H) :=
  match runScript fresh (host262 ++ (if page then pagePrint else "")) with
  | (.ok, h) => pure h
  | _ => throw (IO.userError "the $262 host object failed")

/-- The heap after `$262` and the default harness, computed once per run. -/
def harnessHeap (root : System.FilePath) (fresh : HeapOf H) (page : Bool) : IO (HeapOf H) := do
  let a ← IO.FS.readFile (root / "harness" / "assert.js")
  let s ← IO.FS.readFile (root / "harness" / "sta.js")
  match runScript (← withHost262 fresh page) (a ++ "\n" ++ s) with
  | (.ok, h) => pure h
  | (o, _) =>
    let why := match o with
      | .syntaxError m => m | .threw _ m => m | .halted w => w | .ok => ""
    throw (IO.userError s!"harness failed: {why}")

/-- A module specifier resolved against the path of the module that names it: `./` and `../`
steps taken from its directory (Test262's module tests name files by relative paths). -/
def resolveSpec (from_ spec : String) : String :=
  let dir := (from_.splitOn "/").dropLast
  let parts := if spec.startsWith "/" then (spec.splitOn "/").drop 1 else dir ++ spec.splitOn "/"
  let norm := parts.foldl (init := ([] : List String)) fun acc p =>
    if p == "." || p == "" then acc
    else if p == ".." then acc.dropLast
    else acc ++ [p]
  (if from_.startsWith "/" then "/" else "") ++ "/".intercalate norm

#guard resolveSpec "/t/a/b.js" "./c_FIXTURE.js" = "/t/a/c_FIXTURE.js"
#guard resolveSpec "/t/a/b.js" "../x/c.js" = "/t/x/c.js"
#guard resolveSpec "/t/a/b.js" "./b.js" = "/t/a/b.js"

/-- At most this many modules in one test's graph (the largest Test262 graph has a few dozen). -/
def maxModules : Nat := 512

/-- Load the module graph of `root` (a file path): each module read and parsed once, each
specifier resolved against the path of the module naming it. An error is `(phase, message)`:
`parse` for the test file itself, `resolution` for a module it loads. -/
def loadGraph (root : String) (rootSrc : String) : IO (Except (String × String) ModGraph) := do
  let rootSyn ← match parseModule rootSrc with
    | .ok s => pure s
    | .error e => return .error ("parse", e)
  let mut urls : Array String := #[root]
  let mut syns : Array ModuleSyntax := #[rootSyn]
  let mut deps : Array (Array (String × Nat)) := #[]
  let mut i := 0
  for _ in [0:maxModules] do
    if h : i < syns.size then
      let syn := syns[i]
      let mut ds : Array (String × Nat) := #[]
      for spec in syn.requests do
        let p := resolveSpec urls[i]! spec
        match urls.findIdx? (· == p) with
        | some k => ds := ds.push (spec, k)
        | none =>
          if !(← System.FilePath.pathExists p) then return .error ("resolution", s!"cannot find module {spec}")
          match parseModule (← IO.FS.readFile p) with
          | .error e => return .error ("resolution", s!"SyntaxError in {spec}: {e}")
          | .ok s =>
            ds := ds.push (spec, urls.size)
            urls := urls.push p
            syns := syns.push s
      deps := deps.push ds
      i := i + 1
  if i < syns.size then return .error ("resolution", s!"more than {maxModules} modules")
  return .ok ((urls.zip syns).zip deps |>.map fun ((u, s), ds) => { ModNode.ofSyntax u s with deps := ds })

/-- `force`: `some true` runs the test as strict code, `some false` as sloppy code, `none` by its
flags (strict only for `onlyStrict`). `module` tests run as a module graph (strict); a
`resolution`-phase negative test passes when loading or linking the graph fails with the named
error type. -/
def runTest (root : System.FilePath) (fresh base : HeapOf H) (page : Bool) (path : System.FilePath)
    (force : Option Bool := none) : IO Verdict := do
  let src ← IO.FS.readFile path
  let m := parseMeta src
  let isModule := m.flags.contains "module"
  let isAsync := m.flags.contains "async"
  let strict := isModule || force.getD (m.flags.contains "onlyStrict")
  let raw := m.flags.contains "raw"
  let mut h ← if raw then withHost262 fresh page else pure base
  if !raw then
    for inc in (if isAsync then ["doneprintHandle.js"] else []) ++ m.includes do
      let p := root / "harness" / inc
      if !(← p.pathExists) then return .skip s!"include {inc} not in the harness"
      match runScript h (← IO.FS.readFile p) with
      | (.ok, h') => h := h'
      | _ => return .fail s!"include {inc} failed"
  let hRun := { h with steps := 20000000 }
  -- (outcome, phase of an error: parse, resolution or runtime, heap after)
  let (o, phase, hOut) ← if isModule then do
      match ← loadGraph path.toString src with
      | .error (ph, e) => pure (Outcome.syntaxError e, ph, hRun)
      | .ok g =>
        match linkError g 0 with
        | some e => pure (Outcome.syntaxError e, "resolution", hRun)
        | none =>
          let ((o, _), h1) := runModuleGraph hRun g 0 #[]
          let ((o2, _), h2) := checkpoint h1
          pure ((match o with | .ok => o2 | _ => o), "runtime", h2)
    else
      let (o, h1) := runScript hRun src strict
      pure (o, (match o with | .syntaxError _ => "parse" | _ => "runtime"), h1)
  if isAsync && m.negPhase.isNone then
    match o with
    | .ok =>
      let out := printed hOut page
      if out.contains "Test262:AsyncTestComplete" then return .pass false
      else return .fail ("async: " ++ (" ".intercalate out.toList).take 160)
    | _ => pure ()
  let errName : Outcome → Option String
    | .syntaxError _ => some "SyntaxError"
    | .threw _ e => some e
    | _ => none
  match m.negPhase, m.negType, o with
  | none, _, .ok => pure (.pass false)
  | none, _, .syntaxError e => pure (.fail s!"{phase}: {e}")
  | none, _, .threw _ e => pure (.fail e)
  | none, _, .halted w => pure (.fail s!"halted: {w}")
  | some ph, some t, o =>
    match errName o with
    | none => pure (.fail s!"expected {t} at {ph}, got {match o with | .halted w => "halted: " ++ w | _ => "no error"}")
    | some e =>
      if ph != phase then pure (.fail s!"expected {t} at {ph}, got {e.take 80} at {phase}")
      else if e.startsWith (t ++ ":") || e == t then pure (.pass true)
      else pure (.fail s!"expected {t}, got {e.take 120}")
  | some _, none, _ => pure (.fail "negative test with no type")

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
`PASS|FAIL|SKIP <path> <sloppy|strict|module> [why]`. A driver that sees the process end before the
last line knows which test it was on. -/
def test262Files (root : System.FilePath) (list : String) (fresh : HeapOf H) (page : Bool := false) : IO Unit := do
  let base ← harnessHeap root fresh page
  let out ← IO.getStdout
  for rel in ((← IO.FS.readFile list).splitOn "\n").filter (· != "") do
    let path := root / rel
    let flags := (parseMeta (← IO.FS.readFile path)).flags
    for strict in modesOf flags do
      let mode := if flags.contains "module" then "module" else if strict then "strict" else "sloppy"
      out.putStrLn s!"START {rel} {mode}"
      out.flush
      let v ← runTest root fresh base page path (some strict)
      let line := match v with
        | .pass _ => s!"PASS {rel} {mode}"
        | .fail why => s!"FAIL {rel} {mode} {(why.replace "\n" " ").take 160}"
        | .skip why => s!"SKIP {rel} {mode} {why}"
      out.putStrLn line
      out.flush

end L4Factoidal.JS.Test262
