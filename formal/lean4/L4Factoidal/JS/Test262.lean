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
-- the run's mode (`leanjs` with `BUBBLEPOP_TIER1=off` runs the reference)
variable [md : Mode]

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

/-- The host-defined `$262` object (Test262 `INTERPRETING.md`, "Host-Defined Functions"):
`global`, and `detachArrayBuffer` by `ArrayBuffer.prototype.transfer` (which detaches its
receiver, §25.1.6.9 ArrayBufferCopyAndDetach), taken before any test code runs; the engine's
built-ins of `hostNatives` are added to it. Not given, so the tests that call them fail:
`agent` (no second thread of execution), `IsHTMLDDA`. -/
def host262 : String :=
  "var $262 = (function () { var t = ArrayBuffer.prototype.transfer; var call = Function.prototype.call; " ++
  "return { global: globalThis, detachArrayBuffer: function (b) { call.call(t, b); return null; } }; })();"

/-- On the page realm `print` is the window's (it prints nothing, HTML §8.8.1): Test262's
`print` (what `$DONE` reports with) then appends to `$262.out`, read back by `printed`. -/
def pagePrint : String :=
  "(function () { var out = ''; Object.defineProperty($262, 'out', { get: function () { return out; } }); " ++
  "globalThis.print = function (m) { out = out + String(m) + '\\n'; }; })();"

/-- The `$262` functions the engine serves: `createRealm` (the `$262` of the next realm this
runner made for the test, `addTestRealms`), `evalScript` (a classic script in the global scope
of the `$262`'s own realm, as `importScripts` runs one) and `gc` (does nothing: the heap has
no collector). -/
def hostNatives : Array (String × Native × Nat) :=
  #[("createRealm", .x .realmTake, 0), ("evalScript", .x .classicScript, 1), ("gc", .x .gcNoop, 0)]

/-- `$262` of the running realm with `hostNatives` added. -/
def install262 (h : HeapOf H) (src : String) : Option (Value × HeapOf H) :=
  match runScript h src with
  | (.ok, h) =>
    match evalValue h "$262" with
    | ((.ok, v), h) => some (v, addNatives h v hostNatives)
    | _ => none
  | _ => none

/-- The most realms one test gets (`addTestRealms`). -/
def maxTestRealms : Nat := 8

/-- How many realms to make for a test: two for each place its source names `createRealm`,
at most `maxTestRealms`; none for the rest, which pay nothing. -/
def realmsWanted (src : String) : Nat :=
  Nat.min maxTestRealms (2 * ((src.splitOn "createRealm").length - 1))

#guard realmsWanted "var x = 1;" = 0
#guard realmsWanted "$262.createRealm(); $262.createRealm()" = 4
#guard realmsWanted (String.join (List.replicate 9 "createRealm ")) = maxTestRealms

/-- Kind: a bound. Says: one test never gets more than `maxTestRealms` realms, however often its
source names `createRealm`; past them `$262.createRealm()` is a TypeError. -/
theorem realmsWanted_le (src : String) : realmsWanted src ≤ maxTestRealms := Nat.min_le_left _ _

/-- `count` new realms (`addRealm`), each with its own `$262` (with `hostNatives`), given out
in order by `$262.createRealm()` of any realm (`ColdHeap.spareRealms`); past them it is a
TypeError, a refusal at a bound the runner chose. The realm that ran before runs again. -/
def addTestRealms (h : HeapOf H) (count : Nat) : HeapOf H := Id.run do
  let mut h := h
  for _ in [0:count] do
    let (k, h1) := addRealm h
    let (v, h2) := inRealmH h1 k fun hk =>
      match install262 hk host262 with
      | some (v, hk) => (v, hk)
      | none => (.undef, hk)
    h := { h2 with realms := h2.realms.modify k (fun r => { r with host := v }),
                   spareRealms := h2.spareRealms.push k }
  return h

/-- What the test printed: the engine's own `print` lines, and on the page realm `$262.out`. -/
def printed (h : HeapOf H) (page : Bool) : Array String :=
  if !page then h.out else
  match evalValue h "$262.out" with
  | ((.ok, .str s), _) => h.out ++ (s.splitOn "\n").toArray
  | _ => h.out

/-- A realm with `$262`: what a `raw` test runs on. -/
def withHost262 (fresh : HeapOf H) (page : Bool) : IO (HeapOf H) :=
  match install262 fresh (host262 ++ (if page then pagePrint else "")) with
  | some (_, h) => pure h
  | none => throw (IO.userError "the $262 host object failed")

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

/-- A JSON module (import attribute `type: "json"`, ECMA-262 §16.2.1.8 and the JSON modules
proposal): a module whose default export is the value `JSON.parse` makes of the file's text. -/
def jsonModuleSource (text : String) : String :=
  let esc := text.foldl (init := "") fun acc c =>
    match c with
    | '\\' => acc ++ "\\\\" | '"' => acc ++ "\\\"" | '\n' => acc ++ "\\n" | '\r' => acc ++ "\\r"
    | '\u2028' => acc ++ "\\u2028" | '\u2029' => acc ++ "\\u2029"
    | c => acc.push c
  "export default JSON.parse(\"" ++ esc ++ "\");"

#guard jsonModuleSource "{\"a\": \"x\\n\"}\n" = "export default JSON.parse(\"{\\\"a\\\": \\\"x\\\\n\\\"}\\n\");"

/-- The module a request names from module `fromUrl` (`splitRequest`): its key in the module map
and its source text. A `type: "json"` module has the key of its path and `#json` (a JSON module
and a JavaScript module of one file are two records) and the source `jsonModuleSource`; a JSON
text that does not parse is a SyntaxError here, when the module is loaded (ParseJSONModule). An
unknown type, or a file that is not there, is an error. -/
def readModule (fromUrl request : String) : IO (Except String (String × String)) := do
  let (spec, ty) := ModuleParse.splitRequest request
  let p := resolveSpec fromUrl spec
  if ty.startsWith "!" then return .error s!"SyntaxError: unsupported import attribute '{(ty.drop 1).toString}'"
  if ty != "" && ty != "json" then return .error s!"unsupported module type '{ty}'"
  if !(← System.FilePath.pathExists p) || (← System.FilePath.isDir p) then
    return .error s!"cannot find module {spec}"
  let text ← try IO.FS.readFile p catch e => return .error s!"cannot read module {spec}: {e}"
  if ty == "json" then
    match jsonParseText text.trimAscii.toString with
    | .error _ => return .error s!"SyntaxError: {spec} is not a JSON text"
    | .ok (_, e) =>
      if e < text.trimAscii.toString.length then return .error s!"SyntaxError: {spec} is not a JSON text"
      return .ok (p ++ "#json", jsonModuleSource text)
  return .ok (p, text)

/-- Load module `root` (a file path, its source `rootSrc`) and the modules it needs into graph
`g`: each module read and parsed once, a module already in `g` not read again (the module map:
one module record for each path), each specifier resolved against the path of the module naming
it. The answer is the root's index and the graph; on an error nothing is added. An error is
`(phase, message)`: `parse` for the root itself, `resolution` for a module it loads. -/
def loadInto (g : ModGraph) (root : String) (rootSrc : String) :
    IO (Except (String × String) (Nat × ModGraph)) := do
  if let some k := g.findIdx? (·.url == root) then return .ok (k, g)
  let rootSyn ← match parseModule rootSrc with
    | .ok s => pure s
    | .error e => return .error ("parse", e)
  let start := g.size
  let mut urls : Array String := (g.map (·.url)).push root
  let mut syns : Array ModuleSyntax := #[rootSyn]
  let mut deps : Array (Array (String × Nat)) := #[]
  let mut i := 0
  for _ in [0:maxModules] do
    if h : i < syns.size then
      let syn := syns[i]
      let mut ds : Array (String × Nat) := #[]
      for spec in syn.requests do
        let (sp, ty) := ModuleParse.splitRequest spec
        let key := resolveSpec urls[start + i]! sp ++ (if ty == "json" then "#json" else "")
        match urls.findIdx? (· == key) with
        | some k => ds := ds.push (spec, k)
        | none =>
          match ← readModule urls[start + i]! spec with
          | .error e => return .error ("resolution", e)
          | .ok (key, text) =>
            match parseModule text with
            | .error e => return .error ("resolution", s!"SyntaxError in {sp}: {e}")
            | .ok s =>
              ds := ds.push (spec, urls.size)
              urls := urls.push key
              syns := syns.push s
      deps := deps.push ds
      i := i + 1
  if i < syns.size then return .error ("resolution", s!"more than {maxModules} modules")
  let fresh := ((urls.extract start urls.size).zip syns).zip deps |>.map fun ((u, s), ds) =>
    { ModNode.ofSyntax u s with deps := ds }
  return .ok (start, g ++ fresh)

/-- The most rounds of `import()` calls one test may make (`serveImports`). -/
def maxImportRounds : Nat := 256

/-- Serve the `import()` calls of a run (HostLoadImportedModule, §16.2.1.10, as a host does after
the script's turn): each specifier resolved against the test's own path, loaded into the test's
module graph (`loadInto`: a module once loaded is the same module for every later import),
linked and evaluated (`runModuleGraph`, which evaluates a module once), and the promise settled
with the module's namespace object or the error (a module that does not parse is a SyntaxError,
one that cannot be found or has an unknown `type` a TypeError); then the jobs run, which may
import again. At most `maxImportRounds` rounds: the calls of later rounds stay pending. A halt
(step budget, heap size) ends it, with the reason; so does an error of the test's own module graph when it goes on after an import (the outcome of the test). -/
def serveImports (path : String) (h : HeapOf H) (g : ModGraph) (lives : ModLives)
    (resume : Option Nat := none) : IO (Option Outcome × HeapOf H) := do
  let mut h := h
  let mut g := g
  let mut lives := lives
  for _ in [0:maxImportRounds] do
    let q := h.importQueue.getD #[]
    if q.isEmpty then break
    h := { h with importQueue := some #[] }
    for (spec, ty, pid) in q do
      let res ← match ← readModule path (ModuleParse.withType spec ty) with
        | .error e => pure (.error ((if e.startsWith "SyntaxError" then "parse" else "type"), e))
        | .ok (key, text) => loadInto g key text
      match res with
      | .error (ph, msg) =>
        let (e, h1) := newError h (if ph == "type" then .type else .syntax) msg
        h := settleImport h1 pid e true
      | .ok (root, g') =>
        g := g'
        let ((o, lv), h1) := runModuleGraph h g root lives
        lives := lv
        h := h1
        match o with
        | .ok =>
          let ((ns, lv), h2) := moduleNamespace h g root lives
          lives := lv
          h := settleImport h2 pid (ns.getD .undef) false
        | .threw v _ => h := settleImport h pid v true
        | .halted w => return (some (.halted w), h)
        | .syntaxError m =>
          let (e, h1) := newError h .syntax m
          h := settleImport h1 pid e true
    let ((o, _), h2) := checkpoint h
    h := h2
    if let .halted w := o then return (some (.halted w), h)
    -- a module test whose graph waits for an import (top-level `await import(...)`): run the
    -- graph again, which goes on from the module that waited
    if let some root := resume then
      let ((o, lv), h3) := runModuleGraph h g root lives
      lives := lv
      h := h3
      match o with
      | .halted w => return (some (.halted w), h)
      | .threw v m => return (some (.threw v m), h)
      | _ => pure ()
  return (none, h)

/-- The step budget of one run of a test. -/
def runSteps : UInt64 := 20000000

/-- The heap size of one run of a test (`HeapOf.full`): half the engine's default
(`ColdHeap.maxObjs`, 2^23 objects, 2 to 4 GiB), so a test that makes objects for ever halts
with the engine's refusal (`heapFullMsg`) at 1 to 2 GiB, under the 3,000 MB at which the
driver (`release-tests/test262.py`) kills the process and loses the rest of its chunk. (A
quarter was too small for the `staging/sm/Date/dst-offset-caching-*` tests.) -/
def runMaxObjs : Nat := 4194304

/-- Kind: a bound. Says: the heap of one test run is half the engine's default size. -/
theorem runMaxObjs_half : runMaxObjs * 2 = 8388608 ∧ runMaxObjs < 8388608 := by decide

#guard (({} : ColdHeap Unit).maxObjs) == 8388608

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
  let wanted := realmsWanted src
  if wanted > 0 then h := addTestRealms h wanted
  let hRun := { h with steps := runSteps, maxObjs := runMaxObjs,
                       importQueue := if (src.splitOn "import").length > 1 then some #[] else none }
  -- (outcome, phase of an error: parse, resolution or runtime, heap after)
  let (o, phase, hOut, g, lives) ← if isModule then do
      match ← loadInto #[] path.toString src with
      | .error (ph, e) => pure (Outcome.syntaxError e, ph, hRun, #[], #[])
      | .ok (_, g) =>
        match linkError g 0 with
        | some e => pure (Outcome.syntaxError e, "resolution", hRun, g, #[])
        | none =>
          let ((o, lives), h1) := runModuleGraph hRun g 0 #[]
          let ((o2, _), h2) := checkpoint h1
          pure ((match o with | .ok => o2 | _ => o), "runtime", h2, g, lives)
    else
      let (o, h1) := runScript hRun src strict
      pure (o, (match o with | .syntaxError _ => "parse" | _ => "runtime"), h1, #[], #[])
  -- the `import()` calls of the run, served after its turn (none: nothing to do)
  let (o, hOut) ← if (hOut.importQueue.getD #[]).isEmpty then pure (o, hOut) else do
      let (halt, h3) ← serveImports path.toString hOut g lives (if isModule then some 0 else none)
      pure ((match o, halt with | .ok, some o' => o' | _, _ => o), h3)
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
