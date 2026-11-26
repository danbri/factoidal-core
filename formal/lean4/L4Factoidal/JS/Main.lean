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
- `leanjs numfmt-diff N SEED [OUT]`, `leanjs numfmt-bench`: Number::toString by Ryū against the
  exact reference (`numToStringRef`), and the time of each (issue 1076).

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

/-! ## Number::toString: differential test and timing (issue 1076) -/

def xorshift (s : UInt64) : UInt64 :=
  let s := s ^^^ (s <<< 13)
  let s := s ^^^ (s >>> 7)
  s ^^^ (s <<< 17)

/-- The doubles of the differential test, by bits: `n` random bit patterns (finite), every power
of two and its two neighbours, the decimal powers `1e-325` to `1e309` and their neighbours,
subnormals, integers from 2^53 up and fractions `i / 7`, `i / 10`, `i / 1000`. -/
def numfmtInputs (n : Nat) (seed : UInt64) : Array UInt64 := Id.run do
  let mut out : Array UInt64 := Array.mkEmpty (n + 20000)
  let mut s := if seed == 0 then 88172645463325252 else seed
  for _ in [0:n] do
    s := xorshift s
    if (s >>> 52) &&& 0x7FF != 0x7FF then out := out.push s
  for e in [0:2047] do
    let b := (UInt64.ofNat e) <<< 52
    out := out.push b |>.push (b + 1) |>.push (b - 1) |>.push (b + 0xFFFFFFFFFFFFF)
  for k in [0:635] do
    let x := strToNumber s!"1e{(k : Int) - 325}"
    let b := x.toBits
    out := out.push b |>.push (b + 1) |>.push (b - 1)
    let y := strToNumber s!"5e{(k : Int) - 325}"
    out := out.push y.toBits |>.push (y.toBits + 1) |>.push (y.toBits - 1)
  for i in [1:3000] do
    out := out.push (UInt64.ofNat i) |>.push (0xFFFFFFFFFFFFF - UInt64.ofNat i)
  for i in [0:3000] do
    out := out.push (9007199254740992.0 + Float.ofNat i * 2.0).toBits
    out := out.push (Float.ofNat i / 7.0).toBits |>.push (Float.ofNat i / 10.0).toBits
      |>.push (Float.ofNat i / 1000.0).toBits
  return out.filter fun b => (b >>> 52) &&& 0x7FF != 0x7FF

/-- `leanjs numfmt-diff N SEED [OUT]`: `numToString` against `numToStringRef` on both signs of
each double of `numfmtInputs`; prints the first differences and the counts; with `OUT`, writes
`HEXBITS TEXT` lines for a check against another engine (`tools/ryu-differential.sh`). Exit 1
on any difference. -/
def numfmtDiff (n : Nat) (seed : UInt64) (out? : Option String) : IO UInt32 := do
  let xs := numfmtInputs n seed
  let mut bad := 0
  let mut refLong := 0
  let mut lines : Array String := #[]
  for b in xs do
    for x in [Float.ofBits b, Float.ofBits (b ^^^ 0x8000000000000000)] do
      let f := numToString x
      if out?.isSome then lines := lines.push s!"{(Nat.toDigits 16 x.toBits.toNat).asString} {f}"
      let r := numToStringRef x
      if f != r then
        -- `XPath4.shortestDigits` reads back only the nearest decimal of each length, so where
        -- the interval is narrower below than above (a power of two) it can miss the shortest
        -- text and give one digit more. Counted apart when the fast text is shorter and reads
        -- back as `x`.
        if f.length < r.length && (strToNumber f).toBits == x.toBits && b &&& 0xFFFFFFFFFFFFF == 0 then
          refLong := refLong + 1
        else
          bad := bad + 1
          if bad ≤ 20 then IO.println s!"DIFF bits {x.toBits} fast {f} ref {r}"
  IO.println s!"numfmt-diff: {xs.size * 2} doubles, {bad} differences; {refLong} powers of two where the reference is one digit longer than the shortest"
  -- toFixed, toPrecision, toExponential: the fast paths against the exact path, on every 16th
  -- double above and on `n / 8` random doubles from 2^-24 to 2^40 (both signs)
  let mut ys : Array Float := #[]
  for i in [0:xs.size / 16] do ys := ys.push (Float.ofBits xs[i * 16]!)
  let mut s := seed + 1
  for _ in [0:n / 8] do
    s := xorshift s
    let e : UInt64 := (1003 : UInt64) + (s >>> (52 : UInt64)) % (64 : UInt64)
    ys := ys.push (Float.ofBits ((s &&& (0x800FFFFFFFFFFFFF : UInt64)) ||| (e <<< (52 : UInt64))))
  let mut badF := 0
  for x in ys do
    let (sg, num, den) := NumFmt.ofFloat x
    let mut ds : Array (String × String × String) := #[]
    if x.abs < tenPow21 then
      for f in [0, 1, 2, 3, 5, 10, 19, 20] do
        ds := ds.push (s!"toFixed({f})", NumFmt.fixedOf x f, NumFmt.fixed sg num den f)
    for p in [1, 2, 4, 7, 12, 17, 19, 21] do
      ds := ds.push (s!"toPrecision({p})", NumFmt.precisionOf x p, NumFmt.precision sg num den p)
    for f in [0, 1, 3, 6, 16, 18, 20] do
      ds := ds.push (s!"toExponential({f})", NumFmt.expoOf x f, NumFmt.expo sg num den f)
    ds := ds.push ("toExponential()", NumFmt.expoShortest x,
      NumFmt.expo sg num den (if num == 0 then 0 else NumFmt.shortestFracRef x))
    for (what, a, b) in ds do
      if a != b then
        badF := badF + 1
        if badF ≤ 20 then IO.println s!"DIFF bits {x.toBits} {what} fast {a} exact {b}"
  IO.println s!"numfmt-diff: {ys.size} doubles through toFixed, toPrecision, toExponential, {badF} differences"
  bad := bad + badF
  if let some o := out? then IO.FS.writeFile o ("\n".intercalate lines.toList ++ "\n")
  return if bad == 0 then 0 else 1

/-- `leanjs numfmt-bench`: nanoseconds per conversion of `numToString` and `numToStringRef` on
the fractions `i / 7`. -/
def numfmtBench (n : Nat) : IO Unit := do
  let xs := (Array.range n).map fun i => Float.ofNat (i + 1) / 7.0
  let t0 ← IO.monoNanosNow
  let mut len := 0
  for x in xs do len := len + (numToString x).length
  let t1 ← IO.monoNanosNow
  let m := Nat.min n 20000
  for x in xs[0:m] do len := len + (numToStringRef x).length
  let t2 ← IO.monoNanosNow
  let t3 ← IO.monoNanosNow
  for x in xs do len := len + (NumFmt.fixedOf x 2).length + (NumFmt.precisionOf x 4).length
  let t4 ← IO.monoNanosNow
  IO.println s!"numToString: {(t1 - t0) / n} ns per conversion; numToStringRef: {(t2 - t1) / m} ns per conversion; toFixed(2) and toPrecision(4) together: {(t4 - t3) / n} ns ({len})"

def main (args : List String) : IO UInt32 := do
  -- `BUBBLEPOP_VM=off`: the register machine is off for the run (the heap's `useVm`)
  let vm := (← IO.getEnv "BUBBLEPOP_VM") != some "off"
  let fresh : Heap := { freshHeap with useVm := vm }
  -- `BUBBLEPOP_TIER1=off`: the reference run, the evaluator with tier 1 off (`Mode.ref`)
  -- `BUBBLEPOP_TIER2=off`: the inline caches for property reads are filled and not used
  let md : Mode := ⟨(← IO.getEnv "BUBBLEPOP_TIER1") != some "off", (← IO.getEnv "BUBBLEPOP_TIER2") != some "off"⟩
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
  | ["numfmt-diff", n, seed] => numfmtDiff n.toNat! seed.toNat!.toUInt64 none
  | ["numfmt-diff", n, seed, out] => numfmtDiff n.toNat! seed.toNat!.toUInt64 (some out)
  | ["numfmt-bench"] => numfmtBench 1000000; pure 0
  | ["bench"] =>
    timeIt "fib(24)" fibSrc
    timeIt "loop" loopSrc
    pure 0
  | _ =>
    IO.eprintln "usage: [BUBBLEPOP_VM=off] [BUBBLEPOP_TIER1=off] [BUBBLEPOP_TIER2=off] leanjs run FILE | eval SRC | test262 ROOT DIR... [--list OUT] | test262-files ROOT LIST | bench | numfmt-diff N SEED [OUT] | numfmt-bench"
    pure 64

end L4Factoidal.JS.Main

def main (args : List String) : IO UInt32 := L4Factoidal.JS.Main.main args
