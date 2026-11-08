/-
L4Factoidal.WasmVM.Bench.HarfBuzz: HarfBuzz, compiled to WebAssembly, shaping text
inside the WasmVM engine (https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "HarfBuzz in the VM").

`lake exe wasmvm-bench harfbuzz WASM [N]`, from `formal/lean4`. WASM is the output of
`tools/wasmvm/build-harfbuzz.sh` (not in the repository). The entry point is
`tools/wasmvm/harfbuzz/hb_wasmvm_entry.c`.

1. Load the module with the WASI host (`WasmVM/Wasi.lean`). Capabilities: an empty
   environment (HarfBuzz reads `HB_OPTIONS` with `getenv`), output forwarded, nothing
   else (no clock, no randomness, no files). The one other import,
   `env.emscripten_notify_memory_growth`, does nothing. Run `_initialize`.
2. Copy the two Noto fonts from `third_party/fonts/` into the module's memory
   (`hbw_alloc`), shape each test string with `hbw_shape`, and read the glyph records.
3. Shape the same strings with the native `hb-shape` tool, when it is on the PATH
   (`hb-shape --no-glyph-names --utf8-clusters --output-format=json`), and compare
   glyph ids, clusters, advances and offsets.
4. Time N calls of each string (default 200): shaping calls per second, and the Wasm
   instructions of one call (`invokeSteps`).
-/
import L4Factoidal.WasmVM.WasiIO
import L4Factoidal.WasmVM.Bench.Engine
import L4Factoidal.WasmVM.Bench.Sample
import Lean.Data.Json

namespace L4Factoidal.WasmVM.Bench.HarfBuzz
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Wasi

/-- One glyph: id, cluster (UTF-8 byte offset), x and y advance, x and y offset. -/
structure Glyph where
  g : Int
  cl : Int
  ax : Int
  ay : Int
  dx : Int
  dy : Int
  deriving BEq, Repr

def Glyph.show (x : Glyph) : String := s!"{x.g}@{x.cl}+{x.ax}" ++
  (if x.dx != 0 || x.dy != 0 then s!"<{x.dx},{x.dy}>" else "") ++ (if x.ay != 0 then s!"^{x.ay}" else "")

def fontDir : System.FilePath := "../../third_party/fonts"

/-- (font file, text, what the case is for). -/
def cases : List (String × String × String) :=
  [("noto-sans/NotoSans-Regular.ttf", "office", "Latin, ffi ligature"),
   ("noto-sans/NotoSans-Regular.ttf", "AVATAR Wo", "Latin, kerning"),
   ("noto-sans/NotoSans-Regular.ttf", "éạ̈", "combining marks: composed, and a mark attached"),
   ("noto-sans/NotoSans-Regular.ttf", "x́̂̃", "stacked marks on a base with no precomposed form"),
   ("noto-sans-armenian/NotoSansArmenian-Regular.ttf", "Բարև ձեզ", "Armenian"),
   ("noto-sans-armenian/NotoSansArmenian-Regular.ttf", "ﬓ մն", "Armenian ligature U+FB13 and its letters")]

def i32At (b : ByteArray) (i : Nat) : Int :=
  let u := u32At b i
  if u ≥ 2147483648 then (u : Int) - 4294967296 else u

def noExtra : String → String → Array Value → Store → IO (Store × HostResult) :=
  fun _ _ _ st => pure (st, .values #[])

/-- `hbw_alloc n`. -/
def alloc (l : Loaded) (caps : Caps IO) (n : Nat) : IO (Loaded × Nat) := do
  let (l, o) ← l.run caps "hbw_alloc" #[.i32 n.toUInt32] {} noExtra
  match o with
  | .values #[.i32 p] => if p == 0 then throw (IO.userError "hbw_alloc gave 0") else return (l, p.toNat)
  | o => throw (IO.userError s!"hbw_alloc: {o.describe}")

def put (l : Loaded) (off : Nat) (b : ByteArray) : IO Loaded :=
  match l.store.writeMem l.mem off b with
  | .ok st => pure { l with store := st }
  | .error e => throw (IO.userError e)

def outCap : Nat := 512

/-- Shape with the module: font at `font` (`flen` bytes), text written at `textPtr`. -/
def shape (l : Loaded) (caps : Caps IO) (font flen textPtr tlen out : Nat) : IO (Loaded × Array Glyph) := do
  let args := #[.i32 font.toUInt32, .i32 flen.toUInt32, .i32 textPtr.toUInt32, .i32 tlen.toUInt32,
    .i32 out.toUInt32, .i32 outCap.toUInt32]
  let (l, o) ← if ← Sample.enabled then do
      let ⟨st, inst, mem, bs⟩ := l
      let some (.func fa) := st.export? inst "hbw_shape" | throw (IO.userError "no hbw_shape")
      let (st, o, _) ← Sample.runIO st fa args { fuel := 100000000000 } (host caps mem bs noExtra)
      pure (⟨st, inst, mem, bs⟩, o)
    else l.run caps "hbw_shape" args { fuel := 100000000000 } noExtra
  match o with
  | .values #[.i32 n] =>
    if n.toNat > outCap then throw (IO.userError s!"hbw_shape gave {i32At (le32 n.toNat) 0}")
    let b ← match l.store.readMem l.mem out (24 * n.toNat) with
      | .ok b => pure b | .error e => throw (IO.userError e)
    let gs := (Array.range n.toNat).map fun k =>
      let r := 24 * k
      Glyph.mk (i32At b r) (i32At b (r + 4)) (i32At b (r + 8)) (i32At b (r + 12))
        (i32At b (r + 16)) (i32At b (r + 20))
    return (l, gs)
  | o => throw (IO.userError s!"hbw_shape: {o.describe}")

/-- The native `hb-shape` result, or `none` when the tool is not there. -/
def native (font : System.FilePath) (text : String) : IO (Option (Array Glyph)) := do
  let r ← try
      IO.Process.output {
        cmd := "hb-shape",
        args := #["--no-glyph-names", "--utf8-clusters", "--output-format=json", font.toString, text] }
    catch _ => return none
  if r.exitCode != 0 then return none
  let line := (r.stdout.splitOn "\n").head!
  match Lean.Json.parse line with
  | .error _ => return none
  | .ok (.arr xs) =>
    let get := fun (j : Lean.Json) (k : String) => (j.getObjValAs? Int k).toOption.getD 0
    return some (xs.map fun j =>
      Glyph.mk (get j "g") (get j "cl") (get j "ax") (get j "ay") (get j "dx") (get j "dy"))
  | .ok _ => return none

def nativeVersion : IO String := do
  try
    let r ← IO.Process.output { cmd := "hb-shape", args := #["--version"] }
    return (r.stdout.splitOn "\n").head!
  catch _ => return "not installed"

def run (path : String) (n : Nat) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let caps : Caps IO := { stdout := some forwardStdout, stderr := some forwardStderr }
  let extraNames := fun (mo nm : String) => mo == "env" && nm == "emscripten_notify_memory_growth"
  let ((r : Except String Loaded), ns) ← do
    let t0 ← IO.monoNanosNow
    let r ← load caps bytes {} extraNames noExtra
    let t1 ← IO.monoNanosNow
    pure (r, t1 - t0)
  let l ← match r with
    | .ok l => pure l
    | .error e => IO.println s!"load: {e}"; return 1
  IO.println s!"module: {bytes.size} bytes; decode, validate, link and instantiate: {ns / 1000000} ms"
  IO.println s!"imports: {l.bindings.toList.map fun b => match b with | .wasi f => f.name | .extra m x => s!"{m}.{x}"}"
  let (l, o) ← l.run caps "_initialize" #[] {} noExtra
  IO.println s!"_initialize: {o.describe}"
  IO.println s!"native: {← nativeVersion}"
  let mut l := l
  let mut fonts : Std.HashMap String (Nat × Nat) := {}
  let mut agree := 0
  let mut differ := 0
  let mut noNative := 0
  let out ← do let (l', p) ← alloc l caps (24 * outCap); l := l'; pure p
  for (file, text, what) in cases do
    let (fp, flen) ← match fonts[file]? with
      | some f => pure f
      | none => do
        let fb ← IO.FS.readBinFile (fontDir / file)
        let (l', p) ← alloc l caps fb.size
        l ← put l' p fb
        fonts := fonts.insert file (p, fb.size)
        pure (p, fb.size)
    let tb := text.toUTF8
    let (l', tp) ← alloc l caps (tb.size + 1)
    l ← put l' tp tb
    let (l', gs) ← shape l caps fp flen tp tb.size out
    l := l'
    -- One call's instructions.
    let steps := match l.store.export? l.inst "hbw_shape" with
      | some (.func fa) =>
        let (_, o, s) := invokeSteps l.store fa #[.i32 fp.toUInt32, .i32 flen.toUInt32, .i32 tp.toUInt32,
          .i32 tb.size.toUInt32, .i32 out.toUInt32, .i32 outCap.toUInt32] { fuel := 100000000000 }
        match o with | .values _ => some s | _ => none
      | _ => none
    -- n calls, timed.
    let t0 ← IO.monoNanosNow
    let mut lt := l
    for _ in [0:n] do
      let (l2, _) ← shape lt caps fp flen tp tb.size out
      lt := l2
    let t1 ← IO.monoNanosNow
    l := lt
    let perSec := if t1 == t0 then 0 else n * 1000000000 / (t1 - t0)
    let mips := match steps with
      | some s => if t1 == t0 then 0 else s * n * 1000 / (t1 - t0)
      | none => 0
    let nat ← native (fontDir / file) text
    let verdict := match nat with
      | none => "no native result"
      | some ns => if ns == gs then "same as native hb-shape" else s!"DIFFERS from native hb-shape: {ns.toList.map Glyph.show}"
    match nat with
    | none => noNative := noNative + 1
    | some ns => if ns == gs then agree := agree + 1 else differ := differ + 1
    IO.println s!"{what}: {repr text} ({file.splitOn "/" |>.getLast!})"
    IO.println s!"  WasmVM: {gs.toList.map Glyph.show}"
    IO.println s!"  {verdict}"
    IO.println s!"  {perSec} calls per second ({n} calls, {(t1 - t0) / 1000000} ms); {steps.map toString |>.getD "?"} instructions per call, {mips} million instructions per second"
  IO.println s!"compared with native hb-shape: {agree} same, {differ} differ, {noNative} not compared"
  Sample.report "HarfBuzz hbw_shape, all cases"
  return if differ == 0 then 0 else 1

end L4Factoidal.WasmVM.Bench.HarfBuzz
