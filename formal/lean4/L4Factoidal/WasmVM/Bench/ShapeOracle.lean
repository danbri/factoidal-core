/-
L4Factoidal.WasmVM.Bench.ShapeOracle: HarfBuzz, run in the WasmVM engine, as the
oracle of the Lean shaper (https://github.com/danbri/factoidal/issues/1275 and
https://github.com/danbri/factoidal/issues/1233).

`lake exe wasmvm-bench shape-oracle WASM`, from `formal/lean4`. WASM is the output of
`tools/wasmvm/build-harfbuzz.sh` (not in the repository; see `Bench/HarfBuzz.lean`).

Each case is a sample of the writing-systems page (`labs/demos/foafnaut/pages/
showcase-scripts.html`): its lines and their words, with the Noto font that draws
them (`third_party/fonts/`). Each is shaped twice, with no features and the direction
and script guessed from the text, as `hb-shape` does:

1. by HarfBuzz 15.0.0 compiled to WebAssembly, in WasmVM (`hbw_shape`);
2. by the Lean shaper, `Rendering.SfntShape.shape`.

The two glyph records are compared: glyph id, cluster (UTF-8 byte offset), x and y
advance, x and y offset, all in font units. The report gives, for each script, the
strings whose records are the same, and over the strings with the same number of
glyphs, the glyphs whose ids agree and those whose positions agree too. A string
Lean refuses counts as different. When the native `hb-shape` tool is on the PATH, the
WasmVM result is checked against it too, so a difference is the Lean shaper's.

Exit 0 when every string agrees, 1 otherwise; `--report` always exits 0.
-/
import L4Factoidal.WasmVM.Bench.HarfBuzz
import L4Factoidal.Rendering.SfntShape

namespace L4Factoidal.WasmVM.Bench.ShapeOracle
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Wasi L4Factoidal.Rendering
open L4Factoidal.WasmVM.Bench.HarfBuzz (Glyph alloc put shape native fontDir noExtra)

/-- (script, font file under `third_party/fonts`, text). -/
def cases : List (String × String × String) :=
  let arabic := "noto-sans-arabic/NotoSansArabic-Regular.ttf"
  let hebrew := "noto-sans-hebrew/NotoSansHebrew-Regular.ttf"
  let latin := "noto-sans/NotoSans-Regular.ttf"
  let deva := "noto-sans-devanagari/NotoSansDevanagari-Regular.ttf"
  let beng := "noto-sans-bengali/NotoSansBengali-Regular.ttf"
  (["مرحبا بالعالم", "مرحبا", "بالعالم", "سلام", "السعر ١٢٣٫٤٥ دينار", "السعر", "١٢٣٫٤٥", "دينار",
    "العربية", "لا", "اللّه", "كِتَابٌ", "مُحَمَّد", "شَمْس", "ب‌ب", "ـبـ"].map ("Arabic", arabic, ·)) ++
  (["שלום עולם", "שלום", "עולם", "שלום עולם, זה עמוד בדיקה.", "זה", "עמוד", "בדיקה.",
    "התוכנה", "כתובה", "משנת", "ב-Lean", "(שלום)", "שָׁלוֹם"].map ("Hebrew", hebrew, ·)) ++
  (["office, affluent, flag", "office,", "affluent,", "flag", "fi fl ffi ffl",
    "Café, naïve, façade, coöperate, Ångström, Øresund, Łódź, Škoda, Ţară, Ğ, ẞ",
    "Tiếng Việt: Hà Nội, Đà Nẵng, Huế", "AVATAR Wo", "Hello, world."].map ("Latin", latin, ·)) ++
  (["नमस्ते दुनिया", "नमस्ते", "दुनिया", "क्ष", "त्र", "ज्ञ", "कि", "र्क"].map ("Devanagari", deva, ·)) ++
  (["ওহে বিশ্ব", "ওহে", "বিশ্ব", "কি", "র্ক"].map ("Bengali", beng, ·))

/-- The Lean shaper's record, in HarfBuzz's form. -/
def lean (b : ByteArray) (text : String) : Except String (Array Glyph) := do
  let dir ← FontPolicy.readDirectory b 0
  let face ← SfntMetrics.Face.read b dir
  let s ← SfntShape.shape b dir face text
  return (s.glyphs.zip s.clusterBytes).map fun (g, c) => Glyph.mk g.id c g.advance 0 g.xOffset g.yOffset

structure Tally where
  strings : Nat := 0
  same : Nat := 0
  refused : Nat := 0
  /-- Glyphs of the strings whose glyph counts agree. -/
  glyphs : Nat := 0
  ids : Nat := 0
  positions : Nat := 0
  countDiffers : Nat := 0

def run (path : String) (report : Bool) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let caps : Caps IO := { stdout := some forwardStdout, stderr := some forwardStderr }
  let extraNames := fun (mo nm : String) => mo == "env" && nm == "emscripten_notify_memory_growth"
  let l ← match ← load caps bytes {} extraNames noExtra with
    | .ok l => pure l
    | .error e => IO.println s!"load: {e}"; return 1
  let (l, _) ← l.run caps "_initialize" #[] {} noExtra
  IO.println s!"HarfBuzz in WasmVM: {path}; native hb-shape: {← HarfBuzz.nativeVersion}"
  let mut l := l
  let (l', out) ← alloc l caps (24 * HarfBuzz.outCap)
  l := l'
  let mut fonts : Std.HashMap String (Nat × Nat × ByteArray) := {}
  let mut tallies : Std.HashMap String Tally := {}
  let mut scripts : Array String := #[]
  let mut wasmNative := (0, 0)
  for (script, file, text) in cases do
    unless scripts.contains script do scripts := scripts.push script
    let (fp, flen, fb) ← match fonts[file]? with
      | some f => pure f
      | none => do
        let fb ← IO.FS.readBinFile (fontDir / file)
        let (l2, p) ← alloc l caps fb.size
        l ← put l2 p fb
        fonts := fonts.insert file (p, fb.size, fb)
        pure (p, fb.size, fb)
    let tb := text.toUTF8
    let (l2, tp) ← alloc l caps (tb.size + 1)
    l ← put l2 tp tb
    let (l3, hb) ← shape l caps fp flen tp tb.size out
    l := l3
    if let some nat ← native (fontDir / file) text then
      wasmNative := (wasmNative.1 + (if nat == hb then 1 else 0), wasmNative.2 + 1)
    let mut t := tallies.getD script {}
    t := { t with strings := t.strings + 1 }
    match lean fb text with
    | .error e =>
      t := { t with refused := t.refused + 1 }
      IO.println s!"{script} {repr text}: Lean refused: {e}"
    | .ok ln =>
      if ln == hb then t := { t with same := t.same + 1 }
      else IO.println s!"{script} {repr text}: differs\n  HarfBuzz: {hb.toList.map Glyph.show}\n  Lean:     {ln.toList.map Glyph.show}"
      if ln.size == hb.size then
        let pairs := ln.zip hb
        t := { t with glyphs := t.glyphs + hb.size,
                      ids := t.ids + (pairs.filter fun (a, b) => a.g == b.g).size,
                      positions := t.positions + (pairs.filter fun (a, b) => a == b).size }
      else t := { t with countDiffers := t.countDiffers + 1 }
    tallies := tallies.insert script t
  IO.println s!"WasmVM HarfBuzz against native hb-shape: {wasmNative.1} of {wasmNative.2} strings the same"
  let mut all := true
  for script in scripts do
    let t := tallies.getD script {}
    if t.same != t.strings then all := false
    IO.println s!"{script}: {t.same} of {t.strings} strings the same as HarfBuzz; glyph ids {t.ids} of {t.glyphs}, ids and positions {t.positions} of {t.glyphs} (strings with as many glyphs); {t.countDiffers} with another glyph count, {t.refused} refused"
  return if all || report then 0 else 1

end L4Factoidal.WasmVM.Bench.ShapeOracle
