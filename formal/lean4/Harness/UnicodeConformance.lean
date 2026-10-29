/-
Harness.UnicodeConformance — `l4unicode`: the Lean Unicode algorithms
(`L4Factoidal/Unicode/`, Unicode 18.0.0) over the Unicode conformance
files in `third_party/testing/unicode-18.0.0`
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

  l4unicode norm FILE        NormalizationTest.txt (UAX #15)
  l4unicode grapheme FILE    GraphemeBreakTest.txt (UAX #29)
  l4unicode word FILE        WordBreakTest.txt (UAX #29)
  l4unicode sentence FILE    SentenceBreakTest.txt (UAX #29)
  l4unicode bidi FILE        BidiTest.txt (UAX #9)
  l4unicode bidichar FILE    BidiCharacterTest.txt (UAX #9)
  l4unicode linebreak FILE   LineBreakTest.txt (UAX #14)

Each prints `CMD: N pass, M fail (out of T)` and exits 0 only when M = 0
and T > 0. The test files are read and parsed here, in Lean.
-/
import Harness.Unicode.Normalization
import Harness.Unicode.Segmentation
import Harness.Unicode.Bidi
import Harness.Unicode.LineBreak

namespace Harness.UnicodeConformance

def dispatch (cmd : String) (path : System.FilePath) : IO (Option (Nat × Nat)) := do
  match cmd with
  | "norm" => some <$> Harness.Unicode.Normalization.run cmd path
  | "grapheme" | "word" | "sentence" => some <$> Harness.Unicode.Segmentation.run cmd path
  | "bidi" | "bidichar" => some <$> Harness.Unicode.Bidi.run cmd path
  | "linebreak" => some <$> Harness.Unicode.LineBreak.run cmd path
  | _ => pure none

end Harness.UnicodeConformance

open Harness.UnicodeConformance in
def main (args : List String) : IO UInt32 := do
  match args with
  | [cmd, path] =>
    match ← dispatch cmd path with
    | some (p, f) =>
      IO.println s!"{cmd}: {p} pass, {f} fail (out of {p + f})"
      pure (if f == 0 && p > 0 then 0 else 1)
    | none =>
      IO.eprintln s!"l4unicode: unknown subcommand {cmd}"
      pure 2
  | _ =>
    IO.eprintln "usage: l4unicode norm|grapheme|word|sentence|bidi|bidichar|linebreak FILE"
    pure 2
