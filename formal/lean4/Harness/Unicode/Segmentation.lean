/-
Harness.Unicode.Segmentation — `l4unicode grapheme|word|sentence FILE`:
GraphemeBreakTest.txt, WordBreakTest.txt, SentenceBreakTest.txt (Unicode
18.0.0) against `L4Factoidal.Unicode.Segmentation`
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

A data line is `÷ 0020 × 0308 ÷ 0020 ÷ # comment`: `÷` is a boundary and `×`
is not, between code points given in hexadecimal. One case per line; it
passes when the computed boundary positions are exactly the `÷` positions.
-/
import L4Factoidal.Unicode.Segmentation
import L4Factoidal.Unicode.SegmentationTheorems

namespace Harness.Unicode.Segmentation

open L4Factoidal.Unicode.Segmentation

private def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else c.toNat - 55)) 0

/-- Text and expected boundary positions of one data line. -/
private def parseLine (body : String) : Array Char × Array Nat := Id.run do
  let mut cs : Array Char := #[]
  let mut bs : Array Nat := #[]
  for tok in (body.splitOn " ").filter (· != "") do
    if tok == "÷" then bs := bs.push cs.size
    else if tok == "×" then pure ()
    else cs := cs.push (Char.ofNat (hexVal tok))
  return (cs, bs)

private def showCps (xs : Array Char) : String :=
  " ".intercalate (xs.toList.map fun c => (String.ofList (Nat.toDigits 16 c.toNat)).toUpper)

/-- Run the conformance file at `path` for subcommand `cmd`; return
(pass, fail). -/
def run (cmd : String) (path : System.FilePath) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile path
  let f : Array Char → Array Nat :=
    if cmd == "grapheme" then graphemeBreaks
    else if cmd == "word" then wordBreaks
    else sentenceBreaks
  let mut pass := 0
  let mut fail := 0
  for line in text.splitOn "\n" do
    if line.startsWith "#" || line.trimAscii.isEmpty then pure ()
    else
      let body := ((line.splitOn "#").headD "").map (fun c => if c == (Char.ofNat 9) then (Char.ofNat 32) else c)
      let (cs, expected) := parseLine body
      let got := f cs
      if got == expected then pass := pass + 1
      else
        fail := fail + 1
        if fail ≤ 20 then
          IO.eprintln s!"FAIL {showCps cs}: expected {expected} got {got}  # {line}"
  pure (pass, fail)

end Harness.Unicode.Segmentation
