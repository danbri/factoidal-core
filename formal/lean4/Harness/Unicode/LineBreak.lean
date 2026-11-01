/-
Harness.Unicode.LineBreak — conformance-file runner for `l4unicode linebreak`
(https://github.com/danbri/factoidal/issues/1167, milestone 4): UAX #14
revision 57 over `LineBreakTest.txt` of Unicode 18.0.0. A data line is
`× 0023 × 0308 ÷ 0020 ÷ # comment`; ÷ marks a break opportunity and × none.
One line is one case; it passes when `L4Factoidal.Unicode.LineBreak.breaks`
equals the positions of the ÷ marks after the first character.
-/
import L4Factoidal.Unicode.LineBreak

namespace Harness.Unicode.LineBreak
open L4Factoidal.Unicode

private def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else c.toNat - 55)) 0

/-- Parse one data line into its characters and expected break positions. -/
def parseLine (line : String) : Array Char × Array Nat := Id.run do
  let body := (line.splitOn "#").headD ""
  let mut cs : Array Char := #[]
  let mut exp : Array Nat := #[]
  for tok in body.split (fun c => c == ' ' || c == '\t') do
    if tok == "÷" then
      if cs.size > 0 then exp := exp.push cs.size
    else if tok == "×" || tok == "" then pure ()
    else cs := cs.push (Char.ofNat (hexVal tok.toString))
  return (cs, exp)

/-- Run the conformance file at `path` for subcommand `cmd`; return
(pass, fail). -/
def run (_cmd : String) (path : System.FilePath) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile path
  let mut pass := 0
  let mut fail := 0
  for line in text.splitOn "\n" do
    if line.trimAscii.isEmpty || line.startsWith "#" then continue
    let (cs, exp) := parseLine line
    let got := LineBreak.breaks cs
    if got == exp then pass := pass + 1
    else
      fail := fail + 1
      if fail ≤ 20 then
        IO.eprintln s!"linebreak FAIL: {line}\n  expected {exp}\n  actual   {got}"
  return (pass, fail)

end Harness.Unicode.LineBreak
