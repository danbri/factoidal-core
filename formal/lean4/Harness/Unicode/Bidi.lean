/-
Harness.Unicode.Bidi — conformance-file runner for `l4unicode`
(https://github.com/danbri/factoidal/issues/1167, milestone 4): the Unicode
Bidirectional Algorithm (`L4Factoidal.Unicode.Bidi`, UAX #9 revision 52,
Unicode 18.0.0).

  bidi FILE      BidiTest.txt. `@Levels:` and `@Reorder:` lines set the
                 expected result of the data lines after them; a data line is
                 `classes; bitset` with bit 1 = auto, 2 = LTR, 4 = RTL. Each
                 (data line, direction bit) pair is one case.
  bidichar FILE  BidiCharacterTest.txt: `code points; direction (0 LTR,
                 1 RTL, 2 auto); paragraph level; levels (x = removed by X9);
                 visual order`. One case per line.

A case passes only when the levels and the visual order match (and, for
bidichar, the paragraph level).
-/
import L4Factoidal.Unicode.Bidi
import L4Factoidal.Unicode.BidiTheorems

namespace Harness.Unicode.Bidi

open L4Factoidal.Unicode

private def words (s : String) : List String :=
  (s.split (fun c => c == ' ' || c == '\t')).toList.map (·.toString) |>.filter (· != "")

private def parseLevels (s : String) : Array (Option Nat) :=
  (words s).toArray.map fun w => if w == "x" then none else w.toNat?

private def parseOrder (s : String) : Array Nat :=
  (words s).toArray.filterMap (·.toNat?)

private def hexVal (s : String) : Nat :=
  s.foldl (fun n c =>
    n * 16 + (if c.isDigit then c.toNat - 48
              else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else c.toNat - 55)) 0

private def showLevels (a : Array (Option Nat)) : String :=
  " ".intercalate (a.toList.map fun o => match o with | some l => toString l | none => "x")

private def showOrder (a : Array Nat) : String := " ".intercalate (a.toList.map toString)

def runBidiTest (path : System.FilePath) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile path
  let mut pass := 0
  let mut fail := 0
  let mut shown := 0
  let mut expLv : Array (Option Nat) := #[]
  let mut expOrd : Array Nat := #[]
  let mut lineNo := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    let line := (line.splitOn "#")[0]!.trimAscii.toString
    if line.isEmpty then continue
    if line.startsWith "@Levels:" then
      expLv := parseLevels (line.drop 8).toString
      continue
    if line.startsWith "@Reorder:" then
      expOrd := parseOrder (line.drop 9).toString
      continue
    if line.startsWith "@" then continue
    match line.splitOn ";" with
    | [clsStr, bitsStr] =>
      let names := words clsStr
      let cls := (names.filterMap BidiClass.ofName?).toArray
      if cls.size != names.length then
        fail := fail + 1
        IO.eprintln s!"bidi line {lineNo}: unknown class in {clsStr}"
        continue
      let bits := (hexVal bitsStr.trimAscii.toString)
      for (bit, dir) in [(1, ParaDir.auto), (2, ParaDir.ltr), (4, ParaDir.rtl)] do
        if bits &&& bit != 0 then
          let (lv, _) := levels cls {} dir
          let ord := visualOrder lv
          if lv == expLv && ord == expOrd then pass := pass + 1
          else
            fail := fail + 1
            if shown < 20 then
              shown := shown + 1
              IO.eprintln s!"bidi line {lineNo} [{line}] dir {repr dir}: expected levels [{showLevels expLv}] order [{showOrder expOrd}], got levels [{showLevels lv}] order [{showOrder ord}]"
    | _ =>
      fail := fail + 1
      IO.eprintln s!"bidi line {lineNo}: malformed"
  pure (pass, fail)

def runBidiCharacterTest (path : System.FilePath) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile path
  let mut pass := 0
  let mut fail := 0
  let mut shown := 0
  let mut lineNo := 0
  for line in text.splitOn "\n" do
    lineNo := lineNo + 1
    let line := (line.splitOn "#")[0]!.trimAscii.toString
    if line.isEmpty then continue
    match line.splitOn ";" with
    | [cpStr, dirStr, paraStr, lvStr, ordStr] =>
      let cs := (words cpStr).toArray.map fun w => Char.ofNat (hexVal w)
      let dir := match dirStr.trimAscii.toString with
        | "0" => ParaDir.ltr | "1" => ParaDir.rtl | _ => ParaDir.auto
      let expPara := paraStr.trimAscii.toString.toNat!
      let expLv := parseLevels lvStr
      let expOrd := parseOrder ordStr
      let (lv, para) := levelsOfChars cs dir
      let ord := visualOrder lv
      if lv == expLv && ord == expOrd && para == expPara then pass := pass + 1
      else
        fail := fail + 1
        if shown < 20 then
          shown := shown + 1
          IO.eprintln s!"bidichar line {lineNo} [{line}]: expected para {expPara} levels [{showLevels expLv}] order [{showOrder expOrd}], got para {para} levels [{showLevels lv}] order [{showOrder ord}]"
    | _ =>
      fail := fail + 1
      IO.eprintln s!"bidichar line {lineNo}: malformed"
  pure (pass, fail)

/-- Run the conformance file at `path` for subcommand `cmd`; return
(pass, fail). -/
def run (cmd : String) (path : System.FilePath) : IO (Nat × Nat) :=
  if cmd == "bidichar" then runBidiCharacterTest path else runBidiTest path

end Harness.Unicode.Bidi
