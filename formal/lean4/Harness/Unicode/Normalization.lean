/-
Harness.Unicode.Normalization — `l4unicode norm FILE`: NormalizationTest.txt
(Unicode 18.0.0) against `L4Factoidal.Unicode.Normalization`
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

One case per data line: it passes when all the conformance invariants of the
file header hold (columns c1 to c5 = source; NFC; NFD; NFKC; NFKD):

  c2 == toNFC(c1) == toNFC(c2) == toNFC(c3);  c4 == toNFC(c4) == toNFC(c5)
  c3 == toNFD(c1) == toNFD(c2) == toNFD(c3);  c5 == toNFD(c4) == toNFD(c5)
  c4 == toNFKC(c1..c5);                       c5 == toNFKD(c1..c5)

One more case, `part1-invariance`: every code point not listed in Part 1
as a source normalizes to itself under all four forms.
-/
import L4Factoidal.Unicode.Normalization

namespace Harness.Unicode.Normalization

open L4Factoidal.Unicode.Normalization

private def hexVal (s : String) : Nat :=
  s.foldl (fun n c => n * 16 + (if c.isDigit then c.toNat - 48
    else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else c.toNat - 55)) 0

private def parseCol (s : String) : Array Nat :=
  ((s.splitOn " ").filter (· != "")).foldl (fun a w => a.push (hexVal w)) #[]

private def showCps (xs : Array Nat) : String :=
  " ".intercalate (xs.toList.map fun c => (String.ofList (Nat.toDigits 16 c)).toUpper)

/-- Run the conformance file at `path` for subcommand `cmd`; return
(pass, fail). -/
def run (_cmd : String) (path : System.FilePath) : IO (Nat × Nat) := do
  let text ← IO.FS.readFile path
  let mut pass := 0
  let mut fail := 0
  let mut shown := 0
  let mut inPart1 := false
  let mut listed : Array Bool := Array.replicate 0x110000 false
  for line in text.splitOn "\n" do
    if line.startsWith "@Part" then
      inPart1 := line.startsWith "@Part1"
    else if line.startsWith "#" || line.trimAscii.isEmpty then
      pure ()
    else
      let body := (line.splitOn "#").headD ""
      let cols := (body.splitOn ";").toArray
      if cols.size < 5 then
        fail := fail + 1
      else
        let c1 := parseCol cols[0]!
        let c2 := parseCol cols[1]!
        let c3 := parseCol cols[2]!
        let c4 := parseCol cols[3]!
        let c5 := parseCol cols[4]!
        if inPart1 && c1.size == 1 then listed := listed.set! c1[0]! true
        let ok :=
          c2 == nfcCps c1 && c2 == nfcCps c2 && c2 == nfcCps c3 &&
          c4 == nfcCps c4 && c4 == nfcCps c5 &&
          c3 == nfdCps c1 && c3 == nfdCps c2 && c3 == nfdCps c3 &&
          c5 == nfdCps c4 && c5 == nfdCps c5 &&
          c4 == nfkcCps c1 && c4 == nfkcCps c2 && c4 == nfkcCps c3 &&
          c4 == nfkcCps c4 && c4 == nfkcCps c5 &&
          c5 == nfkdCps c1 && c5 == nfkdCps c2 && c5 == nfkdCps c3 &&
          c5 == nfkdCps c4 && c5 == nfkdCps c5
        if ok then pass := pass + 1
        else
          fail := fail + 1
          if shown < 20 then
            shown := shown + 1
            IO.eprintln s!"FAIL {showCps c1};{showCps c2};{showCps c3};{showCps c4};{showCps c5}: NFC {showCps (nfcCps c1)} NFD {showCps (nfdCps c1)} NFKC {showCps (nfkcCps c1)} NFKD {showCps (nfkdCps c1)}"
  -- Part 1 rule: unlisted code points are stable under all four forms.
  let mut bad := 0
  for cp in [0:0x110000] do
    if !listed[cp]! then
      let x := #[cp]
      if !(nfdCps x == x && nfcCps x == x && nfkdCps x == x && nfkcCps x == x) then
        bad := bad + 1
        if shown < 20 then
          shown := shown + 1
          IO.eprintln s!"FAIL part1-invariance U+{showCps x}"
  if bad == 0 then pass := pass + 1 else fail := fail + 1
  pure (pass, fail)

end Harness.Unicode.Normalization
