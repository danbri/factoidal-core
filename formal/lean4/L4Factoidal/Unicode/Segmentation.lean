/-
L4Factoidal.Unicode.Segmentation — Unicode Text Segmentation (UAX #29
revision 49, Unicode 18.0.0): extended grapheme cluster boundaries (§3.1.1,
rules GB1 to GB999 including GB9c, the Indic conjunct rule), word
boundaries (§4.1.1, WB1 to WB999) and sentence boundaries (§5.1.1, SB1 to
SB998)
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

`graphemeBreaks`, `wordBreaks` and `sentenceBreaks` take the text as an
`Array Char` and return the boundary positions as indices in code points,
including 0 and the length for non-empty text (the form of the lists in the
conformance files); empty text has no boundary. `graphemes`, `words` and
`sentences` cut a `String` at them.

The word and sentence rules ignore Extend, Format and (words) ZWJ
characters (WB4, SB5), except after the start of text, CR, LF, Newline and
Sep. Section 6.2 of the annex reads that as a rewrite of the text; here the
ignored characters are removed from a compact copy of the class sequence
(`absorbed`), the rules run on the compact copy with look-ahead and
look-behind by index, and a boundary is reported at the original index of
the right-hand character. Rules that the annex states over the literal
neighbours (WB3c, WB3d) read the original classes.

All loops are `for` loops over indices; the state that a rule needs about
the text on its left (regional indicator parity, emoji sequence, conjunct
linker, sentence terminator phase) is carried forward, so the work is linear
in the length of the text.
-/
import L4Factoidal.Unicode.RangeTable
import L4Factoidal.Unicode.SegmentData

namespace L4Factoidal.Unicode.Segmentation

open SegmentData

def gcbTable : RangeTable := RangeTable.ofText gcbText
def wbTable : RangeTable := RangeTable.ofText wbText
def sbTable : RangeTable := RangeTable.ofText sbText
def incbTable : RangeTable := RangeTable.ofText incbText
def extPictTable : RangeTable := RangeTable.ofText extPictText

/-! ## Cutting a text at boundaries -/

/-- Piece sizes from boundary positions: consecutive differences. -/
def sizesOfBreaks (bs : Array Nat) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [1:bs.size] do
    out := out.push (bs[i]! - bs[i-1]!)
  return out.toList

/-- Cut `xs` into pieces of the given sizes (tail call with accumulator);
what is left after the last size is one more piece when it is not empty. -/
def cutSizesAux {α : Type} : List Nat → List α → List (List α) → List (List α)
  | [], xs, acc => if xs.isEmpty then acc.reverse else (xs :: acc).reverse
  | s :: ss, xs, acc => cutSizesAux ss (xs.drop s) (xs.take s :: acc)

def cutSizes {α : Type} (ss : List Nat) (xs : List α) : List (List α) :=
  cutSizesAux ss xs []

/-- Cut `xs` at the boundary positions `bs`. -/
def cutAt {α : Type} (xs : List α) (bs : Array Nat) : List (List α) :=
  cutSizes (sizesOfBreaks bs) xs

/-! ## Grapheme clusters -/

structure GState where
  ri : Nat := 0       -- regional indicators immediately before
  ep : UInt8 := 0     -- 1: Extended_Pictographic Extend*, 2: ... ZWJ
  lk : Bool := false  -- InCB=Linker InCB=Extend*

@[inline] def GState.step (s : GState) (g incb ext : UInt8) : GState :=
  { ri := if g == GCB.Regional_Indicator then s.ri + 1 else 0
    ep := if ext == 1 then 1
          else if s.ep == 1 && g == GCB.Extend then 1
          else if s.ep == 1 && g == GCB.ZWJ then 2
          else 0
    lk := if incb == InCB.Linker then true
          else if incb == InCB.Extend then s.lk
          else false }

/-- Is there a boundary between a character with Grapheme_Cluster_Break `p`
and the next one (`q`, with InCB `incb` and Extended_Pictographic `ext`),
given the state `s` after `p`? Rules GB3 to GB999. -/
def graphemeBreakBetween (s : GState) (p q incb ext : UInt8) : Bool :=
  let ctl := fun (x : UInt8) => x == GCB.Control || x == GCB.CR || x == GCB.LF
  if p == GCB.CR && q == GCB.LF then false
  else if ctl p then true
  else if ctl q then true
  else if p == GCB.L && (q == GCB.L || q == GCB.V || q == GCB.LV || q == GCB.LVT) then false
  else if (p == GCB.LV || p == GCB.V) && (q == GCB.V || q == GCB.T) then false
  else if (p == GCB.LVT || p == GCB.T) && q == GCB.T then false
  else if q == GCB.Extend || q == GCB.ZWJ then false
  else if q == GCB.SpacingMark then false
  else if p == GCB.Prepend then false
  else if s.lk && incb == InCB.Consonant then false
  else if s.ep == 2 && ext == 1 then false
  else if q == GCB.Regional_Indicator && s.ri % 2 == 1 then false
  else true

/-- Extended grapheme cluster boundaries (GB1 to GB999). -/
def graphemeBreaks (xs : Array Char) : Array Nat := Id.run do
  let n := xs.size
  if n == 0 then return #[]
  let g := xs.map gcbTable.getChar
  let ib := xs.map incbTable.getChar
  let ep := xs.map extPictTable.getChar
  let mut out : Array Nat := #[0]
  let mut st : GState := GState.step {} g[0]! ib[0]! ep[0]!
  for i in [1:n] do
    if graphemeBreakBetween st g[i-1]! g[i]! ib[i]! ep[i]! then
      out := out.push i
    st := st.step g[i]! ib[i]! ep[i]!
  return out.push n

/-! ## Compacting ignorable characters (WB4, SB5) -/

/-- The indices that survive the removal of the ignorable characters: index
`i` is absorbed into its left neighbour when it is ignorable and the
character before it is not a line or paragraph separator. -/
def keptIndices (cls : Array UInt8) (ign nl : UInt8 → Bool) : Array Nat := Id.run do
  let mut out : Array Nat := #[]
  for i in [0:cls.size] do
    if !(i > 0 && ign cls[i]! && !nl cls[i-1]!) then out := out.push i
  return out

/-! ## Words -/

/-- Word boundaries (WB1 to WB999). -/
def wordBreaks (xs : Array Char) : Array Nat := Id.run do
  let n := xs.size
  if n == 0 then return #[]
  let w := xs.map wbTable.getChar
  let ep := xs.map extPictTable.getChar
  let idx := keptIndices w
    (fun x => x == WB.Extend || x == WB.Format || x == WB.ZWJ)
    (fun x => x == WB.CR || x == WB.LF || x == WB.Newline)
  let m := idx.size
  let c := idx.map (fun i => w[i]!)
  let ahl := fun (x : UInt8) => x == WB.ALetter || x == WB.Hebrew_Letter
  let midq := fun (x : UInt8) => x == WB.MidNumLet || x == WB.Single_Quote
  let nlx := fun (x : UInt8) => x == WB.CR || x == WB.LF || x == WB.Newline
  let mut out : Array Nat := #[0]
  let mut riRun : Nat := if c[0]! == WB.Regional_Indicator then 1 else 0
  for k in [1:m] do
    let p := c[k-1]!
    let q := c[k]!
    let pp := if k ≥ 2 then c[k-2]! else WB.Other
    let nn := if k + 1 < m then c[k+1]! else WB.Other
    let i := idx[k]!
    let brk :=
      if p == WB.CR && q == WB.LF then false
      else if nlx p || nlx q then true
      else if w[i-1]! == WB.ZWJ && ep[i]! == 1 then false
      else if w[i-1]! == WB.WSegSpace && q == WB.WSegSpace then false
      else if ahl p && ahl q then false
      else if ahl p && (q == WB.MidLetter || midq q) && ahl nn then false
      else if ahl pp && (p == WB.MidLetter || midq p) && ahl q then false
      else if p == WB.Hebrew_Letter && q == WB.Single_Quote then false
      else if p == WB.Hebrew_Letter && q == WB.Double_Quote && nn == WB.Hebrew_Letter then false
      else if pp == WB.Hebrew_Letter && p == WB.Double_Quote && q == WB.Hebrew_Letter then false
      else if p == WB.Numeric && q == WB.Numeric then false
      else if ahl p && q == WB.Numeric then false
      else if p == WB.Numeric && ahl q then false
      else if pp == WB.Numeric && (p == WB.MidNum || midq p) && q == WB.Numeric then false
      else if p == WB.Numeric && (q == WB.MidNum || midq q) && nn == WB.Numeric then false
      else if p == WB.Katakana && q == WB.Katakana then false
      else if (ahl p || p == WB.Numeric || p == WB.Katakana || p == WB.ExtendNumLet)
              && q == WB.ExtendNumLet then false
      else if p == WB.ExtendNumLet && (ahl q || q == WB.Numeric || q == WB.Katakana) then false
      else if p == WB.Regional_Indicator && q == WB.Regional_Indicator && riRun % 2 == 1 then false
      else true
    if brk then out := out.push i
    riRun := if q == WB.Regional_Indicator then riRun + 1 else 0
  return out.push n

/-! ## Sentences -/

/-- Sentence boundaries (SB1 to SB998). -/
def sentenceBreaks (xs : Array Char) : Array Nat := Id.run do
  let n := xs.size
  if n == 0 then return #[]
  let s := xs.map sbTable.getChar
  let paraSep := fun (x : UInt8) => x == SB.Sep || x == SB.CR || x == SB.LF
  let idx := keptIndices s (fun x => x == SB.Extend || x == SB.Format) paraSep
  let m := idx.size
  let c := idx.map (fun i => s[i]!)
  let saterm := fun (x : UInt8) => x == SB.ATerm || x == SB.STerm
  -- lowerAhead[k]: the first character at or after k that is OLetter, Upper,
  -- Lower, ParaSep or SATerm is Lower (SB8).
  let mut lowerAhead : Array Bool := Array.replicate (m + 1) false
  for r in [0:m] do
    let k := m - 1 - r
    let x := c[k]!
    lowerAhead := lowerAhead.set! k
      (if x == SB.Lower then true
       else if x == SB.OLetter || x == SB.Upper || paraSep x || saterm x then false
       else lowerAhead[k+1]!)
  let mut out : Array Nat := #[0]
  -- valid: the text before ends in SATerm Close* Sp*; phase 0: Close* only
  let mut valid := false
  let mut phase0 := true
  let mut aterm := false
  let step := fun (valid phase0 aterm : Bool) (x : UInt8) =>
    if saterm x then (true, true, x == SB.ATerm)
    else if valid && phase0 && x == SB.Close then (true, true, aterm)
    else if valid && x == SB.Sp then (true, false, aterm)
    else (false, true, false)
  (valid, phase0, aterm) := step valid phase0 aterm c[0]!
  for k in [1:m] do
    let p := c[k-1]!
    let q := c[k]!
    let brk :=
      if p == SB.CR && q == SB.LF then false
      else if paraSep p then true
      else if p == SB.ATerm && q == SB.Numeric then false
      else if p == SB.ATerm && k ≥ 2 && (c[k-2]! == SB.Upper || c[k-2]! == SB.Lower)
              && q == SB.Upper then false
      else if valid && aterm && lowerAhead[k]! then false
      else if valid && (q == SB.SContinue || saterm q) then false
      else if valid && phase0 && (q == SB.Close || q == SB.Sp || paraSep q) then false
      else if valid && (q == SB.Sp || paraSep q) then false
      else if valid then true
      else false
    if brk then out := out.push idx[k]!
    (valid, phase0, aterm) := step valid phase0 aterm q
  return out.push n

/-! ## Cutting strings -/

def segmentsBy (f : Array Char → Array Nat) (s : String) : List String :=
  let cs := s.toList
  (cutAt cs (f cs.toArray)).map String.ofList

/-- The extended grapheme clusters of `s`. -/
def graphemes (s : String) : List String := segmentsBy graphemeBreaks s
/-- The words (word-boundary segments) of `s`. -/
def words (s : String) : List String := segmentsBy wordBreaks s
/-- The sentences of `s`. -/
def sentences (s : String) : List String := segmentsBy sentenceBreaks s

#guard graphemeBreaks "".toList.toArray == #[]
#guard graphemeBreaks "äb".toList.toArray == #[0, 2, 3]
#guard graphemeBreaks "\r\n".toList.toArray == #[0, 2]
#guard graphemes "éx" == ["é", "x"]
#guard (graphemes (String.ofList [Char.ofNat 0x1F1E6, Char.ofNat 0x1F1E7, Char.ofNat 0x1F1E8])).map String.length == [2, 1]
#guard words "can't stop" == ["can't", " ", "stop"]
#guard words "3.14 ok" == ["3.14", " ", "ok"]
#guard sentences "Hi there. How are you? Fine." == ["Hi there. ", "How are you? ", "Fine."]
#guard sentences "etc. and so" == ["etc. and so"]

end L4Factoidal.Unicode.Segmentation
