/-
L4Factoidal.FullText.Model — the AllMatches model of XQuery and XPath
Full Text 3.0 (W3C Recommendation, 2015-03-24,
https://www.w3.org/TR/xpath-full-text-30/, §4.2) and the full-text
operators on it (§4.2.6), as pure total functions.

The specification states its semantics as XQuery functions in the `fts:`
namespace over an XML representation of AllMatches. This module keeps the
same structure as Lean data:

* `TokenInfo` (§4.1.2): `startPos`, `endPos`, `startSent`, `endSent`,
  `startPara`, `endPara`;
* `StringMatch` (§4.2.1.1): a query position, the `isContiguous` flag and
  a `TokenInfo`; a `Match` is a conjunction of StringIncludes and
  StringExcludes; an `AllMatches` is a disjunction of Matches with the
  `stokenNum` counter;
* one function per `fts:Apply*` function: `applyOr`, `applyAnd`,
  `applyUnaryNot`, `applyMildNot`, `applyOrder`, `applyScope`,
  `applyContent`, `applyWindow`, `applyDistance`, `applyTimes`, with
  `joinIncludes`, `wordDistance` and `formRange` as in the text.

The order of the Matches in a result follows the order of the XQuery
FLWOR expressions of the specification, so the functions can be compared
with the text line by line. Theorems: `FullText.Theorems`.
-/

namespace L4Factoidal.FullText

/-- §4.1.2 TokenInfo. Positions are integers (§4.1). -/
structure TokenInfo where
  startPos : Int
  endPos : Int
  startSent : Int := 0
  endSent : Int := 0
  startPara : Int := 0
  endPara : Int := 0
deriving DecidableEq, Repr, Inhabited

/-- §4.2.1.1 StringMatch. -/
structure StringMatch where
  queryPos : Nat
  isContiguous : Bool := true
  ti : TokenInfo
deriving DecidableEq, Repr, Inhabited

/-- §4.2.1.1 Match: the StringIncludes and the StringExcludes. -/
structure Match where
  incl : List StringMatch := []
  excl : List StringMatch := []
deriving DecidableEq, Repr, Inhabited

/-- §4.2.1.1 AllMatches. -/
structure AllMatches where
  stokenNum : Nat := 0
  ms : List Match := []
deriving DecidableEq, Repr, Inhabited

/-- §4.3: a Match with no StringExclude makes the selection true. -/
def AllMatches.succeeds (a : AllMatches) : Bool :=
  a.ms.any (fun m => m.excl.isEmpty)

/-! ## Logical operators (§4.2.6.1 to §4.2.6.4) -/

/-- `fts:ApplyFTOr`. -/
def applyOr (a b : AllMatches) : AllMatches :=
  { stokenNum := max a.stokenNum b.stokenNum, ms := a.ms ++ b.ms }

/-- One Match of `fts:ApplyFTAnd`: the children of both. -/
def Match.join (m1 m2 : Match) : Match :=
  { incl := m1.incl ++ m2.incl, excl := m1.excl ++ m2.excl }

/-- `fts:ApplyFTAnd`: every pair of Matches. -/
def applyAnd (a b : AllMatches) : AllMatches :=
  { stokenNum := max a.stokenNum b.stokenNum,
    ms := a.ms.flatMap (fun m1 => b.ms.map (fun m2 => m1.join m2)) }

/-- The children of a Match in document order: the StringIncludes, then
    the StringExcludes (`true` marks an include). -/
def Match.children (m : Match) : List (Bool × StringMatch) :=
  m.incl.map (fun s => (true, s)) ++ m.excl.map (fun s => (false, s))

/-- `fts:InvertStringMatch` added to a Match. -/
def Match.addInverted (c : Bool × StringMatch) (m : Match) : Match :=
  if c.1 then { m with excl := c.2 :: m.excl } else { m with incl := c.2 :: m.incl }

/-- `fts:UnaryNotHelper`. -/
def unaryNotHelper : List Match → List Match
  | [] => [{}]
  | m :: rest =>
    let r := unaryNotHelper rest
    m.children.flatMap (fun c => r.map (fun x => x.addInverted c))

/-- One step of `unaryNotHelper`: the inverted children of `m` in front
    of each Match of `acc`. -/
def unaryNotStep (acc : List Match) (m : Match) : List Match :=
  m.children.flatMap (fun c => acc.map (fun x => x.addInverted c))

/-- `unaryNotHelper` as a loop over the Matches, last first. -/
def unaryNotLoop (ms : List Match) : List Match := ms.reverse.foldl unaryNotStep [{}]

theorem unaryNotHelper_eq_loop_pt (ms : List Match) : unaryNotHelper ms = unaryNotLoop ms := by
  induction ms with
  | nil => rfl
  | cons m rest ih =>
    simp only [unaryNotHelper, unaryNotLoop, List.reverse_cons, List.foldl_append, List.foldl_cons,
      List.foldl_nil]
    rw [ih]; rfl

@[csimp] theorem unaryNotHelper_eq_loop : @unaryNotHelper = @unaryNotLoop := by
  funext ms; exact unaryNotHelper_eq_loop_pt ms

/-- `fts:ApplyFTUnaryNot`. -/
def applyUnaryNot (a : AllMatches) : AllMatches :=
  { stokenNum := a.stokenNum, ms := unaryNotHelper a.ms }

/-- `fts:CoveredIncludePositions`. -/
def Match.covered (m : Match) : List Int :=
  m.incl.flatMap (fun s =>
    (List.range (s.ti.endPos - s.ti.startPos + 1).toNat).map (fun (k : Nat) => s.ti.startPos + (k : Int)))

/-- `fts:ApplyFTMildNot`. The error FTDY0017 is `none`. -/
def applyMildNot (a b : AllMatches) : Option AllMatches :=
  if a.ms.any (fun m => !m.excl.isEmpty) then none
  else if b.ms.any (fun m => !m.excl.isEmpty) then none
  else if b.ms.all (fun m => m.incl.isEmpty) then some a
  else some { stokenNum := a.stokenNum,
              ms := a.ms.filter (fun m1 =>
                b.ms.all (fun m2 =>
                  let p2 := m2.covered
                  m1.covered.any (fun p => !p2.contains p))) }

/-! ## Positional filters (§4.2.6.5 to §4.2.6.10) -/

/-- The pairwise order condition of `fts:ApplyFTOrder`. -/
def ordOk (a b : StringMatch) : Bool :=
  (decide (a.ti.startPos ≤ b.ti.startPos) && decide (a.queryPos ≤ b.queryPos)) ||
  (decide (a.ti.startPos ≥ b.ti.startPos) && decide (a.queryPos ≥ b.queryPos))

/-- `fts:ApplyFTOrder`. -/
def applyOrder (a : AllMatches) : AllMatches :=
  { stokenNum := a.stokenNum,
    ms := (a.ms.filter (fun m => m.incl.all (fun s1 => m.incl.all (fun s2 => ordOk s1 s2)))).map
      (fun m => { m with excl := m.excl.filter (fun x => m.incl.all (fun i => ordOk x i)) }) }

/-- The unit of a scope (`sentence` or `paragraph`). -/
inductive BigUnit where
  | sentence | paragraph
deriving DecidableEq, Repr, Inhabited

def TokenInfo.startU (t : TokenInfo) : BigUnit → Int
  | .sentence => t.startSent | .paragraph => t.startPara
def TokenInfo.endU (t : TokenInfo) : BigUnit → Int
  | .sentence => t.endSent | .paragraph => t.endPara

/-- `fts:ApplyFTScopeSameSentence` and `fts:ApplyFTScopeSameParagraph`. -/
def applyScopeSame (u : BigUnit) (a : AllMatches) : AllMatches :=
  let st (s : StringMatch) := s.ti.startU u
  let en (s : StringMatch) := s.ti.endU u
  { stokenNum := a.stokenNum,
    ms := (a.ms.filter (fun m => m.incl.all (fun s1 => m.incl.all (fun s2 =>
              st s1 == st s2 && st s1 == en s1 && st s2 == en s2 && decide (st s1 > 0) &&
              decide (en s2 > 0))))).map
      (fun m => { m with excl := m.excl.filter (fun x =>
          st x == 0 || (st x == en x && m.incl.all (fun i => st i == st x))) }) }

/-- `fts:ApplyFTScopeDifferentSentence` and `...DifferentParagraph`.
    `$stringInclude1 is $stringInclude2` compares the positions in the
    Match (the same element node), not the values. -/
def applyScopeDifferent (u : BigUnit) (a : AllMatches) : AllMatches :=
  let st (s : StringMatch) := s.ti.startU u
  let en (s : StringMatch) := s.ti.endU u
  let differ (s1 s2 : StringMatch) : Bool :=
    (st s1 != st s2 || st s1 != en s1 || st s2 != en s2) && decide (st s1 > 0) && decide (en s2 > 0)
  { stokenNum := a.stokenNum,
    ms := (a.ms.filter (fun m =>
              decide (m.incl.length > 1) &&
              (List.range m.incl.length).all (fun i => (List.range m.incl.length).all (fun j =>
                i == j || differ (m.incl.getD i default) (m.incl.getD j default))))).map
      (fun m => { m with excl := m.excl.filter (fun x => m.incl.all (fun i => differ i x)) }) }

/-- `fts:ApplyFTScope`. -/
def applyScope (same : Bool) (u : BigUnit) (a : AllMatches) : AllMatches :=
  if same then applyScopeSame u a else applyScopeDifferent u a

/-- `fts:TokenInfoCoversTokenPosition`. -/
def TokenInfo.covers (t : TokenInfo) (p : Int) : Bool := decide (t.startPos ≤ p) && decide (p ≤ t.endPos)

/-- The kinds of `fts:ApplyFTContent`. -/
inductive ContentKind where
  | atStart | atEnd | entire
deriving DecidableEq, Repr, Inhabited

/-- The integers `lo` to `hi` (XQuery `lo to hi`). -/
def intRange (lo hi : Int) : List Int :=
  (List.range (hi - lo + 1).toNat).map (fun (k : Nat) => lo + (k : Int))

/-- `fts:ApplyFTContent`, with `fts:getLowestTokenPosition` and
    `fts:getHighestTokenPosition` of the search context given. -/
def applyContent (lo hi : Int) (k : ContentKind) (a : AllMatches) : AllMatches :=
  { stokenNum := a.stokenNum,
    ms := a.ms.filter (fun m =>
      match k with
      | .entire => (intRange lo hi).all (fun p =>
          m.incl.any (fun si => si.isContiguous && si.ti.covers p))
      | .atStart => m.incl.any (fun si => si.ti.covers lo)
      | .atEnd => m.incl.any (fun si => si.ti.covers hi)) }

/-- The minimum and the maximum of a list. -/
def listMin : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl min x)
def listMax : List Int → Option Int
  | [] => none
  | x :: xs => some (xs.foldl max x)

/-- `fts:joinIncludes`. -/
def joinIncludes (ss : List StringMatch) : List StringMatch :=
  match ss with
  | [] => []
  | s0 :: _ =>
    let posSet := ({ incl := ss } : Match).covered
    let mn := (listMin (ss.map (·.ti.startPos))).getD 0
    let mx := (listMax (ss.map (·.ti.endPos))).getD 0
    let contig := (intRange mn mx).all (fun p => posSet.contains p) && ss.all (·.isContiguous)
    [{ queryPos := s0.queryPos, isContiguous := contig,
       ti := { startPos := mn, endPos := mx,
               startSent := (listMin (ss.map (·.ti.startSent))).getD 0,
               endSent := (listMax (ss.map (·.ti.endSent))).getD 0,
               startPara := (listMin (ss.map (·.ti.startPara))).getD 0,
               endPara := (listMax (ss.map (·.ti.endPara))).getD 0 } }]

/-- The unit of a window or a distance. -/
inductive Unit_ where
  | words | sentences | paragraphs
deriving DecidableEq, Repr, Inhabited

def TokenInfo.startOf (t : TokenInfo) : Unit_ → Int
  | .words => t.startPos | .sentences => t.startSent | .paragraphs => t.startPara
def TokenInfo.endOf (t : TokenInfo) : Unit_ → Int
  | .words => t.endPos | .sentences => t.endSent | .paragraphs => t.endPara

/-- `fts:ApplyFTWordWindow`, `...SentenceWindow`, `...ParagraphWindow`. -/
def applyWindow (u : Unit_) (n : Int) (a : AllMatches) : AllMatches :=
  { stokenNum := a.stokenNum,
    ms := a.ms.flatMap (fun m =>
      match listMin (m.incl.map (·.ti.startOf u)), listMax (m.incl.map (·.ti.endOf u)) with
      | some mn, some mx =>
        (intRange (mx - n + 1) mn).map (fun ws =>
          let we := ws + n - 1
          { incl := joinIncludes m.incl,
            excl := m.excl.filter (fun x => decide (x.ti.startOf u ≥ ws) && decide (x.ti.endOf u ≤ we)) })
      | _, _ => []) }

/-- A range of FTTimes or FTDistance, after evaluation (§3.3). -/
inductive Range where
  | exactly (n : Int)
  | atLeast (n : Int)
  | atMost (n : Int)
  | fromTo (m n : Int)
deriving DecidableEq, Repr, Inhabited

def Range.holds : Range → Int → Bool
  | .exactly n, d => d == n
  | .atLeast n, d => decide (d ≥ n)
  | .atMost n, d => decide (d ≤ n)
  | .fromTo m n, d => decide (d ≥ m) && decide (d ≤ n)

/-- `fts:wordDistance` and its sentence and paragraph forms: the tokens in
    order, then the start of the second less the end of the first, less 1. -/
def unitDistance (u : Unit_) (a b : TokenInfo) : Int :=
  let (x, y) := if a.startPos < b.startPos || (a.startPos == b.startPos && a.endPos ≤ b.endPos)
    then (a, b) else (b, a)
  y.startOf u - x.endOf u - 1

/-- `(startPos, endPos)` order (the `order by` of `fts:ApplyFTWordDistance*`). -/
def tiBefore (s t : StringMatch) : Bool :=
  s.ti.startPos < t.ti.startPos || (s.ti.startPos == t.ti.startPos && s.ti.endPos < t.ti.endPos)

/-- The StringIncludes sorted by `(startPos, endPos)`, stable: an insertion
    sort as a loop. -/
def sortIncludes (ss : List StringMatch) : List StringMatch := Id.run do
  let mut a : Array StringMatch := #[]
  for s in ss do
    -- the position after the last element not after `s`
    let mut k := a.size
    for _ in [0:a.size] do
      if k > 0 && tiBefore s (a.getD (k - 1) default) then k := k - 1 else break
    a := (a.extract 0 k).push s ++ a.extract k a.size
  return a.toList

/-- Adjacent pairs of a list. -/
def adjPairs {α} (l : List α) : List (α × α) := l.zip l.tail

/-- `fts:ApplyFTDistance` (all twelve `fts:Apply*Distance*` functions). -/
def applyDistance (u : Unit_) (r : Range) (a : AllMatches) : AllMatches :=
  { stokenNum := a.stokenNum,
    ms := (a.ms.filter (fun m =>
        (adjPairs (sortIncludes m.incl)).all (fun (x, y) => r.holds (unitDistance u x.ti y.ti)))).map
      (fun m => { incl := joinIncludes m.incl,
                  excl := m.excl.filter (fun x => m.incl.any (fun i => r.holds (unitDistance u i.ti x.ti))) }) }

/-! ## FTTimes (§4.2.6.11) -/

/-- `fts:FormCombinations`: every choice of exactly `k` Matches, joined. -/
def formCombinations : List Match → Nat → List Match
  | _, 0 => [{}]
  | [], _ + 1 => []
  | m :: rest, k + 1 =>
    if rest.length + 1 < k + 1 then []
    else if rest.length + 1 == k + 1 then [(m :: rest).foldr Match.join {}]
    else formCombinations rest (k + 1) ++ (formCombinations rest k).map (fun c => m.join c)

/-- `fts:FormCombinationsAtLeast`. -/
def formCombinationsAtLeast (ms : List Match) (t : Nat) : List Match :=
  (List.range (ms.length + 1 - t)).flatMap (fun i => formCombinations ms (t + i))

/-- `fts:FormRange`. -/
def formRange (ms : List Match) (l u : Int) (stok : Nat) : AllMatches :=
  if l > u then { stokenNum := 0 }
  else
    let am1 : AllMatches := { stokenNum := stok, ms := formCombinationsAtLeast ms l.toNat }
    let am2 : AllMatches := { stokenNum := stok, ms := formCombinationsAtLeast ms (u + 1).toNat }
    applyAnd am1 (applyUnaryNot am2)

/-- `fts:ApplyFTTimes`. A StringExclude in the operand is the error
    XPST0003 (`none`). -/
def applyTimes (r : Range) (a : AllMatches) : Option AllMatches :=
  if a.ms.any (fun m => !m.excl.isEmpty) then none
  else some (match r with
    | .exactly n => formRange a.ms n n a.stokenNum
    | .atLeast n => { stokenNum := a.stokenNum, ms := formCombinationsAtLeast a.ms n.toNat }
    | .atMost n => formRange a.ms 0 n a.stokenNum
    | .fromTo m n => formRange a.ms m n a.stokenNum)

end L4Factoidal.FullText
