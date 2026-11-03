/-
L4Factoidal.Unicode.Bidi — the Unicode Bidirectional Algorithm, UAX #9
revision 52 (Unicode 18.0.0)
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

Rules, with the UAX #9 section numbers:

  §3.3.1  P2, P3     paragraph embedding level (or an explicit direction).
  §3.3.2  X1–X8      explicit levels and directions: the directional status
                     stack of 125 + 2 entries, the overflow isolate and
                     overflow embedding counters, the valid isolate count;
                     BD9 matching PDIs.
  §3.3.3  X9, X10    removal of RLE, LRE, RLO, LRO, PDF and BN; level runs and
                     isolating run sequences (BD13) with their sos and eos.
  §3.3.4  W1–W7      weak types.
  §3.3.5  N0–N2      bracket pairs (BD14–BD16, 63-entry stack, canonical
                     equivalents of U+2329/U+232A and U+3008/U+3009), neutral
                     and isolate formatting types.
  §3.3.6  I1, I2     implicit levels.
  §3.4    L1, L2     reset of separators and trailing white space and
                     isolate formatting characters; reordering.

  §3.3.1  P1         `paragraphs` and `levelsOfText`: split text after each
                     character of type B.

`levels` treats its input as one paragraph, as both Unicode conformance files
do. A character of type B gets the paragraph level (X8, L1). `levels` and
`visualOrder` lay a paragraph out as one line; `visualOrderLines` applies L1
and L2 to each line of a paragraph that the caller has broken into lines.

Characters removed by X9 get no level (`none`) and are left out of the visual
order, as in BidiTest.txt and BidiCharacterTest.txt.

All work over the input is in `for` loops over arrays; there is no recursion
per character.
-/
import L4Factoidal.Unicode.BidiData

namespace L4Factoidal.Unicode

/-- The 23 values of Bidi_Class (UAX #9 Table 4). The constructor order is
the value order of `BidiData.bidiClassText`. -/
inductive BidiClass where
  | L | R | AL | EN | ES | ET | AN | CS | NSM | BN | B | S | WS | ON
  | LRE | LRO | RLE | RLO | PDF | LRI | RLI | FSI | PDI
  deriving DecidableEq, Repr, Inhabited

namespace BidiClass

/-- The classes in constructor order. -/
def all : Array BidiClass :=
  #[.L, .R, .AL, .EN, .ES, .ET, .AN, .CS, .NSM, .BN, .B, .S, .WS, .ON,
    .LRE, .LRO, .RLE, .RLO, .PDF, .LRI, .RLI, .FSI, .PDI]

def ofIndex (n : Nat) : BidiClass := all.getD n .L

/-- The short property value alias, as in the UCD and BidiTest.txt. -/
def name : BidiClass → String
  | .L => "L" | .R => "R" | .AL => "AL" | .EN => "EN" | .ES => "ES"
  | .ET => "ET" | .AN => "AN" | .CS => "CS" | .NSM => "NSM" | .BN => "BN"
  | .B => "B" | .S => "S" | .WS => "WS" | .ON => "ON" | .LRE => "LRE"
  | .LRO => "LRO" | .RLE => "RLE" | .RLO => "RLO" | .PDF => "PDF"
  | .LRI => "LRI" | .RLI => "RLI" | .FSI => "FSI" | .PDI => "PDI"

def ofName? (s : String) : Option BidiClass := all.find? (·.name == s)

/-- LRI, RLI, FSI. -/
@[inline] def isIsolateInitiator : BidiClass → Bool
  | .LRI | .RLI | .FSI => true
  | _ => false

/-- Removed by X9: RLE, LRE, RLO, LRO, PDF, BN. -/
@[inline] def isRemovedByX9 : BidiClass → Bool
  | .RLE | .LRE | .RLO | .LRO | .PDF | .BN => true
  | _ => false

/-- NI (BD: neutral or isolate formatting character): B, S, WS, ON, LRI,
RLI, FSI, PDI. -/
@[inline] def isNI : BidiClass → Bool
  | .B | .S | .WS | .ON | .LRI | .RLI | .FSI | .PDI => true
  | _ => false

/-- The strong direction for N0 and N1, where EN and AN count as R. -/
@[inline] def strongNR : BidiClass → Option BidiClass
  | .L => some .L
  | .R | .EN | .AN => some .R
  | _ => none

end BidiClass

/-- Bidi_Class of a code point (DerivedBidiClass.txt, with the default
values of unassigned code points). -/
def bidiClassOf (c : Char) : BidiClass :=
  BidiClass.ofIndex (BidiData.bidiClassTable.getChar c).toNat

/-- The paragraph direction: auto (P2, P3, default left-to-right),
left-to-right (level 0) or right-to-left (level 1). -/
inductive ParaDir where
  | auto | ltr | rtl
  deriving DecidableEq, Repr, Inhabited

/-! ## Bracket and mirroring data -/

/-- One row of BidiBrackets.txt: the code point, the canonical equivalent of
its Bidi_Paired_Bracket, the type (1 open, 2 close) and the canonical
equivalent of the code point itself. -/
structure BracketRow where
  cp : UInt32
  pairCanon : UInt32
  kind : UInt8
  selfCanon : UInt32
  deriving Inhabited

private def hexVal (s : String) : UInt32 :=
  (s.foldl (fun n c =>
    n * 16 + (if c.isDigit then c.toNat - 48
              else if 'a' ≤ c ∧ c ≤ 'f' then c.toNat - 87 else c.toNat - 55)) 0).toUInt32

/-- The rows of BidiBrackets.txt, sorted by code point. -/
def bracketRows : Array BracketRow := Id.run do
  let mut out : Array BracketRow := #[]
  for e in BidiData.bracketText.splitOn ";" do
    match (e.splitOn " ").filter (· != "") with
    | [a, b, k, s] =>
      out := out.push { cp := hexVal a, pairCanon := hexVal b, kind := k.toNat!.toUInt8,
                        selfCanon := hexVal s }
    | _ => pure ()
  pure out

/-- The pairs of BidiMirroring.txt, sorted by code point. -/
def mirrorRows : Array (UInt32 × UInt32) := Id.run do
  let mut out : Array (UInt32 × UInt32) := #[]
  for e in BidiData.mirrorText.splitOn ";" do
    match (e.splitOn " ").filter (· != "") with
    | [a, b] => out := out.push (hexVal a, hexVal b)
    | _ => pure ()
  pure out

/-- Binary search of a sorted array by key; the fuel 40 bounds the depth. -/
def bsearch {α : Type} [Inhabited α] (a : Array α) (key : α → UInt32) (c : UInt32) :
    Option α :=
  let rec go (lo hi : Nat) : Nat → Option α
    | 0 => none
    | f + 1 =>
      if lo ≥ hi then none
      else
        let mid := (lo + hi) / 2
        let k := key a[mid]!
        if c < k then go lo mid f
        else if c > k then go (mid + 1) hi f
        else some a[mid]!
  go 0 a.size 40

/-- The BidiBrackets.txt row of `c`, if it is a paired bracket. -/
def bracketOf (c : Char) : Option BracketRow := bsearch bracketRows (·.cp) c.val

/-- Bidi_Mirroring_Glyph of `c` (UAX #9 §7), if it has one. -/
def mirrorOf (c : Char) : Option Char :=
  (bsearch mirrorRows (·.1) c.val).map fun p => Char.ofNat p.2.toNat

/-- Bracket information for `levels`, one entry per character: `kind` 0 (not
a paired bracket), 1 (opening), 2 (closing); `key` the canonical equivalent of
the Bidi_Paired_Bracket for an opening bracket, of the character itself for a
closing one (BD16). Empty arrays mean no brackets. -/
structure BracketInfo where
  kind : Array UInt8 := #[]
  key : Array UInt32 := #[]
  deriving Inhabited

def BracketInfo.ofChars (cs : Array Char) : BracketInfo := Id.run do
  let mut kind : Array UInt8 := Array.mkEmpty cs.size
  let mut key : Array UInt32 := Array.mkEmpty cs.size
  for c in cs do
    match bracketOf c with
    | some r =>
      kind := kind.push r.kind
      key := key.push (if r.kind == 1 then r.pairCanon else r.selfCanon)
    | none =>
      kind := kind.push 0
      key := key.push 0
  pure { kind, key }

/-! ## The algorithm -/

/-- P2 over `[start, stop)`: the direction of the first L, R or AL that is
not between an isolate initiator and its matching PDI; stops at a B.
`some 0` for L, `some 1` for R or AL. -/
def firstStrong (cls : Array BidiClass) (start stop : Nat) : Option Nat := Id.run do
  let mut depth := 0
  for i in [start:stop] do
    match cls.getD i .ON with
    | .L => if depth == 0 then return some 0
    | .R | .AL => if depth == 0 then return some 1
    | .LRI | .RLI | .FSI => depth := depth + 1
    | .PDI => if depth > 0 then depth := depth - 1
    | .B => return none
    | _ => pure ()
  return none

/-- The maximum explicit embedding depth (BD2). -/
def maxDepth : Nat := 125

private def oddAbove (l : Nat) : Nat := if l % 2 == 0 then l + 1 else l + 2
private def evenAbove (l : Nat) : Nat := if l % 2 == 0 then l + 2 else l + 1

@[inline] private def dirOfLevel (l : Nat) : BidiClass := if l % 2 == 0 then .L else .R

/-- W1–W7, N0–N2 and I1–I2 for one isolating run sequence. `idx` are the
text positions of the sequence, `t` their current types, `lvl` their (common)
embedding level. Returns the resolved levels of the positions in `idx`. -/
def resolveSequence (cls : Array BidiClass) (br : BracketInfo)
    (idx : Array Nat) (t0 : Array BidiClass) (lvl : Nat) (sos eos : BidiClass) :
    Array Nat := Id.run do
  let len := idx.size
  let mut t := t0
  -- W1
  let mut prev := sos
  for k in [0:len] do
    let c := t[k]!
    if c == .NSM then t := t.set! k prev
    else prev := if c.isIsolateInitiator || c == .PDI then .ON else c
  -- W2
  let mut lastStrong := sos
  for k in [0:len] do
    let c := t[k]!
    if c == .L || c == .R || c == .AL then lastStrong := c
    else if c == .EN && lastStrong == .AL then t := t.set! k .AN
  -- W3
  for k in [0:len] do
    if t[k]! == .AL then t := t.set! k .R
  -- W4
  for k in [1:len - 1] do
    let c := t[k]!
    let p := t[k-1]!
    let n := t[k+1]!
    if c == .ES then
      if p == .EN && n == .EN then t := t.set! k .EN
    else if c == .CS then
      if p == .EN && n == .EN then t := t.set! k .EN
      else if p == .AN && n == .AN then t := t.set! k .AN
  -- W5
  let mut runStart := 0
  for k in [0:len] do
    if t[k]! == .ET then
      if k == 0 || t[k-1]! != .ET then runStart := k
      if k + 1 == len || t[k+1]! != .ET then
        let before := if runStart == 0 then sos else t[runStart - 1]!
        let after := if k + 1 == len then eos else t[k+1]!
        if before == .EN || after == .EN then
          for j in [runStart:k+1] do t := t.set! j .EN
  -- W6
  for k in [0:len] do
    let c := t[k]!
    if c == .ES || c == .ET || c == .CS then t := t.set! k .ON
  -- W7
  lastStrong := sos
  for k in [0:len] do
    let c := t[k]!
    if c == .L || c == .R then lastStrong := c
    else if c == .EN && lastStrong == .L then t := t.set! k .L
  -- N0: BD16 bracket pairs
  let e := dirOfLevel lvl
  if br.kind.size > 0 then
    let mut stk : Array (UInt32 × Nat) := #[]
    -- `closeOf[o]` is the closing position of the pair opened at `o`
    -- (`len` for none); a walk over it lists the pairs sorted by opener.
    let mut closeOf : Array Nat := Array.replicate len len
    let mut overflow := false
    for k in [0:len] do
      if !overflow && t[k]! == .ON then
        let i := idx[k]!
        let kd := br.kind.getD i 0
        if kd == 1 then
          if stk.size < 63 then stk := stk.push (br.key.getD i 0, k)
          else overflow := true
        else if kd == 2 then
          let key := br.key.getD i 0
          let mut found := false
          let mut j := stk.size
          for _ in [0:stk.size] do
            if !found then
              j := j - 1
              if stk[j]!.1 == key then
                found := true
          if found then
            closeOf := closeOf.set! stk[j]!.2 k
            stk := stk.extract 0 j
    if overflow then closeOf := Array.replicate len len
    for o in [0:len] do
      let c := closeOf[o]!
      if c == len then continue
      let mut foundE := false
      let mut foundOpp := false
      for k in [o+1:c] do
        match t[k]!.strongNR with
        | some d => if d == e then foundE := true else foundOpp := true
        | none => pure ()
      let mut dir : Option BidiClass := none
      if foundE then dir := some e
      else if foundOpp then
        let mut ctx := sos
        let mut done := false
        let mut k := o
        for _ in [0:o] do
          if !done then
            k := k - 1
            match t[k]!.strongNR with
            | some d => ctx := d; done := true
            | none => pure ()
        dir := some (if ctx != e then ctx else e)
      match dir with
      | some d =>
        t := t.set! o d
        t := t.set! c d
        -- NSMs (original type) right after a bracket take its type.
        let mut go := true
        for k in [o+1:len] do
          if go && cls.getD idx[k]! .ON == .NSM then t := t.set! k d else go := false
        go := true
        for k in [c+1:len] do
          if go && cls.getD idx[k]! .ON == .NSM then t := t.set! k d else go := false
      | none => pure ()
  -- N1, N2
  let mut niStart := 0
  for k in [0:len] do
    if t[k]!.isNI then
      if k == 0 || !(t[k-1]!.isNI) then niStart := k
      if k + 1 == len || !(t[k+1]!.isNI) then
        let before := if niStart == 0 then some sos else t[niStart - 1]!.strongNR
        let after := if k + 1 == len then some eos else t[k+1]!.strongNR
        let d := if before == after && before.isSome then before.getD e else e
        for j in [niStart:k+1] do t := t.set! j d
  -- I1, I2
  let mut out : Array Nat := Array.mkEmpty len
  for k in [0:len] do
    let c := t[k]!
    let l :=
      if lvl % 2 == 0 then
        (if c == .R then lvl + 1 else if c == .AN || c == .EN then lvl + 2 else lvl)
      else
        (if c == .L || c == .EN || c == .AN then lvl + 1 else lvl)
    out := out.push l
  pure out

/-- Resolved embedding levels of one paragraph laid out as one line (rules
P2–P3, X1–X10, W1–W7, N0–N2, I1–I2, L1). `cls` are the Bidi_Class values,
`br` the bracket information (empty for none). Returns the level of each
character (`none` for a character removed by X9) and the paragraph
embedding level. -/
def levels (cls : Array BidiClass) (br : BracketInfo) (paraDir : ParaDir) :
    Array (Option Nat) × Nat := Id.run do
  let n := cls.size
  -- P2, P3
  let para : Nat := match paraDir with
    | .ltr => 0
    | .rtl => 1
    | .auto => (firstStrong cls 0 n).getD 0
  -- BD9: matching PDIs
  let mut matchPDI : Array Nat := Array.replicate n n
  let mut pdiMatched : Array Bool := Array.replicate n false
  let mut openIso : Array Nat := #[]
  for i in [0:n] do
    match cls[i]! with
    | .LRI | .RLI | .FSI => openIso := openIso.push i
    | .PDI =>
      match openIso.back? with
      | some j =>
        matchPDI := matchPDI.set! j i
        pdiMatched := pdiMatched.set! i true
        openIso := openIso.pop
      | none => pure ()
    | .B => openIso := #[]
    | _ => pure ()
  -- X1–X8. Stack entries: level, override (ON, L or R), isolate status.
  let mut stLevel : Array Nat := #[para]
  let mut stOverride : Array BidiClass := #[.ON]
  let mut stIsolate : Array Bool := #[false]
  let mut overflowIsolate := 0
  let mut overflowEmbedding := 0
  let mut validIsolate := 0
  let mut types := cls
  let mut lev : Array Nat := Array.replicate n para
  for i in [0:n] do
    let c := cls[i]!
    match c with
    | .RLE | .LRE | .RLO | .LRO | .RLI | .LRI | .FSI =>
      let isIso := c.isIsolateInitiator
      let isRTL := c == .RLE || c == .RLO || c == .RLI ||
        (c == .FSI && firstStrong cls (i + 1) (matchPDI[i]!) == some 1)
      let top := stLevel.back!
      if isIso then
        lev := lev.set! i top
        let ov := stOverride.back!
        if ov != .ON then types := types.set! i ov
      let newLevel := if isRTL then oddAbove top else evenAbove top
      if newLevel ≤ maxDepth && overflowIsolate == 0 && overflowEmbedding == 0 then
        if isIso then validIsolate := validIsolate + 1
        stLevel := stLevel.push newLevel
        stOverride := stOverride.push (if c == .LRO then .L else if c == .RLO then .R else .ON)
        stIsolate := stIsolate.push isIso
        if !isIso then lev := lev.set! i newLevel
      else
        if isIso then overflowIsolate := overflowIsolate + 1
        else if overflowIsolate == 0 then overflowEmbedding := overflowEmbedding + 1
        if !isIso then lev := lev.set! i top
    | .PDI =>
      if overflowIsolate > 0 then overflowIsolate := overflowIsolate - 1
      else if validIsolate == 0 then pure ()
      else
        overflowEmbedding := 0
        for _ in [0:stIsolate.size] do
          if !stIsolate.back! && stIsolate.size > 1 then
            stLevel := stLevel.pop; stOverride := stOverride.pop; stIsolate := stIsolate.pop
        stLevel := stLevel.pop; stOverride := stOverride.pop; stIsolate := stIsolate.pop
        validIsolate := validIsolate - 1
      lev := lev.set! i stLevel.back!
      let ov := stOverride.back!
      if ov != .ON then types := types.set! i ov
    | .PDF =>
      lev := lev.set! i stLevel.back!
      if overflowIsolate > 0 then pure ()
      else if overflowEmbedding > 0 then overflowEmbedding := overflowEmbedding - 1
      else if !stIsolate.back! && stLevel.size ≥ 2 then
        stLevel := stLevel.pop; stOverride := stOverride.pop; stIsolate := stIsolate.pop
    | .B => lev := lev.set! i para
    | .BN => lev := lev.set! i stLevel.back!
    | _ =>
      lev := lev.set! i stLevel.back!
      let ov := stOverride.back!
      if ov != .ON then types := types.set! i ov
  -- X9: the kept positions.
  let mut kept : Array Nat := #[]
  let mut posInKept : Array Nat := Array.replicate n n
  for i in [0:n] do
    if !(cls[i]!.isRemovedByX9) then
      posInKept := posInKept.set! i kept.size
      kept := kept.push i
  let m := kept.size
  -- X10: level runs over the kept positions, [start, end) in `kept`.
  let mut runs : Array (Nat × Nat) := #[]
  let mut runOf : Array Nat := Array.replicate n 0
  let mut rs := 0
  for p in [0:m] do
    let i := kept[p]!
    runOf := runOf.set! i runs.size
    if p + 1 == m || lev[kept[p+1]!]! != lev[i]! then
      runs := runs.push (rs, p + 1)
      rs := p + 1
  -- BD13 isolating run sequences, each resolved in turn.
  let mut res := lev
  for r in [0:runs.size] do
    let (a0, _) := runs[r]!
    let f := kept[a0]!
    if cls[f]! == .PDI && pdiMatched[f]! then continue
    let mut idx : Array Nat := #[]
    let mut cur := r
    let mut more := true
    for _ in [0:runs.size] do
      if more then
        let (a, b) := runs[cur]!
        for p in [a:b] do idx := idx.push kept[p]!
        let last := kept[b - 1]!
        if cls[last]!.isIsolateInitiator && matchPDI[last]! < n then
          cur := runOf[matchPDI[last]!]!
        else more := false
    let first := idx[0]!
    let last := idx.back!
    let lvl := lev[first]!
    let pf := posInKept[first]!
    let prevLev := if pf == 0 then para else lev[kept[pf - 1]!]!
    let pl := posInKept[last]!
    let nextLev :=
      if cls[last]!.isIsolateInitiator || pl + 1 ≥ m then para else lev[kept[pl + 1]!]!
    let sos := dirOfLevel (max lvl prevLev)
    let eos := dirOfLevel (max lvl nextLev)
    let t0 := idx.map (types[·]!)
    let out := resolveSequence cls br idx t0 lvl sos eos
    for k in [0:idx.size] do
      res := res.set! idx[k]! out[k]!
  -- L1: segment and paragraph separators, and white space and isolate
  -- formatting characters before them or at the end of the line.
  let mut trailing := true
  for q in [0:n] do
    let i := n - 1 - q
    let c := cls[i]!
    if c.isRemovedByX9 then pure ()
    else if c == .S || c == .B then
      res := res.set! i para; trailing := true
    else if c == .WS || c.isIsolateInitiator || c == .PDI then
      if trailing then res := res.set! i para
    else trailing := false
  let mut outLv : Array (Option Nat) := Array.mkEmpty n
  for i in [0:n] do
    outLv := outLv.push (if cls[i]!.isRemovedByX9 then none else some res[i]!)
  pure (outLv, para)

/-- Reverse the elements at positions `[i, j]` (inclusive) by swaps; a tail
call whose fuel is the distance. -/
def revRange {α : Type} (a : Array α) (i j : Nat) : Array α :=
  go a i j (j - i)
where
  go (a : Array α) (i j : Nat) : Nat → Array α
    | 0 => a
    | f + 1 =>
      if h : i < j ∧ j < a.size then
        go (a.swap i j (by omega) h.2) (i + 1) (j - 1) f
      else a

/-- L2: the visual order, left to right, of the characters that have a
level; the input is the output of `levels`. From the highest level down to
the lowest odd level, every maximal run at that level or higher is
reversed. -/
def visualOrder (lv : Array (Option Nat)) : Array Nat := Id.run do
  let mut ord : Array Nat := #[]
  let mut ls : Array Nat := #[]
  for i in [0:lv.size] do
    match lv[i]! with
    | some l => ord := ord.push i; ls := ls.push l
    | none => pure ()
  let m := ord.size
  let hi := ls.foldl max 0
  let lowOdd := ls.foldl (fun acc l => if l % 2 == 1 then min acc l else acc) (hi + 1)
  if lowOdd > hi then return ord
  for s in [0:hi - lowOdd + 1] do
    let cur := hi - s
    let mut start := 0
    let mut inRun := false
    for k in [0:m] do
      if ls[k]! ≥ cur then
        if !inRun then start := k; inRun := true
        if k + 1 == m || ls[k+1]! < cur then
          ord := revRange ord start k
          ls := revRange ls start k
          inRun := false
  pure ord

/-- `levels` over code points: the classes from `bidiClassOf`, the bracket
information from BidiBrackets.txt. -/
def levelsOfChars (cs : Array Char) (paraDir : ParaDir) : Array (Option Nat) × Nat :=
  levels (cs.map bidiClassOf) (BracketInfo.ofChars cs) paraDir

/-- P1: split text into paragraphs. Each paragraph ends after a character of
class B (kept with the paragraph it ends), or at the end of the text. The
result is the list of `[start, stop)` ranges, in order. -/
def paragraphs (cs : Array Char) : Array (Nat × Nat) := Id.run do
  let mut out : Array (Nat × Nat) := #[]
  let mut start := 0
  for i in [0:cs.size] do
    if bidiClassOf cs[i]! == .B then
      out := out.push (start, i + 1)
      start := i + 1
  if start < cs.size then out := out.push (start, cs.size)
  pure out

/-- P1 to I2 over text with any number of paragraphs: each paragraph gets its
own paragraph level (P2, P3, or `paraDir`) and its own levels. The result
lists, per paragraph, its range, its levels and its paragraph level. -/
def levelsOfText (cs : Array Char) (paraDir : ParaDir) :
    Array ((Nat × Nat) × Array (Option Nat) × Nat) :=
  (paragraphs cs).map fun (a, b) => ((a, b), levelsOfChars (cs.extract a b) paraDir)

/-- L1 and L2 for a paragraph that is broken into lines (UAX #9 §3.4). `cs` is
one paragraph, `lp` its result from `levelsOfChars`, and `lineEnds` the
positions, increasing, where its lines end (the last one is `cs.size`; for
example from `LineBreak.breaks`). L1 resets the white space and isolate
formatting characters at the end of each line to the paragraph level; L2
reorders each line by itself. The result is the visual order of the whole
paragraph, line after line, as indices into `cs`. -/
def visualOrderLines (cs : Array Char) (lp : Array (Option Nat) × Nat)
    (lineEnds : Array Nat) : Array Nat := Id.run do
  let (lv0, para) := lp
  let mut lv := lv0
  let mut start := 0
  let mut out : Array Nat := #[]
  for e0 in lineEnds do
    let e := min e0 cs.size
    if e > start then
      -- L1 at the end of this line.
      let mut trailing := true
      for q in [0:e - start] do
        let i := e - 1 - q
        if trailing then
          let c := bidiClassOf cs[i]!
          if c.isRemovedByX9 then pure ()
          else if c == .WS || c.isIsolateInitiator || c == .PDI then
            lv := lv.set! i (some para)
          else trailing := false
      -- L2 on this line.
      for k in visualOrder (lv.extract start e) do
        out := out.push (start + k)
      start := e
  pure out

#guard visualOrderLines "ab".toList.toArray (levelsOfChars "ab".toList.toArray .ltr) #[2] == #[0, 1]
#guard (let t := "אב גד".toList.toArray
        visualOrderLines t (levelsOfChars t .ltr) #[3, 5]) == #[1, 0, 2, 4, 3]
#guard (let t := "אב גד".toList.toArray
        visualOrderLines t (levelsOfChars t .ltr) #[5]) == #[4, 3, 2, 1, 0]

#guard paragraphs "ab\ncd".toList.toArray == #[(0, 3), (3, 5)]
#guard paragraphs "ab\n".toList.toArray == #[(0, 3)]
#guard paragraphs #[] == #[]
#guard ((levelsOfText "a\nא".toList.toArray .auto).map (·.2.2)) == #[0, 1]

#guard bidiClassOf 'a' == .L
#guard bidiClassOf 'א' == .R
#guard bidiClassOf 'ا' == .AL
#guard bidiClassOf '1' == .EN
#guard bidiClassOf '⁧' == .RLI
#guard bidiClassOf '͸' == .L
#guard (bracketOf '(').map (·.kind) == some 1
#guard (bracketOf '〉').map (·.selfCanon) == some 0x3009
#guard mirrorOf '(' == some ')'
#guard levels #[.L, .R] {} .rtl == (#[some 2, some 1], 1)
#guard levels #[.R, .L] {} .auto == (#[some 1, some 2], 1)
#guard levels #[.L, .LRE, .R] {} .ltr == (#[some 0, none, some 3], 0)
#guard visualOrder #[some 2, some 1] == #[1, 0]
#guard visualOrder #[some 0, none, some 1, some 1] == #[0, 3, 2]
#guard revRange #[1, 2, 3, 4, 5] 1 3 == #[1, 4, 3, 2, 5]

end L4Factoidal.Unicode
