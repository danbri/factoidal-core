/-
L4Factoidal.Syntax.TurtleSplitScan — the places where a Turtle or TriG
document can be cut so that several readers read it at once
(https://github.com/danbri/factoidal/issues/842).

The chunk readers (`TurtleChunkFold`, `TriGChunkFold`) cut their input into
statement candidates with a lexical scanner (`StatementScan`, `TriGScan`) and
give each candidate to the grammar. A candidate ends at a `.` in the normal
lexical mode that is followed by white space or `#` (the "dot boundary"), at
a line end after a SPARQL-style directive, and, in TriG, at the `{` and `}`
of a graph block. At a dot boundary the scanner of the reader starts again
from its initial state, and what the reader keeps from the text before is
its `TurtleState` (prefixes, base, the generated blank-node counter and
prefix, the RDF version) and, in TriG, the graph block it is in.

This module reads the bytes of a document once and gives:

* `Plan.splits`: dot boundaries near given byte targets, each with the
  number of directive units before it and, in TriG, the header of the graph
  block it is in;
* `Plan.directives`: the byte ranges of the units (candidates at the top
  level, and graph block headers) that can contain a directive (`@prefix`,
  `@base`, `PREFIX`, `BASE`, `VERSION`). A reader that starts at a split
  reads these units first, with a step that keeps nothing
  (`Source.Reader.resume`), and so has the prefixes and the base of the
  single reader at that place;
* the number of blank nodes the reader mints before each split
  (`Split.counter`): one for each `[` and one for each item of a collection
  (`Hot.brackets`). A reader that starts at the split sets its counter to it,
  so it mints the labels of the single reader; its caller checks the counter
  at the end of the range against the next split's. `~`, `{|` (RDF 1.2
  reifiers and annotations) also mint; a text with them is flagged
  (`Plan.uncounted`) and read as one range;
* the longest run of `_` bytes (the generated blank-node prefix, as
  `Source.Prepass` computes it from characters: `_` is one byte in UTF-8 and
  no byte of a multi-byte sequence equals it) and whether the text has `<<`.

The scanner copies the lexical modes of `StatementScan.feedChar` (Turtle) and
`TriGScan.feedChar` (TriG) byte for byte, so a split is a place where the
single reader also starts a new candidate. It adds what those scanners do not
keep: the depth of `[`, `(` and `{|` (a split needs depth 0), the start of
each candidate, and a flag for a candidate that can hold a directive. A
directive starts a statement, and a statement starts a candidate or follows a
`.` with no white space between them. So a candidate is flagged when its first
bytes after white space and comments are `@`, `PREFIX`, `BASE` or `VERSION`
(any case, as `StatementScan.beginsNoDotDirective` tests), or when a `.` in
the normal mode is followed at once by `@` or by one of the letters that
start these keywords. The test is wider than the grammar: a false positive
costs one more unit to read again; a miss would give a reader the wrong
prefixes.

The scanner is a loop over the bytes whose state is scalars only (`Hot`); the
rare events (a dot boundary, a SPARQL directive line end, a graph block that
opens or closes) are handled with the rest of the state (`Cold`). A state
with arrays updated at every byte cost about 190 ns per byte (7.6 s for 39 MB,
2026-10-22).

A split inside a TriG graph block is offered only when the header of the
block has no `[` or `(` (a header `[]` mints a label) and no directive (a
directive would be applied twice).

The equality of the split read with the single read is not proved; the
measurement is `l4split-diff` (`tools/split-read-differential.sh`) and the
open theorem is https://github.com/danbri/factoidal/issues/944 (row SR-1 of
`tests/known-defects/run.sh`).

No `sorry`, no `axiom`, no `partial`.
-/

import L4Factoidal.Prim.Bytes

namespace L4Factoidal.Syntax.SplitScan


/-- A place where a reader can start. -/
structure Split where
  /-- The byte where the range starts: the white space or `#` after a
      statement's `.`. -/
  pos : Nat
  /-- The directive units (`Plan.directives`) that end at or before `pos`. -/
  directives : Nat
  /-- In TriG, the byte range of the header of the graph block that `pos`
      is in (empty for a block of the default graph); `none` at the top
      level. -/
  block : Option (Nat × Nat)
  /-- The blank nodes the single reader mints before `pos`
      (`TurtleState.bnodeCounter` there). -/
  counter : Nat
  deriving Repr, BEq, Inhabited

/-- A unit that can contain a directive: bytes `[start, stop)`, and whether it
    is the header of a graph block (then it is read again with `{ }` after
    it). -/
structure Unit where
  start : Nat
  stop : Nat
  header : Bool
  deriving Repr, BEq, Inhabited

/-- What one read of the document gives. -/
structure Plan where
  splits : Array Split := #[]
  directives : Array Unit := #[]
  longestUnderscore : Nat := 0
  doubleLt : Bool := false
  /-- The blank nodes minted in the whole document, by the count of the scan. -/
  mints : Nat := 0
  /-- The text has a construct whose minted blank nodes the scan does not count
      (`~`, `{|`, brackets nested 63 deep): the document is one range. -/
  uncounted : Bool := false
  deriving Repr, Inhabited

/-! ## The state of every byte

Modes, as `ScanMode`: 0 normal, 1 IRIREF, 2 comment, 3 one opening quote,
4 two opening quotes, 5 short string, 6 long string. Flags are bits of
`Hot.fl`. -/

def fStrEsc : UInt32 := 1        -- the last string byte was a `\`
def fDot : UInt32 := 2           -- `pendingDot`
def fBlock : UInt32 := 4         -- `TriGScan.inBlock`
def fNameEsc : UInt32 := 8       -- `TriGScan.escaped`
def fHeld : UInt32 := 16         -- `TriGScan.heldOpen`
def fAfterBar : UInt32 := 32     -- `TriGScan.afterBar`
def fPrevBrace : UInt32 := 64    -- the last normal byte was `{`
def fPrevBar : UInt32 := 128     -- the last normal byte was `|`
def fPrevLt : UInt32 := 256      -- the last byte was `<`
def fDoubleLt : UInt32 := 512    -- the text has `<<`
def fCandDir : UInt32 := 1024    -- the candidate can hold a directive (a `.` rule)
def fCandBr : UInt32 := 2048     -- the candidate has `[` or `(`
def fTrig : UInt32 := 4096       -- the document is TriG
def fSigOpen : UInt32 := 8192    -- the candidate has a byte that is not white space or comment
def fSavedDir : UInt32 := 16384  -- the candidate that the event ended can hold a directive
def fSavedBr : UInt32 := 32768   -- the candidate that the event ended has `[` or `(`
def fInItem : UInt32 := 65536    -- in a collection: inside an item
def fAttach : UInt32 := 131072   -- in a collection: after `^^`, the datatype belongs to the item
def fUncounted : UInt32 := 262144 -- a construct whose mints the scan does not count

/-- Events of one byte, bits of `Hot.ev`. -/
def eOpen : UInt8 := 1    -- a held `{` (the byte before) opened a graph block
def eDot : UInt8 := 2     -- a dot boundary at this byte
def eLine : UInt8 := 4    -- a SPARQL directive line ends at this byte
def eClose : UInt8 := 8   -- this `}` closed a graph block

/-- The state that changes at every byte: scalars only, so that an update
    reuses the object. -/
structure Hot where
  mode : UInt8 := 0
  quote : UInt8 := 0
  closing : UInt8 := 0
  ev : UInt8 := 0
  fl : UInt32 := 0
  depth : UInt32 := 0
  annot : UInt32 := 0
  /-- the reader's directive head (`StatementScan.head`): the first 7 bytes
      after leading white space, lower case -/
  hv : UInt64 := 0
  hl : UInt8 := 0
  /-- the first 7 bytes after leading white space and comments, lower case -/
  sv : UInt64 := 0
  sl : UInt8 := 0
  run : UInt64 := 0
  longest : UInt64 := 0
  /-- bit `d` set: the bracket at depth `d` (0 outermost) is `(` -/
  bstack : UInt64 := 0
  /-- the blank nodes the reader mints so far: one for each `[`, one for each
      item of a collection (`TurtleState.freshBnode`) -/
  mints : UInt64 := 0
  deriving Inhabited

@[inline] def Hot.has (h : Hot) (f : UInt32) : Bool := h.fl &&& f != 0

@[inline] def Hot.set (h : Hot) (f : UInt32) (b : Bool) : Hot :=
  { h with fl := if b then h.fl ||| f else h.fl &&& ~~~f }

@[inline] def isWsB (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13

@[inline] def lowerB (c : UInt8) : UInt8 := if c ≥ 65 && c ≤ 90 then c + 32 else c

/-- Bytes of a word, little end first, as `Hot.hv` and `Hot.sv` hold them. -/
def packWord (s : String) : UInt64 :=
  s.toUTF8.toList.foldr (fun b acc => (acc <<< 8) ||| b.toUInt64) 0

def kwPrefix : UInt64 := packWord "prefix"
def kwBase : UInt64 := packWord "base"
def kwVersion : UInt64 := packWord "version"

@[inline] def maskOf (n : UInt8) : UInt64 :=
  if n ≥ 8 then 0xFFFFFFFFFFFFFFFF else ((1 : UInt64) <<< (8 * n.toUInt64)) - 1

/-- `StatementScan.beginsNoDotDirective` on the head bytes. -/
@[inline] def headIsDirective (v : UInt64) (len : UInt8) : Bool :=
  (len ≥ 6 && v &&& maskOf 6 == kwPrefix) || (len ≥ 4 && v &&& maskOf 4 == kwBase) ||
    (len ≥ 7 && v &&& maskOf 7 == kwVersion)

/-- The candidate can hold a directive: the `.` rule, or its first bytes. -/
@[inline] def Hot.candDirective (h : Hot) : Bool :=
  h.has fCandDir || (h.sl ≥ 1 && h.sv &&& 0xFF == 64) || headIsDirective h.sv h.sl

/-- A candidate ends at this byte: keep its two flags for the handler, and
    start the next candidate's flags and heads. -/
@[inline] def Hot.endCand (h : Hot) (ev : UInt8) : Hot :=
  let dir := h.candDirective
  let br := h.has fCandBr
  let fl := h.fl &&& ~~~(fCandDir ||| fCandBr ||| fSigOpen ||| fSavedDir ||| fSavedBr ||| fPrevBrace ||| fPrevBar)
  let fl := fl ||| (if dir then fSavedDir else 0) ||| (if br then fSavedBr else 0)
  { h with fl, ev := h.ev ||| ev, hv := 0, hl := 0, sv := 0, sl := 0 }

/-- `stepMode` of `TurtleStatementScan` on a byte. -/
@[inline] def Hot.stepMode (h : Hot) (c : UInt8) : Hot :=
  match h.mode with
  | 0 =>
      if c == 60 then { h with mode := 1 }
      else if c == 35 then { h with mode := 2 }
      else if c == 34 || c == 39 then { h with mode := 3, quote := c }
      else h
  | 1 => if c == 62 then { h with mode := 0 } else h
  | 2 => if c == 10 || c == 13 then { h with mode := 0 } else h
  | 3 =>
      if c == h.quote then { h with mode := 4 }
      else if c == 92 then { h with mode := 5, fl := h.fl ||| fStrEsc }
      else { h with mode := 5, fl := h.fl &&& ~~~fStrEsc }
  | 4 =>
      if c == h.quote then { h with mode := 6, fl := h.fl &&& ~~~fStrEsc, closing := 0 }
      else { h with mode := 0 }
  | 5 =>
      if h.has fStrEsc then { h with fl := h.fl &&& ~~~fStrEsc }
      else if c == 92 then { h with fl := h.fl ||| fStrEsc }
      else if c == h.quote then { h with mode := 0 }
      else h
  | _ =>
      if h.has fStrEsc then { h with fl := h.fl &&& ~~~fStrEsc, closing := 0 }
      else if c == 92 then { h with fl := h.fl ||| fStrEsc, closing := 0 }
      else if c == h.quote then
        if h.closing + 1 == 3 then { h with mode := 0, closing := 0 } else { h with closing := h.closing + 1 }
      else { h with closing := 0 }

/-- Push a byte on the two heads. `sig` tells that the byte starts or
    continues the significant text of the candidate. -/
@[inline] def Hot.pushHeads (h : Hot) (c : UInt8) (wasNormal : Bool) : Hot :=
  let h :=
    if h.hl == 0 then
      if isWsB c then h else { h with hv := (lowerB c).toUInt64, hl := 1 }
    else if h.hl < 7 then
      { h with hv := h.hv ||| ((lowerB c).toUInt64 <<< (8 * h.hl.toUInt64)), hl := h.hl + 1 }
    else h
  if !h.has fSigOpen then
    if wasNormal && !isWsB c && c != 35 then
      { h with sv := (lowerB c).toUInt64, sl := 1, fl := h.fl ||| fSigOpen }
    else h
  else if h.sl < 7 then
    { h with sv := h.sv ||| ((lowerB c).toUInt64 <<< (8 * h.sl.toUInt64)), sl := h.sl + 1 }
  else h

/-- Whether the innermost open bracket is the `(` of a collection. -/
@[inline] def Hot.inCollection (h : Hot) : Bool :=
  h.depth > 0 && h.depth ≤ 63 && (h.bstack >>> (h.depth - 1).toUInt64) &&& 1 == 1

/-- A byte read in the normal mode: brackets, annotations, and the blank nodes
    the reader mints (`TurtleState.freshBnode`): one for each `[` (`[]`, a
    property list, a `[]` graph label), and one for each item of a collection
    (its cell). An item starts at a byte that is not white space, `#`, `,`,
    `;`, `)`, `]`, `@` (a language tag) or `^` (`^^`: the datatype after it
    belongs to the same item), when no item is open. `~` and `{|` mint blank
    nodes this scan does not count (`fUncounted`). -/
@[inline] def Hot.brackets (h : Hot) (c : UInt8) : Hot :=
  let h :=
    if !h.inCollection then h
    else if isWsB c || c == 35 || c == 44 || c == 59 then h.set fInItem false
    else if c == 41 || c == 93 then h
    else if c == 94 then (h.set fInItem true).set fAttach true
    else if h.has fAttach then (h.set fAttach false).set fInItem true
    else if c == 64 then h.set fInItem true
    else if h.has fInItem then h
    else { h with mints := h.mints + 1, fl := h.fl ||| fInItem }
  if c == 91 || c == 40 then
    let d := h.depth
    let one : UInt64 := (1 : UInt64) <<< d.toUInt64
    let bstack := if c == 40 then h.bstack ||| one else h.bstack &&& ~~~one
    let mints := if c == 91 then h.mints + 1 else h.mints
    let fl := (h.fl ||| fCandBr ||| (if d ≥ 62 then fUncounted else 0)) &&& ~~~(fInItem ||| fAttach)
    { h with depth := d + 1, bstack, mints, fl }
  else if c == 93 || c == 41 then
    { h with depth := if h.depth == 0 then 0 else h.depth - 1, fl := (h.fl ||| fInItem) &&& ~~~fAttach }
  else if c == 124 && h.has fPrevBrace then { h with annot := h.annot + 1, fl := h.fl ||| fUncounted }
  else if c == 125 && h.has fPrevBar then { h with annot := if h.annot == 0 then 0 else h.annot - 1 }
  else if c == 126 then h.set fUncounted true
  else h

/-- `StatementScan.feedChar` on a byte, with the tracking. -/
@[inline] def Hot.inner (h : Hot) (c : UInt8) : Hot :=
  if h.has fDot && (isWsB c || c == 35) then
    let h := (h.endCand eDot).set fDot false
    let h := h.stepMode c
    h.pushHeads c true
  else if h.mode == 0 && !h.has fDot && (c == 10 || c == 13) && headIsDirective h.hv h.hl then
    let h := h.endCand eLine
    h.pushHeads c true
  else
    let wasNormal := h.mode == 0
    -- a statement right after a `.` can be a directive
    let h := if h.has fDot && (c == 64 || c == 112 || c == 80 || c == 98 || c == 66 || c == 118 || c == 86)
      then h.set fCandDir true else h
    let h := h.stepMode c
    let h :=
      if wasNormal then
        let h := h.brackets c
        (h.set fPrevBrace (c == 123)).set fPrevBar (c == 124)
      else { h with fl := h.fl &&& ~~~(fPrevBrace ||| fPrevBar) }
    let h := h.pushHeads c wasNormal
    h.set fDot (h.mode == 0 && c == 46)

/-- `TriGScan.plainChar`. -/
@[inline] def Hot.plain (h : Hot) (c : UInt8) : Hot :=
  let wasNormal := h.mode == 0
  let h := h.inner c
  (h.set fNameEsc (wasNormal && c == 92)).set fAfterBar (wasNormal && c == 124)

def resetBlock : UInt32 := fDot ||| fNameEsc ||| fHeld ||| fAfterBar ||| fPrevBrace ||| fPrevBar

/-- `TriGScan.openHeld`: the held `{` opens a graph block. -/
@[inline] def Hot.openHeld (h : Hot) : Hot :=
  let h := h.endCand eOpen
  { h with mode := 0, fl := (h.fl &&& ~~~resetBlock) ||| fBlock }

/-- `TriGScan.stepChar` on a byte. -/
@[inline] def Hot.trigStep (h : Hot) (c : UInt8) : Hot :=
  if h.has fNameEsc then
    let h := h.inner c
    { h with mode := 0, fl := h.fl &&& ~~~(fDot ||| fNameEsc ||| fAfterBar) }
  else if h.mode == 0 && c == 123 && !h.has fBlock then
    { h with fl := (h.fl ||| fHeld) &&& ~~~fAfterBar }
  else if h.mode == 0 && c == 125 && h.has fBlock && !h.has fAfterBar then
    let h := h.endCand eClose
    { h with mode := 0, fl := h.fl &&& ~~~(resetBlock ||| fBlock) }
  else h.plain c

/-- One byte. -/
@[inline] def Hot.step (h : Hot) (c : UInt8) : Hot :=
  let run := if c == 95 then h.run + 1 else 0
  let dlt := h.has fPrevLt && c == 60
  let fl := (h.fl &&& ~~~fPrevLt) ||| (if c == 60 then fPrevLt else 0) ||| (if dlt then fDoubleLt else 0)
  let h := { h with run, longest := if run > h.longest then run else h.longest, fl, ev := 0 }
  if !h.has fTrig then h.inner c
  else if h.has fHeld && c == 124 then
    -- `{|`: both bytes belong to the statement
    let h := h.set fHeld false
    (h.plain 123).plain c
  else
    let h := if h.has fHeld then h.openHeld else h
    h.trigStep c

/-! ## The rest of the state, changed only at events -/

structure Cold where
  targets : Array Nat
  nextTarget : Nat := 0
  candStart : Nat := 0
  headerStart : Nat := 0
  headerStop : Nat := 0
  headerOk : Bool := false
  splits : Array Split := #[]
  directives : Array Unit := #[]
  deriving Inhabited

/-- Offer a split at `p` when `p` reaches the next target. -/
def Cold.offer (k : Cold) (h : Hot) (p : Nat) : Cold :=
  if h.depth == 0 && h.annot == 0 && k.nextTarget < k.targets.size && p ≥ k.targets[k.nextTarget]!
      && (!h.has fBlock || k.headerOk) then
    let block := if h.has fBlock then some (k.headerStart, k.headerStop) else none
    let sp : Split := { pos := p, directives := k.directives.size, block, counter := h.mints.toNat }
    let rec skip (fuel i : Nat) : Nat :=
      match fuel with
      | 0 => i
      | f + 1 => if i < k.targets.size && k.targets[i]! ≤ p then skip f (i + 1) else i
    { k with splits := k.splits.push sp, nextTarget := skip k.targets.size k.nextTarget }
  else k

/-- The events of the byte at `p`. -/
def Cold.handle (k : Cold) (h : Hot) (p : Nat) : Cold :=
  let dir := h.has fSavedDir
  let k :=
    if h.ev &&& eOpen != 0 then
      let brace := p - 1
      let ok := !dir && !h.has fSavedBr && h.depth == 0 && h.annot == 0
      let dirs := if dir then k.directives.push { start := k.candStart, stop := brace, header := true }
        else k.directives
      { k with headerStart := k.candStart, headerStop := brace, headerOk := ok, directives := dirs,
               candStart := p }
    else k
  let k :=
    if h.ev &&& (eDot ||| eLine) != 0 then
      let dirs := if dir && !h.has fBlock then
          k.directives.push { start := k.candStart, stop := p, header := false } else k.directives
      let k := { k with directives := dirs, candStart := p }
      if h.ev &&& eDot != 0 then k.offer h p else k
    else k
  if h.ev &&& eClose != 0 then { k with candStart := p + 1, headerOk := false } else k

/-! ## The loop -/

/-- The scanner between two chunks. -/
structure State where
  hot : Hot
  cold : Cold
  pos : Nat := 0
  deriving Inhabited

/-- Whether the next bytes may be read by `fastRun`: both heads are full, and
    no flag waits for the next byte. -/
@[inline] def Hot.canSkip (h : Hot) : Bool :=
  h.hl == 7 && h.sl == 7 && h.mode != 2 && !h.inCollection &&
    h.fl &&& (fDot ||| fNameEsc ||| fHeld ||| fStrEsc) == 0 && h.closing == 0

@[inline] def packRun (i : USize) (mode quote : UInt8) : UInt64 :=
  (i.toUInt64 <<< 16) ||| (mode.toUInt64 <<< 8) ||| quote.toUInt64

/-- The bytes from `i` that change only the lexical mode, read with scalar
    state and no allocation; the result packs the index of the first byte
    that `Hot.step` must read, the mode and the quote (`packRun`). Read here:
    in the normal mode, name bytes, white space (a line end only when `nl`,
    the head is not a SPARQL directive), `;`, `,`, `^`, `@`, a `<` that opens
    an IRIREF (not `<<`), a quote that opens a short string; in an IRIREF,
    any byte but `<` (the closing `>` returns to the normal mode); in a short
    string, any byte but the quote (which closes it) and `\` (a `\` and the
    byte after it, when that byte is neither `_` nor `<`). A `_` (the
    underscore run) and every other byte stop the run. With `nl`, as in the
    reader: a line end in the normal mode ends a candidate only after a
    directive head. -/
def fastRun (bytes : ByteArray) (nl : Bool) (i : USize) (mode quote : UInt8) : UInt64 :=
  if hi : i < bytes.usize then
    let c := bytes.uget i (L4Factoidal.Prim.Bytes.usize_lt_size hi)
    if c == 95 then packRun i mode quote
    else match mode with
    | 0 =>
      if (c ≥ 97 && c ≤ 122) || (c ≥ 65 && c ≤ 90) || (c ≥ 48 && c ≤ 58) || c ≥ 128 || c == 32 ||
          c == 9 || c == 45 || c == 59 || c == 44 || c == 94 || c == 64 || (nl && (c == 10 || c == 13)) then
        fastRun bytes nl (i + 1) 0 quote
      else
        let next : UInt8 := if h2 : i + 1 < bytes.usize then
            bytes.uget (i + 1) (L4Factoidal.Prim.Bytes.usize_lt_size h2) else 0
        if c == 60 && next != 60 && next != 0 then fastRun bytes nl (i + 1) 1 quote
        else if (c == 34 || c == 39) && next != c && next != 92 && next != 0 && next != 95 && next != 60 then
          fastRun bytes nl (i + 1) 5 c
        else packRun i mode quote
    | 1 =>
      if c == 60 then packRun i mode quote
      else if c == 62 then fastRun bytes nl (i + 1) 0 quote
      else fastRun bytes nl (i + 1) 1 quote
    | 5 =>
      if c == 60 then packRun i mode quote
      else if c == quote then fastRun bytes nl (i + 1) 0 quote
      else if c == 92 then
        if h2 : i + 1 < bytes.usize then
          let b := bytes.uget (i + 1) (L4Factoidal.Prim.Bytes.usize_lt_size h2)
          if b == 95 || b == 60 then packRun i mode quote
          else fastRun bytes nl ((i + 1) + 1) 5 quote
        else packRun i mode quote
      else fastRun bytes nl (i + 1) 5 quote
    | _ => packRun i mode quote
  else packRun i mode quote
termination_by bytes.usize.toNat - i.toNat
decreasing_by
  all_goals first
    | (have := L4Factoidal.Prim.Bytes.usize_succ_toNat hi
       have := USize.lt_iff_toNat_lt.mp hi
       omega)
    | (have := L4Factoidal.Prim.Bytes.usize_succ_toNat h2
       have := L4Factoidal.Prim.Bytes.usize_succ_toNat hi
       have := USize.lt_iff_toNat_lt.mp h2
       omega)

/-- The state after a `fastRun` that read at least one byte: the mode and the
    quote it ended with, no `_` run, and no flag that holds the last byte. -/
@[inline] def Hot.afterRun (h : Hot) (mode quote : UInt8) : Hot :=
  { h with mode, quote, run := 0, fl := h.fl &&& ~~~(fPrevLt ||| fPrevBrace ||| fPrevBar ||| fAfterBar) }

/-- Read bytes `[i, n)` of a chunk whose first byte is at `base` in the
    document (`skills/lean4-performance`): runs that `fastRun` can read go
    through it, with no allocation; each other byte through `Hot.step`.
    Each round reads at least one byte, so `fuel` = the chunk size + 1 is
    enough. -/
def loop (bytes : ByteArray) (base : Nat) (fuel : Nat) (i : USize) (h : Hot) (k : Cold) : Hot × Cold :=
  match fuel with
  | 0 => (h, k)
  | fuel + 1 =>
    let (j, h) :=
      if h.canSkip then
        let r := fastRun bytes (!headIsDirective h.hv h.hl) i h.mode h.quote
        let j := (r >>> 16).toUSize
        if j != i then (j, h.afterRun (r >>> 8).toUInt8 r.toUInt8) else (i, h)
      else (i, h)
    if hj : j < bytes.usize then
      let c := bytes.uget j (L4Factoidal.Prim.Bytes.usize_lt_size hj)
      let h := h.step c
      let k := if h.ev == 0 then k else k.handle h (base + j.toNat)
      loop bytes base fuel (j + 1) h k
    else (h, k)

/-- A scanner at the start of a document. `targets` are the byte positions
    near which splits are wanted, in increasing order. -/
def State.init (trig : Bool) (targets : Array Nat) : State :=
  { hot := { fl := if trig then fTrig else 0 }, cold := { targets } }

/-- Read a chunk of bytes. -/
def State.feed (s : State) (bytes : ByteArray) : State :=
  let (hot, cold) := loop bytes s.pos (bytes.size + 1) 0 s.hot s.cold
  { hot, cold, pos := s.pos + bytes.size }

/-- The plan, once every byte is read. -/
def State.finish (s : State) : Plan :=
  { splits := s.cold.splits, directives := s.cold.directives,
    longestUnderscore := s.hot.longest.toNat, doubleLt := s.hot.has fDoubleLt,
    mints := s.hot.mints.toNat, uncounted := s.hot.has fUncounted }

/-- The plan of a whole document. -/
def planOf (trig : Bool) (targets : Array Nat) (bytes : ByteArray) : Plan :=
  ((State.init trig targets).feed bytes).finish

/-- Every dot boundary that can be a split: the plan with a target at every
    byte. -/
def allSplits (trig : Bool) (bytes : ByteArray) : Plan :=
  planOf trig (Array.range (bytes.size + 1)) bytes

/-! ## Build-time checks -/

private def posOf (trig : Bool) (doc : String) : List Nat :=
  ((allSplits trig doc.toUTF8).splits.map (·.pos)).toList

-- a dot in a string, an IRI, a comment, a long string, a number and a name is not a boundary
#guard posOf false "<a> <b> \"x. y\" . <c> <d> <e#.f> . # x. y\n<g> <h> \"\"\"a. \"\" .\"\"\" .\n" == [16, 33, 64]
#guard posOf false "<a> <b> 1.5 . <a> <b> p:x.y ." == [13]
-- inside brackets and collections there is no split
#guard posOf false "<a> <b> [ <c> <d> ] . <a> <b> ( 1 2 ) ." == [21]
-- a TriG block: splits inside a block with a plain header, none inside `[] {`
#guard posOf true "<g> { <a> <b> <c> . <a> <b> <d> . } [] { <a> <b> <c> . <a> <b> <e> . }" == [19, 33]
#guard ((allSplits true "<g> { <a> <b> <c> . <a> <b> <d> . }".toUTF8).splits.map (·.block)).toList ==
  [some (0, 4), some (0, 4)]
-- an annotation block of RDF 1.2 is not a graph block
#guard posOf true "<a> <b> <c> {| <d> <e> |} . <f> <g> <h> ." == [27]
-- directive units: `@prefix`, SPARQL `PREFIX` on its own line, and a directive after a statement
#guard ((allSplits false "@prefix p: <x> .\nPREFIX q: <y>\n<a> <b> <c> .\n<a> <b> \"x\".@base <z> .\n".toUTF8).directives.map
    (fun u => (u.start, u.stop))).toList == [(0, 16), (16, 30), (44, 68)]
-- a language tag is not a directive
#guard ((allSplits false "<a> <b> \"x\"@en . <a> <b> \"y\"@prefixx .".toUTF8).directives).size == 0
-- the minted blank nodes: `[]`, and in the collection six cells and one `[ ... ]`
#guard (allSplits false "[] <p> ( <a> [ <q> <r> ] ( ) \"x\"^^<dt> \"y\" @en 1.5 ) .".toUTF8).mints == 8
#guard (allSplits false "<a> <b> <c> ~ <r> .".toUTF8).uncounted
-- the underscore run and `<<`
#guard (allSplits false "_:a__b <p> <o> .".toUTF8).longestUnderscore == 2
#guard (allSplits false "<< <a> <b> <c> >> <p> <o> .".toUTF8).doubleLt

end L4Factoidal.Syntax.SplitScan
