/-
L4Factoidal.Syntax.LangTagWarnings — the warnings of a reader for a language
tag that is not well-formed under BCP 47.

Decision (owner, 2026-10-24), the answer "B." to the question on
https://github.com/danbri/factoidal/issues/1004 and
https://github.com/danbri/factoidal/issues/1005, where option (b) was: "Jena
style: the readers keep the triple and warn, and the writers write the tag
unchanged." Record: CLAUDE.md, "Ill-formed BCP 47 language tags (owner,
2026-10-24)".

Specifications:
* RDF 1.2 Concepts section 3.4 (RDF 1.1 Concepts section 3.3): a language tag
  MUST be well-formed per BCP 47 section 2.2.9.
* RDF 1.2 N-Triples section 6.4 leaves "Error detection, reporting, and
  recovery" to implementors.
* The predicate is `RDF.isWellFormedLangTag` (`RDF/LangTag.lean`, the ABNF of
  BCP 47 section 2.1 with the grandfathered tags of section 2.2.8). It is the
  only BCP 47 well-formedness predicate the readers use.

What a reader does: a tag that its concrete-syntax grammar reads (LANGTAG
[144s] of RDF 1.1; LANG_DIR of RDF 1.2) and that is not well-formed is kept in
the triple, and the reader gives one warning per occurrence that names the tag
and its position. One exception, decided by the W3C test suite: the RDF 1.2
N-Triples negative syntax test `ntriples-langdir-bad-4` (`"Hello"@cantbethislong`)
requires the RDF 1.2 readers to refuse a subtag of more than 8 characters
(`Syntax.Lexing.validLangSubtags`), so that case stays a syntax error in RDF 1.2
mode and is read with a warning in RDF 1.1 mode.

## The position

The readers do not keep the position of a term. `scanLangTags` finds the
position of each `@tag` that follows a string literal in a document of the
N-Triples family (N-Triples, N-Quads, Turtle, TriG): a walk over the UTF-8
bytes that knows IRIs, comments, the four string forms with their escapes, and
the white space that RDF 1.2 allows between a string and its `@`. It takes the
bytes in chunks (`LangScanState.feed`), so a streamed reader can run it on the chunks
it reads. The walk is a loop: one call on itself per byte, each a tail call.

`langTagWarnings` gives the warnings of a parsed document: the ill-formed tags
of the dataset (`illFormedTagsOf`), each occurrence the walk finds with its
position, and, for a tag of the dataset that the walk does not find (RDF/XML,
JSON-LD), one warning at the first place its text occurs in the document (the
start of the document when it does not occur).

`offset`, `line` and `column` follow `Syntax/Diagnostics.lean`: offset 0-based in
Unicode scalar values, line 1-based at LINE FEED, column 1-based in Unicode
scalar values. The position is the first character of the tag (after `@`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.LangTag
import L4Factoidal.RDF.Graph
import L4Factoidal.Syntax.Diagnostics

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## The walk over the bytes -/

/-- Where the walk is. -/
inductive LangScanMode where
  /-- Between tokens. -/
  | normal
  /-- Inside `<...>`. -/
  | iri
  /-- After `#`, to the end of the line. -/
  | comment
  /-- Inside a short string that the quote byte `q` closes. -/
  | short (q : UInt8)
  /-- Inside a long string that three quote bytes `q` close. -/
  | long (q : UInt8)
  /-- After the closing quote of a string, before any byte other than white
  space. -/
  | afterString
  /-- Inside the characters of a language tag after `@`. -/
  | inTag
  deriving DecidableEq, Repr, Inhabited

/-- One `@tag` found: the characters after `@` (the tag and, in RDF 1.2, the
base direction) and the position of the first of them. -/
structure FoundTag where
  raw : String
  offset : Nat
  line : Nat
  column : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The state of the walk between two chunks. -/
structure LangScanState where
  mode : LangScanMode := .normal
  /-- Unicode scalar values before the next byte. -/
  offset : Nat := 0
  line : Nat := 1
  column : Nat := 1
  /-- `inTag`: the position of the tag and its characters so far. -/
  tagOffset : Nat := 0
  tagLine : Nat := 1
  tagColumn : Nat := 1
  tagChars : String := ""
  /-- Bytes of the last chunk that the walk keeps for the next one (at most
  3: a step looks at up to 4 bytes). -/
  carry : ByteArray := ByteArray.empty
  /-- The tags found, in document order. -/
  found : Array FoundTag := #[]
  /-- Record every tag; otherwise only the tags `RDF.isWellFormedLangTag`
  refuses (a streamed read then keeps memory for its warnings only). -/
  keepAll : Bool := false
  /-- The last tag found well-formed: a document repeats few tags, so the
  check runs once for each run of the same tag. -/
  lastWellFormed : String := ""
  deriving Inhabited

namespace LangScanState

/-- The state after the byte `b`: a UTF-8 continuation byte does not start a
character; LINE FEED starts a line. -/
@[inline] def advance (st : LangScanState) (b : UInt8) : LangScanState :=
  if b &&& 0xC0 == 0x80 then st
  else if b == 10 then { st with offset := st.offset + 1, line := st.line + 1, column := 1 }
  else { st with offset := st.offset + 1, column := st.column + 1 }

/-- The tag of `inTag`, recorded when it has a character. -/
def closeTag (st : LangScanState) : LangScanState :=
  let st' := { st with mode := .normal, tagChars := "" }
  if st.tagChars.isEmpty then st'
  else if !st.keepAll && st.tagChars == st.lastWellFormed then st'
  else if !st.keepAll && isWellFormedLangTag ((st.tagChars.splitOn "--").headD st.tagChars) then
    { st' with lastWellFormed := st.tagChars }
  else
    let f : FoundTag :=
      { raw := st.tagChars, offset := st.tagOffset, line := st.tagLine, column := st.tagColumn }
    { st' with found := st.found.push f }

end LangScanState

@[inline] private def isTagByte (b : UInt8) : Bool :=
  (b ≥ 'a'.toNat.toUInt8 && b ≤ 'z'.toNat.toUInt8) ||
  (b ≥ 'A'.toNat.toUInt8 && b ≤ 'Z'.toNat.toUInt8) ||
  (b ≥ '0'.toNat.toUInt8 && b ≤ '9'.toNat.toUInt8) || b == '-'.toNat.toUInt8

@[inline] private def isWsByte (b : UInt8) : Bool := b == 32 || b == 9 || b == 10 || b == 13

private def bLt : UInt8 := '<'.toNat.toUInt8
private def bGt : UInt8 := '>'.toNat.toUInt8
private def bHash : UInt8 := '#'.toNat.toUInt8
private def bDq : UInt8 := '"'.toNat.toUInt8
private def bSq : UInt8 := '\''.toNat.toUInt8
private def bBs : UInt8 := '\\'.toNat.toUInt8
private def bAt : UInt8 := '@'.toNat.toUInt8

/-- The byte at `i`, when there is one. -/
@[inline] def langByteAt? (bs : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < bs.size then some bs[i] else none

/-- Consume the bytes `bs[i]`, ..., `bs[i + n - 1]`. Tail recursive. -/
def langAdvanceN (bs : ByteArray) : Nat → Nat → LangScanState → LangScanState
  | 0, _, st => st
  | n + 1, i, st => langAdvanceN bs n (i + 1) (st.advance (bs.get! i))

/-- A byte that the mode `m` must look at; every other byte only moves the
position. -/
@[inline] def langSpecial (m : LangScanMode) (b : UInt8) : Bool :=
  match m with
  | .normal => b == bLt || b == bHash || b == bDq || b == bSq || b == bBs
  | .iri => b == bGt
  | .comment => b == 10 || b == 13
  | .short q => b == q || b == bBs
  | .long q => b == q || b == bBs
  | .afterString => true
  | .inTag => true

/-- Move over the bytes from `i` up to the next byte that `m` must look at (or
the end), counting offset, line and column. A tail-recursive loop with the
position in its arguments. -/
def langSkipPlain (bs : ByteArray) (m : LangScanMode) :
    Nat → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, i, off, line, col => (i, off, line, col)
  | fuel + 1, i, off, line, col =>
    if h : i < bs.size then
      let b := bs[i]
      if langSpecial m b then (i, off, line, col)
      else if b &&& 0xC0 == 0x80 then langSkipPlain bs m fuel (i + 1) off line col
      else if b == 10 then langSkipPlain bs m fuel (i + 1) (off + 1) (line + 1) 1
      else langSkipPlain bs m fuel (i + 1) (off + 1) line (col + 1)
    else (i, off, line, col)

/-- The walk over `bs` from index `i`. `final`: no chunk follows, so a step
may look past the end (it sees no byte there); otherwise the walk stops when
fewer than 4 bytes are left and keeps them in `carry`. `fuel` bounds the
number of steps: every step consumes a byte except a change of mode out of
`afterString` or `inTag`, which follows a step that consumed one, so
`2 * bs.size + 2` steps are enough. Every call on itself is a tail call. -/
def langScanLoop (bs : ByteArray) (final : Bool) : Nat → Nat → LangScanState → LangScanState
  | 0, _, st => st
  | fuel + 1, i, st =>
    if i ≥ bs.size then st
    else if !langSpecial st.mode (bs.get! i) then
      let (j, off, line, col) := langSkipPlain bs st.mode (bs.size - i) i st.offset st.line st.column
      langScanLoop bs final fuel j { st with offset := off, line := line, column := col }
    else if !final && bs.size - i < 4 then { st with carry := bs.extract i bs.size }
    else
      let b := bs.get! i
      let at1 := langByteAt? bs (i + 1)
      let at2 := langByteAt? bs (i + 2)
      let at3 := langByteAt? bs (i + 3)
      match st.mode with
      | .normal =>
          if b == bLt then
            if at1 == some bLt then langScanLoop bs final fuel (i + 2) (langAdvanceN bs 2 i st)
            else langScanLoop bs final fuel (i + 1) { st.advance b with mode := .iri }
          else if b == bHash then langScanLoop bs final fuel (i + 1) { st.advance b with mode := .comment }
          else if b == bDq || b == bSq then
            if at1 == some b && at2 == some b then
              langScanLoop bs final fuel (i + 3) { langAdvanceN bs 3 i st with mode := .long b }
            else if at1 == some b then
              langScanLoop bs final fuel (i + 2) { langAdvanceN bs 2 i st with mode := .afterString }
            else langScanLoop bs final fuel (i + 1) { st.advance b with mode := .short b }
          else if b == bBs then langScanLoop bs final fuel (i + 2) (langAdvanceN bs 2 i st)
          else langScanLoop bs final fuel (i + 1) (st.advance b)
      | .iri =>
          if b == bGt then langScanLoop bs final fuel (i + 1) { st.advance b with mode := .normal }
          else langScanLoop bs final fuel (i + 1) (st.advance b)
      | .comment =>
          if b == 10 || b == 13 then langScanLoop bs final fuel (i + 1) { st.advance b with mode := .normal }
          else langScanLoop bs final fuel (i + 1) (st.advance b)
      | .short q =>
          if b == bBs then langScanLoop bs final fuel (i + 2) (langAdvanceN bs 2 i st)
          else if b == q then langScanLoop bs final fuel (i + 1) { st.advance b with mode := .afterString }
          else langScanLoop bs final fuel (i + 1) (st.advance b)
      | .long q =>
          if b == bBs then langScanLoop bs final fuel (i + 2) (langAdvanceN bs 2 i st)
          else if b == q && at1 == some q && at2 == some q then
            -- Four quotes: the first is a character of the string.
            if at3 == some q then langScanLoop bs final fuel (i + 1) (st.advance b)
            else langScanLoop bs final fuel (i + 3) { langAdvanceN bs 3 i st with mode := .afterString }
          else langScanLoop bs final fuel (i + 1) (st.advance b)
      | .afterString =>
          if isWsByte b then langScanLoop bs final fuel (i + 1) (st.advance b)
          else if b == bAt then
            let st' := st.advance b
            langScanLoop bs final fuel (i + 1)
              { st' with mode := .inTag, tagOffset := st'.offset, tagLine := st'.line,
                         tagColumn := st'.column, tagChars := "" }
          else langScanLoop bs final fuel i { st with mode := .normal }
      | .inTag =>
          if isTagByte b then
            langScanLoop bs final fuel (i + 1)
              { st.advance b with tagChars := st.tagChars.push (Char.ofNat b.toNat) }
          else langScanLoop bs final fuel i st.closeTag

namespace LangScanState

/-- Walk the next chunk. `final`: it is the last one; a tag open at its end is
recorded. -/
def feed (st : LangScanState) (chunk : ByteArray) (final : Bool) : LangScanState :=
  let bs := st.carry ++ chunk
  let st0 := { st with carry := ByteArray.empty }
  let st1 := langScanLoop bs final (2 * bs.size + 2) 0 st0
  if final && st1.mode == .inTag then st1.closeTag else st1

end LangScanState

/-- Every `@tag` after a string literal in `text`, a document of the N-Triples
family, with its position. -/
def scanLangTags (text : String) : Array FoundTag :=
  (({ keepAll := true } : LangScanState).feed text.toUTF8 true).found

/-- The language tag of a found `@tag`: the characters before `--` (RDF 1.2
LANG_DIR writes the base direction after `--`). -/
def FoundTag.tag (f : FoundTag) : String :=
  (f.raw.splitOn "--").headD f.raw

/-! ## Warnings -/

/-- The warning text for `tag`. -/
def langTagWarningMessage (tag : String) : String :=
  s!"the language tag \"{tag}\" is not well-formed (BCP 47 section 2.2.9, required by RDF 1.2 Concepts section 3.4); the triple is kept and the tag is written unchanged"

/-- The warning for a found tag. -/
def FoundTag.warning (f : FoundTag) : Diagnostic :=
  { cls := .illFormedLangTag, message := langTagWarningMessage f.tag,
    offset := f.offset, line := f.line, column := f.column }

/-- The found tags that are not well-formed, as warnings: what a streamed
reader, which keeps no dataset, reports. -/
def warningsOfFound (found : Array FoundTag) : List Diagnostic :=
  (found.toList.filter fun f => !isWellFormedLangTag f.tag).map FoundTag.warning

/-- The language tag of the literal at the end of `t`: a triple term's object
in turn (a tail call for each level of nesting). -/
def Term.innerLangTag? : Term → Option String
  | .literal wl => wl.val.langTag
  | .tripleTerm _ _ o => Term.innerLangTag? o
  | _ => none

/-- Add the ill-formed tag of each triple of `g` to `acc` (lower case, each
once). -/
def addIllFormedTags (acc : List String) : Graph → List String
  | [] => acc
  | t :: rest =>
      match Term.innerLangTag? t.o with
      | some tag =>
          let lo := tag.toLower
          if !isWellFormedLangTag tag && !acc.contains lo then addIllFormedTags (lo :: acc) rest
          else addIllFormedTags acc rest
      | none => addIllFormedTags acc rest

/-- The language tags of `ds` that are not well-formed, in lower case, each
once. -/
def illFormedTagsOf (ds : Dataset) : List String :=
  ds.named.foldl (fun acc ng => addIllFormedTags acc ng.graph) (addIllFormedTags [] ds.default)

/-- 1-based line and column of codepoint `offset` in `cs`. Tail recursive. -/
def lineColumnAt : List Char → Nat → Nat → Nat → Nat × Nat
  | [], _, line, col => (line, col)
  | _, 0, line, col => (line, col)
  | c :: cs, n + 1, line, col =>
      if c == '\n' then lineColumnAt cs n (line + 1) 1 else lineColumnAt cs n line (col + 1)

/-- The warning for `tag` at the first place its text occurs in `text` (case
not compared), or at the start of the document. -/
def warningAtFirstOccurrence (text : String) (tag : String) : Diagnostic :=
  let pieces := text.toLower.splitOn tag.toLower
  let offset := if pieces.length > 1 then (pieces.headD "").length else 0
  let (line, col) := lineColumnAt text.toList offset 1 1
  { cls := .illFormedLangTag, message := langTagWarningMessage tag,
    offset, line, column := col }

/-- The warnings of a parsed document `text` whose dataset is `ds`. `scan`:
the document is of the N-Triples family, so the walk finds each occurrence. -/
def langTagWarnings (scan : Bool) (text : String) (ds : Dataset) : List Diagnostic :=
  match illFormedTagsOf ds with
  | [] => []
  | bad =>
      -- Only the ill-formed tags are recorded (no `keepAll`).
      let found := if scan then (({} : LangScanState).feed text.toUTF8 true).found.toList else []
      let hits := found.filter fun f => bad.contains f.tag.toLower
      let seen := hits.map (·.tag.toLower)
      hits.map FoundTag.warning ++
        (bad.reverse.filter (!seen.contains ·)).map (warningAtFirstOccurrence text)

/-! ## Build-time checks -/

-- The walk: a tag after a string, its position the character after `@`.
#guard (scanLangTags "<a> <b> \"x\"@en .\n").toList.map (fun f => (f.raw, f.offset, f.line, f.column))
  == [("en", 12, 1, 13)]
-- Base direction: the tag is the part before `--`.
#guard (scanLangTags "<a> <b> \"x\"@ar--rtl .").toList.map FoundTag.tag == ["ar"]
-- White space before `@` (RDF 1.2); the second line.
#guard (scanLangTags "<a> <b> <c> .\n<a> <b> \"x\" @abcdefghijk .").toList.map
  (fun f => (f.raw, f.line, f.column)) == [("abcdefghijk", 2, 14)]
-- `@prefix` is not after a string; `#` comments and IRIs hide `"`.
#guard (scanLangTags "@prefix p: <http://e/\"x\"@zz> . # \"y\"@qq\np:a p:b 'v'@de-CH-1901 .").toList.map
  FoundTag.tag == ["de-CH-1901"]
-- Escaped quotes inside strings; long strings, one ending with a quote.
#guard (scanLangTags "<a> <b> \"a\\\"@no\"@en, \"\"\"x\"@no\"\"\"\"@fr, ''@it .").toList.map
  FoundTag.tag == ["en", "fr", "it"]
-- A multi-byte character counts one column.
#guard (scanLangTags "<a> <b> \"é\"@en .").toList.map (·.column) == [13]
-- The same tags, in chunks of every size.
private def chunked (text : String) (n : Nat) : List String :=
  let bs := text.toUTF8
  let rec go (fuel i : Nat) (st : LangScanState) : LangScanState :=
    match fuel with
    | 0 => st
    | fuel + 1 =>
        if i + n ≥ bs.size then st.feed (bs.extract i bs.size) true
        else go fuel (i + n) (st.feed (bs.extract i (i + n)) false)
  ((go (bs.size + 1) 0 { keepAll := true }).found.toList.map fun f => s!"{f.raw}@{f.offset}")
private def chunkDoc : String :=
  "@prefix p: <http://e/> .\np:a p:b \"\"\"x\"\"\"\"@en-GB, \"y\" @ab--ltr, 'é'@xyz-a .\n"
#guard [1, 2, 3, 4, 5, 7, 64].all fun n => chunked chunkDoc n == chunked chunkDoc 1000

-- Without `keepAll` the walk keeps only the ill-formed tags.
#guard ((({} : LangScanState).feed "<a> <b> \"x\"@en, \"y\"@abcdefghijk .".toUTF8 true).found.toList.map
  FoundTag.tag) == ["abcdefghijk"]

-- The BCP 47 cases of the decision record (BCP 47 section 2.1).
#guard isWellFormedLangTag "en"
#guard isWellFormedLangTag "de-CH-1901"
#guard isWellFormedLangTag "zh-Hant-TW"
#guard isWellFormedLangTag "x-private"
#guard isWellFormedLangTag "i-klingon"
#guard !isWellFormedLangTag "abcdefghijk"
#guard !isWellFormedLangTag "en--"
#guard !isWellFormedLangTag "123"

end L4Factoidal.Syntax
