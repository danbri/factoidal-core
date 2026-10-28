/-
L4Factoidal.FullText.Tokenize — the tokenizer of the full-text
implementation (XQuery and XPath Full Text 3.0 §4.1: tokenization is
implementation-defined, within the constraints listed there).

The rules of this implementation:

* a token is a maximal run of word characters: Unicode General Category
  L (letters), M (marks) or N (numbers), from the tables of the shared
  regular-expression engine (`Regex.XPath40.categoryRanges`); every other
  character separates tokens. A Han ideograph, a Hiragana or a Katakana
  character is a token by itself (these scripts write no spaces between
  words), so a query for a Chinese word is a phrase of its characters;
* each token has one position; positions are consecutive from 1, so a
  phrase is a run of consecutive positions;
* a sentence ends after a token that is followed (before the next token)
  by `.`, `!` or `?`; sentences are numbered from 1;
* a paragraph ends at an element boundary: the text of a node is given as
  segments (the text nodes, in document order), and each segment after
  the first starts a new paragraph, and so a new sentence (§4.1: "taking
  any structural information of the item into account"; the qt4tests
  feature `fullText-units`: "element boundaries … treated as Full Text
  sentence and paragraph boundaries"). A boundary inside a token (a word
  character on both sides, as in `<b>p</b>rototypes`) does not split the
  token, because tokens come from the string value (§4.1). Paragraphs are
  numbered from 1.

Query strings are tokenized with the same word rule (`queryTokens`); when
the wildcard option is on, a `.` with its indicator and an escaped word
character are kept in the token (`queryTokensWild`).
-/
import L4Factoidal.Regex.XPath40
import L4Factoidal.Text.CaseMap

namespace L4Factoidal.FullText

/-- The ranges of the word characters (categories L, M and N), sorted and
    merged, as an array for binary search. -/
def wordRangeArr : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ =>
  (Text.CaseMap.normalizeRanges
    (((Regex.XPath40.categoryRanges "L").getD []) ++ ((Regex.XPath40.categoryRanges "M").getD []) ++
      ((Regex.XPath40.categoryRanges "N").getD []))).toArray

/-- The ranges of the non-spacing marks (category Mn). -/
def markRangeArr : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ =>
  (Text.CaseMap.normalizeRanges ((Regex.XPath40.categoryRanges "Mn").getD [])).toArray

/-- Is `c` in one of the sorted ranges `a`? A binary search on the range
    starts, by a loop with a bounded number of steps. -/
def inRanges (a : Array (Nat × Nat)) (c : Nat) : Bool := Id.run do
  let mut lo := 0
  let mut hi := a.size
  for _ in [0:64] do
    if lo ≥ hi then break
    let mid := (lo + hi) / 2
    let (s, e) := a.getD mid (0, 0)
    if c < s then hi := mid
    else if c > e then lo := mid + 1
    else return true
  return false

/-- A word character: General Category L, M or N. ASCII has a fast path. -/
def isWordChar (c : Char) : Bool :=
  let n := c.toNat
  if n < 128 then c.isAlphanum else inRanges wordRangeArr.get n

/-- A non-spacing mark (General Category Mn). -/
def isMark (c : Char) : Bool := inRanges markRangeArr.get c.toNat

/-- The characters that end a sentence. -/
def isSentenceEnd (c : Char) : Bool := c == '.' || c == '!' || c == '?'

/-- A token of the text being searched: its word, its position, its
    sentence and its paragraph. -/
structure DocTok where
  word : String
  pos : Int
  sent : Int
  para : Int
deriving Repr, Inhabited, DecidableEq

/-- The state of the tokenizer loop. -/
structure TokState where
  out : Array DocTok := #[]
  cur : Array Char := #[]
  pos : Int := 0
  sent : Int := 1
  para : Int := 1
  /-- A sentence end was seen since the last token. -/
  sentEnd : Bool := false
  /-- A paragraph break was seen since the last token. -/
  paraEnd : Bool := false

/-- Close the current token, if any. -/
def TokState.flush (s : TokState) : TokState :=
  if s.cur.isEmpty then s
  else
    let started := !s.out.isEmpty
    let para := if started && s.paraEnd then s.para + 1 else s.para
    let sent := if started && (s.sentEnd || s.paraEnd) then s.sent + 1 else s.sent
    { s with out := s.out.push { word := String.ofList s.cur.toList, pos := s.pos + 1, sent, para },
             cur := #[], pos := s.pos + 1, sent, para, sentEnd := false, paraEnd := false }

/-- Han ideographs, Hiragana and Katakana: each is a token of its own
    (these scripts do not separate words by spaces). -/
def isIdeo (c : Char) : Bool :=
  let n := c.toNat
  (0x3040 ≤ n && n ≤ 0x30FF) || (0x3400 ≤ n && n ≤ 0x4DBF) || (0x4E00 ≤ n && n ≤ 0x9FFF) ||
  (0xF900 ≤ n && n ≤ 0xFAFF) || (0x20000 ≤ n && n ≤ 0x3134F)

/-- One character. -/
def TokState.step (s : TokState) (c : Char) : TokState :=
  if isIdeo c then { s.flush with cur := #[c] }.flush
  else if isWordChar c then { s with cur := s.cur.push c }
  else
    let s := s.flush
    if isSentenceEnd c then { s with sentEnd := true } else s

/-- Tokenize segments of text: each segment after the first starts a new
    paragraph. One loop over the characters (no recursion per character). -/
def tokenizeSegments (segs : List String) : Array DocTok := Id.run do
  let mut st : TokState := {}
  let mut first := true
  for seg in segs do
    -- an element boundary inside a token does not split it (the string
    -- value joins the text nodes); between tokens it ends the paragraph
    let joins := !st.cur.isEmpty && (match seg.toList.head? with
      | some c => isWordChar c
      | none => false)
    if !joins then
      st := st.flush
      if !first then st := { st with paraEnd := true }
    first := false
    for c in seg.toList do
      st := st.step c
  st := st.flush
  return st.out

/-- Tokenize one string (one paragraph). -/
def tokenizeString (s : String) : Array DocTok := tokenizeSegments [s]

/-- The words of a string, in order. -/
def words (s : String) : List String := (tokenizeString s).toList.map (·.word)

/-- Tokenize a query string (§3.2): the words, without positions. -/
def queryTokens (s : String) : List String := words s

/-- Tokenize a query string with the wildcard option on (§3.4.6): a `.`
    is a word character, with the indicator after it (`?`, `*`, `+`, or
    `{` up to the next `}`); `\c` is kept for a word character `c`
    and is a separator otherwise. Every other character follows the word
    rule, so a `?`, `*`, `+`, `{` or `}` that follows no `.` separates
    tokens. -/
def queryTokensWild (s : String) : List String := Id.run do
  let cs := s.toList.toArray
  let mut out : Array String := #[]
  let mut cur : Array Char := #[]
  let mut i := 0
  for _ in [0:cs.size + 1] do
    if i ≥ cs.size then break
    let c := cs.getD i ' '
    if c == '\\' then
      let d := cs.getD (i + 1) ' '
      if i + 1 < cs.size && isWordChar d then
        cur := (cur.push c).push d
      else if i + 1 ≥ cs.size then
        cur := cur.push c
      else
        if !cur.isEmpty then out := out.push (String.ofList cur.toList)
        cur := #[]
      i := i + 2
    else if c == '.' then
      cur := cur.push c
      let n := cs.getD (i + 1) ' '
      if i + 1 < cs.size && (n == '?' || n == '*' || n == '+') then
        cur := cur.push n; i := i + 2
      else if i + 1 < cs.size && n == '{' then
        let mut j := i + 1
        for _ in [0:cs.size] do
          if j ≥ cs.size then break
          let x := cs.getD j ' '
          cur := cur.push x
          j := j + 1
          if x == '}' then break
        i := j
      else i := i + 1
    else if isIdeo c then
      if !cur.isEmpty then out := out.push (String.ofList cur.toList)
      out := out.push c.toString
      cur := #[]
      i := i + 1
    else if isWordChar c then cur := cur.push c; i := i + 1
    else
      if !cur.isEmpty then out := out.push (String.ofList cur.toList)
      cur := #[]
      i := i + 1
  if !cur.isEmpty then out := out.push (String.ofList cur.toList)
  return out.toList

end L4Factoidal.FullText
