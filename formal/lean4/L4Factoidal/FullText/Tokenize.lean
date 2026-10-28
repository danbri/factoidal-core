/-
L4Factoidal.FullText.Tokenize — the tokenizer of the full-text
implementation (XQuery and XPath Full Text 3.0 §4.1: tokenization is
implementation-defined, within the constraints listed there).

The rules of this implementation:

* a token is a maximal run of word characters: Unicode General Category
  L (letters), M (marks) or N (numbers), from the tables of the shared
  regular-expression engine (`Regex.XPath40.categoryRanges`); every other
  character separates tokens;
* each token has one position; positions are consecutive from 1, so a
  phrase is a run of consecutive positions;
* a sentence ends after a token that is followed (before the next token)
  by `.`, `!` or `?`; sentences are numbered from 1;
* a paragraph ends at an element boundary: the text of a node is given as
  segments (the text nodes, in document order), and each segment after
  the first starts a new paragraph, and so a new sentence (§4.1: "taking
  any structural information of the item into account"). Paragraphs are
  numbered from 1.

Query strings are tokenized with the same word rule (`queryTokens`); when
the wildcard option is on, the wildcard characters `.?*+{},` and an
escaped character `\c` are word characters too (`queryTokensWild`), so a
wildcard expression is one token.
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

/-- One character. -/
def TokState.step (s : TokState) (c : Char) : TokState :=
  if isWordChar c then { s with cur := s.cur.push c }
  else
    let s := s.flush
    if isSentenceEnd c then { s with sentEnd := true } else s

/-- Tokenize segments of text: each segment after the first starts a new
    paragraph. One loop over the characters (no recursion per character). -/
def tokenizeSegments (segs : List String) : Array DocTok := Id.run do
  let mut st : TokState := {}
  let mut first := true
  for seg in segs do
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

/-- Characters of a wildcard expression (§3.4.6) kept inside a token. -/
def isWildChar (c : Char) : Bool := c == '.' || c == '?' || c == '*' || c == '+' || c == '{' || c == '}' || c == ','

/-- Tokenize a query string with the wildcard option on: word characters,
    the wildcard characters and escaped characters form tokens. -/
def queryTokensWild (s : String) : List String := Id.run do
  let mut out : Array String := #[]
  let mut cur : Array Char := #[]
  let mut esc := false
  for c in s.toList do
    if esc then cur := cur.push c; esc := false
    else if c == '\\' then cur := cur.push c; esc := true
    else if isWordChar c || isWildChar c then cur := cur.push c
    else
      if !cur.isEmpty then out := out.push (String.ofList cur.toList)
      cur := #[]
  if !cur.isEmpty then out := out.push (String.ofList cur.toList)
  return out.toList

end L4Factoidal.FullText
