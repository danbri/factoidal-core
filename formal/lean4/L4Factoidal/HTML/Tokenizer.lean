/-
L4Factoidal.HTML.Tokenizer — the tokenizer of the WHATWG HTML Living Standard,
§13.2.5 "Tokenization", and the input stream preprocessing of §13.2.3.5.

The tokenizer is a state machine written as a function `step` that makes one
transition; `Tok.pull` runs `step` until a token is queued. Both are loops
bounded by the length of the remaining input (fuel), not recursion over
characters. The tree builder (`HTML/TreeBuilder.lean`) calls `pull` and may
change `Tok.st` between tokens, as the standard requires for `title`,
`textarea`, `style`, `script`, `plaintext` and the other raw text elements.

Implemented states (names of §13.2.5): data, RCDATA, RAWTEXT, script data,
PLAINTEXT, tag open, end tag open, tag name, RCDATA / RAWTEXT / script data
less-than sign, end tag open and end tag name (one shared set of three
states, parameterised by `Tok.back`), before attribute name, attribute name,
after attribute name, before attribute value, attribute value (double
quoted, single quoted, unquoted), after attribute value (quoted),
self-closing start tag, bogus comment, markup declaration open, comment
start, comment start dash, comment, comment end dash, comment end, comment end
bang, CDATA section (when the tree builder reports foreign content), and the
character reference states (see `HTML/Entities.lean`).

Collapsed: the DOCTYPE states (§13.2.5.53 to §13.2.5.68) are one step that
reads up to the next `>` and then splits name, PUBLIC / SYSTEM keyword and
quoted identifiers. It reports the same error codes for the cases that
occur in practice, but not each of the 16 DOCTYPE error codes by state.

Not implemented: the script data escaped and double escaped states
(§13.2.5.20 to §13.2.5.31; a `<!--` inside `script` is plain script text,
which differs from the standard only for a `<script>` start tag inside a
comment inside a script), the comment less-than sign states (nested comment
errors `nested-comment` and `incorrectly-opened-comment` are not
reported), and the RCDATA / RAWTEXT end tag fallback of the temporary buffer
beyond the standard case.
-/

import L4Factoidal.HTML.Entities

namespace L4Factoidal.HTML

inductive Token where
  | doctype (name : Option String) (pub : Option String) (sys : Option String) (forceQuirks : Bool)
  | startTag (name : String) (attrs : List (String × String)) (selfClosing : Bool)
  | endTag (name : String)
  | comment (data : String)
  | char (c : Char)
  | eof
deriving Inhabited

inductive TS where
  | data | rcdata | rawtext | scriptData | plaintext
  | tagOpen | endTagOpen | tagName
  | rawLt | rawEndOpen | rawEndName
  | beforeAttrName | attrName | afterAttrName | beforeAttrValue
  | attrValueDq | attrValueSq | attrValueUnq | afterAttrValueQuoted | selfClosingStart
  | bogusComment | markupDecl | commentStart | commentStartDash | comment
  | commentEndDash | commentEnd | commentEndBang
  | doctype | cdata
deriving BEq, Inhabited

structure Tok where
  inp : Array Char
  pos : Nat := 0
  st : TS := .data
  /-- The state a raw text end tag state returns to. -/
  back : TS := .data
  out : List Token := []
  isEnd : Bool := false
  tagName : String := ""
  attrs : Array (String × String) := #[]
  hasCur : Bool := false
  curName : String := ""
  curVal : String := ""
  selfClose : Bool := false
  buf : String := ""
  tmp : String := ""
  lastStart : String := ""
  /-- Set by the tree builder: the adjusted current node is not in the HTML namespace. -/
  foreign : Bool := false
  errs : Array String := #[]
deriving Inhabited

/-! ## Input stream preprocessing (§13.2.3.5) -/

/-- Newline normalisation: CR LF and CR become LF. -/
def normalizeNewlines (s : String) : Array Char := Id.run do
  let cs := s.toList.toArray
  let mut out : Array Char := Array.mkEmpty cs.size
  let mut i := 0
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '\r' then
      out := out.push '\n'
      if i + 1 < cs.size && cs[i + 1]! == '\n' then i := i + 2 else i := i + 1
    else
      out := out.push c
      i := i + 1
  return out

/-- Parse errors of the input stream: control characters and noncharacters. -/
def inputErrors (inp : Array Char) : Array String := Id.run do
  let mut errs : Array String := #[]
  for c in inp do
    let n := c.toNat
    if isNonCharacter n then errs := errs.push "noncharacter-in-input-stream"
    else if isControlCp n && n != 0 && n != 0x0D then
      if !(n == 0x09 || n == 0x0A || n == 0x0C) then errs := errs.push "control-character-in-input-stream"
  return errs

/-! ## Helpers -/

def isWs (c : Char) : Bool := c == '\t' || c == '\n' || c == '\x0C' || c == ' '
def isAsciiAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def isAsciiUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'
def isAsciiAlnum (c : Char) : Bool := isAsciiAlpha c || ('0' ≤ c && c ≤ '9')
def lowerAscii (c : Char) : Char := if isAsciiUpper c then Char.ofNat (c.toNat + 32) else c
def lowerStr (s : String) : String := String.ofList (s.toList.map lowerAscii)

def Tok.emit (t : Tok) (x : Token) : Tok := { t with out := t.out ++ [x] }
def Tok.err (t : Tok) (e : String) : Tok := { t with errs := t.errs.push e }
def Tok.emitStr (t : Tok) (s : String) : Tok := s.toList.foldl (fun t c => t.emit (.char c)) t
def Tok.adv (t : Tok) : Tok := { t with pos := t.pos + 1 }
def Tok.to (t : Tok) (s : TS) : Tok := { t with st := s }

def Tok.newTag (t : Tok) (isEnd : Bool) : Tok :=
  { t with isEnd, tagName := "", attrs := #[], hasCur := false, curName := "", curVal := "", selfClose := false }

def Tok.finishAttr (t : Tok) : Tok :=
  if !t.hasCur then t
  else if t.attrs.any (fun a => a.1 == t.curName) then
    { t with hasCur := false, curName := "", curVal := "", errs := t.errs.push "duplicate-attribute" }
  else
    { t with hasCur := false, curName := "", curVal := "", attrs := t.attrs.push (t.curName, t.curVal) }

def Tok.newAttr (t : Tok) : Tok :=
  let t := t.finishAttr
  { t with hasCur := true, curName := "", curVal := "" }

def Tok.emitTag (t : Tok) : Tok :=
  let t := t.finishAttr
  if t.isEnd then
    let t := if t.attrs.size > 0 then t.err "end-tag-with-attributes" else t
    let t := if t.selfClose then t.err "end-tag-with-trailing-solidus" else t
    { t.emit (.endTag t.tagName) with st := .data }
  else
    { t.emit (.startTag t.tagName t.attrs.toList t.selfClose) with st := .data, lastStart := t.tagName }

def startsWithAt (inp : Array Char) (p : Nat) (s : String) (ci : Bool) : Bool :=
  let cs := s.toList
  (cs.zipIdx).all (fun (c, k) =>
    match inp[p + k]? with
    | some d => if ci then lowerAscii d == lowerAscii c else d == c
    | none => false)

/-! ## Character references -/

def digitVal (c : Char) (hex : Bool) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if hex && 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if hex && 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

def readDigitsGo (inp : Array Char) (hex : Bool) : Nat → Nat → Nat → Nat × Nat
  | 0, i, v => (v, i)
  | f + 1, i, v =>
    match inp[i]? with
    | some c =>
      match digitVal c hex with
      | some d => readDigitsGo inp hex f (i + 1) (min (v * (if hex then 16 else 10) + d) 0x110000)
      | none => (v, i)
    | none => (v, i)

def alnumEndGo (inp : Array Char) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => match inp[i]? with
    | some c => if isAsciiAlnum c then alnumEndGo inp f (i + 1) else i
    | none => i

/-- The longest prefix of `run` that is a name allowed without a semicolon. -/
def legacyPrefix (run : String) : Option String :=
  let cs := run.toList
  let rec go : Nat → Option String
    | 0 => none
    | k + 1 =>
      let pre := String.ofList (cs.take (k + 1))
      if legacyNames.contains pre then some pre else go k
  go cs.length

def cpStr (n : Nat) : String := String.singleton (Char.ofNat n)

/-- A character reference whose `&` is at `p - 1`: the text to emit, the new position and the
    error codes (§13.2.5.72 to §13.2.5.80). -/
def charRef (inp : Array Char) (p : Nat) (inAttr : Bool) : String × Nat × List String :=
  match inp[p]? with
  | some '#' =>
    let hex := (inp[p + 1]? == some 'x' || inp[p + 1]? == some 'X')
    let ds := if hex then p + 2 else p + 1
    let (n, e) := readDigitsGo inp hex (inp.size - ds) ds 0
    if e == ds then
      (String.ofList (inp.extract (p - 1) ds).toList, ds, ["absence-of-digits-in-numeric-character-reference"])
    else
      let (c, errs) := numericRef n
      if inp[e]? == some ';' then (String.singleton c, e + 1, errs)
      else (String.singleton c, e, "missing-semicolon-after-character-reference" :: errs)
  | some c =>
    if isAsciiAlnum c then
      let e := alnumEndGo inp (inp.size - p) p
      let run := String.ofList (inp.extract p e).toList
      let semi := inp[e]? == some ';'
      match (if semi then namedTable.lookup run else none) with
      | some cp => (cpStr cp, e + 1, [])
      | none =>
        match legacyPrefix run with
        | some k =>
          let after := inp[p + k.length]?
          if inAttr && (after == some '=' || (after.map isAsciiAlnum).getD false) then ("&", p, [])
          else
            match namedTable.lookup k with
            | some cp => (cpStr cp, p + k.length, ["missing-semicolon-after-character-reference"])
            | none => ("&", p, [])
        | none => ("&", p, if semi then ["unknown-named-character-reference"] else [])
    else ("&", p, [])
  | none => ("&", p, [])

/-! ## DOCTYPE -/

def skipWsL : List Char → List Char
  | c :: r => if isWs c then skipWsL r else c :: r
  | [] => []

/-- A quoted identifier at the start of `cs` (after white space). -/
def quotedId (cs : List Char) : Option (String × List Char) :=
  match skipWsL cs with
  | q :: r =>
    if q == '"' || q == '\'' then
      let body := r.takeWhile (· != q)
      some (String.ofList body, (r.drop body.length).drop 1)
    else none
  | [] => none

/-- Parse the text between `<!DOCTYPE` and `>`. -/
def parseDoctype (raw : List Char) : Token × List String :=
  let startErr : List String := match raw with
    | c :: _ => if isWs c then [] else ["missing-whitespace-before-doctype-name"]
    | [] => ["missing-doctype-name"]
  let cs := skipWsL raw
  let nameCs := cs.takeWhile (fun c => !isWs c)
  let rest := skipWsL (cs.drop nameCs.length)
  let name : Option String := if nameCs.isEmpty then none else some (lowerStr (String.ofList nameCs))
  let nameErr : List String := if nameCs.isEmpty && raw != [] then ["missing-doctype-name"] else []
  let kw (s : String) : Bool := rest.length ≥ s.length && lowerStr (String.ofList (rest.take s.length)) == lowerStr s
  if rest.isEmpty then (.doctype name none none nameCs.isEmpty, startErr ++ nameErr)
  else if kw "public" then
    match quotedId (rest.drop 6) with
    | some (pub, r) =>
      match quotedId r with
      | some (sys, r2) =>
        (.doctype name (some pub) (some sys) false,
          startErr ++ (if (skipWsL r2).isEmpty then [] else ["missing-whitespace-after-doctype-system-identifier"]))
      | none =>
        (.doctype name (some pub) none (!(skipWsL r).isEmpty), startErr ++ (if (skipWsL r).isEmpty then [] else ["missing-quote-before-doctype-system-identifier"]))
    | none => (.doctype name none none true, startErr ++ ["missing-quote-before-doctype-public-identifier"])
  else if kw "system" then
    match quotedId (rest.drop 6) with
    | some (sys, r) =>
      (.doctype name none (some sys) false,
        startErr ++ (if (skipWsL r).isEmpty then [] else ["unexpected-character-after-doctype-system-identifier"]))
    | none => (.doctype name none none true, startErr ++ ["missing-quote-before-doctype-system-identifier"])
  else (.doctype name none none true, startErr ++ ["invalid-character-sequence-after-doctype-name"])

def findGtGo (inp : Array Char) : Nat → Nat → Nat
  | 0, i => i
  | f + 1, i => match inp[i]? with
    | some c => if c == '>' then i else findGtGo inp f (i + 1)
    | none => i

/-! ## The state machine -/

def Tok.errs' (t : Tok) (es : List String) : Tok := es.foldl (fun t e => t.err e) t

/-- One transition of the tokenizer. -/
def Tok.step (t : Tok) : Tok :=
  let c? := t.inp[t.pos]?
  match t.st with
  | .data =>
    match c? with
    | none => t.emit .eof
    | some '&' =>
      let (s, p, es) := charRef t.inp (t.pos + 1) false
      { (t.errs' es).emitStr s with pos := p }
    | some '<' => { t.adv with st := .tagOpen }
    | some '\x00' => (t.err "unexpected-null-character").adv.emit (.char '\x00')
    | some c => t.adv.emit (.char c)
  | .rcdata =>
    match c? with
    | none => t.emit .eof
    | some '&' =>
      let (s, p, es) := charRef t.inp (t.pos + 1) false
      { (t.errs' es).emitStr s with pos := p }
    | some '<' => { t.adv with st := .rawLt, back := .rcdata }
    | some '\x00' => (t.err "unexpected-null-character").adv.emit (.char '�')
    | some c => t.adv.emit (.char c)
  | .rawtext =>
    match c? with
    | none => t.emit .eof
    | some '<' => { t.adv with st := .rawLt, back := .rawtext }
    | some '\x00' => (t.err "unexpected-null-character").adv.emit (.char '�')
    | some c => t.adv.emit (.char c)
  | .scriptData =>
    match c? with
    | none => t.emit .eof
    | some '<' => { t.adv with st := .rawLt, back := .scriptData }
    | some '\x00' => (t.err "unexpected-null-character").adv.emit (.char '�')
    | some c => t.adv.emit (.char c)
  | .plaintext =>
    match c? with
    | none => t.emit .eof
    | some '\x00' => (t.err "unexpected-null-character").adv.emit (.char '�')
    | some c => t.adv.emit (.char c)
  | .tagOpen =>
    match c? with
    | some '!' => { t.adv with st := .markupDecl }
    | some '/' => { t.adv with st := .endTagOpen }
    | some '?' => ((t.err "unexpected-question-mark-instead-of-tag-name").to .bogusComment) |> fun t => { t with buf := "" }
    | some c =>
      if isAsciiAlpha c then (t.newTag false).to .tagName
      else ((t.err "invalid-first-character-of-tag-name").emit (.char '<')).to .data
    | none => ((t.err "eof-before-tag-name").emit (.char '<')).emit .eof
  | .endTagOpen =>
    match c? with
    | some '>' => { (t.err "missing-end-tag-name").adv with st := .data }
    | some c =>
      if isAsciiAlpha c then (t.newTag true).to .tagName
      else { (t.err "invalid-first-character-of-tag-name").to .bogusComment with buf := "" }
    | none => (((t.err "eof-before-tag-name").emit (.char '<')).emit (.char '/')).emit .eof
  | .tagName =>
    match c? with
    | none => (t.err "eof-in-tag").emit .eof
    | some c =>
      if isWs c then t.adv.to .beforeAttrName
      else if c == '/' then t.adv.to .selfClosingStart
      else if c == '>' then t.adv.emitTag
      else if c == '\x00' then { (t.err "unexpected-null-character").adv with tagName := t.tagName.push '�' }
      else { t.adv with tagName := t.tagName.push (lowerAscii c) }
  | .rawLt =>
    match c? with
    | some '/' => { t.adv with st := .rawEndOpen, tmp := "" }
    | _ => (t.emit (.char '<')).to t.back
  | .rawEndOpen =>
    match c? with
    | some c =>
      if isAsciiAlpha c then (t.newTag true).to .rawEndName
      else ((t.emit (.char '<')).emit (.char '/')).to t.back
    | none => ((t.emit (.char '<')).emit (.char '/')).to t.back
  | .rawEndName =>
    let appropriate := t.tagName == t.lastStart
    let anything : Tok := (((t.emit (.char '<')).emit (.char '/')).emitStr t.tmp).to t.back
    match c? with
    | some c =>
      if isWs c && appropriate then t.adv.to .beforeAttrName
      else if c == '/' && appropriate then t.adv.to .selfClosingStart
      else if c == '>' && appropriate then t.adv.emitTag
      else if isAsciiAlpha c then { t.adv with tagName := t.tagName.push (lowerAscii c), tmp := t.tmp.push c }
      else anything
    | none => anything
  | .beforeAttrName =>
    match c? with
    | some c =>
      if isWs c then t.adv
      else if c == '/' || c == '>' then t.to .afterAttrName
      else if c == '=' then
        let t := (t.err "unexpected-equals-sign-before-attribute-name").newAttr
        { t.adv with st := .attrName, curName := "=" }
      else t.newAttr.to .attrName
    | none => t.to .afterAttrName
  | .attrName =>
    match c? with
    | some c =>
      if isWs c || c == '/' || c == '>' then t.to .afterAttrName
      else if c == '=' then t.adv.to .beforeAttrValue
      else if c == '\x00' then { (t.err "unexpected-null-character").adv with curName := t.curName.push '�' }
      else if c == '"' || c == '\'' || c == '<' then
        { (t.err "unexpected-character-in-attribute-name").adv with curName := t.curName.push c }
      else { t.adv with curName := t.curName.push (lowerAscii c) }
    | none => t.to .afterAttrName
  | .afterAttrName =>
    match c? with
    | some c =>
      if isWs c then t.adv
      else if c == '/' then t.adv.to .selfClosingStart
      else if c == '=' then t.adv.to .beforeAttrValue
      else if c == '>' then t.adv.emitTag
      else t.newAttr.to .attrName
    | none => (t.err "eof-in-tag").emit .eof
  | .beforeAttrValue =>
    match c? with
    | some c =>
      if isWs c then t.adv
      else if c == '"' then t.adv.to .attrValueDq
      else if c == '\'' then t.adv.to .attrValueSq
      else if c == '>' then (t.err "missing-attribute-value").adv.emitTag
      else t.to .attrValueUnq
    | none => t.to .attrValueUnq
  | .attrValueDq | .attrValueSq =>
    let q := if t.st == .attrValueDq then '"' else '\''
    match c? with
    | none => (t.err "eof-in-tag").emit .eof
    | some c =>
      if c == q then t.adv.to .afterAttrValueQuoted
      else if c == '&' then
        let (s, p, es) := charRef t.inp (t.pos + 1) true
        { (t.errs' es) with curVal := t.curVal ++ s, pos := p }
      else if c == '\x00' then { (t.err "unexpected-null-character").adv with curVal := t.curVal.push '�' }
      else { t.adv with curVal := t.curVal.push c }
  | .attrValueUnq =>
    match c? with
    | none => (t.err "eof-in-tag").emit .eof
    | some c =>
      if isWs c then t.adv.to .beforeAttrName
      else if c == '&' then
        let (s, p, es) := charRef t.inp (t.pos + 1) true
        { (t.errs' es) with curVal := t.curVal ++ s, pos := p }
      else if c == '>' then t.adv.emitTag
      else if c == '\x00' then { (t.err "unexpected-null-character").adv with curVal := t.curVal.push '�' }
      else if c == '"' || c == '\'' || c == '<' || c == '=' || c == '`' then
        { (t.err "unexpected-character-in-unquoted-attribute-value").adv with curVal := t.curVal.push c }
      else { t.adv with curVal := t.curVal.push c }
  | .afterAttrValueQuoted =>
    match c? with
    | none => (t.err "eof-in-tag").emit .eof
    | some c =>
      if isWs c then t.adv.to .beforeAttrName
      else if c == '/' then t.adv.to .selfClosingStart
      else if c == '>' then t.adv.emitTag
      else (t.err "missing-whitespace-between-attributes").to .beforeAttrName
  | .selfClosingStart =>
    match c? with
    | none => (t.err "eof-in-tag").emit .eof
    | some '>' => { t.adv with selfClose := true }.emitTag
    | some _ => (t.err "unexpected-solidus-in-tag").to .beforeAttrName
  | .bogusComment =>
    match c? with
    | none => ({ t.emit (.comment t.buf) with buf := "" }).emit .eof
    | some '>' => { t.adv.emit (.comment t.buf) with st := .data, buf := "" }
    | some '\x00' => { (t.err "unexpected-null-character").adv with buf := t.buf.push '�' }
    | some c => { t.adv with buf := t.buf.push c }
  | .markupDecl =>
    if startsWithAt t.inp t.pos "--" false then { t with pos := t.pos + 2, st := .commentStart, buf := "" }
    else if startsWithAt t.inp t.pos "doctype" true then { t with pos := t.pos + 7, st := .doctype }
    else if startsWithAt t.inp t.pos "[CDATA[" false then
      if t.foreign then { t with pos := t.pos + 7, st := .cdata }
      else { (t.err "cdata-in-html-content") with pos := t.pos + 7, st := .bogusComment, buf := "[CDATA[" }
    else { (t.err "incorrectly-opened-comment") with st := .bogusComment, buf := "" }
  | .commentStart =>
    match c? with
    | some '-' => t.adv.to .commentStartDash
    | some '>' => { (t.err "abrupt-closing-of-empty-comment").adv.emit (.comment t.buf) with st := .data, buf := "" }
    | _ => t.to .comment
  | .commentStartDash =>
    match c? with
    | some '-' => t.adv.to .commentEnd
    | some '>' => { (t.err "abrupt-closing-of-empty-comment").adv.emit (.comment t.buf) with st := .data, buf := "" }
    | none => (({ t.err "eof-in-comment" with }).emit (.comment t.buf)).emit .eof
    | some _ => { t with buf := t.buf.push '-', st := .comment }
  | .comment =>
    match c? with
    | none => ((t.err "eof-in-comment").emit (.comment t.buf)).emit .eof
    | some '-' => t.adv.to .commentEndDash
    | some '\x00' => { (t.err "unexpected-null-character").adv with buf := t.buf.push '�' }
    | some c => { t.adv with buf := t.buf.push c }
  | .commentEndDash =>
    match c? with
    | some '-' => t.adv.to .commentEnd
    | none => ((t.err "eof-in-comment").emit (.comment t.buf)).emit .eof
    | some _ => { t with buf := t.buf.push '-', st := .comment }
  | .commentEnd =>
    match c? with
    | some '>' => { t.adv.emit (.comment t.buf) with st := .data, buf := "" }
    | some '!' => t.adv.to .commentEndBang
    | some '-' => { t.adv with buf := t.buf.push '-' }
    | none => ((t.err "eof-in-comment").emit (.comment t.buf)).emit .eof
    | some _ => { t with buf := t.buf ++ "--", st := .comment }
  | .commentEndBang =>
    match c? with
    | some '-' => { t.adv with buf := t.buf ++ "--!", st := .commentEndDash }
    | some '>' => { (t.err "incorrectly-closed-comment").adv.emit (.comment t.buf) with st := .data, buf := "" }
    | none => ((t.err "eof-in-comment").emit (.comment t.buf)).emit .eof
    | some _ => { t with buf := t.buf ++ "--!", st := .comment }
  | .doctype =>
    let e := findGtGo t.inp (t.inp.size - t.pos) t.pos
    let raw := (t.inp.extract t.pos e).toList
    let (tok, es) := parseDoctype raw
    let atEof := e ≥ t.inp.size
    let tok := match tok with
      | .doctype n p s q => .doctype n p s (q || atEof)
      | x => x
    let t := (t.errs' es).emit tok
    if atEof then ((t.err "eof-in-doctype").to .data) |> fun t => { t with pos := e }
    else { t with pos := e + 1, st := .data }
  | .cdata =>
    if startsWithAt t.inp t.pos "]]>" false then { t with pos := t.pos + 3, st := .data }
    else match c? with
      | none => ((t.err "eof-in-cdata").emit .eof)
      | some c => t.adv.emit (.char c)

/-- Run the machine until a token is queued, and take it. -/
def Tok.pull (t : Tok) : Token × Tok :=
  go ((t.inp.size - t.pos + 2) * 16) t
where
  go : Nat → Tok → Token × Tok
    | 0, t => (.eof, t)
    | f + 1, t =>
      match t.out with
      | x :: rest => (x, { t with out := rest })
      | [] => go f t.step

end L4Factoidal.HTML
