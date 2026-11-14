/-
L4Factoidal.Rendering.CssValues.Token — CSS Syntax 3: the tokenizer (§4), component values
(§5.4.7), and their serialisation (§9, CSSOM §6.7.2 "serialize a CSS component value").

Numbers are exact: a CSS number is a decimal, and here it is a `Rat`. No `Float` is used
anywhere in `CssValues`, so equality of values is decidable and the arithmetic of `calc()`
and of the colour conversions is exact.

This module depends on the Lean core library only: it is used by the style declaration
block of page scripts, `CSS.supports`, computed values and CSS Typed OM, and can be
checked on its own.
-/

namespace L4Factoidal.Rendering.CssValues

/-- A CSS token (CSS Syntax 3 §4). `func`, the parentheses, brackets and braces are only
seen between the tokenizer and `CV.parse`. -/
inductive Tok where
  | ident (s : String)
  | func (s : String)
  | atKeyword (s : String)
  | hash (s : String) (isId : Bool)
  | str (s : String)
  | badStr
  | url (s : String)
  | badUrl
  | delim (c : Char)
  /-- A number: its value, whether it was written as an integer. -/
  | num (v : Rat) (int : Bool)
  | pct (v : Rat)
  /-- A dimension: value, written as an integer, unit as written. -/
  | dim (v : Rat) (int : Bool) (unit : String)
  | ws
  | cdo | cdc | colon | semicolon | comma
  | lbracket | rbracket | lparen | rparen | lbrace | rbrace
  deriving Repr, DecidableEq, Inhabited

/-- A component value (CSS Syntax 3 §5.4.7): a preserved token, a function with its
contents, or a simple block. -/
inductive CV where
  | tok (t : Tok)
  | fn (name : String) (args : List CV)
  | block (opener : Char) (body : List CV)
  /-- Canonical text made by a value parser (a colour, a simplified `calc()`): serialised
  as it is. Never made by `CV.parse`. -/
  | raw (s : String)
  -- no `Repr`: deriving it for a nested inductive makes a `partial def`
  deriving Inhabited

/-! ### Characters -/

def isNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat ≥ 0x80
def isNameChar (c : Char) : Bool := isNameStart c || c.isDigit || c == '-'
def isWs (c : Char) : Bool := c == ' ' || c == '\n' || c == '\t'

def hexVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a'.toNat ≤ c.toNat && c.toNat ≤ 'f'.toNat then some (c.toNat - 87)
  else if 'A'.toNat ≤ c.toNat && c.toNat ≤ 'F'.toNat then some (c.toNat - 55)
  else none

/-- ASCII lower case of a string. -/
def lower (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- §4.3.8: two code points are a valid escape. -/
def validEscape : List Char → Bool
  | '\\' :: c :: _ => c != '\n'
  | _ => false

/-- §4.3.9: the next code points start an identifier. -/
def startsIdent : List Char → Bool
  | '-' :: c :: rest => isNameStart c || c == '-' || validEscape (c :: rest)
  | c :: rest => isNameStart c || validEscape (c :: rest)
  | [] => false

/-- §4.3.10: the next code points start a number. -/
def startsNumber : List Char → Bool
  | '+' :: c :: rest => c.isDigit || (c == '.' && (rest.head?.map Char.isDigit).getD false)
  | '-' :: c :: rest => c.isDigit || (c == '.' && (rest.head?.map Char.isDigit).getD false)
  | '.' :: c :: _ => c.isDigit
  | c :: _ => c.isDigit
  | [] => false

/-- §4.3.7: consume an escaped code point (the input is after the backslash). -/
def consumeEscape (cs : List Char) : Char × List Char :=
  match cs with
  | [] => (Char.ofNat 0xFFFD, [])
  | c :: rest =>
    match hexVal c with
    | none => (c, rest)
    | some _ =>
      let hexs := (cs.takeWhile fun c => (hexVal c).isSome).take 6
      let rest := cs.drop hexs.length
      let rest := match rest with
        | w :: r => if isWs w then r else rest
        | [] => rest
      let n := hexs.foldl (fun a c => a * 16 + (hexVal c).getD 0) 0
      (if n == 0 || (0xD800 ≤ n && n ≤ 0xDFFF) || n > 0x10FFFF then Char.ofNat 0xFFFD else Char.ofNat n, rest)

/-- §4.3.11: consume an ident sequence. -/
def consumeName : Nat → List Char → List Char → String × List Char
  | 0, cs, acc => (String.ofList acc.reverse, cs)
  | fuel + 1, cs, acc =>
    match cs with
    | c :: rest =>
      if isNameChar c then consumeName fuel rest (c :: acc)
      else if validEscape cs then
        let (e, r) := consumeEscape rest
        consumeName fuel r (e :: acc)
      else (String.ofList acc.reverse, cs)
    | [] => (String.ofList acc.reverse, [])

def digitsVal (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- `10 ^ n` as a rational. -/
def pow10 (n : Nat) : Rat := ((10 ^ n : Nat) : Rat)

/-- §4.3.12: consume a number: its exact value, whether it is an integer in the source, the
rest. An exponent beyond 400 in size is cut to 400: such a number is beyond any range a
property accepts. -/
def consumeNumber (cs : List Char) : Rat × Bool × List Char :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | _ => (false, cs)
  let ip := cs.takeWhile Char.isDigit
  let cs := cs.drop ip.length
  let (fp, cs, isInt) := match cs with
    | '.' :: d :: r =>
      if d.isDigit then
        let f := (d :: r).takeWhile Char.isDigit
        (f, (d :: r).drop f.length, false)
      else ([], cs, true)
    | _ => ([], cs, true)
  let (ex, cs, isInt) : Int × List Char × Bool := match cs with
    | e :: r =>
      if e == 'e' || e == 'E' then
        let (eneg, r2) := match r with
          | '-' :: r' => (true, r')
          | '+' :: r' => (false, r')
          | _ => (false, r)
        let ed := r2.takeWhile Char.isDigit
        if ed.isEmpty then (0, cs, isInt)
        else
          let n := min (digitsVal ed) 400
          ((if eneg then -(Int.ofNat n) else Int.ofNat n), r2.drop ed.length, false)
      else (0, cs, isInt)
    | [] => (0, cs, isInt)
  let m : Rat := ((digitsVal (ip ++ fp) : Nat) : Rat)
  let scale : Int := ex - Int.ofNat fp.length
  let v := if scale ≥ 0 then m * pow10 scale.toNat else m / pow10 (-scale).toNat
  (if neg then -v else v, isInt, cs)

/-- §4.3.5: consume a string token; the input is after the opening quote. -/
def consumeString (q : Char) : Nat → List Char → List Char → Tok × List Char
  | 0, cs, acc => (.str (String.ofList acc.reverse), cs)
  | fuel + 1, cs, acc =>
    match cs with
    | [] => (.str (String.ofList acc.reverse), [])
    | c :: rest =>
      if c == q then (.str (String.ofList acc.reverse), rest)
      else if c == '\n' then (.badStr, cs)
      else if c == '\\' then
        match rest with
        | [] => (.str (String.ofList acc.reverse), [])
        | '\n' :: r => consumeString q fuel r acc
        | _ =>
          let (e, r) := consumeEscape rest
          consumeString q fuel r (e :: acc)
      else consumeString q fuel rest (c :: acc)

/-- §4.3.14: consume the remnants of a bad url. -/
def consumeBadUrl : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    match cs with
    | [] => []
    | ')' :: rest => rest
    | '\\' :: _ :: rest => consumeBadUrl fuel rest
    | _ :: rest => consumeBadUrl fuel rest

/-- §4.3.6: consume a url token; the input is after `url(` and its white space. -/
def consumeUrl : Nat → List Char → List Char → Tok × List Char
  | 0, cs, acc => (.url (String.ofList acc.reverse), cs)
  | fuel + 1, cs, acc =>
    match cs with
    | [] => (.url (String.ofList acc.reverse), [])
    | ')' :: rest => (.url (String.ofList acc.reverse), rest)
    | c :: rest =>
      if isWs c then
        let r := rest.dropWhile isWs
        match r with
        | [] => (.url (String.ofList acc.reverse), [])
        | ')' :: r' => (.url (String.ofList acc.reverse), r')
        | _ => (.badUrl, consumeBadUrl fuel r)
      else if c == '"' || c == '\'' || c == '(' || c.toNat ≤ 8 || c.toNat == 0xB || (0xE ≤ c.toNat && c.toNat ≤ 0x1F) || c.toNat == 0x7F then
        (.badUrl, consumeBadUrl fuel rest)
      else if c == '\\' then
        if validEscape cs then
          let (e, r) := consumeEscape rest
          consumeUrl fuel r (e :: acc)
        else (.badUrl, consumeBadUrl fuel rest)
      else consumeUrl fuel rest (c :: acc)

/-- Skip a comment body: the input is after `/*`. -/
def skipComment : Nat → List Char → List Char
  | 0, cs => cs
  | fuel + 1, cs =>
    match cs with
    | '*' :: '/' :: rest => rest
    | _ :: rest => skipComment fuel rest
    | [] => []

/-- §4.3.3 and §4.3.4: a numeric token, or an ident-like token. -/
def consumeNumeric (cs : List Char) : Tok × List Char :=
  let (v, isInt, rest) := consumeNumber cs
  if startsIdent rest then
    let (unit, rest) := consumeName (rest.length + 1) rest []
    (.dim v isInt unit, rest)
  else match rest with
    | '%' :: r => (.pct v, r)
    | _ => (.num v isInt, rest)

def consumeIdentLike (cs : List Char) : Tok × List Char :=
  let (name, rest) := consumeName (cs.length + 1) cs []
  match rest with
  | '(' :: r =>
    if lower name == "url" then
      let r' := r.dropWhile isWs
      match r' with
      | '"' :: _ => (.func name, r)
      | '\'' :: _ => (.func name, r)
      | _ => consumeUrl (r'.length + 1) r' []
    else (.func name, r)
  | _ => (.ident name, rest)

/-- §4.3.1: consume tokens until the input ends. Each step takes at least one code point. -/
def tokensLoop : Nat → List Char → Array Tok → Array Tok
  | 0, _, acc => acc
  | fuel + 1, cs, acc =>
    match cs with
    | [] => acc
    | c :: rest =>
      if isWs c then tokensLoop fuel (rest.dropWhile isWs) (acc.push .ws)
      else if c == '/' && rest.head? == some '*' then tokensLoop fuel (skipComment (rest.length + 1) (rest.drop 1)) acc
      else if c == '"' || c == '\'' then
        let (t, r) := consumeString c (rest.length + 1) rest []
        tokensLoop fuel r (acc.push t)
      else if c == '#' then
        match rest with
        | d :: _ =>
          if isNameChar d || validEscape rest then
            let (name, r) := consumeName (rest.length + 1) rest []
            tokensLoop fuel r (acc.push (.hash name (startsIdent rest)))
          else tokensLoop fuel rest (acc.push (.delim c))
        | [] => tokensLoop fuel rest (acc.push (.delim c))
      else if c == '(' then tokensLoop fuel rest (acc.push .lparen)
      else if c == ')' then tokensLoop fuel rest (acc.push .rparen)
      else if c == '[' then tokensLoop fuel rest (acc.push .lbracket)
      else if c == ']' then tokensLoop fuel rest (acc.push .rbracket)
      else if c == '{' then tokensLoop fuel rest (acc.push .lbrace)
      else if c == '}' then tokensLoop fuel rest (acc.push .rbrace)
      else if c == ',' then tokensLoop fuel rest (acc.push .comma)
      else if c == ':' then tokensLoop fuel rest (acc.push .colon)
      else if c == ';' then tokensLoop fuel rest (acc.push .semicolon)
      else if startsNumber cs then
        let (t, r) := consumeNumeric cs
        tokensLoop fuel r (acc.push t)
      else if c == '-' && rest.take 2 == ['-', '>'] then tokensLoop fuel (rest.drop 2) (acc.push .cdc)
      else if c == '<' && rest.take 3 == ['!', '-', '-'] then tokensLoop fuel (rest.drop 3) (acc.push .cdo)
      else if c == '@' && startsIdent rest then
        let (name, r) := consumeName (rest.length + 1) rest []
        tokensLoop fuel r (acc.push (.atKeyword name))
      else if startsIdent cs then
        let (t, r) := consumeIdentLike cs
        tokensLoop fuel r (acc.push t)
      else tokensLoop fuel rest (acc.push (.delim c))

/-- §3.3: preprocess the input stream (CR, FF and CRLF become LF; NUL becomes U+FFFD). -/
def preprocess : List Char → List Char
  | '\r' :: '\n' :: rest => '\n' :: preprocess rest
  | '\r' :: rest => '\n' :: preprocess rest
  | '\x0c' :: rest => '\n' :: preprocess rest
  | '\x00' :: rest => Char.ofNat 0xFFFD :: preprocess rest
  | c :: rest => c :: preprocess rest
  | [] => []

/-- The tokens of a CSS text. -/
def tokenize (s : String) : List Tok :=
  let cs := preprocess s.toList
  (tokensLoop (cs.length + 1) cs #[]).toList

/-! ### Component values -/

def closerOf : Char → Tok
  | '(' => .rparen
  | '[' => .rbracket
  | _ => .rbrace

/-- §5.4.7–§5.4.9: component values up to the token `close` (or the end of the input, which
closes every open block). Answers the values and the tokens after the closing token. -/
def parseCVs : Nat → List Tok → Option Tok → List CV → List CV × List Tok
  | 0, ts, _, acc => (acc.reverse, ts)
  | fuel + 1, ts, close, acc =>
    match ts with
    | [] => (acc.reverse, [])
    | t :: rest =>
      if some t == close then (acc.reverse, rest)
      else match t with
        | .func name =>
          let (args, rest') := parseCVs fuel rest (some .rparen) []
          parseCVs fuel rest' close (.fn name args :: acc)
        | .lparen =>
          let (body, rest') := parseCVs fuel rest (some .rparen) []
          parseCVs fuel rest' close (.block '(' body :: acc)
        | .lbracket =>
          let (body, rest') := parseCVs fuel rest (some .rbracket) []
          parseCVs fuel rest' close (.block '[' body :: acc)
        | .lbrace =>
          let (body, rest') := parseCVs fuel rest (some .rbrace) []
          parseCVs fuel rest' close (.block '{' body :: acc)
        | t => parseCVs fuel rest close (.tok t :: acc)

/-- The component values of a CSS text. -/
def CV.parse (s : String) : List CV :=
  let ts := tokenize s
  (parseCVs (2 * ts.length + 2) ts none []).1

def CV.isWs : CV → Bool
  | .tok .ws => true
  | _ => false

/-- White space removed at the start and at the end. -/
def trimWs (cvs : List CV) : List CV :=
  ((cvs.dropWhile CV.isWs).reverse.dropWhile CV.isWs).reverse

/-- White space removed everywhere at this level. -/
def stripWs (cvs : List CV) : List CV := cvs.filter (!·.isWs)

/-! ### Serialisation -/

def hexDigits (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- CSSOM §2.1 "serialize an identifier". -/
def serializeIdent (s : String) : String :=
  let cs := s.toList
  let hex := fun (c : Char) => "\\" ++ hexDigits c.toNat ++ " "
  let rec go : Nat → List Char → String → String
    | _, [], out => out
    | i, c :: rest, out =>
      let n := c.toNat
      let piece :=
        if n == 0 then String.singleton (Char.ofNat 0xFFFD)
        else if (1 ≤ n && n ≤ 0x1F) || n == 0x7F then hex c
        else if i == 0 && c.isDigit then hex c
        else if i == 1 && c.isDigit && cs.head? == some '-' then hex c
        else if i == 0 && c == '-' && cs.length == 1 then "\\-"
        else if n ≥ 0x80 || c == '-' || c == '_' || c.isAlphanum then String.singleton c
        else "\\" ++ String.singleton c
      go (i + 1) rest (out ++ piece)
  go 0 cs ""

/-- CSSOM §2.1 "serialize a string". -/
def serializeString (s : String) : String :=
  let body := s.toList.foldl (fun out c =>
    let n := c.toNat
    if n == 0 then out.push (Char.ofNat 0xFFFD)
    else if (1 ≤ n && n ≤ 0x1F) || n == 0x7F then out ++ "\\" ++ hexDigits n ++ " "
    else if c == '"' || c == '\\' then (out.push '\\').push c
    else out.push c) ""
  "\"" ++ body ++ "\""

/-- The decimal digits of `n`, padded on the left with zeros to `width`. -/
def padDigits (n width : Nat) : List Char :=
  let ds := (toString n).toList
  List.replicate (width - ds.length) '0' ++ ds

/-- The number of zeros after the decimal point before the first non-zero digit of a
rational strictly between 0 and 1 (at most `fuel`). -/
def leadingZeros : Nat → Rat → Nat → Nat
  | 0, _, k => k
  | fuel + 1, a, k => if a * 10 < 1 then leadingZeros fuel (a * 10) (k + 1) else k

/-- `a` (non-negative) with `places` decimal places, rounded half up, trailing zeros and a
bare decimal point removed. -/
def fmtPlaces (a : Rat) (places : Nat) : String :=
  let scaled := (a * pow10 places + (1 : Rat) / 2).floor.toNat
  let ds := padDigits scaled (places + 1)
  let ip := ds.take (ds.length - places)
  let fp := ((ds.drop (ds.length - places)).reverse.dropWhile (· == '0')).reverse
  String.ofList (if fp.isEmpty then ip else ip ++ '.' :: fp)

/-- A CSS number as text (CSSOM §6.7.2): an integer in full; otherwise six significant
digits, with no exponent. -/
def fmtRat (v : Rat) : String :=
  if v.den == 1 then toString v.num
  else
    let neg := v < 0
    let a := if neg then -v else v
    let ip := a.floor.toNat
    let places :=
      if ip == 0 then 6 + leadingZeros 30 a 0
      else 6 - (toString ip).length
    let s := fmtPlaces a places
    if neg && s != "0" then "-" ++ s else s

def Tok.css : Tok → String
  | .ident s => serializeIdent s
  | .func s => serializeIdent s ++ "("
  | .atKeyword s => "@" ++ serializeIdent s
  | .hash s _ => "#" ++ s
  | .str s => serializeString s
  | .badStr => "\""
  | .url s => "url(" ++ serializeString s ++ ")"
  | .badUrl => "url()"
  | .delim c => String.singleton c
  | .num v _ => fmtRat v
  | .pct v => fmtRat v ++ "%"
  | .dim v _ unit => fmtRat v ++ lower unit
  | .ws => " "
  | .cdo => "<!--" | .cdc => "-->" | .colon => ":" | .semicolon => ";" | .comma => ","
  | .lbracket => "[" | .rbracket => "]" | .lparen => "(" | .rparen => ")"
  | .lbrace => "{" | .rbrace => "}"

def closerChar : Char → Char
  | '(' => ')'
  | '[' => ']'
  | _ => '}'

/-- Whether a space goes between two adjacent values of a canonical serialisation: not
before a comma, and not next to white space that is already there. -/
def spaceBetween (a b : CV) : Bool :=
  match a, b with
  | _, .tok .comma => false
  | .tok .ws, _ => false
  | _, .tok .ws => false
  | _, _ => true

mutual
  /-- The canonical text of one component value: a function with its name as the value
  parser gave it (the grammar's spelling), its contents serialised as a list. -/
  def CV.css : Nat → CV → String
    | 0, _ => ""
    | fuel + 1, cv =>
      match cv with
      | .tok t => t.css
      | .fn name args => name ++ "(" ++ cssList fuel args ++ ")"
      | .block o body => String.singleton o ++ cssList fuel body ++ String.singleton (closerChar o)
      | .raw s => s
  /-- The canonical text of a list of component values: one space between values, none
  before a comma. -/
  def cssList : Nat → List CV → String
    | 0, _ => ""
    | fuel + 1, cvs =>
      match cvs with
      | [] => ""
      | [a] => CV.css fuel a
      | a :: b :: rest => CV.css fuel a ++ (if spaceBetween a b then " " else "") ++ cssList fuel (b :: rest)
end

/-- A bound on the recursion of `cssList` for a list: the size of the tree. -/
def cvSize : Nat → List CV → Nat
  | 0, _ => 0
  | fuel + 1, cvs => cvs.foldl (fun n cv => n + 2 + match cv with
      | .tok _ => 0
      | .raw _ => 0
      | .fn _ args => cvSize fuel args
      | .block _ body => cvSize fuel body) 1

/-- The canonical text of a list of component values. -/
def serialize (cvs : List CV) : String := cssList (cvSize 64 cvs + 2) cvs

/-- The text as written, token by token (for values kept as specified: custom properties,
values with `var()`): white space collapsed to one space. -/
def rawText (cvs : List CV) : String :=
  let rec go : Nat → List CV → String
    | 0, _ => ""
    | fuel + 1, cvs => cvs.foldl (fun out cv => out ++ match cv with
        | .tok t => t.css
        | .raw s => s
        | .fn name args => serializeIdent name ++ "(" ++ go fuel args ++ ")"
        | .block o body => String.singleton o ++ go fuel body ++ String.singleton (closerChar o)) ""
  go (cvSize 64 cvs + 2) (trimWs cvs)

/-! ### Tests and theorems -/

#guard tokenize "1px" == [.dim 1 true "px"]
#guard tokenize "-1.5e2%" == [.pct (-150)]
#guard tokenize ".5" == [.num ((1 : Rat) / 2) false]
#guard tokenize "a b" == [.ident "a", .ws, .ident "b"]
#guard tokenize "a/**/b" == [.ident "a", .ident "b"]
#guard tokenize "url( x )" == [.url "x"]
#guard tokenize "url(\"x\")" == [.func "url", .str "x", .rparen]
#guard tokenize "#fff" == [.hash "fff" true]
#guard tokenize "--x" == [.ident "--x"]
#guard tokenize "\\41 b" == [.ident "Ab"]
#guard tokenize "+" == [.delim '+']
#guard tokenize "1e3" == [.num 1000 false]
#guard tokenize "1e" == [.dim 1 true "e"]
#guard fmtRat 0 == "0"
#guard fmtRat (-3) == "-3"
#guard fmtRat ((1 : Rat) / 2) == "0.5"
#guard fmtRat ((-1 : Rat) / 4) == "-0.25"
#guard fmtRat ((1 : Rat) / 3) == "0.333333"
#guard fmtRat ((2 : Rat) / 3) == "0.666667"
#guard fmtRat ((1000 : Rat) / 3) == "333.333"
#guard fmtRat ((1 : Rat) / 300) == "0.00333333"
#guard fmtRat (1234567 + (1 : Rat) / 2) == "1234568"
#guard fmtRat ((377953 : Rat) / 1000) == "377.953"
#guard serialize (stripWs (CV.parse "a  ,  b c")) == "a, b c"
#guard serializeString "a\"b" == "\"a\\\"b\""
#guard serializeIdent "0a" == "\\30 a"
#guard rawText (CV.parse "  var( --x ,  1px ) ") == "var( --x , 1px )"

/-- Kind: structure. Says: ASCII lower-casing of a code point is idempotent. Does not say:
anything about non-ASCII case folding (CSS keywords are ASCII case-insensitive only). -/
theorem toLower_idempotent (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split
  · rename_i h
    split
    · rename_i h2
      exfalso
      have h1 := h.1
      have h3 := h2.2
      have h4 := h.2
      simp only [ge_iff_le, UInt32.le_iff_toNat_le, UInt32.toNat_add] at h1 h3 h4
      have e1 : 'A'.val.toNat = 65 := by decide
      have e2 : 'Z'.val.toNat = 90 := by decide
      have e3 : ('a'.val - 'A'.val).toNat = 32 := by decide
      rw [e1] at h1
      rw [e2] at h3 h4
      rw [e3] at h3
      omega
    · rfl
  · simp

/-- Kind: structure. Says: lower-casing a string is idempotent, so a keyword or unit that
was made canonical stays as it is when it is read again. Does not say: that two strings
with the same lower case are the same keyword in every context (custom identifiers are
case-sensitive). -/
theorem lower_idempotent (s : String) : lower (lower s) = lower s := by
  simp [lower, List.map_map, Function.comp_def, toLower_idempotent]

end L4Factoidal.Rendering.CssValues
