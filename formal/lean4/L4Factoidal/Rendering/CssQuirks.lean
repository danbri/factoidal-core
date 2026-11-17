import L4Factoidal.Rendering.SheetReader

/-! The two value quirks of a document in quirks mode (the Quirks Mode standard, §3.2 "The
hashless hex color quirk" and §3.3 "The unitless length quirk"), as a rewrite of a
declaration's value before it is read:

- a property of `lengthProps` reads a plain number token (at the top level, or for `clip` in
  `rect()`) as that many `px`: `width: 10` is `width: 10px`;
- a property of `colorProps` reads a hash-less hex colour: an identifier of 3 or 6 hex digits,
  or a number or dimension with an integer value of at most 6 characters (zero-padded to 6),
  as that colour: `color: 123` is `color: #000123`.

Only declarations of those properties change (`quirkDecl_other`); a document in no-quirks
mode reads its sheets as before (`CSS.parseRawQ_false`). The rewrite is one pass over the
value's characters. Not done: escapes in a hash-less colour (`\31 23`), the quirks in
`style` attributes and CSSOM. -/
namespace L4Factoidal.Rendering.CssQuirks

/-- The properties of the unitless length quirk (Quirks Mode §3.3). -/
def lengthProps : List String :=
  ["background-position", "border-spacing", "border-top-width", "border-right-width",
   "border-bottom-width", "border-left-width", "border-width", "bottom", "clip", "font-size",
   "height", "left", "letter-spacing", "margin-right", "margin-left", "margin-top",
   "margin-bottom", "margin", "max-height", "max-width", "min-height", "min-width",
   "padding-top", "padding-right", "padding-bottom", "padding-left", "padding", "right",
   "text-indent", "top", "vertical-align", "width", "word-spacing"]

/-- The properties of the hashless hex color quirk (Quirks Mode §3.2). -/
def colorProps : List String :=
  ["background-color", "border-color", "border-top-color", "border-right-color",
   "border-bottom-color", "border-left-color", "color"]

/-- The leading decimal digits of `cs`, and the rest. -/
def takeDigits : List Char → List Char × List Char
  | c :: cs => if c.isDigit then let (a, r) := takeDigits cs; (c :: a, r) else ([], c :: cs)
  | [] => ([], [])

theorem takeDigits_length (cs : List Char) : (takeDigits cs).2.length ≤ cs.length := by
  induction cs with
  | nil => simp [takeDigits]
  | cons c cs ih =>
    simp only [takeDigits]
    split <;> simp_all <;> omega

/-- `cs` starts an identifier (CSS Syntax 3 §4.3.9, roughly: a letter, `_`, a non-ASCII
character, an escape, or `-` before one of those or `-`): after a number it makes a
dimension. -/
def startsIdent : List Char → Bool
  | '-' :: c :: _ => c.isAlpha || c == '_' || c == '-' || c.toNat ≥ 0x80 || c == '\\'
  | c :: _ => c.isAlpha || c == '_' || c.toNat ≥ 0x80 || c == '\\'
  | [] => false

/-- The exponent of a number (`e3`, `E-2`) at the head of `cs`, and the rest. -/
def exponent : List Char → List Char × List Char
  | e :: d :: r =>
    if (e == 'e' || e == 'E') && d.isDigit then let (x, r') := takeDigits (d :: r); (e :: x, r')
    else if (e == 'e' || e == 'E') && (d == '+' || d == '-') then
      match r with
      | d2 :: r3 => if d2.isDigit then let (x, r4) := takeDigits (d2 :: r3); (e :: d :: x, r4) else ([], e :: d :: r)
      | [] => ([], e :: d :: r)
    else ([], e :: d :: r)
  | cs => ([], cs)

/-- A number token at the head of `cs` (CSS Syntax 3 §4.3.12): its characters and the rest. -/
def numberAt (cs : List Char) : Option (List Char × List Char) :=
  let (sgn, r) := match cs with
    | '+' :: r => (['+'], r)
    | '-' :: r => (['-'], r)
    | r => ([], r)
  let (ip, r) := takeDigits r
  let (fp, r) := match r with
    | '.' :: d :: r' => if d.isDigit then (let (f, r'') := takeDigits (d :: r'); ('.' :: f, r'')) else ([], r)
    | _ => ([], r)
  if ip.isEmpty && fp.isEmpty then none else
  let (ex, r) := exponent r
  some (sgn ++ ip ++ fp ++ ex, r)

/-- A string's characters up to and with its closing quote `q`, and the rest. -/
def takeString (q : Char) : List Char → List Char × List Char
  | '\\' :: d :: r => let (s, t) := takeString q r; ('\\' :: d :: s, t)
  | c :: r => if c == q then ([c], r) else let (s, t) := takeString q r; (c :: s, t)
  | [] => ([], [])

/-- A comment's characters after `/*`, up to and with `*/`, and the rest. -/
def takeComment : List Char → List Char × List Char
  | '*' :: '/' :: r => (['*', '/'], r)
  | c :: r => let (s, t) := takeComment r; (c :: s, t)
  | [] => ([], [])

/-- The unitless length quirk over the characters `cs` (`fuel` steps, each taking at least
one character): a number token that starts a component at the top level (or, with `clip`,
in `rect()`), and is not a dimension or a percentage, gets `px`. `acc` is the output so far,
reversed. -/
def lengthsGo (clip : Bool) : Nat → List Char → Nat → Bool → List Char → List Char
  | 0, cs, _, _, acc => acc.reverse ++ cs
  | _ + 1, [], _, _, acc => acc.reverse
  | f + 1, c :: rest, depth, boundary, acc =>
    if c == '"' || c == '\'' then
      let (s, r) := takeString c rest
      lengthsGo clip f r depth false (s.reverse ++ c :: acc)
    else if c == '/' && rest.head? == some '*' then
      let (s, r) := takeComment (rest.drop 1)
      lengthsGo clip f r depth boundary (s.reverse ++ '*' :: '/' :: acc)
    else if c == '\\' then
      match rest with
      | d :: r => lengthsGo clip f r depth false (d :: c :: acc)
      | [] => lengthsGo clip f [] depth false (c :: acc)
    else if c == '(' then lengthsGo clip f rest (depth + 1) true (c :: acc)
    else if c == ')' then lengthsGo clip f rest (depth - 1) false (c :: acc)
    else if c.isWhitespace || c == ',' then lengthsGo clip f rest depth true (c :: acc)
    else if boundary && (depth == 0 || (clip && depth == 1)) then
      match numberAt (c :: rest) with
      | some (num, r) =>
        if startsIdent r || r.head? == some '%' then lengthsGo clip f r depth false (num.reverse ++ acc)
        else lengthsGo clip f r depth false ('x' :: 'p' :: num.reverse ++ acc)
      | none => lengthsGo clip f rest depth false (c :: acc)
    else lengthsGo clip f rest depth false (c :: acc)

/-- The unitless length quirk on a value (`lengthsGo`). -/
def unitless (clip : Bool) (v : String) : String :=
  String.ofList (lengthsGo clip (v.length + 1) v.toList 0 true [])

/-- A hex digit. -/
def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')

/-- The hashless hex color quirk on one component `t`: an identifier of 3 or 6 hex digits is
that colour; a number or dimension with an integer value (an optional `+`, digits, then hex
letters; no exponent) of at most 6 characters is that colour zero-padded to 6. Else `t`. -/
def hashless (t : String) : String :=
  let cs := t.toList
  let (plus, r) := match cs with
    | '+' :: r => (true, r)
    | r => (false, r)
  if r.isEmpty || !r.all isHex then t
  else match r with
    | c :: _ =>
      if c.isDigit then
        let rest := (takeDigits r).2
        let expo := match rest with
          | e :: d :: _ => (e == 'e' || e == 'E') && d.isDigit
          | _ => false
        if expo || r.length > 6 then t else "#" ++ String.ofList (List.replicate (6 - r.length) '0' ++ r)
      else if plus then t
      else if r.length == 3 || r.length == 6 then "#" ++ t else t
    | [] => t

/-- The hashless hex color quirk on a value: each whitespace-separated component of a value
with no function, string, comment or escape. -/
def hashlessValue (v : String) : String :=
  if v.any (fun c => c == '(' || c == '"' || c == '\'' || c == '/' || c == '\\') then v
  else " ".intercalate (((v.splitOn " ").filter (· != "")).map hashless)

/-- A declaration of a document in quirks mode: its value with the quirk of its property. -/
def quirkDecl (d : SheetReader.Decl) : SheetReader.Decl :=
  let k := d.name.toLower
  if (d.value.splitOn "var(").length > 1 then d
  else if lengthProps.contains k then { d with value := unitless (k == "clip") d.value }
  else if colorProps.contains k then { d with value := hashlessValue d.value.trimAscii.toString }
  else d

/-- Kind: functional. Says: the quirks change only the declarations of the properties they
name; every other declaration is read as written. -/
theorem quirkDecl_other (d : SheetReader.Decl) (h1 : lengthProps.contains d.name.toLower = false)
    (h2 : colorProps.contains d.name.toLower = false) : quirkDecl d = d := by
  unfold quirkDecl
  simp only [h1, h2]
  split <;> simp

/-- A leaf of a sheet of a document in quirks mode. -/
def quirkLeaf (leaf : SheetReader.Leaf) : SheetReader.Leaf :=
  { leaf with decls := leaf.decls.map quirkDecl }

#guard unitless false "10" == "10px"
#guard unitless false "1px 2" == "1px 2px"
#guard unitless false "1 -2" == "1px -2px"
#guard unitless false "+1.5" == "+1.5px"
#guard unitless false "calc(1)" == "calc(1)"
#guard unitless false "1a" == "1a"
#guard unitless false "#01" == "#01"
#guard unitless false "+/**/1" == "+/**/1"
#guard unitless false "10%" == "10%"
#guard unitless false "1e3" == "1e3px"
#guard unitless true "rect(auto, auto, auto, 1)" == "rect(auto, auto, auto, 1px)"
#guard unitless false "\"1\"" == "\"1\""
#guard hashless "123" == "#000123"
#guard hashless "abc" == "#abc"
#guard hashless "aabbcc" == "#aabbcc"
#guard hashless "1ab" == "#0001ab"
#guard hashless "+12345a" == "#12345a"
#guard hashless "+123456a" == "+123456a"
#guard hashless "aaaa" == "aaaa"
#guard hashless "-1" == "-1"
#guard hashless "+a" == "+a"
#guard hashless "1e3" == "1e3"
#guard hashless "1234567" == "1234567"
#guard hashless "red" == "red"

end L4Factoidal.Rendering.CssQuirks
