/-
L4Factoidal.WHATWG.MimeType — MIME types (MIME Sniffing Standard,
https://mimesniff.spec.whatwg.org/): §4.4 "parse a MIME type", §4.5 "serialize a MIME
type", §4.6 the JavaScript MIME type essences, and the two decisions of a response's type
that a page must not influence by its body: the `X-Content-Type-Options: nosniff` rule of
Fetch (§2.2.6 "should response to request be blocked due to nosniff?") and the type a
resource is treated as (`computedType`, MIME Sniffing §7 with its no-sniff flag).

The strings are code points. An HTTP header value is its bytes read as code points
(isomorphic decoding), so a "quoted-string token code point" above U+007F is a byte.

## Decisions

* `nosniff` is absolute for scripts and style sheets: with it, a response whose declared type
  is not a JavaScript MIME type never runs as a script, whatever its body looks like
  (`nosniff_never_script`, `nosniff_blocks_script`), and one whose declared type is not
  `text/css` is never a style sheet (`nosniff_blocks_style`).
* The body is consulted only without `nosniff` (`computedType_nosniff`).

Every loop is a core list combinator or a tail call on a shorter list.
-/

namespace L4Factoidal.WHATWG.MimeType

/-! ## Code points (Fetch §2.2, MIME Sniffing §4.1) -/

/-- HTTP whitespace: tab, line feed, carriage return, space. -/
def isHttpWs (c : Char) : Bool := c == '\t' || c == '\n' || c == '\r' || c == ' '

/-- An HTTP token code point. -/
def isTokenChar (c : Char) : Bool :=
  (c.toNat < 128 && c.isAlphanum) || "!#$%&'*+-.^_`|~".toList.contains c

/-- An HTTP quoted-string token code point: tab, U+0020 to U+007E, U+0080 to U+00FF. -/
def isQuotedChar (c : Char) : Bool :=
  c == '\t' || (0x20 ≤ c.toNat && c.toNat ≤ 0x7E) || (0x80 ≤ c.toNat && c.toNat ≤ 0xFF)

/-- ASCII lower case. -/
def lowerChar (c : Char) : Char := if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Without trailing HTTP whitespace. -/
def trimEnd (cs : List Char) : List Char := (cs.reverse.dropWhile isHttpWs).reverse

/-- Without leading and trailing HTTP whitespace. -/
def trim (cs : List Char) : List Char := trimEnd (cs.dropWhile isHttpWs)

/-! ## The MIME type record (§4.2) -/

/-- A MIME type: type and subtype in ASCII lower case, and its parameters in order (a name
at most once; names in ASCII lower case). -/
structure MimeType where
  type : String
  subtype : String
  params : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited

/-- The essence: `type/subtype`. -/
def MimeType.essence (m : MimeType) : String := m.type ++ "/" ++ m.subtype

/-! ## Parse (§4.4) -/

/-- "Collect an HTTP quoted string" with the extract-value flag (Fetch §2.2), after the
opening quote: the characters after the closing quote, and the value (escapes removed). An
unclosed string ends at the end of the input. -/
def quoted : List Char → List Char → List Char × List Char
  | [], acc => ([], acc.reverse)
  | '"' :: rest, acc => (rest, acc.reverse)
  | ['\\'], acc => ([], ('\\' :: acc).reverse)
  | '\\' :: c :: rest, acc => quoted rest (c :: acc)
  | c :: rest, acc => quoted rest (c :: acc)

/-- Step 11.10: the parameter is kept when its name is a non-empty token, its value is
quoted-string token code points, and the name is new. `acc` is in reverse order. -/
def addParam (acc : List (String × String)) (name value : List Char) : List (String × String) :=
  let n := String.ofList name
  if !name.isEmpty && name.all isTokenChar && value.all isQuotedChar && !(acc.any fun p => p.1 == n)
  then (n, String.ofList value) :: acc else acc

/-- Step 11, the parameters: `cs` is the input from a `;` on (or empty). `fuel` bounds the
turns; each turn drops at least that `;`, so the length of `cs` and one suffices. -/
def paramsGo : List Char → List (String × String) → Nat → List (String × String)
  | _, acc, 0 => acc.reverse
  | [], acc, _ => acc.reverse
  | _ :: cs, acc, fuel + 1 =>
    let cs := cs.dropWhile isHttpWs
    let name := (cs.takeWhile fun c => c != ';' && c != '=').map lowerChar
    match cs.dropWhile (fun c => c != ';' && c != '=') with
    | [] => acc.reverse
    | ';' :: rest => paramsGo (';' :: rest) acc fuel
    | _ :: [] => acc.reverse
    | _ :: '"' :: q =>
      let (after, value) := quoted q []
      paramsGo (after.dropWhile (· != ';')) (addParam acc name value) fuel
    | _ :: value =>
      let raw := trimEnd (value.takeWhile (· != ';'))
      let after := value.dropWhile (· != ';')
      if raw.isEmpty then paramsGo after acc fuel else paramsGo after (addParam acc name raw) fuel

/-- "Parse a MIME type" (§4.4); `none` is failure. -/
def parse (input : String) : Option MimeType :=
  let cs := trim input.toList
  let type := cs.takeWhile (· != '/')
  if type.isEmpty || !type.all isTokenChar then none else
  match cs.dropWhile (· != '/') with
  | [] => none
  | _ :: rest =>
    let subtype := trimEnd (rest.takeWhile (· != ';'))
    if subtype.isEmpty || !subtype.all isTokenChar then none else
    let tail := rest.dropWhile (· != ';')
    some { type := String.ofList (type.map lowerChar), subtype := String.ofList (subtype.map lowerChar),
           params := paramsGo tail [] (tail.length + 1) }

/-! ## Serialize (§4.5) -/

/-- A parameter value as it is written: itself when it is a non-empty token, else a quoted
string with `"` and `\` escaped. -/
def serializeValue (v : String) : String :=
  if !v.isEmpty && v.toList.all isTokenChar then v
  else "\"" ++ String.ofList (v.toList.flatMap fun c => if c == '"' || c == '\\' then ['\\', c] else [c]) ++ "\""

/-- "Serialize a MIME type" (§4.5). -/
def serialize (m : MimeType) : String :=
  m.params.foldl (fun s p => s ++ ";" ++ p.1 ++ "=" ++ serializeValue p.2) m.essence

/-- Parse and serialize: the canonical text of a MIME type, `none` for failure (the type of
`Request.blob()` and `Response.blob()`, Fetch §5 "consume body"). -/
def canonical (input : String) : Option String := (parse input).map serialize

/-! ## A MIME type from header values (Fetch §2.2.4 "extract a MIME type") -/

/-- "Collect an HTTP quoted string" without the extract-value flag, after the opening quote:
the characters after the closing quote, and `acc` (in reverse) with the string as written. -/
def quotedRaw : List Char → List Char → List Char × List Char
  | [], acc => ([], acc)
  | '"' :: rest, acc => (rest, '"' :: acc)
  | ['\\'], acc => ([], '\\' :: acc)
  | '\\' :: c :: rest, acc => quotedRaw rest (c :: '\\' :: acc)
  | c :: rest, acc => quotedRaw rest (c :: acc)

/-- A value of a split header: without leading and trailing HTTP tabs and spaces. `tmp` is
in reverse. -/
def splitValue (tmp : List Char) : String :=
  let tabOrSpace := fun (c : Char) => c == '\t' || c == ' '
  String.ofList ((tmp.dropWhile tabOrSpace).reverse.dropWhile tabOrSpace)

/-- Fetch §2.2.2 "get, decode, and split": the values of a field's combined value, split at
the commas that are not in a quoted string. Each turn takes at least one `"` or `,`. -/
def splitGo : List Char → List Char → List String → Nat → List String
  | _, tmp, acc, 0 => (splitValue tmp :: acc).reverse
  | cs, tmp, acc, fuel + 1 =>
    let tmp := (cs.takeWhile fun c => c != '"' && c != ',').reverse ++ tmp
    match cs.dropWhile (fun c => c != '"' && c != ',') with
    | [] => (splitValue tmp :: acc).reverse
    | '"' :: q =>
      let (after, tmp) := quotedRaw q ('"' :: tmp)
      if after.isEmpty then (splitValue tmp :: acc).reverse else splitGo after tmp acc fuel
    | _ :: after => splitGo after [] (splitValue tmp :: acc) fuel

/-- The values of a combined header value. -/
def splitValues (combined : String) : List String :=
  splitGo combined.toList [] [] (combined.length + 1)

/-- The value of parameter `name`. -/
def MimeType.param (m : MimeType) (name : String) : Option String :=
  (m.params.find? fun p => p.1 == name).map (·.2)

/-- Fetch §2.2.4 "extract a MIME type" from the combined value of the `Content-Type` fields:
the last value that is a MIME type other than `*/*`, with the `charset` of an earlier value
of the same essence when it has none. `none` is failure. -/
def extract (combined : String) : Option MimeType :=
  ((splitValues combined).foldl (fun (st : Option MimeType × Option String) value =>
    match parse value with
    | none => st
    | some t =>
      if t.essence == "*/*" then st
      else if (st.1.map (·.essence)) != some t.essence then (some t, t.param "charset")
      else match t.param "charset", st.2 with
        | none, some c => (some { t with params := t.params ++ [("charset", c)] }, st.2)
        | _, _ => (some t, st.2)) (none, none)).1

/-- The canonical text of the MIME type that `extract` gives; `none` for failure. -/
def extractCanonical (combined : String) : Option String := (extract combined).map serialize

/-! ## Groups (§4.6) -/

/-- The JavaScript MIME type essences. -/
def javaScriptEssences : List String :=
  ["application/ecmascript", "application/javascript", "application/x-ecmascript", "application/x-javascript",
   "text/ecmascript", "text/javascript", "text/javascript1.0", "text/javascript1.1", "text/javascript1.2",
   "text/javascript1.3", "text/javascript1.4", "text/javascript1.5", "text/jscript", "text/livescript",
   "text/x-ecmascript", "text/x-javascript"]

/-- A JavaScript MIME type. -/
def MimeType.isJavaScript (m : MimeType) : Bool := javaScriptEssences.contains m.essence

/-- A JSON MIME type: `application/json`, `text/json`, or a subtype that ends in `+json`. -/
def MimeType.isJson (m : MimeType) : Bool :=
  m.essence == "application/json" || m.essence == "text/json" || m.subtype.endsWith "+json"

/-! ## `nosniff` and the computed type -/

/-- What a response is fetched for, as far as its type matters. -/
inductive Destination where
  /-- A script-like destination (script, worker, import): the response will run. -/
  | script
  /-- A style sheet. -/
  | style
  /-- Anything else. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- Fetch §2.2.6 "should response to request be blocked due to nosniff?": with `nosniff`, a
script-like destination needs a JavaScript MIME type and a style sheet needs `text/css`.
`declared` is the parsed `Content-Type` of the response (`none`: absent or not a MIME type). -/
def nosniffBlocks (nosniff : Bool) (dest : Destination) (declared : Option MimeType) : Bool :=
  nosniff && match dest with
    | .script => !(declared.map (·.isJavaScript)).getD false
    | .style => !(declared.map (·.essence == "text/css")).getD false
    | .other => false

/-- The type a resource is treated as (MIME Sniffing §7 "determine the computed MIME type of
a resource"): with the no-sniff flag it is the declared type; without it, the type that
sniffing the body gave when there is one (`sniffed`: the caller's reading of the body). -/
def computedType (nosniff : Bool) (declared sniffed : Option MimeType) : Option MimeType :=
  if nosniff then declared else
  match sniffed with
  | some t => some t
  | none => declared

/-- A response runs as a classic script: it is not blocked, and its computed type is a
JavaScript MIME type. -/
def runsAsScript (nosniff : Bool) (declared sniffed : Option MimeType) : Bool :=
  !nosniffBlocks nosniff .script declared &&
    ((computedType nosniff declared sniffed).map (·.isJavaScript)).getD false

/-! ## Theorems -/

/-- Kind: security theorem (`nosniff`). Says: with `nosniff`, the computed type of a
resource is its declared type whatever sniffing the body says: the body cannot change it.
Does not say: what sniffing says without `nosniff`. -/
theorem computedType_nosniff (declared sniffed : Option MimeType) :
    computedType true declared sniffed = declared := rfl

/-- Kind: security theorem (`nosniff`, Fetch §2.2.6). Says: with `nosniff`, a response
fetched as a script whose declared type is not a JavaScript MIME type is blocked. Does not
say: anything without `nosniff`. -/
theorem nosniff_blocks_script (declared : Option MimeType)
    (h : (declared.map (·.isJavaScript)).getD false = false) :
    nosniffBlocks true .script declared = true := by
  simp [nosniffBlocks, h]

/-- Kind: security theorem (`nosniff`). Says: with `nosniff`, a response fetched as a style
sheet whose declared type is not `text/css` is blocked. -/
theorem nosniff_blocks_style (declared : Option MimeType)
    (h : (declared.map (·.essence == "text/css")).getD false = false) :
    nosniffBlocks true .style declared = true := by
  simp [nosniffBlocks, h]

/-- Kind: security theorem (`nosniff` never upgrades to a script). Says: with `nosniff`, a
response whose declared type is not a JavaScript MIME type never runs as a script, whatever
type sniffing its body would give: MIME sniffing cannot upgrade it. Does not say: that every
host passes the header to this function (a host that reads a script itself and gives only
its text decides this outside Lean: see the design record). -/
theorem nosniff_never_script (declared sniffed : Option MimeType)
    (h : (declared.map (·.isJavaScript)).getD false = false) :
    runsAsScript true declared sniffed = false := by
  simp [runsAsScript, nosniffBlocks, h]

/-- Kind: totality of the format. Says: a MIME type that `parse` gives has a non-empty type
and subtype. Does not say: that they are tokens in lower case (they are: tested below). -/
theorem parse_nonempty (input : String) (m : MimeType) (h : parse input = some m) :
    m.type ≠ "" ∧ m.subtype ≠ "" := by
  dsimp only [parse] at h
  split at h
  · simp at h
  · rename_i hty
    split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hsub
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨fun e => ?_, fun e => ?_⟩
        · have e' : List.map lowerChar (List.takeWhile (fun x => x != '/') (trim input.toList)) = [] := by
            simpa using e
          rw [List.map_eq_nil_iff] at e'
          simp [e'] at hty
        · rename_i rest _
          have e' : List.map lowerChar (trimEnd (List.takeWhile (fun x => x != ';') rest)) = [] := by
            simpa using e
          rw [List.map_eq_nil_iff] at e'
          simp [e'] at hsub

/-! ## Checks (the cases of WPT mimesniff/mime-types/resources/mime-types.json) -/

#guard canonical "text/html;charset=gbk" == some "text/html;charset=gbk"
#guard canonical "TEXT/HTML;CHARSET=GBK" == some "text/html;charset=GBK"
-- legacy comment syntax is a value to quote
#guard canonical "text/html;charset=gbk(" == some "text/html;charset=\"gbk(\""
#guard canonical "text/html;x=(;charset=gbk" == some "text/html;x=\"(\";charset=gbk"
-- a duplicate parameter: the first one stays
#guard canonical "text/html;charset=gbk;charset=windows-1255" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=();charset=GBK" == some "text/html;charset=\"()\""
-- spaces
#guard canonical "text/html;charset =gbk" == some "text/html"
#guard canonical "text/html ;charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html; charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;charset= gbk" == some "text/html;charset=\" gbk\""
#guard canonical "text/html;charset= \"gbk\"" == some "text/html;charset=\" \\\"gbk\\\"\""
-- U+000B and U+000C are not whitespace
#guard canonical "text/html;charset=\x0bgbk" == some "text/html"
#guard canonical "text/html;\x0ccharset=gbk" == some "text/html"
-- single quotes are token characters
#guard canonical "text/html;charset='gbk'" == some "text/html;charset='gbk'"
#guard canonical "text/html;charset=';charset=GBK" == some "text/html;charset='"
-- invalid parameters are dropped
#guard canonical "text/html;test;charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;test=;charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;';charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;\";charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html ; ; charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;;;;charset=gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;charset= \"\x7f;charset=GBK" == some "text/html;charset=GBK"
#guard canonical "text/html;charset=\"\x7f;charset=foo\";charset=GBK" == some "text/html;charset=GBK"
-- double quotes
#guard canonical "text/html;charset=\"gbk\"" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=\"gbk" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=gbk\"" == some "text/html;charset=\"gbk\\\"\""
#guard canonical "text/html;charset=\" gbk\"" == some "text/html;charset=\" gbk\""
#guard canonical "text/html;charset=\"\\ gbk\"" == some "text/html;charset=\" gbk\""
#guard canonical "text/html;charset=\"\\g\\b\\k\"" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=\"gbk\"x" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=\"\";charset=GBK" == some "text/html;charset=\"\""
#guard canonical "text/html;charset=\";charset=GBK" == some "text/html;charset=\";charset=GBK\""
-- failures
#guard canonical "" == none
#guard canonical "\t" == none
#guard canonical "/" == none
#guard canonical "bogus" == none
#guard canonical "bogus/" == none
#guard canonical "bogus/ " == none
#guard canonical "bogus/bogus/;" == none
#guard canonical "</>" == none
#guard canonical "(/)" == none
#guard canonical "ÿ/ÿ" == none
#guard canonical "text/html(;doesnot=matter" == none
#guard canonical "{/}" == none
#guard canonical "\x00/x" == none
#guard canonical "x/x;\x00=x;bonus=x" == some "x/x;bonus=x"
#guard canonical "x/x;x=\"\x00\";bonus=x" == some "x/x;bonus=x"
-- whitespace around the whole, and a valueless end
#guard canonical " text/html;charset=gbk\t" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=gbk;" == some "text/html;charset=gbk"
#guard canonical "text/html;charset=" == some "text/html"
#guard canonical "x/x;x=\"ÿ\"" == some "x/x;x=\"ÿ\""
#guard canonical "x/x;x=ÿ" == some "x/x;x=\"ÿ\""
#guard canonical "x/x;x=\"Ā\"" == some "x/x"
-- extract a MIME type (Fetch §2.2.4): the last type; a charset carried over; `*/*` skipped
#guard extractCanonical "text/html;charset=gbk" == some "text/html;charset=gbk"
#guard extractCanonical "text/plain;charset=gbk, text/html" == some "text/html"
#guard extractCanonical "text/html;charset=gbk, text/html" == some "text/html;charset=gbk"
#guard extractCanonical "text/html;charset=gbk, text/html;x=y" == some "text/html;x=y;charset=gbk"
#guard extractCanonical "text/html, */*" == some "text/html"
#guard extractCanonical "text/html, bogus" == some "text/html"
#guard extractCanonical "text/html;x=\"a,b\"" == some "text/html;x=\"a,b\""
#guard extractCanonical "" == none && extractCanonical "," == none && extractCanonical "*/*" == none
#guard splitValues "a, b ,\"c,d\" e,\tf" == ["a", "b", "\"c,d\" e", "f"]
#guard splitValues "" == [""] && splitValues "\"x" == ["\"x"]
-- the groups
#guard ((parse "Text/JavaScript; charset=utf-8").map (·.isJavaScript)) == some true
#guard ((parse "text/plain").map (·.isJavaScript)) == some false
#guard ((parse "application/ld+json").map (·.isJson)) == some true
-- nosniff
#guard nosniffBlocks true .script (parse "text/plain") && nosniffBlocks true .script none
#guard !nosniffBlocks true .script (parse "text/javascript") && !nosniffBlocks false .script (parse "text/plain")
#guard nosniffBlocks true .style (parse "text/html") && !nosniffBlocks true .style (parse "text/css;charset=utf-8")
#guard !runsAsScript true (parse "text/plain") (parse "text/javascript")
#guard runsAsScript false (parse "text/plain") (parse "text/javascript")

end L4Factoidal.WHATWG.MimeType
