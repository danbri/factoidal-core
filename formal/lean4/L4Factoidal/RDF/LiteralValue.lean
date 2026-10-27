/-
L4Factoidal.RDF.LiteralValue — the value of an RDF literal, its validity and
its canonical lexical form; and the literal of a JavaScript value, with an
optional datatype the caller names
(https://github.com/danbri/factoidal/issues/1051 items 1, 2 and 3).

Every echo of a library API (RDFLib `Literal.toPython`/`ill_typed`, Jena
`Literal.getValue`/`LiteralLabel.isWellFormed`/`createTypedLiteral(Object)`,
RDF4J `Literal.intValue`/`XMLDatatypeUtil.isValid`) asks the same three
questions. This module answers them ONCE, from the shared XSD code:

  * the lexical-to-value mapping is `XSD.lexicalFor .xsd11`
    (`XSD/Lexical.lean`, over `XSD.lexicalMap`, XSD 1.1 Part 2 §3), with no
    whiteSpace processing, which is RDF 1.1 Semantics §7's reading (the
    lexical space as XSD defines it; `" 3 "^^xsd:int` is ill-typed, rdf-mt
    `xmlsch-02-whitespace-facet-*`). A lexical form that `whiteSpace` would
    change is outside the lexical space of a `replace` or `collapse` type;
  * the canonical form is `XSD.canonicalMap` (§3.3 and §3.4, the float and
    double cases by §E.1);
  * `rdf:langString`, `rdf:dirLangString` (RDF 1.2 Concepts §3.3),
    `rdf:XMLLiteral` (RDF 1.1 Concepts §5.1) and `rdf:JSON` (RDF 1.2
    Concepts §5.3) are recognised with the predicates of `RDF/Datatypes.lean`
    and `RDF/LangTag.lean`;
  * the datatype of a JavaScript value with no named datatype is
    `XSD.JsValue.jsLiteral`'s table (the module header there gives the table
    and its reasons).

## The value as JSON

A value crosses the boundary as a JSON object with a `kind`. A number that a
JavaScript number may not hold exactly is a decimal STRING; the member
`number` is present only when the value is exactly a binary64 value (it is
then the exact decimal text, so `JSON.parse` gives that value with no
rounding). Integer components (`year`, `month`, `months`, ...) are JSON
numbers when their magnitude is at most 2^53 − 1, else decimal strings.

  kind `string` / `anyURI`  `string`
  kind `boolean`            `boolean`
  kind `decimal`            `decimal` (the canonical decimal text), `integer`
                            (true when the value is an integer), `number`
  kind `float` / `double`   finite: `decimal` (the exact value) and `number`;
                            `-0`: also `negativeZero: true`; NaN, ±INF:
                            `special` = `NaN` | `INF` | `-INF`
  kind `duration`           `months` (integer), `seconds` (decimal text)
                            (§3.3.6, the two-property model)
  kind `dateTime`, `time`, `date`, `gYearMonth`, `gYear`, `gMonthDay`,
  `gDay`, `gMonth`          the properties the type has (§3.3.7): `year`,
                            `month`, `day`, `hour`, `minute`, `second`
                            (decimal text), `timezoneOffset` (minutes)
  kind `hexBinary` / `base64Binary`  `hex` (the octets, upper-case hex)
  kind `QName` / `NOTATION` `prefix`, `localName`
  kind `list`               `items` (§3.4.5 NMTOKENS, IDREFS, ENTITIES)
  kind `langString`         `string`, `language` (lower case, RDF 1.1
                            Concepts §3.3), and `direction` for
                            `rdf:dirLangString`

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDF.LangTag
import L4Factoidal.XSD.JsValue
import L4Factoidal.XSD.Lexical
import L4Factoidal.XSD.CanonicalTheorems
import L4Factoidal.Fn.Cast
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.RDF.LiteralValue

open L4Factoidal.XSD
open L4Factoidal.JSON

/-! ## The lexical-to-value mapping -/

/-- 2^53 − 1. -/
def maxSafe : Nat := 9007199254740991

/-- The value of `lex` under the built-in `b`, RDF 1.1 Semantics §7: no
whiteSpace processing, so a form that `whiteSpace` would change is outside
the lexical space. -/
def xsdValue (b : Builtin) (lex : String) : Option Val :=
  if applyWhiteSpace b.whiteSpace lex != lex then none else lexicalFor .xsd11 b lex

/-- The XSD built-ins a literal may name. The two ur-types are not datatypes
of a literal (XSD 1.1 Part 2 §3.2.1-§3.2.2: `anySimpleType` and
`anyAtomicType` have no lexical mapping of their own). -/
def literalBuiltin? (dt : String) : Option Builtin :=
  match builtinOfIri? dt with
  | some .anySimpleType | some .anyAtomicType => none
  | r => r

/-! ## The value as JSON -/

def intJson (i : Int) : Json :=
  if i.natAbs ≤ maxSafe then .number (toString i) else .string (toString i)

def natJson (n : Nat) : Json := intJson n

/-- The canonical decimal text of `d` when `d` is exactly a binary64 value. -/
def decNumber? (d : Dec) : Option String :=
  let n := Dec.norm d
  let f := canonDouble (.num (n.mantissa < 0) n.mantissa.natAbs (-(n.scale : Int)))
  if Fn.Cast.floatingDecimal f == some n then some (Dec.canonical n) else none

def fvalFields (f : Fval) : List (String × Json) :=
  match f.cls with
  | .nan => [("special", .string "NaN")]
  | .inf => [("special", .string (if f.neg then "-INF" else "INF"))]
  | .zero =>
      [("decimal", .string "0"), ("number", .number (if f.neg then "-0" else "0"))] ++
      (if f.neg then [("negativeZero", .bool true)] else [])
  | .finite .. =>
      match Fn.Cast.floatingDecimal f with
      | some d => [("decimal", .string d.canonical), ("number", .number d.canonical)]
      | none => []

def dtKindName : DTKind → String
  | .dateTime => "dateTime" | .time => "time" | .date => "date"
  | .gYearMonth => "gYearMonth" | .gYear => "gYear" | .gMonthDay => "gMonthDay"
  | .gDay => "gDay" | .gMonth => "gMonth"

def dtFields (v : DTValue) : List (String × Json) :=
  (v.year.toList.map fun y => ("year", intJson y)) ++
  (v.month.toList.map fun m => ("month", natJson m)) ++
  (v.day.toList.map fun d => ("day", natJson d)) ++
  (v.hour.toList.map fun h => ("hour", natJson h)) ++
  (v.minute.toList.map fun m => ("minute", natJson m)) ++
  (v.second.toList.map fun s => ("second", .string (Dec.canonical s))) ++
  (v.tz.toList.map fun z => ("timezoneOffset", intJson z))

/-- The JSON form of a value (see the module header). -/
def valueJsonFuel : Nat → Val → Json
  | 0, _ => .null
  | fuel + 1, v =>
    match v with
    | .str p s => .object [("kind", .string (if p == .anyURI then "anyURI" else "string")),
                           ("string", .string s)]
    | .bool b => .object [("kind", .string "boolean"), ("boolean", .bool b)]
    | .dec d =>
        .object ([("kind", .string "decimal"), ("decimal", .string (Dec.canonical d)),
                  ("integer", .bool ((Dec.norm d).scale == 0))] ++
                 ((decNumber? d).toList.map fun n => ("number", .number n)))
    | .flt f => .object (("kind", .string "float") :: fvalFields f)
    | .dbl f => .object (("kind", .string "double") :: fvalFields f)
    | .dur d => .object [("kind", .string "duration"), ("months", intJson d.months),
                         ("seconds", .string (Dec.canonical d.seconds))]
    | .dt k w => .object (("kind", .string (dtKindName k)) :: dtFields w)
    | .bin isHex bs => .object [("kind", .string (if isHex then "hexBinary" else "base64Binary")),
                                ("hex", .string (hexOfBytes bs))]
    | .qname p l isN => .object [("kind", .string (if isN then "NOTATION" else "QName")),
                                 ("prefix", .string p), ("localName", .string l)]
    | .seq vs => .object [("kind", .string "list"),
                          ("items", .array (vs.map (valueJsonFuel fuel)))]

def valueJson (v : Val) : Json := valueJsonFuel 4 v

/-! ## A literal: recognised, valid, value, canonical form -/

/-- What the engine knows of one literal. `recognized` false: the datatype
is not one the engine has a lexical space for (RDF 1.1 Concepts §5: such a
literal is still a literal; its value is not known). `valid` is meaningful
only when `recognized`; `value` and `canonical` are present only when the
literal is valid and the datatype has a value model here. -/
structure Analysis where
  recognized : Bool
  valid      : Bool
  value      : Option Json
  canonical  : Option String

def analyzeXsd (b : Builtin) (lex : String) : Analysis :=
  match xsdValue b lex with
  | some v => ⟨true, true, some (valueJson v), some (canonicalMap b v)⟩
  | none => ⟨true, false, none, none⟩

/-- The analysis of a literal (lexical form, datatype IRI, language tag,
direction). -/
def analyze (lex dt : String) (lang : Option String) (dir : Option String) : Analysis :=
  if dt == rdfLangString.val || dt == rdfDirLangString.val then
    match lang with
    | none => ⟨true, false, none, none⟩
    | some tag =>
      if isWellFormedLangTag tag then
        ⟨true, true, some (.object ([("kind", .string "langString"), ("string", .string lex),
            ("language", .string tag.toLower)] ++ (dir.toList.map fun d => ("direction", .string d)))),
         some lex⟩
      else ⟨true, false, none, none⟩
  else if dt == rdfXMLLiteral.val then ⟨true, xmlLiteralWellFormed lex, none, none⟩
  else if dt == rdfJSON.val then ⟨true, rdfJsonLexicalOk lex, none, none⟩
  else match literalBuiltin? dt with
    | some b => analyzeXsd b lex
    | none => ⟨false, false, none, none⟩

/-- The members of the op answer. -/
def Analysis.fields (a : Analysis) (dt : String) : List (String × Json) :=
  [("datatype", .string dt), ("recognized", .bool a.recognized)] ++
  (if a.recognized then [("valid", .bool a.valid)] else []) ++
  (a.value.toList.map fun v => ("value", v)) ++
  (a.canonical.toList.map fun c => ("canonical", .string c))

/-! ## The literal of a JavaScript value, with a named datatype

`jsValueLiteral tag v hint`: with no `hint`, `JsValue.jsLiteral`'s table.
With a `hint` (an XSD built-in), the literal of the value under that
datatype, or a refusal when the value is not in its value space:

  * `string`: the string is a lexical form of `hint`; it must be in the
    lexical space and is kept as given (RDF 1.1 Concepts §3.3).
  * `boolean`: only `xsd:boolean`.
  * `number`, `bigint`, integer types and `decimal`: the EXACT value (a
    number is its binary64 value: `2^60` is `1152921504606846976`, `0.1` is
    `0.1000000000000000055511151231257827021181583404541015625`); it must be
    in the type's value space (an integer, within the type's bounds). Give a
    string for a decimal lexical form.
  * `number`, `bigint`, `float` and `double`: the value the type's lexical
    mapping gives to the JavaScript text (`Number::toString`), that is, the
    value of the literal `"<text>"^^hint`: it rounds to the nearest value. A
    finite value that rounds to an infinity is refused. NaN and ±Infinity
    are `NaN`, `INF`, `-INF`.
  * `date`: `xsd:dateTime` and `xsd:dateTimeStamp` (UTC).

Every other pair is refused. The lexical form of a non-string answer is the
canonical form (`canonicalMap`). -/

/-- A named datatype: an XSD built-in, by its IRI or by its local name
(`int`, `dateTime`), so a caller need not write the XSD namespace. -/
def hintOf? (s : String) : Option Builtin :=
  match literalBuiltin? s with
  | some b => some b
  | none =>
    match builtinOfName? s with
    | some .anySimpleType | some .anyAtomicType => none
    | r => r

def notInSpace (what : String) (b : Builtin) : Except String (Builtin × String) :=
  .error s!"literalFromValue: {what} is not in the value space of xsd:{b.localName} (XML Schema 1.1 Part 2 section 2.2.1)"

/-- The exact value of a numeric JavaScript value (`number` text or `bigint`
text) as a decimal; `none` for NaN and the infinities. -/
def exactDecimal (tag v : String) : Option Dec :=
  if tag == "bigint" then (parseIntegerLex v).map Dec.ofInt
  else match lexicalMap .double v with
    | some (.dbl f) => Fn.Cast.floatingDecimal f
    | _ => none

def jsSpecial? (v : String) : Option String :=
  if v == "NaN" then some "NaN" else if v == "Infinity" then some "INF"
  else if v == "-Infinity" then some "-INF" else none

def numericWithHint (tag v : String) (b : Builtin) : Except String (Builtin × String) :=
  if tag == "bigint" && !(parseIntegerLex v).isSome then
    .error s!"literalFromValue: '{v}' is not the text of a BigInt"
  else if tag == "number" && (jsSpecial? v).isNone && (lexicalMap .double v).isNone then
    .error s!"literalFromValue: '{v}' is not the text of a Number"
  else if b == .double || b == .float then
    match jsSpecial? v with
    | some sp => .ok (b, sp)
    | none =>
      match lexicalMap b v with
      | some val@(.dbl f) | some val@(.flt f) =>
          if f.cls == .inf then notInSpace s!"{tag} {v} (it rounds to an infinity)" b
          else .ok (b, canonicalMap b val)
      | _ => notInSpace s!"{tag} {v}" b
  else if (intBounds b).isSome then
    match exactDecimal tag v with
    | some d =>
        match d.toInt? with
        | some i => if inIntBounds b i then .ok (b, canonicalMap b (.dec (Dec.ofInt i)))
                    else notInSpace s!"{tag} {v}" b
        | none => notInSpace s!"{tag} {v} (not an integer)" b
    | none => notInSpace s!"{tag} {v}" b
  else if b == .decimal then
    match exactDecimal tag v with
    | some d => .ok (b, canonicalMap b (.dec d))
    | none => notInSpace s!"{tag} {v}" b
  else notInSpace s!"a {tag}" b

/-- The datatype and the lexical form of a tagged JavaScript value
(`{"js":tag,"v":text}`, the encoding of `Wasm/Ops/ExtFns.lean`), with an
optional named datatype. -/
def jsValueLiteral (tag v : String) (hint : Option Builtin) : Except String (Builtin × String) :=
  match hint with
  | none =>
      match JsValue.jsLiteral tag v with
      | some (name, lex) =>
          match builtinOfName? name with
          | some b => .ok (b, lex)
          | none => .error s!"literalFromValue: no datatype {name}"
      | none => .error s!"literalFromValue: a JavaScript {tag} '{v}' has no literal (the table of XSD.JsValue.jsLiteral)"
  | some b =>
      if tag == "string" then
        if (xsdValue b v).isSome then .ok (b, v)
        else .error s!"literalFromValue: '{v}' is not in the lexical space of xsd:{b.localName} (XML Schema 1.1 Part 2 section 3)"
      else if tag == "boolean" then
        if b == .boolean then
          match JsValue.jsLiteral tag v with
          | some (_, lex) => .ok (b, lex)
          | none => .error s!"literalFromValue: '{v}' is not a boolean"
        else notInSpace "a boolean" b
      else if tag == "date" then
        if b == .dateTime || b == .dateTimeStamp then
          match JsValue.epochMillisLexical v with
          | some lex => .ok (b, lex)
          | none => .error s!"literalFromValue: the Date '{v}' is not a valid time value (ECMAScript section 21.4.1.1)"
        else notInSpace "a Date (an instant)" b
      else if tag == "number" || tag == "bigint" then numericWithHint tag v b
      else .error s!"literalFromValue: a JavaScript {tag} has no literal"

/-! ## Theorems -/

/-- `valid` is exactly "the lexical form has a value under the datatype". -/
theorem analyzeXsd_valid (b : Builtin) (lex : String) :
    (analyzeXsd b lex).valid = (xsdValue b lex).isSome := by
  unfold analyzeXsd
  cases h : xsdValue b lex <;> simp

/-- The canonical form of a valid integer-typed literal has the same value
(XSD 1.1 Part 2 §2.3.1; `CanonicalTheorems.integer_canonical_roundTrip`). -/
theorem integer_canonical_sameValue (b : Builtin) (hb : (intBounds b).isSome = true) (i : Int)
    (hin : inIntBounds b i = true) :
    lexicalMap b (canonicalMap b (.dec (Dec.ofInt i))) = some (.dec (Dec.ofInt i)) :=
  CanonicalTheorems.integer_canonical_roundTrip b hb i hin

/-- An answer for an integer type is the canonical form of an integer in the
type's bounds, so it is in the type's lexical space with that value. -/
theorem numericWithHint_integer (tag v : String) (b : Builtin) (hb : (intBounds b).isSome = true)
    (hnd : b ≠ .double) (hnf : b ≠ .float) (lex : String)
    (h : numericWithHint tag v b = .ok (b, lex)) :
    ∃ i, inIntBounds b i = true ∧ lex = canonicalMap b (.dec (Dec.ofInt i)) := by
  unfold numericWithHint at h
  have hd1 : (b == .double) = false := by simp [hnd]
  have hd2 : (b == .float) = false := by simp [hnf]
  simp only [hd1, hd2, Bool.or_false, Bool.false_eq_true, if_false, hb, if_true] at h
  repeat' (split at h)
  all_goals (first | (simp [notInSpace] at h) | skip)
  all_goals (first | (exact ⟨_, by assumption, h.symm⟩) | skip)

/-- A string with a named datatype is kept as given, and only when it is in
that datatype's lexical space. -/
theorem jsValueLiteral_string (v : String) (b : Builtin) (b' : Builtin) (lex : String)
    (h : jsValueLiteral "string" v (some b) = .ok (b', lex)) :
    b' = b ∧ lex = v ∧ (xsdValue b v).isSome = true := by
  unfold jsValueLiteral at h
  simp only [beq_self_eq_true, if_true] at h
  split at h
  · rename_i hv
    have h2 := Prod.mk.inj (Except.ok.inj h)
    exact ⟨h2.1.symm, h2.2.symm, hv⟩
  · simp at h

#print axioms analyzeXsd_valid
#print axioms integer_canonical_sameValue
#print axioms numericWithHint_integer
#print axioms jsValueLiteral_string

/-! ## Build-time checks (positive and negative) -/

private def xsd (n : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ n
private def js (a : Analysis) : String :=
  (Json.object (a.fields "")).toString
private def okLex (tag v : String) (hint : Option Builtin) : Option (String × String) :=
  match jsValueLiteral tag v hint with
  | .ok (b, lex) => some (b.localName, lex)
  | .error _ => none

-- Integers: value, canonical form, number when exact; bounds decide validity.
#guard (analyze "01" (xsd "integer") none none).canonical == some "1"
#guard (analyze "+99" (xsd "int") none none).valid
#guard !(analyze "2147483648" (xsd "int") none none).valid
#guard !(analyze "1.0" (xsd "integer") none none).valid
#guard !(analyze " 3 " (xsd "int") none none).valid
#guard js (analyze "-7" (xsd "byte") none none) ==
  "{\"datatype\":\"\",\"recognized\":true,\"valid\":true,\"value\":{\"kind\":\"decimal\",\"decimal\":\"-7\",\"integer\":true,\"number\":-7},\"canonical\":\"-7\"}"
-- A large integer is a decimal string with no number.
#guard ((analyze "9007199254740993" (xsd "integer") none none).value.map (·.toString)) ==
  some "{\"kind\":\"decimal\",\"decimal\":\"9007199254740993\",\"integer\":true}"
#guard ((analyze "9007199254740992" (xsd "integer") none none).value.map (·.toString)) ==
  some "{\"kind\":\"decimal\",\"decimal\":\"9007199254740992\",\"integer\":true,\"number\":9007199254740992}"
-- Decimals: 0.5 is exact in binary64, 0.1 is not.
#guard ((analyze "0.50" (xsd "decimal") none none).value.map (·.toString)) ==
  some "{\"kind\":\"decimal\",\"decimal\":\"0.5\",\"integer\":false,\"number\":0.5}"
#guard ((analyze "0.1" (xsd "decimal") none none).value.map (·.toString)) ==
  some "{\"kind\":\"decimal\",\"decimal\":\"0.1\",\"integer\":false}"
#guard (analyze "1." (xsd "decimal") none none).canonical == some "1"
-- Doubles: exact decimal, number, canonical form (§3.3.5.2).
#guard ((analyze "0.1" (xsd "double") none none).value.map (·.toString)) ==
  some "{\"kind\":\"double\",\"decimal\":\"0.1000000000000000055511151231257827021181583404541015625\",\"number\":0.1000000000000000055511151231257827021181583404541015625}"
#guard (analyze "0.1" (xsd "double") none none).canonical == some "1.0E-1"
#guard (analyze "1e3" (xsd "float") none none).canonical == some "1.0E3"
#guard ((analyze "-0" (xsd "double") none none).value.map (·.toString)) ==
  some "{\"kind\":\"double\",\"decimal\":\"0\",\"number\":-0,\"negativeZero\":true}"
#guard ((analyze "-INF" (xsd "double") none none).value.map (·.toString)) ==
  some "{\"kind\":\"double\",\"special\":\"-INF\"}"
#guard !(analyze "Infinity" (xsd "double") none none).valid
#guard !(analyze "1e" (xsd "double") none none).valid
-- Booleans, strings.
#guard ((analyze "1" (xsd "boolean") none none).value.map (·.toString)) ==
  some "{\"kind\":\"boolean\",\"boolean\":true}"
#guard (analyze "1" (xsd "boolean") none none).canonical == some "true"
#guard !(analyze "yes" (xsd "boolean") none none).valid
#guard (analyze "a b" (xsd "token") none none).valid
#guard !(analyze "a  b" (xsd "token") none none).valid
#guard !(analyze "a\tb" (xsd "normalizedString") none none).valid
#guard !(analyze "1a" (xsd "NCName") none none).valid
-- Date/time: the properties the type has.
#guard ((analyze "2026-10-27T10:30:15.250+01:00" (xsd "dateTime") none none).value.map (·.toString)) ==
  some "{\"kind\":\"dateTime\",\"year\":2026,\"month\":10,\"day\":27,\"hour\":10,\"minute\":30,\"second\":\"15.25\",\"timezoneOffset\":60}"
#guard (analyze "2026-10-27T10:30:15.250+01:00" (xsd "dateTime") none none).canonical ==
  some "2026-10-27T10:30:15.25+01:00"
#guard ((analyze "--12-25" (xsd "gMonthDay") none none).value.map (·.toString)) ==
  some "{\"kind\":\"gMonthDay\",\"month\":12,\"day\":25}"
#guard !(analyze "2026-02-30" (xsd "date") none none).valid
#guard !(analyze "2026-10-27T10:30:00" (xsd "dateTimeStamp") none none).valid
#guard ((analyze "P1Y2M3DT4H" (xsd "duration") none none).value.map (·.toString)) ==
  some "{\"kind\":\"duration\",\"months\":14,\"seconds\":\"273600\"}"
#guard (analyze "P0Y14M" (xsd "duration") none none).canonical == some "P1Y2M"
#guard !(analyze "P1Y" (xsd "dayTimeDuration") none none).valid
-- Binary, lists.
#guard ((analyze "0fb7" (xsd "hexBinary") none none).value.map (·.toString)) ==
  some "{\"kind\":\"hexBinary\",\"hex\":\"0FB7\"}"
#guard (analyze "0fb7" (xsd "hexBinary") none none).canonical == some "0FB7"
#guard !(analyze "0fb" (xsd "hexBinary") none none).valid
-- RDF datatypes.
#guard ((analyze "chat" "http://www.w3.org/1999/02/22-rdf-syntax-ns#langString" (some "FR") none).value.map (·.toString)) ==
  some "{\"kind\":\"langString\",\"string\":\"chat\",\"language\":\"fr\"}"
#guard (analyze "<a>b</a>" "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral" none none).valid
#guard !(analyze "<a>b" "http://www.w3.org/1999/02/22-rdf-syntax-ns#XMLLiteral" none none).valid
#guard (analyze "{\"a\":1}" "http://www.w3.org/1999/02/22-rdf-syntax-ns#JSON" none none).valid
-- A datatype the engine does not have: not recognised, no verdict.
#guard !(analyze "x" "http://example.org/dt" none none).recognized
#guard !(analyze "x" (xsd "anySimpleType") none none).recognized
#guard js (analyze "x" "http://example.org/dt" none none) == "{\"datatype\":\"\",\"recognized\":false}"

-- The JavaScript-value table with no named datatype (JsValue.jsLiteral).
#guard okLex "number" "99" none == some ("integer", "99")
#guard okLex "number" "1.5" none == some ("double", "1.5E0")
#guard okLex "bigint" "99" none == some ("integer", "99")
#guard okLex "boolean" "true" none == some ("boolean", "true")
#guard okLex "string" "x" none == some ("string", "x")
#guard okLex "date" "0" none == some ("dateTime", "1970-01-01T00:00:00Z")
#guard okLex "symbol" "x" none == none
-- A named datatype.
#guard okLex "number" "99" (hintOf? "int") == some ("int", "99")
#guard okLex "number" "99" (hintOf? (xsd "long")) == some ("long", "99")
#guard okLex "number" "99" (hintOf? "double") == some ("double", "9.9E1")
#guard okLex "number" "14" (hintOf? "float") == some ("float", "1.4E1")
#guard okLex "number" "0.1" (hintOf? "float") == some ("float", "1.0E-1")
#guard okLex "number" "1e+39" (hintOf? "float") == none
#guard okLex "number" "NaN" (hintOf? "float") == some ("float", "NaN")
#guard okLex "number" "-Infinity" (hintOf? "double") == some ("double", "-INF")
#guard okLex "number" "1152921504606847000" (hintOf? "integer") == some ("integer", "1152921504606846976")
#guard okLex "number" "0.5" (hintOf? "decimal") == some ("decimal", "0.5")
#guard okLex "number" "1.5" (hintOf? "int") == none
#guard okLex "number" "300" (hintOf? "byte") == none
#guard okLex "number" "-1" (hintOf? "nonNegativeInteger") == none
#guard okLex "number" "NaN" (hintOf? "integer") == none
#guard okLex "number" "99" (hintOf? "string") == none
#guard okLex "number" "abc" (hintOf? "int") == none
#guard okLex "bigint" "123456789012345678901234567890" (hintOf? "decimal") ==
  some ("decimal", "123456789012345678901234567890")
#guard okLex "bigint" "9223372036854775808" (hintOf? "long") == none
#guard okLex "bigint" "9223372036854775807" (hintOf? "long") == some ("long", "9223372036854775807")
#guard okLex "string" "01" (hintOf? "integer") == some ("integer", "01")
#guard okLex "string" "0.1" (hintOf? "decimal") == some ("decimal", "0.1")
#guard okLex "string" "x" (hintOf? "integer") == none
#guard okLex "boolean" "false" (hintOf? "boolean") == some ("boolean", "false")
#guard okLex "boolean" "true" (hintOf? "integer") == none
#guard okLex "date" "0" (hintOf? "dateTimeStamp") == some ("dateTimeStamp", "1970-01-01T00:00:00Z")
#guard okLex "date" "0" (hintOf? "date") == none
#guard okLex "date" "NaN" (hintOf? "dateTime") == none
#guard (hintOf? "http://example.org/dt").isNone
#guard (hintOf? "anyAtomicType").isNone
-- Every answer is in the lexical space of its datatype, with the value of
-- the answer's canonical form equal to the answer's value.
#guard ([("number", "99", "int"), ("number", "0.1", "double"), ("number", "0.1", "float"),
         ("number", "1152921504606847000", "unsignedLong"), ("bigint", "-5", "short"),
         ("number", "2.5", "decimal"), ("date", "1793102400123", "dateTime"),
         ("string", "0042", "integer")].all fun (tag, v, h) =>
  match jsValueLiteral tag v (hintOf? h) with
  | .ok (b, lex) =>
      match xsdValue b lex with
      | some val => xsdValue b (canonicalMap b val) == some val
      | none => false
  | .error _ => false)

end L4Factoidal.RDF.LiteralValue
