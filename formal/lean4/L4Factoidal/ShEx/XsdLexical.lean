/-
L4Factoidal.ShEx.XsdLexical — is a literal's lexical form in its
datatype's lexical space?

ShEx 2.0 §5.4.3 (`datatype`): a node satisfies a datatype constraint
when it is a literal WITH that datatype AND its lexical form is a
valid lexical form for it. The second half is not decoration — the
validation suite spends 144 entries on it, one per shape of
`"1.0"^^xsd:integer`, `"NaN"^^xsd:decimal`, `"+1"^^xsd:negativeInteger`
and their kin, every one of which the port accepted.

## Shared implementation

XSD.Lexical owns edition-sensitive date and numeric lexical decisions.
ShEx's adapter selects the XSD 1.0 reading used by its corpus. Unknown
and context-dependent datatypes remain explicit gaps.

## An UNMODELLED datatype imposes no lexical check

`inXsdLexicalSpace` returns `none` for a datatype whose lexical space
this module does not decide — a non-XSD IRI, or an XSD type nobody
here has written down. `none` is not `true`: the caller keeps the
behaviour it had, and the gap is a `none` that can be counted rather
than a silent `true` that cannot.
-/
import L4Factoidal.XSD.Lexical
import L4Factoidal.Regex.XPath

namespace L4Factoidal.ShEx

open L4Factoidal.XSD

def xsdNs : String := "http://www.w3.org/2001/XMLSchema#"

/-- The local name of an XSD datatype IRI, or `none` for anything
    outside the XSD namespace. -/
def xsdLocal (iri : String) : Option String :=
  if iri.startsWith xsdNs then some (String.ofList (iri.toList.drop xsdNs.length))
  else none

/-- The XSD types whose lexical space is `xsd:string`'s — every string
    is in it, so the check always holds. Listed rather than defaulted
    to `true` so that "no constraint" and "a constraint that always
    holds" stay distinguishable. -/
def stringLikeBases : List String :=
  ["string", "normalizedString", "token", "anyURI", "language",
   "Name", "NCName", "NMTOKEN", "ID", "IDREF", "ENTITY", "QName", "NOTATION"]

def binaryBases : List String := ["hexBinary", "base64Binary"]

/-- `xsd:boolean` (§3.3.2). -/
def isBooleanLexical (s : String) : Bool :=
  (parseBooleanLex s).isSome

/-- The lexical-space decision for one datatype IRI. `none` means this
    module does not decide that datatype — see the header. -/
def inXsdLexicalSpace (dtIri lex : String) : Option Bool :=
  match xsdLocal dtIri with
  | none      => none
  | some base =>
      if base == "boolean" then some (isBooleanLexical lex)
      else if stringLikeBases.contains base then some true
      else validLexicalFor .xsd10 base lex

/-! ## The numeric-digit facets (§5.4.6)

`totalDigits` and `fractionDigits` count DIGITS in the lexical form,
so they apply only to a literal whose lexical form is a decimal. One
that is not fails the facet rather than being coerced — the same rule
`matchesNumericFacets` already follows for the ordering facets. -/

/-- The XSD types DERIVED FROM `xsd:decimal`, which are the only ones
    `totalDigits` and `fractionDigits` are defined on (XSD 1.1 Part 2
    §4.3.11, §4.3.12: both facets apply to `xsd:decimal` and to types
    derived from it). `xsd:float` is NOT one of them — its value space
    is the IEEE binary floats, and it has no digit count. -/
def decimalDerivedBases : List String :=
  ["decimal", "integer", "long", "int", "short", "byte",
   "nonNegativeInteger", "positiveInteger", "unsignedLong",
   "unsignedInt", "unsignedShort", "unsignedByte",
   "nonPositiveInteger", "negativeInteger"]

/-- Is this datatype IRI one the digit facets are defined on, with
    `lex` in its lexical space? -/
def digitFacetsApply (dtIri lex : String) : Bool :=
  match xsdLocal dtIri with
  | none      => false
  | some base => decimalDerivedBases.contains base
                 && (inXsdLexicalSpace dtIri lex == some true)

/-- The integer-part and fraction-part digit runs of a decimal lexical
    form, `none` when it is not one. -/
def decimalDigits (s : String) : Option (List Char × List Char) :=
  if (parseDecimalLex s).isNone then none
  else
    let body := if s.startsWith "-" || s.startsWith "+" then s.toList.drop 1 else s.toList
    match (String.ofList body).splitOn "." with
    | [ip, fp] => some (ip.toList, fp.toList)
    | [ip] => some (ip.toList, [])
    | _ => none

/-- `totalDigits`: the count of digits in the value, with leading
    zeros of the integer part and trailing zeros of the fraction NOT
    counted — `007.700` has two, not six. XSD counts digits of the
    VALUE, and those zeros are not part of it. -/
def totalDigitsOf (s : String) : Option Nat :=
  (decimalDigits s).map (fun (ip, fp) =>
    let ipTrim := ip.dropWhile (· == '0')
    let fpTrim := (fp.reverse.dropWhile (· == '0')).reverse
    ipTrim.length + fpTrim.length)

/-- `fractionDigits`: the digits after the point, trailing zeros not
    counted for the same reason. -/
def fractionDigitsOf (s : String) : Option Nat :=
  (parseDecimalLex s).map Dec.fractionDigits

end L4Factoidal.ShEx
