/-
L4Factoidal.RDF.Datatypes — the datatype map `D` of RDF 1.1 Semantics
§7 ("D-interpretations"), for the datatypes the rdf-mt and sparql11
entailment suites recognise: lexical spaces (is a literal well-formed?),
value equality (do two literals denote the same value?), and value-space
membership (is this value in that datatype's space?).

  https://www.w3.org/TR/rdf11-mt/#datatype-interpretations  (§7)
  https://www.w3.org/TR/rdf11-concepts/#section-Datatypes     (Concepts §5)

## Scope — the MODELLED datatypes, stated once

`modelledDatatypes` lists exactly the IRIs this module knows a lexical
space and value space for: `xsd:string`, `rdf:langString`,
`xsd:integer`, `xsd:int`, `xsd:decimal`, `xsd:boolean`, and
`rdf:XMLLiteral` (RDF 1.1 Concepts §5.1: "well-balanced, self-contained
XML content" — decided by wrapping the lexical form in an element and
running the Lean XML parser, `XML/Parser.lean`). A caller that is asked
to recognise any OTHER datatype must say so (the harness reports
`unsupported`), not silently treat it as opaque.

`xsd:string` and `rdf:langString` are recognised by every
D-interpretation (§7: "every D-interpretation ... recognizes the
datatypes rdf:langString and xsd:string"), so `withMinimalD` adds them
to any caller-supplied map.

## The value model

* **Numbers** (`xsd:integer`, `xsd:int`, `xsd:decimal`): a lexical form
  is normalised to `(mantissa : Int, scale : Nat)` with no trailing
  zeros in the fraction (`XSD.Dec.norm`), so `"010"`, `"10"` and
  `"10.0"` all normalise to `(10, 0)` — RDF 1.1 Semantics §7's "the
  value of the literal". `xsd:int` is `xsd:integer` restricted to
  [-2147483648, 2147483647] (XSD 1.1 §3.4.17). The value space of
  `xsd:int` is inside `xsd:integer`'s, which is inside `xsd:decimal`'s
  (XSD 1.1 §3.4: "the ·value space· of integer is the infinite set ...
  a subset of decimal"). `valueInSpace` delegates to `XSD.ValueSpace`,
  including individual decimal values in the integer/int spaces;
  every other pair of modelled datatypes has disjoint value spaces
  (§7: "datatypes ... with disjoint value spaces").
* **Strings**: `xsd:string` values are the lexical forms;
  `rdf:langString` values are (string, lowercased tag) pairs (RDF 1.1
  Concepts §3.3: "the value space of language tags is always in lower
  case"), which is why `"a"@en-us` and `"a"@en-US` are the same value
  (rdf-mt `tex-01`). `Literal.eqb` already compares tags case-
  insensitively, so it is the base of `literalValueEq`.
* **Whitespace**: XSD's whitespace-collapse facet is NOT applied to
  integer / decimal lexical forms — `" 3 "^^xsd:int` is ILL-FORMED.
  That is RDF 1.1 Semantics §7's reading ("the lexical-to-value mapping
  ... of the datatype", with the lexical space as XSD defines it before
  facet pre-processing) and what rdf-mt `xmlsch-02-whitespace-facet-*`
  require; the F\* `XSD.Datatypes.literal_ill_formed` makes the same
  choice, by the same tests.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Core
import L4Factoidal.XML.Parser
import L4Factoidal.XSD.ValueSpace

namespace L4Factoidal.RDF

/-- `xsd:int` — XSD 1.1 §3.4.17. -/
def xsdInt : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩

/-- The datatype IRIs this module models — see the header. -/
def modelledDatatypes : List WfIri :=
  [xsdString, rdfLangString, xsdInteger, xsdInt, xsdDecimal, xsdBoolean, rdfXMLLiteral]

/-- `D` with the two datatypes every D-interpretation recognises. -/
def withMinimalD (D : List WfIri) : List WfIri :=
  let base := if D.contains xsdString then D else D ++ [xsdString]
  if base.contains rdfLangString then base else base ++ [rdfLangString]

/-! ## Numeric lexical forms -/

/-- A normalised decimal value: `mantissa × 10⁻ˢᶜᵃˡᵉ`, fraction with no
trailing zeros (so equality of values is equality of the pair). -/
structure NumVal where
  mantissa : Int
  scale    : Nat
  deriving DecidableEq, Repr

/-- XSD `integer` lexical space (§3.4.13): `[+-]? [0-9]+`, nothing
else — no whitespace, no exponent, no point. -/
def parseIntegerLexical (s : String) : Option Int := XSD.parseIntegerLex s

/-- XSD `decimal` lexical space (§3.3.3): `[+-]? ([0-9]+ ('.' [0-9]*)? |
'.' [0-9]+)`. Returns the normalised value. -/
def parseDecimalLexical (s : String) : Option NumVal :=
  (XSD.parseDecimalLex s).map (fun d => ⟨d.mantissa, d.scale⟩)

/-- XSD `int` bounds (§3.4.17). -/
def intInRange (i : Int) : Bool := XSD.inIntBounds .int i

/-- The numeric value of a literal of a modelled numeric datatype;
`none` when the lexical form is not in the datatype's lexical space or
the datatype is not numeric. -/
def numericValue? (l : Literal) : Option NumVal :=
  if l.datatype == xsdInteger then
    (parseIntegerLexical l.lexicalForm).map (fun i => ⟨i, 0⟩)
  else if l.datatype == xsdInt then
    match parseIntegerLexical l.lexicalForm with
    | some i => if intInRange i then some ⟨i, 0⟩ else none
    | none   => none
  else if l.datatype == xsdDecimal then parseDecimalLexical l.lexicalForm
  else none

def isNumericDatatype (d : WfIri) : Bool :=
  d == xsdInteger || d == xsdInt || d == xsdDecimal

/-! ## XMLLiteral -/

/-- RDF 1.1 Concepts §5.1: the lexical space of `rdf:XMLLiteral` is
"the set of all strings which are well-balanced, self-contained XML
content". Decided by parsing `<x>` ++ lex ++ `</x>` as a document with
the Lean XML parser: balanced content makes it a well-formed document,
a stray `<` or an unclosed tag does not. -/
def xmlLiteralWellFormed (lex : String) : Bool :=
  match XML.parseXML ("<x>" ++ lex ++ "</x>") with
  | .ok _    => true
  | .error _ => false

/-! ## Well-formedness under D -/

/-- Is `l` ILL-FORMED under `D`: its datatype is recognised (in `D`)
and modelled, and its lexical form is outside the lexical space? A
datatype outside `D` is never checked (§7: unrecognised datatype IRIs
are treated as opaque), and a recognised datatype this module does not
model is never checked either — the CALLER must refuse such a `D`
(`modelledDatatypes`). -/
def literalIllFormed (D : List WfIri) (l : Literal) : Bool :=
  D.contains l.datatype &&
  (if isNumericDatatype l.datatype then (numericValue? l).isNone
   else if l.datatype == rdfXMLLiteral then !xmlLiteralWellFormed l.lexicalForm
   else if l.datatype == xsdBoolean then
     !(l.lexicalForm == "true" || l.lexicalForm == "false" ||
       l.lexicalForm == "1" || l.lexicalForm == "0")
   else false)

/-! ## Value equality and value-space membership -/

/-- D-value equality (§7): the engine literal equality (`Literal.eqb`:
exact datatype, lexical forms exact except XMLLiteral canonical form,
language tags case-insensitive) OR — when BOTH datatypes are
recognised numeric datatypes — equal numeric values. -/
def literalValueEq (D : List WfIri) (l1 l2 : Literal) : Bool :=
  l1.eqb l2 ||
  (isNumericDatatype l1.datatype && isNumericDatatype l2.datatype &&
   D.contains l1.datatype && D.contains l2.datatype &&
   (match numericValue? l1, numericValue? l2 with
    | some a, some b => a == b
    | _, _ => false))

/-- Membership for the modelled datatype map. Numeric values use the shared
XSD service, including decimal values that are integral and fit `int`.
Recognition by the caller's datatype map remains the caller's responsibility. -/
def valueInSpace (l : Literal) (c : WfIri) : Bool :=
  if isNumericDatatype l.datatype && isNumericDatatype c then
    let source := if l.datatype == xsdInt then XSD.Builtin.int
      else if l.datatype == xsdInteger then .integer else .decimal
    let target := if c == xsdInt then XSD.Builtin.int
      else if c == xsdInteger then .integer else .decimal
    (XSD.lexicalValueInBuiltin .xsd11 source l.lexicalForm target).getD false
  else l.datatype == c

end L4Factoidal.RDF
