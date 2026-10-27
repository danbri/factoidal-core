/-
L4Factoidal.SPARQL.SameValue — value equality of two RDF terms, and the keys of
a value index of literals.

https://github.com/danbri/factoidal/issues/1052 (value-based matching).

## The relation

`sameValue a b` is the SPARQL 1.1 `=` operator on two RDF terms (section 17.3,
the operator table, and section 17.4.1.7 `RDFterm-equal`), as
`valueCompare (.term a) (.term b) .eq` decides it (`SPARQL/Expr.lean`). It is
three-valued:

  * `some true`: the terms have the same value (two numeric literals with equal
    values after F&O numeric promotion, XPath 3.1 section B.1, so
    `"01"^^xsd:integer`, `"1"^^xsd:int`, `"1.0"^^xsd:decimal` and
    `"1e0"^^xsd:double` are one value; two `xsd:boolean`, `xsd:dateTime` or
    `xsd:date` literals with equal values; the same RDF term);
  * `some false`: the terms have different values (different IRIs, different
    blank nodes, terms of different kinds, two literals of one comparable
    datatype with different values, the disjoint value spaces of
    `mf:KnownTypesDefault2Neq`);
  * `none`: incomparable. `RDFterm-equal` "produces a type error if the
    arguments are both literal but are not the same RDF term" when no value
    comparison applies: an unknown datatype, `rdf:XMLLiteral`, a lexical form
    outside the lexical space, and pairs of datatypes the operator table does
    not relate (`xsd:integer` and `xsd:boolean`).

The decision is the query engine's: a FILTER `(?a = ?b)` and `sameValue` give
the same answer by definition (`sameValue_eq_valueCompare`). Two consequences
a host must know: `"NaN"^^xsd:double` is not the same value as itself
(F&O `op:numeric-equal`), and the relation is not transitive across `xsd:float`
and `xsd:decimal` (a decimal is rounded to the float type before the
comparison, F&O section 4.2).

## The value index

A dataset matched by value (`Wasm/Ops/Handles.lean`, `valueMatchDataset`) files
each distinct object literal under the keys `storeKeys` gives it, and looks up
a pattern literal under the keys `probeKeys` gives it; a candidate is kept when
it is the same term as the pattern literal or `sameValue` is `some true`. The
keys only have to be complete: a pair with `sameValue = some true` shares a
key. They are exact (one key per value) where the comparison is exact:

  * an integer or decimal value (`xsd:integer`, `xsd:decimal` and the types
    derived from them) is filed under `nx:` and its canonical decimal form
    (`Dec.canonical`, XSD 1.1 Part 2 section 3.3.3.2), and under `nx`;
  * a `xsd:float` or `xsd:double` value is filed under `nf`. A float or double
    is compared after rounding to a common type, so an exact key is not sound:
    a float pattern looks up `nx` and `nf`, an exact one `nx:<canonical>` and
    `nf`;
  * a valid `xsd:boolean` under `b:true` or `b:false`;
  * every `xsd:dateTime` under `dt`, every `xsd:date` under `date` (the order
    with a timezone window, `Fn.Comparison.calendarOrder`, is not a key);
  * any other literal under `t:` and its lexical form, datatype, lower-case
    language tag and direction: such a literal is the same value only as the
    same term (or as a literal of `lexicalValueDatatype` with the same lexical
    form, which is the same term).

The completeness of the keys over a matrix of literals is a `#guard` below
(`keysComplete`).
-/
import L4Factoidal.SPARQL.Expr
import L4Factoidal.RDF.TermIdentity
import L4Factoidal.RDF.TermJson

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- SPARQL 1.1 `=` on two RDF terms (sections 17.3 and 17.4.1.7): `some true`
the same value, `some false` different values, `none` incomparable (the
operator's type error). -/
def sameValue (a b : Term) : Option Bool :=
  valueCompare (.term a) (.term b) .eq

/-- `sameValue` is the `=` of a SPARQL FILTER, by definition. -/
theorem sameValue_eq_valueCompare (a b : Term) :
    sameValue a b = valueCompare (.term a) (.term b) .eq := rfl

/-- The answer as the JSON string of the op `sameValue`. -/
def sameValueWord : Option Bool → String
  | some true => "true"
  | some false => "false"
  | none => "incomparable"

/-! ### Terms that are not literals

On IRIs and blank nodes the relation is term identity; two terms of different
kinds are different values. -/

theorem sameValue_iri (a b : WfIri) :
    sameValue (.iri a) (.iri b) = some (a.val == b.val) := by
  have h0 : sameValue (.iri a) (.iri b) = some (applyCompOp (strCompare a.val b.val) .eq) := rfl
  rw [h0, strCompare_eq_fast]
  simp only [strCompareFast, applyCompOp]
  by_cases h : a.val = b.val
  · simp [h]
  · have hb : (a.val == b.val) = false := by simpa using h
    rw [hb]; split <;> decide

theorem sameValue_bnode (a b : BNodeId) : sameValue (.bnode a) (.bnode b) = some (a == b) := rfl

theorem sameValue_iri_symm (a b : WfIri) :
    sameValue (.iri a) (.iri b) = sameValue (.iri b) (.iri a) := by
  rw [sameValue_iri, sameValue_iri]
  exact congrArg some (Bool.eq_iff_iff.mpr
    ⟨fun h => by simp_all [beq_iff_eq], fun h => by simp_all [beq_iff_eq]⟩)

theorem sameValue_bnode_symm (a b : BNodeId) :
    sameValue (.bnode a) (.bnode b) = sameValue (.bnode b) (.bnode a) := by
  rw [sameValue_bnode, sameValue_bnode]
  exact congrArg some (Bool.eq_iff_iff.mpr
    ⟨fun h => by simp_all [beq_iff_eq], fun h => by simp_all [beq_iff_eq]⟩)

/-! ### Index keys -/

/-- The key of a literal as a term: lexical form, datatype, lower-case language
tag and direction, separated by U+0000 (a character no IRI and no language tag
holds). -/
def termKey (l : Literal) : String :=
  "t:" ++ l.lexicalForm ++ "\u0000" ++ l.datatype.val ++ "\u0000" ++
    (l.langTag.map String.toLower).getD "" ++ "\u0000" ++
    (match l.direction with | some .ltr => "ltr" | some .rtl => "rtl" | none => "")

/-- The datatype family of a literal for the value index. -/
inductive ValueFamily where
  /-- An integer or decimal value, with its canonical decimal form. -/
  | exact (canonical : String)
  /-- A `xsd:float` or `xsd:double` value. -/
  | floating
  | boolean (b : Bool)
  | dateTime
  | date
  /-- No value comparison: the literal is the same value only as the same term. -/
  | term
  deriving DecidableEq, Repr

/-- The family of a literal (see the module header). -/
def valueFamily (l : Literal) : ValueFamily :=
  if Fn.Comparison.numericDatatype l.datatype then
    match Fn.Numeric.literalValue? l with
    | some (.dec d) => .exact d.canonical
    | some (.flt _) | some (.dbl _) => .floating
    | _ => .term
  else if l.datatype == xsdBoolean then
    match l.lexicalForm with
    | "true" | "1" => .boolean true
    | "false" | "0" => .boolean false
    | _ => .term
  else if l.datatype == xsdDateTime then .dateTime
  else if l.datatype == xsdDate then .date
  else .term

/-- The keys a stored object literal is filed under. -/
def storeKeys (l : Literal) : List String :=
  match valueFamily l with
  | .exact c => ["nx:" ++ c, "nx"]
  | .floating => ["nf"]
  | .boolean b => [if b then "b:true" else "b:false"]
  | .dateTime => ["dt"]
  | .date => ["date"]
  | .term => [termKey l]

/-- The keys a pattern literal looks up. -/
def probeKeys (l : Literal) : List String :=
  match valueFamily l with
  | .exact c => ["nx:" ++ c, "nf"]
  | .floating => ["nx", "nf"]
  | .boolean b => [if b then "b:true" else "b:false"]
  | .dateTime => ["dt"]
  | .date => ["date"]
  | .term => [termKey l]

/-- A stored literal `c` matches a pattern literal `q` by value: the same term,
or the same value. -/
def valueMatches (c q : WfLiteral) : Bool :=
  c.val.sameTerm q.val || sameValue (.literal c) (.literal q) == some true

/-! ### Build-time checks -/

private def xsd (local' : String) : WfIri :=
  match TermJson.iriOf? ("http://www.w3.org/2001/XMLSchema#" ++ local') with
  | some i => i
  | none => xsdString

private def lit (lex : String) (dt : String) : Term := .literal (mkTypedLiteral lex (xsd dt))

private def otherDt : WfIri :=
  match TermJson.iriOf? "http://example.org/dt" with | some i => i | none => xsdString

private def matrix : List Term :=
  [ lit "1" "integer", lit "01" "integer", lit "+1" "integer", lit "1" "int", lit "1" "long"
  , lit "1.0" "decimal", lit "1.00" "decimal", lit "1e0" "double", lit "1.0E0" "double"
  , lit "1" "float", lit "2" "integer", lit "0.1" "decimal", lit "0.1" "double", lit "0.1" "float"
  , lit "0" "integer", lit "-0" "decimal", lit "0.0e0" "double", lit "-0.0e0" "double"
  , lit "NaN" "double", lit "NaN" "float", lit "INF" "double", lit "INF" "float"
  , lit "abc" "integer", lit "1x" "decimal"
  , lit "true" "boolean", lit "1" "boolean", lit "false" "boolean", lit "0" "boolean"
  , lit "yes" "boolean"
  , lit "2000-01-01T00:00:00Z" "dateTime", lit "2000-01-01T01:00:00+01:00" "dateTime"
  , lit "2000-01-01T00:00:00" "dateTime", lit "2000-01-01" "date", lit "2000-01-01Z" "date"
  , .literal (Literal.string "1"), .literal (Literal.string "a"), .literal (Literal.string "A")
  , .literal (Literal.langString "a" "en"), .literal (Literal.langString "a" "EN-gb")
  , .literal (Literal.langString "a" "en-GB"), .literal (Literal.langString "b" "en")
  , .literal (mkTypedLiteral "a" otherDt), .literal (mkTypedLiteral "b" otherDt)
  , lit "a" "normalizedString", lit "x" "anyURI"
  , .iri xsdString, .iri xsdInteger, .bnode "b1", .bnode "b2" ]

private def lits : List WfLiteral :=
  matrix.filterMap fun t => match t with | .literal l => some l | _ => none

-- One value, five spellings and four datatypes.
#guard sameValue (lit "01" "integer") (lit "1" "integer") == some true
#guard sameValue (lit "1" "int") (lit "1" "integer") == some true
#guard sameValue (lit "1.0" "decimal") (lit "1" "integer") == some true
#guard sameValue (lit "1e0" "double") (lit "1" "integer") == some true
#guard sameValue (lit "1" "float") (lit "1.00" "decimal") == some true
#guard sameValue (lit "2" "integer") (lit "1" "integer") == some false
#guard sameValue (lit "-0" "decimal") (lit "0" "integer") == some true
#guard sameValue (lit "-0.0e0" "double") (lit "0.0e0" "double") == some true
-- F&O op:numeric-equal: NaN is not equal to NaN.
#guard sameValue (lit "NaN" "double") (lit "NaN" "double") == some false
-- An ill-typed literal is the same value as itself, incomparable with another.
#guard sameValue (lit "abc" "integer") (lit "abc" "integer") == some true
#guard sameValue (lit "abc" "integer") (lit "1" "integer") == none
#guard sameValue (lit "true" "boolean") (lit "1" "boolean") == some true
#guard sameValue (lit "true" "boolean") (lit "false" "boolean") == some false
#guard sameValue (lit "2000-01-01T00:00:00Z" "dateTime") (lit "2000-01-01T01:00:00+01:00" "dateTime") == some true
#guard sameValue (lit "2000-01-01T00:00:00" "dateTime") (lit "2000-01-01T00:00:00Z" "dateTime") == none
#guard sameValue (.literal (Literal.string "a")) (.literal (Literal.string "a")) == some true
#guard sameValue (.literal (Literal.string "a")) (.literal (Literal.string "A")) == some false
#guard sameValue (.literal (Literal.langString "a" "en-GB")) (.literal (Literal.langString "a" "EN-gb")) == some true
#guard sameValue (.literal (Literal.langString "a" "en")) (.literal (Literal.string "a")) == some false
-- Unknown datatype: the same term, or incomparable.
#guard sameValue (.literal (mkTypedLiteral "a" otherDt)) (.literal (mkTypedLiteral "a" otherDt)) == some true
#guard sameValue (.literal (mkTypedLiteral "a" otherDt)) (.literal (mkTypedLiteral "b" otherDt)) == none
#guard sameValue (lit "1" "integer") (lit "true" "boolean") == none
#guard sameValue (lit "1" "integer") (.literal (Literal.string "1")) == none
#guard sameValue (.iri xsdString) (.literal (Literal.string "a")) == some false
#guard sameValue (.bnode "b1") (.bnode "b1") == some true
#guard sameValue (.bnode "b1") (.iri xsdString) == some false
#guard sameValueWord (sameValue (lit "abc" "integer") (lit "1" "integer")) == "incomparable"

-- Symmetric on every pair of the matrix (the theorems above cover IRIs and
-- blank nodes for all terms).
#guard matrix.all fun a => matrix.all fun b => sameValue a b == sameValue b a

-- The keys are complete: a pair of the same value, or of the same term, shares
-- a key (a stored key of one is a probe key of the other).
private def keysComplete (c q : WfLiteral) : Bool :=
  !valueMatches c q || (storeKeys c.val).any (probeKeys q.val).contains

#guard lits.all fun c => lits.all fun q => keysComplete c q
#guard storeKeys (mkTypedLiteral "01" xsdInteger).val == ["nx:1", "nx"]
#guard probeKeys (mkTypedLiteral "1.0" xsdDecimal).val == ["nx:1", "nf"]
#guard valueMatches (mkTypedLiteral "NaN" xsdDouble) (mkTypedLiteral "NaN" xsdDouble)

end L4Factoidal.SPARQL
