/-
L4Factoidal.XSD11.ShaclBridge — one definition of a built-in datatype for
XML Schema validation and for SHACL `sh:datatype`.

XSD 1.1 validation (`XSD11.Validate`, through `XSD.valueOf`) and the
SHACL ill-formed-literal test (`SHACL.literalIllFormed`, SHACL §4.1.2)
both reduce to the lexical mapping of `L4Factoidal.XSD.Datatypes`
(`XSD.lexicalMap`). The theorems here state that reduction, so a change
to a built-in's lexical space changes both validators together.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Theorems
import L4Factoidal.SHACL.Validation

namespace L4Factoidal.XSD11

open L4Factoidal.XSD

/-- A built-in type with no facets: its values are exactly the lexical
mapping of `XSD.Datatypes` on the whitespace-normalized literal. -/
theorem valueOf_builtin (b : Builtin) (lit : String) :
    valueOf (.atomic b {}) lit = lexicalMap b (applyWhiteSpace b.whiteSpace lit) := by
  cases h : lexicalMap b (applyWhiteSpace b.whiteSpace lit) with
  | none =>
    simp [valueOf, valueOfFuel, SimpleType.whiteSpaceOf, SimpleType.facets, patternMatches, h]
  | some v =>
    simp [valueOf, valueOfFuel, SimpleType.whiteSpaceOf, SimpleType.facets, patternMatches, h,
      valueFacetsOk, boundOk, explicitTimezoneOk]
    split <;> rfl

/-- For a built-in that is not a date/time type, SHACL's ill-formed test
and XML Schema validation agree on a literal already in whitespace-
normalized form: the literal is ill-formed for SHACL exactly when the
facet-free type of that built-in rejects it. (The date/time types use
the edition-aware parser of `XSD.Lexical`; `float` and `double` differ
on `+INF` between XSD 1.0, which SHACL uses, and XSD 1.1.) -/
theorem shacl_datatype_is_xsd (dt : L4Factoidal.RDF.WfIri) (b : Builtin) (lex : String)
    (hb : builtinOfIri? dt.val = some b) (hk : dtKindOf? b = none)
    (hf : b ≠ .float ∧ b ≠ .double) (hn : applyWhiteSpace b.whiteSpace lex = lex) :
    SHACL.literalIllFormed dt lex = (valueOf (.atomic b {}) lex).isNone := by
  rw [valueOf_builtin, hn]
  simp only [SHACL.literalIllFormed, hb, lexicalFor, hk]
  have : ¬ (b == .float || b == .double) = true := by
    cases b <;> simp_all
  simp [this]

end L4Factoidal.XSD11
