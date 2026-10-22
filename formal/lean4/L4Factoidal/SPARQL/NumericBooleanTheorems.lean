/- SPARQL numeric EBV and F&O Boolean casts share the same parsed values.
   These prove integration agreement, not independent XSD parser correctness. -/
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.SPARQL
open RDF

theorem castBoolean_double_agrees_ebv (s : String) :
    castBoolean (.dbl s) = ((ebv (.dbl s)).map EvalResult.bool).getD .error := by
  have hd : XSD.builtinOfIri? xsdDouble.val = some .double := by decide +kernel
  simp [castBoolean, EvalResult.numericValue?, ebv, numericLexicalEbv,
    Fn.Numeric.lexicalValue?, hd, Fn.Numeric.isType, XSD.intBounds]

theorem castBoolean_decimal_agrees_ebv (s : String) :
    castBoolean (.dec s) = ((ebv (.dec s)).map EvalResult.bool).getD .error := by
  have hd : XSD.builtinOfIri? xsdDecimal.val = some .decimal := by decide +kernel
  simp [castBoolean, EvalResult.numericValue?, ebv, numericLexicalEbv,
    Fn.Numeric.lexicalValue?, hd, Fn.Numeric.isType, XSD.intBounds,
    XSD.lexicalFor, XSD.dtKindOf?, XSD.lexicalMap, XSD.lexicalMapFuel]

/-- Numeric RDF literals keep their original type through both consumers.
    No lexical-validity premise is needed: failure agrees too. -/
theorem castBoolean_numeric_literal_agrees_ebv (l : WfLiteral)
    (hn : isNumericDatatype l.val.datatype = true)
    (hb : l.val.datatype ≠ xsdBoolean) (hs : l.val.datatype ≠ xsdString) :
    castBoolean (.term (.literal l)) =
      ((ebv (.term (.literal l))).map EvalResult.bool).getD .error := by
  have hb' : l.val.datatype.val ≠ xsdBoolean.val := fun h => hb (Subtype.ext h)
  have hs' : l.val.datatype.val ≠ xsdString.val := fun h => hs (Subtype.ext h)
  simp [castBoolean, EvalResult.numericValue?, ebv, numericLexicalEbv,
    Fn.Numeric.literalValue?, hn, hb', hs']

theorem isNumeric_literal_uses_shared_value (l : WfLiteral) :
    fnIsNumeric (.term (.literal l)) = .bool (Fn.Numeric.literalValue? l.val).isSome := rfl

#print axioms castBoolean_double_agrees_ebv
#print axioms castBoolean_decimal_agrees_ebv
#print axioms castBoolean_numeric_literal_agrees_ebv
#print axioms isNumeric_literal_uses_shared_value

end L4Factoidal.SPARQL
