/- Shared numeric inputs for F&O comparisons and Boolean conversion.
   SPARQL §§17.1–17.3 and §17.4.2.4; F&O 2007 §17.1.6.
   Lexical parsing uses XSD 1.0, including integer-derived bounds and the
   existing IEEE conversion profile. This module does not implement arithmetic. -/
import L4Factoidal.RDF.Core
import L4Factoidal.XSD.Lexical

namespace L4Factoidal.Fn.Numeric
open RDF XSD

def isType (b : Builtin) : Bool :=
  (intBounds b).isSome || b == .decimal || b == .float || b == .double

/-- Datatype classification alone does not establish lexical validity. -/
def isDatatype (dt : WfIri) : Bool := (builtinOfIri? dt.val).any isType

def lexicalValue? (dt : WfIri) (s : String) : Option Val := do
  let b ← builtinOfIri? dt.val
  if isType b then lexicalFor .xsd10 b s else none

def literalValue? (l : Literal) : Option Val := lexicalValue? l.datatype l.lexicalForm

/-- Exact decimal input to the shared IEEE conversion profile. -/
def decimalParsed (d : Dec) : Parsed :=
  .num (d.mantissa < 0) d.mantissa.natAbs (-(d.scale : Int))

/-- F&O numeric promotion, shared by comparison and arithmetic. -/
def floatingValue (double : Bool) : Val → Option Fval
  | .dec d => some (if double then canonDouble (decimalParsed d) else canonFloat (decimalParsed d))
  | .flt f => some f
  | .dbl f => if double then some f else none
  | _ => none

/-- F&O numeric-to-Boolean conversion: zero and NaN are false. Parsing
    must happen first so underflow and derived-type bounds have taken effect.
    Nonnumeric values remain errors; string conversion is a caller policy. -/
def booleanValue? : Val → Option Bool
  | .dec d => some (d.mantissa != 0)
  | .flt f | .dbl f => some (match f.cls with
      | .zero | .nan => false
      | .inf => true
      | .finite m _ => m != 0)
  | _ => none

end L4Factoidal.Fn.Numeric
