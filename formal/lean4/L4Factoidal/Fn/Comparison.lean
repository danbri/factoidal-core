/- SPARQL 1.1 §17.3 comparisons, using XSD/F&O value spaces.
   Shared by SPARQL expressions and SHACL §§4.3/4.5. This is not ORDER BY
   (which orders additional RDF term categories), nor RDF term identity.
   No implicit timezone is supplied: uncertain timezone order is refused.
   IEEE conversion inherits XSD.IEEE754's documented rounding profile. -/
import L4Factoidal.Fn.Numeric

namespace L4Factoidal.Fn.Comparison
open RDF XSD

inductive Op where
  | lt | le | gt | ge | eq | ne
  deriving DecidableEq, Repr

def Op.apply (op : Op) (order : Ordering) : Bool :=
  match op with
  | .lt => order == .lt
  | .le => order != .gt
  | .gt => order == .gt
  | .ge => order != .lt
  | .eq => order == .eq
  | .ne => order != .eq

/-- Compatibility views of the shared numeric input layer. -/
abbrev numericType := Numeric.isType

/-- Classification is separate from parsing. Callers can distinguish an
    invalid numeric lexical form from an unrelated datatype. SPARQL §17.3. -/
abbrev numericDatatype := Numeric.isDatatype

abbrev numericLiteralValue? := Numeric.literalValue?

/-- Exact decimal -> IEEE lexical-value input; conversion happens once at
    the promoted type, using the existing XSD rounding implementation. -/
abbrev decimalParsed := Numeric.decimalParsed

/-- Float values widen exactly to double; decimal/integer values round at
    the common operand type. Values outside numeric spaces are rejected. -/
abbrev floatingValue := Numeric.floatingValue

/-- F&O numeric comparisons: NaN yields true only for `ne`, unlike invalid
    lexical forms or unsupported operands, which yield an error (`none`). -/
def numericCompare (a b : Val) (op : Op) : Option Bool := do
  match a, b with
  | .dec x, .dec y => some (op.apply (Dec.cmp x y))
  | _, _ =>
      let double := match a, b with | .dbl _, _ | _, .dbl _ => true | _, _ => false
      let x ← floatingValue double a
      let y ← floatingValue double b
      some ((fvalCmp x y).map op.apply |>.getD (op == .ne))

/-- XSD 1.0 calendar values, exact fractions and timezone offsets. Without
    an implicit timezone, use XSD's ±14-hour window: some mixed pairs have
    an unambiguous order, while overlapping windows remain incomparable. -/
def calendarOrder (kind : DTKind) (a b : String) : Option Ordering := do
  let x ← parseDateTimeFor .xsd10 kind a
  let y ← parseDateTimeFor .xsd10 kind b
  dtCompare x y

def dateTimeOrder (a b : String) : Option Ordering := calendarOrder .dateTime a b

/-- The supported SPARQL relational operand table. Unknown datatypes, IRIs,
    language-tagged strings and XML literals have no relational mapping.
    The existing xsd:date extension is retained with XSD value comparison.
    Equality and ordering of result sequences are separate contracts. -/
def literalCompare (a b : Literal) (op : Op) : Option Bool := do
  let ta ← builtinOfIri? a.datatype.val
  let tb ← builtinOfIri? b.datatype.val
  if numericType ta && numericType tb then
    let x ← lexicalFor .xsd10 ta a.lexicalForm
    let y ← lexicalFor .xsd10 tb b.lexicalForm
    numericCompare x y op
  else match ta, tb with
  | .string, .string => some (op.apply (compare a.lexicalForm b.lexicalForm))
  | .boolean, .boolean => do
      let x ← parseBooleanLex a.lexicalForm
      let y ← parseBooleanLex b.lexicalForm
      some (op.apply (compare x y))
  | .dateTime, .dateTime => (dateTimeOrder a.lexicalForm b.lexicalForm).map op.apply
  | .date, .date => (calendarOrder .date a.lexicalForm b.lexicalForm).map op.apply
  | _, _ => none

def termCompare (a b : Term) (op : Op) : Option Bool :=
  match a, b with
  | .literal x, .literal y => literalCompare x.val y.val op
  | _, _ => none

end L4Factoidal.Fn.Comparison
