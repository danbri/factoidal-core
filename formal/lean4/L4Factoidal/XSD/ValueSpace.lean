/- Shared membership in built-in XSD value spaces (XSD 1.1 Part 2 §§3–4).
   Membership is not a cast or a test of the target's lexical grammar.
   Inputs to `valueInBuiltin` must be well-formed parsed values; the checked
   lexical adapter below validates the source as well as the target.
   QName/NOTATION need namespace context; list/universal types and the
   provisional precisionDecimal representation are deliberately undecided. -/
import L4Factoidal.XSD.Lexical

namespace L4Factoidal.XSD

def valueMembershipSupported (b : Builtin) : Bool :=
  match b.primitive with
  | none => false
  | some p => p != .qname && p != .notation && p != .precisionDecimal

/-- `none` means this value-space decision is not implemented. Primitive
    tags remain distinct, including float/double and hex/base64Binary. -/
def valueInBuiltin (b : Builtin) (v : Val) : Option Bool :=
  if !valueMembershipSupported b then none
  else match v with
  | .str p s =>
      some (b.primitive == some p && applyWhiteSpace b.whiteSpace s == s &&
        (lexicalMap b s).isSome)
  | .dec d =>
      some (b.primitive == some .decimal &&
        (b == .decimal || (d.toInt?).any (inIntBounds b)))
  | .dur d =>
      some (b == .duration ||
        (b == .dayTimeDuration && d.months == 0) ||
        (b == .yearMonthDuration && Dec.cmp d.seconds Dec.zero == .eq))
  | .dt k d =>
      some (dtKindOf? b == some k && (b != .dateTimeStamp || d.tz.isSome))
  | .bool _ => some (b == .boolean)
  | .flt _ => some (b == .float)
  | .dbl _ => some (b == .double)
  | .bin h _ => some (b == if h then .hexBinary else .base64Binary)
  | .qname .. | .seq _ => none

/-- Validate the source datatype before asking about the value's membership
    in the target. No whitespace preprocessing: source string restrictions
    must already hold, as for RDF/RIF lexical forms. Invalid or unsupported
    sources return `none`, never a successful negative membership verdict. -/
def checkedLexicalValue (edition : Edition) (source : Builtin)
    (lexical : String) : Option Val := do
  let v ← lexicalFor edition source lexical
  let sourceValid ← valueInBuiltin source v
  if sourceValid then some v else none

def lexicalValueInBuiltin (edition : Edition) (source : Builtin)
    (lexical : String) (target : Builtin) : Option Bool :=
  (checkedLexicalValue edition source lexical).bind (valueInBuiltin target)

end L4Factoidal.XSD
