/-
L4Factoidal.Storage.Sbm11.TypedCmp — a FILTER comparison of a typed literal
with a constant, decided on the dictionary key bytes
(https://github.com/danbri/factoidal/issues/930; benchmark record
docs/designissues/2026-10-12-three-engine-benchmark.md section 11.15).

DBpedia d14 is `FILTER(?d < "1800-01-01"^^xsd:date)` on 953 joined rows. The
reference evaluator decodes the dictionary key of each date to a `Term`
(list-based `decodeKey?`, about 2 microseconds per row) and evaluates the
comparison on it. For a constant of a datatype that has no value for the
operators (not numeric, not derived from `xsd:integer`, not `xsd:boolean`,
not `xsd:string`, no language tag), `valueCompare` compares two literals of
that datatype by the code point order of their lexical forms (SPARQL 1.1
section 17.3 as `Expr.valueCompare` implements it). `typedCmpKey?` reads that
order off the key of a class 5 dictionary literal (`[5] ++ datatype ++ [0] ++
lexical form`) without building a `Term`: it checks the key prefix, decodes
the lexical form and applies the operator.

`TypedCmpTheorems.typedCmpKey_sound`: when `typedCmpKey?` answers, the answer
is the reference FILTER value on the term that `decodeKey?` gives for the
key. A key it does not decide (another class, another datatype, a lexical
form that is not UTF-8) gives `none` and goes to the reference evaluator.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKeyFast
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.Storage.Sbm11.TypedCmp

open L4Factoidal.RDF
open L4Factoidal.SPARQL (CompOp applyCompOp strCompare integerDerivedBuiltinOfIri?)
open L4Factoidal.Storage (bytesOfString)

/-- A typed literal constant that `typedCmpKey?` may compare against: no
    language tag or direction; a datatype that is not `xsd:string`, has no
    `0x00` byte, and has no value for the relational operators (not
    `xsd:integer`, `xsd:decimal`, `xsd:double`, `xsd:float`, `xsd:boolean`
    and not derived from `xsd:integer`). -/
def typedConstOk (c : WfLiteral) : Bool :=
  c.val.langTag.isNone && c.val.direction.isNone && c.val.datatype != xsdString &&
  noZero (bytesOfString c.val.datatype.val) &&
  (integerDerivedBuiltinOfIri? c.val.datatype.val).isNone &&
  !(c.val.datatype == xsdInteger) && !(c.val.datatype == xsdDecimal) &&
  !(c.val.datatype == xsdDouble) && !(c.val.datatype == L4Factoidal.SPARQL.xsdFloat) &&
  !(c.val.datatype == xsdBoolean)

/-- The key bytes before the lexical form of a literal of the constant's
    datatype: the class byte, the datatype's UTF-8 bytes, `0x00`. -/
def typedPre (c : WfLiteral) : ByteArray :=
  ⟨(classTyped :: (bytesOfString c.val.datatype.val ++ [0])).toArray⟩

/-- The comparison `lexical form OP constant` (`swap`: `constant OP lexical
    form`) of the dictionary key `buf[a, e)` with the constant's lexical
    form `cLex`, when the key is `pre ++ lexical form` with a lexical form
    that is UTF-8; `none` otherwise. -/
def typedCmpKey? (op : CompOp) (swap : Bool) (pre : ByteArray) (cLex : String)
    (buf : ByteArray) (a e : Nat) : Option Bool :=
  if sliceOk buf a e && decide (a + pre.size ≤ e) && buf.extract a (a + pre.size) == pre then
    match String.fromUTF8? (buf.extract (a + pre.size) e) with
    | some lex => some (applyCompOp (if swap then strCompare cLex lex else strCompare lex cLex) op)
    | none => none
  else none

end L4Factoidal.Storage.Sbm11.TypedCmp
