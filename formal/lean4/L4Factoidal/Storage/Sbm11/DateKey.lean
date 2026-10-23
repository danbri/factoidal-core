/-
L4Factoidal.Storage.Sbm11.DateKey — a FILTER comparison of an `xsd:date`
literal with an `xsd:date` constant, decided on the dictionary key bytes
(https://github.com/danbri/factoidal/issues/948, the d14 target of
https://github.com/danbri/factoidal/issues/930; benchmark record
docs/designissues/2026-10-12-three-engine-benchmark.md section 11.19).

The operators `<`, `<=`, `>` and `>=` compare two `xsd:date` literals in the
XSD value space (SPARQL 1.1 section 17.3, `Fn.Comparison.termCompare`, which
parses each lexical form with `XSD.parseDateTimeFor .xsd10 .date` and orders
the values with `XSD.dtCompare`). The code point order of the lexical forms is
not that order in general: a timezone (`"2000-01-01+05:00"`), a negative year
or a year of five or more digits change it, and an invalid date
(`"2001-02-29"`) has no value.

The admitted set, `dateParts?`: a lexical form of exactly ten bytes
`YYYY-MM-DD`, all of `Y`, `M`, `D` ASCII digits, with year 0001 to 9999, month
1 to 12 and a day that exists in that month (`XSD.daysInMonth`), and no
timezone. For two such forms the XSD order is the order of the number
`year * 512 + month * 32 + day` (`DateKeyTheorems.calendarOrder_admitted`).
`dateCmpKey?` decides `?v OP c` (`swap`: `c OP ?v`) on the key of a class 5
dictionary literal (`[5] ++ xsd:date IRI ++ [0] ++ lexical form`) when the
lexical form is admitted, without building a `Term`; any other key gives
`none`, and `applyFilters` asks the reference evaluator for that row.
`dateConst?` admits the constant by the same rule; a constant outside the set
gives no `dateCmp` conjunct at all.

Theorems: `DateKeyTheorems.dateCmpKey_termCompare` (when `dateCmpKey?`
answers `r`, `Fn.Comparison.termCompare` of the decoded term and the constant
is `some r`) and `dateCmpKey_sound` (the answer is the reference FILTER value).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKeyFast
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.Storage.Sbm11.DateKey

open L4Factoidal.RDF
open L4Factoidal.SPARQL (CompOp)
open L4Factoidal.Storage (bytesOfString)

/-- An ASCII decimal digit. -/
@[inline] def isDB (b : UInt8) : Bool := 48 ≤ b.toNat && b.toNat ≤ 57

/-- The value of an ASCII decimal digit. -/
@[inline] def dv (b : UInt8) : Nat := b.toNat - 48

/-- The year, month and day of an admitted lexical form (see the module
    header): `YYYY-MM-DD`, ten ASCII bytes, year 1 to 9999, month 1 to 12, a
    day of that month. `none` for every other byte list. -/
def dateParts? : List UInt8 → Option (Nat × Nat × Nat)
  | [y1, y2, y3, y4, h1, m1, m2, h2, d1, d2] =>
    if isDB y1 && isDB y2 && isDB y3 && isDB y4 && h1 == 45 && isDB m1 && isDB m2 && h2 == 45 &&
        isDB d1 && isDB d2 then
      let y := ((dv y1 * 10 + dv y2) * 10 + dv y3) * 10 + dv y4
      let mo := dv m1 * 10 + dv m2
      let d := dv d1 * 10 + dv d2
      if 1 ≤ y && 1 ≤ mo && mo ≤ 12 && 1 ≤ d && d ≤ XSD.daysInMonth y mo then some (y, mo, d)
      else none
    else none
  | _ => none

/-- The order key of a date: `year * 512 + month * 32 + day`. -/
@[inline] def dateOrd (p : Nat × Nat × Nat) : Nat := p.1 * 512 + p.2.1 * 32 + p.2.2

/-- The relational operators, as the operators of `Fn.Comparison`; `=` and
    `!=` are not decided here (they compare `xsd:date` literals by lexical
    form, `Expr.valueCompare`). -/
def relOp? : CompOp → Option Fn.Comparison.Op
  | .lt => some .lt
  | .le => some .le
  | .gt => some .gt
  | .ge => some .ge
  | _ => none

/-- The key bytes before the lexical form of a literal of the constant's
    datatype: the class byte 5, the datatype IRI's UTF-8 bytes, `0x00`. -/
def datePre (c : WfLiteral) : ByteArray :=
  ⟨(classTyped :: (bytesOfString c.val.datatype.val ++ [0])).toArray⟩

/-- An admitted `xsd:date` constant: no language tag or direction, a datatype
    that `XSD.builtinOfIri?` reads as `date` (so not `xsd:string`) and whose
    IRI has no `0x00` byte, and a lexical form that `dateParts?` admits. The
    result is the key prefix of literals of that datatype and the order key
    of the constant. -/
def dateConst? (c : WfLiteral) : Option (ByteArray × Nat) :=
  if c.val.langTag.isNone && c.val.direction.isNone &&
      XSD.builtinOfIri? c.val.datatype.val == some .date && c.val.datatype != xsdString &&
      noZero (bytesOfString c.val.datatype.val) then
    (dateParts? (bytesOfString c.val.lexicalForm)).map fun p => (datePre c, dateOrd p)
  else none

/-- `?v OP c` (`swap`: `c OP ?v`) for the dictionary key `buf[a, e)`, with
    `pre` and `kc` from `dateConst? c`: decided when the key is `pre` and ten
    bytes that `dateParts?` admits; `none` otherwise. -/
def dateCmpKey? (op : Fn.Comparison.Op) (swap : Bool) (pre : ByteArray) (kc : Nat)
    (buf : ByteArray) (a e : Nat) : Option Bool :=
  if sliceOk buf a e && decide (a + pre.size + 10 = e) && buf.extract a (a + pre.size) == pre then
    match dateParts? (sliceList buf (a + pre.size) e) with
    | some p => some (op.apply (if swap then compare kc (dateOrd p) else compare (dateOrd p) kc))
    | none => none
  else none

end L4Factoidal.Storage.Sbm11.DateKey
