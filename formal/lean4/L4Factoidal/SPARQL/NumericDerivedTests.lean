/-
L4Factoidal.SPARQL.NumericDerivedTests — the types derived from
`xsd:integer` are numeric operand types.

SPARQL 1.1 Query §17.1 (Operand Data Types): "numeric denotes typed
literals with datatypes xsd:integer, xsd:decimal, xsd:float, and
xsd:double", and the operator mapping also accepts "types derived from
xsd:integer and xsd:decimal". XSD 1.1 Part 2 §3.4 has twelve built-in
types derived from `xsd:integer` and none derived from `xsd:decimal`
other than `xsd:integer` itself.

A literal of a derived type whose lexical form is not in the type's
lexical space, or whose value is outside the type's bounds, is
ill-typed: it has no value, so it is not numeric. A relational operator
or arithmetic on it is a type error, and FILTER drops the row.

Lexical forms are read without whitespace processing: RDF 1.1 Semantics
§7 maps a literal through "the lexical-to-value mapping" of its datatype
on the lexical form as written, so `" 72"^^xsd:int` is ill-typed. That
is the rule `RDF/Datatypes.lean` applies for D-entailment, and rdf-mt
`xmlsch-02-whitespace-facet-*` require it.

Regression for https://github.com/danbri/factoidal/issues/782. Every
`#guard` is evaluated by `lake build`, so a wrong answer fails the build.
-/
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.SPARQL.NumericDerivedTests

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ### The twelve types (XSD 1.1 Part 2 §3.4.14-§3.4.26) -/

private def tLong  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#long", rfl⟩
private def tInt   : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#int", rfl⟩
private def tShort : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#short", rfl⟩
private def tByte  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#byte", rfl⟩
private def tNonNeg : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩
private def tPos   : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#positiveInteger", rfl⟩
private def tNonPos : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonPositiveInteger", rfl⟩
private def tNeg   : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#negativeInteger", rfl⟩
private def tULong : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedLong", rfl⟩
private def tUInt  : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedInt", rfl⟩
private def tUShort : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedShort", rfl⟩
private def tUByte : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#unsignedByte", rfl⟩

/- The IRI table of `integerDerivedBuiltinOfIri?` names exactly the
built-ins that `XSD.derivedFrom` puts below `xsd:integer`, and each one
as itself. -/
#guard XSD.allBuiltins.all (fun b =>
  integerDerivedBuiltinOfIri? b.iri ==
    (if b != .integer && XSD.derivedFrom b .integer then some b else none))
#guard (XSD.allBuiltins.filter (fun b => b != .integer && XSD.derivedFrom b .integer)).length == 12

private def mu (lex : String) (dt : WfIri) : Binding := [("a", .literal (mkTypedLiteral lex dt))]

/-- The literal `lex^^dt` is numeric with value `v`: comparison, equality
and arithmetic all see `v`, `isNumeric` is true, and the sum is an
`xsd:integer` (XPath 3.1 §B.1 type promotion: a derived integer type
promotes to `xsd:integer`). -/
private def numericWith (lex : String) (dt : WfIri) (v : Int) : Bool :=
  let m := mu lex dt
  (Expr.compare .ge (.var "a") (.numericLit v)).eval m == .bool true &&
  (Expr.compare .eq (.var "a") (.numericLit v)).eval m == .bool true &&
  (Expr.compare .ne (.var "a") (.numericLit v)).eval m == .bool false &&
  (Expr.compare .lt (.var "a") (.numericLit (v + 1))).eval m == .bool true &&
  (Expr.compare .gt (.var "a") (.numericLit (v - 1))).eval m == .bool true &&
  (Expr.arith .add (.var "a") (.numericLit 1)).eval m == .num (v + 1) &&
  (Expr.arith .mul (.var "a") (.numericLit 2)).eval m == .num (2 * v) &&
  (Expr.isNumeric (.var "a")).eval m == .bool true

/-- The literal `lex^^dt` is ill-typed: every numeric operator is a type
error, and `isNumeric` is false (§17.4.2.4: `isNumeric("1200"^^xsd:byte)`
is false). -/
private def illTyped (lex : String) (dt : WfIri) : Bool :=
  let m := mu lex dt
  (Expr.compare .ge (.var "a") (.numericLit 0)).eval m == .error &&
  (Expr.compare .lt (.var "a") (.numericLit 0)).eval m == .error &&
  (Expr.compare .eq (.var "a") (.numericLit 0)).eval m == .error &&
  (Expr.arith .add (.var "a") (.numericLit 1)).eval m == .error &&
  (Expr.isNumeric (.var "a")).eval m == .bool false

/-! ### Each derived type is numeric -/

#guard numericWith "72" tLong 72
#guard numericWith "72" tInt 72
#guard numericWith "72" tShort 72
#guard numericWith "72" tByte 72
#guard numericWith "72" tNonNeg 72
#guard numericWith "72" tPos 72
#guard numericWith "-72" tNonPos (-72)
#guard numericWith "-72" tNeg (-72)
#guard numericWith "72" tULong 72
#guard numericWith "72" tUInt 72
#guard numericWith "72" tUShort 72
#guard numericWith "72" tUByte 72

/-! ### Bounds (XSD 1.1 Part 2 §3.4.16-§3.4.26) -/

#guard numericWith "9223372036854775807" tLong 9223372036854775807
#guard numericWith "-9223372036854775808" tLong (-9223372036854775808)
#guard illTyped "9223372036854775808" tLong
#guard numericWith "2147483647" tInt 2147483647
#guard numericWith "-2147483648" tInt (-2147483648)
#guard illTyped "2147483648" tInt
#guard illTyped "-2147483649" tInt
#guard numericWith "32767" tShort 32767
#guard illTyped "32768" tShort
#guard numericWith "127" tByte 127
#guard numericWith "-128" tByte (-128)
#guard illTyped "128" tByte
#guard illTyped "-129" tByte
#guard illTyped "1200" tByte
#guard numericWith "0" tNonNeg 0
#guard illTyped "-1" tNonNeg
#guard numericWith "1" tPos 1
#guard illTyped "0" tPos
#guard numericWith "0" tNonPos 0
#guard illTyped "1" tNonPos
#guard numericWith "-1" tNeg (-1)
#guard illTyped "0" tNeg
#guard numericWith "18446744073709551615" tULong 18446744073709551615
#guard illTyped "18446744073709551616" tULong
#guard illTyped "-1" tULong
#guard numericWith "4294967295" tUInt 4294967295
#guard illTyped "4294967296" tUInt
#guard numericWith "65535" tUShort 65535
#guard illTyped "65536" tUShort
#guard numericWith "255" tUByte 255
#guard illTyped "256" tUByte
#guard illTyped "-1" tUByte

/-! ### Lexical space (XSD 1.1 Part 2 §3.4.13: `[\-+]?[0-9]+`) -/

#guard numericWith "+72" tInt 72
#guard numericWith "0072" tInt 72
#guard numericWith "-0" tInt 0
#guard illTyped "+0" tPos
#guard illTyped " 72" tInt
#guard illTyped "72 " tInt
#guard illTyped "7 2" tInt
#guard illTyped "72.0" tInt
#guard illTyped "7.2E1" tInt
#guard illTyped "" tInt
#guard illTyped "+" tInt
#guard illTyped "-" tInt
#guard illTyped "abc" tInt
-- `xsd:integer` has the same lexical space, leading `+` included.
#guard numericWith "+72" RDF.xsdInteger 72

/-! ### Promotion across the numeric types (§17.1, XPath 3.1 §B.1) -/

private def mInt := mu "72" tInt
#guard (Expr.arith .add (.var "a") (.decimalLit "1.5")).eval mInt == .dec "73.5"
#guard (Expr.arith .add (.var "a") (.doubleLit "1.0E0")).eval mInt == .dbl "7.3E1"
#guard (Expr.arith .div (.var "a") (.numericLit 2)).eval mInt == .dec "36.0"
#guard (Expr.arith .sub (.var "a") (.var "a")).eval mInt == .num 0
#guard (Expr.compare .eq (.var "a") (.decimalLit "72.0")).eval mInt == .bool true
#guard (Expr.compare .eq (.var "a") (.doubleLit "7.2E1")).eval mInt == .bool true
#guard (Expr.compare .lt (.var "a") (.decimalLit "72.5")).eval mInt == .bool true
#guard (Expr.unaryMinus (.var "a")).eval mInt == .num (-72)
#guard (Expr.abs (.var "a")).eval (mu "-5" tByte) == .num 5
#guard (Expr.round (.var "a")).eval mInt == .num 72
-- Two derived types of different width compare by value.
#guard (Expr.compare .eq (.var "a") (.var "b")).eval
  [("a", .literal (mkTypedLiteral "72" tInt)), ("b", .literal (mkTypedLiteral "072" tUByte))]
  == .bool true
-- A literal written in the expression is numeric too.
#guard (Expr.compare .eq (.lit (mkTypedLiteral "72" tShort)) (.numericLit 72)).eval [] == .bool true

/-! ### §17.2.2 effective boolean value -/

#guard ebv ((Expr.var "a").eval (mu "0" tInt)) == some false
#guard ebv ((Expr.var "a").eval (mu "00" tInt)) == some false
#guard ebv ((Expr.var "a").eval (mu "5" tInt)) == some true
#guard ebv ((Expr.var "a").eval (mu "300" tByte)) == none

/-! ### The term is kept: only the operators see the value

DATATYPE, STR and an assignment return the literal as written, not a
rewritten `xsd:integer`. -/

#guard (Expr.datatype (.var "a")).eval (mu "0072" tInt) == .term (.iri tInt)
#guard (Expr.str (.var "a")).eval (mu "0072" tInt) ==
  .term (.literal (Literal.string "0072"))
#guard (Expr.sameTerm (.var "a") (.var "b")).eval
  [("a", .literal (mkTypedLiteral "72" tInt)), ("b", .literal (mkTypedLiteral "72" RDF.xsdInteger))]
  == .bool false

/-! ### `=` on two ill-typed literals is RDFterm-equal (§17.4.1.7) -/

#guard (Expr.compare .eq (.var "a") (.var "b")).eval
  [("a", .literal (mkTypedLiteral "300" tByte)), ("b", .literal (mkTypedLiteral "300" tByte))]
  == .bool true

/-! ### Whole queries, reference evaluator and indexed backend

The data and the first three queries of issue 782. -/

private def data : Graph :=
  (Syntax.parseTurtle ("@prefix xsd: <http://www.w3.org/2001/XMLSchema#> . " ++
    "<http://ex/a> <http://ex/age> \"72\"^^xsd:int . " ++
    "<http://ex/b> <http://ex/age> \"72\"^^xsd:integer . " ++
    "<http://ex/c> <http://ex/age> \"73\"^^xsd:int . " ++
    "<http://ex/d> <http://ex/age> \"100\"^^xsd:unsignedByte . " ++
    "<http://ex/e> <http://ex/age> \"300\"^^xsd:unsignedByte .")).toOption.getD []

#guard data.length == 5

private def ds : Dataset := { default := data, named := [] }

private def refRows (q : String) : Option SolutionSeq := do
  let query ← (parseSparql q).toOption
  return (evalSelect emptyEnv ds query).2

private def idxRows (q : String) : Option SolutionSeq := do
  let query ← (parseSparql q).toOption
  StoreDataset.runSelectQueryBackendDataset emptyEnv query (StoreDataset.indexedDatasetBackend ds)

/-- Column `v` of the rows from both paths, which must agree. -/
private def col (v : VarName) (q : String) : Option (List (Option Term)) :=
  let r := (refRows q).map (fun rows => rows.map (Binding.lookup v))
  let i := (idxRows q).map (fun rows => rows.map (Binding.lookup v))
  if r == i then r else none

private def ex (s : String) (h : isIri s := by rfl) : Option Term := some (.iri ⟨s, h⟩)
private def int (n : Int) : Option Term := some (.literal (mkTypedLiteral (toString n) RDF.xsdInteger))

#guard col "s" "SELECT ?s WHERE { ?s <http://ex/age> ?a FILTER(?a >= 72) } ORDER BY ?s" ==
  some [ex "http://ex/a", ex "http://ex/b", ex "http://ex/c", ex "http://ex/d"]
#guard col "s" "SELECT ?s WHERE { ?s <http://ex/age> ?a FILTER(?a = 72) } ORDER BY ?s" ==
  some [ex "http://ex/a", ex "http://ex/b"]
#guard col "b" "SELECT ?s ?b WHERE { ?s <http://ex/age> ?a BIND(?a + 1 AS ?b) } ORDER BY ?s" ==
  some [int 73, int 73, int 74, int 101, none]
-- ORDER BY sorts by value; the ill-typed literal sorts after the numerics.
#guard col "s" "SELECT ?s WHERE { ?s <http://ex/age> ?a } ORDER BY ?a ?s" ==
  some [ex "http://ex/a", ex "http://ex/b", ex "http://ex/c", ex "http://ex/d", ex "http://ex/e"]
#guard col "s" "SELECT ?s WHERE { ?s <http://ex/age> ?a } ORDER BY DESC(?a) ?s" ==
  some [ex "http://ex/e", ex "http://ex/d", ex "http://ex/c", ex "http://ex/a", ex "http://ex/b"]
-- Aggregates: SUM over valid values, MAX by value.
#guard col "t" ("SELECT (SUM(?a) AS ?t) WHERE { ?s <http://ex/age> ?a " ++
  "FILTER(?s != <http://ex/e>) }") == some [int 317]
#guard col "m" ("SELECT (MAX(?a) AS ?m) WHERE { ?s <http://ex/age> ?a " ++
  "FILTER(?s != <http://ex/e>) }") ==
  some [some (.literal (mkTypedLiteral "100" tUByte))]

/-! ### A typed numeric or boolean literal written in the query

SPARQL 1.1 §4.1.2: `72` is syntax for `"72"^^xsd:integer`; both denote
the same RDF term, so an operator sees the same value for both. The
literal stays a term (DATATYPE, STR and sameTerm see it as written);
only the operators read its value (§17.3 operator mapping, §17.1
promotion). An ill-typed literal written in the query has no value and
compares as a term (§17.4.1.7 RDFterm-equal).
https://github.com/danbri/factoidal/issues/784 -/

private def tDec : WfIri := RDF.xsdDecimal
private def tDbl : WfIri := RDF.xsdDouble
private def tBool : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#boolean", rfl⟩
private def litE (lex : String) (dt : WfIri) : Expr := .lit (mkTypedLiteral lex dt)

-- Equality and ordering against each primitive numeric type.
#guard (Expr.compare .eq (.var "a") (litE "72" RDF.xsdInteger)).eval mInt == .bool true
#guard (Expr.compare .eq (.var "a") (litE "072" RDF.xsdInteger)).eval mInt == .bool true
#guard (Expr.compare .ne (.var "a") (litE "72" RDF.xsdInteger)).eval mInt == .bool false
#guard (Expr.compare .lt (.var "a") (litE "73.0" tDec)).eval mInt == .bool true
#guard (Expr.compare .eq (.var "a") (litE "72.0" tDec)).eval mInt == .bool true
#guard (Expr.compare .eq (.var "a") (litE "7.2E1" tDbl)).eval mInt == .bool true
#guard (Expr.compare .gt (.var "a") (litE "7.1E1" tDbl)).eval mInt == .bool true
#guard (Expr.compare .eq (litE "72" tShort) (litE "72" RDF.xsdInteger)).eval [] == .bool true
#guard (Expr.compare .le (litE "72" RDF.xsdInteger) (litE "72.5" tDec)).eval [] == .bool true
#guard (Expr.compare .eq (litE "1" RDF.xsdInteger) (litE "1.0E0" tDbl)).eval [] == .bool true
-- Boolean literals are not numeric, but `=` compares their values.
#guard (Expr.compare .eq (litE "true" tBool) (.boolLit true)).eval [] == .bool true
#guard (Expr.compare .eq (litE "1" tBool) (.boolLit true)).eval [] == .bool true
#guard (Expr.compare .lt (litE "false" tBool) (litE "1" tBool)).eval [] == .bool true
#guard (Expr.compare .eq (.var "a") (.boolLit true)).eval (mu "1" tBool) == .bool true
#guard (Expr.isNumeric (litE "true" tBool)).eval [] == .bool false
-- Arithmetic, with promotion.
#guard (Expr.arith .add (.var "a") (litE "1" RDF.xsdInteger)).eval mInt == .num 73
#guard (Expr.arith .add (litE "1" RDF.xsdInteger) (litE "1.5" tDec)).eval [] == .dec "2.5"
#guard (Expr.arith .mul (litE "2" RDF.xsdInteger) (litE "1.5E0" tDbl)).eval [] == .dbl "3.0E0"
#guard (Expr.arith .sub (litE "5" tByte) (litE "2" RDF.xsdInteger)).eval [] == .num 3
#guard (Expr.unaryMinus (litE "72" RDF.xsdInteger)).eval [] == .num (-72)
#guard (Expr.abs (litE "-2.5" tDec)).eval [] == .dec "2.5"
-- The term itself is kept.
#guard (Expr.datatype (litE "072" RDF.xsdInteger)).eval [] == .term (.iri RDF.xsdInteger)
#guard (Expr.str (litE "072" RDF.xsdInteger)).eval [] ==
  .term (.literal (Literal.string "072"))
#guard (Expr.sameTerm (litE "072" RDF.xsdInteger) (litE "72" RDF.xsdInteger)).eval [] == .bool false
-- An ill-typed literal compares as a term: equal to itself, unordered.
#guard (Expr.compare .eq (litE "abc" RDF.xsdInteger) (litE "abc" RDF.xsdInteger)).eval [] == .bool true
#guard (Expr.compare .eq (litE "abc" tDec) (litE "abc" tDec)).eval [] == .bool true
#guard (Expr.compare .eq (litE "abc" tBool) (litE "abc" tBool)).eval [] == .bool true
#guard (Expr.compare .eq (.var "a") (litE "abc" RDF.xsdInteger)).eval mInt == .error
#guard (Expr.arith .add (litE "abc" RDF.xsdInteger) (.numericLit 1)).eval [] == .error

-- The queries of issue 784, reference evaluator and indexed backend.
#guard col "s" ("SELECT ?s WHERE { ?s <http://ex/age> ?a " ++
  "FILTER(?a = \"72\"^^<http://www.w3.org/2001/XMLSchema#integer>) } ORDER BY ?s") ==
  some [ex "http://ex/a", ex "http://ex/b"]
#guard col "s" ("SELECT ?s WHERE { ?s <http://ex/age> ?a " ++
  "FILTER(?a < \"73.0\"^^<http://www.w3.org/2001/XMLSchema#decimal>) } ORDER BY ?s") ==
  some [ex "http://ex/a", ex "http://ex/b"]
#guard col "s" ("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> SELECT ?s WHERE { " ++
  "?s <http://ex/age> ?a FILTER(?a = \"7.2E1\"^^xsd:double) } ORDER BY ?s") ==
  some [ex "http://ex/a", ex "http://ex/b"]
#guard col "s" ("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> SELECT ?s WHERE { " ++
  "?s <http://ex/age> ?a FILTER(?a = \"72\"^^xsd:short) } ORDER BY ?s") ==
  some [ex "http://ex/a", ex "http://ex/b"]
#guard col "s" ("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> SELECT ?s WHERE { " ++
  "?s <http://ex/age> ?a FILTER(?a >= \"73\"^^xsd:integer && \"true\"^^xsd:boolean) } ORDER BY ?s") ==
  some [ex "http://ex/c", ex "http://ex/d"]
#guard col "b" ("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> SELECT ?s ?b WHERE { " ++
  "?s <http://ex/age> ?a FILTER(?s != <http://ex/e>) BIND(?a + \"1\"^^xsd:integer AS ?b) } ORDER BY ?s") ==
  some [int 73, int 73, int 74, int 101]
-- BIND of the constant itself keeps the lexical form as written.
#guard col "b" ("PREFIX xsd: <http://www.w3.org/2001/XMLSchema#> SELECT ?b WHERE { " ++
  "<http://ex/a> <http://ex/age> ?a BIND(\"072\"^^xsd:integer AS ?b) }") ==
  some [some (.literal (mkTypedLiteral "072" RDF.xsdInteger))]

end L4Factoidal.SPARQL.NumericDerivedTests
