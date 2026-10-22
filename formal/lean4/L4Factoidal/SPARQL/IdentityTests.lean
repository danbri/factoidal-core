/- RDF term identity survives expression evaluation; value operators opt in
   to datatype conversion. Authored SPARQL §17 regressions, not a corpus. -/
import L4Factoidal.SPARQL.Expr
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SHACL.Sparql

namespace L4Factoidal.SPARQL.IdentityTests
open L4Factoidal.RDF

private def integer (s : String) := mkTypedLiteral s RDF.xsdInteger
private def mu : Binding := [("n", .literal (integer "01")),
  ("zero", .literal (integer "00")),
  ("f", .literal (mkTypedLiteral "1.0" xsdFloat)),
  ("b", .literal (mkTypedLiteral "1" RDF.xsdBoolean))]

#guard (Expr.var "n").eval mu == .term (.literal (integer "01"))
#guard (Expr.str (.var "n")).eval mu == erString "01"
#guard (Expr.str (.cond (.boolLit true) (.var "n") (.numericLit 0))).eval mu == erString "01"
#guard (Expr.str (.coalesce [.var "missing", .var "n"])).eval mu == erString "01"
#guard (Expr.datatype (.var "f")).eval mu == .term (.iri xsdFloat)
#guard (Expr.str (.var "b")).eval mu == erString "1"
#guard (Expr.str (.boolLit true)).eval [] == erString "true"
#guard (Expr.str (.var "blank")).eval [("blank", .bnode "x")] == .error
#guard (Expr.compare .eq (.var "n") (.numericLit 1)).eval mu == .bool true
#guard (Expr.compare .eq (.lit (integer "01")) (.decimalLit "1.0")).eval [] == .bool true
#guard (Expr.arith .add (.var "n") (.numericLit 1)).eval mu == .num 2
#guard (Expr.unaryMinus (.var "n")).eval mu == .num (-1)
#guard (Expr.abs (.var "n")).eval mu == .num 1
#guard (Expr.not (.var "zero")).eval mu == .bool true
#guard (Expr.sameTerm (.var "n") (.numericLit 1)).eval mu == .bool false
#guard (Expr.sameTerm (.var "n") (.lit (integer "01"))).eval mu == .bool true
#guard (Expr.sameTerm (.var "missing") (.numericLit 1)).eval mu == .error
#guard (Expr.sameTerm (.lit (mkTypedLiteral "<e/>" rdfXMLLiteral))
  (.lit (mkTypedLiteral "<e></e>" rdfXMLLiteral))).eval [] == .bool false
#guard (Expr.compare .eq (.lit (Literal.langString "x" "en"))
  (.lit (Literal.langString "x" "EN"))).eval [] == .bool true
#guard (Expr.sameTerm (.lit (Literal.langString "x" "en"))
  (.lit (Literal.langString "x" "EN"))).eval [] == .bool true
#guard (Expr.compare .eq (.var "a") (.var "b")).eval
  [("a", .bnode "x"), ("b", .bnode "x")] == .bool true

private def queryValue (text name : String) : Option Term := do
  let q ← (parseSparql text).toOption
  let row ← (evalSelect emptyEnv Dataset.empty q).2.head?
  row.lookup name

#guard queryValue "SELECT (STR(01) AS ?s) WHERE {}" "s" == some (.literal (Literal.string "01"))
#guard queryValue "SELECT (?n AS ?copy) WHERE { VALUES ?n { 01 } }" "copy" ==
  some (.literal (integer "01"))
#guard queryValue "SELECT ?copy WHERE { VALUES ?n { 01 } BIND(COALESCE(?n, 0) AS ?copy) }" "copy" ==
  some (.literal (integer "01"))
#guard queryValue "SELECT (SUM(?n) AS ?sum) WHERE { VALUES ?n { 01 2 } }" "sum" ==
  some (.literal (integer "3"))
#guard queryValue "SELECT (MIN(?n) AS ?min) WHERE { VALUES ?n { 01 2.2 } }" "min" ==
  some (.literal (integer "01"))
#guard queryValue "SELECT ?n WHERE { VALUES ?n { 2.2 01 } } ORDER BY ?n LIMIT 1" "n" ==
  some (.literal (integer "01"))
#guard queryValue "SELECT (COUNT(DISTINCT ?n) AS ?count) WHERE { VALUES ?n { 01 1 01 } }" "count" ==
  some (.literal (integer "2"))
#guard queryValue "SELECT (COUNT(*) AS ?count) WHERE { VALUES ?n { 1 001 1 } } GROUP BY ?n ORDER BY DESC(?count)" "count" ==
  some (.literal (integer "2"))
#guard (L4Factoidal.SHACL.substVarExpr "value" (.literal (integer "01"))
  (.str (.var "value"))).eval [] == erString "01"

/-- No datatype conversion is hidden in variable lookup, for any RDF term. -/
theorem lookup_preserves_term (env : EvalEnv) (row : Binding) (name : VarName) (t : Term)
    (h : row.lookup name = some t) : Expr.evalIn env row (.var name) = .term t := by
  simp [Expr.evalIn, h]
#print axioms lookup_preserves_term

end L4Factoidal.SPARQL.IdentityTests
