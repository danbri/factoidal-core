import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL.AggregateExpressionTests

open L4Factoidal.RDF

private def count : Expr := .aggregate .count false (.var "x")
private def group : SolutionGroup :=
  { key := [], solutions := [[("x", .literal (Literal.string "a"))],
                             [("x", .literal (Literal.string "b"))]] }

#guard exprHasAggregate (.str count)
#guard exprHasAggregate (.concat [.lit (Literal.string "n="), .str count])
#guard exprHasAggregate (.coalesce [.var "missing", count])
#guard exprHasAggregate (.substr (.str count) (.numericLit 1) (some count))
#guard exprHasAggregate (.regex (.lit (Literal.string "a")) (.lit (Literal.string "a")) (some (.str count)))
#guard evalExprInGroup emptyEnv group (.str count) == .term (.literal (Literal.string "2"))
#guard evalExprInGroup emptyEnv group (.unaryMinus count) == .num (-2)
#guard evalExprInGroup emptyEnv group (.coalesce [count, .numericLit 99]) == .num 2
#guard evalExprInGroup emptyEnv group (.cond (.compare .gt count (.numericLit 0))
  (.str count) (.lit (Literal.string "empty"))) == .term (.literal (Literal.string "2"))

private def answer (text : String) : Option (List VarName × SolutionSeq) := do
  let query ← (parseSparql text).toOption
  return evalSelect emptyEnv Dataset.empty query

#guard answer "SELECT (STR(COUNT(?x)) AS ?n) WHERE { VALUES ?x { 1 2 3 } }" ==
  some (["n"], [[("n", .literal (Literal.string "3"))]])
#guard answer "SELECT (CONCAT(\"n=\", STR(COUNT(*))) AS ?n) WHERE { VALUES ?x { 1 2 3 } }" ==
  some (["n"], [[("n", .literal (Literal.string "n=3"))]])
#guard answer "SELECT (STR(COUNT(*)) AS ?n) WHERE { VALUES ?x {} }" ==
  some (["n"], [[("n", .literal (Literal.string "0"))]])
#guard answer "SELECT ?g (STR(COUNT(?x)) AS ?n) WHERE { VALUES (?g ?x) { (\"a\" 1) (\"a\" 2) (\"b\" 3) } } GROUP BY ?g ORDER BY ?g" ==
  some (["g", "n"], [[("g", .literal (Literal.string "a")), ("n", .literal (Literal.string "2"))],
                      [("g", .literal (Literal.string "b")), ("n", .literal (Literal.string "1"))]])

#guard (parseSparql "SELECT (COUNT(SUBSTR(\"abc\", 1, STR(COUNT(*)))) AS ?n) WHERE {}").toOption.isNone
#guard (parseSparql "SELECT (COUNT(REGEX(\"abc\", \"a\", STR(COUNT(*)))) AS ?n) WHERE {}").toOption.isNone
#guard (parseSparql "SELECT (COUNT(REPLACE(\"abc\", \"a\", \"b\", STR(COUNT(*)))) AS ?n) WHERE {}").toOption.isNone

-- A subquery aggregate belongs to its own query scope.
#guard !exprHasAggregate (.existsPat (.subSelect (mkQuery
  (.select (.vars [.expr count "n"])) .empty)))

end L4Factoidal.SPARQL.AggregateExpressionTests
