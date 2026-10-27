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

/-! ### ORDER BY an aggregate (https://github.com/danbri/factoidal/issues/1050)

§18.2.4.1: the aggregates of ORDER BY are computed in the Aggregation step, so
`ORDER BY DESC(COUNT(?s))` orders the groups by their counts. -/

private def iriName : Term → Option String
  | .iri i => some (i.val.drop "http://example.org/".length).toString
  | _ => none

/-- The local names of the IRIs that `v` is bound to, row by row. -/
private def column (v : VarName) (text : String) : Option (List String) :=
  (answer text).map fun r => r.2.filterMap (fun mu => (mu.lookup v).bind iriName)

private def ex (l : String) : String := l

private def typeData : String :=
  "PREFIX : <http://example.org/> SELECT ?type WHERE { " ++
  "VALUES (?s ?type) { (:b :D) (:a :L) (:c :D) (:d :N) (:e :N) (:f :N) } } GROUP BY ?type "

#guard column "type" (typeData ++ "ORDER BY DESC(COUNT(?s))") == some [ex "N", ex "D", ex "L"]
#guard column "type" (typeData ++ "ORDER BY (COUNT(?s))") == some [ex "L", ex "D", ex "N"]
#guard column "type" (typeData ++ "ORDER BY ASC(COUNT(?s))") == some [ex "L", ex "D", ex "N"]
-- An aggregate inside a larger expression, and a second condition.
#guard column "type" (typeData ++ "ORDER BY DESC(COUNT(?s) * 2 + 1)") == some [ex "N", ex "D", ex "L"]
#guard column "type" (typeData ++ "ORDER BY DESC(COUNT(?s) > 1) ?type") == some [ex "D", ex "N", ex "L"]
-- The alias form gives the same order.
#guard (answer ("PREFIX : <http://example.org/> SELECT ?type (COUNT(?s) AS ?n) WHERE { " ++
    "VALUES (?s ?type) { (:b :D) (:a :L) (:c :D) (:d :N) (:e :N) (:f :N) } } GROUP BY ?type " ++
    "ORDER BY DESC(?n)")).map (fun r => r.2.filterMap (fun mu => (mu.lookup "type").bind iriName)) ==
  some [ex "N", ex "D", ex "L"]
-- The key variable is not projected.
#guard (answer (typeData ++ "ORDER BY DESC(COUNT(?s))")).map (·.2.all (·.length == 1)) == some true
-- With LIMIT the order decides the answer (RDF4J sparql11-subquery-03 shape).
#guard (answer ("PREFIX : <http://example.org/> SELECT ?popular WHERE { " ++
    "VALUES (?someone ?popular) { (:george :ringo) (:george :john) (:ringo :george) " ++
    "(:ringo :john) (:paul :george) (:paul :john) } } GROUP BY ?popular " ++
    "ORDER BY DESC(COUNT(?someone)) LIMIT 1")).map (fun r => r.2.filterMap (fun mu => (mu.lookup "popular").bind iriName)) ==
  some ["john"]
#guard orderHasAggregate [.desc count]
#guard !orderHasAggregate [.asc (.var "x")]

end L4Factoidal.SPARQL.AggregateExpressionTests
