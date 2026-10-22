import L4Factoidal.SPARQL.HashGrouping

namespace L4Factoidal.SPARQL.HashGroupingTests

open L4Factoidal.RDF

private def a : WfIri := ⟨"urn:a", rfl⟩
private def b : WfIri := ⟨"urn:b", rfl⟩
private def view (groups : List SolutionGroup) := groups.map fun g => (g.key, g.solutions)
private def rows : SolutionSeq :=
  [[("g", .iri b), ("name", .literal (Literal.string "first"))],
   [("g", .iri a), ("name", .literal (Literal.string "second"))],
   [("g", .iri b), ("name", .literal (Literal.string "third"))],
   [("name", .literal (Literal.string "unbound"))]]

#guard (HashGrouping.key? [.error]).isSome
#guard (HashGrouping.key? [.bool true, .term (.iri a), .term (.bnode "blank")]).isSome
#guard (HashGrouping.key? [.term (.literal (Literal.string "Ω"))]).isSome
#guard (HashGrouping.key? [.num 1]).isSome
#guard (HashGrouping.key? [.dec "1.00"]).isSome
#guard (HashGrouping.key? [.dbl "NaN"]).isSome
#guard (HashGrouping.key? [.term (.tripleTerm (.iri a) b (.iri a))]).isNone
#guard HashGrouping.key? [.term (.literal (Literal.langString "colour" "en"))] ==
  HashGrouping.key? [.term (.literal (Literal.langString "colour" "EN"))]
-- Grouping shares RDF term identity: tag case folds, direction remains distinct.
#guard HashGrouping.key? [.term (.literal (mkDirLangLiteral "word" "en" .ltr))] !=
  HashGrouping.key? [.term (.literal (mkDirLangLiteral "word" "en" .rtl))]

-- Computed numbers share keys with their projected terms, without merging
-- alternate lexical spellings or datatypes. Errors form one unbound group.
#guard HashGrouping.key? [.num 1] ==
  HashGrouping.key? [.term (.literal (mkTypedLiteral "1" xsdInteger))]
#guard HashGrouping.key? [.num 1] !=
  HashGrouping.key? [.term (.literal (mkTypedLiteral "001" xsdInteger))]
#guard HashGrouping.key? [.num 1] != HashGrouping.key? [.dec "1"]
#guard HashGrouping.key? [.bool true] ==
  HashGrouping.key? [.term (.literal (mkTypedLiteral "true" xsdBoolean))]
#guard HashGrouping.key? [.bool true] !=
  HashGrouping.key? [.term (.literal (mkTypedLiteral "1" xsdBoolean))]
#guard erEqual .error .error
#guard !erEqual .error (.num 0)

private def identityRows : SolutionSeq :=
  [[("g", .literal (mkTypedLiteral "1" xsdInteger))],
   [("g", .literal (mkTypedLiteral "001" xsdInteger))],
   [("g", .literal (mkTypedLiteral "1" xsdInteger))]]
#guard ([.var "g", .expr (.var "g") none] : List GroupCondition).all fun condition =>
  let expected := [([.term (.literal (mkTypedLiteral "1" xsdInteger))],
      [identityRows[0]!, identityRows[2]!]),
    ([.term (.literal (mkTypedLiteral "001" xsdInteger))], [identityRows[1]!])]
  view (HashGrouping.groupSolutionsFast emptyEnv [condition] identityRows) == expected &&
    view (groupSolutions emptyEnv [condition] identityRows) == expected

#guard view (HashGrouping.groupSolutionsFast emptyEnv [.var "g"] rows) ==
  [([.term (.iri b)], [rows[0]!, rows[2]!]),
   ([.term (.iri a)], [rows[1]!]), ([.error], [rows[3]!])]
#guard view (HashGrouping.groupSolutionsFast emptyEnv [.var "g"] rows) ==
  view (groupSolutions emptyEnv [.var "g"] rows)
#guard view (HashGrouping.groupSolutionsFast emptyEnv [] rows) == [([], rows)]
#guard view (HashGrouping.groupSolutionsFast emptyEnv [.var "g"] []) == []
#guard view (HashGrouping.groupSolutionsFast emptyEnv [.var "g", .var "name"] rows) ==
  view (groupSolutions emptyEnv [.var "g", .var "name"] rows)
#guard view (HashGrouping.groupSolutionsFast emptyEnv [.expr (.str (.var "g")) (some "alias")] rows) ==
  view (groupSolutions emptyEnv [.expr (.str (.var "g")) (some "alias")] rows)

private def numericRows : SolutionSeq :=
  [[("g", .iri a)], [("g", .literal (mkTypedLiteral "1" xsdInteger))],
   [("g", .literal (mkTypedLiteral "1.0" xsdDecimal))], [("g", .iri a)]]
#guard view (HashGrouping.groupSolutionsFast emptyEnv [.expr (.var "g") none] numericRows) ==
  view (groupSolutions emptyEnv [.expr (.var "g") none] numericRows)
#guard view (HashGrouping.groupSolutionsFast emptyEnv [.var "g"] numericRows) ==
  view (groupSolutions emptyEnv [.var "g"] numericRows)

private def grouped (selection : SelectClause) (having : List Expr)
    (modifier : SolutionModifier) (postValues : Option SolutionSeq) : Query :=
  .mk (.select selection) [] .empty (some [.var "g"]) having modifier postValues none
private def count : Expr := .aggregate .count false (.boolLit true)
private def selections : List SelectClause :=
  [.all, .vars [.var "g", .expr (.str count) "n"]]
private def modifiers : List SolutionModifier :=
  [{}, { orderBy := some [.asc (.var "g")] }, { distinct := true },
   { reduced := true, offset := some 1, limit := some 2 }, { limit := some 0 }]
#guard selections.all fun selection =>
  modifiers.all fun modifier =>
    ([[], [.compare .gt count (.numericLit 1)]] : List (List Expr)).all fun having =>
      ([none, some [[("g", .iri b)]], some []] : List (Option SolutionSeq)).all fun postValues =>
        let query := grouped selection having modifier postValues
        HashGrouping.selectPostFast emptyEnv [] query rows == selectPost emptyEnv [] query rows
#guard HashGrouping.selectPostFast emptyEnv [] (mkQuery (.select .all) .empty) rows ==
  selectPost emptyEnv [] (mkQuery (.select .all) .empty) rows

end L4Factoidal.SPARQL.HashGroupingTests
