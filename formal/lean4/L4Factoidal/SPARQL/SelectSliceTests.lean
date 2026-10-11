import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL.SelectSliceTests

open L4Factoidal.RDF

private def rows : SolutionSeq :=
  ([(2, "a"), (1, "b"), (2, "c"), (0, "d"), (1, "e"), (2, "f"), (0, "g")] : List (Nat × String)).map fun (n, name) =>
    [("key", .literal (Literal.string (toString n))),
     ("name", .literal (Literal.string name))]
private def cmp := compareOnConditions emptyEnv [] [.asc (.var "key")]
private def projections : List (Binding → Binding) :=
  [id, projectBinding ["key"], projectBinding ["name"], fun _ => []]

#guard ([none, some cmp] : List (Option (Binding → Binding → Int))).all fun order =>
  projections.all fun project =>
    [false, true].all fun distinct =>
      [false, true].all fun reduced =>
        ([none, some 0, some 1, some 3, some 20] : List (Option Nat)).all fun offset =>
          ([none, some 0, some 1, some 3, some 20] : List (Option Nat)).all fun limit =>
            finishSelectRowsPrefix order project distinct reduced offset limit rows
              == finishSelectRows order project distinct reduced offset limit rows

end L4Factoidal.SPARQL.SelectSliceTests
