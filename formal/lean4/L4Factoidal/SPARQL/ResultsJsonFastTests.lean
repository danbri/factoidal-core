import L4Factoidal.SPARQL.ResultsJsonFast

namespace L4Factoidal.SPARQL.ResultsJsonFastTests

open L4Factoidal.RDF

private def sameBytes (result : QueryResult) : Bool :=
  result.toSrjFast == result.toSrj

private def sampleRows : SolutionSeq :=
  [[("quoted\"var", .literal (Literal.string "quote\" slash\\\n\tΩ")),
    ("lang", .literal (Literal.langString "été" "fr"))],
   [],
   [("blank", .bnode "b0"),
    ("direction", .literal (Literal.dirLangString "مرحبا" "ar" .rtl))],
   [("triple", .tripleTerm (.iri ⟨"urn:subject", rfl⟩) ⟨"urn:predicate", rfl⟩
      (.tripleTerm (.bnode "nested") ⟨"urn:inner", rfl⟩
        (.literal (Literal.string "nested object"))))]]

#guard sameBytes (.bindings [] [])
#guard sameBytes (.bindings ["unbound"] [])
#guard sameBytes (.bindings [] [[]])
#guard sameBytes (.bindings [] [[], []])
#guard sameBytes (.boolean true)
#guard sameBytes (.boolean false)
#guard (QueryResult.boolean true).toSrjFast == "{\"head\":{},\"boolean\":true}"
#guard (QueryResult.bindings [] [[]]).toSrjFast ==
  "{\"head\":{\"vars\":[]},\"results\":{\"bindings\":[{}]}}"
#guard sameBytes (.bindings ["typed"]
  [[("typed", .literal ⟨
    { lexicalForm := "007", datatype := xsdInteger, langTag := none, direction := none }, rfl⟩)]])
#guard sameBytes (.bindings ["quoted\"var", "lang", "blank", "direction", "triple", "unbound"] sampleRows)
#guard sameBytes (.bindings ["repeated"]
  (List.replicate 37 [("repeated", .literal (Literal.string "same"))]))
#guard sameBytes (.bindings [] (List.replicate 1000 []))
#guard sameBytes (.bindings ["escaped\n\t\\\"Ω"] sampleRows)
#guard parseSrj (QueryResult.bindings
  ["quoted\"var", "lang", "blank", "direction", "triple", "unbound"] sampleRows).toSrjFast ==
  .ok (.bindings ["quoted\"var", "lang", "blank", "direction", "triple", "unbound"] sampleRows)

end L4Factoidal.SPARQL.ResultsJsonFastTests
