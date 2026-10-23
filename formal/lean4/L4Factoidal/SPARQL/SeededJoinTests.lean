import L4Factoidal.SPARQL.SeededJoin

namespace L4Factoidal.SPARQL.SeededJoinTests

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan

private def alice : WfIri := ⟨"urn:alice", rfl⟩
private def bob : WfIri := ⟨"urn:bob", rfl⟩
private def predicate : WfIri := ⟨"urn:edge", rfl⟩
private def label : WfIri := ⟨"urn:label", rfl⟩
private def missing : WfIri := ⟨"urn:missing", rfl⟩

private def text (value : String) : Term := .literal (Literal.string value)

private def xml (value : String) : Term :=
  .literal ⟨{ lexicalForm := value, datatype := rdfXMLLiteral,
    langTag := none, direction := none }, rfl⟩

private def triple (subject pred : WfIri) (object : Term) : Triple :=
  ⟨.iri subject, pred, object⟩

private def graph : Graph :=
  [triple alice predicate (.iri bob), triple bob predicate (.iri alice),
   triple alice label (text "Alice"), triple alice predicate (.iri bob),
   triple bob label (text "Bob"), triple alice predicate (.iri alice),
   triple alice label (.literal (Literal.langString "colour" "EN")),
   triple bob label (.tripleTerm (.iri alice) predicate (.iri bob)),
   triple alice label (xml "<root/>"),
   triple bob label (.tripleTerm (.iri alice) predicate
     (.literal (Literal.langString "colour" "EN")))]

private def source := OWL.RL.Index.ofGraph graph

private def edge : TriplePattern := ⟨.var "s", .iri predicate, .var "o"⟩

private def seeds : SolutionSeq :=
  [[("s", .iri alice)], [], [("s", .iri bob)], [("o", .iri bob)],
   [("s", text "not a subject")], [("p", text "not a predicate")],
   [("outside", text "retained")], [("s", .iri alice), ("s", .iri bob)],
   [("s", .iri alice)], [("o", .literal (Literal.langString "colour" "en"))]]

private def patterns : List TriplePattern :=
  [edge, ⟨.var "s", .var "p", .var "o"⟩,
   ⟨.iri alice, .var "p", .var "o"⟩,
   ⟨.var "s", .iri missing, .var "o"⟩,
   ⟨.var "s", .var "p", .var "s"⟩,
   ⟨.var "same", .var "same", .var "same"⟩,
   ⟨.var "s", .iri label, .literal (Literal.langString "colour" "en")⟩,
   ⟨.var "s", .iri label, .tripleTerm (.var "inner") (.iri predicate) (.var "object")⟩,
   ⟨.tripleTerm (.var "s") (.var "p") (.var "o"), .var "p", .var "o"⟩]

private def agrees (pattern : TriplePattern) (rows : SolutionSeq) : Bool :=
  SeededJoin.single source pattern rows ==
    join rows (evalSingleTpBackend pattern (.indexed source) [])

private def chain : Bgp :=
  [edge, ⟨.var "o", .iri label, .var "name"⟩]

private def agreesBgp (patterns : Bgp) (rows : SolutionSeq) : Bool :=
  SeededJoin.bgp source patterns rows == join rows (evalBgpBackend patterns (.indexed source))

#guard patterns.all fun pattern => agrees pattern seeds
#guard patterns.all fun pattern => agrees pattern []
#guard patterns.all fun pattern => agrees pattern [[], []]
#guard SeededJoin.single source edge [] == []
#guard SeededJoin.single (OWL.RL.Index.ofGraph []) edge seeds == []
#guard SeededJoin.single source edge [[("s", .iri alice)]] ==
  [[("o", .iri bob), ("s", .iri alice)],
   [("o", .iri bob), ("s", .iri alice)],
   [("o", .iri alice), ("s", .iri alice)]]
#guard (SeededJoin.single source edge [[("s", .iri alice)], [("s", .iri alice)]]).length == 6
#guard SeededJoin.single source edge [[("s", .iri alice), ("s", .iri bob)]] == []
#guard (SeededJoin.single source edge [[("outside", text "retained")]]).head? ==
  some [("s", .iri alice), ("o", .iri bob), ("outside", text "retained")]
#guard SeededJoin.single source ⟨.var "s", .iri label, .var "o"⟩
  [[("o", .literal (Literal.langString "colour" "en"))]] ==
    [[("s", .iri alice), ("o", .literal (Literal.langString "colour" "en"))]]
#guard agrees ⟨.var "s", .var "p", .var "o"⟩
  [[("s", .iri alice), ("p", .iri predicate), ("o", .iri bob)],
   [("s", .iri bob), ("p", text "not a predicate")],
   [("o", .tripleTerm (.iri alice) predicate (.iri bob))]]
#guard agrees edge (evalValues ["s", "outside"]
  [[some (.iri alice), none], [none, some (text "retained")],
   [some (.iri alice), none]])
#guard agrees edge (evalValues ["s", "s"] [[some (.iri alice), some (.iri bob)]])
#guard agrees ⟨.var "s", .iri label, .var "o"⟩
  [[("o", xml "<root></root>")],
   [("o", .tripleTerm (.iri alice) predicate
     (.literal (Literal.langString "colour" "en")))]]
#guard agrees ⟨.var "s", .iri label,
  .tripleTerm (.var "inner") (.iri predicate) (.var "object")⟩
  [[("inner", .iri alice), ("object", .iri bob)],
   [("inner", .iri alice), ("object", .literal (Literal.langString "colour" "en"))],
   [("inner", text "not a subject"), ("object", .iri bob)]]
#guard let invalid := { source with bySP := ∅ }
  SeededJoin.single invalid edge [[("s", .iri alice)]] !=
    join [[("s", .iri alice)]] (evalSingleTpBackend edge (.indexed invalid) [])
#guard agreesBgp chain seeds
#guard agreesBgp chain.reverse seeds
#guard agreesBgp (chain ++ chain) seeds
#guard agreesBgp chain [[("name", text "Bob")]]
#guard SeededJoin.bgp source chain [[("name", text "Bob")]] ==
  [[("s", .iri alice), ("o", .iri bob), ("name", text "Bob")],
   [("s", .iri alice), ("o", .iri bob), ("name", text "Bob")]]
#guard SeededJoin.bgp source [] seeds == seeds
#guard SeededJoin.bgp source chain [] == []
#guard SeededJoin.bgp source chain [[], []] ==
  join [[], []] (evalBgpBackend chain (.indexed source))
#guard agreesBgp [⟨.var "s", .iri label, .var "o"⟩,
  ⟨.var "s", .var "pred", .var "o"⟩]
  [[("o", xml "<root></root>")],
   [("o", .literal (Literal.langString "colour" "en"))]]

end L4Factoidal.SPARQL.SeededJoinTests
