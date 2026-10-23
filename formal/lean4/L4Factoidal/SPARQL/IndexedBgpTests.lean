import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL.IndexedBgpTests

open L4Factoidal.RDF

private def alice : WfIri := ⟨"http://example.org/alice", by decide⟩
private def bob : WfIri := ⟨"http://example.org/bob", by decide⟩
private def namePred : WfIri := ⟨"http://example.org/name", by decide⟩
private def agePred : WfIri := ⟨"http://example.org/age", by decide⟩
private def rolePred : WfIri := ⟨"http://example.org/role", by decide⟩
private def knowsPred : WfIri := ⟨"http://example.org/knows", by decide⟩
private def absentPred : WfIri := ⟨"http://example.org/absent", by decide⟩

private def text (value : String) : Term := .literal (Literal.string value)

private def triple (subject predicate : WfIri) (object : Term) : Triple :=
  { s := .iri subject, p := predicate, o := object }

private def starGraph : Graph :=
  [triple alice namePred (text "Alice 1"),
   triple bob agePred (text "20"),
   triple alice agePred (text "30"),
   triple bob namePred (text "Bob"),
   triple alice rolePred (text "A"),
   triple alice namePred (text "Alice 2"),
   triple bob rolePred (text "B"),
   triple alice agePred (text "30")]

private def star : Bgp :=
  [{ s := .var "s", p := .iri namePred, o := .var "name" },
   { s := .var "s", p := .iri agePred, o := .var "age" },
   { s := .var "s", p := .iri rolePred, o := .var "role" }]

private def seededSpec (graph : Graph) (patterns : Bgp) (rows : SolutionSeq) :
    SolutionSeq :=
  rows.flatMap (evalBgpFrom graph patterns)

private def seeds : SolutionSeq :=
  [[("s", .iri alice), ("name", text "Alice 1")],
   [],
   [("s", .iri bob)],
   [("s", text "invalid subject")],
   [("age", text "30")]]

#guard evalBgpIdx star starGraph == evalBgp star starGraph
#guard (evalBgpIdx star starGraph).length == 5
#guard evalBgpIdx (star ++ star) starGraph == evalBgp (star ++ star) starGraph
#guard evalBgpRowsIdx starGraph star seeds == seededSpec starGraph star seeds
#guard evalBgpRowsIdx starGraph (star ++ star) seeds
  == seededSpec starGraph (star ++ star) seeds
#guard evalBgpIdx [] starGraph == [[]]
#guard evalBgpIdx star [] == []
#guard evalBgpRowsIdx starGraph [] seeds == seeds
#guard evalBgpRowsIdx starGraph star [] == []
#guard evalBgpIdx [{ s := .var "s", p := .iri absentPred, o := .var "o" }] starGraph == []
#guard evalBgpIdx (star ++ [{ s := .var "s", p := .iri absentPred, o := .var "o" }])
  starGraph == []

private def masks : Bgp :=
  [{ s := .var "s", p := .var "p", o := .var "o" },
   { s := .iri alice, p := .var "p", o := .var "o" },
   { s := .var "s", p := .iri namePred, o := .var "o" },
   { s := .var "s", p := .var "p", o := .literal (Literal.string "Alice 1") },
   { s := .iri alice, p := .iri namePred, o := .var "o" },
   { s := .iri alice, p := .var "p", o := .literal (Literal.string "Alice 1") },
   { s := .var "s", p := .iri namePred, o := .literal (Literal.string "Alice 1") },
   { s := .iri alice, p := .iri namePred, o := .literal (Literal.string "Alice 1") }]

#guard masks.all (fun pattern =>
  evalBgpStepIdx pattern starGraph seeds == seeds.flatMap (evalTP pattern starGraph))
#guard masks.all (fun pattern =>
  evalBgpIdx [pattern, pattern] starGraph == evalBgp [pattern, pattern] starGraph)

#guard evalBgpRowsCached starGraph star seeds [] == seededSpec starGraph star seeds
#guard evalBgpRowsCached starGraph (star ++ star) seeds []
  == seededSpec starGraph (star ++ star) seeds
#guard masks.all (fun pattern =>
  (evalBgpStepCached pattern starGraph seeds []).1
    == seeds.flatMap (evalTP pattern starGraph))
#guard masks.all (fun pattern =>
  evalBgpRowsCached starGraph [pattern, pattern] [[], []] []
    == seededSpec starGraph [pattern, pattern] [[], []])

private def runSteps (graph : Graph) (patterns : Bgp) (rows : SolutionSeq) :
    SolutionSeq × BgpIndexCache :=
  patterns.foldl (fun state pattern =>
    evalBgpStepCached pattern graph state.1 state.2) (rows, [])

#guard (runSteps starGraph star [[]]).2.length == 1
#guard (runSteps starGraph (star ++ star) [[]]).2.length == 2
#guard (runSteps starGraph star []).2.length == 0
#guard masks.all (fun pattern => (evalBgpStepCached pattern starGraph [[]] []).2.isEmpty)
#guard (evalBgpStepCached { s := .var "s", p := .var "p", o := .var "o" }
  starGraph [[], []] []).2.isEmpty

private def cachedMask : TpMask := { s := true, p := true, o := false }
private def cached : BgpIndexCache := (cachedTpIndex starGraph cachedMask []).2

#guard cached.length == 1
#guard (cachedTpIndex starGraph cachedMask cached).2.length == 1
#guard (cachedTpIndex starGraph { s := false, p := true, o := false } cached).2.length == 2
#guard (evalBgpStepCached { s := .var "s", p := .iri agePred, o := .var "age" }
  starGraph [] cached).2.length == 1
#guard (evalBgpStepCached { s := .var "s", p := .iri agePred, o := .var "age" }
  starGraph [[]] cached).2.length == 1

private def repeatedGraph : Graph :=
  [triple alice knowsPred (.iri bob),
   triple bob knowsPred (.iri bob),
   triple alice knowsPred (.iri alice),
   triple alice namePred (text "Alice")]

private def repeated : Bgp :=
  [{ s := .var "x", p := .iri knowsPred, o := .var "x" },
   { s := .var "x", p := .iri knowsPred, o := .var "y" },
   { s := .var "y", p := .iri knowsPred, o := .var "y" }]

#guard evalBgpIdx repeated repeatedGraph == evalBgp repeated repeatedGraph
#guard (evalBgpIdx repeated repeatedGraph).length == 3
#guard evalBgpIdx [{ s := .var "x", p := .literal (Literal.string "bad"), o := .var "o" }]
  repeatedGraph == []

private def langUpper : Term := .literal (Literal.langString "chat" "en-US")
private def langLower : Term := .literal (Literal.langString "chat" "en-us")
private def xml (value : String) : Term :=
  .literal ⟨{ lexicalForm := value, datatype := rdfXMLLiteral,
              langTag := none, direction := none }, by rfl⟩
private def xmlShort : Term := xml "<root/>"
private def xmlLong : Term := xml "<root></root>"
private def nestedUpper : Term := .tripleTerm (.iri alice) knowsPred langUpper
private def nestedLower : Term := .tripleTerm (.iri alice) knowsPred langLower

private def canonicalGraph : Graph :=
  [triple alice namePred langUpper,
   triple alice agePred langLower,
   triple bob namePred xmlShort,
   triple bob agePred xmlLong,
   triple alice rolePred nestedUpper,
   triple bob rolePred nestedLower]

private def canonicalJoin : Bgp :=
  [{ s := .var "s", p := .iri namePred, o := .var "value" },
   { s := .var "s", p := .iri agePred, o := .var "value" }]

#guard langUpper.eqb langLower
-- Two rdf:XMLLiteral spellings of one value are two RDF terms
-- (RDF 1.1 Concepts §3.3, https://github.com/danbri/factoidal/issues/963).
#guard !xmlShort.eqb xmlLong
#guard nestedUpper.eqb nestedLower
#guard evalBgpIdx canonicalJoin canonicalGraph == evalBgp canonicalJoin canonicalGraph
#guard (evalBgpIdx canonicalJoin canonicalGraph).length == 1
#guard evalBgpRowsIdx canonicalGraph
  [{ s := .var "s", p := .iri rolePred, o := .var "value" }]
  [[("value", nestedUpper)], [("value", nestedLower)], []]
  == seededSpec canonicalGraph
    [{ s := .var "s", p := .iri rolePred, o := .var "value" }]
    [[("value", nestedUpper)], [("value", nestedLower)], []]
#guard evalBgpIdx
  [{ s := .var "s", p := .iri rolePred,
     o := .tripleTerm (.iri alice) (.iri knowsPred) (.var "nested") },
   { s := .iri alice, p := .iri agePred, o := .var "nested" }]
  canonicalGraph
  == evalBgp
    [{ s := .var "s", p := .iri rolePred,
       o := .tripleTerm (.iri alice) (.iri knowsPred) (.var "nested") },
     { s := .iri alice, p := .iri agePred, o := .var "nested" }]
    canonicalGraph
#guard (evalBgpIdx
  [{ s := .var "s", p := .iri rolePred,
     o := .tripleTerm (.iri alice) (.iri knowsPred) (.var "nested") },
   { s := .iri alice, p := .iri agePred, o := .var "nested" }]
  canonicalGraph).length == 2

end L4Factoidal.SPARQL.IndexedBgpTests
