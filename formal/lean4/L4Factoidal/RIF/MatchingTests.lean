import L4Factoidal.RIF.Saturate

namespace L4Factoidal.RIF.MatchingTests

private def integerOne := gLit "1" (xsdNs ++ "integer")
private def decimalOne := gLit "1.0" (xsdNs ++ "decimal")
private def literalTm (s t : String) : Tm := .const s (xsdNs ++ t)

#guard (matchTm [] (literalTm "1" "integer") decimalOne).1.isSome
#guard (matchTm [("x", integerOne)] (.var "x") decimalOne).1.isSome
#guard !(matchAtom [] [] (.equal (literalTm "1" "integer")
  (literalTm "1.0" "decimal"))).1.isEmpty
#guard (matchAtom [] [] (.equal (.var "x") (literalTm "1" "integer"))).1.length == 1
#guard (matchAtom [] [] (.equal (literalTm "1" "integer") (.var "x"))).1.length == 1
#guard (matchTm [] (literalTm "bad" "decimal") decimalOne).2
#guard (matchTm [("x", gLit "bad" (xsdNs ++ "decimal"))] (.var "x") decimalOne).2
#guard (matchTm [] (.list [literalTm "1" "integer"]) (.list [decimalOne])).1.isSome

#guard Saturate.termOfG (.const "hello@" (rdfNs ++ "PlainLiteral")) ==
  some (.literal (RDF.Literal.string "hello"))
#guard Saturate.termOfG (.const "a@b@" (rdfNs ++ "PlainLiteral")) ==
  some (.literal (RDF.Literal.string "a@b"))

#guard groundMatch integerOne decimalOne == .yes
#guard groundMatch integerOne (gStr "1") == .no
#guard groundMatch (gIri "https://example.org/a") (gIri "https://example.org/b") == .no
#guard groundMatch (.list [integerOne]) decimalOne == .no
#guard groundMatch (.list [integerOne]) (.list [decimalOne]) == .yes
#guard groundMatch (.list []) (.list [integerOne]) == .no
#guard groundMatch (gLit "a" (xsdNs ++ "QName")) (gLit "b" (xsdNs ++ "QName")) == .unknown
#guard groundMatch (.fapp "f" iriSpace [integerOne]) (.fapp "f" iriSpace [decimalOne]) == .yes
#guard groundMatch (gLit "2002-10-10T12:00:00-05:00" (xsdNs ++ "dateTime"))
  (gLit "2002-10-10T17:00:00Z" (xsdNs ++ "dateTime")) == .no
#guard groundMatch (gLit "true" (xsdNs ++ "boolean")) (gLit "1" (xsdNs ++ "boolean")) == .yes
#guard groundMatch (gLit "0" (xsdNs ++ "double")) (gLit "-0" (xsdNs ++ "double")) == .no
#guard groundMatch (.const "hello@EN" (rdfNs ++ "PlainLiteral"))
  (.const "hello@en" (rdfNs ++ "PlainLiteral")) == .yes
#guard groundMatch (.const "hello@" (rdfNs ++ "PlainLiteral")) (gStr "hello") == .yes
#guard (matchTm [] (.list [.var "x", .var "x"]) (.list [integerOne, decimalOne])).1.isSome
#guard !(matchTm [] (.list [.var "x", .var "x"]) (.list [integerOne, gStr "1"])).1.isSome
#guard (matchTm [] (.fapp "f" iriSpace [.var "x"]) (.fapp "f" iriSpace [integerOne])).1.isSome
#guard (matchAtom [] [] (.equal (.list [.var "x"])
  (.list [literalTm "1" "integer"]))).1.length == 1
#guard (matchAtom [] [] (.equal (.var "x") (.var "y"))).2
#guard (matchAtom [] [] (.equal (literalTm "bad" "decimal") (literalTm "1" "integer"))).2

private def joined : Atom := .pos "joined" iriSpace [.var "x"]
private def joinRule : Rule :=
  { vars := ["x"], head := joined
    body := some (.and [.atom (.pos "p" iriSpace [.var "x"]),
      .atom (.pos "q" iriSpace [.var "x"])]) }
private def joinFacts : Facts := [.pos "p" iriSpace [integerOne], .pos "q" iriSpace [decimalOne]]

#guard entails [joinRule] joinFacts (.atom (.pos "joined" iriSpace [literalTm "1.0" "decimal"])) 4 == .holds
#guard entails [] [.frame (gIri "s") (gIri "p") decimalOne]
  (.atom (.frame (.const "s" iriSpace) (.const "p" iriSpace) (literalTm "1" "integer"))) 4 == .holds
#guard entails [{ head := joined, body := some (.atom (.equal (.var "x") (literalTm "1" "integer"))) }]
  [] (.atom (.pos "joined" iriSpace [literalTm "1.0" "decimal"])) 4 == .holds
#guard (match entails [joinRule] [.pos "p" iriSpace [gLit "bad" (xsdNs ++ "decimal")],
    .pos "q" iriSpace [integerOne]] (.atom joined) 4 with
  | .undecided _ => true | _ => false)
#guard (instantiate [] (.equal (literalTm "1" "integer") (literalTm "1" "integer"))).2

#guard RdfMapping.termOfG (.const "hello@EN" (rdfNs ++ "PlainLiteral")) ==
  some (.literal (RDF.Literal.langString "hello" "en"))
#guard (RdfMapping.termOfG (.const "missing delimiter" (rdfNs ++ "PlainLiteral"))).isNone
#guard RdfMapping.gOfTerm (.literal (RDF.Literal.string "hello")) == some (gStr "hello")
#guard ((RdfMapping.termOfG (.const "hello@" (rdfNs ++ "PlainLiteral"))).bind RdfMapping.gOfTerm) ==
  some (gStr "hello")
#guard ((RdfMapping.termOfG (.const "hello@EN" (rdfNs ++ "PlainLiteral"))).bind RdfMapping.gOfTerm) ==
  some (.const "hello@en" (rdfNs ++ "PlainLiteral"))

private def triple : RDF.Triple :=
  ⟨.iri ⟨"https://example.org/s", rfl⟩, ⟨"https://example.org/p", rfl⟩,
    .literal (RDF.Literal.string "hello")⟩
#guard (RdfMapping.factsOfTriple triple).filterMap RdfMapping.tripleOfGAtom == [triple]
#guard (RdfMapping.factsOfTriple { triple with p := RDFS.rdfType }).length == 2
#guard (RdfMapping.factsOfTriple { triple with p := RDFS.rdfsSubClassOf }).length == 2

private def emitsPlain : Rule :=
  { head := .frame (.const "https://example.org/s" iriSpace)
      (.const "https://example.org/p" iriSpace) (.const "hello@" (rdfNs ++ "PlainLiteral")) }
#guard (Saturate.saturateGraph "test" [emitsPlain] []).completeGraph?.any (·.contains triple)

end L4Factoidal.RIF.MatchingTests
