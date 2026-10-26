import L4Factoidal.RIF.Saturate

namespace L4Factoidal.RIF.BoundaryTests
open RDF

private def input (term : Term) : Graph :=
  [⟨.iri ⟨"urn:s", rfl⟩, ⟨"urn:p", rfl⟩, term⟩]
private def directed : Term := .literal (Literal.dirLangString "hello" "en" .ltr)
private def plain : Term := .literal (Literal.langString "hello" "en")
private def blocked : Rule :=
  { head := .pos "urn:result" iriSpace []
    body := some (.atom (.externalPred (predNs ++ "unimplemented") [])) }
private def noRdfSubject : Rule :=
  { head := .frame (.const "literal" (xsdNs ++ "string"))
      (.const "urn:p" iriSpace) (.const "urn:o" iriSpace) }

#guard (RdfMapping.gOfTerm directed).isNone
#guard (RdfMapping.gOfTerm plain).isSome
#guard !RdfMapping.graphMappingSupported (input directed)
#guard RdfMapping.graphMappingSupported (input plain)
#guard RdfMapping.graphMappingSupported []
#guard (Saturate.saturateGraph "t" [] []).complete
#guard (Saturate.saturateGraph "t" [] []).completeGraph? == some []
#guard (Saturate.saturateGraph "t" [] (input plain)).completeGraph? == some (input plain)
#guard (Saturate.saturateGraph "t" [] (input directed)).unsupportedInput
#guard (Saturate.saturateGraph "t" [] (input directed)).completeGraph?.isNone
#guard (Saturate.saturateGraph "t" [] (input directed)).partialGraph == input directed
#guard (Saturate.saturateGraph "t" [blocked] []).blocked
#guard (Saturate.saturateGraph "t" [blocked] []).completeGraph?.isNone
#guard (Saturate.saturateGraph "t" [] [] 0).capped
#guard (Saturate.saturateGraph "t" [] [] 0).completeGraph?.isNone
#guard (Saturate.saturateGraph "t" [noRdfSubject] []).unsupportedOutput
#guard (Saturate.saturateGraph "t" [noRdfSubject] []).completeGraph?.isNone
#guard (Saturate.saturateGraph "t" [{ head := .pos "urn:p" iriSpace [] }] []).complete
#guard (Saturate.saturateWithProgram "<bad" []).isNone
#guard !(Saturate.saturateGraph "t" [blocked] []).diagnostic.isEmpty
#guard (Saturate.saturateGraph "t" [] []).diagnostic.isEmpty

end L4Factoidal.RIF.BoundaryTests
