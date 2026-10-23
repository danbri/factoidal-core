import Wasm.Ops.ReasonDl
open L4Wasm.Ops
private def rdf := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
private def owl := "http://www.w3.org/2002/07/owl#"
private def rdfs := "http://www.w3.org/2000/01/rdf-schema#"
private def edge (s p o : String) := s!"<{s}> <{p}> <{o}> .\n"
#eval owlEntails "" "<urn:a> <urn:p> \"value\" ." ""
#eval owlEntails "" "_:b <urn:p> <urn:o> ." ""
#eval owlEntails "" (edge "urn:a" (rdf ++ "type") "urn:C") "{\"fuel\":\"0\"}"
#eval owlIsConsistent (edge "urn:a" (owl ++ "sameAs") "urn:b" ++ edge "urn:a" (owl ++ "differentFrom") "urn:b") "{\"fuel\":\"0\"}"
