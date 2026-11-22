/- Checked RDFS execution regression tests. These guards are tests, not proofs.
Issue: https://github.com/danbri/factoidal-core/issues/745. -/
import L4Factoidal.RDFS.CheckedTheorems
import L4Factoidal.Syntax.NTriples

namespace L4Factoidal.RDFS.Checked.Tests

open L4Factoidal.RDF

def parsed (text : String) : Graph :=
  (L4Factoidal.Syntax.parseNTriples text).toOption.getD []

def sourceText : String :=
  "<urn:a> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:b> .\n" ++
  "<urn:b> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:c> .\n" ++
  "<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:a> .\n"

def source : Graph := parsed sourceText
def inferred : Graph := parsed
  "<urn:x> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:c> ."

def isExhausted : Except Error Graph → Bool
  | .error .exhausted => true
  | _ => false

def isLimit : Except Error Graph → Bool
  | .error .tripleLimit => true
  | _ => false

#guard (L4Factoidal.Syntax.parseNTriples sourceText).toOption.isSome
#guard source.length == 3
#guard inferred.length == 1
#guard isExhausted (loop 1024 0 [])
#guard (loop 0 1 []).toOption == some []
#guard isExhausted (loop 1024 1 source)
#guard isLimit (loop 2 8 source)
#guard isLimit (fullClosure ⟨64, 2⟩ [] [] source)

def complete : Except Error Graph := fullClosure ⟨64, 1024⟩ [] [] source
#guard complete.toOption.isSome
#guard complete.toOption.any (fun g => source.all (fun t => Graph.mem t g))
#guard complete.toOption.any (fun g => inferred.all (fun t => Graph.mem t g))
#guard complete.toOption.any (fun g => g == fullStep g)

-- An already saturated full-RDFS result needs exactly one checking round.
#guard complete.toOption.any (fun g => isExhausted (loop 1024 0 g))
#guard complete.toOption.any (fun g => (loop 1024 1 g).toOption == some g)
-- The final round's output cap is enforced, not merely the input cap.
#guard isLimit (loop source.length 4 source)

end L4Factoidal.RDFS.Checked.Tests
