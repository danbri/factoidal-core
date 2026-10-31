/- Actual normalizer/closure boundary controls. Accepted fallback and empty-name
loss remain visible; neither is silently folded into the checked subset. -/
import Wasm.Ops.Handles

namespace L4Factoidal.Dataflow.NormalizationHandoffTests
open L4Factoidal.RDF L4Factoidal.Syntax L4Factoidal.JSON L4Wasm.Ops

private def read (text : String) : IO Dataset :=
  match readNQuadsText .rdf12 text with
  | .ok ds => pure ds
  | .error e => throw (IO.userError (fmtParseError e))
private def check (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError label)
private def handle (text : String) : IO String :=
  match (parseJson? text).bind (fun j => j.getString? "handle") with
  | some h => pure h
  | none => throw (IO.userError s!"missing handle: {text}")
private def stored (h : String) : IO Dataset := do
  match ← lookupHandleDataset h with
  | some (ds, _) => pure ds
  | none => throw (IO.userError "missing stored dataset")

private def run : IO Unit := do
  let text := "<urn:Contributor> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <urn:Person> <urn:schema> .\n_:alice <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:Contributor> <urn:people> .\n_:bob <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:Contributor> <urn:people> ."
  let source ← read text
  let input := (unionDefault source).certify
  check (roundTripSafe .rdf12 input.val) "actual union input must meet theorem's syntactic precondition"
  let .ok normalized := datasetForOps .rdf12 input.val | throw (IO.userError "safe normalization failed")
  check (normalized.default == input.val.default) "normalizer changed exact default input/order"
  let expected ← read "_:alice <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:Person> .\n_:bob <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <urn:Person> ."
  let .ok closure := closureStreamOf input.val "rdfs" | throw (IO.userError "actual safe closure failed")
  check (expected.default.all (fun t => closure.mem t)) "actual closure lost RDFS consequences or source blank nodes"
  let ih ← storeNewHandle (unionDefault source) >>= handle
  let oh ← datasetClosure ih "rdfs" >>= handle
  try
    let actual ← stored oh
    check (expected.default.all (fun t => actual.default.mem t)) "public handle closure lost consequences"
  finally
    let _ ← datasetClose ih
    let _ ← datasetClose oh
  let language ← read "<urn:s> <urn:p> \"word\"@en .\n<urn:s> <urn:p> <<( <urn:x> <urn:q> \"nested\"@fr )>> ."
  let typed := language.certify
  check (roundTripSafe .rdf12 typed.val && (normalizeDataset typed.val).default == typed.val.default)
    "typed language/nested triple-term normalization identity"
  let some triple := input.val.default.head? | throw (IO.userError "empty positive fixture")
  let duplicate : Dataset := { default := [triple,triple], named := [] }
  check ((normalizeDataset duplicate).default.length == 1 && duplicate.default.length == 2)
    "set premise must remain necessary for exact list identity"
  let some named := source.named.head? | throw (IO.userError "missing named positive fixture")
  let emptyName := ({ default := [triple], named := [{ named with graph := [] }] } : Dataset).certify
  let .ok removed := datasetForOps .rdf12 emptyName.val | throw (IO.userError "empty-name control failed")
  check (emptyName.val.named.length == 1 && removed.named.isEmpty && removed.default == emptyName.val.default)
    "empty named graph deletion must not be claimed full-dataset preservation"
  let escaped ← read "<urn:s> <urn:p> \"control\\u0001\" ."
  check (!roundTripSafe .rdf12 escaped.certify.val && (datasetForOps .rdf12 escaped.certify.val).isOk)
    "accepted unicode-escape fallback remains outside checked-subset theorem"
  IO.println "Normalizer/RDFS handoff: 8 pass, 0 fail; accepted fallback tested, outside theorem"

#eval run
end L4Factoidal.Dataflow.NormalizationHandoffTests
