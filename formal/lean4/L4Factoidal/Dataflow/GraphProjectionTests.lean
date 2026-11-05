/- Concrete public union-adapter handoff controls; no network or model driver. -/
import Wasm.Ops.Handles

namespace L4Factoidal.Dataflow.GraphProjectionTests
open L4Factoidal.RDF L4Factoidal.JSON L4Wasm.Ops

private def read (text : String) : IO Dataset :=
  match readNQuadsText .rdf12 text with
  | .ok ds => pure ds
  | .error e => throw (IO.userError (fmtParseError e))
private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)
private def handle (text : String) : IO String :=
  match (parseJson? text).bind (fun j => j.getString? "handle") with
  | some h => pure h
  | none => throw (IO.userError s!"missing handle: {text}")
private def data (h : String) : IO Dataset := do
  match ← lookupHandleDataset h with
  | some (ds, _) => pure ds
  | none => throw (IO.userError "missing stored dataset")

private def run : IO Unit := do
  let ds ← read "<urn:a> <urn:p> \"A\" .\n<urn:b> <urn:p> \"B\" <urn:g1> .\n<urn:a> <urn:p> \"A\" <urn:g1> .\n<urn:c> <urn:p> \"C\" <urn:g2> ."
  let expected ← read "<urn:a> <urn:p> \"A\" .\n<urn:b> <urn:p> \"B\" .\n<urn:c> <urn:p> \"C\" ."
  check (unionGraph ds == expected.default) "first-occurrence A/B/C order and cross-graph duplicate removal"
  let blank ← read "_:shared <urn:p> <urn:a> <urn:g1> .\n_:shared <urn:p> <urn:b> <urn:g2> .\n_:different <urn:p> <urn:c> <urn:g2> ."
  check ((unionGraph blank).map (·.s) == (blank.named.flatMap (·.graph)).map (·.s))
    "projection must not rename or merge distinct blank-node labels"
  let none : Dataset := { default := [], named := [] }
  check ((unionDefault none).default.isEmpty && (unionDefault none).named.isEmpty) "empty input is empty"
  let emptyNamed := { ds with default := [], named := ds.named.map (fun ng => { ng with graph := [] }) }
  check ((unionDefault emptyNamed).default.isEmpty && (unionDefault emptyNamed).named.isEmpty)
    "empty named graph identities are intentionally dropped"
  let source ← storeNewHandle ds >>= handle
  let projected ← datasetGraphAsDefault source "{\"type\":\"union\"}" >>= handle
  try
    let actual ← data projected
    check (actual.default == expected.default && actual.named.isEmpty)
      "actual handle op stores the proved producer in the same order"
    let retained ← data source
    check (retained.named.length == ds.named.length) "source named graphs are not mutated"
  finally
    let _ ← datasetClose source
    let _ ← datasetClose projected
  let language ← read "<urn:s> <urn:p> \"word\"@en <urn:g> .\n<urn:s> <urn:p> \"word\"@fr <urn:h> ."
  check ((unionDefault language).certify.val.default.length == 2)
    "language-tag distinctions survive the projection and certification"
  IO.println "Graph union handoff: 7 pass, 0 fail"

#eval run
end L4Factoidal.Dataflow.GraphProjectionTests
