/- Snapshot preservation across serialized SPARQL result entry points.
No network transport; providers are registered local graph values. -/
import Wasm.Ops.Handles

namespace L4Wasm.Ops.ServiceSerializationTests
open L4Factoidal.JSON

private def query := "SELECT ?v WHERE { VALUES ?ep { <urn:one> } SERVICE ?ep { ?s <urn:value> ?v } }"
private def graphText := "<urn:s> <urn:value> \"one\" ."
private def opts := "{\"dataFormat\":\"ntriples\",\"output\":\"xml\"}"
private def ok (text : String) : Bool :=
  (parseJson? text).bind (fun j => j.field? "ok") == some (.bool true)
private def containsText (text needle : String) : Bool := (text.splitOn needle).length > 1
private def expected (text : String) : Bool := ok text && containsText text ">one<"
private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def run : IO Unit := do
  let _ ← clearServiceEndpoints
  let _ ← extClear
  let _ ← registerServiceEndpoint "urn:one" graphText
  let captured ← serviceSnapshot
  check (expected (queryRawBy noExtraReader "" query opts none (extFnsWith []) captured))
    "explicit captured providers are preserved in XML output"
  check (!ok (queryRawBy noExtraReader "" query opts))
    "pure defaults do not acquire ambient providers"
  check (expected (← queryRawIOBy noExtraReader "" query opts))
    "IO queryRaw snapshots providers"
  let stored ← storeNewHandle { default := [], named := [] }
  let some handle := (parseJson? stored).bind (fun j => j.getString? "handle")
    | throw (IO.userError "missing test dataset handle")
  try
    check (expected (← datasetQueryRaw handle query opts))
      "stored dataset serialization snapshots providers"
    let _ ← clearServiceEndpoints
    check (!ok (← queryRawIOBy noExtraReader "" query opts))
      "next IO query observes provider removal"
    check (!ok (← datasetQueryRaw handle query opts))
      "next stored-dataset query observes provider removal"
    check (expected (queryRawBy noExtraReader "" query opts none (extFnsWith []) captured))
      "explicit immutable snapshot survives ambient mutation"
  finally
    let _ ← datasetClose handle
    let _ ← clearServiceEndpoints
  IO.println "SERVICE serialization snapshots: 7 pass, 0 fail"

#eval run
end L4Wasm.Ops.ServiceSerializationTests
