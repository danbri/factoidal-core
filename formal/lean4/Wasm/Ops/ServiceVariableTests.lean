/- Parsed-query regression for backend/reference SERVICE variable correlation.
SPARQL 1.1 Federation section 4 is informative; these pin the already implemented
reference behavior, not a new claim of normative variable-SERVICE semantics.
https://github.com/danbri/factoidal/issues/1212
-/
import Wasm.Ops.Query

namespace L4Wasm.Ops.ServiceVariableTests
open L4Factoidal L4Factoidal.RDF L4Factoidal.Dataflow L4Factoidal.JSON

private structure Case where
  name : String
  query : String
  values : List String := []
  data : String := ""
  denied : Bool := false
  error : Bool := false
  retained : String := ""

private def body := "{ ?s <urn:value> ?v }"
private def endpoints := "VALUES ?endpoint { <urn:one> <urn:two> }"
private def service := "SERVICE ?endpoint " ++ body
private def selected (pattern : String) := "SELECT ?v ?tag WHERE { " ++ pattern ++ " } ORDER BY ?v"
private def localData := "<urn:one> <urn:enabled> \"yes\" ."
private def cases : List Case := [
  {name:="VALUES right",query:=selected (endpoints++service),values:=["one","two"]},
  {name:="VALUES left",query:=selected (service++endpoints),values:=["one","two"]},
  {name:="BIND right",query:=selected ("BIND(<urn:one> AS ?endpoint) "++service),values:=["one"]},
  {name:="BIND left grouped",query:=selected (service++" { BIND(<urn:one> AS ?endpoint) }"),values:=["one"]},
  {name:="late BIND scope refusal",query:=selected (service++" BIND(<urn:one> AS ?endpoint)"),error:=true},
  {name:="triple right",data:=localData,query:=selected ("?endpoint <urn:enabled> ?tag . "++service),values:=["one"]},
  {name:="triple left",data:=localData,query:=selected (service++" ?endpoint <urn:enabled> ?tag ."),values:=["one"]},
  {name:="bag duplicates",query:=selected ("VALUES ?endpoint { <urn:one> <urn:one> <urn:two> } "++service),values:=["one","one","two"]},
  {name:="compatible shared binding",query:=selected ("VALUES (?endpoint ?v) { (<urn:one> \"wrong\") (<urn:one> \"one\") } "++service),values:=["one"]},
  {name:="known SILENT",query:=selected ("VALUES ?endpoint { <urn:one> } SERVICE SILENT ?endpoint "++body),values:=["one"]},
  {name:="unknown SILENT",query:=selected ("VALUES (?endpoint ?tag) { (<urn:missing> \"keep\") } SERVICE SILENT ?endpoint "++body),values:=["<unbound>"],retained:="keep"},
  {name:="nonIRI SILENT",query:=selected ("VALUES (?endpoint ?tag) { (42 \"keep\") } SERVICE SILENT ?endpoint "++body),values:=["<unbound>"],retained:="keep"},
  {name:="unknown failure",query:=selected ("VALUES ?endpoint { <urn:missing> } "++service),error:=true},
  {name:="denied failure",query:=selected ("VALUES ?endpoint { <urn:one> } "++service),denied:=true,error:=true},
  {name:="denied SILENT",query:=selected ("VALUES ?endpoint { <urn:one> } SERVICE SILENT ?endpoint "++body),denied:=true,values:=["<unbound>"]},
  {name:="empty binder",query:=selected ("VALUES ?endpoint {} "++service)},
  {name:="nested SERVICE",query:=selected ("SERVICE <urn:outer> { VALUES ?endpoint { <urn:one> } "++service++" }"),values:=["one"]}
]

private def evaluate (backend : Bool) (c : Case) : Except String String := do
  let ds ← (readNQuadsText .rdf12 c.data).mapError fmtParseError
  let one ← (readNQuadsText .rdf12 "<urn:s> <urn:value> \"one\" .").mapError fmtParseError
  let two ← (readNQuadsText .rdf12 "<urn:s> <urn:value> \"two\" .").mapError fmtParseError
  let providers := if c.denied then [] else [("urn:one",one.default),("urn:two",two.default),("urn:outer",[])]
  return queryParsedDatasetWith ds (if backend then some (LawfulDataset.ofDataset ds) else none)
    c.query [] [] providers

private def answer (text : String) : Option (Bool × List String) := do
  let json ← parseJson? text
  if json.field? "ok" == some (.bool false) then return (false,[])
  if json.field? "ok" != some (.bool true) then none else do
    let result ← json.field? "srj"
    let results ← result.field? "results"
    let .array rows ← results.field? "bindings" | none
    let values := rows.map fun row =>
      match (row.field? "v").bind (fun value => value.field? "value") with
      | some (.string value) => value
      | _ => "<unbound>"
    return (true,values)

private def containsText (text needle : String) : Bool := (text.splitOn needle).length > 1

def run : IO Unit := do
  let failures ← IO.mkRef 0
  for c in cases do
    let reference ← match evaluate false c with | .ok r => pure r | .error e => throw (IO.userError e)
    let backend ← match evaluate true c with | .ok r => pure r | .error e => throw (IO.userError e)
    unless answer reference == some (!c.error,c.values) && (c.retained.isEmpty || containsText reference c.retained) do
      throw (IO.userError s!"reference positive/control expectation failed: {c.name}: {reference}")
    if answer backend != answer reference || (c.retained != "" && !containsText backend c.retained) then
      failures.modify (· + 1)
      IO.println s!"MISMATCH {c.name}: reference {reference}; backend {backend}"
  IO.println s!"Parsed SERVICE controls: {cases.length} reference cases, {cases.length-(← failures.get)} backend matches, {← failures.get} mismatches"
  unless (← failures.get) == 0 do throw (IO.userError "SERVICE backend/reference regression")

#eval run
end L4Wasm.Ops.ServiceVariableTests
