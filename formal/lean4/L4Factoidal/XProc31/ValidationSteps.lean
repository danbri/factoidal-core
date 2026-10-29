import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Loading

namespace L4Factoidal.XProc31
open XML

def supportsValidation (name : String) : Bool := name == "validate-with-dtd"

/-- Document serialization properties take precedence for DTD revalidation. -/
def dtdSerialization (step : Node) (env : XPath4.Env) (source : Document) : Result XPath4.Seq := do
  let [.map supplied] ← typedOption step "serialization" env "map{}" | error "XD0036" "serialization must be a map"
  let stored := match documentProperty source ⟨"", "serialization", ""⟩ with
    | [.map entries] => entries
    | _ => []
  let normalize : List (XPath4.Atomic × XPath4.Seq) → List (XPath4.Atomic × XPath4.Seq) := fun entries => entries.map fun (key,value) =>
    ((match key.v with | .qn q => if q.uri == "" then XPath4.Atomic.ofStr q.loc else key | _ => key), value)
  let stored := normalize stored
  let supplied := normalize supplied
  pure [.map (stored ++ supplied.filter (fun (key,_) => !stored.any (fun (other,_) => key.str == other.str)))]

def dtdReport (issues : List (String × String)) (baseUri : String) : Document :=
  let detections := issues.map fun (code,message) =>
    XML.Node.element "xvrl:detection" [⟨"severity", "error"⟩, ⟨"code", code⟩] [.element "xvrl:message" [] [.text message]]
  {node := .element "xvrl:report" [⟨"xmlns:xvrl", "http://www.xproc.org/ns/xvrl"⟩] detections, baseUri}

/-- Serialize and reparse so external declarations, default attributes and
attribute normalization use the shared XML parser. Validation uses its DTD. -/
def revalidateDtd (source : Document) (serialized : String) : IO (Result (Document × List (String × String))) := do
  let resources ← match ← preloadDocumentResources 256 [(source.baseUri,serialized)] [] with
    | .ok resources => pure resources
    | .error e => if e.unsupported then return .error e else return .ok (source, [(e.code,e.message)])
  let resolve : XML.Resolver := fun identifier => (resources.find? (·.systemId == identifier)).map (·.text)
  match XML.parseDecodedXMLWith resolve serialized with
  | .error e => return .ok (source, [("XML",toString e)])
  | .ok parsed =>
    if parsed.doctype.any (·.incomplete) then return unsupported "DTD parameter entity declarations are incomplete"
    let violations := XML.validate parsed
    let nodes := parsed.children
    let node := match nodes with | [node] => node | nodes => .element "#document" [] nodes
    return .ok ({source with node, value := none}, violations.map (fun violation => (violation.vc,violation.message)))

def validationPorts (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : IO (Result (List (String × List Document))) := do
  if !supportsValidation (tag step) then return unsupported ("validation step " ++ tag step)
  let prepared : Result (Document × String × Bool) := do
    let source ← oneSource ((ports.lookup "source").getD [])
    let kind ← classifyMediaType source.contentType
    if kind != MediaKind.xml then return ← error "XD0038" "DTD validation requires an XML document"
    let options ← dtdSerialization step env source
    let content := (documentNodes source).filter (fun n => match n with
      | .text text | .cdata text => !text.trimAscii.toString.isEmpty
      | _ => true)
    let node := match content with | [root] => root | nodes => .element "#document" [] nodes
    let e := xpathEnv (some {source with node, value := none}) env.vars env.ns
    let params ← fromXPath (XPath4.serParamsOf e options)
    let serialized ← fromXPath (e.serializeWith params (e.ctx.getD []))
    let assertValid := (← option step "assert-valid" env "true") != "false"
    pure (source, serialized, assertValid)
  let .ok (source,serialized,assertValid) := prepared | return prepared.map (fun _ => [])
  let checked ← revalidateDtd source serialized
  let .ok (result,issues) := checked | return checked.map (fun _ => [])
  if assertValid && !issues.isEmpty then
    return error "XC0210" (String.intercalate "; " (issues.map (·.2)))
  return .ok [("result",[result]), ("report",[dtdReport issues env.baseUri])]

def validationStep (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : IO (Result (List Document)) := do
  return (← validationPorts step ports env).map (fun ports => (ports.lookup "result").getD [])

/-- Validate actual declarations and exercise default attribute normalization,
then reject an invalid child and surface its diagnostic report. -/
def validationStepsRegression : IO Bool := IO.FS.withTempDir fun root => do
  let dtd := root / "schema.dtd"
  IO.FS.writeFile dtd "<!ELEMENT doc (child)><!ATTLIST doc status CDATA 'default'><!ELEMENT child EMPTY>"
  let base := "file://" ++ root.toString ++ "/source.xml"
  let source : Document := {node := .element "doc" [] [.element "child" [] []], baseUri := base}
  let step := XML.Node.element "p:validate-with-dtd" [⟨"serialization", "map{'doctype-system':'schema.dtd'}"⟩] []
  let result ← validationPorts step [("source",[source])] {baseUri := base}
  let .ok result := result | return false
  let some [doc] := result.lookup "result" | return false
  if attr doc.node "status" != "default" then return false
  let some [report] := result.lookup "report" | return false
  if !(kids report.node).isEmpty then return false
  let invalid := {source with node := .element "doc" [] [.element "wrong" [] []]}
  let failure ← validationPorts step [("source",[invalid])] {baseUri := base}
  if failure.toBool then return false
  let permissive := XML.Node.element "p:validate-with-dtd" (⟨"assert-valid", "false"⟩ :: step.elementAttrs) []
  let .ok reports ← validationPorts permissive [("source",[invalid])] {baseUri := base} | return false
  let some [report] := reports.lookup "report" | return false
  return !(kids report.node).isEmpty

end L4Factoidal.XProc31
