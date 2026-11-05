import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Loading
import L4Factoidal.Codec.Archive

namespace L4Factoidal.XProc31

def supportsCompression (name : String) : Bool := ["compress", "uncompress"].contains name

def compressionStep (step : XML.Node) (ports : List (String × List Document))
    (env : XPath4.Env) : IO (Result (List Document)) := do
  let prepared : Result (Document × String × XPath4.Seq × String) := do
    let source ← oneSource ((ports.lookup "source").getD [])
    let format ← option step "format" env "gzip"
    if format != "gzip" then return ← error "XC0202" ("unsupported compression format " ++ format)
    let parameters ← typedOption step "parameters" env "map{}"
    match parameters with
    | [.map []] => pure ()
    | [.map _] => return ← unsupported "compression parameters"
    | _ => return ← error "XD0036" "compression parameters must be a map"
    let serialization ← typedOption step "serialization" env "map{}"
    let contentType ← option step "content-type" env "application/octet-stream"
    if tag step == "uncompress" then let _ ← parseMediaType contentType; pure ()
    pure (source,format,serialization,contentType)
  let .ok (source,_,serialization,contentType) := prepared | return prepared.map (fun _ => [])
  let properties := source.properties.filter (fun (key,_) => propertyName key != some ⟨"", "serialization", ""⟩)
  if tag step == "compress" then
    let bytes := documentBytes source serialization env
    return bytes.map (fun bytes => [binaryDocument (Codec.gzip bytes) "application/gzip" source.baseUri properties])
  else if tag step == "uncompress" then
    let some bytes := binaryBytes source | return error "XC0202" "compressed input is not a binary document"
    let .ok expanded := Codec.gunzip bytes | return error "XC0202" "input is not a valid gzip stream"
    match ← decodedDocument expanded contentType source.baseUri with
    | .error e => return if e.unsupported then .error e else .error {e with code := "XC0201"}
    | .ok result => return .ok [{result with properties}]
  else return unsupported ("compression step " ++ tag step)

def compressionStepsRegression : IO Bool := do
  let source : Document := {node := .element "doc" [] [.text "binary roundtrip"], baseUri := "file:///roundtrip.xml", properties := [(XPath4.Atomic.ofQN ⟨"", "custom", ""⟩, XPath4.sInt 42)]}
  let .ok [compressed] ← compressionStep (.element "p:compress" [] []) [("source",[source])] {} | return false
  if compressed.contentType != "application/gzip" || (binaryBytes compressed).isNone then return false
  let .ok [expanded] ← compressionStep (.element "p:uncompress" [⟨"content-type", "application/xml"⟩] []) [("source",[compressed])] {} | return false
  if expanded.node.textContent != "binary roundtrip" || expanded.baseUri != source.baseUri then return false
  if (documentProperty expanded ⟨"", "custom", ""⟩).isEmpty then return false
  let corrupt := binaryDocument ⟨#[0,1,2]⟩ "application/gzip"
  match ← compressionStep (.element "p:uncompress" [] []) [("source",[corrupt])] {} with
  | .error e => return e.code == "XC0202"
  | .ok _ => return false
end L4Factoidal.XProc31
