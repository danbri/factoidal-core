import L4Factoidal.XProc31.Core
import L4Factoidal.XProc31.MediaTypes
import L4Factoidal.EXPath.Binary.Lib

namespace L4Factoidal.XProc31

def binaryDocument (bytes : ByteArray) (contentType : String := "application/octet-stream")
    (baseUri : String := "") (properties : List (XPath4.Atomic × XPath4.Seq) := []) : Document :=
  {node := .element "#document" [] [], contentType, baseUri, properties, value := some (EXPath.Binary.b64 (bytes.toList.map UInt8.toNat))}

def binaryBytes (document : Document) : Option ByteArray := do
  let value ← document.value
  let bytes ← EXPath.Binary.binArg value
  pure ⟨(bytes.map UInt8.ofNat).toArray⟩

def serializationEntries (values : XPath4.Seq) : Result (List (XPath4.Atomic × XPath4.Seq)) := do
  let [.map entries] := values | error "XD0036" "serialization must be a map"
  pure (entries.map fun (key,value) =>
    ((match key.v with | .qn q => if q.uri == "" then XPath4.Atomic.ofStr q.loc else key | _ => key),value))

/-- Serialize actual XDM content at an octet boundary; binary values are already
bytes and must never be serialized as a base64 lexical string. -/
def documentBytes (document : Document) (serialization : XPath4.Seq := [.map []])
    (env : XPath4.Env := {}) : Result ByteArray := do
  if let some bytes := binaryBytes document then return bytes
  let supplied ← serializationEntries serialization
  let stored ← match documentProperty document ⟨"", "serialization", ""⟩ with
    | [] => pure []
    | values => serializationEntries values
  let entries := supplied ++ stored.filter (fun (key,_) => !supplied.any (fun (other,_) => key.str == other.str))
  let kind ← classifyMediaType document.contentType
  if kind == .binary then return ← error "XD0038" "binary document has no octet payload"
  let context := { (xpathEnv (some document) env.vars env.ns) with resources := env.resources, resourceBytes := env.resourceBytes }
  let params ← fromXPath (XPath4.serParamsOf context [.map entries])
  let defaultMethod := match kind with | .text => "text" | .json => "json" | .html => "html" | _ => "xml"
  let params := if entries.any (fun (key,_) => key.str == "method") then params else {params with method := defaultMethod}
  let serialized ← fromXPath (context.serializeWith params (context.ctx.getD []))
  let some encoding := EXPath.Binary.encOfName? params.encoding | unsupported ("serialization encoding " ++ params.encoding)
  let some bytes := EXPath.Binary.encodeWith encoding serialized | error "SERE0008" "serialized characters cannot be represented in the requested encoding"
  pure ⟨(bytes.map UInt8.ofNat).toArray⟩

#guard (binaryBytes (binaryDocument ⟨#[0,128,255]⟩)).map (·.toList) == some [0,128,255]
#guard (documentBytes {node := .text "<raw>", contentType := "text/plain"}).toOption.map (·.toList) == some "<raw>".toUTF8.toList
#guard (documentBytes (binaryDocument ⟨#[0,128,255]⟩)).toOption.map (·.toList) == some [0,128,255]
end L4Factoidal.XProc31
