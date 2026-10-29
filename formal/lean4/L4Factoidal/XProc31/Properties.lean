import L4Factoidal.XProc31.MediaTypes
import L4Factoidal.XProc31.Functions
import L4Factoidal.RDF.IriSyntax

namespace L4Factoidal.XProc31

def propertyQName (env : XPath4.Env) (key : XPath4.Atomic) : Result XPath4.QN :=
  match functionQName {ns := env.ns.filter (fun p => p.1 != "")} [.atom key] with
  | .ok q => pure q
  | .error _ => error "XD0070" "document property key must be a QName"

def normalizedProperties (env : XPath4.Env) (values : XPath4.Seq) : Result (List (XPath4.Atomic × XPath4.Seq)) := do
  let [.map entries] := values | error "XD0070" "document properties must be a map"
  entries.mapM fun (key,value) => do
    let q ← propertyQName env key
    let value ← if q == ⟨"", "serialization", ""⟩ then do
      let [.map parameters] := value | error "XD0070" "serialization property must be a map"
      let parameters ← parameters.mapM fun (key,v) => do
        pure (XPath4.Atomic.ofQN (← propertyQName env key), retainItems env 256 v)
      pure [.map parameters]
      else pure (retainItems env 256 value)
    pure (XPath4.Atomic.ofQN q,value)

/-- Property maps retain XPath values, including nested maps, arrays and nodes. -/
def updateProperties (env : XPath4.Env) (d : Document) (values : XPath4.Seq)
    (merge : Bool := true) (contentTypeError : String := "XD0062") : Result Document := do
  let entries ← normalizedProperties env values
  let mut result := if merge then d else {d with baseUri := "", properties := []}
  for (key,value) in entries do
    let q := (propertyName key).getD ⟨"", "", ""⟩
    if q == ⟨"", "base-uri", ""⟩ then
      let [.atom a] := value | error "XD0064" "base-uri must be one absolute URI"
      if !RDF.isAbsoluteIri a.str then return ← error "XD0064" "base-uri must be an absolute URI"
      result := {result with baseUri := a.str}
    else if q == ⟨"", "content-type", ""⟩ then
      let [.atom a] := value | error "XD0079" "content-type must be one media type"
      let _ ← parseMediaType a.str
      if a.str != d.contentType then return ← error contentTypeError "content-type property conflicts with document content type"
    else
      result := {result with properties := (key,value) :: result.properties.filter (fun (k,_) => propertyName k != some q)}
  pure result

#guard match updateProperties {} {node := .text "", baseUri := "file:///old"}
    [.map [(XPath4.Atomic.ofStr "custom", [.map [(XPath4.Atomic.ofStr "x", XPath4.sInt 7)]])]] false with
  | .ok d => d.baseUri == "" && (documentProperty d ⟨"", "custom", ""⟩).length == 1 && (documentProperties d).length == 2
  | _ => false
#guard match updateProperties {} {node := .text ""}
    [.map [(XPath4.Atomic.ofStr "base-uri", XPath4.sStr "relative")]] with
  | .error e => e.code == "XD0064" | _ => false
#guard match updateProperties {} {node := .text "", properties := [(XPath4.Atomic.ofQN ⟨"urn:test", "keep", "t"⟩, XPath4.sInt 9)]}
    [.map [(XPath4.Atomic.ofStr "serialization", [.map [(XPath4.Atomic.ofStr "indent", XPath4.sBool true)]])]] with
  | .ok d => (documentProperty d ⟨"urn:test", "keep", ""⟩).length == 1 &&
    (match documentProperty d ⟨"", "serialization", ""⟩ with
      | [.map [(k,_)]] => propertyName k == some ⟨"", "indent", ""⟩
      | _ => false)
  | _ => false
#guard match updateProperties {} {node := .text ""}
    [.map [(XPath4.Atomic.ofStr "serialization", XPath4.sStr "invalid")]] with
  | .error e => e.code == "XD0070" | _ => false
#guard match updateProperties {} {node := .text ""}
    [.map [(XPath4.Atomic.ofStr "content-type", XPath4.sStr "text/plain")]] true "XC0069" with
  | .error e => e.code == "XC0069" | _ => false
end L4Factoidal.XProc31
