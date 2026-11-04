import WebRender
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! Scripting boundary: Lean owns the arena, script discovery and mutations.
The separate QuickJS heap receives element handles and emits typed commands.
This is a bounded MVP binding, not a full WebIDL or DOM event implementation.
DOM semantics come from DOM.Arena, WHATWG DOM §4.4 and §4.9. -/
namespace WebRenderScript
open L4Factoidal

private def field (value : JSON.Json) (name : String) : Except String JSON.Json :=
  match value.field? name with
  | some result => .ok result
  | none => .error s!"script command: missing {name}"

private def string (value : JSON.Json) : Except String String := do
  let .string value := value | throw "script command: expected string"
  if value.utf8ByteSize > 65536 then throw "script command: string exceeds 64KiB"
  return value

private def nodeId (value : JSON.Json) : Except String Nat := do
  let .number raw := value | throw "script command: nodeId must be an integer"
  let some id := raw.toNat? | throw "script command: nodeId must be a natural integer"
  if id > 1048576 then throw "script command: nodeId exceeds bound"
  return id

private def applyCommand (dom : DOM.Dom) (command : JSON.Json) : Except String DOM.Dom := do
  let .object fields := command | throw "script command: expected object"
  let keys := fields.map Prod.fst
  if keys.eraseDups.length != keys.length then throw "script command: duplicate key"
  let operation ← field command "op" >>= string
  let id ← field command "nodeId" >>= nodeId
  let some node := dom.nodes[id]? | throw "script command: unknown nodeId"
  if node.type != .element then throw "script command: target must be an element"
  let value ← field command "value" >>= string
  if operation == "setTextContent" then
    if keys.length != 3 then throw "script command: unexpected field"
    return dom.setTextContent id value
  else if operation == "setAttribute" then
    if keys.length != 4 then throw "script command: unexpected field"
    let name ← field command "name" >>= string
    if name.utf8ByteSize > 256 then throw "script command: attribute name exceeds bound"
    let (updated,result) := dom.setAttribute id name value
    match result with
    | .ok () => return updated
    | .error error => throw s!"script command: {error.name}"
  else throw "script command: unsupported operation"

/-- A rejected batch returns no arena. Callers retain their old DOM. The MVP
replays the cumulative list over the original parsed document in each request.
Node IDs remain those of the arena; no host HTML source editing occurs. -/
def applyCommands (dom : DOM.Dom) (commands : JSON.Json) : Except String DOM.Dom := do
  let .array commands := commands | throw "script commands: expected array"
  if commands.length > 4096 then throw "script commands: maximum 4096 commands in history"
  let mut current := dom
  for command in commands do
    current ← applyCommand current command
    if current.size > 1048576 then throw "script commands: arena exceeds node budget"
  return current

private def attrValue (node : DOM.Node) (name : String) : String :=
  ((node.attrs.find? (fun attr => attr.ns.isNone && attr.lname == name)).map (·.value)).getD ""

private def scriptKind (node : DOM.Node) : String :=
  let kind := (attrValue node "type").trimAscii.toString.toLower
  if kind == "module" then "module"
  else if ["","text/javascript","application/javascript","text/ecmascript","application/ecmascript"].contains kind then "classic"
  else "data"

/-- Only connected element handles are projected. Text is computed by Lean's
DOM textContent operation. Scripts remain inert until a host explicitly opts
in and submits their source to a separate engine. -/
def snapshot (dom : DOM.Dom) : JSON.Json := Id.run do
  let mut nodes : List JSON.Json := []
  let mut scripts : List JSON.Json := []
  for id in dom.treeOrder 0 do
    let node := dom.get id
    if node.type == .element then
      let attrs := node.attrs.toList.filter (fun attr => attr.ns.isNone)
      nodes := .object [
        ("id",.number (toString id)), ("tagName",.string node.lname),
        ("attributes",.object (attrs.map fun attr => (attr.qname,.string attr.value))),
        ("textContent",.string ((dom.textContent id).getD ""))] :: nodes
      if DOM.Dom.isHtmlElement node "script" then
        scripts := .object [
          ("nodeId",.number (toString id)),
          ("source",.string ((dom.textContent id).getD "")),
          ("src",.string (attrValue node "src")),
          ("kind",.string (scriptKind node)),
          ("type",.string (attrValue node "type"))] :: scripts
  return .object [("schema",.string "factoidal-script-dom-v1"),
    ("nodes",.array nodes.reverse),("scripts",.array scripts.reverse)]

def snapshotJSON (dom : DOM.Dom) : String := (snapshot dom).toString
end WebRenderScript
