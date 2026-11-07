import WebRender
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! Scripting boundary: Lean owns the arena, script discovery and mutations.
The separate script engine heap receives element handles and emits typed commands.
This is a bounded binding, not a full WebIDL or DOM event implementation.
DOM semantics come from DOM.Arena, WHATWG DOM §4.2, §4.4, §4.5, §4.9 and §7.1,
and CSSOM §6.6 for the inline style declarations. Issue 1271. -/
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

private def element (dom : DOM.Dom) (id : Nat) : Except String DOM.Node := do
  let some node := dom.nodes[id]? | throw "script command: unknown nodeId"
  if node.type != .element then throw "script command: target must be an element"
  return node

private def domError (error : DOM.DomError) : String := s!"script command: {error.name}"

/-- The attribute name that `setAttribute` and `removeAttribute` use: lower case for an
HTML element of an HTML document (DOM §4.9, "get an attribute by name"). -/
def attributeName (dom : DOM.Dom) (id : Nat) (name : String) : String :=
  let node := dom.get id
  if node.ns == some DOM.htmlNS && (dom.get node.doc).htmlDoc then DOM.Dom.asciiLower name else name

/-- The value of the attribute with this qualified name, if any. -/
def attributeValue (dom : DOM.Dom) (id : Nat) (qname : String) : Option String :=
  ((dom.get id).attrs.find? (·.qname == qname)).map (·.value)

/-- `element.removeAttribute(qualifiedName)` (DOM §4.9). -/
def removeAttribute (dom : DOM.Dom) (id : Nat) (name : String) : DOM.Dom :=
  let qname := attributeName dom id name
  dom.setNode id fun n => {n with attrs := n.attrs.filter (·.qname != qname)}

private def setAttr (dom : DOM.Dom) (id : Nat) (name value : String) : Except String DOM.Dom :=
  let (updated,result) := dom.setAttribute id name value
  match result with
  | .ok () => .ok updated
  | .error error => .error (domError error)

/-- `textContent` setter. When the element has one child and it is a Text node, its
data changes in place. A script sees no Text node handles, so the result is the
same DOM tree as "string replace all" (DOM §4.4), and a repeated write does not
grow the arena: node ids that a script gets from `createElement` stay stable. -/
def setText (dom : DOM.Dom) (id : Nat) (value : String) : DOM.Dom :=
  match (dom.get id).kids.toList with
  | [kid] =>
    if (dom.get kid).type == .text && !value.isEmpty then dom.setNode kid fun n => {n with data := value}
    else dom.setTextContent id value
  | _ => dom.setTextContent id value

private def asciiSpace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'

/-- The ordered set of tokens of a DOMTokenList value (DOM §7.1, "ordered set parser"). -/
def tokens (value : String) : List String :=
  let split := (String.ofList (value.toList.map fun c => if asciiSpace c then ' ' else c)).splitOn " "
  split.foldl (fun out token => if token.isEmpty || out.contains token then out else out ++ [token]) []

/-- `classList.add`, `remove` and `toggle` of one token (DOM §7.1). The update
steps set the `class` attribute to the serialized ordered set. -/
def classList (dom : DOM.Dom) (id : Nat) (action token : String) : Except String DOM.Dom := do
  if token.isEmpty then throw "script command: SyntaxError"
  if token.toList.any asciiSpace then throw "script command: InvalidCharacterError"
  let current := tokens ((attributeValue dom id (attributeName dom id "class")).getD "")
  let next ← match action with
    | "add" => pure (if current.contains token then current else current ++ [token])
    | "remove" => pure (current.filter (· != token))
    | "toggle" => pure (if current.contains token then current.filter (· != token) else current ++ [token])
    | _ => throw "script command: unsupported classList action"
  setAttr dom id "class" (" ".intercalate next)

/-- The declarations of a `style` attribute as (property, value) pairs, in order. -/
def styleDeclarations (value : String) : List (String × String) :=
  (value.splitOn ";").filterMap fun item =>
    match item.splitOn ":" with
    | key::first::more =>
      let property := (key.trimAscii.toString).toLower
      if property.isEmpty then none else some (property,(":".intercalate (first::more)).trimAscii.toString)
    | _ => none

private def propertyName (name : String) : Bool :=
  !name.isEmpty && name.toList.all fun c => c.isAlphanum || c == '-'

/-- `style.setProperty(property, value)` and `style.x = value` (CSSOM §6.6.1): the
declaration is replaced in place, or appended; an empty value removes it. The result
is written back to the `style` attribute, which the cascade then reads. -/
def setStyleProperty (dom : DOM.Dom) (id : Nat) (property value : String) : Except String DOM.Dom := do
  let property := property.trimAscii.toString.toLower
  if !propertyName property || property.length > 128 then throw "script command: invalid style property"
  let value := value.trimAscii.toString
  if value.contains ';' || value.contains '{' || value.contains '}' then throw "script command: invalid style value"
  let qname := attributeName dom id "style"
  let current := styleDeclarations ((attributeValue dom id qname).getD "")
  let next := if value.isEmpty then current.filter (·.1 != property)
    else if current.any (·.1 == property) then current.map fun (k,v) => if k == property then (k,value) else (k,v)
    else current ++ [(property,value)]
  if next.isEmpty then return removeAttribute dom id "style"
  setAttr dom id "style" ("; ".intercalate (next.map fun (k,v) => k ++ ": " ++ v))

private def exactly (keys : List String) (expected : List String) : Except String Unit :=
  if keys.length == expected.length && expected.all keys.contains then .ok ()
  else .error "script command: unexpected field"

/-- One command. The fields of each operation are exact; a failed command changes
nothing that a caller keeps (see `applyCommands`). -/
def applyCommand (dom : DOM.Dom) (command : JSON.Json) : Except String DOM.Dom := do
  let .object fields := command | throw "script command: expected object"
  let keys := fields.map Prod.fst
  if keys.eraseDups.length != keys.length then throw "script command: duplicate key"
  let operation ← field command "op" >>= string
  let id ← field command "nodeId" >>= nodeId
  if operation == "createElement" then
    exactly keys ["op","nodeId","tagName","namespace"]
    if id != dom.size then throw s!"script command: createElement nodeId must be the next arena id {dom.size}"
    let tag ← field command "tagName" >>= string
    let space ← field command "namespace" >>= string
    if tag.utf8ByteSize > 256 then throw "script command: tag name exceeds bound"
    -- A template element makes two nodes, and a created script would never run.
    if ["template","script"].contains (DOM.Dom.asciiLower tag) then
      throw s!"script command: creating {tag} elements is outside this profile"
    if space == "html" then
      let (updated,result) := dom.createElement 0 tag
      match result with
      | .ok _ => return updated
      | .error error => throw (domError error)
    else if space == "svg" then
      if !DOM.Dom.validElementLocalName tag then throw "script command: InvalidCharacterError"
      return (dom.create {type := .element,doc := 0,ns := some DOM.svgNS,lname := tag}).1
    else throw "script command: namespace must be html or svg"
  let _ ← element dom id
  if operation == "setTextContent" then
    exactly keys ["op","nodeId","value"]
    return setText dom id (← field command "value" >>= string)
  else if operation == "setAttribute" then
    exactly keys ["op","nodeId","name","value"]
    let name ← field command "name" >>= string
    if name.utf8ByteSize > 256 then throw "script command: attribute name exceeds bound"
    setAttr dom id name (← field command "value" >>= string)
  else if operation == "removeAttribute" then
    exactly keys ["op","nodeId","name"]
    let name ← field command "name" >>= string
    if name.utf8ByteSize > 256 then throw "script command: attribute name exceeds bound"
    return removeAttribute dom id name
  else if operation == "appendChild" || operation == "removeChild" then
    exactly keys ["op","nodeId","child"]
    let child ← field command "child" >>= nodeId
    let _ ← element dom child
    let (updated,result) := if operation == "appendChild" then dom.appendChild id child else dom.preRemove child id
    match result with
    | .ok () => return updated
    | .error error => throw (domError error)
  else if operation == "classList" then
    exactly keys ["op","nodeId","action","token"]
    classList dom id (← field command "action" >>= string) (← field command "token" >>= string)
  else if operation == "setStyleProperty" then
    exactly keys ["op","nodeId","property","value"]
    setStyleProperty dom id (← field command "property" >>= string) (← field command "value" >>= string)
  else throw "script command: unsupported operation"

/-- A rejected batch returns no arena. Callers retain their old DOM. The host
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

/-! ### A shorter history with the same arena

An animation writes the same attributes on every frame, so the history grows past
its bound in a few seconds. `compact` drops a write that a later write replaces, and
keeps the result only when it replays to the same arena, node by node. -/

private def sameNode (a b : DOM.Node) : Bool :=
  a.type == b.type && a.doc == b.doc && a.ns == b.ns && a.pfx == b.pfx && a.lname == b.lname &&
    a.attrs == b.attrs && a.data == b.data && a.pubId == b.pubId && a.sysId == b.sysId &&
    a.parent == b.parent && a.kids == b.kids && a.host == b.host && a.content == b.content

/-- The two arenas are equal: the same nodes at the same ids. -/
def sameDom (a b : DOM.Dom) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => sameNode (a.get i) (b.get i)

private def number (n : Nat) : JSON.Json := .number (toString n)

/-- What a command leaves: the command in a form that does not read the arena
(an attribute write as its final value), the attribute it sets, and the element
whose text it sets without making a node. -/
private structure Step where
  command : JSON.Json
  written : Option (Nat × String) := none
  textOf : Option Nat := none

private def step (before after : DOM.Dom) (command : JSON.Json) : Step := Id.run do
  let op := match command.field? "op" with | some (.string s) => s | _ => ""
  let id := match command.field? "nodeId" with | some (.number n) => n.toNat?.getD 0 | _ => 0
  let named := match command.field? "name" with | some (.string s) => s | _ => ""
  let qname := if op == "classList" then attributeName before id "class"
    else if op == "setStyleProperty" then attributeName before id "style"
    else attributeName before id named
  if ["setAttribute","removeAttribute","classList","setStyleProperty"].contains op then
    let written := match attributeValue after id qname with
      | some value => JSON.Json.object [("op",.string "setAttribute"),("nodeId",number id),("name",.string qname),("value",.string value)]
      | none => .object [("op",.string "removeAttribute"),("nodeId",number id),("name",.string qname)]
    return {command := written,written := some (id,qname)}
  if op == "setTextContent" && after.size == before.size then return {command,textOf := some id}
  return {command}

/-- Drop each step that a later step of the same kind on the same target replaces. -/
private def supersede (steps : List Step) (texts : Bool) : List JSON.Json := Id.run do
  let mut attributes : List (Nat × String) := []
  let mut written : List Nat := []
  let mut kept : List JSON.Json := []
  for s in steps.reverse do
    match s.written with
    | some key =>
      if !attributes.contains key then kept := s.command :: kept
      attributes := key :: attributes
    | none =>
      match s.textOf with
      | some id =>
        if !(texts && written.contains id) then kept := s.command :: kept
        written := id :: written
      | none => kept := s.command :: kept
  return kept

/-- A history that replays to the same arena as `commands`, often much shorter. -/
def compact (dom : DOM.Dom) (commands : JSON.Json) : Except String JSON.Json := do
  let .array list := commands | throw "script commands: expected array"
  if list.length > 65536 then throw "script commands: too many to compact"
  let mut current := dom
  let mut steps : Array Step := #[]
  for command in list do
    let after ← applyCommand current command
    steps := steps.push (step current after command)
    current := after
  for texts in [true,false] do
    let candidate := supersede steps.toList texts
    if candidate.length <= 4096 then
      if let .ok replayed := applyCommands dom (.array candidate) then
        if sameDom replayed current then return .array candidate
  if list.length <= 4096 then return commands
  throw "script commands: history exceeds 4096 commands after compaction"

/-! ### Queries -/

/-- `querySelectorAll` (DOM §4.2.6) with the selectors of the engine's CSS profile
(type, id, class, the user action pseudo-classes and the descendant combinator),
matched by the same Lean matcher as the cascade. Elements after `scope` in tree
order, among its descendants. A list the profile can not read is a SyntaxError. -/
def query (dom : DOM.Dom) (scope : Nat) (selectors : String) : Except String (List Nat) := do
  if selectors.utf8ByteSize > 1024 then throw "SyntaxError: selector exceeds 1KiB"
  if selectors.contains '{' || selectors.contains '}' || selectors.trimAscii.isEmpty then throw "SyntaxError: invalid selector"
  let some node := dom.nodes[scope]? | throw "query: unknown scope"
  if node.type != .element && node.type != .document then throw "query: scope must be an element or the document"
  let rules ← Rendering.CSS.parse (selectors ++ "{}")
  let [rule] := rules | throw s!"SyntaxError: '{selectors}' is outside the selector profile"
  return (dom.treeOrder scope false).toList.filter fun id =>
    (dom.get id).type == .element && rule.selectors.any (Rendering.CSS.selectorMatches dom id ·)

/-! ### Discovery and the element projection -/

private def attrValue (node : DOM.Node) (name : String) : String :=
  ((node.attrs.find? (fun attr => attr.ns.isNone && attr.lname == name)).map (·.value)).getD ""

private def scriptKind (node : DOM.Node) : String :=
  let kind := (attrValue node "type").trimAscii.toString.toLower
  if kind == "module" then "module"
  else if ["","text/javascript","application/javascript","text/ecmascript","application/ecmascript"].contains kind then "classic"
  else "data"

/-- The script elements in tree order. A render needs these, not the whole snapshot. -/
def scriptRecords (dom : DOM.Dom) : List JSON.Json := Id.run do
  let mut scripts : List JSON.Json := []
  for id in dom.treeOrder 0 do
    let node := dom.get id
    if node.type == .element && DOM.Dom.isHtmlElement node "script" then
      scripts := .object [
        ("nodeId",.number (toString id)),
        ("source",.string ((dom.textContent id).getD "")),
        ("src",.string (attrValue node "src")),
        ("kind",.string (scriptKind node)),
        ("type",.string (attrValue node "type"))] :: scripts
  return scripts.reverse

private def projection (dom : DOM.Dom) (id : Nat) : JSON.Json :=
  let node := dom.get id
  let attrs := node.attrs.toList.filter (fun attr => attr.ns.isNone)
  let parent := match node.parent with
    | some p => if (dom.get p).type == .element then number p else .null
    | none => .null
  .object [
    ("id",number id),("tagName",.string node.lname),
    ("namespace",.string (if node.ns == some DOM.svgNS then "svg" else "html")),
    ("parent",parent),
    ("attributes",.object (attrs.map fun attr => (attr.qname,.string attr.value))),
    ("textContent",.string ((dom.textContent id).getD ""))]

/-- Only connected element handles are projected. Text is computed by Lean's
DOM textContent operation. `next` is the id that the next created node gets.
Scripts remain inert until a host explicitly opts in and submits their source
to a separate engine. -/
def snapshot (dom : DOM.Dom) : JSON.Json := Id.run do
  let mut nodes : List JSON.Json := []
  for id in dom.treeOrder 0 do
    if (dom.get id).type == .element then nodes := projection dom id :: nodes
  return .object [("schema",.string "factoidal-script-dom-v2"),
    ("nodes",.array nodes.reverse),("next",number dom.size),("scripts",.array (scriptRecords dom))]

def snapshotJSON (dom : DOM.Dom) : String := (snapshot dom).toString

/-! ### The page script setting (issue 1271)

Owner, 2026-11-07: "A switch in the settings to chose none/VerifiedJS/TheOtherOneJS".
The host keeps the setting; Lean says what it means for a page. -/

/-- The setting values and their names. The first engine is the default. -/
def engines : List (String × String) := [("quickjs","QuickJS-NG"),("verifiedjs","VerifiedJS"),("none","None")]
def defaultEngine : String := "quickjs"

def engineName (setting : String) : String := ((engines.find? (·.1 == setting)).map (·.2)).getD setting

/-- A setting from a link or a command (`foafnaut:scripts/quickjs`, `:scripts none`). -/
def setting? (value : String) : Option String :=
  let key := value.trimAscii.toString.toLower
  let key := if key == "quickjs-ng" then "quickjs" else key
  (engines.find? (·.1 == key)).map (·.1)

/-- What a page with `scripts` classic scripts does under `setting`. `unavailable` is
the host's reason why the engine can not start here, and `failure` the reason why a
started engine stopped; either makes a refusal that names the reason.
`marker` is drawn in the chrome; `notice` is put at the top of the page. -/
structure Plan where
  engine : String
  run : Bool
  marker : String
  notice : String
  deriving Repr, BEq

def plan (setting : String) (scripts : Nat) (unavailable failure : String := "") : Plan :=
  let setting := (setting? setting).getD defaultEngine
  let name := engineName setting
  if scripts == 0 then ⟨setting,false,"",""⟩
  else if setting == "none" then ⟨setting,false,"JS OFF",""⟩
  else if !failure.isEmpty then
    ⟨setting,false,"JS STOPPED",s!"Page scripts stopped ({name}): {failure}"⟩
  else if !unavailable.isEmpty then
    ⟨setting,false,"JS REFUSED",s!"Page scripts refused ({name}): {unavailable}"⟩
  else ⟨setting,true,"JS " ++ name.toUpper,""⟩

def Plan.json (p : Plan) : JSON.Json :=
  .object [("engine",.string p.engine),("name",.string (engineName p.engine)),("run",.bool p.run),
    ("marker",.string p.marker),("notice",.string p.notice)]

/-- A notice at the top of the body, as the page's first element. It is made after the
script commands, so it takes no id that a script holds. -/
def withNotice (dom : DOM.Dom) (notice : String) : DOM.Dom := Id.run do
  if notice.isEmpty then return dom
  let some body := (dom.treeOrder 0).toList.find? (fun id => DOM.Dom.isHtmlElement (dom.get id) "body") | return dom
  let (d,result) := dom.createElement 0 "p"
  let .ok p := result | return dom
  let (d,_) := d.setAttribute p "style"
    "margin:0 0 8px 0;padding:6px 8px;background:#fff3cd;color:#5c3c00;border:1px solid #c89b2c;font-size:13px;line-height:18px"
  let d := d.setTextContent p (String.ofList (notice.toList.take 512))
  let (d,_) := d.insertBefore body p (d.get body).kids[0]?
  return d
end WebRenderScript
