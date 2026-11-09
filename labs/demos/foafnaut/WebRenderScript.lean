import WebRender
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize
import L4Factoidal.WasmVM.Hosts.Dom

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

/-- The JSON form of a command of `WasmVM.Hosts.Dom.Command`, the typed commands of page
scripts (QuickJS in WasmVM, `WebScripts`). The keys of each form are exactly these. -/
def commandJson : L4Factoidal.WasmVM.Hosts.Dom.Command → JSON.Json
  | .setTextContent n v => .object [("op",.string "setTextContent"),("nodeId",num n),("value",.string v)]
  | .setAttribute n k v => .object [("op",.string "setAttribute"),("nodeId",num n),("name",.string k),("value",.string v)]
  | .createElement k n => .object [("op",.string "createElement"),("name",.string k),("nodeId",num n)]
  | .appendChild p c => .object [("op",.string "appendChild"),("parent",num p),("nodeId",num c)]
  | .removeAttribute n k => .object [("op",.string "removeAttribute"),("nodeId",num n),("name",.string k)]
  | .createNode k d n => .object [("op",.string "createNode"),("kind",num k),("data",.string d),("nodeId",num n)]
  | .createElementNS ns q n => .object [("op",.string "createElementNS"),("namespace",.string ns),("name",.string q),("nodeId",num n)]
  | .insertBefore p c b => .object [("op",.string "insertBefore"),("parent",num p),("nodeId",num c),
      ("before",match b with | some k => num k | none => .null)]
  | .removeChild p c => .object [("op",.string "removeChild"),("parent",num p),("nodeId",num c)]
  | .replaceChild p n c => .object [("op",.string "replaceChild"),("parent",num p),("nodeId",num n),("child",num c)]
  | .cloneNode n d r => .object [("op",.string "cloneNode"),("source",num n),("deep",.bool d),("nodeId",num r)]
  | .normalize n => .object [("op",.string "normalize"),("nodeId",num n)]
  | .setAttributeNS n ns q v => .object [("op",.string "setAttributeNS"),("nodeId",num n),("namespace",.string ns),("name",.string q),("value",.string v)]
  | .removeAttributeNS n ns l => .object [("op",.string "removeAttributeNS"),("nodeId",num n),("namespace",.string ns),("name",.string l)]
  | .adoptNode n doc => .object [("op",.string "adoptNode"),("nodeId",num n),("document",num doc)]
  | .importNode n doc deep r => .object [("op",.string "importNode"),("source",num n),("document",num doc),("deep",.bool deep),("nodeId",num r)]
  | .setChecked n v => .object [("op",.string "setChecked"),("nodeId",num n),("value",.bool v)]
  | .resetForm n => .object [("op",.string "resetForm"),("nodeId",num n)]
  | .replaceData n o k v => .object [("op",.string "replaceData"),("nodeId",num n),("offset",num o),("count",num k),("value",.string v)]
  | .splitText n o r => .object [("op",.string "splitText"),("source",num n),("offset",num o),("nodeId",num r)]
where num (n : Nat) : JSON.Json := .number (toString n)

private def commandOf (command : JSON.Json) : Except String L4Factoidal.WasmVM.Hosts.Dom.Command := do
  let .object fields := command | throw "script command: expected object"
  let keys := fields.map Prod.fst
  if keys.eraseDups.length != keys.length then throw "script command: duplicate key"
  let operation ← field command "op" >>= string
  let exactly := fun (names : List String) =>
    if keys.length == names.length + 1 && names.all keys.contains then Except.ok () else .error "script command: unexpected field"
  let node := fun (name : String) => field command name >>= nodeId
  let str := fun (name : String) => field command name >>= string
  let attrName := fun (name : String) => do
    let v ← str name
    if v.utf8ByteSize > 256 then throw "script command: attribute name exceeds bound"
    return v
  match operation with
  | "setTextContent" => exactly ["nodeId","value"]; return .setTextContent (← node "nodeId") (← str "value")
  | "setAttribute" => exactly ["nodeId","name","value"]; return .setAttribute (← node "nodeId") (← attrName "name") (← str "value")
  | "removeAttribute" => exactly ["nodeId","name"]; return .removeAttribute (← node "nodeId") (← attrName "name")
  | "createElement" => exactly ["name","nodeId"]; return .createElement (← attrName "name") (← node "nodeId")
  | "createElementNS" => exactly ["namespace","name","nodeId"]; return .createElementNS (← str "namespace") (← attrName "name") (← node "nodeId")
  | "setAttributeNS" => exactly ["nodeId","namespace","name","value"]; return .setAttributeNS (← node "nodeId") (← str "namespace") (← attrName "name") (← str "value")
  | "removeAttributeNS" => exactly ["nodeId","namespace","name"]; return .removeAttributeNS (← node "nodeId") (← str "namespace") (← attrName "name")
  | "setChecked" =>
    exactly ["nodeId","value"]
    let v ← match ← field command "value" with
      | .bool b => pure b
      | _ => throw "script command: value must be a boolean"
    return .setChecked (← node "nodeId") v
  | "resetForm" => exactly ["nodeId"]; return .resetForm (← node "nodeId")
  | "adoptNode" => exactly ["nodeId","document"]; return .adoptNode (← node "nodeId") (← node "document")
  | "importNode" =>
    exactly ["source","document","deep","nodeId"]
    let deep ← match ← field command "deep" with
      | .bool b => pure b
      | _ => throw "script command: deep must be a boolean"
    return .importNode (← node "source") (← node "document") deep (← node "nodeId")
  | "createNode" => exactly ["kind","data","nodeId"]; return .createNode (← node "kind") (← str "data") (← node "nodeId")
  | "appendChild" => exactly ["parent","nodeId"]; return .appendChild (← node "parent") (← node "nodeId")
  | "insertBefore" =>
    exactly ["parent","nodeId","before"]
    let before ← match ← field command "before" with
      | .null => pure none
      | other => some <$> nodeId other
    return .insertBefore (← node "parent") (← node "nodeId") before
  | "removeChild" => exactly ["parent","nodeId"]; return .removeChild (← node "parent") (← node "nodeId")
  | "replaceChild" => exactly ["parent","nodeId","child"]; return .replaceChild (← node "parent") (← node "nodeId") (← node "child")
  | "cloneNode" =>
    exactly ["source","deep","nodeId"]
    let deep ← match ← field command "deep" with
      | .bool b => pure b
      | _ => throw "script command: deep must be a boolean"
    return .cloneNode (← node "source") deep (← node "nodeId")
  | "normalize" => exactly ["nodeId"]; return .normalize (← node "nodeId")
  | "replaceData" =>
    exactly ["nodeId","offset","count","value"]
    return .replaceData (← node "nodeId") (← field command "offset" >>= nodeId) (← field command "count" >>= nodeId) (← str "value")
  | "splitText" => exactly ["source","offset","nodeId"]; return .splitText (← node "source") (← field command "offset" >>= nodeId) (← node "nodeId")
  | _ => throw "script command: unsupported operation"

/-- One command: its JSON form read, then the arena operation the script ran
(`WasmVM.Hosts.Dom.Command.apply`). -/
private def applyCommand (dom : DOM.Dom) (command : JSON.Json) : Except String DOM.Dom := do
  (← commandOf command).apply dom

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

/-- Only connected element handles are projected. Text is computed by Lean's
DOM textContent operation. Scripts remain inert until a host explicitly opts
in and submits their source to a separate engine. -/
def snapshot (dom : DOM.Dom) : JSON.Json := Id.run do
  let mut nodes : List JSON.Json := []
  for id in dom.treeOrder 0 do
    let node := dom.get id
    if node.type == .element then
      let attrs := node.attrs.toList.filter (fun attr => attr.ns.isNone)
      nodes := .object [
        ("id",.number (toString id)), ("tagName",.string node.lname),
        ("attributes",.object (attrs.map fun attr => (attr.qname,.string attr.value))),
        ("textContent",.string ((dom.textContent id).getD "")),
        -- The parent element, for the event path of DOM §2.9; null at the root element.
        ("parent",match node.parent with
          | some p => if (dom.get p).type == .element then .number (toString p) else .null
          | none => .null)] :: nodes
  return .object [("schema",.string "factoidal-script-dom-v1"),
    ("nodes",.array nodes.reverse),("scripts",.array (scriptRecords dom))]

def snapshotJSON (dom : DOM.Dom) : String := (snapshot dom).toString

/-! ### The page script setting

Which engine runs a page's classic scripts: BubblePopJS, the JavaScript engine written in
Lean (`L4Factoidal.JS`, run by `WasmVM.Hosts.LeanJS`), QuickJS-NG in WasmVM
(`WasmVM.Hosts.Page`), or none. The settings page links each choice
(`foafnaut:scripts/bubblepop`, `/quickjs`, `/none`, a `scripts` command of `WebShell.link`);
the host keeps the value in its browser state (`WebState.Settings.scripts`) and asks Lean
what it means (ops `scriptSetting`, `scriptPlan`, `scriptChoices`). VerifiedJS is not a
choice: it cannot run the script fixtures (issue 1252). -/

/-- The engines and their names, in the order of the settings page. -/
def engines : List (String × String) := [("bubblepop","BubblePopJS"),("quickjs","QuickJS-NG"),("none","None")]

/-- The chrome marker of an engine that runs a page's scripts. -/
def engineMarker (setting : String) : String :=
  if setting == "bubblepop" then "JS BUBBLEPOP" else if setting == "quickjs" then "JS QUICKJS-NG" else "JS " ++ setting.toUpper

/-- The default engine of a host. A native host (the window, `run_html.ts`) runs
BubblePopJS: Lean compiles it to native code, so it runs without a second interpreter. The
Hub runs QuickJS-NG: there the guest is translated to the browser's WebAssembly
(`WasmVM.Aot`), and runs faster than BubblePopJS compiled to WebAssembly. -/
def defaultEngine (host : String) : String := if host == "hub" || host == "wasm" then "quickjs" else "bubblepop"

def engineName (setting : String) : String := ((engines.find? (·.1 == setting)).map (·.2)).getD setting

/-- A setting from a link or a command (`foafnaut:scripts/bubblepop`, `:scripts none`). -/
def setting? (value : String) : Option String :=
  let key := value.trimAscii.toString.toLower
  let key := if key == "quickjs-ng" then "quickjs" else if key == "bubblepopjs" then "bubblepop" else key
  (engines.find? (·.1 == key)).map (·.1)

/-- What a page with `scripts` classic scripts does under `setting` on `host` (an empty
or unknown setting is the host's default). `unavailable` is the host's reason why the
engine can not start here, and `failure` the reason why a started engine stopped; either
makes a refusal that names the reason. `marker` is drawn in the chrome
(`WebShell.Shell.script`); `notice` is a line at the top of the page. -/
structure Plan where
  engine : String
  run : Bool
  marker : String
  notice : String
  deriving Repr, BEq

/-- Why an engine can not run on a host, or "". BubblePopJS does not run in the Wasm engine
yet (docs/designissues/2026-11-08-lean-js-engine.md, section 12). -/
def hostRefusal (setting host : String) : String :=
  if setting == "bubblepop" && (host == "hub" || host == "wasm") then
    "BubblePopJS does not run in the WebAssembly engine yet"
  else ""

def plan (setting : String) (scripts : Nat) (host : String := "native") (unavailable failure : String := "") : Plan :=
  let setting := (setting? setting).getD (defaultEngine host)
  let name := engineName setting
  let unavailable := if unavailable.isEmpty then hostRefusal setting host else unavailable
  if scripts == 0 then ⟨setting,false,"",""⟩
  else if setting == "none" then ⟨setting,false,"JS OFF",""⟩
  else if !failure.isEmpty then
    ⟨setting,false,"JS STOPPED",s!"Page scripts stopped ({name}): {failure}"⟩
  else if !unavailable.isEmpty then
    ⟨setting,false,"JS REFUSED",s!"Page scripts refused ({name}): {unavailable}"⟩
  else ⟨setting,true,engineMarker setting,""⟩

def Plan.json (p : Plan) : JSON.Json :=
  .object [("engine",.string p.engine),("name",.string (engineName p.engine)),("run",.bool p.run),
    ("marker",.string p.marker),("notice",.string p.notice)]

/-- The rows of the settings page for the setting: one large link for each engine, the
current one ticked (the boxes of the classic UI row). A host puts them in place of the
part of `settings.html` between the comments `foafnaut:scripts` and `/foafnaut:scripts`. -/
def choicesHTML (setting : String) (host : String := "native") : String :=
  let current := (setting? setting).getD (defaultEngine host)
  let row := fun (e : String × String) =>
    -- The chosen row's box is filled (`boxon`): an empty block inside the inline-block box is
    -- not painted yet (issue in showcase_gaps_test.ts), so the tick is the box's own colour.
    let box := if e.1 == current then "<span class=\"box boxon\"></span>" else "<span class=\"box\"></span>"
    let note := if e.1 == defaultEngine host then " (default here)"
      else if !(hostRefusal e.1 host).isEmpty then " (not here yet)" else ""
    s!"<p class=\"check\"><a href=\"foafnaut:scripts/{e.1}\">{box} {e.2}{note}</a></p>"
  String.join (engines.map row)

/-- A notice at the top of the body, as the page's first element. It is made after the
script commands, so it takes no node id that a script holds. -/
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
