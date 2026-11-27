import L4Factoidal.WasmVM.Hosts.LeanJS
import L4Factoidal.DOM.OfXml
import L4Factoidal.DOM.XmlSerialize
import L4Factoidal.JSON.Serialize
import L4Factoidal.WHATWG.URL.Parser

/-!
# SVGScript: the scripts of an SVG Tiny 1.2 document, run before it is drawn

SVG Tiny 1.2 chapter 15 (scripting) and the XML Events attributes it uses (§15.3, §15.4).
The document is read into a DOM arena (`DOM.parseXmlDocument`). BubblePopJS runs its
`script` elements in document order on that arena, in a page session
(`WasmVM.Hosts.LeanJS`); every DOM effect is a typed command of the arena. Each `handler`
element, and each XML Events `listener` element, becomes an event listener on its observer.
Then the `load` events are dispatched. The arena after this is serialized again as XML
(`DOM.XmlSerialize`), without the `script`, `handler` and `listener` elements, which are not
rendered (§15.2: "the script element is never rendered"; §15.4 for `handler`), and that
markup is what the SVG reader draws.

Lean decides here: which scripts run (their content type, §15.2 and `contentScriptType`,
§5.1.2), their order, the observer and the options of each listener (XML Events 1.0 §3.1:
`event`, `observer`, `target`, `handler`, `phase`, `propagate`, `defaultAction`), which
events are dispatched and where. The host gives only the bytes of an external script
(`fetch`).

A `script` or `handler` whose type is not ECMAScript is not run (§15.2: a user agent does
not execute a script in a language it does not support); it is still not drawn.

Refusals (each names the element and the reason): an
external script whose text the host did not give, a `listener` whose `handler` is not a local
`handler` element, an uncaught error in a script or a handler. A document with none of these
elements is returned unchanged by `run`.
-/

namespace NativeSVGScript
open L4Factoidal
open L4Factoidal.DOM
open L4Factoidal.WasmVM.Hosts

def xmlEventsNS : String := "http://www.w3.org/2001/xml-events"

/-- The ECMAScript content types (RFC 4329 §3 and §7; SVG Tiny 1.2 §15.2 names
`application/ecmascript`), compared without parameters and case. -/
def ecmascriptTypes : List String :=
  ["application/ecmascript","text/ecmascript","application/javascript","text/javascript"]

def lower (s : String) : String := s.trimAscii.toString.toLower

/-- An attribute in no namespace. -/
def attrNo (n : Node) (name : String) : Option String :=
  (n.attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

/-- An attribute in namespace `ns`. -/
def attrIn (n : Node) (ns name : String) : Option String :=
  (n.attrs.find? fun a => a.ns == some ns && a.lname == name).map (·.value)

def isSvg (n : Node) (name : String) : Bool :=
  n.type == .element && n.ns == some svgNS && n.lname == name

/-- The elements this module runs and then leaves out of the drawing. -/
def isScripting (n : Node) : Bool :=
  isSvg n "script" || isSvg n "handler" || (n.type == .element && n.ns == some xmlEventsNS && n.lname == "listener")

/-- The root element of the document. -/
def rootOf (d : Dom) : Option NodeId :=
  (d.get 0).kids.find? fun k => (d.get k).type == .element

/-- §15.2 and §5.1.2: the type of a `script` or `handler` is its `type` attribute, else the
root's `contentScriptType`, else `application/ecmascript`. Parameters (`;...`) are not part
of the comparison. -/
def scriptType (d : Dom) (n : Node) : String :=
  let root := ((rootOf d).map d.get)
  let dflt := (root.bind (attrNo · "contentScriptType")).getD "application/ecmascript"
  let t := (attrNo n "type").getD dflt
  lower ((t.splitOn ";").headD "")

def isEcmascript (t : String) : Bool := ecmascriptTypes.contains t

/-- The `xlink:href` of a `script` (SVG Tiny 1.2 §15.2), or SVG 2's `href`. -/
def scriptHref (n : Node) : Option String :=
  match attrNo n "href" with
  | some h => if h.trimAscii.isEmpty then none else some h
  | none => (attrIn n xlinkNS "href").bind fun h => if h.trimAscii.isEmpty then none else some h

/-- The element with an ID: `xml:id` (SVG Tiny 1.2 §5.10.2) or `id`. -/
def byId (d : Dom) (id : String) : Option NodeId :=
  (d.treeOrder 0).find? fun k =>
    let n := d.get k
    n.type == .element && (attrIn n xmlNS "id" == some id || attrNo n "id" == some id)

/-- One step of the start, in document order. -/
inductive Step where
  /-- Run a classic script: the element, its text. -/
  | script (node : NodeId) (source : String)
  /-- Add a listener: the observer, the event type, the capture flag, the target filter, stop
  propagation, cancel the default action, the handler's text. -/
  | listen (observer : NodeId) (event : String) (capture : Bool) (target : Option NodeId)
      (stop cancel : Bool) (source : String)
  deriving Repr, Inhabited

/-- XML Events 1.0 §3.1 for a `handler` with `ev:event` (its parent is the observer, SVG Tiny
1.2 §15.4) or for a `listener`. -/
def listenStep (d : Dom) (owner : Node) (observer : NodeId) (event : String) (source : String) :
    Except String Step := do
  let phase := (attrIn owner xmlEventsNS "phase" <|> attrNo owner "phase").map lower
  let capture ← match phase with
    | none | some "default" => pure false
    | some "capture" => pure true
    | some p => throw s!"{owner.lname}: phase {p} unsupported"
  let target ← match attrIn owner xmlEventsNS "target" <|> attrNo owner "target" with
    | none => pure none
    | some t => match byId d t.trimAscii.toString with
      | some k => pure (some k)
      | none => throw s!"{owner.lname}: target {t} not found"
  let stop := ((attrIn owner xmlEventsNS "propagate" <|> attrNo owner "propagate").map lower) == some "stop"
  let cancel := ((attrIn owner xmlEventsNS "defaultAction" <|> attrNo owner "defaultAction").map lower) == some "cancel"
  pure (.listen observer event.trimAscii.toString capture target stop cancel source)

/-- The steps of a document, in tree order: its scripts and its listeners. `fetch` gives the
text of an external script by its reference (as written; the host resolves it against the
document). -/
def plan (d : Dom) (fetch : String → Option String) : Except String (Array Step) := do
  let mut out : Array Step := #[]
  for k in d.treeOrder 0 do
    let n := d.get k
    if isSvg n "script" then
      -- §15.2: a script in a language the user agent does not run is not executed
      if !isEcmascript (scriptType d n) then continue
      match scriptHref n with
      | some href =>
        match fetch href with
        | some src => out := out.push (.script k src)
        | none => throw s!"external script not loaded: {href}"
      | none => out := out.push (.script k ((d.textContent k).getD ""))
    else if isSvg n "handler" then
      if !isEcmascript (scriptType d n) then continue
      if scriptHref n |>.isSome then throw "handler: external handler text unsupported"
      -- a handler with no `ev:event` is run only by a `listener` that names it
      if let some ev := attrIn n xmlEventsNS "event" then
        let some parent := n.parent | throw "handler: no parent"
        out := out.push (← listenStep d n parent ev ((d.textContent k).getD ""))
    else if n.type == .element && n.ns == some xmlEventsNS && n.lname == "listener" then
      let some ev := attrIn n xmlEventsNS "event" <|> attrNo n "event" | throw "listener: no event"
      let observer ← match attrIn n xmlEventsNS "observer" <|> attrNo n "observer" with
        | some o => match byId d o.trimAscii.toString with
          | some k => pure k
          | none => throw s!"listener: observer {o} not found"
        | none => match n.parent with
          | some p => pure p
          | none => throw "listener: no parent"
      let some href := attrIn n xmlEventsNS "handler" <|> attrNo n "handler" | throw "listener: no handler"
      let href := href.trimAscii.toString
      if !href.startsWith "#" then throw s!"listener: handler {href} is not in this document"
      let some h := byId d (href.drop 1).toString | throw s!"listener: handler {href} not found"
      let hn := d.get h
      if !isSvg hn "handler" then throw s!"listener: {href} is not a handler element"
      if !isEcmascript (scriptType d hn) then continue
      out := out.push (← listenStep d n observer ev ((d.textContent h).getD ""))
  return out

def jsString (s : String) : String := "\"" ++ JSON.escapeString s ++ "\""

/-- The script that adds a listener, run with the observer as the current script, so that
`document.currentScript` is the observer. The handler's text is the body of a function of
`evt` (SVG Tiny 1.2 §15.4: "the event object ... is available as `evt`"). The target filter,
`propagate="stop"` and `defaultAction="cancel"` are decided here and written as code. -/
def listenSource (event : String) (capture : Bool) (target : Option NodeId) (stop cancel : Bool)
    (source : String) : String :=
  let pre := (if stop then "evt.stopPropagation();" else "") ++ (if cancel then "evt.preventDefault();" else "")
  let guard := match target with
    | some _ => "if (evt.target !== __svgTarget) return;"
    | none => ""
  "(function(){var __svgObserver=document.currentScript;" ++
  (match target with | some _ => "var __svgTarget=document.__svgTargetNode;" | none => "") ++
  "__svgObserver.addEventListener(" ++ jsString event ++ ",function(evt){" ++ guard ++ pre ++
  "\n" ++ source ++ "\n}," ++ (if capture then "true" else "false") ++ ");})();"

/-- The elements of the arena in post-order (children before their parent; siblings in
document order): the order in which SVG 1.1 §18.4 dispatches `SVGLoad`, "at the point at
which the user agent has fully parsed the element and its descendants". -/
def postOrder (d : Dom) (root : NodeId) : Array NodeId := Id.run do
  -- an explicit stack of (node, children done): a loop, not one frame per node
  let mut stack : List (NodeId × Bool) := [(root, false)]
  let mut out : Array NodeId := #[]
  for _ in [0:2 * d.size + 2] do
    match stack with
    | [] => break
    | (k, true) :: rest => out := out.push k; stack := rest
    | (k, false) :: rest =>
      let kids := (d.get k).kids.toList.filter fun c => (d.get c).type == .element
      stack := kids.map (·, false) ++ (k, true) :: rest
  return out

/-- An attribute that a script made with a colon in its name and no namespace
(`setAttribute("v:crispness", ...)`, DOM §4.9: the qualified name is the local name). It is
an unknown attribute in no namespace, so it does not change the rendering; XML with
namespaces can not write it (Namespaces in XML 1.0 §7: a colon in a name starts a prefix). -/
def unwritableAttr (a : Attr) : Bool := a.ns.isNone && a.lname.contains ':'

/-- The arena with the `script`, `handler` and `listener` elements taken out of their
parents' children (they are not rendered), and without the attributes of `unwritableAttr`;
the arena is otherwise the same. -/
def withoutScripting (d : Dom) : Dom := Id.run do
  let mut out := d
  for k in d.treeOrder 0 do
    let n := d.get k
    if n.kids.any fun c => isScripting (d.get c) then
      out := out.setNode k fun m => { m with kids := m.kids.filter fun c => !isScripting (d.get c) }
    if n.attrs.any unwritableAttr then
      out := out.setNode k fun m => { m with attrs := m.attrs.filter fun a => !unwritableAttr a }
  return out

/-- Run the scripts of `d` on the realm `base` (`LeanJS.prepareSource`). The arena after the
start, or the first error. -/
def runDom (base : LeanJS.Session) (d : Dom) (url : String) (fetch : String → Option String) : Except String Dom := do
  let steps ← plan d fetch
  if steps.isEmpty then return d
  let mut s := LeanJS.startBegin base d url
  for st in steps do
    match st with
    | .script node src => s := LeanJS.startScript s node src
    | .listen observer event capture target stop cancel src =>
      if let some t := target then
        -- the target is passed through the current script too: set it, read it into a slot
        s := (s.api? "script" #[.num (Float.ofNat t)]).1
        s := s.eval "document.__svgTargetNode=document.currentScript;"
      s := (s.api? "script" #[.num (Float.ofNat observer)]).1
      s := LeanJS.engine.checkpoint (s.eval (listenSource event capture target stop cancel src))
  s := (s.api? "script" #[.num (-1)]).1
  -- SVG 1.1 §18.4 `SVGLoad` at each element after its descendants; SVG Tiny 1.2 §13.3 `load`
  -- at the root element (the name of the same event in Tiny 1.2), then the window's events.
  if let some root := rootOf s.host.dom.dom then
    for k in postOrder s.host.dom.dom root do
      s := (LeanJS.engine.dispatch s k "SVGLoad").1
    s := (LeanJS.engine.dispatch s root "load").1
  s := LeanJS.startFinish s
  if let some e := s.errors[0]? then throw s!"script error: {e}"
  return s.host.dom.dom

/-- The document `source` after its scripts, as XML markup without the scripting elements;
the source itself when it has no `script`, `handler` or `listener` element. -/
def run (base : LeanJS.Session) (source : String) (url : String := "about:svg")
    (fetch : String → Option String := fun _ => none) : Except String String := do
  let d ← parseXmlDocument source
  if !(d.treeOrder 0).any (fun k => isScripting (d.get k)) then return source
  let d' ← runDom base d url fetch
  return XmlSerialize.serializeChildren (withoutScripting d') 0

/-- The external scripts of `source` (SVG Tiny 1.2 §15.2 `xlink:href` on `script`): each
reference as written and its URL resolved against `documentURL` (URL Standard basic URL
parser). The host reads only these URLs, by its own resource policy. -/
def scriptRequests (source documentURL : String) : List (String × String) :=
  match parseXmlDocument source with
  | .error _ => []
  | .ok d => (d.treeOrder 0).toList.filterMap fun k =>
    let n := d.get k
    if isSvg n "script" then
      (scriptHref n).bind fun h =>
        (L4Factoidal.WHATWG.URL.parseUrl h.trimAscii.toString (some documentURL)).map fun u => (h, u.href)
    else none

/-- Whether `source` has any element that `run` acts on. -/
def hasScripting (source : String) : Bool :=
  match parseXmlDocument source with
  | .ok d => (d.treeOrder 0).any fun k => isScripting (d.get k)
  | .error _ => false

end NativeSVGScript
