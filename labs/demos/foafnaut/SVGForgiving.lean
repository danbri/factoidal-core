import SVG

/- Forgiving front door for the strict SVG reader.

   The strict reader in SVG.lean refuses any document it can not fully draw.
   A browser must instead draw what it can. This pass removes what the strict
   reader refuses, and it records each removal. The reader itself is unchanged,
   so each thing it learns to draw leaves this log with no change here.

   `dropped` is the to-do list. A scene made here is a partial rendering. It
   makes no claim of SVG conformance. -/
namespace NativeSVGForgiving

open L4Factoidal.XML

private def svgURI := "http://www.w3.org/2000/svg"
private def xmlURI := "http://www.w3.org/XML/1998/namespace"
/-- XML nesting limit of this pass; the strict reader stops at 32 groups. -/
private def maxDepth : Nat := 64
/-- Strict parses allowed for one document. Each one is a full reader run. -/
private def maxParses : Nat := 4000

/-- Elements the strict reader reads. Any other element is removed and logged. -/
private def readable := ["svg","g","use","symbol","defs","style","metadata","title","desc",
  "rect","circle","ellipse","line","polygon","polyline","path"]
/-- Elements that paint nothing: their content needs no reader support. -/
private def silent := ["title","desc","metadata"]

private def isSpace (s : String) : Bool :=
  s.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')

/-- `xml:id` is an ID (XML ID 1.0); the strict reader reads only `id`. -/
private def renameId (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.map fun a =>
    if a.name.namespace_ == some xmlURI && a.name.localPart == "id"
    then {a with name:={namespace_:=none,localPart:="id"}} else a

/-- Remove foreign and unread elements, stray text and the content of silent
    elements. Returns the new tree and one log line for each removal. -/
private def normalise : Nat → Bool → NamespaceNode → Option NamespaceNode × List String
  | 0,_,_ => (none,["element: nesting exceeds 64"])
  | _,_,.other (.comment c) => (some (.other (.comment c)),[])
  | _,keepText,.other raw => match raw with
    | .text t | .cdata t =>
      if keepText || isSpace t then (some (.other raw),[]) else (none,["text outside a text element"])
    | _ => (none,["processing instruction"])
  | fuel+1,_,.element name attrs children =>
    if name.namespace_ != some svgURI then (none,["foreign element: " ++ name.localPart])
    else if !readable.contains name.localPart then (none,["element: " ++ name.localPart])
    else if silent.contains name.localPart then (some (.element name (renameId attrs) []),[])
    else
      let keepText := name.localPart == "style"
      let results := children.map (normalise fuel keepText)
      (some (.element name (renameId attrs) (results.filterMap (·.1))),results.flatMap (·.2))

private def stripAttr (tag : String) (key : String) : Nat → NamespaceNode → NamespaceNode × Nat
  | 0,node => (node,0)
  | _,.other raw => (.other raw,0)
  | fuel+1,.element name attrs children =>
    let kept := if name.localPart == tag then attrs.filter (fun a => a.name.localPart != key) else attrs
    let results := children.map (stripAttr tag key fuel)
    (.element name kept (results.map (·.1)),
      attrs.length-kept.length + (results.map (·.2)).foldl (·+·) 0)

/-- Element paths, deepest first, so a removal takes the least possible. -/
private def elementPaths : Nat → List Nat → NamespaceNode → List (List Nat)
  | 0,_,_ => []
  | _,_,.other _ => []
  | fuel+1,path,.element _ _ children =>
    (children.zipIdx.flatMap fun (child,index) => elementPaths fuel (path++[index]) child) ++ [path]

private def removeAt : Nat → List Nat → NamespaceNode → NamespaceNode
  | 0,_,node => node
  | _,[],node => node
  | _,_,.other raw => .other raw
  | fuel+1,[index],.element name attrs children =>
    let _ := fuel
    .element name attrs (children.eraseIdx index)
  | fuel+1,index::rest,.element name attrs children =>
    .element name attrs (children.zipIdx.map fun (child,i) =>
      if i == index then removeAt fuel rest child else child)

private def nodeAt : Nat → List Nat → NamespaceNode → Option NamespaceNode
  | _,[],node => some node
  | 0,_,_ => none
  | _,_,.other _ => none
  | fuel+1,index::rest,.element _ _ children => do
    nodeAt fuel rest (← children[index]?)

private def tagName : NamespaceNode → String
  | .element name _ _ => name.localPart
  | _ => "node"

/-- `unsupported attribute on TAG: KEY`, with or without "qualified". -/
private def attributeError (message : String) : Option (String × String) :=
  let tail := if message.startsWith "unsupported attribute on "
    then some (message.drop 25).toString
    else if message.startsWith "qualified attribute unsupported on "
    then some (message.drop 35).toString else none
  tail.bind fun tail => match tail.splitOn ": " with
    | [tag,key] => some (tag,key)
    | _ => none

private structure Attempt where
  root : NamespaceNode
  dropped : List String
  parses : Nat

/-- Remove the deepest element whose removal changes the reader's first error.
    The reader stops at its first error, so an element that does not cause it
    can not change it, except by a reference to the element that does. -/
private def removeOffender (width height : Nat) (message : String) (a : Attempt) :
    Option Attempt := Id.run do
  let mut parses := a.parses
  for path in elementPaths maxDepth [] a.root do
    if path.isEmpty then continue
    if parses >= maxParses then return none
    parses := parses + 1
    let next := removeAt maxDepth path a.root
    let changed := match NativeSVG.parseRoot next width height with
      | .ok _ => true
      | .error other => other != message
    if changed then
      let tag := ((nodeAt maxDepth path a.root).map tagName).getD "node"
      return some {root:=next,parses,dropped:=a.dropped ++ [s!"removed {tag}: {message}"]}
  return none

private def repair (width height : Nat) : Nat → Attempt → Except String (NativeSVG.Scene × List String)
  | 0,_ => throw "forgiving pass exceeded its repair limit"
  | fuel+1,a =>
    match NativeSVG.parseRoot a.root width height with
    | .ok scene => pure (scene,a.dropped)
    | .error message =>
      let stripped := (attributeError message).bind fun (tag,key) =>
        let (root,count) := stripAttr tag key maxDepth a.root
        if count == 0 then none
        else some {a with root,parses:=a.parses+1,dropped:=a.dropped ++ List.replicate count s!"attribute: {tag} {key}"}
      match stripped.orElse (fun _ => removeOffender width height message a) with
      | some next => repair width height fuel next
      | none => throw message

/-- The `version` label names a language edition; it does not change drawing. -/
private def rootAttrs (root : NamespaceNode) : NamespaceNode × List String :=
  match root with
  | .element name attrs children =>
    let kept := attrs.filter fun a => !(a.name.namespace_.isNone && ["version","baseProfile"].contains a.name.localPart)
    (.element name kept children,(attrs.filter (fun a => !kept.any (fun k => k.name == a.name))).map
      (fun a => "attribute: svg " ++ a.name.localPart))
  | node => (node,[])

/-- Parse as a browser would: draw what the strict reader can draw. A document
    that is not well-formed XML stays an error. -/
def parse (xml : String) (width height : Nat) : Except String (NativeSVG.Scene × List String) := do
  if xml.length > NativeSVG.maxInputChars then throw "SVG input exceeds 1048576 characters"
  let root ← parseNamespaceView xml
  let (root,rootLog) := rootAttrs root
  let (some root,log) := normalise maxDepth false root | throw "root element is not read"
  repair width height 1024 {root,dropped:=rootLog ++ log,parses:=0}

end NativeSVGForgiving
