/-
L4Factoidal.DOM.Arena — the node tree of the WHATWG DOM Standard as an arena.

Specification: DOM Living Standard, whatwg/dom commit `3c53f93a` (main on
2026-11-01): §4.2 "Node tree" (the mutation algorithms of §4.2.3), §4.4
"Interface Node", §4.5 "Interface Document" (the create methods), §4.9
"Interface Element" (`setAttribute`), §4.10 to §4.14 (`DocumentFragment`,
`CharacterData`, `Text`, `CDATASection`, `ProcessingInstruction`, `Comment`).
HTML Living Standard (whatwg/html `93967771`) §4.12.3 for the template
contents of a `template` element and its cloning steps.

The arena is an array of `Node` records. A node is its index (`NodeId`). Indexes
are never reused: a removed node stays in the arena, without a parent, so that a
handle to it stays valid (as a JavaScript reference to a removed node does). A
node keeps its parent and its ordered list of children; the sibling links of
the standard are derived from the list. The design record is
`docs/designissues/2026-11-01-dom-arena.md`.

Every operation is a total function `Dom → Dom × Except DomError α` (`Res α`)
or `Dom → Dom`. Walks up the tree are bounded by the arena size; walks down the
tree are loops with an explicit work list, not one stack frame per node.

Implemented: the node types Document, DocumentType, DocumentFragment, Element,
Text, CDATASection, Comment and ProcessingInstruction; ensure pre-insert
validity, pre-insert, insert, append, replace, replace all, pre-remove, remove,
adopt (one document per arena in the tests), and move (`moveBefore`, without a
shadow tree); `textContent` (get and set), `normalize`, `cloneNode`,
`isEqualNode`, `contains`, `getElementById`; `createElement` (no custom
elements), `createTextNode`, `createComment`, `createCDATASection`,
`createProcessingInstruction`, `createDocumentFragment`, `createDocumentType`;
`setAttribute`; the
template contents fragment of an HTML `template` element (its host is the
element, so the host-including inclusive ancestor rule applies).

Not implemented, tracked in https://github.com/danbri/factoidal/issues/1216
(the DOM features after the first implementation): shadow trees and slots, live
ranges, `NodeIterator`, mutation observers, events, custom elements, the
namespace methods (`createElementNS`, `setAttributeNS`), `Attr` nodes, the
adopting steps of `template` across documents, and the insertion, removing and
moving steps of other specifications. Tests: `tests/dom/run.sh`.
-/
import L4Factoidal.XML.Document

namespace L4Factoidal.DOM

/-- The node types of DOM §4.4 (`nodeType`), without `Attr` nodes. -/
inductive NodeType where
  | document | doctype | fragment | element | text | cdata | comment | pi
deriving BEq, DecidableEq, Inhabited, Repr

/-- `nodeType` values of DOM §4.4. -/
def NodeType.code : NodeType → Nat
  | .element => 1 | .text => 3 | .cdata => 4 | .pi => 7 | .comment => 8
  | .document => 9 | .doctype => 10 | .fragment => 11

def htmlNS : String := "http://www.w3.org/1999/xhtml"
def svgNS : String := "http://www.w3.org/2000/svg"
def mathmlNS : String := "http://www.w3.org/1998/Math/MathML"
def xlinkNS : String := "http://www.w3.org/1999/xlink"
def xmlNS : String := "http://www.w3.org/XML/1998/namespace"
def xmlnsNS : String := "http://www.w3.org/2000/xmlns/"

/-- An attribute (DOM §4.9.2): namespace, namespace prefix, local name, value. -/
structure Attr where
  ns : Option String := none
  pfx : Option String := none
  lname : String
  value : String
deriving BEq, Inhabited, Repr

/-- The qualified name of an attribute (DOM §4.9.2). -/
def Attr.qname (a : Attr) : String :=
  match a.pfx with
  | some p => p ++ ":" ++ a.lname
  | none => a.lname

abbrev NodeId := Nat

/-- One node of the arena. Fields that a node type does not have keep their
default. `lname` is the local name of an element, the name of a doctype and
the target of a processing instruction. -/
structure Node where
  type : NodeType := .element
  /-- The node document (DOM §4.4). For a document, its own index. -/
  doc : NodeId := 0
  ns : Option String := none
  pfx : Option String := none
  lname : String := ""
  attrs : Array Attr := #[]
  /-- The data of a CharacterData node. -/
  data : String := ""
  pubId : String := ""
  sysId : String := ""
  parent : Option NodeId := none
  kids : Array NodeId := #[]
  /-- The host of a DocumentFragment (DOM §4.7): the `template` element whose
  template contents it is. -/
  host : Option NodeId := none
  /-- The template contents of an HTML `template` element (HTML §4.12.3). -/
  content : Option NodeId := none
  /-- A document's type (DOM §4.5): `true` for "html", `false` for "xml". -/
  htmlDoc : Bool := true
  /-- A document's content type (DOM §4.5); "" is the default of its type, "text/html"
  or "application/xml". -/
  contentType : String := ""
deriving Inhabited, Repr

structure Dom where
  nodes : Array Node := #[]
deriving Inhabited

/-- The names of `DOMException` (WebIDL §2.8.1) that these algorithms throw. -/
inductive DomError where
  | hierarchyRequest | notFound | invalidCharacter | notSupported | namespace
deriving BEq, DecidableEq, Inhabited, Repr

def DomError.name : DomError → String
  | .hierarchyRequest => "HierarchyRequestError"
  | .notFound => "NotFoundError"
  | .invalidCharacter => "InvalidCharacterError"
  | .notSupported => "NotSupportedError"
  | .namespace => "NamespaceError"

/-- The result of an operation that can throw: the arena after it (the same
arena when it throws) and the value or the exception. The arena is given back
in both cases, so a caller never keeps the old arena alive while an operation
changes it; `Array.modify` then changes it in place. -/
abbrev Res (α : Type) := Dom × Except DomError α

namespace Dom

def get (d : Dom) (i : NodeId) : Node := d.nodes.getD i default
def setNode (d : Dom) (i : NodeId) (f : Node → Node) : Dom := { nodes := d.nodes.modify i f }
def size (d : Dom) : Nat := d.nodes.size

/-- Append a node to the arena; its index is the old size. The size is read
before the push: read after it, the array is shared during the push and
copied (the same fault as `newNode` of the HTML tree builder, design record
`2026-10-29-html-parser.md` § Speed). -/
def push (d : Dom) (n : Node) : Dom × NodeId :=
  let i := d.nodes.size
  ({ nodes := d.nodes.push n }, i)

def isCharacterData (n : Node) : Bool := n.type == .text || n.type == .cdata || n.type == .comment || n.type == .pi
/-- A `Text` node (DOM §4.11): `CDATASection` inherits from `Text`. -/
def isTextNode (n : Node) : Bool := n.type == .text || n.type == .cdata
def isHtmlElement (n : Node) (nm : String) : Bool :=
  n.type == .element && n.ns == some htmlNS && n.lname == nm

def children (d : Dom) (p : NodeId) : Array NodeId := (d.get p).kids

/-- The index of `c` among its parent's children (DOM §4.2.1). -/
def index (d : Dom) (c : NodeId) : Option Nat :=
  match (d.get c).parent with
  | none => none
  | some p => (d.get p).kids.findIdx? (· == c)

def nextSibling (d : Dom) (c : NodeId) : Option NodeId :=
  match (d.get c).parent, d.index c with
  | some p, some i => (d.get p).kids[i + 1]?
  | _, _ => none

def previousSibling (d : Dom) (c : NodeId) : Option NodeId :=
  match (d.get c).parent, d.index c with
  | some p, some (i + 1) => (d.get p).kids[i]?
  | _, _ => none

/-- The walk up from `cur` over at most `fuel` parents: `true` when it meets
`a`. Tail-recursive. -/
def ancestorWalk (d : Dom) (a : NodeId) : Nat → NodeId → Bool
  | 0, _ => false
  | f + 1, cur =>
    if cur == a then true
    else match (d.get cur).parent with
      | some p => d.ancestorWalk a f p
      | none => false

/-- `a` is an inclusive ancestor of `n` (DOM §4.2.1). The walk up is bounded
by the arena size; a well-formed arena has no cycle. -/
def isInclusiveAncestor (d : Dom) (a n : NodeId) : Bool := d.ancestorWalk a (d.size + 1) n

/-- The walk up from `cur` over parents, and from a root with a host to that
host, over at most `fuel` steps: `true` when it meets `a`. Tail-recursive. -/
def hostWalk (d : Dom) (a : NodeId) : Nat → NodeId → Bool
  | 0, _ => false
  | f + 1, cur =>
    if cur == a then true
    else
      let c := d.get cur
      match c.parent with
      | some p => d.hostWalk a f p
      | none =>
        match c.host with
        | some h => d.hostWalk a f h
        | none => false

/-- `a` is a host-including inclusive ancestor of `n` (DOM §4.2.2): an
inclusive ancestor of `n`, or a host-including inclusive ancestor of the host
of the root of `n`. One walk: up the parents, and from a root with a host to
that host. -/
def isHostIncludingInclusiveAncestor (d : Dom) (a n : NodeId) : Bool := d.hostWalk a (2 * d.size + 2) n

/-- The root of `n` (DOM §4.2.1). -/
def root (d : Dom) (n : NodeId) : NodeId := Id.run do
  let mut cur := n
  for _ in [0:d.size + 1] do
    match (d.get cur).parent with
    | some p => cur := p
    | none => return cur
  return cur

/-- The shadow-including root (DOM §4.8). With no shadow trees it is the root. -/
def shadowIncludingRoot (d : Dom) (n : NodeId) : NodeId := d.root n

/-- The descendants of `n` in tree order (DOM §4.2.1), `n` first when
`inclusive`. Template contents are not children, so they are not visited. -/
def treeOrder (d : Dom) (n : NodeId) (inclusive : Bool := true) : Array NodeId := Id.run do
  let mut out : Array NodeId := #[]
  let mut work : List NodeId := if inclusive then [n] else (d.get n).kids.toList
  for _ in [0:d.size + 1] do
    match work with
    | [] => break
    | x :: rest =>
      out := out.push x
      work := (d.get x).kids.toList ++ rest
  return out

def hasElementChildExcept (d : Dom) (p : NodeId) (excl : List NodeId) : Bool :=
  (d.get p).kids.any fun c => (d.get c).type == .element && !excl.contains c

def hasDoctypeChildExcept (d : Dom) (p : NodeId) (excl : List NodeId) : Bool :=
  (d.get p).kids.any fun c => (d.get c).type == .doctype && !excl.contains c

/-- A doctype is following `child` among its siblings. -/
def doctypeFollowing (d : Dom) (p child : NodeId) : Bool :=
  let ks := (d.get p).kids
  match ks.findIdx? (· == child) with
  | some i => (ks.extract (i + 1) ks.size).any fun c => (d.get c).type == .doctype
  | none => false

/-- An element is preceding `child` among its siblings. -/
def elementPreceding (d : Dom) (p child : NodeId) : Bool :=
  let ks := (d.get p).kids
  match ks.findIdx? (· == child) with
  | some i => (ks.extract 0 i).any fun c => (d.get c).type == .element
  | none => false

/-! ## Mutation algorithms (DOM §4.2.3) -/

/-- "Ensure pre-insert validity" of `node` into `parent` before `child`,
excluding `excl` (DOM §4.2.3), step by step. -/
def ensurePreInsertValidity (d : Dom) (node parent : NodeId) (child : Option NodeId)
    (excl : List NodeId) : Except DomError Unit := do
  let p := d.get parent
  let n := d.get node
  -- 1
  if !(p.type == .document || p.type == .fragment || p.type == .element) then
    throw .hierarchyRequest
  -- 2
  if d.isHostIncludingInclusiveAncestor node parent then throw .hierarchyRequest
  -- 3
  if let some c := child then
    if (d.get c).parent != some parent then throw .notFound
  -- 4
  if !(n.type == .fragment || n.type == .doctype || n.type == .element || isCharacterData n) then
    throw .hierarchyRequest
  -- 5
  if p.type != .document then
    if n.type == .doctype then throw .hierarchyRequest
    return ()
  -- 6
  if isTextNode n then throw .hierarchyRequest
  -- 7
  if isCharacterData n then return ()
  -- 8
  if n.type == .fragment then
    let elems := n.kids.filter fun k => (d.get k).type == .element
    if elems.size > 1 || n.kids.any (fun k => isTextNode (d.get k)) then throw .hierarchyRequest
    if elems.size == 0 then return ()
  -- 9
  if n.type == .fragment || n.type == .element then
    let childIsDoctype := match child with
      | some c => (d.get c).type == .doctype && !excl.contains c
      | none => false
    let docAfter := match child with
      | some c => d.doctypeFollowing parent c
      | none => false
    if d.hasElementChildExcept parent excl || docAfter || childIsDoctype then
      throw .hierarchyRequest
    return ()
  -- 10, 11: `node` is a doctype
  let elemBefore := match child with
    | some c => d.elementPreceding parent c
    | none => d.hasElementChildExcept parent excl
  if d.hasDoctypeChildExcept parent excl || elemBefore then throw .hierarchyRequest

/-- "Remove" (DOM §4.2.3) without the checks of `preRemove`: take `node` out of
its parent's children. Observers, ranges and removing steps do not exist here. -/
def remove (d : Dom) (node : NodeId) : Dom :=
  match (d.get node).parent with
  | none => d
  | some p =>
    let d1 := d.setNode p fun pn => { pn with kids := pn.kids.filter (· != node) }
    d1.setNode node fun n => { n with parent := none }

/-- Set the node document of `node` and its inclusive descendants, and of the
template contents below them. -/
def setNodeDocument (d : Dom) (node : NodeId) (doc : NodeId) : Dom := Id.run do
  let mut d := d
  let mut work : List NodeId := [node]
  for _ in [0:d.size + 1] do
    match work with
    | [] => break
    | x :: rest =>
      d := d.setNode x fun n => { n with doc }
      let n := d.get x
      work := n.kids.toList ++ (match n.content with | some c => [c] | none => []) ++ rest
  return d

/-- "Adopt" `node` into `doc` (DOM §4.5): remove it from its parent, then set
the node document of its subtree. -/
def adopt (d : Dom) (node doc : NodeId) : Dom :=
  let d := if (d.get node).parent.isSome then d.remove node else d
  if (d.get node).doc == doc then d else d.setNodeDocument node doc

/-- Put `c` into the children of `p`, before `before` or at the end. -/
def linkChild (d : Dom) (p c : NodeId) (before : Option NodeId) : Dom :=
  let d1 := d.setNode p fun pn =>
    -- the child array is taken out of the node first, so it is not shared
    -- while it changes
    let ks := pn.kids
    let pn := { pn with kids := #[] }
    let kids := match before with
      | none => ks.push c
      | some b => match ks.findIdx? (· == b) with
        | some k => ks.insertIdxIfInBounds k c
        | none => ks.push c
    { pn with kids }
  d1.setNode c fun n => { n with parent := some p }

/-- "Insert" `node` into `parent` before `child` (DOM §4.2.3). A
DocumentFragment gives its children, in tree order. -/
def insert (d : Dom) (node parent : NodeId) (child : Option NodeId) : Dom := Id.run do
  let n := d.get node
  let nodes := if n.type == .fragment then n.kids else #[node]
  if nodes.size == 0 then return d
  let mut d := d
  if n.type == .fragment then
    for k in nodes do d := d.remove k
  let doc := (d.get parent).doc
  for k in nodes do
    d := d.adopt k doc
    d := d.linkChild parent k child
  return d

/-- "Pre-insert" (DOM §4.2.3). The inserted node is `node`. -/
def preInsert (d : Dom) (node parent : NodeId) (child : Option NodeId) : Res Unit :=
  match d.ensurePreInsertValidity node parent child [] with
  | .error e => (d, .error e)
  | .ok () =>
    let ref := if child == some node then d.nextSibling node else child
    (d.insert node parent ref, .ok ())

/-- `parent.appendChild(node)` (DOM §4.4). -/
def appendChild (d : Dom) (parent node : NodeId) : Res Unit := d.preInsert node parent none

/-- `parent.insertBefore(node, child)` (DOM §4.4). -/
def insertBefore (d : Dom) (parent node : NodeId) (child : Option NodeId) : Res Unit :=
  d.preInsert node parent child

/-- "Replace" `child` with `node` within `parent` (DOM §4.2.3);
`parent.replaceChild(node, child)`. -/
def replace (d : Dom) (child node parent : NodeId) : Res Unit :=
  match d.ensurePreInsertValidity node parent (some child) [child] with
  | .error e => (d, .error e)
  | .ok () =>
    let ref0 := d.nextSibling child
    let ref := if ref0 == some node then d.nextSibling node else ref0
    let doc := (d.get parent).doc
    let d := d.adopt node doc
    let d := if (d.get child).parent.isSome then d.remove child else d
    (d.insert node parent ref, .ok ())

/-- "Replace all" with `node` within `parent` (DOM §4.2.3). -/
def replaceAll (d : Dom) (node : Option NodeId) (parent : NodeId) : Dom := Id.run do
  let mut d := d
  for k in (d.get parent).kids do d := d.remove k
  match node with
  | some n => d.insert n parent none
  | none => d

/-- "Pre-remove" (DOM §4.2.3); `parent.removeChild(child)`. -/
def preRemove (d : Dom) (child parent : NodeId) : Res Unit :=
  if (d.get child).parent != some parent then (d, .error .notFound) else (d.remove child, .ok ())

/-- `node.remove()` (DOM §4.2.8, ChildNode). -/
def removeSelf (d : Dom) (node : NodeId) : Dom :=
  if (d.get node).parent.isNone then d else d.remove node

/-- The checks of "move" (DOM §4.2.3), steps 1 to 7. -/
def moveCheck (d : Dom) (node newParent : NodeId) (child : Option NodeId) : Except DomError Unit := do
  let np := d.get newParent
  let n := d.get node
  if d.shadowIncludingRoot newParent != d.shadowIncludingRoot node then throw .hierarchyRequest
  if d.isHostIncludingInclusiveAncestor node newParent then throw .hierarchyRequest
  if let some c := child then
    if (d.get c).parent != some newParent then throw .notFound
  if !(n.type == .element || isCharacterData n) then throw .hierarchyRequest
  if isTextNode n && np.type == .document then throw .hierarchyRequest
  if np.type == .document && n.type == .element then
    let childDoctype := match child with
      | some c => (d.get c).type == .doctype
      | none => false
    let docAfter := match child with
      | some c => d.doctypeFollowing newParent c
      | none => false
    if d.hasElementChildExcept newParent [] || childDoctype || docAfter then throw .hierarchyRequest
  if n.parent.isNone then throw .hierarchyRequest

/-- "Move" `node` into `newParent` before `child` (DOM §4.2.3);
`newParent.moveBefore(node, child)` (DOM §4.2.6). Without shadow trees the
shadow-including root is the root. -/
def move (d : Dom) (node newParent : NodeId) (child : Option NodeId) : Res Unit :=
  match d.moveCheck node newParent child with
  | .error e => (d, .error e)
  | .ok () =>
    -- `moveBefore` (§4.2.6) passes `child` unchanged when it is `node`: the
    -- reference child is then the node's next sibling, as in pre-insert.
    let ref := if child == some node then d.nextSibling node else child
    let d := d.remove node
    (d.linkChild newParent node ref, .ok ())

/-! ## Node creation (DOM §4.5) -/

def isAsciiAlpha (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'
def isAsciiWhitespace (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

/-- "Valid element local name" (DOM §1.4 "Namespaces"). -/
def validElementLocalName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | c :: rest =>
    if isAsciiAlpha c then
      !(name.toList.any fun x => isAsciiWhitespace x || x == '\x00' || x == '/' || x == '>')
    else if !(c == ':' || c == '_' || c.toNat ≥ 0x80) then false
    else rest.all fun x => isAsciiAlpha x || isAsciiDigit x || x == '-' || x == '.' ||
      x == ':' || x == '_' || x.toNat ≥ 0x80

/-- "Valid attribute local name" (DOM §1.4). -/
def validAttributeLocalName (name : String) : Bool :=
  !name.isEmpty && !(name.toList.any fun x =>
    isAsciiWhitespace x || x == '\x00' || x == '/' || x == '=' || x == '>')

def asciiLower (s : String) : String :=
  s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- A new node of `doc`. An HTML `template` element gets its template contents,
a DocumentFragment whose host is the element (HTML §4.12.3). -/
def create (d : Dom) (n : Node) : Dom × NodeId :=
  let (d, id) := d.push n
  if isHtmlElement n "template" then
    let (d, c) := d.push { type := .fragment, doc := n.doc, host := some id }
    (d.setNode id fun e => { e with content := some c }, id)
  else (d, id)

/-- `document.createElement(localName)` (DOM §4.5), with no custom elements. -/
def createElement (d : Dom) (doc : NodeId) (localName : String) : Res NodeId :=
  if !validElementLocalName localName then (d, .error .invalidCharacter)
  else
    let htmlDoc := (d.get doc).htmlDoc
    let lname := if htmlDoc then asciiLower localName else localName
    let ns := if htmlDoc || (d.get doc).contentType == "application/xhtml+xml" then some htmlNS else none
    let (d, id) := d.create { type := .element, doc, ns, lname }
    (d, .ok id)

def createTextNode (d : Dom) (doc : NodeId) (data : String) : Dom × NodeId := d.create { type := .text, doc, data }
def createComment (d : Dom) (doc : NodeId) (data : String) : Dom × NodeId := d.create { type := .comment, doc, data }
def createDocumentFragment (d : Dom) (doc : NodeId) : Dom × NodeId := d.create { type := .fragment, doc }

/-- "Valid doctype name" (DOM §1.4): no ASCII whitespace, U+0000 or `>`; the
empty string is valid. -/
def validDoctypeName (name : String) : Bool :=
  !(name.toList.any fun x => isAsciiWhitespace x || x == '\x00' || x == '>')

/-- `document.implementation.createDocumentType(name, publicId, systemId)`
(DOM §4.5.1). -/
def createDocumentType (d : Dom) (doc : NodeId) (name pubId sysId : String) : Res NodeId :=
  if !validDoctypeName name then (d, .error .invalidCharacter)
  else let (d, id) := d.create { type := .doctype, doc, lname := name, pubId, sysId }; (d, .ok id)

/-- `document.createCDATASection(data)` (DOM §4.5). -/
def createCDATASection (d : Dom) (doc : NodeId) (data : String) : Res NodeId :=
  if (d.get doc).htmlDoc then (d, .error .notSupported)
  else if (data.splitOn "]]>").length > 1 then (d, .error .invalidCharacter)
  else let (d, id) := d.create { type := .cdata, doc, data }; (d, .ok id)

/-- `document.createProcessingInstruction(target, data)` (DOM §4.5, §4.13). -/
def createProcessingInstruction (d : Dom) (doc : NodeId) (target data : String) : Res NodeId :=
  if !XML.isName target then (d, .error .invalidCharacter)
  else if (data.splitOn "?>").length > 1 then (d, .error .invalidCharacter)
  else let (d, id) := d.create { type := .pi, doc, lname := target, data }; (d, .ok id)

/-- `element.setAttribute(qualifiedName, value)` (DOM §4.9). -/
def setAttribute (d : Dom) (el : NodeId) (qualifiedName value : String) : Res Unit :=
  if !validAttributeLocalName qualifiedName then (d, .error .invalidCharacter)
  else
    let q := if (d.get el).ns == some htmlNS && (d.get (d.get el).doc).htmlDoc then asciiLower qualifiedName
      else qualifiedName
    match (d.get el).attrs.findIdx? (·.qname == q) with
    | some i => (d.setNode el fun e => { e with attrs := e.attrs.modify i fun a => { a with value } }, .ok ())
    | none => (d.setNode el fun e => { e with attrs := e.attrs.push { lname := q, value } }, .ok ())

/-! ## Namespaces (DOM §1.4) and the namespaced attribute methods (DOM §4.9) -/

/-- "Valid namespace prefix" (DOM §1.4): not empty, and no ASCII whitespace, U+0000,
"/" or ">". -/
def validNamespacePrefix (p : String) : Bool :=
  !p.isEmpty && !(p.toList.any fun x => isAsciiWhitespace x || x == '\x00' || x == '/' || x == '>')

/-- "Validate and extract" (DOM §1.4) a namespace and qualified name, for an element
(`attr := false`) or an attribute: the namespace (the empty string is null), the
prefix and the local name. The prefix is what comes before the first ":"; the local
name is all the rest. -/
def validateAndExtract (ns : Option String) (qname : String) (attr : Bool) :
    Except DomError (Option String × Option String × String) := do
  let ns := if ns == some "" then none else ns
  let (pfx, lname) := match qname.splitOn ":" with
    | [] | [_] => (none, qname)
    | p :: rest => (some p, ":".intercalate rest)
  if let some p := pfx then
    if !validNamespacePrefix p then throw .invalidCharacter
  if attr && !validAttributeLocalName lname then throw .invalidCharacter
  if !attr && !validElementLocalName lname then throw .invalidCharacter
  if pfx.isSome && ns.isNone then throw .namespace
  if pfx == some "xml" && ns != some xmlNS then throw .namespace
  if (qname == "xmlns" || pfx == some "xmlns") && ns != some xmlnsNS then throw .namespace
  if ns == some xmlnsNS && qname != "xmlns" && pfx != some "xmlns" then throw .namespace
  return (ns, pfx, lname)

/-- The index of the attribute of `el` with namespace `ns` and local name `lname`. -/
def attrIndexNS (d : Dom) (el : NodeId) (ns : Option String) (lname : String) : Option Nat :=
  let ns := if ns == some "" then none else ns
  (d.get el).attrs.findIdx? fun a => a.ns == ns && a.lname == lname

/-- `getAttributeNS(namespace, localName)` (DOM §4.9). -/
def getAttributeNS? (d : Dom) (el : NodeId) (ns : Option String) (lname : String) : Option String :=
  (d.attrIndexNS el ns lname).bind fun i => (d.get el).attrs[i]?.map (·.value)

/-- `setAttributeNS(namespace, qualifiedName, value)` (DOM §4.9): validate and extract,
then "set an attribute value": an attribute with that namespace and local name keeps its
prefix and gets the value; otherwise a new attribute is appended. -/
def setAttributeNS (d : Dom) (el : NodeId) (ns : Option String) (qname value : String) : Res Unit :=
  match validateAndExtract ns qname true with
  | .error e => (d, .error e)
  | .ok (ns, pfx, lname) =>
    match d.attrIndexNS el ns lname with
    | some i => (d.setNode el fun e => { e with attrs := e.attrs.modify i fun a => { a with value } }, .ok ())
    | none => (d.setNode el fun e => { e with attrs := e.attrs.push { ns, pfx, lname, value } }, .ok ())

/-- `removeAttributeNS(namespace, localName)` (DOM §4.9). -/
def removeAttributeNS (d : Dom) (el : NodeId) (ns : Option String) (lname : String) : Dom :=
  match d.attrIndexNS el ns lname with
  | some i => d.setNode el fun e => { e with attrs := e.attrs.eraseIdxIfInBounds i }
  | none => d

/-- The parent of `n` when it is an element. -/
def parentElement (d : Dom) (n : NodeId) : Option NodeId :=
  (d.get n).parent.bind fun p => if (d.get p).type == .element then some p else none

/-- The document element of document `n`. -/
def documentElement (d : Dom) (n : NodeId) : Option NodeId :=
  (d.get n).kids.find? fun k => (d.get k).type == .element

/-- "Locate a namespace" for `prefix` (DOM §4.4), `fuel` steps up the tree. -/
def locateNamespace (d : Dom) (pfx : Option String) : Nat → NodeId → Option String
  | 0, _ => none
  | fuel + 1, n =>
    let x := d.get n
    let up := fun (k : Option NodeId) => k.bind (d.locateNamespace pfx fuel)
    match x.type with
    | .element =>
      if pfx == some "xml" then some xmlNS
      else if pfx == some "xmlns" then some xmlnsNS
      else if x.ns.isSome && x.pfx == pfx then x.ns
      else
        let decl := x.attrs.find? fun a => a.ns == some xmlnsNS &&
          ((a.pfx == some "xmlns" && some a.lname == pfx) || (a.pfx.isNone && a.lname == "xmlns" && pfx.isNone))
        match decl with
        | some a => if a.value.isEmpty then none else some a.value
        | none => up (d.parentElement n)
    | .document => up (d.documentElement n)
    | .doctype | .fragment => none
    | _ => up (d.parentElement n)

/-- `lookupNamespaceURI(prefix)` (DOM §4.4); the empty prefix is null. -/
def lookupNamespaceURI (d : Dom) (n : NodeId) (pfx : Option String) : Option String :=
  d.locateNamespace (if pfx == some "" then none else pfx) (d.size + 1) n

/-- "Locate a namespace prefix" for `ns` on element `n` (DOM §4.4). -/
def locatePrefix (d : Dom) (ns : String) : Nat → NodeId → Option String
  | 0, _ => none
  | fuel + 1, n =>
    let x := d.get n
    if x.ns == some ns && x.pfx.isSome then x.pfx
    else match x.attrs.find? (fun a => a.pfx == some "xmlns" && a.value == ns) with
      | some a => some a.lname
      | none => (d.parentElement n).bind (d.locatePrefix ns fuel)

/-- `lookupPrefix(namespace)` (DOM §4.4). -/
def lookupPrefix (d : Dom) (n : NodeId) (ns : Option String) : Option String :=
  match ns with
  | none | some "" => none
  | some ns =>
    let start := match (d.get n).type with
      | .element => some n
      | .document => d.documentElement n
      | .doctype | .fragment => none
      | _ => d.parentElement n
    start.bind (d.locatePrefix ns (d.size + 1))

/-! ## Node interface methods (DOM §4.4) -/

/-- The descendant text content (DOM §4.4): the data of the Text descendants,
in tree order. -/
def descendantTextContent (d : Dom) (n : NodeId) : String :=
  (d.treeOrder n false).foldl (init := "") fun acc k =>
    let x := d.get k
    if isTextNode x then acc ++ x.data else acc

/-- `textContent` getter (DOM §4.4): `none` is null. -/
def textContent (d : Dom) (n : NodeId) : Option String :=
  let x := d.get n
  match x.type with
  | .fragment | .element => some (d.descendantTextContent n)
  | .text | .cdata | .comment | .pi => some x.data
  | .document | .doctype => none

/-- `textContent` setter (DOM §4.4, "set text content"); null is the empty string. -/
def setTextContent (d : Dom) (n : NodeId) (value : String) : Dom :=
  let x := d.get n
  match x.type with
  | .fragment | .element =>
    if value.isEmpty then d.replaceAll none n
    else
      let (d, t) := d.createTextNode x.doc value
      d.replaceAll (some t) n
  | .text | .cdata | .comment | .pi => d.setNode n fun y => { y with data := value }
  | .document | .doctype => d

/-- `normalize()` (DOM §4.4): for each exclusive Text descendant in tree order,
remove it when its data is empty, else append to it the data of the contiguous
exclusive Text siblings that follow it and remove them.

One pass over the child array of each inclusive descendant of `n`, which gives
the same result: in each run of adjacent exclusive Text siblings, the first node
with non-empty data takes the data of the whole run, and every other node of the
run is removed (all of them when all are empty). Walking with `nextSibling`
searched the child array once per Text node, which was quadratic in the number
of siblings (measured 2026-11-01: 80,000 siblings, 16 s). -/
def normalizeChildren (d : Dom) (p : NodeId) : Dom := Id.run do
  let ks := (d.get p).kids
  if !(ks.any fun k => (d.get k).type == .text) then return d
  let mut d := d
  let mut keep : Array NodeId := #[]
  -- the node of the current run that takes the run's data, and that data
  let mut keeper : Option NodeId := none
  let mut acc : String := ""
  let mut gone : Array NodeId := #[]
  for k in ks do
    let x := d.get k
    if x.type == .text then
      match keeper with
      | some _ =>
        acc := acc ++ x.data
        gone := gone.push k
      | none =>
        if x.data.isEmpty then gone := gone.push k
        else
          keeper := some k
          acc := x.data
          keep := keep.push k
    else
      if let some t := keeper then d := d.setNode t fun y => { y with data := acc }
      keeper := none
      keep := keep.push k
  if let some t := keeper then d := d.setNode t fun y => { y with data := acc }
  d := d.setNode p fun y => { y with kids := keep }
  for g in gone do d := d.setNode g fun y => { y with parent := none }
  return d

def normalize (d : Dom) (n : NodeId) : Dom := Id.run do
  let mut d := d
  for p in d.treeOrder n true do
    d := d.normalizeChildren p
  return d

/-- "Clone a single node" (DOM §4.4) into document `doc`; a document is its
own node document. -/
def cloneSingle (d : Dom) (src : NodeId) (doc : Option NodeId) : Dom × NodeId :=
  let x := d.get src
  let n : Node := { type := x.type, doc := doc.getD x.doc, ns := x.ns, pfx := x.pfx, lname := x.lname,
                    attrs := x.attrs, data := x.data, pubId := x.pubId, sysId := x.sysId,
                    htmlDoc := x.htmlDoc, contentType := x.contentType }
  let (d, id) := d.create n
  if x.type == .document then (d.setNode id fun y => { y with doc := id }, id) else (d, id)

/-- `cloneNode(deep)` (DOM §4.4, "clone a node"), with the cloning steps of an
HTML `template` element: a deep clone also clones the template contents. A loop
over a work list of (source, copy parent) pairs. -/
def cloneNode (d : Dom) (src : NodeId) (deep : Bool) : Dom × NodeId := Id.run do
  let (d0, top) := d.cloneSingle src none
  let mut d := d0
  if !deep then return (d, top)
  let docOf (d : Dom) (copy : NodeId) : NodeId :=
    let c := d.get copy
    if c.type == .document then copy else c.doc
  -- (source node, parent of its copy)
  let srcContent := fun (d : Dom) (s c : NodeId) =>
    match (d.get s).content, (d.get c).content with
    | some sc, some cc => (d.get sc).kids.toList.map (·, cc)
    | _, _ => []
  let mut work : List (NodeId × NodeId) :=
    (d.get src).kids.toList.map (·, top) ++ srcContent d src top
  for _ in [0:2 * d.size + 2] do
    match work with
    | [] => break
    | (s, cp) :: rest =>
      let (d1, c) := d.cloneSingle s (some (docOf d cp))
      d := d1.linkChild cp c none
      work := (d.get s).kids.toList.map (·, c) ++ srcContent d s c ++ rest
  return (d, top)

/-- Attribute lists equal as sets of (namespace, local name, value) (DOM §4.4
"equals"). -/
def attrsEqual (a b : Array Attr) : Bool :=
  a.size == b.size && a.all fun x => b.any fun y => x.ns == y.ns && x.lname == y.lname && x.value == y.value

/-- `isEqualNode` (DOM §4.4 "equals"). A loop over a work list of pairs. -/
def isEqualNode (d : Dom) (a b : NodeId) : Bool := Id.run do
  let mut work : List (NodeId × NodeId) := [(a, b)]
  for _ in [0:d.size + 1] do
    match work with
    | [] => return true
    | (x, y) :: rest =>
      let p := d.get x
      let q := d.get y
      let same := p.type == q.type && match p.type with
        | .doctype => p.lname == q.lname && p.pubId == q.pubId && p.sysId == q.sysId
        | .element => p.ns == q.ns && p.pfx == q.pfx && p.lname == q.lname && attrsEqual p.attrs q.attrs
        | .pi => p.lname == q.lname && p.data == q.data
        | .text | .cdata | .comment => p.data == q.data
        | .document | .fragment => true
      if !same || p.kids.size != q.kids.size then return false
      work := (p.kids.toList.zip q.kids.toList) ++ rest
  return work.isEmpty

/-- `contains(other)` (DOM §4.4): `other` is an inclusive descendant. -/
def contains (d : Dom) (n : NodeId) (other : Option NodeId) : Bool :=
  match other with
  | some o => d.isInclusiveAncestor n o
  | none => false

/-- "Get an element by ID" (DOM §4.2.4): the first element in tree order among
the descendants of `n` whose ID is `id`. -/
def getElementById (d : Dom) (n : NodeId) (id : String) : Option NodeId :=
  (d.treeOrder n false).find? fun k =>
    let x := d.get k
    x.type == .element && x.attrs.any fun a => a.ns.isNone && a.lname == "id" && a.value == id

/-! ## Documents of other browsing contexts -/

/-- Append every node of arena `src` to `d`, its node numbers moved by `d.size`: a
document parsed on its own (an `iframe`'s document) joins the arena of the page, so that
scripts reach both through the same node numbers. The answer is the new number of
`src`'s node 0. -/
def graft (d src : Dom) : Dom × NodeId :=
  let k := d.size
  let move := fun (x : Node) => { x with
    doc := x.doc + k, parent := x.parent.map (· + k), kids := x.kids.map (· + k),
    host := x.host.map (· + k), content := x.content.map (· + k) }
  ({ nodes := d.nodes ++ src.nodes.map move }, k)

theorem graft_size (d src : Dom) : (d.graft src).1.size = d.size + src.size := by
  simp [graft, size]

theorem graft_root (d src : Dom) : (d.graft src).2 = d.size := rfl

/-! ## The tree invariant -/

/-- The arena is a forest whose parent and child links agree: every child
names its parent, every node with a parent is among its parent's children
exactly once, every index is in range, and no node is its own proper
ancestor. Checked after every operation of the differential test. -/
def wellFormed (d : Dom) : Bool := Id.run do
  let n := d.size
  for i in [0:n] do
    let x := d.get i
    for k in x.kids do
      if k ≥ n || (d.get k).parent != some i then return false
    match x.parent with
    | some p =>
      if p ≥ n || ((d.get p).kids.filter (· == i)).size != 1 then return false
      if d.isInclusiveAncestor i p then return false
    | none => pure ()
    match x.content with
    | some c => if c ≥ n || (d.get c).host != some i then return false
    | none => pure ()
  return true

end Dom
end L4Factoidal.DOM
