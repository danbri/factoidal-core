/-
L4Factoidal.DOM.Shadow — shadow trees and slots of the WHATWG DOM Standard, on the
arena of `DOM.Arena`.

Specification: DOM Living Standard (whatwg/dom `3c53f93a`) §4.2.2 "Shadow tree" (slots,
slottables, finding slots and slottables, assigning slottables), §4.8 "Interface
ShadowRoot", §4.9 `attachShadow` ("attach a shadow root"), §2.5 "retarget", §2.9 the
event path ("get the parent" of a node and of a shadow root) and §2.2 `composedPath`.
CSS Scoping 1 §2.2 for the flat tree (record:
docs/designissues/2026-11-08-shadow-dom-frames.md).

A shadow root is a DocumentFragment with a `ShadowInit`; its `host` field is its host,
and the host's `shadow` field is the shadow root. It is not a child of its host, so tree
order (`Dom.treeOrder`) and the selectors of the light tree never enter it.

Slot assignment is computed when asked, from the tree: `findSlot` and
`findSlottables` are the algorithms of §4.2.2.3, and the "assigned nodes" of a slot are
`findSlottables` of it (the assign steps of §4.2.2.4 run after every change, so the
assigned nodes always equal what `findSlottables` answers on the current tree).

Theorems:
- `flat_eq_of_noShadow`: the flat tree of an arena with no shadow root is the arena.
- `flatChildren_eq_kids`: with no shadow host and no shadow root, the flat children of a
  node are its children (the algorithm, not only its guard).
- `retarget_visible`: retargeting answers a node whose root is not a shadow root, or a
  shadow root that is a shadow-including inclusive ancestor of the listener's node.
- `retarget_closed`: so a node inside a closed shadow root is never the target a
  listener outside that shadow root sees.
- `shadowIncludingRoot_eq_root`: with no shadow root, the shadow-including root is the
  root.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.Dom

/-! ## Attaching a shadow root -/

/-- The HTML elements that may host a shadow root (DOM §4.9 `attachShadow` step 3), besides
a valid custom element name. -/
def shadowHostNames : List String :=
  ["article", "aside", "blockquote", "body", "div", "footer", "h1", "h2", "h3", "h4", "h5", "h6",
   "header", "main", "nav", "p", "section", "span"]

/-- A PCENChar after the first (HTML §4.13.2), for the characters below U+0080: `-`, `.`,
`0`-`9`, `_` and `a`-`z`; all code points from U+00B7 up that the production allows. -/
def pcenChar (c : Char) : Bool :=
  c == '-' || c == '.' || ('0' ≤ c && c ≤ '9') || c == '_' || ('a' ≤ c && c ≤ 'z') || c.val == 0xB7 ||
  (0xC0 ≤ c.val && c.val ≤ 0xD6) || (0xD8 ≤ c.val && c.val ≤ 0xF6) || (0xF8 ≤ c.val && c.val ≤ 0x37D) ||
  (0x37F ≤ c.val && c.val ≤ 0x1FFF) || (0x200C ≤ c.val && c.val ≤ 0x200D) || (0x203F ≤ c.val && c.val ≤ 0x2040) ||
  (0x2070 ≤ c.val && c.val ≤ 0x218F) || (0x2C00 ≤ c.val && c.val ≤ 0x2FEF) || (0x3001 ≤ c.val && c.val ≤ 0xD7FF) ||
  (0xF900 ≤ c.val && c.val ≤ 0xFDCF) || (0xFDF0 ≤ c.val && c.val ≤ 0xFFFD) || (0x10000 ≤ c.val && c.val ≤ 0xEFFFF)

/-- A valid custom element name (HTML §4.13.2): `[a-z] PCENChar* '-' PCENChar*`, not one of
the reserved names. -/
def validCustomElementName (name : String) : Bool :=
  match name.toList with
  | c :: rest =>
    'a' ≤ c && c ≤ 'z' && rest.all pcenChar && rest.contains '-' &&
    !["annotation-xml", "color-profile", "font-face", "font-face-src", "font-face-uri",
      "font-face-format", "font-face-name", "missing-glyph"].contains name
  | [] => false

/-- `attachShadow` (DOM §4.9, "attach a shadow root"): the element must be an HTML element
whose local name is a valid custom element name or one of `shadowHostNames`
(NotSupportedError otherwise). An element that already hosts a shadow root gets
NotSupportedError, except when that shadow root is declarative and of the same mode: then
its children are removed, it is no longer declarative, and it is the answer. -/
def attachShadow (d : Dom) (el : NodeId) (init : ShadowInit) : Res NodeId :=
  let x := d.get el
  if el ≥ d.size || x.type != .element || x.ns != some htmlNS then (d, .error .notSupported)
  else if !(validCustomElementName x.lname || shadowHostNames.contains x.lname) then (d, .error .notSupported)
  else match x.shadow with
    | some sr =>
      let cur := (d.get sr).shadowInit.getD {}
      if !cur.declarative || cur.closed != init.closed then (d, .error .notSupported)
      else
        let d := d.replaceAll none sr
        (d.setNode sr fun n => { n with shadowInit := some { cur with declarative := false } }, .ok sr)
    | none =>
      let (d, sr) := d.push { type := .fragment, doc := x.doc, host := some el, shadowInit := some init }
      (d.setNode el fun n => { n with shadow := some sr }, .ok sr)

/-- The host of a shadow root, or none. -/
def shadowHost? (d : Dom) (n : NodeId) : Option NodeId :=
  if d.isShadowRoot n then (d.get n).host else none

/-- A shadow root's state, or none for any other node. -/
def shadowInitOf? (d : Dom) (n : NodeId) : Option ShadowInit :=
  if (d.get n).type == .fragment then (d.get n).shadowInit else none

/-! ## Slots and slottables (DOM §4.2.2) -/

/-- The value of attribute `name` (no namespace) of a node, or "". -/
def plainAttr (n : Node) (name : String) : String :=
  ((n.attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)).getD ""

/-- The element has attribute `name` (no namespace). -/
def hasAttr (n : Node) (name : String) : Bool := n.attrs.any fun a => a.ns.isNone && a.lname == name

/-- A slot: an HTML `slot` element (DOM §4.2.2.1). -/
def isSlot (d : Dom) (n : NodeId) : Bool := isHtmlElement (d.get n) "slot"

/-- A slottable: an Element or a Text node (DOM §4.2.2.2). -/
def isSlottable (d : Dom) (n : NodeId) : Bool :=
  let t := (d.get n).type
  t == .element || t == .text || t == .cdata

/-- A slot's name: its `name` attribute, or "" (DOM §4.2.2.1). -/
def slotName (d : Dom) (n : NodeId) : String := plainAttr (d.get n) "name"

/-- A slottable's name: an element's `slot` attribute, or "" (DOM §4.2.2.2). -/
def slottableName (d : Dom) (n : NodeId) : String :=
  if (d.get n).type == .element then plainAttr (d.get n) "slot" else ""

/-- The slots of shadow root `sr`, in tree order. -/
def slotsOf (d : Dom) (sr : NodeId) : Array NodeId := (d.treeOrder sr false).filter (d.isSlot ·)

/-- "Find a slot" (DOM §4.2.2.3) for slottable `s` among the slots of its parent's shadow
root (`slots`, in tree order): with `openOnly`, none in a closed shadow root. -/
def findSlotIn (d : Dom) (s : NodeId) (init : ShadowInit) (slots : Array NodeId) (openOnly : Bool) : Option NodeId :=
  if openOnly && init.closed then none
  else if init.manual then slots.find? fun k => (d.get k).manual.contains s
  else
    let name := d.slottableName s
    slots.find? fun k => d.slotName k == name

/-- "Find a slot" (DOM §4.2.2.3): the slot of the shadow root of `s`'s parent that `s` is
assigned to. -/
def findSlot (d : Dom) (s : NodeId) (openOnly : Bool := false) : Option NodeId := do
  let p ← (d.get s).parent
  let sr ← (d.get p).shadow
  let init ← (d.get sr).shadowInit
  d.findSlotIn s init (d.slotsOf sr) openOnly

/-- "Find slottables" (DOM §4.2.2.3): the nodes assigned to `slot`; this is the slot's
"assigned nodes" (`assignedNodes()`). Empty for a slot that is not in a shadow tree. -/
def findSlottables (d : Dom) (slot : NodeId) : Array NodeId :=
  let root := d.root slot
  if !d.isShadowRoot root then #[] else
  match (d.get root).host, (d.get root).shadowInit with
  | some host, some init =>
    if init.manual then
      (d.get slot).manual.filter fun s => (d.get s).parent == some host && d.isSlottable s
    else
      let slots := d.slotsOf root
      (d.get host).kids.filter fun c => d.isSlottable c && d.findSlotIn c init slots false == some slot
  | _, _ => #[]

/-- A slot whose root is a shadow root: in the flat tree it takes the place of its
assigned nodes, or of its own children when none is assigned. -/
def isSlotInShadow (d : Dom) (n : NodeId) : Bool := d.isSlot n && d.isShadowRoot (d.root n)

/-- "Find flattened slottables" (DOM §4.2.2.3), with at most `fuel` nested slots. -/
def flattenedGo (d : Dom) : Nat → NodeId → Array NodeId
  | 0, _ => #[]
  | fuel + 1, slot =>
    if !d.isShadowRoot (d.root slot) then #[] else
    let assigned := d.findSlottables slot
    let list := if assigned.isEmpty then (d.get slot).kids.filter (d.isSlottable ·) else assigned
    list.flatMap fun k => if d.isSlotInShadow k then d.flattenedGo fuel k else #[k]

/-- `assignedNodes({flatten: true})`: the flattened slottables of `slot`. -/
def findFlattenedSlottables (d : Dom) (slot : NodeId) : Array NodeId := d.flattenedGo (d.size + 1) slot

/-- `assignedSlot` of a slottable (DOM §4.2.2.2): "find a slot" with open only. -/
def assignedSlot (d : Dom) (s : NodeId) : Option NodeId := d.findSlot s true

/-- `slot.assign(...nodes)` (HTML §4.12.4, DOM §4.2.2.1 manual assignment). -/
def assignSlot (d : Dom) (slot : NodeId) (nodes : Array NodeId) : Dom := Id.run do
  let mut d := d
  for k in (d.get slot).manual do d := d.setNode k fun n => { n with manualSlot := none }
  d := d.setNode slot fun n => { n with manual := #[] }
  for k in nodes do
    if k < d.size && !(d.get slot).manual.contains k then
      if let some old := (d.get k).manualSlot then
        d := d.setNode old fun n => { n with manual := n.manual.filter (· != k) }
      d := d.setNode k fun n => { n with manualSlot := some slot }
      d := d.setNode slot fun n => { n with manual := n.manual.push k }
  return d

/-- Every slot of every shadow tree with its assigned nodes, for "signal a slot change"
(DOM §4.2.2.5): a host compares two of these to find the slots whose assigned nodes
changed. -/
def slotAssignments (d : Dom) (roots : Array NodeId) : Array (NodeId × Array NodeId) :=
  roots.flatMap fun sr => if d.isShadowRoot sr then (d.slotsOf sr).map fun k => (k, d.findSlottables k) else #[]

/-- The slots whose assigned nodes differ between `before` and `after` (both from
`slotAssignments`), in the order of `after`: a slot that is new and has assigned nodes, or
a slot whose list changed. -/
def slotChanges (before after : Array (NodeId × Array NodeId)) : Array NodeId :=
  after.filterMap fun (k, xs) =>
    match before.find? (·.1 == k) with
    | some (_, ys) => if xs == ys then none else some k
    | none => if xs.isEmpty then none else some k

/-! ## The flat tree (CSS Scoping 1 §2.2) -/

/-- The children of `n` in the node tree that the flat tree starts from: a shadow host's
shadow root's children, else its own. -/
def treeChildren (d : Dom) (n : NodeId) : Array NodeId :=
  match (d.get n).shadow with
  | some sr => (d.get sr).kids
  | none => (d.get n).kids

/-- The flat-tree children of `n`, with each slot of a shadow tree replaced by what it
shows: its flattened slottables, or its children (as `display: contents`; the slot is not a
box of this layout). -/
def flatChildren (d : Dom) (n : NodeId) : Array NodeId :=
  (d.treeChildren n).flatMap fun k =>
    if d.isSlotInShadow k then
      let shown := d.findFlattenedSlottables k
      if shown.isEmpty then
        -- fallback content: the slot's own children, with nested slots shown in turn
        (d.get k).kids.flatMap fun c => if d.isSlotInShadow c then d.findFlattenedSlottables c else #[c]
      else shown
    else #[k]

/-- Some node of the arena is a shadow host. -/
def hasShadow (d : Dom) : Bool := d.nodes.any (·.shadow.isSome)

/-- The flat tree of the document (CSS Scoping 1 §2.2), as an arena with the same node
numbers: from node 0 down, each node's children are its `flatChildren`, and their parent
is that node. A node outside the flat tree (a host's unassigned child, a shadow root, a
slot of a shadow tree) is not reached from node 0. An arena with no shadow host is
answered unchanged (`flat_eq_of_noShadow`), so a page with no shadow tree pays one scan. -/
def flat (d : Dom) : Dom := Id.run do
  if !d.hasShadow then return d
  let mut out := d
  let mut work : List NodeId := [0]
  for _ in [0:2 * d.size + 2] do
    match work with
    | [] => break
    | n :: rest =>
      let ks := d.flatChildren n
      out := out.setNode n fun x => { x with kids := ks }
      for k in ks do out := out.setNode k fun x => { x with parent := some n }
      work := ks.toList ++ rest
  return out

theorem flat_eq_of_noShadow (d : Dom) (h : d.hasShadow = false) : d.flat = d := by
  simp [flat, h]

/-- With no shadow root in the arena, no slot is in a shadow tree. -/
theorem isSlotInShadow_false (d : Dom) (h : ∀ i, (d.get i).shadowInit = none) (n : NodeId) :
    d.isSlotInShadow n = false := by
  simp [isSlotInShadow, isShadowRoot, h]

theorem flatChildren_eq_kids (d : Dom) (hs : ∀ i, (d.get i).shadow = none)
    (hi : ∀ i, (d.get i).shadowInit = none) (n : NodeId) :
    d.flatChildren n = (d.get n).kids := by
  simp [flatChildren, treeChildren, hs n, isSlotInShadow_false d hi]

theorem shadowIncludingRoot_eq_root (d : Dom) (hi : ∀ i, (d.get i).shadowInit = none) (n : NodeId) :
    d.shadowIncludingRoot n = d.root n := by
  simp [shadowIncludingRoot, shadowRootWalk, isShadowRoot, hi]

/-! ## Retargeting and the event path (DOM §2.5, §2.9) -/

/-- The walk up from `cur` over parents, and from a shadow root to its host, at most
`fuel` steps: `true` when it meets `a`. -/
def shadowWalk (d : Dom) (a : NodeId) : Nat → NodeId → Bool
  | 0, _ => false
  | f + 1, cur =>
    if cur == a then true
    else match (d.get cur).parent with
      | some p => d.shadowWalk a f p
      | none => if d.isShadowRoot cur then
          match (d.get cur).host with
          | some h => d.shadowWalk a f h
          | none => false
        else false

/-- `a` is a shadow-including inclusive ancestor of `b` (DOM §4.8). -/
def shadowIncludingAncestor (d : Dom) (a b : NodeId) : Bool := d.shadowWalk a (2 * d.size + 2) b

/-- What a listener at `b` may see of node `a` (DOM §2.5 "retarget", the stop condition):
`a`'s root is not a shadow root, or it is a shadow-including inclusive ancestor of `b`. -/
def visible (d : Dom) (a b : NodeId) : Bool :=
  !d.isShadowRoot (d.root a) || d.shadowIncludingAncestor (d.root a) b

/-- "Retarget `a` against `b`" (DOM §2.5), at most `fuel` steps: while `a`'s root is a
shadow root that does not contain `b`, `a` becomes that shadow root's host. None when the
walk does not end (a malformed arena), so nothing hidden is answered. -/
def retargetGo (d : Dom) (b : NodeId) : Nat → NodeId → Option NodeId
  | 0, _ => none
  | f + 1, a =>
    if d.visible a b then some a
    else match (d.get (d.root a)).host with
      | some h => d.retargetGo b f h
      | none => none

def retarget (d : Dom) (a b : NodeId) : Option NodeId := d.retargetGo b (d.size + 1) a

theorem retargetGo_visible (d : Dom) (b : NodeId) :
    ∀ (fuel : Nat) (a t : NodeId), d.retargetGo b fuel a = some t → d.visible t b = true := by
  intro fuel
  induction fuel with
  | zero => intro a t h; simp [retargetGo] at h
  | succ f ih =>
    intro a t h
    unfold retargetGo at h
    split at h
    · rename_i hv; cases h; exact hv
    · split at h
      · exact ih _ _ h
      · cases h

/-- Retargeting answers a node the listener at `b` may see. -/
theorem retarget_visible (d : Dom) (a b t : NodeId) (h : d.retarget a b = some t) : d.visible t b = true :=
  retargetGo_visible d b _ a t h

/-- A node inside a closed shadow root (its root is that shadow root) is never the
retargeted target for a listener outside it: the listener's node is a shadow-including
descendant of that shadow root. -/
theorem retarget_closed (d : Dom) (a b t : NodeId) (h : d.retarget a b = some t)
    (hc : d.isShadowRoot (d.root t) = true) : d.shadowIncludingAncestor (d.root t) b = true := by
  have hv := retarget_visible d a b t h
  simp [visible, hc] at hv
  exact hv

/-- "Get the parent" (DOM §2.9) of a node of the event path, for an event whose
first target is `first`: a slottable that is assigned: its assigned slot; a shadow root:
its host, unless the event is not composed and it is the root of `first`; else the
parent. The document's parent (the window) is the host's to add. -/
def eventParent (d : Dom) (first : NodeId) (composed : Bool) (n : NodeId) : Option NodeId :=
  if d.isShadowRoot n then
    if !composed && d.root first == n then none else (d.get n).host
  else if d.isSlottable n then
    match d.findSlot n with
    | some s => some s
    | none => (d.get n).parent
  else (d.get n).parent

/-- The event path of DOM §2.9 over nodes, target first, at most `fuel` nodes: each node's
`eventParent`. -/
def eventPathGo (d : Dom) (first : NodeId) (composed : Bool) : Nat → NodeId → List NodeId
  | 0, _ => []
  | f + 1, n => n :: match d.eventParent first composed n with
    | some p => d.eventPathGo first composed f p
    | none => []

def eventPath (d : Dom) (target : NodeId) (composed : Bool) : List NodeId :=
  d.eventPathGo target composed (2 * d.size + 2) target

/-- `composedPath()` (DOM §2.2) for the listener at `current`: the path without the
nodes a closed shadow root hides from it. A node is kept when every closed shadow root
that contains it also contains `current` (`hiddenFrom`). -/
def hiddenGo (d : Dom) (c : NodeId) : Nat → NodeId → Bool
  | 0, _ => false
  | f + 1, x =>
    let r := d.root x
    if d.isShadowRoot r then
      let closed := ((d.get r).shadowInit.map (·.closed)).getD false
      if closed && !d.shadowIncludingAncestor r c then true
      else match (d.get r).host with
        | some h => d.hiddenGo c f h
        | none => false
    else false

/-- Node `x` is inside a closed shadow root that does not contain `c`. -/
def hiddenFrom (d : Dom) (x c : NodeId) : Bool := d.hiddenGo c (d.size + 1) x

/-! ## The root of a node, composed or not (DOM §4.4 `getRootNode`) -/

/-- `getRootNode({composed})`: the root, or with `composed` the shadow-including root. -/
def rootNode (d : Dom) (n : NodeId) (composed : Bool) : NodeId :=
  if composed then d.shadowIncludingRoot n else d.root n

/-- `isConnected` (DOM §4.4): the shadow-including root is a document. -/
def connected (d : Dom) (n : NodeId) : Bool := (d.get (d.shadowIncludingRoot n)).type == .document

-- a host with a shadow root, a slot and two light children
private def sample : Dom := Id.run do
  let d : Dom := { nodes := #[{ type := .document, doc := 0 }] }
  let (d, host) := d.create { type := .element, doc := 0, ns := some htmlNS, lname := "div" }
  let d := d.linkChild 0 host none
  let (d, a) := d.create { type := .element, doc := 0, ns := some htmlNS, lname := "p", attrs := #[{ lname := "slot", value := "x" }] }
  let d := d.linkChild host a none
  let (d, b) := d.create { type := .element, doc := 0, ns := some htmlNS, lname := "p" }
  let d := d.linkChild host b none
  match d.attachShadow host {} with
  | (d, .ok sr) =>
    let (d, s) := d.create { type := .element, doc := 0, ns := some htmlNS, lname := "slot", attrs := #[{ lname := "name", value := "x" }] }
    d.linkChild sr s none
  | (d, .error _) => d

-- node 1 host, 2 and 3 light children, 4 the shadow root, 5 the named slot
#guard sample.findSlottables 5 == #[2]
#guard sample.flatChildren 1 == #[2]
#guard (sample.flat.get 1).kids == #[2] && (sample.flat.get 2).parent == some 1
#guard sample.eventPath 2 false == [2, 5, 4, 1, 0]
#guard sample.eventPath 5 false == [5, 4] && sample.eventPath 5 true == [5, 4, 1, 0]
#guard sample.retarget 5 0 == some 1 && sample.retarget 5 4 == some 5
#guard sample.assignedSlot 2 == some 5 && sample.assignedSlot 3 == none
#guard sample.connected 5 && sample.rootNode 5 false == 4 && sample.rootNode 5 true == 0
#guard (sample.attachShadow 1 {}).2.toOption.isNone
#guard (sample.attachShadow 2 {}).2.toOption.isSome
#guard validCustomElementName "my-el" && !validCustomElementName "myel" && !validCustomElementName "font-face"
#guard sample.wellFormed

end L4Factoidal.DOM.Dom
