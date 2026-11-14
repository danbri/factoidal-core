/-
L4Factoidal.WasmVM.Hosts.DomOps: the DOM operations of page scripts that keep state beyond
the arena: live ranges (DOM §5), the selection (Selection API), NodeIterator and
TreeWalker (DOM §6), and the CharacterData changes that move live ranges (DOM §4.10,
§4.11).

They are `node_query` ops from 100 (`Hosts.Page.serveExtra` sends them here, with the
page's DOM state): `n.query(id, op, s)` in prelude.js, so neither QuickJS-NG in WasmVM
nor BubblePopJS needs a new native. Each change of the tree is a typed `Hosts.Dom.Command`
(`exec`), recorded as every other change is, so a host that replays the commands gets the
same arena; the live ranges and iterators move with each command (`Command.live`). An op
that changes the tree answers a short string (a number, or nothing): the QuickJS guest's
first buffer holds it, so the import runs once.

Answers: "" or a number as text; errors are negative codes: -2 not a node or range, -4
HierarchyRequestError, -5 over a budget, -9 NotFoundError, -10 NotSupportedError, -13
InvalidNodeTypeError, -14 IndexSizeError, -15 WrongDocumentError, -16 InvalidStateError.
-/
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.DOM.Reflect
import L4Factoidal.Rendering.CssSupports
import L4Factoidal.Rendering.CssValues.Declaration
import L4Factoidal.Rendering.ComputedGeneric
import L4Factoidal.Rendering.CssSheet
import L4Factoidal.Rendering.CssTyped
import L4Factoidal.HTML.FormSubmission
import L4Factoidal.DOM.Editing.Commands
import L4Factoidal.Rendering.Style
import L4Factoidal.DOM.Named
import L4Factoidal.DOM.CustomElements
import L4Factoidal.HTML.ScriptType
import L4Factoidal.DOM.ElementRef
import L4Factoidal.DOM.FormControls
import L4Factoidal.HTML.TextSelection
import L4Factoidal.DOM.FormValidity
import L4Factoidal.DOM.Focus
import L4Factoidal.HTML.InnerText

namespace L4Factoidal.WasmVM.Hosts.Dom
open L4Factoidal.DOM L4Factoidal.DOM.Range

def rangeErr : Range.Err → Int
  | .invalidNodeType => -13 | .indexSize => -14 | .wrongDocument => -15 | .notSupported => -10
  | .hierarchyRequest => -4 | .invalidState => -16 | .dom e => domErr e

/-- The most live ranges and NodeIterators a page may make. -/
def maxLive : Nat := 1048576

/-- An operation on the page's DOM state that may throw a DOM error code. -/
abbrev Op := StateT State (Except Int)

/-- Run command `c` on the arena (`Command.apply`, the algorithm of the import that
records it), move the live ranges and record it (`addCommand`). -/
def exec (c : Command) : Op Unit := do
  let s ← get
  match c.apply s.dom with
  | .error _ => throw (-4)
  | .ok d => match addCommand s c d with
    | (s', .values #[.i32 0]) => set s'
    | _ => throw (-5)

/-- A command that makes the node numbered as the arena's next node. -/
def make (f : Nat → Command) : Op Nat := do
  let r := (← get).dom.size
  exec (f r)
  return r

def dom : Op Dom := return (← get).dom

def liftR {α : Type} (x : Except Range.Err α) : Op α :=
  match x with
  | .ok a => pure a
  | .error e => throw (rangeErr e)

def getRange (id : Nat) : Op Rng := do
  match (← get).live.ranges[id]? with
  | some (some r) => pure r
  | _ => throw (-2)

def setRange (id : Nat) (r : Rng) : Op Unit :=
  modify fun s => { s with live := { s.live with ranges := s.live.ranges.set! id (some r) } }

/-- A new live range; its number. -/
def newRange (r : Rng) : Op Nat := do
  let s ← get
  if s.live.ranges.size + s.live.iters.size ≥ maxLive && s.live.free.isEmpty then throw (-5)
  let (live, k) := s.live.add r
  set { s with live }
  return k

def nodeArg (d : Dom) (k : Int) : Op Nat :=
  if k < 0 || k.toNat ≥ d.size then throw (-2) else pure k.toNat

/-- The numbers of an op's string argument, separated by spaces. -/
def nums (q : String) : Array Int := ((q.splitOn " ").filterMap String.toInt?).toArray

def num (xs : Array Int) (i : Nat) : Int := xs.getD i 0

/-! ## CharacterData (DOM §4.10, §4.11) -/

/-- "Replace data" with its check (DOM §4.10 step 2). -/
def replaceData (n o k : Nat) (v : String) : Op Unit := do
  let d ← dom
  if !Dom.isCharacterData (d.get n) then throw (-2)
  if o > nodeLength d n then throw (-14)
  exec (.replaceData n o k v)

/-- "Split a Text node" (DOM §4.11). -/
def splitText (n o : Nat) : Op Nat := do
  let d ← dom
  if !Dom.isTextNode (d.get n) then throw (-2)
  if o > nodeLength d n then throw (-14)
  make (.splitText n o)

/-! ## Range algorithms (DOM §5.5) -/

def cloneOf (n : Nat) (deep : Bool) : Op Nat := make (.cloneNode n deep)
def setData (n : Nat) (v : String) : Op Unit := exec (.setTextContent n v)
def append (p c : Nat) : Op Unit := exec (.appendChild p c)
def newFragment (doc : Nat) : Op Nat := make (.createNode (2 + 16 * doc) "")

def removeNode (n : Nat) : Op Unit := do
  match ((← dom).get n).parent with
  | some p => exec (.removeChild p n)
  | none => pure ()

/-- The node document of `n` (a document is its own). -/
def docOf (d : Dom) (n : Nat) : Nat := if (d.get n).type == .document then n else (d.get n).doc

/-- Steps 5 and 6 of delete, 10 and 11 of extract: the boundary point the range collapses
to. -/
def collapsePoint (d : Dom) (r : Rng) : BP := Id.run do
  let sn := r.start.node
  let en := r.stop.node
  if d.isInclusiveAncestor sn en then return r.start
  let mut ref := sn
  for _ in [0:d.size + 1] do
    match (d.get ref).parent with
    | some p => if d.isInclusiveAncestor p en then break else ref := p
    | none => break
  return ⟨((d.get ref).parent).getD ref, indexOf d ref + 1⟩

/-- `deleteContents()` (DOM §5.5). -/
def deleteContents (rid : Nat) : Op Unit := do
  let r ← getRange rid
  if r.collapsed then return
  let d ← dom
  let (sn, so, en, eo) := (r.start.node, r.start.offset, r.stop.node, r.stop.offset)
  if sn == en && Dom.isCharacterData (d.get sn) then
    replaceData sn so (eo - so) ""
    return
  let toRemove := (d.treeOrder (commonAncestor d r) true).filter fun k =>
    contained d r k && !(((d.get k).parent).any (contained d r ·))
  let bp := collapsePoint d r
  if Dom.isCharacterData (d.get sn) then replaceData sn so (nodeLength d sn - so) ""
  for k in toRemove do removeNode k
  if Dom.isCharacterData (d.get en) then replaceData en 0 eo ""
  setRange rid ⟨bp, bp⟩

/-- The partially contained children of the common ancestor and its contained children
(extract and clone, steps 5 to 9). -/
def split (d : Dom) (r : Rng) : Op (Option Nat × Option Nat × Array Nat) := do
  let (sn, en) := (r.start.node, r.stop.node)
  let kids := (d.get (commonAncestor d r)).kids
  let first := if d.isInclusiveAncestor sn en then none else kids.find? (partiallyContained d r ·)
  let last := if d.isInclusiveAncestor en sn then none else kids.reverse.find? (partiallyContained d r ·)
  let inside := kids.filter (contained d r ·)
  if inside.any (fun k => (d.get k).type == .doctype) then throw (-4)
  return (first, last, inside)

/-- "Extract" a live range (DOM §5.5): the fragment, and the point the range collapses to
(the caller sets the range; a subrange is not live). `fuel` bounds the recursion by the
tree's depth. -/
def extractR : Nat → Rng → Op (Nat × BP)
  | 0, _ => throw (-5)
  | fuel + 1, r => do
    let d ← dom
    let frag ← newFragment (docOf d r.start.node)
    if r.collapsed then return (frag, r.start)
    let (sn, so, en, eo) := (r.start.node, r.start.offset, r.stop.node, r.stop.offset)
    if sn == en && Dom.isCharacterData (d.get sn) then
      let c ← cloneOf sn false
      setData c (substringUnits (d.get sn).data so (eo - so))
      append frag c
      replaceData sn so (eo - so) ""
      return (frag, r.start)
    let (first, last, inside) ← split d r
    let bp := collapsePoint d r
    if let some f := first then
      if Dom.isCharacterData (d.get f) then
        let len := nodeLength d sn
        let c ← cloneOf sn false
        setData c (substringUnits (d.get sn).data so (len - so))
        append frag c
        replaceData sn so (len - so) ""
      else
        let c ← cloneOf f false
        append frag c
        let (sub, _) ← extractR fuel ⟨⟨sn, so⟩, ⟨f, nodeLength d f⟩⟩
        append c sub
    for k in inside do append frag k
    if let some l := last then
      let d ← dom
      if Dom.isCharacterData (d.get l) then
        let c ← cloneOf en false
        setData c (substringUnits (d.get en).data 0 eo)
        append frag c
        replaceData en 0 eo ""
      else
        let c ← cloneOf l false
        append frag c
        let (sub, _) ← extractR fuel ⟨⟨l, 0⟩, ⟨en, eo⟩⟩
        append c sub
    return (frag, bp)

/-- "Clone the contents" of a range (DOM §5.5). -/
def cloneR : Nat → Rng → Op Nat
  | 0, _ => throw (-5)
  | fuel + 1, r => do
    let d ← dom
    let frag ← newFragment (docOf d r.start.node)
    if r.collapsed then return frag
    let (sn, so, en, eo) := (r.start.node, r.start.offset, r.stop.node, r.stop.offset)
    if sn == en && Dom.isCharacterData (d.get sn) then
      let c ← cloneOf sn false
      setData c (substringUnits (d.get sn).data so (eo - so))
      append frag c
      return frag
    let (first, last, inside) ← split d r
    if let some f := first then
      if Dom.isCharacterData (d.get f) then
        let c ← cloneOf sn false
        setData c (substringUnits (d.get sn).data so (nodeLength d sn - so))
        append frag c
      else
        let c ← cloneOf f false
        append frag c
        let sub ← cloneR fuel ⟨⟨sn, so⟩, ⟨f, nodeLength d f⟩⟩
        append c sub
    for k in inside do
      let c ← cloneOf k true
      append frag c
    if let some l := last then
      if Dom.isCharacterData (d.get l) then
        let c ← cloneOf en false
        setData c (substringUnits (d.get en).data 0 eo)
        append frag c
      else
        let c ← cloneOf l false
        append frag c
        let sub ← cloneR fuel ⟨⟨l, 0⟩, ⟨en, eo⟩⟩
        append c sub
    return frag

/-- `extractContents()`: extract, then the range collapses. -/
def extractContents (rid : Nat) : Op Nat := do
  let r ← getRange rid
  let (frag, bp) ← extractR ((← dom).size + 1) r
  if !r.collapsed then setRange rid ⟨bp, bp⟩
  return frag

/-- "Insert" `node` into a live range (DOM §5.5, `insertNode`). -/
def insertNode (rid node : Nat) : Op Unit := do
  let r ← getRange rid
  let d ← dom
  let sn := r.start.node
  let x := d.get sn
  if x.type == .pi || x.type == .comment || (Dom.isTextNode x && x.parent.isNone) || sn == node then throw (-4)
  let refNode := if Dom.isTextNode x then some sn else x.kids[r.start.offset]?
  let parent := match refNode with
    | none => sn
    | some k => ((d.get k).parent).getD sn
  match d.ensurePreInsertValidity node parent refNode [] with
  | .error e => throw (domErr e)
  | .ok () => pure ()
  let mut ref := refNode
  if Dom.isTextNode x then ref := some (← splitText sn r.start.offset)
  if ref == some node then ref := (← dom).nextSibling node
  if ((← dom).get node).parent.isSome then removeNode node
  let d ← dom
  let newOffset := (match ref with | none => nodeLength d parent | some k => indexOf d k) +
    (if (d.get node).type == .fragment then nodeLength d node else 1)
  exec (match ref with | none => .appendChild parent node | some k => .insertBefore parent node (some k))
  let r ← getRange rid
  if r.collapsed then setRange rid { r with stop := ⟨parent, newOffset⟩ }

/-- `surroundContents(newParent)` (DOM §5.5). -/
def surroundContents (rid np : Nat) : Op Unit := do
  let r ← getRange rid
  let d ← dom
  -- a non-Text node that is partially contained: an inclusive ancestor of one end only
  let ends := (chain d r.start.node) ++ (chain d r.stop.node)
  if ends.any (fun k => partiallyContained d r k && !Dom.isTextNode (d.get k)) then throw (-16)
  let t := (d.get np).type
  if t == .document || t == .doctype || t == .fragment then throw (-13)
  let frag ← extractContents rid
  if ((← dom).get np).kids.size > 0 then exec (.setTextContent np "")
  insertNode rid np
  append np frag
  setRange rid (← liftR (selectNode (← dom) np))

/-- `createContextualFragment(fragment)` (DOM Parsing, HTML document case). -/
def contextualFragment (rid : Nat) (src : String) : Op Nat := do
  let r ← getRange rid
  let d ← dom
  let sn := r.start.node
  let x := d.get sn
  let element : Option Nat :=
    if x.type == .element then some sn
    else if Dom.isTextNode x || x.type == .comment then (d.parentElement sn)
    else none
  let doc := docOf d sn
  let (ns, name) := match element with
    | some e =>
      let ex := d.get e
      if (d.get ex.doc).htmlDoc && ex.lname == "html" && ex.ns == some htmlNS then (htmlNS, "body")
      else (ex.ns.getD "", ex.lname)
    | none => (htmlNS, "body")
  make (.createNode (13 + 16 * doc) (ns ++ "\x00" ++ name ++ "\x00" ++ src))

/-! ## The selection (Selection API, w3c/selection-api) -/

/-- The document a selection belongs to: the page's (node 0). -/
def selectionDoc : Nat := 0

def setSelection (rid : Option Nat) (dir : Nat) : Op Unit :=
  modify fun s => { s with selection := rid, selDirection := dir }

/-- Anchor and focus of the selection's range: the start and end, swapped when backwards. -/
def anchorFocus (s : State) : Option (BP × BP) := do
  let rid ← s.selection
  let r ← (s.live.ranges[rid]?).join
  return if s.selDirection == 2 then (r.stop, r.start) else (r.start, r.stop)

/-- `collapse(node, offset)`: a new range at the point. -/
def selCollapse (node offset : Nat) : Op Unit := do
  let d ← dom
  liftR (checkPoint d node offset)
  if d.root node != selectionDoc then return
  let rid ← newRange ⟨⟨node, offset⟩, ⟨node, offset⟩⟩
  setSelection (some rid) 0

/-- `extend(node, offset)` (Selection API §2). -/
def selExtend (node offset : Nat) : Op Unit := do
  let s ← get
  let some (anchor, _) := anchorFocus s | throw (-16)
  let d ← dom
  if d.root node != selectionDoc then return
  liftR (checkPoint d node offset)
  let focus : BP := ⟨node, offset⟩
  let rng : Rng :=
    if d.root anchor.node != d.root node then ⟨focus, focus⟩
    else if position d anchor focus != .after then ⟨anchor, focus⟩ else ⟨focus, anchor⟩
  let rid ← newRange rng
  setSelection (some rid) (if d.root anchor.node == d.root node && position d focus anchor == .before then 2 else 1)

/-- `setBaseAndExtent(anchorNode, anchorOffset, focusNode, focusOffset)`. -/
def selSetBaseAndExtent (an ao fn fo : Nat) : Op Unit := do
  let d ← dom
  if ao > nodeLength d an || fo > nodeLength d fn then throw (-14)
  if d.root an != selectionDoc || d.root fn != selectionDoc then return
  let a : BP := ⟨an, ao⟩
  let f : BP := ⟨fn, fo⟩
  let back := position d f a == .before
  let rid ← newRange (if back then ⟨f, a⟩ else ⟨a, f⟩)
  setSelection (some rid) (if back then 2 else 1)

/-- `containsNode(node, allowPartialContainment)`. -/
def selContainsNode (s : State) (node : Nat) (partial_ : Bool) : Bool :=
  match s.selection.bind (fun k => (s.live.ranges[k]?).join) with
  | none => false
  | some r =>
    let d := s.dom
    if d.root node != selectionDoc || d.root r.start.node != d.root node then false else
    let first : BP := ⟨node, 0⟩
    let lastBP : BP := ⟨node, nodeLength d node⟩
    if partial_ then position d r.start lastBP != .after && position d r.stop first != .before
    else position d r.start first != .after && position d r.stop lastBP != .before

/-! ## The ops -/

/-- The ops that change the tree (`Hosts.Page` counts them as writes for layout reads). -/
def treeOps : List Nat := [112, 113, 114, 116, 119, 120, 149, 167]

def bpText (b : BP) : String := s!"{b.node} {b.offset}"

/-- The TreeWalker machine's answer: "d NODE" (or "d -1") when the method is done, else
"f NODE" and the machine's state, which the page gives back with the filter result. -/
def askText : Traversal.Ask → String
  | .done (some n) => s!"d {n}"
  | .done none => "d -1"
  | .filter w n =>
    let m := match w.method with
      | .parentNode => 0 | .firstChild => 1 | .lastChild => 2 | .previousSibling => 3
      | .nextSibling => 4 | .previousNode => 5 | .nextNode => 6
    s!"f {n} {m} {w.root} {w.whatToShow} {w.current} {w.node} {w.at_}"

/-- Op `op` of `node_query` from 100, on the node or range number `id`, with argument `q`.

Ranges: 100 a new range of document `id` (its number); 101 the range: "startNode
startOffset endNode endOffset"; 102 set the start (`q` "1 node offset") or the end ("0 node
offset"); 103 `setStartBefore`, `setStartAfter`, `setEndBefore`, `setEndAfter` ("which
node", which 0 to 3); 104 `collapse` ("1" to the start); 105 `selectNode` ("0 node") or
`selectNodeContents` ("1 node"); 106 `compareBoundaryPoints` ("how sourceRange"); 107
`comparePoint` ("node offset"); 108 `isPointInRange` ("node offset", "1" or "0"); 109
`intersectsNode` ("node"); 110 `commonAncestorContainer`; 111 the stringifier; 112
`deleteContents` ("0", answers ""), `extractContents` ("1") and `cloneContents` ("2")
(the fragment); 113 `insertNode` ("node"); 114 `surroundContents` ("node"); 115
`cloneRange` (the new range); 116 `createContextualFragment` (`q` the markup; the
fragment); 117 a new range with the boundary points of `q` ("sn so en eo", checked as
`setStart` then `setEnd`); 118 range `id` can no longer be reached by the page (its slot
is free; not the selection's range).

CharacterData: 119 `replaceData` of node `id` ("offset count" U+0000 data); 120
`splitText` ("offset"; the new node).

NodeIterator: 130 a new iterator of root `id` ("whatToShow"); 131 the next node to filter
("next node beforeNode", next 1 or 0; "node beforeNode", or -1 none); 132 set the
reference ("node beforeNode"); 133 the reference ("node beforeNode"); 136 the node being
filtered ("node beforeNode", or "" for none); 137 it was accepted: it becomes the reference.
TreeWalker: 134 start method ("method root whatToShow", from current node `id`); 135 go on
("method root whatToShow current node at result") (`askText`).

Reflection (`DOM.Reflect`): 160 the getter of a row on element `id` ("row", and for a URL
U+0000 the document's URL); 161 the setter's decision ("row" U+0000 the converted value); 162 the rows
of the interface named `q`; 165 `CSS.supports` ("1" U+0000 property U+0000 value, or "0" U+0000 condition
text; "1" or "0"); 166 `CSS.escape`; 167 a reflected setter applied ("row" U+0000 the
converted value): the content attribute is set or removed by a command.

Selection: 140 "range direction", or -1 when empty; 141 `addRange` (range `id`); 142
`removeRange` (range `id`; -9 when it is not the selection's); 143 `removeAllRanges`; 144
`collapse` ("node offset"); 145 `collapseToStart` ("1") and `collapseToEnd` ("0"); 146
`extend` ("node offset"); 147 `setBaseAndExtent` ("an ao fn fo"); 148 `selectAllChildren`
("node"); 149 `deleteFromDocument`; 150 `containsNode` ("node partial", "1" or "0").

DOM and HTML decisions (read-only): 180 the value of the Window's named property `q` for
document `id` (`DOM.Named.answer`: "", "w" container, "e" element, or "c" elements); 181
whether `q` is a valid custom element name ("1" or "0"); 182 the elements a tree change at
node `id` reaches, in shadow-including tree order (`DOM.CustomElements`); 183 the kind of
script element `id` (`HTML.ScriptType`: "classic", "module", "importmap" or "data"); 184 the
element and 185 the elements that a reflecting IDL attribute of element `id` answers
(`DOM.ElementRef`: `q` is the content attribute, U+0000, the explicitly set element or
elements); 186 form owner, form elements, options, selected options, labels, labeled control
and selectedness (`DOM.FormControls.answer`); 187 the range and selection of `setRangeText`
(`HTML.TextSelection.answer`); 188 an input's typed value and constraint validation
(`DOM.FormValidity.answer`); 189 the node that `focus()` focuses (`DOM.Focus.answer`); 191
the text of `innerText` for collected items (`HTML.InnerText.answer`). -/
def domOpM (id op : Nat) (q : String) : Op String := do
  let xs := nums q
  let d ← dom
  match op with
  | 100 =>
    if id ≥ d.size || (d.get id).type != .document then throw (-2)
    return toString (← newRange ⟨⟨id, 0⟩, ⟨id, 0⟩⟩)
  | 101 => let r ← getRange id; return s!"{bpText r.start} {bpText r.stop}"
  | 102 =>
    let r ← getRange id
    let n ← nodeArg d (num xs 1)
    setRange id (← liftR (setBoundary d r n (num xs 2).toNat (num xs 0 == 1)))
    return ""
  | 103 =>
    let r ← getRange id
    let n ← nodeArg d (num xs 1)
    setRange id (← liftR (setRelative d r n (num xs 0).toNat))
    return ""
  | 104 =>
    let r ← getRange id
    setRange id (if q == "1" then ⟨r.start, r.start⟩ else ⟨r.stop, r.stop⟩)
    return ""
  | 105 =>
    let _ ← getRange id
    let n ← nodeArg d (num xs 1)
    setRange id (← liftR (if num xs 0 == 1 then selectNodeContents d n else selectNode d n))
    return ""
  | 106 =>
    let r ← getRange id
    let src ← getRange (num xs 1).toNat
    return toString (← liftR (compareBoundaryPoints d r (num xs 0).toNat src))
  | 107 =>
    let r ← getRange id
    let n ← nodeArg d (num xs 0)
    return toString (← liftR (comparePoint d r n (num xs 1).toNat))
  | 108 =>
    let r ← getRange id
    let n ← nodeArg d (num xs 0)
    return if (← liftR (isPointInRange d r n (num xs 1).toNat)) then "1" else "0"
  | 109 =>
    let r ← getRange id
    let n ← nodeArg d (num xs 0)
    return if intersectsNode d r n then "1" else "0"
  | 110 => let r ← getRange id; return toString (commonAncestor d r)
  | 111 => let r ← getRange id; return toText d r
  | 112 =>
    let r ← getRange id
    match q with
    | "0" => deleteContents id; return ""
    | "1" => return toString (← extractContents id)
    | _ => return toString (← cloneR (d.size + 1) r)
  | 113 => let n ← nodeArg d (num xs 0); insertNode id n; return ""
  | 114 => let n ← nodeArg d (num xs 0); surroundContents id n; return ""
  | 115 => let r ← getRange id; return toString (← newRange r)
  | 116 => return toString (← contextualFragment id q)
  | 118 =>
    -- the page can no longer reach range `id` (its object was collected); the selection's
    -- range stays
    if (← get).selection != some id then modify fun s => { s with live := s.live.release id }
    return ""
  | 117 =>
    let sn ← nodeArg d (num xs 0)
    let en ← nodeArg d (num xs 2)
    let r0 : Rng := ⟨⟨sn, 0⟩, ⟨sn, 0⟩⟩
    let r1 ← liftR (setBoundary d r0 sn (num xs 1).toNat true)
    let r2 ← liftR (setBoundary d r1 en (num xs 3).toNat false)
    return toString (← newRange r2)
  | 119 =>
    let n ← nodeArg d id
    match q.splitOn "\x00" with
    | [a, data] =>
      let ys := nums a
      replaceData n (num ys 0).toNat (num ys 1).toNat data
      return ""
    | _ => throw (-2)
  | 120 => let n ← nodeArg d id; return toString (← splitText n (num xs 0).toNat)
  | 130 =>
    let n ← nodeArg d id
    let s ← get
    if s.live.ranges.size + s.live.iters.size ≥ maxLive then throw (-5)
    let it : Traversal.Iter := { root := n, reference := n, whatToShow := (num xs 0).toNat }
    set { s with live := { s.live with iters := s.live.iters.push it } }
    return toString s.live.iters.size
  | 131 =>
    let some it := (← get).live.iters[id]? | throw (-2)
    let n ← nodeArg d (num xs 1)
    match Traversal.iterMove d it n (num xs 2 == 1) (num xs 0 == 1) with
    | some (k, b) => return s!"{k} {if b then 1 else 0}"
    | none => throw (-1)
  | 132 =>
    let s ← get
    let some it := s.live.iters[id]? | throw (-2)
    let n ← nodeArg d (num xs 0)
    let it' := { it with reference := n, beforeRef := num xs 1 == 1 }
    set { s with live := { s.live with iters := s.live.iters.set! id it' } }
    return ""
  | 133 =>
    let some it := (← get).live.iters[id]? | throw (-2)
    return s!"{it.reference} {if it.beforeRef then 1 else 0}"
  | 136 =>
    -- the node being filtered ("node beforeNode"), or none ("")
    let s ← get
    let some it := s.live.iters[id]? | throw (-2)
    let cand := match nums q with
      | #[k, b] => if k ≥ 0 then some (k.toNat, b == 1) else none
      | _ => none
    set { s with live := { s.live with iters := s.live.iters.set! id { it with cand } } }
    return ""
  | 137 =>
    -- the node being filtered was accepted: it becomes the reference, as the removals during
    -- its filtering left it
    let s ← get
    let some it := s.live.iters[id]? | throw (-2)
    let it' := match it.cand with
      | some (k, b) => { it with reference := k, beforeRef := b, cand := none }
      | none => it
    set { s with live := { s.live with iters := s.live.iters.set! id it' } }
    return ""
  | 134 =>
    let cur ← nodeArg d id
    let root ← nodeArg d (num xs 1)
    return askText (Traversal.start d (Traversal.Method.ofNat (num xs 0).toNat) root (num xs 2).toNat cur)
  | 135 =>
    let w : Traversal.Walk := {
      method := Traversal.Method.ofNat (num xs 0).toNat
      root := (num xs 1).toNat
      whatToShow := (num xs 2).toNat
      current := (num xs 3).toNat
      node := (num xs 4).toNat
      at_ := (num xs 5).toNat }
    if w.root ≥ d.size || w.current ≥ d.size || w.node ≥ d.size then throw (-2)
    return askText (Traversal.run d w (num xs 6).toNat)
  | 140 =>
    let s ← get
    match s.selection with
    | some r => return s!"{r} {s.selDirection}"
    | none => throw (-1)
  | 141 =>
    let r ← getRange id
    if (← get).selection.isNone && d.root r.start.node == selectionDoc then setSelection (some id) 0
    return ""
  | 142 => if (← get).selection == some id then setSelection none 0; return "" else throw (-9)
  | 143 => setSelection none 0; return ""
  | 144 =>
    let n ← nodeArg d (num xs 0)
    selCollapse n (num xs 1).toNat
    return ""
  | 145 =>
    let s ← get
    let some rid := s.selection | throw (-16)
    let r ← getRange rid
    let p := if q == "1" then r.start else r.stop
    let nr ← newRange ⟨p, p⟩
    setSelection (some nr) 0
    return ""
  | 146 => let n ← nodeArg d (num xs 0); selExtend n (num xs 1).toNat; return ""
  | 147 =>
    let an ← nodeArg d (num xs 0)
    let fn ← nodeArg d (num xs 2)
    selSetBaseAndExtent an (num xs 1).toNat fn (num xs 3).toNat
    return ""
  | 148 =>
    let n ← nodeArg d (num xs 0)
    if (d.get n).type == .doctype then throw (-13)
    if d.root n != selectionDoc then return ""
    let rid ← newRange ⟨⟨n, 0⟩, ⟨n, (d.get n).kids.size⟩⟩
    setSelection (some rid) 1
    return ""
  | 149 =>
    match (← get).selection with
    | some rid => deleteContents rid; return ""
    | none => return ""
  | 150 =>
    let n ← nodeArg d (num xs 0)
    return if selContainsNode (← get) n (num xs 1 == 1) then "1" else "0"
  | 160 =>
    -- a reflected IDL attribute's getter (`DOM.Reflect.get`): "row" U+0000 the document's URL
    let n ← nodeArg d id
    let (row, base) := match q.splitOn "\x00" with
      | [row, base] => (row, base)
      | _ => (q, "")
    match row.toNat?.bind (L4Factoidal.DOM.Reflect.table[·]?) with
    | some r => return L4Factoidal.DOM.Reflect.get d n r base
    | none => throw (-2)
  | 161 =>
    -- its setter (`DOM.Reflect.set`): "row" U+0000 the converted value
    match q.splitOn "\x00" with
    | row :: rest =>
      match row.toNat?.bind (L4Factoidal.DOM.Reflect.table[·]?) with
      | some r => match L4Factoidal.DOM.Reflect.set r ("\x00".intercalate rest) with
        | .ok a => return a
        | .error e => throw e
      | none => throw (-2)
    | [] => throw (-2)
  | 162 => return L4Factoidal.DOM.Reflect.rowsOf q
  | 165 =>
    -- `CSS.supports`: "1" U+0000 property U+0000 value, or "0" U+0000 condition text
    match q.splitOn "\x00" with
    | ["1", p, v] => return if L4Factoidal.Rendering.CSS.supportsDeclaration p v then "1" else "0"
    | "0" :: rest => return if L4Factoidal.Rendering.CssSupports.supportsText ("\x00".intercalate rest) then "1" else "0"
    | _ => throw (-2)
  | 166 => return L4Factoidal.Rendering.CssSupports.escape q
  | 151 =>
    -- the style declaration block of a page's CSSStyleDeclaration (CSSOM §6.6), as text
    -- operations on the `style` attribute's value (`CssValues.styleOp`)
    return L4Factoidal.Rendering.CssValues.styleOp q
  | 152 =>
    -- the property names of a computed style (`ComputedGeneric.namesText`): the page
    -- reads the value of the k-th name with measure op 200 + k
    return L4Factoidal.Rendering.ComputedGeneric.namesText
  | 153 =>
    -- the rules of a style sheet text and its changes (CSSOM §6.4, `CssSheet.sheetOp`)
    return L4Factoidal.Rendering.CssSheet.sheetOp q
  | 154 =>
    -- CSS Typed OM: reification, serialisation, numeric types and arithmetic (`CssTyped.typedOp`)
    return L4Factoidal.Rendering.CssTyped.typedOp q
  | 167 =>
    -- a reflected attribute's setter, applied: the decision of 161, then the content
    -- attribute set or removed as a command (the page has no MutationObserver and the row
    -- is not a URL)
    let n ← nodeArg d id
    match q.splitOn "\x00" with
    | row :: rest =>
      match row.toNat?.bind (L4Factoidal.DOM.Reflect.table[·]?) with
      | some r =>
        if (d.get n).type != .element then throw (-2)
        match L4Factoidal.DOM.Reflect.set r ("\x00".intercalate rest) with
        | .ok a =>
          if a == "r" then
            if (L4Factoidal.DOM.Reflect.attr d n r.content).isSome then exec (.removeAttribute n r.content)
          else if a != "" then
            let v := (a.drop 1).toString
            if L4Factoidal.DOM.Reflect.attr d n r.content != some v then exec (.setAttribute n r.content v)
          return ""
        | .error e => throw e
      | none => throw (-2)
    | [] => throw (-2)
  -- ==== encoding100: form submission and frame document URLs ====
  | 170 =>
    -- the form submission algorithm of form `id` (HTML.FormSubmission.plan): "submitter
    -- U+0000 document encoding label" (submitter "" for `form.submit()`); a GET navigation
    -- of a frame is queued for the embedder. "1" when a navigation was queued, "0" when the
    -- submission navigates nowhere here.
    let (sub, label) := match q.splitOn "\x00" with
      | [a, b] => (a, b)
      | _ => (q, "")
    let form ← nodeArg d id
    if !L4Factoidal.DOM.Forms.isHtml d form ["form"] then throw (-2)
    let submitter := sub.toNat?.filter (· < d.size)
    let st ← get
    let doc := (d.get form).doc
    -- the form's document must be the page's or a frame's (it has a browsing context)
    let docEl := (st.frames.find? (·.2 == doc)).map (·.1)
    if doc != 0 && docEl.isNone then return "0"
    -- HTML §4.10.21.3 step 3: a sandboxed document's forms do not submit
    if let some el := docEl then
      if !(elementFrame st el).formsMaySubmit then return "0"
    let docURL := if doc == 0 then st.url else ((st.docURLs.find? (·.1 == doc)).map (·.2)).getD "about:blank"
    let frameLabel := match docEl with
      | some el => ((st.frameEncodings.find? (·.1 == el)).map (·.2)).getD label
      | none => label
    let enc := (L4Factoidal.WHATWG.Encoding.getEncoding frameLabel).getD .utf_8
    let baseTarget := (((d.treeOrder doc).find? fun k => L4Factoidal.DOM.Forms.isHtml d k ["base"] &&
      (L4Factoidal.DOM.Forms.attr? d k "target").isSome).bind (L4Factoidal.DOM.Forms.attr? d · "target")).getD ""
    match L4Factoidal.HTML.FormSubmission.plan d form submitter docURL enc baseTarget with
    | none => return "0"
    | some p =>
      -- the rules for choosing a navigable: "" and `_self` the form's own frame; a name, the
      -- first frame of that name. The page itself, `_parent`, `_top` and `_blank` would leave
      -- or open a top-level document: not done here.
      let tl := L4Factoidal.DOM.Dom.asciiLower p.target
      let target := if tl == "" || tl == "_self" then docEl
        else if tl.startsWith "_" then none
        else (st.frames.find? fun (fr : Nat × Nat) => attrValue? d fr.1 "name" == some p.target).map (·.1)
      match target with
      | none => return "0"
      | some el =>
        let u := if st.hostLoads then p.url else ""
        set { st with navigations := (st.navigations.filter fun (nv : Nat × String) => nv.1 != el).push (el, u) }
        return "1"
  | 171 =>
    -- the URL of document `id`: the page's, or a frame document the page may reach
    if id == 0 then return (← get).url
    let st ← get
    match st.frames.find? (·.2 == id) with
    | some (el, _) =>
      if !frameAccessible st el then throw (-2)
      return ((st.docURLs.find? (·.1 == id)).map (·.2)).getD "about:blank"
    | none => throw (-2)
  | 172 =>
    -- the encoding name of frame document `id` the page may reach (`characterSet`), as the
    -- embedder's decode named it; UTF-8 when it did not say
    let st ← get
    match st.frames.find? (·.2 == id) with
    | some (el, _) =>
      if !frameAccessible st el then throw (-2)
      let e := ((st.frameEncodings.find? (·.1 == el)).map (·.2)).bind L4Factoidal.WHATWG.Encoding.getEncoding
      return (e.getD .utf_8).name
    | none => throw (-2)
  -- ==== end of encoding100 ====
  -- ==== domhtml (ops 180 to 199): decisions of DOM and HTML features, read-only ====
  -- 180: named access on the Window object (HTML §7.3.3, `DOM.Named.answer`): the value of
  -- the named property `q` of the Window of document `id`
  | 180 => return L4Factoidal.DOM.Named.answer d id q
  -- 181: whether `q` is a valid custom element name (HTML §4.13.3, `DOM.CustomElements.validName`)
  | 181 => return if L4Factoidal.DOM.CustomElements.validName q then "1" else "0"
  -- 182: the elements a tree change at node `id` reaches, in shadow-including tree order
  -- (`DOM.CustomElements.reach`)
  | 182 =>
    let n ← nodeArg d id
    return L4Factoidal.DOM.CustomElements.reachWire d n
  -- 183: the kind of script element `id` (HTML §4.12.1 steps 8 to 12, `HTML.ScriptType.kind`):
  -- "classic", "module", "importmap" or "data"; the `language` of an SVG script has no say
  | 183 =>
    let n ← nodeArg d id
    let x := d.get n
    let av := fun (nm : String) => (x.attrs.find? fun a => a.ns.isNone && a.lname == nm).map (·.value)
    return (L4Factoidal.HTML.ScriptType.kind (av "type") (if x.ns == some htmlNS then av "language" else none)).name
  -- 184 and 185: an IDL attribute that reflects an element or a list of elements (HTML §2.6.1,
  -- `DOM.ElementRef`): `q` is the content attribute's name, U+0000, and the explicitly set
  -- element (184) or elements, "-" for none (185)
  | 184 =>
    let n ← nodeArg d id
    return L4Factoidal.DOM.ElementRef.answerOne d n q
  | 185 =>
    let n ← nodeArg d id
    return L4Factoidal.DOM.ElementRef.answerMany d n q
  -- 186: form controls (`DOM.FormControls.answer`): `q` "f" the form owner of `id`, "e" the
  -- elements of form `id`, "o" the options of select `id`, "s" its selected options, "l" the
  -- labels of `id`, "c" the labeled control of label `id`, "x" the selectedness of option `id`
  | 186 =>
    let n ← nodeArg d id
    return L4Factoidal.DOM.FormControls.answer d n q
  -- 187: `setRangeText` (`HTML.TextSelection.answer`): `q` "len start end selStart selEnd
  -- newLen mode"; the replaced range and the selection after
  | 187 => return L4Factoidal.HTML.TextSelection.answer q
  -- 188: the typed value of an input and constraint validation (`DOM.FormValidity.answer`):
  -- `q` is a letter and U+0000-separated arguments (sanitized value, value as number or date
  -- and back, stepUp and stepDown, validity bits, willValidate)
  | 188 =>
    let n ← nodeArg d id
    return L4Factoidal.DOM.FormValidity.answer d n q
  -- 189: the node that `focus()` on element `id` focuses, or with `q` "d" its focus delegate
  -- (`DOM.Focus.answer`); "" for none
  | 189 =>
    let n ← nodeArg d id
    return L4Factoidal.DOM.Focus.answer d n q
  -- 191: the text of `innerText` for the collected items `q` (`HTML.InnerText.answer`)
  | 191 => return L4Factoidal.HTML.InnerText.answer q
  -- ==== end of domhtml ====
  | _ => throw (-2)

/-! ## Editing (W3C Editing APIs draft; the algorithms are `DOM.Editing`)

`node_query` ops 175 to 177, served by `editOp` (`Hosts.Page` gives it the text of the
page's style sheets, which the editing algorithms read styles from).

175 `execCommand`: `q` is the command, U+0000, the value; "1" or "0". The algorithm runs on
the arena as a pure function and logs its primitive changes (`Editing.Prim`); each one is
then run here as a typed command (`exec`), so it is recorded, the layout replay sees it and
the page's live ranges move. The selection's range becomes the active range the algorithm
left.

176 the queries: `q` is "e" (enabled), "i" (indeterminate), "s" (state), "u" (supported) or
"v" (value), U+0000, the command; "1" or "0", or the value.

177 on node `id`: `q` "c" the `contentEditable` state of the element; "i" `isContentEditable`
("1" or "0"); "d" the design mode ("on" or "off"); "d1" and "d0" set it; "f" `focus()` of
an editing host (the selection moves into it).

The answer of 175 for a command that fires `input` is "1", U+0000, the editing host, U+0000,
the `inputType`, and U+0000 and the `data` when there is one. -/

/-- The ops of `editOp`. -/
def editOps : List Nat := [175, 176, 177]

/-- The declarations the page's style sheets give element `n`, lowest priority first: the
author rules that match it (`Rendering.CSS.matchedRules`), ordered by importance,
specificity and source order (CSS Cascade 4 §6.1). The user agent's rules are not here:
`Editing.uaDecls` has the defaults that editing reads. -/
def editSheet (rules : List L4Factoidal.Rendering.CSS.Rule) (d : Dom) (n : Nat) : L4Factoidal.DOM.Editing.Decls := Id.run do
  if rules.isEmpty then return []
  let mut out : Array (List Nat × String × String) := #[]
  let mut order := 0
  for (origin, rule, matched) in L4Factoidal.Rendering.CSS.matchedRules d n rules do
    if origin == 1 then
      let spec := matched.foldl (fun (m : Nat × Nat × Nat) sel =>
        if m.1 < sel.specificity.1 || (m.1 == sel.specificity.1 && (m.2.1 < sel.specificity.2.1 ||
            (m.2.1 == sel.specificity.2.1 && m.2.2 ≤ sel.specificity.2.2))) then sel.specificity else m) (0, 0, 0)
      for dcl in rule.declarations do
        out := out.push ([if dcl.important then 1 else 0, spec.1, spec.2.1, spec.2.2, order], dcl.property, dcl.value)
        order := order + 1
  let le := fun (a b : List Nat × String × String) => !(decide (b.1 < a.1))
  return ((out.toList.mergeSort le).map fun (_, p, v) => (p, v))

/-- A primitive change of the editing algorithms as a typed command. -/
def primCommand (doc : Nat) : L4Factoidal.DOM.Editing.Prim → Command
  | .createElement name r => .createNode (3 + 16 * doc) name r
  | .createText data r => .createNode (16 * doc) data r
  | .insertBefore parent node child => .insertBefore parent node child
  | .remove parent node => .removeChild parent node
  | .setAttr node name value => .setAttribute node name value
  | .removeAttr node name => .removeAttribute node name
  | .replaceData node offset count data => .replaceData node offset count data
  | .splitText node offset r => .splitText node offset r
  | .cloneNode node deep r => .cloneNode node deep r
  | .createFragment r => .createNode (2 + 16 * doc) "" r
  | .parseFragment ns name src r => .createNode (13 + 16 * doc) (ns ++ "\x00" ++ name ++ "\x00" ++ src) r

/-- Run an editing program on the page: the arena, the selection's range and the
document's editing flags go in; the program's changes are run as typed commands, and its
active range and flags are kept. -/
def editRun {α : Type} (sheet : String) (prog : L4Factoidal.DOM.Editing.M α) : Op α := do
  let s ← get
  let rules := if sheet.isEmpty then [] else
    ((L4Factoidal.Rendering.CSS.parseIn { medium := "screen" } sheet).toOption).getD []
  let sel := s.selection.bind fun k => (s.live.ranges[k]?).join
  let ed := L4Factoidal.DOM.Editing.Ed.start s.dom sel s.edit { sheet := editSheet rules }
  let (a, ed) := prog.run ed
  let log := ed.log
  let size := ed.dom.size
  let active := (ed.live.ranges[0]?).join
  let flags := ed.flags
  for p in log do
    match p with
    | .createElement _ r | .createText _ r | .splitText _ _ r | .cloneNode _ _ r | .createFragment r =>
      if r != (← dom).size then throw (-5)
    | _ => pure ()
    exec (primCommand 0 p)
  if !log.isEmpty && (← dom).size != size then throw (-5)
  match active with
  | some r =>
    match (← get).selection with
    | some k => if (← getRange k) != r then setRange k r
    | none =>
      let rid ← newRange r
      setSelection (some rid) 1
  | none => if sel.isSome then setSelection none 0
  modify fun s => { s with edit := flags }
  return a

def editOpM (sheet : String) (id op : Nat) (q : String) : Op String := do
  let b := fun (v : Bool) => if v then "1" else "0"
  match op with
  | 175 =>
    match q.splitOn "\x00" with
    | command :: rest =>
      let (ok, ev) ← editRun sheet (L4Factoidal.DOM.Editing.execCommandWithEvent command ("\x00".intercalate rest))
      match ev with
      | some (host, inputType, data) =>
        return b ok ++ "\x00" ++ toString host ++ "\x00" ++ inputType ++ (match data with
          | some v => "\x00" ++ v
          | none => "")
      | none => return b ok
    | [] => return "0"
  | 176 =>
    match q.splitOn "\x00" with
    | [which, command] =>
      let command := L4Factoidal.DOM.Editing.lower command
      match which with
      | "e" => return b (← editRun sheet (L4Factoidal.DOM.Editing.queryEnabled command))
      | "i" => return b (← editRun sheet (L4Factoidal.DOM.Editing.queryIndeterm command))
      | "s" => return b (← editRun sheet (L4Factoidal.DOM.Editing.queryState command))
      | "u" => return b (L4Factoidal.DOM.Editing.isSupported command)
      | "v" => editRun sheet (L4Factoidal.DOM.Editing.queryValue command)
      | _ => throw (-2)
    | _ => throw (-2)
  | 177 =>
    let s ← get
    let d := s.dom
    let ed := L4Factoidal.DOM.Editing.Ed.start d none s.edit {}
    match q with
    | "c" => if id < d.size && (d.get id).type == .element then return L4Factoidal.DOM.Editing.contentEditable d id else throw (-2)
    | "i" => return b (id < d.size && (L4Factoidal.DOM.Editing.isEditable ed id || L4Factoidal.DOM.Editing.isEditingHost ed id))
    | "d" => return if s.edit.design then "on" else "off"
    | "d1" => set { s with edit := { s.edit with design := true } }; return ""
    | "d0" => set { s with edit := { s.edit with design := false } }; return ""
    | "f" =>
      -- `focus()` of an editing host: the selection moves into it (a caret at its start)
      -- unless it is in it already
      if id ≥ d.size || !L4Factoidal.DOM.Editing.isEditingHost ed id then return ""
      let inside := match s.selection.bind fun k => (s.live.ranges[k]?).join with
        | some r => d.isInclusiveAncestor id r.start.node
        | none => false
      if inside then return ""
      let r : Rng := ⟨⟨id, 0⟩, ⟨id, 0⟩⟩
      match s.selection with
      | some k => setRange k r
      | none =>
        let rid ← newRange r
        setSelection (some rid) 1
      return ""
    | _ => throw (-2)
  | _ => throw (-2)

/-- Run editing op `op` with the text of the page's style sheets. -/
def editOp (s : State) (sheet : String) (id op : Nat) (q : String) : State × Except Int String :=
  match (editOpM sheet id op q).run s with
  | .ok (a, s') => (s', .ok a)
  | .error e => (s, .error e)

/-- Run op `op`: the state after it (unchanged when it throws) and the answer. -/
def domOp (s : State) (id op : Nat) (q : String) : State × Except Int String :=
  match (domOpM id op q).run s with
  | .ok (a, s') => (s', .ok a)
  | .error e => (s, .error e)

end L4Factoidal.WasmVM.Hosts.Dom
