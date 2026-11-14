/-
L4Factoidal.DOM.Editing.Core — the state, the primitive changes and the common
definitions of the editing algorithms.

Specification: the W3C Editing APIs draft ("execCommand"), the sections "Common
definitions" and "Common algorithms"; the Web Platform Tests keep a reference
implementation of it (`editing/include/implementation.js`), and each function here names
the definition of the draft it follows.

The algorithms are pure: an `Ed` holds the arena, the live ranges (slot 0 is the active
range), the editing flags, and the log of the primitive changes made (`Prim`). The host
(`WasmVM.Hosts`) replays the log as its typed DOM commands, so the page's arena, its
layout replay and its other live ranges see the same changes.

Safety by construction: every change of the arena goes through `applyPrim`, which does
nothing unless each node the change touches is detached from a document or is inside an
editing host (`permitted`). `applyPrim_refused` states it.

"Collapsed line break" and "extraneous line break" are defined by layout in the draft (a
`br` that begins an empty line box; a `br` whose removal changes no layout). Here they are
decided on the tree: a `br` is a collapsed line break when no inline content follows it in
its block, and extraneous when, in addition, inline content precedes it on its line.
-/
import L4Factoidal.DOM.Editing.Style
import L4Factoidal.DOM.Live
import L4Factoidal.DOM.Fragment

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-- One primitive change of the arena. A node a change makes is the next node of the
arena (`result`), so a replay over the same arena makes the same node numbers. -/
inductive Prim where
  | createElement (name : String) (result : NodeId)
  | createText (data : String) (result : NodeId)
  /-- `parent.insertBefore(node, child)`. -/
  | insertBefore (parent node : NodeId) (child : Option NodeId)
  /-- `node.remove()`. -/
  | remove (parent node : NodeId)
  | setAttr (node : NodeId) (name value : String)
  | removeAttr (node : NodeId) (name : String)
  /-- "Replace data" (DOM §4.10) in UTF-16 code units. -/
  | replaceData (node offset count : Nat) (data : String)
  | splitText (node offset : Nat) (result : NodeId)
  | cloneNode (node : NodeId) (deep : Bool) (result : NodeId)
  /-- A new, empty DocumentFragment. -/
  | createFragment (result : NodeId)
  /-- The DocumentFragment that the HTML fragment parsing algorithm makes of `src` for a
  context element (`DOM.Fragment.parseInto`). -/
  | parseFragment (ns name src : String) (result : NodeId)
  deriving BEq, Repr, Inhabited

/-- The editing state. -/
structure Ed where
  dom : Dom
  /-- Slot 0 is the active range; the others are ranges an algorithm keeps for itself. -/
  live : Live.Live := {}
  log : Array Prim := #[]
  /-- The document of the active range. -/
  doc : NodeId := 0
  /-- The CSS styling flag (`styleWithCSS`). -/
  css : Bool := false
  /-- The default single-line container name (`defaultParagraphSeparator`). -/
  sep : String := "div"
  /-- The design mode of the document is enabled. -/
  design : Bool := false
  stateOv : List (String × Bool) := []
  valueOv : List (String × String) := []
  /-- The active range for which the overrides were set. -/
  ovRange : Option Rng := none
  /-- The range the command deletes first ("delete the selection" notes it): the target
  range of the command's `beforeinput` event (Input Events §4.1.2 `getTargetRanges()`). -/
  target : Option Rng := none
  env : Env := {}

instance : Inhabited Ed := ⟨{ dom := {} }⟩

/-- The editing state a document keeps between commands. -/
structure Flags where
  css : Bool := false
  sep : String := "div"
  design : Bool := false
  stateOv : List (String × Bool) := []
  valueOv : List (String × String) := []
  ovRange : Option Rng := none
  deriving Inhabited

def Ed.flags (e : Ed) : Flags :=
  { css := e.css, sep := e.sep, design := e.design, stateOv := e.stateOv, valueOv := e.valueOv, ovRange := e.ovRange }

/-- The editing state of a command: the arena, the selection's range (or none), the
document's flags and the style sheets' declarations. -/
def Ed.start (d : Dom) (sel : Option Rng) (f : Flags) (env : Env) : Ed :=
  { dom := d, live := { ranges := #[sel] }, css := f.css, sep := f.sep, design := f.design,
    stateOv := f.stateOv, valueOv := f.valueOv, ovRange := f.ovRange, env }

abbrev M := StateM Ed

/-- Read the state with a pure function (the snapshot is dropped at once). -/
@[inline] def rd {α : Type} (f : Ed → α) : M α := do return f (← get)

/-! ## Tree reading -/

def isEl (d : Dom) (n : NodeId) : Bool := (d.get n).type == .element
def isText (d : Dom) (n : NodeId) : Bool := (d.get n).type == .text
def parentOf (d : Dom) (n : NodeId) : Option NodeId := (d.get n).parent
def kidsOf (d : Dom) (n : NodeId) : Array NodeId := (d.get n).kids
def firstChild (d : Dom) (n : NodeId) : Option NodeId := (d.get n).kids[0]?
def lastChild (d : Dom) (n : NodeId) : Option NodeId := (d.get n).kids.back?
def hasKids (d : Dom) (n : NodeId) : Bool := !(d.get n).kids.isEmpty

/-- An HTML element (any name). -/
def isHtmlEl (d : Dom) (n : NodeId) : Bool :=
  (d.get n).type == .element && (d.get n).ns == some htmlNS

/-- An HTML element with one of the names. -/
def isHtml (d : Dom) (n : NodeId) (tags : List String) : Bool :=
  isHtmlEl d n && tags.contains (d.get n).lname

def isHtmlO (d : Dom) (n : Option NodeId) (tags : List String) : Bool :=
  match n with
  | some n => isHtml d n tags
  | none => false

/-- The local name of an HTML element, "" for another node. -/
def tagOf (d : Dom) (n : NodeId) : String := if isHtmlEl d n then (d.get n).lname else ""

def attr (d : Dom) (n : NodeId) (name : String) : Option String := attrOf (d.get n) name
def hasAttr (d : Dom) (n : NodeId) (name : String) : Bool := (attr d n name).isSome
def attrCount (d : Dom) (n : NodeId) : Nat := (d.get n).attrs.size

/-- The next node in tree order that is not a descendant of `n`. -/
def nextNodeDesc (d : Dom) (n : NodeId) : Option NodeId := Id.run do
  let mut cur := n
  for _ in [0:d.size + 1] do
    match d.nextSibling cur with
    | some s => return some s
    | none =>
      match parentOf d cur with
      | some p => cur := p
      | none => return none
  return none

/-- The next node in tree order. -/
def nextNode (d : Dom) (n : NodeId) : Option NodeId :=
  match firstChild d n with
  | some c => some c
  | none => nextNodeDesc d n

/-- The deepest last descendant of `n` (`n` when it has no child). -/
def deepLast (d : Dom) (n : NodeId) : NodeId := Id.run do
  let mut cur := n
  for _ in [0:d.size + 1] do
    match lastChild d cur with
    | some c => cur := c
    | none => return cur
  return cur

/-- The previous node in tree order, stopping at a parent that is not an element. -/
def prevNode (d : Dom) (n : NodeId) : Option NodeId :=
  match d.previousSibling n with
  | some s => some (deepLast d s)
  | none =>
    match parentOf d n with
    | some p => if isEl d p then some p else none
    | none => none

/-- `a` is an ancestor of `n` (not `n` itself). -/
def isAncestor (d : Dom) (a n : NodeId) : Bool := a != n && d.isInclusiveAncestor a n

/-- `a` is before `b` in tree order; a missing `b` is after everything. -/
def isBefore (d : Dom) (a : Option NodeId) (b : Option NodeId) : Bool :=
  match a, b with
  | none, _ => false
  | some _, none => true
  | some a, some b => precedes d a b

def bpOf (n : NodeId) (o : Nat) : BP := ⟨n, o⟩

/-- The ancestors of `n`, nearest first. -/
def ancestors (d : Dom) (n : NodeId) : List NodeId := ((chain d n).toList.reverse).drop 1

/-! ## Editable nodes and editing hosts -/

/-- The `contentEditable` IDL value of an element: "true", "false", "plaintext-only" or
"inherit" (HTML §6.8.1). -/
def contentEditable (d : Dom) (n : NodeId) : String :=
  match attr d n "contenteditable" with
  | some v =>
    let v := lower v
    if v == "" || v == "true" then "true"
    else if v == "false" then "false"
    else if v == "plaintext-only" then "plaintext-only"
    else "inherit"
  | none => "inherit"

/-- "Editing host": an HTML element with `contenteditable` true (or plaintext-only), or a
child HTML element of a document in design mode. -/
def isEditingHost (e : Ed) (n : NodeId) : Bool :=
  isHtmlEl e.dom n &&
    (contentEditable e.dom n == "true" || contentEditable e.dom n == "plaintext-only" ||
      (e.design && match parentOf e.dom n with
        | some p => (e.dom.get p).type == .document
        | none => false))

/-- "Editable": not an editing host, not `contenteditable=false`, its parent an editing
host or editable, and an HTML element, an `svg` or `math` root, or a non-element child of
an HTML element. The walk up is bounded by `fuel`. -/
def isEditableF (e : Ed) : Nat → NodeId → Bool
  | 0, _ => false
  | fuel + 1, n =>
    let d := e.dom
    if isEditingHost e n then false
    else if isEl d n && contentEditable d n == "false" then false
    else match parentOf d n with
      | none => false
      | some p =>
        (isEditingHost e p || isEditableF e fuel p) &&
          (isHtmlEl d n ||
            (isEl d n && (d.get n).ns == some svgNS && (d.get n).lname == "svg") ||
            (isEl d n && (d.get n).ns == some mathmlNS && (d.get n).lname == "math") ||
            (!isEl d n && isHtmlEl d p))

def isEditable (e : Ed) (n : NodeId) : Bool := isEditableF e (e.dom.size + 1) n

def isEditableO (e : Ed) (n : Option NodeId) : Bool :=
  match n with
  | some n => isEditable e n
  | none => false

/-- "Editing host of" a node: itself when it is an editing host, the nearest ancestor
that is one when it is editable. -/
def editingHostOf (e : Ed) (n : NodeId) : Option NodeId :=
  if isEditingHost e n then some n
  else if isEditable e n then (ancestors e.dom n).find? (isEditingHost e)
  else none

def inSameEditingHost (e : Ed) (a b : NodeId) : Bool :=
  match editingHostOf e a with
  | some h => editingHostOf e b == some h
  | none => false

/-- Some inclusive ancestor of `n` is an editing host. -/
def inHost (e : Ed) (n : NodeId) : Bool := (chain e.dom n).any (isEditingHost e)

/-- `n` is in no document. -/
def detached (d : Dom) (n : NodeId) : Bool := (d.get (d.root n)).type != .document

/-! ## The primitive changes -/

/-- A node an editing change may touch: one in no document, or one inside an editing host. -/
def touchable (e : Ed) (n : NodeId) : Bool := detached e.dom n || inHost e n

/-- The change touches only nodes that are detached or inside an editing host, and keeps
the tree a tree. -/
def permitted (e : Ed) : Prim → Bool
  | .createElement _ _ => true
  | .createText _ _ => true
  | .cloneNode _ _ _ => true
  | .createFragment _ => true
  | .parseFragment _ _ _ _ => true
  | .insertBefore parent node child =>
    touchable e parent &&
      (match parentOf e.dom node with
        | some p => touchable e p
        | none => true) &&
      (e.dom.ensurePreInsertValidity node parent child []).isOk
  | .remove parent node => touchable e parent && parentOf e.dom node == some parent
  | .setAttr node _ _ => touchable e node && isEl e.dom node
  | .removeAttr node _ => touchable e node && isEl e.dom node
  | .replaceData node offset _ _ => touchable e node && Dom.isCharacterData (e.dom.get node) &&
      offset ≤ nodeLength e.dom node
  | .splitText node offset _ => touchable e node && Dom.isTextNode (e.dom.get node) &&
      offset ≤ nodeLength e.dom node

/-- The arena and live ranges after a change, with no check. -/
def runPrim (d : Dom) (lv : Live.Live) (doc : NodeId) : Prim → Dom × Live.Live
  | .createElement name _ => ((d.createElement doc name).1, lv)
  | .createText data _ => ((d.createTextNode doc data).1, lv)
  | .cloneNode node deep _ => ((d.cloneNode node deep).1, lv)
  | .createFragment _ => ((d.createDocumentFragment doc).1, lv)
  | .parseFragment ns name src _ => ((Fragment.parseInto d doc ns name src).1, lv)
  | .insertBefore parent node child => Live.preInsert d lv node parent child
  | .remove _ node => Live.remove d lv node
  | .setAttr node name value => ((d.setAttribute node name value).1, lv)
  | .removeAttr node name => (d.removeAttributeNS node none name, lv)
  | .replaceData node offset count data => Live.replaceData d lv node offset count data
  | .splitText node offset _ => let (d, lv, _) := Live.splitText d lv node offset; (d, lv)

/-- Make one change: nothing when it is not `permitted`; else the arena and the live
ranges change and the change is logged. -/
def applyPrim (e : Ed) (p : Prim) : Ed :=
  if permitted e p then
    let d := e.dom
    let lv := e.live
    let doc := e.doc
    let e := { e with dom := {}, live := {} }
    let (d, lv) := runPrim d lv doc p
    { e with dom := d, live := lv, log := e.log.push p }
  else e

/-- Safety, by construction. Says: a change that is not permitted (it touches a node that
is in a document and outside every editing host, or would break the tree) leaves the whole
editing state as it was, and logs nothing. Does not say: that a permitted change keeps
every node outside the editing host as it was (an insertion of a node moves that node;
`permitted` asks that its old parent is touchable too), nor anything about the host's
replay of the log. -/
theorem applyPrim_refused (e : Ed) (p : Prim) (h : permitted e p = false) : applyPrim e p = e := by
  simp [applyPrim, h]

/-- The guard, read off. Says: a permitted insertion goes into a parent that is in no
document or inside an editing host, a permitted removal comes out of such a parent, and a
permitted change of an attribute or of character data is of such a node. So no permitted
change has a node of the document outside every editing host as its place. Does not say:
that the inserted node itself came from inside the host (its old parent is checked by
`permitted` too, not stated here), nor that `touchable` survives later changes. -/
theorem permitted_touchable (e : Ed) :
    (∀ parent node child, permitted e (.insertBefore parent node child) = true → touchable e parent = true) ∧
    (∀ parent node, permitted e (.remove parent node) = true → touchable e parent = true) ∧
    (∀ node name value, permitted e (.setAttr node name value) = true → touchable e node = true) ∧
    (∀ node name, permitted e (.removeAttr node name) = true → touchable e node = true) ∧
    (∀ node offset count data, permitted e (.replaceData node offset count data) = true → touchable e node = true) ∧
    (∀ node offset r, permitted e (.splitText node offset r) = true → touchable e node = true) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [permitted]

/-- The log only grows, by at most one change per `applyPrim`. -/
theorem applyPrim_log (e : Ed) (p : Prim) :
    (applyPrim e p).log = e.log ∨ (applyPrim e p).log = e.log.push p := by
  unfold applyPrim
  split <;> simp

def prim (p : Prim) : M Unit := modify fun e => applyPrim e p

/-- A new HTML element (a `span` when the name is not a valid element name). -/
def createElement (name : String) : M NodeId := do
  let r ← rd fun e => e.dom.size
  let ok ← rd fun e => !name.isEmpty && name.toList.all (fun c => c.isAlphanum) && name != "template" && (e.dom.get e.doc).htmlDoc
  prim (.createElement (if ok then name else "span") r)
  return r

def createText (data : String) : M NodeId := do
  let r ← rd fun e => e.dom.size
  prim (.createText data r)
  return r

def insertBefore (parent node : NodeId) (child : Option NodeId) : M Unit := prim (.insertBefore parent node child)
def appendChild (parent node : NodeId) : M Unit := prim (.insertBefore parent node none)

def removeNode (n : NodeId) : M Unit := do
  match ← rd fun e => parentOf e.dom n with
  | some p => prim (.remove p n)
  | none => pure ()

def setAttr (n : NodeId) (name value : String) : M Unit := prim (.setAttr n name value)
def removeAttr (n : NodeId) (name : String) : M Unit := prim (.removeAttr n name)
def replaceData (n offset count : Nat) (data : String) : M Unit := prim (.replaceData n offset count data)

def splitText (n offset : Nat) : M NodeId := do
  let r ← rd fun e => e.dom.size
  let ok ← rd fun e => permitted e (.splitText n offset r)
  prim (.splitText n offset r)
  return if ok then r else n

def cloneNode (n : NodeId) (deep : Bool) : M NodeId := do
  let r ← rd fun e => e.dom.size
  prim (.cloneNode n deep r)
  return r

def createFragment : M NodeId := do
  let r ← rd fun e => e.dom.size
  prim (.createFragment r)
  return r

/-- The fragment of `src` parsed for a context element `ns`, `name`. -/
def parseFragment (ns name src : String) : M NodeId := do
  let r ← rd fun e => (Fragment.parseInto e.dom e.doc ns name src).2
  prim (.parseFragment ns name src r)
  return r

/-! ## The inline style of an element -/

def styleDecls (d : Dom) (n : NodeId) : Decls := parseDecls ((attr d n "style").getD "")

/-- `element.style[property]`: "" when not set. `text-decoration` also reads
`text-decoration-line`. -/
def styleGet (d : Dom) (n : NodeId) (prop : String) : String :=
  let ds := styleDecls d n
  match getDecl ds prop with
  | some v => v
  | none => if prop == "text-decoration" then (getDecl ds "text-decoration-line").getD "" else ""

/-- `element.style[property] = value`; "" removes the property. -/
def styleSet (n : NodeId) (prop value : String) : M Unit := do
  let ds ← rd fun e => styleDecls e.dom n
  let ds := if value.isEmpty then removeDecl (if prop == "text-decoration" then removeDecl ds "text-decoration-line" else ds) prop
    else setDecl ds prop value
  setAttr n "style" (serializeDecls ds)

/-! ## The active range -/

def activeOf (e : Ed) : Rng := ((e.live.ranges[0]?).join).getD ⟨⟨e.doc, 0⟩, ⟨e.doc, 0⟩⟩
def getActive : M Rng := rd activeOf

def setRangeAt (k : Nat) (r : Rng) : M Unit :=
  modify fun e => { e with live := { e.live with ranges := e.live.ranges.set! k (some r) } }

def setActive (r : Rng) : M Unit := setRangeAt 0 r

/-- The innermost editing host around the active range's common ancestor is
`contenteditable=plaintext-only`. -/
def inPlaintextHost (e : Ed) : Bool :=
  match (chain e.dom (commonAncestor e.dom (activeOf e))).toList.reverse.find? (isEditingHost e) with
  | some h => contentEditable e.dom h == "plaintext-only"
  | none => false

/-- `range.setStart(node, offset)` (DOM §5.5): the end follows a start that is after it. -/
def setStart (n : NodeId) (o : Nat) : M Unit := do
  let r ← getActive
  let d ← rd (·.dom)
  let bp : BP := ⟨n, o⟩
  if d.root n != d.root r.stop.node || position d bp r.stop == .after then setActive ⟨bp, bp⟩
  else setActive ⟨bp, r.stop⟩

/-- `range.setEnd(node, offset)` (DOM §5.5). -/
def setEnd (n : NodeId) (o : Nat) : M Unit := do
  let r ← getActive
  let d ← rd (·.dom)
  let bp : BP := ⟨n, o⟩
  if d.root n != d.root r.start.node || position d bp r.start == .before then setActive ⟨bp, bp⟩
  else setActive ⟨r.start, bp⟩

/-- A range the algorithm keeps for itself: its slot. -/
def addRange (r : Rng) : M Nat := do
  let e ← get
  let k := e.live.ranges.size
  set { e with live := { e.live with ranges := e.live.ranges.push (some r) } }
  return k

def rangeAt (k : Nat) : M Rng := rd fun e => ((e.live.ranges[k]?).join).getD (activeOf e)

/-- Drop the ranges from slot `k` on (the algorithm's own). -/
def dropRanges (k : Nat) : M Unit :=
  modify fun e => { e with live := { e.live with ranges := e.live.ranges.extract 0 k } }

/-! ## Blocks, visibility, line breaks -/

def displayOf (e : Ed) (n : NodeId) : String := (styleOf e.env e.dom n).display

/-- "Block node": an element whose `display` is not inline, inline-block, inline-table or
none, or a document or fragment. -/
def isBlockNode (e : Ed) (n : NodeId) : Bool :=
  let t := (e.dom.get n).type
  if t == .element then !(["inline", "inline-block", "inline-table", "none"].contains (displayOf e n))
  else t == .document || t == .fragment

def isBlockNodeO (e : Ed) (n : Option NodeId) : Bool :=
  match n with
  | some n => isBlockNode e n
  | none => false

/-- "Inline node": a node that is not a block node. -/
def isInlineNode (e : Ed) (n : NodeId) : Bool := !isBlockNode e n

def isInlineNodeO (e : Ed) (n : Option NodeId) : Bool :=
  match n with
  | some n => isInlineNode e n
  | none => false

def whiteSpaceOf (e : Ed) (n : NodeId) : String := (styleOf e.env e.dom n).whiteSpace

/-- "Whitespace node": an empty Text node, or one of only whitespace whose parent
collapses it. -/
def isWhitespaceNode (e : Ed) (n : NodeId) : Bool :=
  let d := e.dom
  isText d n &&
    (let data := (d.get n).data
     data.isEmpty ||
      (match parentOf d n with
        | some p =>
          isEl d p &&
            ((data.toList.all (fun c => c == '\t' || c == '\n' || c == '\r' || c == ' ') &&
                ["normal", "nowrap"].contains (whiteSpaceOf e p)) ||
             (data.toList.all (fun c => c == '\t' || c == '\r' || c == ' ') && whiteSpaceOf e p == "pre-line"))
        | none => false))

/-- Some inclusive ancestor element of `n` has `display: none`. -/
def displayNone (e : Ed) (n : NodeId) : Bool :=
  (chain e.dom n).any fun a => isEl e.dom a && displayOf e a == "none"

/-- "Collapsed whitespace node". -/
def isCollapsedWhitespaceNode (e : Ed) (n : NodeId) : Bool := Id.run do
  let d := e.dom
  if !isWhitespaceNode e n then return false
  if (d.get n).data.isEmpty then return true
  let some p := parentOf d n | return true
  if (ancestors d n).any (fun a => isEl d a && displayOf e a == "none") then return true
  let mut ancestor := p
  for _ in [0:d.size + 1] do
    if isBlockNode e ancestor then break
    match parentOf d ancestor with
    | some q => ancestor := q
    | none => break
  let mut reference := n
  for _ in [0:d.size + 1] do
    if reference == ancestor then break
    match prevNode d reference with
    | none => break
    | some r =>
      reference := r
      if isBlockNode e r || isHtml d r ["br"] then return true
      if (isText d r && !isWhitespaceNode e r) || isHtml d r ["img"] then break
  reference := n
  let stop := nextNodeDesc d ancestor
  for _ in [0:d.size + 1] do
    match nextNode d reference with
    | none => break
    | some r =>
      reference := r
      if isBlockNode e r || isHtml d r ["br"] then return true
      if (isText d r && !isWhitespaceNode e r) || isHtml d r ["img"] then break
      if some r == stop then break
  return false

/-- Inline content that takes room on a line: a Text node that is not a whitespace node,
or a replaced or inline-block element. -/
def isLineContent (e : Ed) (n : NodeId) : Bool :=
  let d := e.dom
  (isText d n && !isWhitespaceNode e n) ||
    isHtml d n ["img", "input", "button", "select", "textarea", "video", "audio", "canvas", "object", "embed", "iframe"]

/-- Inline content follows `br` in its block: the walk forward meets content or another
`br` before a block boundary. -/
def contentAfter (e : Ed) (br : NodeId) : Bool := Id.run do
  let d := e.dom
  let mut cur := br
  for _ in [0:d.size + 1] do
    match d.nextSibling cur with
    | some s =>
      if isEl d s && displayOf e s == "none" then cur := s
      else if isBlockNode e s then return false
      else
        for m in d.treeOrder s true do
          if isEl d m && m != s && isBlockNode e m then return false
          if isHtml d m ["br"] || isLineContent e m then return true
        cur := s
    | none =>
      match parentOf d cur with
      | some p => if isBlockNode e p then return false else cur := p
      | none => return false
  return false

/-- Inline content precedes `br` on its line: the walk backward meets content before a
`br` or a block boundary. -/
def contentBefore (e : Ed) (br : NodeId) : Bool := Id.run do
  let d := e.dom
  let mut cur := br
  for _ in [0:d.size + 1] do
    match d.previousSibling cur with
    | some s =>
      if isEl d s && displayOf e s == "none" then cur := s
      else if isBlockNode e s then return false
      else
        for m in (d.treeOrder s true).reverse do
          if isEl d m && m != s && isBlockNode e m then return false
          if isHtml d m ["br"] then return false
          if isLineContent e m then return true
        cur := s
    | none =>
      match parentOf d cur with
      | some p => if isBlockNode e p then return false else cur := p
      | none => return false
  return false

/-- "Collapsed line break": a `br` that begins a line box with nothing else in it; on the
tree, a `br` that no inline content follows in its block. -/
def isCollapsedLineBreak (e : Ed) (n : NodeId) : Bool :=
  isHtml e.dom n ["br"] && (parentOf e.dom n).isSome && !contentAfter e n

/-- "Extraneous line break": a `br` with no visual effect, except the only child of an
`li`; on the tree, a collapsed line break that inline content precedes on its line. -/
def isExtraneousLineBreak (e : Ed) (n : NodeId) : Bool :=
  let d := e.dom
  isHtml d n ["br"] &&
    (match parentOf d n with
      | some p =>
        !(isHtml d p ["li"] && (kidsOf d p).size == 1) && !contentAfter e n && contentBefore e n
      | none => false)

/-- "Visible": no ancestor with `display: none`, and the node or a descendant is a block
node, a Text node that is not a collapsed whitespace node, an `img`, or a `br` that is not
an extraneous line break. -/
def isVisible (e : Ed) (n : NodeId) : Bool :=
  let d := e.dom
  if displayNone e n then false
  else (d.treeOrder n true).any fun m =>
    (m == n || !((chain d m).any fun a => a != n && d.isInclusiveAncestor n a && isEl d a && displayOf e a == "none")) &&
    (isBlockNode e m || (isText d m && !isCollapsedWhitespaceNode e m) || isHtml d m ["img"] ||
      (isHtml d m ["br"] && !isExtraneousLineBreak e m))

def isInvisible (e : Ed) (n : NodeId) : Bool := !isVisible e n

def isVisibleO (e : Ed) (n : Option NodeId) : Bool :=
  match n with
  | some n => isVisible e n
  | none => false

/-- A missing node is not invisible (the draft's "invisible" is of a node). -/
def isInvisibleO (e : Ed) (n : Option NodeId) : Bool :=
  match n with
  | some n => isInvisible e n
  | none => false

/-- "Collapsed block prop": a collapsed line break that is not extraneous, or an inline
element whose children are all invisible or collapsed block props, with at least one
collapsed block prop. -/
def isCollapsedBlockPropF (e : Ed) : Nat → NodeId → Bool
  | 0, _ => false
  | fuel + 1, n =>
    let d := e.dom
    if isCollapsedLineBreak e n && !isExtraneousLineBreak e n then true
    else if !isInlineNode e n || !isEl d n then false
    else
      let kids := (kidsOf d n).toList
      kids.all (fun c => isInvisible e c || isCollapsedBlockPropF e fuel c) &&
        kids.any (fun c => isCollapsedBlockPropF e fuel c)

def isCollapsedBlockProp (e : Ed) (n : NodeId) : Bool := isCollapsedBlockPropF e (e.dom.size + 1) n

def prohibitedParagraphChildNames : List String :=
  ["address", "article", "aside", "blockquote", "caption", "center", "col", "colgroup", "dd", "details",
   "dir", "div", "dl", "dt", "fieldset", "figcaption", "figure", "footer", "form", "h1", "h2", "h3", "h4",
   "h5", "h6", "header", "hgroup", "hr", "li", "listing", "menu", "nav", "ol", "p", "plaintext", "pre",
   "section", "summary", "table", "tbody", "td", "tfoot", "th", "thead", "tr", "ul", "xmp"]

/-- "Prohibited paragraph child". -/
def isProhibitedParagraphChild (d : Dom) (n : NodeId) : Bool := isHtml d n prohibitedParagraphChildNames

def namesOfElementsWithInlineContents : List String :=
  ["a", "abbr", "b", "bdi", "bdo", "cite", "code", "dfn", "em", "h1", "h2", "h3", "h4", "h5", "h6", "i",
   "kbd", "mark", "p", "pre", "q", "rp", "rt", "ruby", "s", "samp", "small", "span", "strong", "sub", "sup",
   "u", "var", "acronym", "listing", "strike", "xmp", "big", "blink", "font", "marquee", "nobr", "tt"]

def headingNames : List String := ["h1", "h2", "h3", "h4", "h5", "h6"]

/-- "Allowed child" for names: `child` and `parent` are element names. -/
def allowedChildNames (child parent : String) : Bool :=
  match parent with
  | "colgroup" => child == "col"
  | "table" => ["caption", "col", "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"].contains child
  | "tbody" | "thead" | "tfoot" => ["td", "th", "tr"].contains child
  | "tr" => ["td", "th"].contains child
  | "dl" => ["dt", "dd"].contains child
  | "dir" | "ol" | "ul" => ["dir", "li", "ol", "ul"].contains child
  | "hgroup" => headingNames.contains child
  | _ =>
    if ["body", "caption", "col", "colgroup", "frame", "frameset", "head", "html", "tbody", "td", "tfoot", "th",
        "thead", "tr"].contains child then false
    else if ["dd", "dt"].contains child && parent != "dl" then false
    else if child == "li" && parent != "ol" && parent != "ul" then false
    else
      let table : List (List String × List String) := [
        (["a"], ["a"]), (["dd", "dt"], ["dd", "dt"]), (headingNames, headingNames), (["li"], ["li"]),
        (["nobr"], ["nobr"]), (namesOfElementsWithInlineContents, prohibitedParagraphChildNames),
        (["td", "th"], ["caption", "col", "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"])]
      !(table.any fun (ps, cs) => ps.contains parent && cs.contains child)

/-- A child for "allowed child": a node or an element name. -/
inductive ChildRef where
  | node (n : NodeId)
  | name (s : String)

/-- "Allowed child" of a parent node. -/
def isAllowedChild (e : Ed) (child : ChildRef) (parent : NodeId) : Bool := Id.run do
  let d := e.dom
  -- a Text node with content in a table part
  if isHtml d parent ["colgroup", "table", "tbody", "tfoot", "thead", "tr"] then
    if let .node c := child then
      if isText d c && !((d.get c).data.toList.all isWs) then return false
  if isHtml d parent ["script", "style", "plaintext", "xmp"] then
    match child with
    | .node c => if !isText d c then return false
    | .name _ => return false
  let childName : Option String ← match child with
    | .node c =>
      let t := (d.get c).type
      if t == .document || t == .fragment || t == .doctype then return false
      pure (if isHtmlEl d c then some (d.get c).lname else none)
    | .name s => pure (some s)
  let some cn := childName | return true
  if isHtmlEl d parent then
    for a in chain d parent do
      if cn == "a" && isHtml d a ["a"] then return false
      if prohibitedParagraphChildNames.contains cn && isHtml d a namesOfElementsWithInlineContents then return false
      if headingNames.contains cn && isHtml d a headingNames then return false
    return allowedChildNames cn (d.get parent).lname
  let t := (d.get parent).type
  return t == .element || t == .fragment

/-- "Allowed child" of a parent given as an element name. -/
def isAllowedChildOfName (e : Ed) (child : ChildRef) (parent : String) : Bool :=
  let d := e.dom
  match child with
  | .node c =>
    if ["colgroup", "table", "tbody", "tfoot", "thead", "tr"].contains parent && isText d c &&
        !((d.get c).data.toList.all isWs) then false
    else if ["script", "style", "plaintext", "xmp"].contains parent && !isText d c then false
    else
      let t := (d.get c).type
      if t == .document || t == .fragment || t == .doctype then false
      else if isHtmlEl d c then allowedChildNames (d.get c).lname parent
      else true
  | .name s =>
    if ["script", "style", "plaintext", "xmp"].contains parent then false else allowedChildNames s parent

/-! ## Moving nodes, wrapping, splitting -/

/-- "Preserving ranges", move `node` to be child `newIndex` of `newParent` (`none`: the
last child): a boundary point at the node's old place follows it, as the draft's steps say. -/
def movePreservingRanges (node newParent : NodeId) (newIndex : Option Nat) : M Unit := do
  let e ← get
  let d := e.dom
  let some oldParent := parentOf d node | (insertBefore newParent node none)
  let newIndex := newIndex.getD (kidsOf d newParent).size
  let oldIndex := indexOf d node
  let fix := fun (bp : BP) =>
    let bp := if bp.node == newParent && bp.offset > newIndex then { bp with offset := bp.offset + 1 } else bp
    if bp.node == oldParent && (bp.offset == oldIndex || bp.offset == oldIndex + 1) then
      (⟨newParent, bp.offset + newIndex - oldIndex⟩ : BP)
    else if bp.node == oldParent && bp.offset > oldIndex + 1 then { bp with offset := bp.offset - 1 }
    else bp
  let ranges := e.live.ranges.map fun r => r.map (Rng.map fix)
  let child := (kidsOf d newParent)[newIndex]?
  let before := e.log.size
  insertBefore newParent node child
  let e ← get
  if e.log.size > before then
    set { e with live := { e.live with ranges } }

/-- "Set the tag name" of an element: a new element with its attributes and children. -/
def setTagName (el : NodeId) (name : String) : M NodeId := do
  let d ← rd (·.dom)
  if isHtml d el [name] then return el
  let some p := parentOf d el | return el
  let r ← createElement name
  insertBefore p r (some el)
  for a in (d.get el).attrs do
    setAttr r a.qname a.value
  for c in kidsOf d el do
    movePreservingRanges c r none
  removeNode el
  -- the element was not replaced (the change was refused): keep it
  if (← rd fun e => parentOf e.dom r).isNone then return el
  return r

/-- "Remove extraneous line breaks before" a node. -/
def removeExtraneousLineBreaksBefore (n : NodeId) : M Unit := do
  let e ← get
  let d := e.dom
  let some s := d.previousSibling n | return
  let mut ref := deepLast d s
  for _ in [0:d.size + 1] do
    if isInvisible e ref && !isExtraneousLineBreak e ref && some ref != parentOf d n then
      match prevNode d ref with
      | some r => ref := r
      | none => break
    else break
  if isEditable e ref && isExtraneousLineBreak e ref then removeNode ref

/-- "Remove extraneous line breaks at the end of" a node. -/
def removeExtraneousLineBreaksAtTheEndOf (n : NodeId) : M Unit := do
  let e ← get
  let d := e.dom
  let mut ref := deepLast d n
  for _ in [0:d.size + 1] do
    if isInvisible e ref && !isExtraneousLineBreak e ref && ref != n then
      match prevNode d ref with
      | some r => ref := r
      | none => break
    else break
  if isEditable e ref && isExtraneousLineBreak e ref then
    for _ in [0:d.size + 1] do
      match parentOf d ref with
      | some p => if isEditable e p && isInvisible e p then ref := p else break
      | none => break
    removeNode ref

def removeExtraneousLineBreaksFrom (n : NodeId) : M Unit := do
  removeExtraneousLineBreaksBefore n
  removeExtraneousLineBreaksAtTheEndOf n

/-- "Wrap" a list of sibling nodes: into an editable sibling that `siblingCriteria`
accepts, else into the node `newParentInstructions` makes. The new parent, or `none`. -/
def wrap (nodeList : Array NodeId) (siblingCriteria : Ed → NodeId → Bool)
    (newParentInstructions : M (Option NodeId)) : M (Option NodeId) := do
  let e ← get
  let d := e.dom
  if nodeList.isEmpty then return none
  if nodeList.all (isInvisible e) && !(nodeList.any fun n => isHtml d n ["br"]) then return none
  if (parentOf d nodeList[0]!).isNone then return none
  let mut nodes := nodeList
  let last := nodes.back!
  if isInlineNode e last && !isHtml d last ["br"] && isHtmlO d (d.nextSibling last) ["br"] then
    nodes := nodes.push ((d.nextSibling last).getD last)
  for _ in [0:d.size + 1] do
    match d.previousSibling nodes[0]! with
    | some s => if isInvisible e s then nodes := #[s] ++ nodes else break
    | none => break
  for _ in [0:d.size + 1] do
    match d.nextSibling nodes.back! with
    | some s => if isInvisible e s then nodes := nodes.push s else break
    | none => break
  let prevS := d.previousSibling nodes[0]!
  let nextS := d.nextSibling nodes.back!
  let newParent : Option NodeId ←
    if isEditableO e prevS && (prevS.map (siblingCriteria e)).getD false then pure prevS
    else if isEditableO e nextS && (nextS.map (siblingCriteria e)).getD false then pure nextS
    else newParentInstructions
  let some np := newParent | return none
  let e ← get
  let d := e.dom
  if (parentOf d np).isNone then
    let some p0 := parentOf d nodes[0]! | return none
    insertBefore p0 np (some nodes[0]!)
    -- a boundary point that was before the first node stays before the new parent's content
    let r ← getActive
    let d ← rd (·.dom)
    let i := indexOf d np
    if r.start.node == p0 && r.start.offset == i then setActive { (← getActive) with start := ⟨p0, i + 1⟩ }
    let r ← getActive
    if r.stop.node == p0 && r.stop.offset == i then setActive { r with stop := ⟨p0, i + 1⟩ }
  let e ← get
  let d := e.dom
  let originalParent := parentOf d nodes[0]!
  if precedes d np nodes[0]! then
    let visKids := (kidsOf d np).filter (isVisible e)
    if !isInlineNode e np && isInlineNodeO e visKids.back? && isInlineNodeO e (nodes.filter (isVisible e))[0]? &&
        !isHtmlO d (lastChild d np) ["br"] then
      let br ← createElement "br"
      appendChild np br
    for n in nodes do movePreservingRanges n np none
  else
    let visKids := (kidsOf d np).filter (isVisible e)
    if !isInlineNode e np && isInlineNodeO e visKids[0]? && isInlineNodeO e (nodes.filter (isVisible e)).back? &&
        !isHtml d nodes.back! ["br"] then
      let br ← createElement "br"
      insertBefore np br (firstChild d np)
    for n in nodes.reverse do movePreservingRanges n np (some 0)
  let e ← get
  if let some op := originalParent then
    if isEditable e op && !hasKids e.dom op then removeNode op
  let e ← get
  let d := e.dom
  if let some ns := d.nextSibling np then
    if isEditable e ns && siblingCriteria e ns then
      if !isInlineNode e np && isInlineNodeO e (lastChild d np) && isInlineNodeO e (firstChild d ns) &&
          !isHtmlO d (lastChild d np) ["br"] then
        let br ← createElement "br"
        appendChild np br
      for c in kidsOf d ns do movePreservingRanges c np none
      removeNode ns
  removeExtraneousLineBreaksFrom np
  return some np

/-- "Block start point": the start of a root, or just after a visible block node or `br`. -/
def isBlockStartPoint (e : Ed) (n : NodeId) (o : Nat) : Bool :=
  let d := e.dom
  ((parentOf d n).isNone && o == 0) ||
    (o ≥ 1 && match (kidsOf d n)[o - 1]? with
      | some c => isVisible e c && (isBlockNode e c || isHtml d c ["br"])
      | none => false)

/-- "Block end point": the end of a root, or just before a visible block node. -/
def isBlockEndPoint (e : Ed) (n : NodeId) (o : Nat) : Bool :=
  let d := e.dom
  ((parentOf d n).isNone && o == nodeLength d n) ||
    (match (kidsOf d n)[o]? with
      | some c => isVisible e c && isBlockNode e c
      | none => false)

def isBlockBoundaryPoint (e : Ed) (n : NodeId) (o : Nat) : Bool :=
  isBlockStartPoint e n o || isBlockEndPoint e n o

/-- "Follows a line break". -/
def followsLineBreak (e : Ed) (n : NodeId) : Bool := Id.run do
  let d := e.dom
  let mut node := n
  let mut offset := 0
  for _ in [0:2 * d.size + 4] do
    if isBlockBoundaryPoint e node offset then return true
    if offset ≥ 1 then
      if let some c := (kidsOf d node)[offset - 1]? then
        if isVisible e c then return false
    if offset == 0 || !hasKids d node then
      match parentOf d node with
      | some p => offset := indexOf d node; node := p
      | none => return true
    else
      node := (kidsOf d node)[offset - 1]!
      offset := nodeLength d node
  return true

/-- "Precedes a line break". -/
def precedesLineBreak (e : Ed) (n : NodeId) : Bool := Id.run do
  let d := e.dom
  let mut node := n
  let mut offset := nodeLength d n
  for _ in [0:2 * d.size + 4] do
    if isBlockBoundaryPoint e node offset then return true
    if let some c := (kidsOf d node)[offset]? then
      if isVisible e c then return false
    if offset == nodeLength d node || !hasKids d node then
      match parentOf d node with
      | some p => offset := indexOf d node + 1; node := p
      | none => return true
    else
      node := (kidsOf d node)[offset]!
      offset := 0
  return true

/-- The innermost `li` among the inclusive ancestors of `n`. -/
def liAncestor (d : Dom) (n : NodeId) : Option NodeId :=
  ((chain d n).toList.reverse).find? fun a => isHtml d a ["li"]

/-- "Block-extend" a range: its start moves back and its end forward to block boundaries
(a whole `li` when a boundary point is in one). -/
def blockExtend (e : Ed) (r : Rng) : Rng := Id.run do
  let d := e.dom
  let mut sn := r.start.node
  let mut so := r.start.offset
  let mut en := r.stop.node
  let mut eo := r.stop.offset
  if let some li := liAncestor d sn then
    if let some p := parentOf d li then
      so := indexOf d li
      sn := p
  if !isBlockStartPoint e sn so then
    for _ in [0:2 * d.size + 4] do
      if so == 0 then
        match parentOf d sn with
        | some p => so := indexOf d sn; sn := p
        | none => break
      else so := so - 1
      if isBlockBoundaryPoint e sn so then break
  for _ in [0:d.size + 1] do
    if so != 0 then break
    match parentOf d sn with
    | some p => so := indexOf d sn; sn := p
    | none => break
  if let some li := liAncestor d en then
    if let some p := parentOf d li then
      eo := 1 + indexOf d li
      en := p
  if !isBlockEndPoint e en eo then
    for _ in [0:2 * d.size + 4] do
      if eo == nodeLength d en then
        match parentOf d en with
        | some p => eo := 1 + indexOf d en; en := p
        | none => break
      else eo := eo + 1
      if isBlockBoundaryPoint e en eo then break
  for _ in [0:d.size + 1] do
    if eo != nodeLength d en then break
    match parentOf d en with
    | some p => eo := 1 + indexOf d en; en := p
    | none => break
  return ⟨⟨sn, so⟩, ⟨en, eo⟩⟩

/-- "Split the parent" of a list of sibling nodes. -/
def splitParent (nodeList : Array NodeId) : M Unit := do
  if nodeList.isEmpty then return
  let e ← get
  let d := e.dom
  let some op := parentOf d nodeList[0]! | return
  if !isEditable e op || (parentOf d op).isNone then return
  let hasFirst := match firstChild d op with
    | some c => nodeList.contains c
    | none => false
  let hasLast := match lastChild d op with
    | some c => nodeList.contains c
    | none => false
  if hasFirst then removeExtraneousLineBreaksBefore op
  let e ← get
  let d := e.dom
  let follows := hasFirst && followsLineBreak e op
  let precedesLB := hasLast && precedesLineBreak e op
  let some opp := parentOf d op | return
  if !hasFirst && hasLast then
    for n in nodeList.reverse do
      let i ← rd fun e => indexOf e.dom op
      movePreservingRanges n opp (some (i + 1))
    let e ← get
    if precedesLB && !precedesLineBreak e nodeList.back! then
      let br ← createElement "br"
      let d ← rd (·.dom)
      match parentOf d nodeList.back! with
      | some p => insertBefore p br (d.nextSibling nodeList.back!)
      | none => pure ()
    removeExtraneousLineBreaksAtTheEndOf op
    return
  if !hasFirst then
    let cloned ← cloneNode op false
    removeAttr op "id"
    insertBefore opp cloned (some op)
    for _ in [0:d.size + 1] do
      let d ← rd (·.dom)
      if (d.previousSibling nodeList[0]!).isNone then break
      match firstChild d op with
      | some c => movePreservingRanges c cloned none
      | none => break
  for n in nodeList do
    let i ← rd fun e => indexOf e.dom op
    movePreservingRanges n opp (some i)
  let e ← get
  let d := e.dom
  if follows && !followsLineBreak e nodeList[0]! then
    let br ← createElement "br"
    match parentOf d nodeList[0]! with
    | some p => insertBefore p br (some nodeList[0]!)
    | none => pure ()
  let e ← get
  let d := e.dom
  let last := nodeList.back!
  if isInlineNode e last && !isHtml d last ["br"] && isHtmlO d (firstChild d op) ["br"] && !isInlineNode e op then
    match firstChild d op with
    | some c => removeNode c
    | none => pure ()
  let e ← get
  let d := e.dom
  if !hasKids d op then
    removeNode op
    let e ← get
    if precedesLB && !precedesLineBreak e last then
      let br ← createElement "br"
      let d ← rd (·.dom)
      match parentOf d last with
      | some p => insertBefore p br (d.nextSibling last)
      | none => pure ()
  else removeExtraneousLineBreaksBefore op
  let d ← rd (·.dom)
  if (d.nextSibling last).isNone then
    match parentOf d last with
    | some p => removeExtraneousLineBreaksAtTheEndOf p
    | none => pure ()

/-- "Remove a node, preserving its descendants". -/
def removePreservingDescendants (n : NodeId) : M Unit := do
  let d ← rd (·.dom)
  if hasKids d n then splitParent (kidsOf d n) else removeNode n

end L4Factoidal.DOM.Editing
