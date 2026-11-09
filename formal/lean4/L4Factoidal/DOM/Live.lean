/-
L4Factoidal.DOM.Live — the live ranges and NodeIterators of a document, moved by the
mutation algorithms of the DOM Standard.

Specification: DOM Living Standard, whatwg/dom `3c53f93a`: §4.2.3 "insert" (step 5),
"remove" (steps 4 to 8, with the NodeIterator pre-removing steps of §6.1), "replace",
"replace all", "adopt"; §4.4 `textContent` and `normalize()` (step 6); §4.10 "replace
data"; §4.11 "split a Text node".

Each function here follows the arena operation of `DOM.Arena` that has its name, step by
step in the standard's order, and moves the live ranges (`Range.removeStep`, ...) and
NodeIterators (`Traversal.preRemove`) where the standard does. The host
(`WasmVM.Hosts.Dom.addCommand`) runs the function of each command only when the page has a
live range or a NodeIterator (`Live.idle`), and keeps the arena that `DOM.Arena` gave: the
arena half of the answer here is for the next step's positions only.
-/
import L4Factoidal.DOM.Range
import L4Factoidal.DOM.Traversal
import Std.Data.HashSet

namespace L4Factoidal.DOM.Live
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-- The live ranges and NodeIterators of the page. A range is its index in `ranges`;
`none` is a range the page can no longer reach (its object was collected), whose slot a new
range takes (`free`). An iterator is never dropped. -/
structure Live where
  ranges : Array (Option Rng) := #[]
  /-- The slots of `ranges` that hold no range. -/
  free : Array Nat := #[]
  iters : Array Traversal.Iter := #[]
  deriving Inhabited

/-- Nothing to move: no change runs any live step. -/
def Live.idle (lv : Live) : Bool := lv.ranges.size == lv.free.size && lv.iters.isEmpty

def Live.mapBP (lv : Live) (f : BP → BP) : Live := { lv with ranges := lv.ranges.map (·.map (Rng.map f)) }

/-- A new live range: the number of its slot. -/
def Live.add (lv : Live) (r : Rng) : Live × Nat :=
  match lv.free.back? with
  | some k => ({ lv with ranges := lv.ranges.set! k (some r), free := lv.free.pop }, k)
  | none => ({ lv with ranges := lv.ranges.push (some r) }, lv.ranges.size)

/-- The page can no longer reach range `k`: its slot is free. -/
def Live.release (lv : Live) (k : Nat) : Live :=
  match lv.ranges[k]? with
  | some (some _) => { lv with ranges := lv.ranges.set! k none, free := lv.free.push k }
  | _ => lv

/-- "Remove" `node` (DOM §4.2.3): the live range steps 4 to 7 and the NodeIterator
pre-removing steps (step 8) before the node leaves its parent. -/
def remove (d : Dom) (lv : Live) (node : NodeId) : Dom × Live :=
  match (d.get node).parent with
  | none => (d, lv)
  | some p =>
    let i := indexOf d node
    -- the removed subtree, once: each range then costs one lookup
    let inside : Std.HashSet NodeId := (d.treeOrder node true).foldl (·.insert ·) {}
    let lv := { lv.mapBP (removeStep (inside.contains ·) p i) with
                iters := lv.iters.map (Traversal.preRemove d · node) }
    (d.remove node, lv)

/-- "Adopt" (DOM §4.5): remove from the old parent, then the node document. -/
def adopt (d : Dom) (lv : Live) (node doc : NodeId) : Dom × Live :=
  let (d, lv) := if (d.get node).parent.isSome then remove d lv node else (d, lv)
  (if (d.get node).doc == doc then d else d.setNodeDocument node doc, lv)

/-- "Insert" `node` into `parent` before `child` (DOM §4.2.3), as `Dom.insert`. -/
def insert (d : Dom) (lv : Live) (node parent : NodeId) (child : Option NodeId) : Dom × Live := Id.run do
  let n := d.get node
  let nodes := if n.type == .fragment then n.kids else #[node]
  if nodes.size == 0 then return (d, lv)
  let mut d := d
  let mut lv := lv
  if n.type == .fragment then
    for k in nodes do (d, lv) := remove d lv k
  if let some c := child then
    lv := lv.mapBP (insertStep parent (indexOf d c) nodes.size)
  let doc := (d.get parent).doc
  for k in nodes do
    (d, lv) := adopt d lv k doc
    d := d.linkChild parent k child
  return (d, lv)

/-- "Pre-insert" after its checks (`Dom.preInsert`). -/
def preInsert (d : Dom) (lv : Live) (node parent : NodeId) (child : Option NodeId) : Dom × Live :=
  let ref := if child == some node then d.nextSibling node else child
  insert d lv node parent ref

/-- "Replace" `child` with `node` within `parent` after its checks, as `Dom.replace`. -/
def replace (d : Dom) (lv : Live) (child node parent : NodeId) : Dom × Live :=
  let ref0 := d.nextSibling child
  let ref := if ref0 == some node then d.nextSibling node else ref0
  let (d, lv) := adopt d lv node (d.get parent).doc
  let (d, lv) := if (d.get child).parent.isSome then remove d lv child else (d, lv)
  insert d lv node parent ref

/-- "Replace all" with `node` within `parent` (DOM §4.2.3), as `Dom.replaceAll`. -/
def replaceAll (d : Dom) (lv : Live) (node : Option NodeId) (parent : NodeId) : Dom × Live := Id.run do
  let mut d := d
  let mut lv := lv
  for k in (d.get parent).kids do (d, lv) := remove d lv k
  match node with
  | some n => return insert d lv n parent none
  | none => return (d, lv)

/-- "Replace data" (DOM §4.10) after its checks: `count` units at `offset` by `data`. -/
def replaceData (d : Dom) (lv : Live) (node offset count : Nat) (data : String) : Dom × Live :=
  let x := d.get node
  let len := utf16Length x.data
  let count := min count (len - offset)
  (d.setNode node fun y => { y with data := replaceUnits y.data offset count data },
   lv.mapBP (replaceDataStep node offset count (utf16Length data)))

/-- `textContent` setter (DOM §4.4), as `Dom.setTextContent`. -/
def setTextContent (d : Dom) (lv : Live) (n : NodeId) (value : String) : Dom × Live :=
  let x := d.get n
  match x.type with
  | .fragment | .element =>
    if value.isEmpty then replaceAll d lv none n
    else
      let (d, t) := d.createTextNode x.doc value
      replaceAll d lv (some t) n
  | .text | .cdata | .comment | .pi => replaceData d lv n 0 (utf16Length x.data) value
  | .document | .doctype => (d, lv)

/-- "Split a Text node" (DOM §4.11) after its check: the new node is the next node of the
arena (`d.size`). -/
def splitText (d : Dom) (lv : Live) (node offset : Nat) : Dom × Live × NodeId := Id.run do
  let x := d.get node
  let len := utf16Length x.data
  let count := len - offset
  let newData := substringUnits x.data offset count
  let (d0, fresh) := d.createTextNode x.doc newData
  let mut d := d0
  let mut lv := lv
  if let some p := x.parent then
    let i := indexOf d node
    (d, lv) := insert d lv fresh p (d.nextSibling node)
    lv := lv.mapBP (splitTextStep node offset fresh p i)
  let (d2, lv2) := replaceData d lv node offset count ""
  return (d2, lv2, fresh)

/-- An exclusive Text node: a Text node that is not a CDATASection. -/
def exclusiveText (d : Dom) (n : NodeId) : Bool := (d.get n).type == .text

/-- `normalize()` (DOM §4.4), step by step. -/
def normalize (d : Dom) (lv : Live) (n : NodeId) : Dom × Live := Id.run do
  let mut d := d
  let mut lv := lv
  for node in d.treeOrder n false do
    -- a node removed by an earlier step is not a descendant any more
    if !exclusiveText d node || (d.get node).parent.isNone || !d.isInclusiveAncestor n node then continue
    let mut length := nodeLength d node
    if length == 0 then
      (d, lv) := remove d lv node
      continue
    -- the contiguous exclusive Text nodes after `node`
    let mut run : Array NodeId := #[]
    let mut cur := d.nextSibling node
    for _ in [0:d.size] do
      match cur with
      | some c => if exclusiveText d c then run := run.push c; cur := d.nextSibling c else break
      | none => break
    let data := run.foldl (fun acc k => acc ++ (d.get k).data) ""
    (d, lv) := replaceData d lv node length 0 data
    let p := ((d.get node).parent).getD node
    for c in run do
      lv := lv.mapBP (mergeStep node c p (indexOf d c) length)
      length := length + nodeLength d c
    for c in run do (d, lv) := remove d lv c
  return (d, lv)

/-! ## Agreement with the arena

With no live range and no iterator, these functions change the arena as `DOM.Arena` does:
tested on documents here; `tests/dom` checks `DOM.Arena`. -/

private def doc1 : Dom := parseHtmlDocument "<p id=a>xy<b id=b>z</b>w</p><i id=c></i>"
private def idOf (d : Dom) (s : String) : NodeId := (d.getElementById 0 s).getD 0
private def same (a b : Dom) : Bool := a.nodes.size == b.nodes.size &&
  (List.range a.nodes.size).all fun i => (a.get i).kids == (b.get i).kids && (a.get i).parent == (b.get i).parent &&
    (a.get i).data == (b.get i).data

#guard same (insert doc1 {} (idOf doc1 "c") (idOf doc1 "a") (some (idOf doc1 "b"))).1
  (doc1.insert (idOf doc1 "c") (idOf doc1 "a") (some (idOf doc1 "b")))
#guard same (remove doc1 {} (idOf doc1 "b")).1 (doc1.remove (idOf doc1 "b"))
#guard same (replace doc1 {} (idOf doc1 "b") (idOf doc1 "c") (idOf doc1 "a")).1
  (match doc1.replace (idOf doc1 "b") (idOf doc1 "c") (idOf doc1 "a") with | (d, _) => d)
#guard same (normalize (doc1.setTextContent (idOf doc1 "b") "") {} 0).1 ((doc1.setTextContent (idOf doc1 "b") "").normalize 0)

-- live ranges: a range in the removed node goes to its parent; one after it moves back
#guard (let a := idOf doc1 "a"; let b := idOf doc1 "b"
  let lv : Live := { ranges := #[some ⟨⟨b, 0⟩, ⟨a, 3⟩⟩] }
  (remove doc1 lv b).2.ranges) == #[some ⟨⟨idOf doc1 "a", 1⟩, ⟨idOf doc1 "a", 2⟩⟩]
-- replace data: an offset inside the replaced units goes to its start
#guard (let t := (doc1.get (idOf doc1 "a")).kids[0]!
  (replaceData doc1 { ranges := #[some ⟨⟨t, 1⟩, ⟨t, 2⟩⟩] } t 0 2 "abc").2.ranges) ==
  (let t := (doc1.get (idOf doc1 "a")).kids[0]!; #[some ⟨⟨t, 0⟩, ⟨t, 0⟩⟩])
#guard (let t := (doc1.get (idOf doc1 "a")).kids[0]!
  (replaceData doc1 { ranges := #[some ⟨⟨t, 1⟩, ⟨t, 2⟩⟩] } t 0 1 "abc").2.ranges) ==
  (let t := (doc1.get (idOf doc1 "a")).kids[0]!; #[some ⟨⟨t, 0⟩, ⟨t, 4⟩⟩])

end L4Factoidal.DOM.Live
