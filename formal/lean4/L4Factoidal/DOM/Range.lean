/-
L4Factoidal.DOM.Range — boundary points and live ranges of the WHATWG DOM Standard (§5,
"Ranges"), on the DOM arena (`L4Factoidal/DOM/Arena.lean`).

Specification: DOM Living Standard, whatwg/dom commit `3c53f93a` (the commit of
`DOM.Arena`): §5.2 "Boundary points" (position), §5.3 "Interface AbstractRange", §5.5
"Interface Range" (set the start or end, collapse, select, compareBoundaryPoints,
comparePoint, isPointInRange, intersectsNode, the stringifier, delete, extract, clone the
contents, insert, surroundContents), and the live range steps of the mutation algorithms:
§4.2.3 "insert" (step 4) and "remove" (steps 4 to 7), §4.10 "replace data" (steps 8 to
11), §4.11 "split a Text node" (step 7), §4.4 `normalize()` (step 6).

A range here is four numbers: start (node, offset) and end (node, offset). Offsets of a
CharacterData node count UTF-16 code units, as in the standard (`utf16Length`); the arena
keeps the data as a Lean string (code points).

What changes the arena is not here: the host (`WasmVM.Hosts.Dom`) runs the change as typed
commands and moves its live ranges with the step functions of this module
(`removeStep`, `insertStep`, `replaceDataStep`, `splitTextStep`, `mergeStep`). A page with
no live range runs none of them.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.Range
open L4Factoidal.DOM

/-- A boundary point (DOM §5.2): a node and an offset. -/
structure BP where
  node : NodeId
  offset : Nat
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A range: its start and end boundary points (DOM §5.3). -/
structure Rng where
  start : BP
  stop : BP
  deriving BEq, DecidableEq, Repr, Inhabited

/-- The position of one boundary point relative to another (DOM §5.2). -/
inductive Pos where
  | before | equal | after
  deriving BEq, DecidableEq, Repr, Inhabited

def Pos.flip : Pos → Pos
  | .before => .after | .equal => .equal | .after => .before

/-- The answer of `compareBoundaryPoints` and `comparePoint`: -1, 0, 1. -/
def Pos.toInt : Pos → Int
  | .before => -1 | .equal => 0 | .after => 1

theorem Pos.flip_flip (p : Pos) : p.flip.flip = p := by cases p <;> rfl

/-! ## UTF-16 code units (the offsets of CharacterData) -/

def unitsOf (c : Char) : Nat := if c.val.toNat ≥ 0x10000 then 2 else 1

/-- The length of a string in UTF-16 code units. -/
def utf16Length (s : String) : Nat := s.foldl (fun n c => n + unitsOf c) 0

/-- The characters of `s` before UTF-16 offset `k`, and those from it. An offset inside a
surrogate pair goes to the end of the pair (a Lean string holds no lone surrogate). -/
def splitAtUnits (s : String) (k : Nat) : String × String := Id.run do
  let mut pre : List Char := []
  let mut rest := s.toList
  let mut n := 0
  for _ in [0:s.length] do
    match rest with
    | [] => break
    | c :: r =>
      if n ≥ k then break
      pre := c :: pre
      n := n + unitsOf c
      rest := r
  return (String.ofList pre.reverse, String.ofList rest)

/-- `substringData(offset, count)` without the checks: `count` units from `offset`. -/
def substringUnits (s : String) (offset count : Nat) : String :=
  (splitAtUnits (splitAtUnits s offset).2 count).1

/-- The data after "replace data" (DOM §4.10 steps 6 and 7): `count` units at `offset`
replaced by `data`; `count` is clipped to the end. -/
def replaceUnits (s : String) (offset count : Nat) (data : String) : String :=
  let (pre, rest) := splitAtUnits s offset
  pre ++ data ++ (splitAtUnits rest count).2

#guard utf16Length ("a" ++ String.singleton (Char.ofNat 0x1F600) ++ "b") == 4
#guard replaceUnits "abcdef" 2 2 "XY" == "abXYef"
#guard replaceUnits "abc" 1 10 "" == "a"
#guard substringUnits "abcdef" 1 3 == "bcd"

/-! ## Nodes -/

/-- The length of a node (DOM §4.2): 0 for a doctype, the data's length in code units for
a CharacterData node, else the number of children. -/
def nodeLength (d : Dom) (n : NodeId) : Nat :=
  let x := d.get n
  match x.type with
  | .doctype => 0
  | .text | .cdata | .comment | .pi => utf16Length x.data
  | _ => x.kids.size

/-- The inclusive ancestors of `n`, root first, `n` last. The walk is bounded by the
arena size. -/
def chain (d : Dom) (n : NodeId) : Array NodeId := Id.run do
  let mut out : Array NodeId := #[n]
  let mut cur := n
  for _ in [0:d.size + 1] do
    match (d.get cur).parent with
    | some p => out := out.push p; cur := p
    | none => break
  return out.reverse

def indexOf (d : Dom) (n : NodeId) : Nat := (d.index n).getD 0

/-- The first index at which two root-first chains differ (their common length when one
is a prefix of the other). -/
def divergence (a b : Array NodeId) : Nat := Id.run do
  let m := min a.size b.size
  for i in [0:m] do
    if a[i]! != b[i]! then return i
  return m

/-- `a` is preceding `b` (DOM §4.2.1): same root, and `a` is before `b` in tree order. -/
def precedes (d : Dom) (a b : NodeId) : Bool :=
  if a == b then false else
  let ca := chain d a
  let cb := chain d b
  if ca[0]! != cb[0]! then false else
  let i := divergence ca cb
  if i == ca.size then true          -- `a` is an ancestor of `b`
  else if i == cb.size then false    -- `b` is an ancestor of `a`
  else indexOf d ca[i]! < indexOf d cb[i]!

def following (d : Dom) (a b : NodeId) : Bool := precedes d b a

def sameRoot (d : Dom) (a b : NodeId) : Bool := d.root a == d.root b

/-- The position of `a` relative to `b` when `a.node` is not `b.node` and is not
following it (DOM §5.2 steps 4 and 5). -/
def positionNotFollowing (d : Dom) (a b : BP) : Pos :=
  if d.isInclusiveAncestor a.node b.node then
    -- the child of `a.node` that is an inclusive ancestor of `b.node`
    let cb := chain d b.node
    let i := (cb.findIdx? (· == a.node)).getD 0
    let child := cb[i + 1]!
    if indexOf d child < a.offset then .after else .before
  else .before

/-- The position of boundary point `a` relative to `b` (DOM §5.2); both in one tree. -/
def position (d : Dom) (a b : BP) : Pos :=
  if a.node == b.node then
    if a.offset == b.offset then .equal else if a.offset < b.offset then .before else .after
  else if following d a.node b.node then (positionNotFollowing d b a).flip
  else positionNotFollowing d a b

theorem position_self (d : Dom) (a : BP) : position d a a = .equal := by
  simp [position]

/-- On one node, the position is the order of the offsets, so it is antisymmetric. -/
theorem position_same_node (d : Dom) (a b : BP) (h : a.node = b.node) :
    position d a b = (position d b a).flip := by
  unfold position
  simp only [h, beq_self_eq_true, if_true]
  by_cases e : a.offset = b.offset
  · simp [e, Pos.flip]
  · by_cases l : a.offset < b.offset
    · have : ¬ b.offset < a.offset := by omega
      simp [e, l, this, Pos.flip, Ne.symm e]
    · have : b.offset < a.offset := by omega
      simp [e, l, this, Pos.flip, Ne.symm e]

/-! ## Range attributes and checks -/

def Rng.collapsed (r : Rng) : Bool := r.start == r.stop

def Rng.root (d : Dom) (r : Rng) : NodeId := d.root r.start.node

/-- The errors a range method throws (DOM §5.5), as the host's codes. -/
inductive Err where
  | invalidNodeType | indexSize | wrongDocument | notSupported | hierarchyRequest | invalidState
  | dom (e : DomError)
  deriving BEq, Repr, Inhabited

/-- "Set the start or end" (DOM §5.5) of `r` to (`node`, `offset`). -/
def setBoundary (d : Dom) (r : Rng) (node offset : Nat) (isStart : Bool) : Except Err Rng :=
  if node ≥ d.size then .error .invalidNodeType else
  if (d.get node).type == .doctype then .error .invalidNodeType else
  if offset > nodeLength d node then .error .indexSize else
  let bp : BP := ⟨node, offset⟩
  let other := r.root d != d.root node
  if isStart then
    let r := if other || position d bp r.stop == .after then { r with stop := bp } else r
    .ok { r with start := bp }
  else
    let r := if other || position d bp r.start == .before then { r with start := bp } else r
    .ok { r with stop := bp }

/-- `setStartBefore` (0), `setStartAfter` (1), `setEndBefore` (2), `setEndAfter` (3). -/
def setRelative (d : Dom) (r : Rng) (node which : Nat) : Except Err Rng :=
  if node ≥ d.size then .error .invalidNodeType else
  match (d.get node).parent with
  | none => .error .invalidNodeType
  | some p =>
    let i := indexOf d node
    match which with
    | 0 => setBoundary d r p i true
    | 1 => setBoundary d r p (i + 1) true
    | 2 => setBoundary d r p i false
    | _ => setBoundary d r p (i + 1) false

/-- "Select" `node` within a range (DOM §5.5). -/
def selectNode (d : Dom) (node : NodeId) : Except Err Rng :=
  match (d.get node).parent with
  | none => .error .invalidNodeType
  | some p => let i := indexOf d node; .ok ⟨⟨p, i⟩, ⟨p, i + 1⟩⟩

/-- `selectNodeContents(node)` (DOM §5.5). -/
def selectNodeContents (d : Dom) (node : NodeId) : Except Err Rng :=
  if (d.get node).type == .doctype then .error .invalidNodeType
  else .ok ⟨⟨node, 0⟩, ⟨node, nodeLength d node⟩⟩

/-- `compareBoundaryPoints(how, sourceRange)` (DOM §5.5). -/
def compareBoundaryPoints (d : Dom) (r : Rng) (how : Nat) (src : Rng) : Except Err Int :=
  if how > 3 then .error .notSupported
  else if r.root d != src.root d then .error .wrongDocument
  else
    let (p, q) := match how with
      | 0 => (r.start, src.start)
      | 1 => (r.stop, src.start)
      | 2 => (r.stop, src.stop)
      | _ => (r.start, src.stop)
    .ok (position d p q).toInt

/-- The checks of `isPointInRange` and `comparePoint` after the root (DOM §5.5). -/
def checkPoint (d : Dom) (node offset : Nat) : Except Err Unit :=
  if (d.get node).type == .doctype then .error .invalidNodeType
  else if offset > nodeLength d node then .error .indexSize
  else .ok ()

def isPointInRange (d : Dom) (r : Rng) (node offset : Nat) : Except Err Bool :=
  if r.root d != d.root node then .ok false else do
  checkPoint d node offset
  let bp : BP := ⟨node, offset⟩
  return !(position d bp r.start == .before || position d bp r.stop == .after)

def comparePoint (d : Dom) (r : Rng) (node offset : Nat) : Except Err Int :=
  if r.root d != d.root node then .error .wrongDocument else do
  checkPoint d node offset
  let bp : BP := ⟨node, offset⟩
  if position d bp r.start == .before then return -1
  if position d bp r.stop == .after then return 1
  return 0

/-- `intersectsNode(node)` (DOM §5.5). -/
def intersectsNode (d : Dom) (r : Rng) (node : NodeId) : Bool :=
  if r.root d != d.root node then false else
  match (d.get node).parent with
  | none => true
  | some p =>
    let i := indexOf d node
    position d ⟨p, i⟩ r.stop == .before && position d ⟨p, i + 1⟩ r.start == .after

/-- `commonAncestorContainer` (DOM §5.5). -/
def commonAncestor (d : Dom) (r : Rng) : NodeId := Id.run do
  let mut c := r.start.node
  for _ in [0:d.size + 1] do
    if d.isInclusiveAncestor c r.stop.node then return c
    match (d.get c).parent with
    | some p => c := p
    | none => return c
  return c

/-- `node` is contained in `r` (DOM §5.5): its root is the range's root, (node, 0) is
after the start and (node, length) is before the end. -/
def contained (d : Dom) (r : Rng) (node : NodeId) : Bool :=
  d.root node == r.root d && position d ⟨node, 0⟩ r.start == .after &&
    position d ⟨node, nodeLength d node⟩ r.stop == .before

/-- `node` is partially contained in `r`: an inclusive ancestor of the start node but not
of the end node, or the other way round. -/
def partiallyContained (d : Dom) (r : Rng) (node : NodeId) : Bool :=
  d.isInclusiveAncestor node r.start.node != d.isInclusiveAncestor node r.stop.node

/-- The stringifier (DOM §5.5): the data of the Text nodes in the range, cut at its ends. -/
def toText (d : Dom) (r : Rng) : String := Id.run do
  let sn := d.get r.start.node
  if r.start.node == r.stop.node && Dom.isTextNode sn then
    return substringUnits sn.data r.start.offset (r.stop.offset - r.start.offset)
  let mut s := ""
  if Dom.isTextNode sn then s := s ++ (splitAtUnits sn.data r.start.offset).2
  -- the Text nodes contained in the range, in tree order: those of the common ancestor's
  -- subtree that are after the start and before the end
  for k in d.treeOrder (commonAncestor d r) true do
    let x := d.get k
    if Dom.isTextNode x && contained d r k then s := s ++ x.data
  let en := d.get r.stop.node
  if Dom.isTextNode en then s := s ++ (splitAtUnits en.data r.stop.offset).1
  return s

/-! ## Live range steps of the mutation algorithms

Each function moves one boundary point; the host applies it to the start and the end of
every live range. `d` is the arena before the change. -/

/-- "Remove" (DOM §4.2.3) steps 4 to 7, for a node removed from `parent` at `index`;
`inside` tells the inclusive descendants of the removed node. -/
def removeStep (inside : NodeId → Bool) (parent index : Nat) (bp : BP) : BP :=
  if inside bp.node then ⟨parent, index⟩
  else if bp.node == parent && bp.offset > index then ⟨parent, bp.offset - 1⟩
  else bp

/-- "Insert" (DOM §4.2.3) step 4: `count` nodes go into `parent` before the child at
`index`. -/
def insertStep (parent index count : Nat) (bp : BP) : BP :=
  if bp.node == parent && bp.offset > index then ⟨parent, bp.offset + count⟩ else bp

/-- "Replace data" (DOM §4.10) steps 8 to 11: `count` units of `node` at `offset`
replaced by `len` units. -/
def replaceDataStep (node offset count len : Nat) (bp : BP) : BP :=
  if bp.node != node then bp
  else if bp.offset > offset && bp.offset ≤ offset + count then ⟨node, offset⟩
  else if bp.offset > offset + count then ⟨node, bp.offset + len - count⟩
  else bp

/-- "Split a Text node" (DOM §4.11) steps 7.2 to 7.5: `node` at `index` of `parent` is
split at `offset`; `fresh` is the new node, already inserted after it. -/
def splitTextStep (node offset fresh parent index : Nat) (bp : BP) : BP :=
  if bp.node == node && bp.offset > offset then ⟨fresh, bp.offset - offset⟩
  else if bp.node == parent && bp.offset == index + 1 then ⟨parent, bp.offset + 1⟩
  else bp

/-- `normalize()` (DOM §4.4) steps 6.1 to 6.4: the Text node `cur` at `index` of
`parent` is merged into `node`, whose data has `length` units before it. -/
def mergeStep (node cur parent index length : Nat) (bp : BP) : BP :=
  if bp.node == cur then ⟨node, bp.offset + length⟩
  else if bp.node == parent && bp.offset == index then ⟨node, length⟩
  else bp

def Rng.map (f : BP → BP) (r : Rng) : Rng := ⟨f r.start, f r.stop⟩

/-! ### The steps keep a boundary point within its node

A range is valid when each offset is at most its node's length. Each step gives an offset
within the node's length after the change. -/

theorem insertStep_le (parent index count L : Nat) (bp : BP) (h : bp.offset ≤ L) :
    (insertStep parent index count bp).offset ≤ L + count := by
  unfold insertStep; split <;> (try simp) <;> omega

/-- The parent loses one child at `index < L`: an offset into it stays at most `L - 1`. -/
theorem removeStep_parent_le (inside : NodeId → Bool) (parent index L : Nat) (bp : BP)
    (hp : bp.node = parent) (h : bp.offset ≤ L) (hi : index < L) :
    (removeStep inside parent index bp).node = parent →
      (removeStep inside parent index bp).offset ≤ L - 1 := by
  unfold removeStep
  split
  · intro _; simp; omega
  · split
    · intro _; simp; omega
    · rename_i h2; intro _
      have : ¬ (bp.offset > index) := by
        intro hc; apply h2; simp [hp, hc]
      omega

/-- After "replace data", an offset into the node is at most its new length. -/
theorem replaceDataStep_le (node offset count len L : Nat) (bp : BP) (hn : bp.node = node)
    (h : bp.offset ≤ L) (hc : offset + count ≤ L) :
    (replaceDataStep node offset count len bp).offset ≤ L - count + len := by
  unfold replaceDataStep
  have hb : (bp.node != node) = false := by simp [hn]
  rw [if_neg (by simp [hb])]
  by_cases h1 : bp.offset > offset ∧ bp.offset ≤ offset + count
  · rw [if_pos (by simp [h1.1, h1.2])]; simp; omega
  · by_cases h2 : bp.offset > offset + count
    · rw [if_neg (by simpa using h1), if_pos h2]; simp; omega
    · rw [if_neg (by simpa using h1), if_neg h2]
      have : bp.offset ≤ offset := by omega
      omega

#guard position {} ⟨0, 1⟩ ⟨0, 2⟩ == .before
#guard replaceDataStep 5 2 3 1 ⟨5, 4⟩ == ⟨5, 2⟩
#guard replaceDataStep 5 2 3 1 ⟨5, 9⟩ == ⟨5, 7⟩
#guard insertStep 1 2 3 ⟨1, 3⟩ == ⟨1, 6⟩

end L4Factoidal.DOM.Range
