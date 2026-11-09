/-
L4Factoidal.DOM.Traversal — `NodeIterator` and `TreeWalker` of the WHATWG DOM Standard
(§6, "Traversal"), on the DOM arena.

Specification: DOM Living Standard, whatwg/dom `3c53f93a`: §6.1 "Interface NodeIterator"
(the iterator collection, the NodeIterator pre-removing steps, traverse), §6.2 "Interface
TreeWalker" (traverse children, traverse siblings, parentNode, previousNode, nextNode),
§6.3 "Interface NodeFilter" (whatToShow).

A filter is a page's JavaScript callback, so the algorithms here are machines that stop
where the standard says "filter node": `Walk.step` answers either a node for the page to
filter or the result. The page gives each filter result back (`Walk.step` again), and the
machine goes on. So the order of the filter calls, and every move, is Lean's; the page only
calls its callback. A `whatToShow` test that fails is FILTER_SKIP without asking the page.

A NodeIterator lives in the host's state (`Iter`): its reference and its pointer before
reference move when a node is removed (`preRemove`, run by `DOM.Live.remove`).
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.DOM.OfHtml

namespace L4Factoidal.DOM.Traversal
open L4Factoidal.DOM

/-- `whatToShow` (DOM §6.3): bit `nodeType - 1` shows nodes of that type. -/
def shows (whatToShow : Nat) (d : Dom) (n : NodeId) : Bool :=
  let t := (d.get n).type.code
  (whatToShow / 2 ^ (t - 1)) % 2 == 1

/-! ## Moves within a root -/

/-- The next sibling of `n` or of its nearest ancestor below `root` that has one. -/
def nextSkipping (d : Dom) (root n : NodeId) : Option NodeId := Id.run do
  let mut cur := n
  for _ in [0:d.size + 1] do
    if cur == root then return none
    match d.nextSibling cur with
    | some s => return some s
    | none =>
      match (d.get cur).parent with
      | some p => cur := p
      | none => return none
  return none

/-- The first node following `n` that is an inclusive descendant of `root` (tree order). -/
def following (d : Dom) (root n : NodeId) : Option NodeId :=
  match (d.get n).kids[0]? with
  | some c => some c
  | none => nextSkipping d root n

/-- The last inclusive descendant of `n` in tree order. -/
def lastDescendant (d : Dom) (n : NodeId) : NodeId := Id.run do
  let mut cur := n
  for _ in [0:d.size + 1] do
    match (d.get cur).kids.back? with
    | some c => cur := c
    | none => return cur
  return cur

/-- The first node preceding `n` that is an inclusive descendant of `root`. -/
def preceding (d : Dom) (root n : NodeId) : Option NodeId :=
  if n == root then none else
  match d.previousSibling n with
  | some s => some (lastDescendant d s)
  | none => (d.get n).parent

/-! ## NodeIterator -/

/-- A NodeIterator's state: root, reference, pointer before reference, whatToShow. -/
structure Iter where
  root : NodeId
  reference : NodeId
  beforeRef : Bool := true
  whatToShow : Nat
  deriving BEq, Repr, Inhabited

/-- The NodeIterator pre-removing steps (DOM §6.1) for `node`, about to be removed. -/
def preRemove (d : Dom) (it : Iter) (node : NodeId) : Iter := Id.run do
  if !d.isInclusiveAncestor node it.reference || node == it.root then return it
  let mut it := it
  if it.beforeRef then
    -- the first following node that is an inclusive descendant of the root and not an
    -- inclusive descendant of `node`
    match (nextSkipping d it.root node).filter (d.isInclusiveAncestor it.root ·) with
    | some next => return { it with reference := next }
    | none => it := { it with beforeRef := false }
  match d.previousSibling node with
  | some s => return { it with reference := lastDescendant d s }
  | none => return { it with reference := ((d.get node).parent).getD it.reference }

/-- One move of "traverse" (DOM §6.1 steps 3.1, 3.2) from (`node`, `beforeNode`): the next
node to filter and the new before flag, or none when the iterator is at its end. Nodes that
`whatToShow` does not show are passed over (their filter result is FILTER_SKIP). -/
def iterMove (d : Dom) (it : Iter) (node : NodeId) (beforeNode next : Bool) : Option (NodeId × Bool) := Id.run do
  let mut node := node
  let mut before := beforeNode
  for _ in [0:d.size + 2] do
    if next then
      if !before then
        match following d it.root node with
        | some k => node := k
        | none => return none
      else before := false
    else
      if before then
        match preceding d it.root node with
        | some k => node := k
        | none => return none
      else before := true
    if shows it.whatToShow d node then return some (node, before)
  return none

/-! ## TreeWalker: the algorithms as machines that stop to filter -/

/-- The TreeWalker method a machine runs. -/
inductive Method where
  | parentNode | firstChild | lastChild | previousSibling | nextSibling | previousNode | nextNode
  deriving BEq, Repr, Inhabited

def Method.ofNat : Nat → Method
  | 0 => .parentNode | 1 => .firstChild | 2 => .lastChild | 3 => .previousSibling
  | 4 => .nextSibling | 5 => .previousNode | _ => .nextNode

/-- Filter results (DOM §6.3). -/
def accept : Nat := 1
def reject : Nat := 2
def skip : Nat := 3

/-- Where a machine stopped: the step of its algorithm, and its variables. -/
structure Walk where
  method : Method
  root : NodeId
  whatToShow : Nat
  /-- The walker's current node when the method started. -/
  current : NodeId
  /-- The algorithm's `node` variable. -/
  node : NodeId
  /-- The step to go on with when the filter answers (the label of the stop). -/
  at_ : Nat := 0
  deriving Repr, Inhabited

/-- What a machine asks for: filter a node (the walker stopped), or the method's result:
a node that becomes the current node, or null (the current node stays). -/
inductive Ask where
  | filter (w : Walk) (node : NodeId)
  | done (result : Option NodeId)
  deriving Repr, Inhabited

/-- "Filter" without the page: FILTER_SKIP when `whatToShow` does not show the node; else
the page must be asked. -/
def needsPage (w : Walk) (d : Dom) (n : NodeId) : Bool := shows w.whatToShow d n

def firstOf (d : Dom) (n : NodeId) (first : Bool) : Option NodeId :=
  if first then (d.get n).kids[0]? else (d.get n).kids.back?

def sibOf (d : Dom) (n : NodeId) (nextDir : Bool) : Option NodeId :=
  if nextDir then d.nextSibling n else d.previousSibling n

/-- Run `w` from its step `w.at_`, where `r` is the filter result of `w.node` (when the
machine stopped to filter it). The loop is bounded by the arena size. -/
def run (d : Dom) (w : Walk) (r : Nat) : Ask := Id.run do
  let mut w := w
  let mut r := r
  -- `pending`: the machine needs the filter result of `w.node` before going on
  for _ in [0:4 * d.size + 8] do
    match w.method with
    | .parentNode =>
      -- §6.2 parentNode(): node = current; while node is not root: node = parent; if
      -- non-null and accepted, return it
      if w.at_ == 1 && r == accept then return .done (some w.node)
      if w.node == w.root then return .done none
      match (d.get w.node).parent with
      | none => return .done none
      | some p =>
        w := { w with node := p, at_ := 1 }
        if !needsPage w d p then r := skip else return .filter w p
    | .firstChild | .lastChild =>
      -- §6.2 traverse children
      let first := w.method == .firstChild
      -- at_ 0: start; 1: have the result of node
      if w.at_ == 0 then
        match firstOf d w.current first with
        | none => return .done none
        | some c =>
          w := { w with node := c, at_ := 1 }
          if !needsPage w d c then r := skip else return .filter w c
      else
        if r == accept then return .done (some w.node)
        -- skip: descend into node's children
        let mut moved := false
        if r == skip then
          match firstOf d w.node first with
          | some c =>
            w := { w with node := c }
            moved := true
          | none => pure ()
        if !moved then
          -- climb to a sibling
          let mut found : Option NodeId := none
          let mut give := false
          let mut node := w.node
          for _ in [0:d.size + 1] do
            match sibOf d node first with
            | some s => found := some s; break
            | none =>
              match (d.get node).parent with
              | none => give := true; break
              | some p =>
                if p == w.root || p == w.current then give := true; break
                node := p
          if give then return .done none
          match found with
          | some s => w := { w with node := s }
          | none => return .done none
        if !needsPage w d w.node then r := skip else return .filter w w.node
    | .previousSibling | .nextSibling =>
      -- §6.2 traverse siblings
      let nextDir := w.method == .nextSibling
      if w.at_ == 0 then
        if w.current == w.root then return .done none
        w := { w with node := w.current, at_ := 2 }
        r := 0
      -- at_ 2: find the sibling of node (or climb); at_ 1: have the result of node
      if w.at_ == 1 then
        if r == accept then return .done (some w.node)
        -- sibling = node's first or last child when skip
        let sib := if r == skip then firstOf d w.node nextDir else none
        match sib with
        | some c =>
          w := { w with node := c }
          if !needsPage w d c then r := skip else return .filter w c
          continue
        | none =>
          match sibOf d w.node nextDir with
          | some s =>
            w := { w with node := s }
            if !needsPage w d s then r := skip else return .filter w s
            continue
          | none =>
            -- climb
            match (d.get w.node).parent with
            | none => return .done none
            | some p =>
              if p == w.root then return .done none
              w := { w with node := p, at_ := 3 }
              -- step 3.4: if node's filter result is accept, return null (the parent was
              -- filtered before: a parent that is not shown is skipped)
              if !needsPage w d p then r := skip else return .filter w p
              continue
      if w.at_ == 3 then
        if r == accept then return .done none
        w := { w with at_ := 2 }
      -- at_ 2: sibling of node
      match sibOf d w.node nextDir with
      | some s =>
        w := { w with node := s, at_ := 1 }
        if !needsPage w d s then r := skip else return .filter w s
      | none =>
        match (d.get w.node).parent with
        | none => return .done none
        | some p =>
          if p == w.root then return .done none
          w := { w with node := p, at_ := 3 }
          if !needsPage w d p then r := skip else return .filter w p
    | .previousNode =>
      -- §6.2 previousNode(): at_ 0 start; 1 result of a sibling; 2 result of a last child;
      -- 3 result of the parent
      if w.at_ == 0 then
        w := { w with node := w.current, at_ := 4 }
      if w.at_ == 1 || w.at_ == 2 then
        if r != reject then
          match (d.get w.node).kids.back? with
          | some c =>
            w := { w with node := c, at_ := 2 }
            if !needsPage w d c then r := skip else return .filter w c
            continue
          | none => pure ()
        if r == accept then return .done (some w.node)
        w := { w with at_ := 4 }
      if w.at_ == 3 then
        if r == accept then return .done (some w.node)
        w := { w with at_ := 4 }
      -- at_ 4: while node is not root
      if w.node == w.root then return .done none
      match d.previousSibling w.node with
      | some s =>
        w := { w with node := s, at_ := 1 }
        if !needsPage w d s then r := skip else return .filter w s
      | none =>
        match (d.get w.node).parent with
        | none => return .done none
        | some p =>
          if w.node == w.root then return .done none
          w := { w with node := p, at_ := 3 }
          if !needsPage w d p then r := skip else return .filter w p
    | .nextNode =>
      -- §6.2 nextNode(): at_ 0 start (result = accept); 1 the result of `node`
      if w.at_ == 0 then
        w := { w with node := w.current, at_ := 1 }
        r := accept
      else if r == accept then return .done (some w.node)
      -- step 3.1: while result is not reject and node has a child
      if r != reject then
        match (d.get w.node).kids[0]? with
        | some c =>
          w := { w with node := c }
          if !needsPage w d c then r := skip else return .filter w c
          continue
        | none => pure ()
      -- steps 3.2, 3.3: the next sibling of node or of an ancestor below root
      let mut temp := w.node
      for _ in [0:d.size + 1] do
        if temp == w.root then return .done none
        match d.nextSibling temp with
        | some s => w := { w with node := s }; break
        | none =>
          match (d.get temp).parent with
          | some p => temp := p
          | none => break
      -- step 3.4 (with no sibling found, node is filtered again)
      if !needsPage w d w.node then r := skip else return .filter w w.node
  return .done none

/-- Start method `m` of a walker at `current`. -/
def start (d : Dom) (m : Method) (root whatToShow current : NodeId) : Ask :=
  run d { method := m, root, whatToShow, current, node := current } 0

/-- All filters accept: the result of a method, for tests. -/
def runAll (d : Dom) (m : Method) (root current : NodeId) (whatToShow : Nat := 0xFFFFFFFF) : Option NodeId := Id.run do
  let mut a := start d m root whatToShow current
  for _ in [0:d.size + 2] do
    match a with
    | .done r => return r
    | .filter w _ => a := run d w accept
  return none

private def tdoc : Dom := parseHtmlDocument "<div id=r><p id=a><b id=b></b></p><i id=c></i></div>"
private def tid (s : String) : NodeId := (tdoc.getElementById 0 s).getD 0
private def walk (m : Method) (from_ : String) : Option NodeId := runAll tdoc m (tid "r") (tid from_)
#guard walk .nextNode "r" == some (tid "a")
#guard walk .nextNode "a" == some (tid "b")
#guard walk .nextNode "b" == some (tid "c")
#guard walk .nextNode "c" == none
#guard walk .previousNode "c" == some (tid "b")
#guard walk .previousNode "b" == some (tid "a")
#guard walk .previousNode "a" == some (tid "r")
#guard walk .previousNode "r" == none
#guard walk .firstChild "r" == some (tid "a")
#guard walk .lastChild "r" == some (tid "c")
#guard walk .parentNode "b" == some (tid "a")
#guard walk .parentNode "r" == none
#guard walk .nextSibling "a" == some (tid "c")
#guard walk .previousSibling "c" == some (tid "a")
#guard walk .nextSibling "c" == none
-- whatToShow SHOW_TEXT only: no element is a result
#guard runAll tdoc .nextNode (tid "r") (tid "r") 4 == none
-- the NodeIterator pre-removing steps: removing the reference moves it to the next node
#guard (preRemove tdoc { root := tid "r", reference := tid "a", whatToShow := 0xFFFFFFFF } (tid "a")).reference == tid "c"
#guard (preRemove tdoc { root := tid "r", reference := tid "b", beforeRef := false, whatToShow := 0xFFFFFFFF } (tid "a")).reference == tid "r"

end L4Factoidal.DOM.Traversal

