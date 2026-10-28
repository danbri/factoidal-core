/-
L4Factoidal.XSLT4.Streaming.Events — the event stream of an XML tree, the
tree built back from it, and accumulators evaluated over the stream.

A streaming XSLT processor reads its source as a sequence of events (start
tag, end tag, character data, ...) and keeps only the state that the open
elements need. This module defines that stream for the parse tree of
`L4Factoidal.XML` (`XML.Node`, `XML.Document`) and proves three bridge
statements:

* `build_docEvents`: the tree built from the event stream of a document is
  the document's children (`XML.Document.children`); `parse_events_rebuild`
  states it for every document that `XML.parseXML` returns. So the event
  stream loses nothing of the parser's tree.
* `streamAcc_events`: an accumulator evaluated over the event stream (the
  pre-descent rule at a start event, the post-descent rule at the matching
  end event, XSLT 4.0 §19) gives the same values, in the same order, as its
  tree-walk definition (`walk`).
* `events_depth_le`: the stream processor for accumulators keeps one stack
  frame per open element, so its memory is bounded by the depth of the
  tree, not by its size.

Spec: XSLT 4.0 §19 (accumulators: "the value of the accumulator before and
after each node"), XSLT Streaming 4.0 §11. The events are those of a SAX
parser (start tag with attributes, end tag, text, comment, CDATA section,
processing instruction).
-/
import L4Factoidal.XML.Parser

namespace L4Factoidal.XSLT4.Streaming

open L4Factoidal.XML

/-! ## Events -/

inductive Event where
  | start (tag : String) (attrs : List Attribute)
  | stop
  | text (s : String)
  | comment (s : String)
  | cdata (s : String)
  | pi (target data : String)
deriving DecidableEq, Repr, Inhabited

mutual
/-- The events of a node, in document order. -/
def events : Node → List Event
  | .element t a cs => .start t a :: (eventsList cs ++ [.stop])
  | .text s => [.text s]
  | .comment s => [.comment s]
  | .cdata s => [.cdata s]
  | .pi t d => [.pi t d]

def eventsList : List Node → List Event
  | [] => []
  | n :: ns => events n ++ eventsList ns
end

/-- The events of a document: those of its children (prolog, document
    element, epilog). The document node itself has no event. -/
def docEvents (d : Document) : List Event := eventsList d.children

/-! ## Building the tree back -/

/-- An open element: its tag, attributes and the children read so far
    (newest first). -/
structure Frame where
  tag : String
  attrs : List Attribute
  kids : List Node
deriving Inhabited

/-- The builder's state: the open elements (innermost first) and the
    top-level nodes read so far (newest first). -/
structure BSt where
  stack : List Frame
  top : List Node
deriving Inhabited

/-- Add a finished node to the innermost open element, or to the top. -/
def BSt.add (st : BSt) (n : Node) : BSt :=
  match st.stack with
  | f :: fs => { st with stack := { f with kids := n :: f.kids } :: fs }
  | [] => { st with top := n :: st.top }

/-- One event. An end event with no open element is an error. -/
def BSt.step (st : BSt) : Event → Option BSt
  | .start t a => some { st with stack := { tag := t, attrs := a, kids := [] } :: st.stack }
  | .stop => match st.stack with
    | f :: fs => some (BSt.add { st with stack := fs } (.element f.tag f.attrs f.kids.reverse))
    | [] => none
  | .text s => some (st.add (.text s))
  | .comment s => some (st.add (.comment s))
  | .cdata s => some (st.add (.cdata s))
  | .pi t d => some (st.add (.pi t d))

def BSt.run : List Event → BSt → Option BSt
  | [], st => some st
  | e :: es, st => (st.step e).bind (BSt.run es)

/-- The nodes of an event stream; `none` when the start and end events do
    not match. -/
def build (es : List Event) : Option (List Node) :=
  (BSt.run es { stack := [], top := [] }).bind (fun st =>
    if st.stack.isEmpty then some st.top.reverse else none)

theorem BSt.run_append (xs ys : List Event) (st : BSt) :
    BSt.run (xs ++ ys) st = (BSt.run xs st).bind (BSt.run ys) := by
  induction xs generalizing st with
  | nil => simp [BSt.run]
  | cons e es ih =>
    simp only [List.cons_append, BSt.run]
    cases st.step e with
    | none => rfl
    | some st' => simp [ih]

/-- Adding a list of nodes to an open frame puts them, newest first, in
    front of its children. -/
theorem foldl_add_frame (ns : List Node) (f : Frame) (fs : List Frame) (top : List Node) :
    ns.foldl BSt.add { stack := f :: fs, top } =
      { stack := { f with kids := ns.reverse ++ f.kids } :: fs, top } := by
  induction ns generalizing f with
  | nil => simp
  | cons n ns ih =>
    simp only [List.foldl, BSt.add]
    rw [ih]
    simp

mutual
theorem run_events (n : Node) (st : BSt) :
    BSt.run (events n) st = some (st.add n) := by
  match n with
  | .element t a cs =>
    simp only [events, BSt.run, BSt.step, Option.bind_some]
    rw [BSt.run_append, run_eventsList]
    simp only [Option.bind_some]
    rw [foldl_add_frame]
    simp [BSt.run, BSt.step]
  | .text s => simp [events, BSt.run, BSt.step]
  | .comment s => simp [events, BSt.run, BSt.step]
  | .cdata s => simp [events, BSt.run, BSt.step]
  | .pi t d => simp [events, BSt.run, BSt.step]

theorem run_eventsList (ns : List Node) (st : BSt) :
    BSt.run (eventsList ns) st = some (ns.foldl BSt.add st) := by
  match ns with
  | [] => simp [eventsList, BSt.run]
  | n :: rest =>
    simp only [eventsList]
    rw [BSt.run_append, run_events]
    simp only [Option.bind_some]
    rw [run_eventsList]
    simp
end

theorem foldl_add_top (ns : List Node) (top : List Node) :
    ns.foldl BSt.add { stack := [], top } = { stack := [], top := ns.reverse ++ top } := by
  induction ns generalizing top with
  | nil => simp
  | cons n ns ih =>
    simp only [List.foldl, BSt.add]
    rw [ih]
    simp

/-- **The event stream reconstructs the tree.** -/
theorem build_eventsList (ns : List Node) : build (eventsList ns) = some ns := by
  simp [build, run_eventsList, foldl_add_top]

theorem build_docEvents (d : Document) : build (docEvents d) = some d.children :=
  build_eventsList d.children

/-- For every document that the XML parser returns, the event stream gives
    back the parser's tree: the prolog, the document element and the
    epilog (`XML.Document.children_eq`). -/
theorem parse_events_rebuild (s : String) (d : Document) (_h : parseXML s = .ok d) :
    build (docEvents d) = some (d.prolog ++ (d.root :: d.epilog)) := by
  rw [build_docEvents]
  rfl

/-! ## Accumulators over the stream

An accumulator (XSLT 4.0 §19) has a value before each node (computed by
its pre-descent rules, `phase="start"`) and after each node (its
post-descent rules, `phase="end"`, after the node's descendants). Here a
rule is any function of what the start event shows of the node (`Label`)
and the current value; matching patterns against the label and choosing a
rule are inside `pre` and `post`. -/

/-- What the start of a node shows: an element's tag and attributes, or a
    whole leaf node. -/
inductive Label where
  | elem (tag : String) (attrs : List Attribute)
  | leaf (n : Node)
deriving Inhabited

structure Acc (α : Type) where
  pre : Label → α → α
  post : Label → α → α

mutual
/-- The tree-walk definition: the values of the accumulator before and
    after every node, in document order (pre-descent value at the start
    of a node, post-descent value at its end), and the final value. -/
def walk {α : Type} (A : Acc α) : Node → α → List α × α
  | .element t a cs, v =>
    let v1 := A.pre (.elem t a) v
    let (tr, v2) := walkList A cs v1
    let v3 := A.post (.elem t a) v2
    (v1 :: tr ++ [v3], v3)
  | n, v =>
    let v1 := A.pre (.leaf n) v
    let v2 := A.post (.leaf n) v1
    ([v1, v2], v2)

def walkList {α : Type} (A : Acc α) : List Node → α → List α × α
  | [], v => ([], v)
  | n :: ns, v =>
    let (t1, v1) := walk A n v
    let (t2, v2) := walkList A ns v1
    (t1 ++ t2, v2)
end

/-- The stream processor's state: the value, the labels of the open
    elements (innermost first), and the values observed so far (newest
    first). -/
structure ASt (α : Type) where
  v : α
  open_ : List Label
  trace : List α

def ASt.step {α : Type} (A : Acc α) (st : ASt α) : Event → Option (ASt α)
  | .start t a =>
    let v1 := A.pre (.elem t a) st.v
    some { v := v1, open_ := .elem t a :: st.open_, trace := v1 :: st.trace }
  | .stop => match st.open_ with
    | l :: ls =>
      let v1 := A.post l st.v
      some { v := v1, open_ := ls, trace := v1 :: st.trace }
    | [] => none
  | e =>
    let n : Node := match e with
      | .text s => .text s | .comment s => .comment s | .cdata s => .cdata s
      | .pi t d => .pi t d | _ => .text ""
    let v1 := A.pre (.leaf n) st.v
    let v2 := A.post (.leaf n) v1
    some { st with v := v2, trace := v2 :: v1 :: st.trace }

def ASt.run {α : Type} (A : Acc α) : List Event → ASt α → Option (ASt α)
  | [], st => some st
  | e :: es, st => (st.step A e).bind (ASt.run A es)

/-- The accumulator evaluated over an event stream: the observed values
    in order and the final value. -/
def streamAcc {α : Type} (A : Acc α) (es : List Event) (v : α) : Option (List α × α) :=
  (ASt.run A es { v, open_ := [], trace := [] }).map (fun st => (st.trace.reverse, st.v))

theorem ASt.run_append {α : Type} (A : Acc α) (xs ys : List Event) (st : ASt α) :
    ASt.run A (xs ++ ys) st = (ASt.run A xs st).bind (ASt.run A ys) := by
  induction xs generalizing st with
  | nil => simp [ASt.run]
  | cons e es ih =>
    simp only [List.cons_append, ASt.run]
    cases st.step A e with
    | none => rfl
    | some st' => simp [ih]

mutual
theorem arun_events {α : Type} (A : Acc α) (n : Node) (st : ASt α) :
    ASt.run A (events n) st =
      some { v := (walk A n st.v).2, open_ := st.open_,
             trace := (walk A n st.v).1.reverse ++ st.trace } := by
  match n with
  | .element t a cs =>
    simp only [events, ASt.run, ASt.step, Option.bind_some]
    rw [ASt.run_append, arun_eventsList]
    simp [ASt.run, ASt.step, walk]
  | .text s => simp [events, ASt.run, ASt.step, walk]
  | .comment s => simp [events, ASt.run, ASt.step, walk]
  | .cdata s => simp [events, ASt.run, ASt.step, walk]
  | .pi t d => simp [events, ASt.run, ASt.step, walk]

theorem arun_eventsList {α : Type} (A : Acc α) (ns : List Node) (st : ASt α) :
    ASt.run A (eventsList ns) st =
      some { v := (walkList A ns st.v).2, open_ := st.open_,
             trace := (walkList A ns st.v).1.reverse ++ st.trace } := by
  match ns with
  | [] => simp [eventsList, ASt.run, walkList]
  | n :: rest =>
    simp only [eventsList]
    rw [ASt.run_append, arun_events]
    simp only [Option.bind_some]
    rw [arun_eventsList]
    simp [walkList]
end

/-- **Streamed accumulators equal their tree-walk definition.** -/
theorem streamAcc_events {α : Type} (A : Acc α) (ns : List Node) (v : α) :
    streamAcc A (eventsList ns) v = some (walkList A ns v) := by
  simp [streamAcc, arun_eventsList]

/-! ## Memory of the stream processor

The accumulator processor keeps one label per open element. -/

mutual
def depth : Node → Nat
  | .element _ _ cs => depthList cs + 1
  | _ => 0

def depthList : List Node → Nat
  | [] => 0
  | n :: ns => max (depth n) (depthList ns)
end

/-- The largest number of open elements at any point of the event stream,
    starting from `k` open elements. -/
def maxOpen : List Event → Nat → Nat
  | [], k => k
  | .start _ _ :: es, k => max k (maxOpen es (k + 1))
  | .stop :: es, k => max k (maxOpen es (k - 1))
  | _ :: es, k => max k (maxOpen es k)

mutual
/-- The events of a node open at most `depth n` elements above `k`, and
    close every element they open. -/
theorem events_depth_le (n : Node) (k : Nat) (ys : List Event) :
    maxOpen (events n ++ ys) k ≤ max (k + depth n) (maxOpen ys k) := by
  match n with
  | .element t a cs =>
    simp only [events, List.cons_append, List.append_assoc, List.nil_append, maxOpen]
    have h := eventsList_depth_le cs (k + 1) (.stop :: ys)
    simp only [maxOpen] at h
    simp only [depth]
    have : k + 1 - 1 = k := by omega
    rw [this] at h
    omega
  | .text _ => simp [events, maxOpen, depth] <;> omega
  | .comment _ => simp [events, maxOpen, depth] <;> omega
  | .cdata _ => simp [events, maxOpen, depth] <;> omega
  | .pi _ _ => simp [events, maxOpen, depth] <;> omega

theorem eventsList_depth_le (ns : List Node) (k : Nat) (ys : List Event) :
    maxOpen (eventsList ns ++ ys) k ≤ max (k + depthList ns) (maxOpen ys k) := by
  match ns with
  | [] => simp [eventsList, depthList] <;> omega
  | n :: rest =>
    simp only [eventsList, List.append_assoc, depthList]
    have h1 := events_depth_le n k (eventsList rest ++ ys)
    have h2 := eventsList_depth_le rest k ys
    omega
end

/-- The event stream of a list of nodes never has more open elements than
    the depth of the deepest node. -/
theorem maxOpen_eventsList (ns : List Node) : maxOpen (eventsList ns) 0 ≤ depthList ns := by
  have h := eventsList_depth_le ns 0 []
  simp [maxOpen] at h
  omega

end L4Factoidal.XSLT4.Streaming
