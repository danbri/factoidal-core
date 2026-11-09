/-!
# Event dispatch order (WHATWG DOM §2.9 and §2.10)

The order in which the listeners of one event run, for an event path of
elements. `path` is root first and ends at the target. DOM §2.9 "dispatch",
steps 5.13 and 5.14:

* for each struct of the path in reverse order (root first), "invoke" with
  phase "capturing": the capture listeners. At the target the event phase is
  `AT_TARGET`, else `CAPTURING_PHASE`;
* then for each struct in order (target first), "invoke" with phase
  "bubbling": the other listeners. At the target the event phase is
  `AT_TARGET`; at an ancestor `BUBBLING_PHASE`, and only if the event bubbles.

"inner invoke" runs the listeners of one node in the order they were added.
`stopPropagation` sets the stop propagation flag; the next "invoke" checks it
first and returns, so the listeners of the current invoke still run and no
later invoke does. `stopImmediatePropagation` stops at once.

Shadow trees: `planAt` (the structs at the target are given; the path and the
retargeted targets are `DOM.Shadow.eventPath` and `DOM.Shadow.retarget`). Not modelled
here: Document and Window on the path, `once` and
`passive`, and listeners added during the dispatch to a node not yet reached
(the plan is fixed when dispatch starts). The host checks the removed flag of
a listener before it runs it.
-/
namespace L4Factoidal.EventLoop.Dispatch

/-- A registered listener: its node, its capture flag, and the opaque callback. -/
structure Listener where
  node : Nat
  capture : Bool
  callback : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Phase where
  | capturing | atTarget | bubbling
  deriving DecidableEq, Repr, Inhabited

/-- One listener call: `depth` is the index of the node in the path (0 is the
root); `capture` names the pass ("capturing" or "bubbling"). -/
structure Visit where
  node : Nat
  depth : Nat
  capture : Bool
  phase : Phase
  callback : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The listeners of one invoke, in the order they were added. -/
def invoke (listeners : List Listener) (target : Nat) (node depth : Nat) (capture : Bool) : List Visit :=
  (listeners.filter fun l => l.node == node && l.capture == capture).map fun l =>
    { node, depth, capture, callback := l.callback,
      phase := if depth == target then .atTarget else if capture then .capturing else .bubbling }

/-- The whole plan for an event at the last node of `path`. -/
def plan (path : List Nat) (listeners : List Listener) (bubbles : Bool) : List Visit :=
  let target := path.length - 1
  (List.range path.length).flatMap (fun d => invoke listeners target (path.getD d 0) d true) ++
  (List.range path.length).reverse.flatMap (fun d =>
    if d == target || bubbles then invoke listeners target (path.getD d 0) d false else [])

/-- `invoke` for a struct that is at the target or not (DOM §2.9: its shadow-adjusted target
is non-null). -/
def invokeAt (listeners : List Listener) (atT : Bool) (node depth : Nat) (capture : Bool) : List Visit :=
  (listeners.filter fun l => l.node == node && l.capture == capture).map fun l =>
    { node, depth, capture, callback := l.callback,
      phase := if atT then .atTarget else if capture then .capturing else .bubbling }

/-- The plan of DOM §2.9 steps 5.13 and 5.14 for a path through shadow trees: `atTarget d`
says that the struct at depth `d` (root first) has a shadow-adjusted target, as the
target has and a shadow host on the path of an event from its shadow tree has. Such a
struct's phase is `AT_TARGET`, and its bubbling listeners run when the event does not
bubble. With `atTarget` true only at the last struct it is `plan` (`planAt_plan`). -/
def planAt (path : List Nat) (atTarget : Nat → Bool) (listeners : List Listener) (bubbles : Bool) : List Visit :=
  (List.range path.length).flatMap (fun d => invokeAt listeners (atTarget d) (path.getD d 0) d true) ++
  (List.range path.length).reverse.flatMap (fun d =>
    if atTarget d || bubbles then invokeAt listeners (atTarget d) (path.getD d 0) d false else [])

theorem invokeAt_invoke (ls : List Listener) (target node depth : Nat) (capture : Bool) :
    invokeAt ls (depth == target) node depth capture = invoke ls target node depth capture := rfl

/-- A path with no shadow tree: `planAt` is `plan`. -/
theorem planAt_plan (path : List Nat) (ls : List Listener) (bubbles : Bool) :
    planAt path (· == path.length - 1) ls bubbles = plan path ls bubbles := rfl

/-- The rank of a visit in the walk: capture invokes count up from the root,
then the bubbling invokes count up from the target to the root. -/
def rank (target : Nat) (v : Visit) : Nat :=
  if v.capture then v.depth else 2 * target + 1 - v.depth

/-- The visits after visit `i` that still run when its callback calls
`stopPropagation` (`immediate` false) or `stopImmediatePropagation` (true):
the rest of the same invoke. -/
def afterStop (visits : List Visit) (i : Nat) (immediate : Bool) : List Visit :=
  match visits[i]? with
  | none => []
  | some v =>
    if immediate then []
    else (visits.drop (i + 1)).takeWhile fun w => w.depth == v.depth && w.capture == v.capture

end L4Factoidal.EventLoop.Dispatch
