/-!
# Web Audio API: the audio graph and the processing order

Follows https://webaudio.github.io/web-audio-api/ :
* section 1.5.5 "Methods" of the `AudioNode` interface: `connect(destinationNode, output, input)`,
  `connect(destinationParam, output)` and the six `disconnect` overloads;
* section "Rendering an Audio Graph", the step "Order the AudioNodes of the BaseAudioContext to
  be processed" (cycle breakers, `DelayWriter` and `DelayReader`, muting, the visit procedure);
* section 1.18.4 "Processing" of the `DelayNode` interface (`DelayWriter`, `DelayReader`).

Stage B of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, sections 4 and 9.

## Model

* A `Graph` has a list of node kinds (index = `NodeId`), audio connections (`Edge`: output
  `out` of `src` to input `inp` of `dst`) and parameter connections (`ParamEdge`: output `out`
  of `src` to `AudioParam` number `param` of `dst`). One `Graph` is one `BaseAudioContext`, so
  the `InvalidAccessError` for nodes of different contexts cannot occur and is not modelled.
* `connect`, `connectParam` and the `disconnect*` functions are pure functions on `Graph` with
  the errors of the specification: `IndexSizeError` for an output, input or parameter index out
  of bounds, `InvalidAccessError` when a `disconnect` names a connection that does not exist.
  `unknownNode` is added for a `NodeId` that is not in the graph (in the API this cannot happen,
  the argument is an object).
* `order g` is the ordering step of the rendering algorithm:
  1. a `DelayNode` that is part of a cycle of the graph (audio and parameter connections both
     count) is a cycle breaker. It becomes two steps. `delayWrite` has the input connections of
     the delay, `delayRead` has its output connections (`DelayWriter` and `DelayReader` of
     section 1.18.4). No connection joins the two.
  2. a node that lies on a cycle of the graph so obtained is muted: it is left out of the steps
     and listed in `muted`.
  3. the remaining steps are put in an order in which every step comes after all the steps that
     feed it (an input or an `AudioParam` of it). The specification does this with a depth-first
     visit and a reversal. This file uses repeated selection of the first step whose feeding
     steps are all placed (Kahn's algorithm, in the order of node numbers). Both give a
     topological order; they can give different ones, and the specification does not fix one.
     The tests in this file check properties of the order, with exact lists only where the
     graph has one possible order.

## What is proved (all over the actual definitions, no hypothesis restates a conclusion)

* `order_nodup`: no step is listed twice.
* `order_topological`, `order_topological_edge`, `order_topological_param`: if a connection
  joins two nodes that are not muted, and the two steps that stand for its ends are in the
  list, the step at the source end comes first. For a delay in a cycle the source end is its
  `delayRead` and the destination end is its `delayWrite`, so the cut at the split needs no
  exception.
* `muted_on_cycle`, `muted_on_graph_cycle`: a muted node lies on a cycle of the split graph,
  and then on a cycle of the original graph.
* `connect_idempotent`, `connectParam_idempotent`: connecting the same termini twice gives the
  same graph as once.

## What is tested only (`#guard`)

* The converse of `muted_on_cycle` (a node on a cycle of the split graph is muted) holds by the
  definition of `mutedIds`; what is tested is that the fuel of the reachability search is
  enough (`reachAux` stops after `es.length + 1` rounds; each round adds a new vertex, and
  there are at most `es.length` distinct targets) and that the result is as expected on cycles
  of length 1, 2 and 3 and on two cycles.
* Completeness: every vertex that is not muted appears in the steps (`orderComplete`). The
  proof needs the fact that a finite graph with no cycle has a vertex with no predecessor in
  any non-empty subset; it is not proved here, so `order_topological` is stated for steps that
  are in the list. Every graph of the tests below is complete.

## Not done yet

* Nodes that are no longer alive (garbage collected) are not removed; a node stays in the
  graph for ever. The `AudioListener` is not a vertex.
* `DelayNode` `maxDelayTime` and the rule that a delay in a cycle has a minimum of one render
  quantum are for the kernel stage, not for the order.
* The kind table gives the number of inputs, outputs and parameters of the node types named in
  `Kind`; `AudioWorkletNode`, `ConvolverNode`, `AnalyserNode`, `WaveShaperNode` and the others
  go through `Kind.other` with explicit numbers.
* The `ChannelMerger`/`ChannelSplitter` counts are fixed at construction (`Kind.merger n`,
  `Kind.splitter n`); the specification's default of 6 is for the constructor, not here.
* The order that a real engine would use is a topological order with more rules (for example
  an `AnalyserNode` or a destination with no output is still processed); every node here is
  processed.
-/

namespace L4Factoidal.WebAudio.Graph

abbrev NodeId := Nat

/-- Node types. The numbers of inputs, outputs and `AudioParam`s of each are in `Kind.numInputs`,
`Kind.numOutputs` and `Kind.numParams`. -/
inductive Kind where
  | destination
  | gain
  | constantSource
  | oscillator
  | bufferSource
  | delay
  | biquad
  | stereoPanner
  | splitter (outputs : Nat)
  | merger (inputs : Nat)
  | other (name : String) (inputs outputs params : Nat)
  deriving DecidableEq, Repr

/-- `numberOfInputs` of the node: sources have 0, `ChannelMergerNode` has `n`. -/
def Kind.numInputs : Kind → Nat
  | .destination => 1
  | .gain => 1
  | .constantSource => 0
  | .oscillator => 0
  | .bufferSource => 0
  | .delay => 1
  | .biquad => 1
  | .stereoPanner => 1
  | .splitter _ => 1
  | .merger n => n
  | .other _ i _ _ => i

/-- `numberOfOutputs` of the node: `AudioDestinationNode` has 0, `ChannelSplitterNode` has `n`. -/
def Kind.numOutputs : Kind → Nat
  | .destination => 0
  | .gain => 1
  | .constantSource => 1
  | .oscillator => 1
  | .bufferSource => 1
  | .delay => 1
  | .biquad => 1
  | .stereoPanner => 1
  | .splitter n => n
  | .merger _ => 1
  | .other _ _ o _ => o

/-- Number of `AudioParam`s of the node: `gain`; `offset`; `frequency` and `detune`;
`playbackRate` and `detune`; `delayTime`; `frequency`, `detune`, `Q` and `gain`; `pan`. -/
def Kind.numParams : Kind → Nat
  | .destination => 0
  | .gain => 1
  | .constantSource => 1
  | .oscillator => 2
  | .bufferSource => 2
  | .delay => 1
  | .biquad => 4
  | .stereoPanner => 1
  | .splitter _ => 0
  | .merger _ => 0
  | .other _ _ _ p => p

/-- Output `out` of node `src` connected to input `inp` of node `dst`. -/
structure Edge where
  src : NodeId
  out : Nat
  dst : NodeId
  inp : Nat
  deriving DecidableEq, Repr

/-- Output `out` of node `src` connected to `AudioParam` number `param` of node `dst`. -/
structure ParamEdge where
  src : NodeId
  out : Nat
  dst : NodeId
  param : Nat
  deriving DecidableEq, Repr

/-- The nodes (index = `NodeId`) and the connections of one `BaseAudioContext`. -/
structure Graph where
  kinds : Array Kind
  edges : List Edge
  paramEdges : List ParamEdge
  deriving DecidableEq, Repr

/-- An entry of the ordered list of nodes. `delayWrite` and `delayRead` are the `DelayWriter` and
the `DelayReader` of a `DelayNode` that is part of a cycle (section 1.18.4 "Processing"). -/
inductive Step where
  | node (id : NodeId)
  | delayWrite (id : NodeId)
  | delayRead (id : NodeId)
  deriving DecidableEq, Repr

/-- The node a step belongs to. -/
def Step.nodeId : Step → NodeId
  | .node i => i
  | .delayWrite i => i
  | .delayRead i => i

/-- The result of the ordering step: the steps in processing order, and the nodes that are muted
(on a cycle that no `DelayNode` breaks; they output silence and are not processed). -/
structure Order where
  steps : List Step
  muted : List NodeId
  deriving DecidableEq, Repr

/-! ## Connections -/

/-- Errors of `connect` and `disconnect` (names of the `DOMException`s of the specification). -/
inductive Error where
  | indexSize
  | invalidAccess
  | unknownNode
  deriving DecidableEq, Repr

/-- An empty graph. -/
def Graph.empty : Graph := ⟨#[], [], []⟩

/-- Add a node. Returns the new graph and the id of the new node. -/
def Graph.addNode (g : Graph) (k : Kind) : Graph × NodeId :=
  ({ g with kinds := g.kinds.push k }, g.kinds.size)

/-- `connect(destinationNode, output, input)` of `AudioNode` (section 1.5.5). An output or input
index out of bounds gives `IndexSizeError`. "There can only be one connection between a given
output of one specific node and a given input of another specific node. Multiple connections with
the same termini are ignored." -/
def connect (g : Graph) (src out dst inp : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some ks, some kd =>
    if out < ks.numOutputs ∧ inp < kd.numInputs then
      if (⟨src, out, dst, inp⟩ : Edge) ∈ g.edges then .ok g
      else .ok { g with edges := g.edges ++ [⟨src, out, dst, inp⟩] }
    else .error .indexSize
  | _, _ => .error .unknownNode

/-- `connect(destinationParam, output)` of `AudioNode` (section 1.5.5). `param` is the number of
the `AudioParam` of `dst`. An output index or parameter number out of bounds gives
`IndexSizeError`. A repeated connection is ignored. -/
def connectParam (g : Graph) (src out dst param : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some ks, some kd =>
    if out < ks.numOutputs ∧ param < kd.numParams then
      if (⟨src, out, dst, param⟩ : ParamEdge) ∈ g.paramEdges then .ok g
      else .ok { g with paramEdges := g.paramEdges ++ [⟨src, out, dst, param⟩] }
    else .error .indexSize
  | _, _ => .error .unknownNode

/-- `disconnect()`: all outgoing connections of `src`, to nodes and to `AudioParam`s. -/
def disconnectAll (g : Graph) (src : Nat) : Except Error Graph :=
  match g.kinds[src]? with
  | some _ => .ok { g with edges := g.edges.filter (fun e => e.src != src),
                           paramEdges := g.paramEdges.filter (fun e => e.src != src) }
  | none => .error .unknownNode

/-- `disconnect(output)`: all outgoing connections of one output of `src`, to nodes and to
`AudioParam`s. An output index out of bounds gives `IndexSizeError`. -/
def disconnectOutput (g : Graph) (src out : Nat) : Except Error Graph :=
  match g.kinds[src]? with
  | some ks =>
    if out < ks.numOutputs then
      .ok { g with edges := g.edges.filter (fun e => !(e.src == src && e.out == out)),
                   paramEdges := g.paramEdges.filter (fun e => !(e.src == src && e.out == out)) }
    else .error .indexSize
  | none => .error .unknownNode

/-- `disconnect(destinationNode)`: all outputs of `src` that go to the node `dst`.
`InvalidAccessError` if there is no such connection. -/
def disconnectNode (g : Graph) (src dst : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some _, some _ =>
    if g.edges.any (fun e => e.src == src && e.dst == dst) then
      .ok { g with edges := g.edges.filter (fun e => !(e.src == src && e.dst == dst)) }
    else .error .invalidAccess
  | _, _ => .error .unknownNode

/-- `disconnect(destinationNode, output)`: one output of `src` from every input of `dst`.
`IndexSizeError` for a bad output; `InvalidAccessError` if there is no such connection. -/
def disconnectNodeOutput (g : Graph) (src dst out : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some ks, some _ =>
    if out < ks.numOutputs then
      if g.edges.any (fun e => e.src == src && e.dst == dst && e.out == out) then
        .ok { g with edges := g.edges.filter (fun e => !(e.src == src && e.dst == dst && e.out == out)) }
      else .error .invalidAccess
    else .error .indexSize
  | _, _ => .error .unknownNode

/-- `disconnect(destinationNode, output, input)`: one output of `src` from one input of `dst`.
`IndexSizeError` for a bad output or input; `InvalidAccessError` if there is no such connection. -/
def disconnectNodeOutputInput (g : Graph) (src dst out inp : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some ks, some kd =>
    if out < ks.numOutputs ∧ inp < kd.numInputs then
      if (⟨src, out, dst, inp⟩ : Edge) ∈ g.edges then
        .ok { g with edges := g.edges.filter (fun e => e != ⟨src, out, dst, inp⟩) }
      else .error .invalidAccess
    else .error .indexSize
  | _, _ => .error .unknownNode

/-- `disconnect(destinationParam)`: all outputs of `src` that go to `AudioParam` number `param`
of `dst`. `InvalidAccessError` if there is no such connection. -/
def disconnectParam (g : Graph) (src dst param : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some _, some _ =>
    if g.paramEdges.any (fun e => e.src == src && e.dst == dst && e.param == param) then
      .ok { g with paramEdges := g.paramEdges.filter (fun e =>
              !(e.src == src && e.dst == dst && e.param == param)) }
    else .error .invalidAccess
  | _, _ => .error .unknownNode

/-- `disconnect(destinationParam, output)`: one output of `src` from `AudioParam` number `param`
of `dst`. `IndexSizeError` for a bad output; `InvalidAccessError` if there is no such
connection. -/
def disconnectParamOutput (g : Graph) (src dst param out : Nat) : Except Error Graph :=
  match g.kinds[src]?, g.kinds[dst]? with
  | some ks, some _ =>
    if out < ks.numOutputs then
      if g.paramEdges.any (fun e => e.src == src && e.dst == dst && e.param == param && e.out == out) then
        .ok { g with paramEdges := g.paramEdges.filter (fun e =>
                !(e.src == src && e.dst == dst && e.param == param && e.out == out)) }
      else .error .invalidAccess
    else .error .indexSize
  | _, _ => .error .unknownNode

/-! ## Reachability over an edge list (fuel-bounded search, and the relation it is checked against) -/

section Reach

variable {α : Type} [DecidableEq α]

/-- `Path es a b`: there is a path of one or more edges of `es` from `a` to `b`. -/
inductive Path (es : List (α × α)) : α → α → Prop
  | edge {a b : α} : (a, b) ∈ es → Path es a b
  | step {a b c : α} : (a, b) ∈ es → Path es b c → Path es a c

/-- The targets of the edges of `es` whose source is in `fr`. -/
def expand (es : List (α × α)) (fr : List α) : List α :=
  es.filterMap (fun e => if e.1 ∈ fr then some e.2 else none)

/-- Breadth-first search. `fr` is the frontier, `seen` the vertices found so far. The recursion is
on the fuel; each round that does not stop adds at least one vertex that is not yet in `seen`. -/
def reachAux (es : List (α × α)) : Nat → List α → List α → List α
  | 0, _, seen => seen
  | f + 1, fr, seen =>
    let new := (expand es fr).filter (fun x => decide (x ∉ seen))
    if new.isEmpty then seen else reachAux es f new (seen ++ new)

/-- The vertices reachable from `v` by a path of one or more edges. Fuel: `es.length + 1`. -/
def reach (es : List (α × α)) (v : α) : List α := reachAux es (es.length + 1) [v] []

/-- `v` lies on a cycle of `es` (a path of one or more edges from `v` to `v`). -/
def onCycle (es : List (α × α)) (v : α) : Bool := decide (v ∈ reach es v)

end Reach

/-! ## The order -/

/-- The dependency edges of the graph at node level: a node that feeds an input or an
`AudioParam` of another node must be processed first. -/
def depEdges (g : Graph) : List (NodeId × NodeId) :=
  g.edges.map (fun e => (e.src, e.dst)) ++ g.paramEdges.map (fun e => (e.src, e.dst))

/-- A `DelayNode` that is part of a cycle (the "cycle breakers" of the specification). -/
def isCycleDelay (g : Graph) (n : NodeId) : Bool :=
  decide (g.kinds[n]? = some Kind.delay) && onCycle (depEdges g) n

/-- The step that stands for the source end of a connection from `a`: the `DelayReader` if `a`
is a cycle breaker, else the node. -/
def srcStep (g : Graph) (a : NodeId) : Step :=
  if isCycleDelay g a then .delayRead a else .node a

/-- The step that stands for the destination end of a connection to `b`: the `DelayWriter` if
`b` is a cycle breaker, else the node. -/
def dstStep (g : Graph) (b : NodeId) : Step :=
  if isCycleDelay g b then .delayWrite b else .node b

/-- The dependency edges between steps, after the split of the cycle breakers. -/
def stepEdges (g : Graph) : List (Step × Step) :=
  (depEdges g).map (fun p => (srcStep g p.1, dstStep g p.2))

/-- All vertices after the split: a cycle breaker gives two, any other node one. -/
def nodeSteps (g : Graph) : List Step :=
  (List.range g.kinds.size).flatMap
    (fun i => if isCycleDelay g i then [Step.delayWrite i, Step.delayRead i] else [Step.node i])

/-- The muted nodes: those on a cycle of the graph after the split. -/
def mutedIds (g : Graph) : List NodeId :=
  let se := stepEdges g
  (List.range g.kinds.size).filter (fun i => onCycle se (Step.node i))

/-- Is the step a muted node? -/
def isMuted (M : List NodeId) : Step → Bool
  | .node i => M.contains i
  | _ => false

/-- The step edges that do not touch a muted node. -/
def liveEdges (M : List NodeId) (es : List (Step × Step)) : List (Step × Step) :=
  es.filter (fun e => !isMuted M e.1 && !isMuted M e.2)

/-- The vertices that are not muted nodes. -/
def liveVerts (M : List NodeId) (vs : List Step) : List Step :=
  vs.filter (fun s => !isMuted M s)

/-- The steps that feed `v` in `es`. -/
def predsOf (es : List (Step × Step)) (v : Step) : List Step :=
  (es.filter (fun e => e.2 == v)).map (·.1)

/-- Kahn's algorithm. At each round, the first vertex of `rem` that is not yet placed and whose
feeding steps are all placed is appended to `acc`. The recursion is on the fuel. It stops when no
vertex qualifies. -/
def kahn (preds : Step → List Step) : Nat → List Step → List Step → List Step
  | 0, _, acc => acc
  | f + 1, rem, acc =>
    match rem.find? (fun v => !acc.contains v && (preds v).all (fun p => acc.contains p)) with
    | none => acc
    | some v => kahn preds f (rem.filter (fun w => w != v)) (acc ++ [v])

/-- The ordering step of "Rendering an Audio Graph". -/
def order (g : Graph) : Order :=
  let M := mutedIds g
  let es := liveEdges M (stepEdges g)
  let vs := liveVerts M (nodeSteps g)
  { steps := kahn (predsOf es) vs.length vs [], muted := M }

/-- True if every vertex that is not muted is in the steps (see the header: tested, not
proved). -/
def orderComplete (g : Graph) : Bool :=
  (order g).steps.length == (liveVerts (mutedIds g) (nodeSteps g)).length

/-! ## Tests -/

namespace Tests

/-- A graph from kinds and tuples `(src, out, dst, inp)` and `(src, out, dst, param)`. -/
def mk (ks : List Kind) (es : List (Nat × Nat × Nat × Nat))
    (pes : List (Nat × Nat × Nat × Nat) := []) : Graph :=
  ⟨ks.toArray, es.map (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩),
   pes.map (fun t => ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩)⟩

def err? (r : Except Error Graph) : Option Error :=
  match r with
  | .error e => some e
  | .ok _ => none

def pos (g : Graph) (s : Step) : Option Nat := (order g).steps.findIdx? (· == s)

/-- Step `a` is in the list, step `b` is in the list, and `a` is first. -/
def before (g : Graph) (a b : Step) : Bool :=
  match pos g a, pos g b with
  | some i, some j => decide (i < j)
  | _, _ => false

open Step Kind

-- 1. Chain, nodes numbered in processing order.
#guard (order (mk [oscillator, gain, destination] [(0,0,1,0), (1,0,2,0)])).steps
  == [node 0, node 1, node 2]
-- 2. Chain, nodes numbered against processing order.
#guard (order (mk [destination, gain, oscillator] [(2,0,1,0), (1,0,0,0)])).steps
  == [node 2, node 1, node 0]
-- 3. Fan-out: one source, two gains, one destination.
#guard
  let g := mk [oscillator, gain, gain, destination] [(0,0,1,0), (0,0,2,0), (1,0,3,0), (2,0,3,0)]
  before g (node 0) (node 1) && before g (node 0) (node 2) && before g (node 1) (node 3)
    && before g (node 2) (node 3) && (order g).muted == [] && orderComplete g
-- 4. Fan-in: two sources into one gain; the sources are numbered after it.
#guard
  let g := mk [gain, destination, oscillator, constantSource] [(2,0,0,0), (3,0,0,0), (0,0,1,0)]
  before g (node 2) (node 0) && before g (node 3) (node 0) && before g (node 0) (node 1)
    && orderComplete g
-- 5. Param connection: a source numbered after the gain feeds its gain parameter.
#guard (order (mk [gain, constantSource, destination] [(0,0,2,0)] [(1,0,0,0)])).steps
  == [node 1, node 0, node 2]
-- 6. Param connections to an oscillator detune (param 1) and frequency (param 0).
#guard
  let g := mk [oscillator, gain, oscillator, destination] [(0,0,3,0)] [(2,0,0,1), (1,0,0,0)]
  before g (node 2) (node 0) && before g (node 1) (node 0) && orderComplete g
-- 7. Cycle through a DelayNode: the delay is split, nothing is muted.
#guard
  let g := mk [gain, delay, destination, oscillator] [(3,0,0,0), (0,0,1,0), (1,0,0,0), (0,0,2,0)]
  (order g).steps == [delayRead 1, node 3, node 0, delayWrite 1, node 2] && (order g).muted == []
-- 8. In 7, there is one writer and one reader and no `node 1`.
#guard
  let g := mk [gain, delay, destination, oscillator] [(3,0,0,0), (0,0,1,0), (1,0,0,0), (0,0,2,0)]
  (order g).steps.filter (fun s => s.nodeId == 1) == [delayRead 1, delayWrite 1]
-- 9. Cycle with no DelayNode: both nodes muted, the nodes outside are still ordered.
#guard
  let g := mk [gain, gain, destination, oscillator] [(3,0,0,0), (0,0,1,0), (1,0,0,0), (1,0,2,0)]
  (order g).muted == [0, 1] && (order g).steps == [node 2, node 3] && orderComplete g
-- 10. Node downstream of a muted cycle is not muted and is processed after its other inputs.
#guard
  let g := mk [gain, gain, gain, destination, oscillator]
    [(0,0,1,0), (1,0,0,0), (1,0,2,0), (4,0,2,0), (2,0,3,0)]
  (order g).muted == [0, 1] && before g (node 4) (node 2) && before g (node 2) (node 3)
    && orderComplete g
-- 11. Two cycles, one with a DelayNode and one without.
#guard
  let g := mk [gain, gain, destination, gain, delay]
    [(0,0,1,0), (1,0,0,0), (3,0,4,0), (4,0,3,0), (3,0,2,0)]
  (order g).muted == [0, 1]
    && before g (delayRead 4) (node 3) && before g (node 3) (delayWrite 4)
    && before g (node 3) (node 2) && orderComplete g
-- 12. Two cycles that each have a DelayNode: nothing is muted, two splits.
#guard
  let g := mk [gain, delay, gain, delay, destination]
    [(0,0,1,0), (1,0,0,0), (2,0,3,0), (3,0,2,0), (0,0,4,0), (2,0,4,0)]
  (order g).muted == [] && (order g).steps.length == 7 && orderComplete g
    && before g (delayRead 1) (node 0) && before g (node 0) (delayWrite 1)
    && before g (delayRead 3) (node 2) && before g (node 2) (delayWrite 3)
-- 13. Self-connection of a gain: muted.
#guard (order (mk [gain, destination] [(0,0,0,0), (0,0,1,0)])).muted == [0]
-- 14. Self-connection of a DelayNode: split, writer after reader, nothing muted.
#guard (order (mk [delay] [(0,0,0,0)])).steps == [delayRead 0, delayWrite 0]
  && (order (mk [delay] [(0,0,0,0)])).muted == []
-- 15. Cycle through an AudioParam connection with no delay: muted.
#guard (order (mk [gain, gain] [(1,0,0,0)] [(0,0,1,0)])).muted == [0, 1]
-- 16. Cycle through an AudioParam connection with a delay: split.
#guard
  let g := mk [gain, delay] [(0,0,1,0)] [(1,0,0,0)]
  (order g).muted == [] && (order g).steps == [delayRead 1, node 0, delayWrite 1]
-- 17. A DelayNode that is not in a cycle is not split.
#guard (order (mk [oscillator, delay, destination] [(0,0,1,0), (1,0,2,0)])).steps
  == [node 0, node 1, node 2]
-- 18. A DelayNode downstream of a cycle, not in it, is not split.
#guard
  let g := mk [gain, gain, delay, destination] [(0,0,1,0), (1,0,0,0), (1,0,2,0), (2,0,3,0)]
  (order g).muted == [0, 1] && (order g).steps == [node 2, node 3]
-- 19. A cycle of three nodes with a delay in the middle.
#guard
  let g := mk [gain, delay, gain] [(0,0,1,0), (1,0,2,0), (2,0,0,0)]
  (order g).muted == [] && (order g).steps == [delayRead 1, node 2, node 0, delayWrite 1]
-- 20. A cycle of three nodes with no delay.
#guard (order (mk [gain, gain, gain] [(0,0,1,0), (1,0,2,0), (2,0,0,0)])).muted == [0, 1, 2]
-- 21. The empty graph and a graph with unconnected nodes.
#guard (order Graph.empty) == ⟨[], []⟩
#guard (order (mk [gain, delay, oscillator] [])).steps == [node 0, node 1, node 2]
-- 22. Fuel: a long cycle (60 nodes) is found; a long chain (60 nodes) has none.
#guard
  let n := 60
  let ring := mk (List.replicate n gain) ((List.range n).map (fun i => (i, 0, (i + 1) % n, 0)))
  (order ring).muted == List.range n && (order ring).steps == []
#guard
  let n := 60
  let chain := mk (List.replicate n gain) ((List.range (n - 1)).map (fun i => (i, 0, i + 1, 0)))
  (order chain).muted == [] && (order chain).steps == (List.range n).map node
-- 23. Long cycle with one delay: split, the reader first and the writer last.
#guard
  let n := 40
  let ks := (List.replicate (n - 1) gain) ++ [delay]
  let ring := mk ks ((List.range n).map (fun i => (i, 0, (i + 1) % n, 0)))
  (order ring).muted == [] && orderComplete ring && (order ring).steps.length == n + 1
    && (order ring).steps.head? == some (delayRead (n - 1))
    && (order ring).steps.getLast? == some (delayWrite (n - 1))

-- Connections.
-- 24. connect: a good connection, a repeated connection, bad indices, unknown node.
#guard (connect (mk [oscillator, gain] []) 0 0 1 0).toOption
  == some (mk [oscillator, gain] [(0,0,1,0)])
#guard ((connect (mk [oscillator, gain] []) 0 0 1 0).toOption.bind
    (fun g => (connect g 0 0 1 0).toOption))
  == some (mk [oscillator, gain] [(0,0,1,0)])
#guard err? (connect (mk [oscillator, gain] []) 0 1 1 0) == some .indexSize
#guard err? (connect (mk [oscillator, gain] []) 0 0 1 1) == some .indexSize
#guard err? (connect (mk [oscillator, gain] []) 1 0 0 0) == some .indexSize
#guard err? (connect (mk [oscillator, destination] []) 1 0 0 0) == some .indexSize
#guard err? (connect (mk [oscillator, gain] []) 0 0 7 0) == some .unknownNode
-- 25. Splitter and merger index bounds.
#guard err? (connect (mk [splitter 2, gain] []) 0 1 1 0) == none
#guard err? (connect (mk [splitter 2, gain] []) 0 2 1 0) == some .indexSize
#guard err? (connect (mk [gain, merger 3] []) 0 0 1 2) == none
#guard err? (connect (mk [gain, merger 3] []) 0 0 1 3) == some .indexSize
-- 26. connectParam: bounds and fan-in to one parameter.
#guard err? (connectParam (mk [oscillator, gain] []) 0 0 1 0) == none
#guard err? (connectParam (mk [oscillator, gain] []) 0 0 1 1) == some .indexSize
#guard err? (connectParam (mk [oscillator, oscillator] []) 0 0 1 1) == none
#guard err? (connectParam (mk [oscillator, destination] []) 0 0 1 0) == some .indexSize
#guard ((connectParam (mk [oscillator, constantSource, gain] []) 0 0 2 0).toOption.bind
    (fun g => (connectParam g 1 0 2 0).toOption.bind (fun g => (connectParam g 1 0 2 0).toOption)))
  == some (mk [oscillator, constantSource, gain] [] [(0,0,2,0), (1,0,2,0)])
-- 27. disconnect variants.
#guard
  let ks := [oscillator, gain, gain, destination]
  let g := mk ks [(0,0,1,0), (0,0,2,0), (1,0,3,0)] [(0,0,1,0)]
  (disconnectAll g 0).toOption == some (mk ks [(1,0,3,0)])
    && (disconnectOutput g 0 0).toOption == some (mk ks [(1,0,3,0)])
    && err? (disconnectOutput g 0 1) == some .indexSize
    && (disconnectNode g 0 1).toOption == some (mk ks [(0,0,2,0), (1,0,3,0)] [(0,0,1,0)])
    && err? (disconnectNode g 2 3) == some .invalidAccess
    && (disconnectNodeOutput g 0 2 0).toOption == some (mk ks [(0,0,1,0), (1,0,3,0)] [(0,0,1,0)])
    && err? (disconnectNodeOutput g 0 2 1) == some .indexSize
    && err? (disconnectNodeOutput g 1 2 0) == some .invalidAccess
    && (disconnectNodeOutputInput g 1 3 0 0).toOption
      == some (mk ks [(0,0,1,0), (0,0,2,0)] [(0,0,1,0)])
    && err? (disconnectNodeOutputInput g 1 3 0 1) == some .indexSize
    && err? (disconnectNodeOutputInput g 0 3 0 0) == some .invalidAccess
    && (disconnectParam g 0 1 0).toOption == some (mk ks [(0,0,1,0), (0,0,2,0), (1,0,3,0)])
    && err? (disconnectParam g 0 2 0) == some .invalidAccess
    && (disconnectParamOutput g 0 1 0 0).toOption
      == some (mk ks [(0,0,1,0), (0,0,2,0), (1,0,3,0)])
    && err? (disconnectParamOutput g 0 1 0 1) == some .indexSize
    && err? (disconnectParamOutput g 1 1 0 0) == some .invalidAccess
    && err? (disconnectAll g 9) == some .unknownNode
-- 28. Disconnecting the feedback edge of 7 removes the split; reconnecting it restores it.
#guard
  let g := mk [gain, delay, destination, oscillator] [(3,0,0,0), (0,0,1,0), (1,0,0,0), (0,0,2,0)]
  match disconnectNodeOutputInput g 1 0 0 0 with
  | .ok g' => (order g').steps == [node 3, node 0, node 1, node 2] && (order g').muted == []
      && (match connect g' 1 0 0 0 with | .ok g'' => order g'' == order g | _ => false)
  | .error _ => false
-- 29. Disconnecting the feedback edge of 9 un-mutes the nodes.
#guard
  let g := mk [gain, gain, destination, oscillator] [(3,0,0,0), (0,0,1,0), (1,0,0,0), (1,0,2,0)]
  match disconnectNode g 1 0 with
  | .ok g' => (order g').muted == [] && (order g').steps == [node 3, node 0, node 1, node 2]
  | .error _ => false
-- 30. Building a graph with addNode and connect.
#guard
  let (g, a) := Graph.empty.addNode oscillator
  let (g, b) := g.addNode gain
  let (g, c) := g.addNode destination
  match connect g a 0 b 0 with
  | .ok g => match connect g b 0 c 0 with
    | .ok g => (order g).steps == [node 0, node 1, node 2]
    | .error _ => false
  | .error _ => false

end Tests

end L4Factoidal.WebAudio.Graph
