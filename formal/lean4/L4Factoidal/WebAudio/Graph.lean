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
     section 1.18.4). No connection joins the two. A connection to the `delayTime` parameter
     of a split delay ends at its `delayRead` (`paramDstStep`), the step that uses `delayTime`.
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
* `order_topological_step`, `order_topological_edge`, `order_topological_param`: if a connection
  joins two nodes that are not muted, and the two steps that stand for its ends are in the
  list, the step at the source end comes first. For a delay in a cycle the source end is its
  `delayRead`; the destination end of an audio connection is its `delayWrite` and that of a
  parameter connection its `delayRead`, so the cut at the split needs no exception.
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

/-- The step that stands for the destination end of a connection to an `AudioParam` of `b`: the
`DelayReader` if `b` is a cycle breaker, else the node. The only `AudioParam` of a `DelayNode`,
`delayTime`, is used where the delay line is read (`DelayReader`), so a connection to it must be
processed before the reader, not before the writer. -/
def paramDstStep (g : Graph) (b : NodeId) : Step :=
  if isCycleDelay g b then .delayRead b else .node b

/-- The dependency edges between steps, after the split of the cycle breakers: an audio connection
ends at `dstStep` (the writer of a split delay), a parameter connection at `paramDstStep` (the
reader of a split delay). Order for a split delay `d` whose `delayTime` is fed by `s`: `s`, then
`delayRead d`; `delayWrite d` is ordered after the nodes that feed its input. A node `s` that
is reached from `delayRead d` and feeds `delayTime` of `d` is on a cycle that the split does not
cut, so it is muted. -/
def stepEdges (g : Graph) : List (Step × Step) :=
  g.edges.map (fun e => (srcStep g e.src, dstStep g e.dst)) ++
  g.paramEdges.map (fun e => (srcStep g e.src, paramDstStep g e.dst))

/-- All vertices after the split: a cycle breaker gives two, any other node one. -/
def nodeSteps (g : Graph) : List Step :=
  (List.range g.kinds.size).flatMap
    (fun i => if isCycleDelay g i then [Step.delayWrite i, Step.delayRead i] else [Step.node i])

/-- Is the step a step of a muted node? (A muted `DelayNode` loses both of its steps.) -/
def isMuted (M : List NodeId) (s : Step) : Bool := M.contains s.nodeId

/-- The step edges that do not touch a muted node. -/
def liveEdges (M : List NodeId) (es : List (Step × Step)) : List (Step × Step) :=
  es.filter (fun e => !isMuted M e.1 && !isMuted M e.2)

/-- The nodes whose own step is on a cycle of the graph after the split. -/
def mutedNodes (g : Graph) : List NodeId :=
  (List.range g.kinds.size).filter (fun i => onCycle (stepEdges g) (Step.node i))

/-- The muted nodes: those on a cycle of the graph after the split, and the `DelayNode`s in a
cycle whose `DelayReader` is on a cycle that has no other muted node. The second kind is a cycle
made only of `delayTime` connections between cycle breakers (`DelayReader` to `DelayReader`): the
split does not cut it, and no node step is on it to be muted. Without this case such a delay has
no step before it in any order and `order` would drop it. -/
def mutedIds (g : Graph) : List NodeId :=
  let se := stepEdges g
  (List.range g.kinds.size).filter
    (fun i => onCycle se (Step.node i) || onCycle (liveEdges (mutedNodes g) se) (Step.delayRead i))

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

/-! ## Theorems -/

section Proofs

variable {α : Type} [DecidableEq α]

omit [DecidableEq α] in
/-- Paths join. -/
theorem Path.trans {es : List (α × α)} {a b c : α} (h1 : Path es a b) (h2 : Path es b c) :
    Path es a c := by
  induction h1 with
  | edge h => exact Path.step h h2
  | step h _ ih => exact Path.step h (ih h2)

/-- A target found by `expand` is the target of an edge from a vertex of the frontier. -/
theorem mem_expand {es : List (α × α)} {fr : List α} {x : α} (h : x ∈ expand es fr) :
    ∃ a, a ∈ fr ∧ (a, x) ∈ es := by
  simp only [expand, List.mem_filterMap] at h
  obtain ⟨⟨a, b⟩, hmem, hx⟩ := h
  by_cases ha : a ∈ fr
  · simp only [ha, if_true, Option.some.injEq] at hx
    exact ⟨a, ha, hx ▸ hmem⟩
  · simp [ha] at hx

omit [DecidableEq α] in
private theorem ext_path {es : List (α × α)} {v a b : α} (h : a = v ∨ Path es v a)
    (hab : (a, b) ∈ es) : Path es v b := by
  rcases h with rfl | h
  · exact Path.edge hab
  · exact h.trans (Path.edge hab)

private theorem reachAux_sound (es : List (α × α)) (v : α) :
    ∀ (f : Nat) (fr seen : List α), (∀ x ∈ fr, x = v ∨ Path es v x) →
      (∀ x ∈ seen, Path es v x) → ∀ x ∈ reachAux es f fr seen, Path es v x := by
  intro f
  induction f with
  | zero => intro fr seen _ hs x hx; exact hs x (by simpa [reachAux] using hx)
  | succ f ih =>
    intro fr seen hf hs x hx
    simp only [reachAux] at hx
    by_cases hne : ((expand es fr).filter (fun x => decide (x ∉ seen))).isEmpty
    · simp only [hne, if_true] at hx
      exact hs x hx
    · simp only [hne] at hx
      have hnew : ∀ y ∈ (expand es fr).filter (fun x => decide (x ∉ seen)), Path es v y := by
        intro y hy
        obtain ⟨a, ha, hae⟩ := mem_expand (List.mem_filter.mp hy).1
        exact ext_path (hf a ha) hae
      refine ih _ _ (fun y hy => Or.inr (hnew y hy)) ?_ x hx
      intro y hy
      rcases List.mem_append.mp hy with h | h
      · exact hs y h
      · exact hnew y h

/-- Soundness of the search. Says: every vertex that `reach es v` returns is joined to `v` by a
path of one or more edges of `es`. Does not say: that the search finds every such vertex (the
fuel `es.length + 1` is tested, not proved, to be enough). -/
theorem reach_sound (es : List (α × α)) (v x : α) (h : x ∈ reach es v) : Path es v x :=
  reachAux_sound es v _ [v] [] (fun y hy => Or.inl (by simpa using hy)) (by simp) x h

private theorem reachAux_mono (es : List (α × α)) :
    ∀ (f : Nat) (fr seen : List α) (x : α), x ∈ seen → x ∈ reachAux es f fr seen := by
  intro f
  induction f with
  | zero => intro fr seen x hx; simpa [reachAux] using hx
  | succ f ih =>
    intro fr seen x hx
    simp only [reachAux]
    split
    · exact hx
    · exact ih _ _ x (List.mem_append_left _ hx)

private theorem filter_len_lt {β : Type} (q q' : β → Bool) (h : ∀ y, q' y = true → q y = true) :
    ∀ T : List β, (∃ x ∈ T, q x = true ∧ q' x = false) →
      (T.filter q').length < (T.filter q).length := by
  have hle : ∀ T : List β, (T.filter q').length ≤ (T.filter q).length := by
    intro T
    induction T with
    | nil => simp
    | cons z T ih2 =>
      simp only [List.filter_cons]
      by_cases h1 : q' z = true
      · have := h z h1
        simp [h1, this]; omega
      · by_cases h2 : q z = true <;> simp [h1, h2] <;> omega
  intro T
  induction T with
  | nil => intro ⟨x, hx, _⟩; simp at hx
  | cons y T ih =>
    intro ⟨x, hx, hqx, hq'x⟩
    rcases List.mem_cons.mp hx with rfl | hxT
    · simp only [List.filter_cons, hqx, hq'x]
      have := hle T
      simp; omega
    · have := ih ⟨x, hxT, hqx, hq'x⟩
      simp only [List.filter_cons]
      by_cases h1 : q' y = true
      · have := h y h1
        simp [h1, this]; omega
      · by_cases h2 : q y = true <;> simp [h1, h2] <;> omega

private theorem reachAux_complete (es : List (α × α)) :
    ∀ (f : Nat) (fr seen : List α),
      ((es.map Prod.snd).filter (fun x => decide (x ∉ seen))).length ≤ f →
      (∀ a b, (a, b) ∈ es → a ∈ seen → b ∈ seen ∨ a ∈ fr) →
      ∀ a b, (a, b) ∈ es → (a ∈ fr ∨ a ∈ reachAux es f fr seen) → b ∈ reachAux es f fr seen := by
  intro f
  induction f with
  | zero =>
    intro fr seen hc _ a b hab _
    simp only [reachAux]
    have hlen : ((es.map Prod.snd).filter (fun x => decide (x ∉ seen))) = [] :=
      List.length_eq_zero_iff.mp (Nat.le_zero.mp hc)
    refine Classical.byContradiction fun hb => ?_
    have : b ∈ (es.map Prod.snd).filter (fun x => decide (x ∉ seen)) := by
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨List.mem_map.mpr ⟨(a, b), hab, rfl⟩, hb⟩
    rw [hlen] at this
    simp at this
  | succ f ih =>
    intro fr seen hc hinv a b hab hh
    have hexp : ∀ a b, (a, b) ∈ es → a ∈ fr → b ∈ expand es fr := by
      intro a b hab ha
      simp only [expand, List.mem_filterMap]
      exact ⟨(a, b), hab, by simp [ha]⟩
    by_cases hne : ((expand es fr).filter (fun x => decide (x ∉ seen))).isEmpty
    · have hR : reachAux es (f + 1) fr seen = seen := by
        simp only [reachAux]; rw [if_pos hne]
      have hfr : ∀ a b, (a, b) ∈ es → a ∈ fr → b ∈ seen := by
        intro a b hab ha
        refine Classical.byContradiction fun hb => ?_
        have hm : b ∈ (expand es fr).filter (fun x => decide (x ∉ seen)) := by
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hexp a b hab ha, hb⟩
        have := List.isEmpty_iff.mp hne
        rw [this] at hm
        simp at hm
      rw [hR]
      rcases hh with ha | ha
      · exact hfr a b hab ha
      · rw [hR] at ha
        rcases hinv a b hab ha with h | h
        · exact h
        · exact hfr a b hab h
    · have hR : reachAux es (f + 1) fr seen
          = reachAux es f ((expand es fr).filter (fun x => decide (x ∉ seen)))
              (seen ++ (expand es fr).filter (fun x => decide (x ∉ seen))) := by
        simp only [reachAux]; rw [if_neg hne]
      rw [hR] at hh ⊢
      have hnew_mem : ∀ y, y ∈ (expand es fr).filter (fun x => decide (x ∉ seen)) →
          y ∈ expand es fr ∧ y ∉ seen := by
        intro y hy
        simpa [List.mem_filter] using hy
      generalize hnew : (expand es fr).filter (fun x => decide (x ∉ seen)) = new at *
      have hbnew : ∀ a b, (a, b) ∈ es → a ∈ fr → b ∈ seen ++ new := by
        intro a b hab ha
        by_cases hb : b ∈ seen
        · exact List.mem_append_left _ hb
        · refine List.mem_append_right _ ?_
          rw [← hnew]
          simp only [List.mem_filter, decide_eq_true_eq]
          exact ⟨hexp a b hab ha, hb⟩
      have hcount : ((es.map Prod.snd).filter (fun x => decide (x ∉ seen ++ new))).length ≤ f := by
        have hx : ∃ x, x ∈ new := by
          cases new with
          | nil => simp at hne
          | cons x xs => exact ⟨x, List.mem_cons_self⟩
        obtain ⟨x, hx⟩ := hx
        obtain ⟨hxe, hxs⟩ := hnew_mem x hx
        obtain ⟨a', ha', hxa⟩ := mem_expand hxe
        have hlt := filter_len_lt (fun x => decide (x ∉ seen)) (fun x => decide (x ∉ seen ++ new))
          (by intro y hy; simp only [decide_eq_true_eq, List.mem_append, not_or] at hy ⊢; exact hy.1)
          (es.map Prod.snd)
          ⟨x, List.mem_map.mpr ⟨(a', x), hxa, rfl⟩,
            by simpa using hxs, by simp [hx]⟩
        omega
      have hinv' : ∀ a b, (a, b) ∈ es → a ∈ seen ++ new → b ∈ seen ++ new ∨ a ∈ new := by
        intro a b hab ha
        rcases List.mem_append.mp ha with ha | ha
        · rcases hinv a b hab ha with h | h
          · exact Or.inl (List.mem_append_left _ h)
          · exact Or.inl (hbnew a b hab h)
        · exact Or.inr ha
      rcases hh with ha | ha
      · exact reachAux_mono es f _ _ b (hbnew a b hab ha)
      · exact ih new (seen ++ new) hcount hinv' a b hab (Or.inr ha)

/-- Says: if `onCycle es v` is true, there is a path of one or more edges from `v` to `v`.
Does not say: the converse (see `reach_sound`). -/
theorem onCycle_sound {es : List (α × α)} {v : α} (h : onCycle es v = true) : Path es v v :=
  reach_sound es v v (by simpa [onCycle] using h)

private theorem reach_complete_aux (es : List (α × α)) (v : α) :
    ∀ a c, Path es a c → (a = v ∨ a ∈ reach es v) → c ∈ reach es v := by
  have hstep : ∀ a b, (a, b) ∈ es → (a = v ∨ a ∈ reach es v) → b ∈ reach es v := by
    intro a b hab ha
    refine reachAux_complete es (es.length + 1) [v] [] ?_ (by simp) a b hab ?_
    · have := List.length_filter_le (fun x => decide (x ∉ ([] : List α))) (es.map Prod.snd)
      rw [List.length_map] at this
      omega
    · rcases ha with rfl | ha
      · exact Or.inl (by simp)
      · exact Or.inr ha
  intro a c hp
  induction hp with
  | @edge a b hab => exact fun ha => hstep a b hab ha
  | @step a b c hab _ ih => exact fun ha => ih (Or.inr (hstep a b hab ha))

/-- Completeness of the search: every vertex joined to `v` by a path of one or more edges of `es`
is returned by `reach es v`. The fuel `es.length + 1` is enough because each round that does not
stop adds a target that is not yet found, and `es` has at most `es.length` targets. Does not say:
anything about the order of the result. -/
theorem reach_complete (es : List (α × α)) (v x : α) (h : Path es v x) : x ∈ reach es v :=
  reach_complete_aux es v v x h (Or.inl rfl)

/-- Says: `onCycle es v` is true exactly when there is a path of one or more edges from `v` to `v`.
Does not say: how long the cycle is. -/
theorem onCycle_iff {es : List (α × α)} {v : α} : onCycle es v = true ↔ Path es v v :=
  ⟨onCycle_sound, fun h => by simpa [onCycle] using reach_complete es v v h⟩

/-! ### Muted nodes lie on cycles -/

theorem nodeId_srcStep (g : Graph) (a : NodeId) : (srcStep g a).nodeId = a := by
  unfold srcStep; split <;> rfl

theorem nodeId_dstStep (g : Graph) (b : NodeId) : (dstStep g b).nodeId = b := by
  unfold dstStep; split <;> rfl

theorem nodeId_paramDstStep (g : Graph) (b : NodeId) : (paramDstStep g b).nodeId = b := by
  unfold paramDstStep; split <;> rfl

omit [DecidableEq α] in
/-- Paths survive adding edges. -/
theorem path_mono {E1 E2 : List (α × α)} (h : ∀ e ∈ E1, e ∈ E2) {a b : α} (p : Path E1 a b) :
    Path E2 a b := by
  induction p with
  | edge hm => exact Path.edge (h _ hm)
  | step hm _ ih => exact Path.step (h _ hm) ih

omit [DecidableEq α] in
/-- A finite non-empty set of vertices on none of which `Path E` has a cycle has a vertex that no
vertex of the set reaches. This replaces the counting argument on the length of a walk. -/
theorem path_minimal {E : List (α × α)} : ∀ R : List α, R ≠ [] → (∀ x ∈ R, ¬ Path E x x) →
    ∃ v ∈ R, ∀ p ∈ R, ¬ Path E p v := by
  intro R
  induction R with
  | nil => intro h; exact absurd rfl h
  | cons a R ih =>
    intro _ hirr
    by_cases hR : R = []
    · subst hR
      refine ⟨a, List.mem_cons_self, ?_⟩
      intro p hp
      have : p = a := by simpa using hp
      subst this
      exact hirr _ List.mem_cons_self
    · obtain ⟨v, hv, hmin⟩ := ih hR (fun x hx => hirr x (List.mem_cons_of_mem _ hx))
      by_cases hav : Path E a v
      · refine ⟨a, List.mem_cons_self, ?_⟩
        intro p hp hpa
        rcases List.mem_cons.mp hp with rfl | hpR
        · exact hirr _ List.mem_cons_self hpa
        · exact hmin p hpR (hpa.trans hav)
      · refine ⟨v, List.mem_cons_of_mem _ hv, ?_⟩
        intro p hp hpv
        rcases List.mem_cons.mp hp with rfl | hpR
        · exact hav hpv
        · exact hmin p hpR hpv

/-- An edge of the split graph gives an edge of the original graph between the same nodes. -/
theorem stepEdge_project (g : Graph) {x y : Step} (hm : (x, y) ∈ stepEdges g) :
    (x.nodeId, y.nodeId) ∈ depEdges g := by
  simp only [stepEdges, depEdges, List.mem_append, List.mem_map] at hm ⊢
  rcases hm with ⟨e, he, h⟩ | ⟨e, he, h⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [nodeId_srcStep, nodeId_dstStep]
    exact Or.inl ⟨e, he, rfl⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    rw [nodeId_srcStep, nodeId_paramDstStep]
    exact Or.inr ⟨e, he, rfl⟩

/-- A path in the split graph gives a path in the original graph between the same nodes. -/
theorem path_project (g : Graph) {x y : Step} (h : Path (stepEdges g) x y) :
    Path (depEdges g) x.nodeId y.nodeId := by
  induction h with
  | edge hm => exact Path.edge (stepEdge_project g hm)
  | step hm _ ih => exact Path.step (stepEdge_project g hm) ih

/-- Says: a node listed in `muted` has a path of one or more connections back to itself in the
graph after the `DelayNode`s that are in cycles have been split (`stepEdges`), through its own node
step; or it is a `DelayNode` whose `DelayReader` has such a path through connections that touch no
node of the first kind (a cycle of `delayTime` connections between cycle breakers). Does not say:
that every node on such a cycle is listed (that is the definition of `mutedIds`; completeness of
the search is `reach_complete`); and nothing about a node that only receives from a muted node,
which is not muted. -/
theorem muted_on_cycle (g : Graph) {i : NodeId} (h : i ∈ (order g).muted) :
    Path (stepEdges g) (Step.node i) (Step.node i) ∨
    Path (liveEdges (mutedNodes g) (stepEdges g)) (Step.delayRead i) (Step.delayRead i) := by
  simp only [order, mutedIds, List.mem_filter, Bool.or_eq_true] at h
  rcases h.2 with h2 | h2
  · exact Or.inl (onCycle_sound h2)
  · exact Or.inr (onCycle_sound h2)

/-- Says: a node listed in `muted` is on a cycle of the graph as the author connected it (audio and
parameter connections both count). Does not say: the converse. A node on a cycle that passes
through a `DelayNode` is not muted, because the split cuts that cycle. -/
theorem muted_on_graph_cycle (g : Graph) {i : NodeId} (h : i ∈ (order g).muted) :
    Path (depEdges g) i i := by
  rcases muted_on_cycle g h with h1 | h1
  · have := path_project g h1
    simpa [Step.nodeId] using this
  · have := path_project g (path_mono (fun e he => (List.mem_filter.mp he).1) h1)
    simpa [Step.nodeId] using this

end Proofs

/-! ### Properties of Kahn's algorithm -/

/-- `Good preds l`: every entry of `l` has all of its feeding steps (`preds`) earlier in `l`. -/
def Good (preds : Step → List Step) (l : List Step) : Prop :=
  ∀ (j : Nat) (v : Step), l[j]? = some v → ∀ p ∈ preds v, ∃ i : Nat, i < j ∧ l[i]? = some p

theorem good_nil (preds : Step → List Step) : Good preds [] := by
  intro j v h; simp at h

theorem good_snoc (preds : Step → List Step) {acc : List Step} (hg : Good preds acc) (v : Step)
    (hp : ∀ p ∈ preds v, p ∈ acc) : Good preds (acc ++ [v]) := by
  intro j w hw p hpw
  by_cases hj : j < acc.length
  · rw [List.getElem?_append_left hj] at hw
    obtain ⟨i, hi, hip⟩ := hg j w hw p hpw
    have hi' : i < acc.length := Nat.lt_trans hi hj
    exact ⟨i, hi, by rw [List.getElem?_append_left hi']; exact hip⟩
  · have hj' : j = acc.length := by
      have h1 := (List.getElem?_eq_some_iff.mp hw).1
      simp at h1
      omega
    subst hj'
    have hwv : w = v := by simpa using hw.symm
    subst hwv
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp (hp p hpw)
    have hil : i < acc.length := (List.getElem?_eq_some_iff.mp hi).1
    exact ⟨i, hil, by rw [List.getElem?_append_left hil]; exact hi⟩

theorem kahn_good (preds : Step → List Step) :
    ∀ (f : Nat) (rem acc : List Step), Good preds acc → Good preds (kahn preds f rem acc) := by
  intro f
  induction f with
  | zero => intro rem acc h; simpa [kahn] using h
  | succ f ih =>
    intro rem acc h
    simp only [kahn]
    split
    · exact h
    · rename_i v hv
      have hsome := List.find?_some hv
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hsome
      exact ih _ _ (good_snoc preds h v hsome.2)

theorem kahn_nodup (preds : Step → List Step) :
    ∀ (f : Nat) (rem acc : List Step), acc.Nodup → (kahn preds f rem acc).Nodup := by
  intro f
  induction f with
  | zero => intro rem acc h; simpa [kahn] using h
  | succ f ih =>
    intro rem acc h
    simp only [kahn]
    split
    · exact h
    · rename_i v hv
      have hsome := List.find?_some hv
      have hv : v ∉ acc := (by simpa using hsome : v ∉ acc ∧ ∀ x ∈ preds v, x ∈ acc).1
      refine ih _ _ ?_
      rw [List.nodup_append]
      refine ⟨h, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩, ?_⟩
      intro a ha b hb
      simp only [List.mem_singleton] at hb
      subst hb
      intro hab
      exact hv (hab ▸ ha)

/-- Says: Kahn's loop with enough fuel (`rem.length`) lists every vertex of `rem`, provided that
(a) every non-empty set of vertices of the kind `Q` has a vertex with no feeding step in the set
(`hacyc`), (b) no vertex of `rem` is placed yet, and (c) every feeding step of a vertex of `rem` is
in `rem` or placed. Does not say: anything about the order (see `kahn_good`). -/
theorem kahn_complete (preds : Step → List Step) (Q : Step → Prop)
    (hacyc : ∀ R : List Step, R ≠ [] → (∀ x ∈ R, Q x) → ∃ v ∈ R, ∀ p ∈ preds v, p ∉ R) :
    ∀ (f : Nat) (rem acc : List Step), rem.length ≤ f → (∀ w ∈ rem, Q w) → (∀ w ∈ rem, w ∉ acc) →
      (∀ w ∈ rem, ∀ p ∈ preds w, p ∈ rem ∨ p ∈ acc) →
      ∀ x, (x ∈ rem ∨ x ∈ acc) → x ∈ kahn preds f rem acc := by
  intro f
  induction f with
  | zero =>
    intro rem acc hl _ _ _ x hx
    have : rem = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hl)
    subst this
    simpa [kahn] using hx
  | succ f ih =>
    intro rem acc hl hQ hdisj hcl x hx
    simp only [kahn]
    split
    · rename_i hv
      by_cases hrem : rem = []
      · subst hrem
        simpa using hx
      · obtain ⟨v, hvR, hvmin⟩ := hacyc rem hrem hQ
        have hno := List.find?_eq_none.mp hv v hvR
        exfalso
        apply hno
        simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, Bool.not_eq_true']
        refine ⟨by simpa using hdisj v hvR, ?_⟩
        intro p hp
        rcases hcl v hvR p hp with h | h
        · exact absurd h (hvmin p hp)
        · exact h
    · rename_i v hv
      have hsome := List.find?_some hv
      have hvR : v ∈ rem := List.mem_of_find?_eq_some hv
      simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at hsome
      have hlt : (rem.filter (fun w => w != v)).length < rem.length := by
        rw [List.length_filter_lt_length_iff_exists]
        exact ⟨v, hvR, by simp⟩
      refine ih _ _ (by omega) ?_ ?_ ?_ x ?_
      · intro w hw; exact hQ w (List.mem_filter.mp hw).1
      · intro w hw
        have hw' := List.mem_filter.mp hw
        have : w ≠ v := by simpa using hw'.2
        simp only [List.mem_append, List.mem_singleton, not_or]
        exact ⟨hdisj w hw'.1, this⟩
      · intro w hw p hp
        have hw' := List.mem_filter.mp hw
        rcases hcl w hw'.1 p hp with h | h
        · by_cases hpv : p = v
          · subst hpv; right; simp
          · left; exact List.mem_filter.mpr ⟨h, by simpa using hpv⟩
        · right; exact List.mem_append_left _ h
      · rcases hx with h | h
        · by_cases hxv : x = v
          · subst hxv; right; simp
          · left; exact List.mem_filter.mpr ⟨h, by simpa using hxv⟩
        · right; exact List.mem_append_left _ h

/-- Says: no step is listed twice. Does not say: that every vertex is listed (see
`orderComplete`). -/
theorem order_nodup (g : Graph) : (order g).steps.Nodup :=
  kahn_nodup _ _ _ _ List.nodup_nil

theorem order_good (g : Graph) :
    Good (predsOf (liveEdges (mutedIds g) (stepEdges g))) (order g).steps :=
  kahn_good _ _ _ _ (good_nil _)

private theorem isMuted_srcStep (g : Graph) {a : NodeId} (ha : a ∉ mutedIds g) :
    isMuted (mutedIds g) (srcStep g a) = false := by
  unfold isMuted
  rw [nodeId_srcStep]
  simpa using ha

private theorem isMuted_dstStep (g : Graph) {a : NodeId} (ha : a ∉ mutedIds g) :
    isMuted (mutedIds g) (dstStep g a) = false := by
  unfold isMuted
  rw [nodeId_dstStep]
  simpa using ha

private theorem isMuted_paramDstStep (g : Graph) {a : NodeId} (ha : a ∉ mutedIds g) :
    isMuted (mutedIds g) (paramDstStep g a) = false := by
  unfold isMuted
  rw [nodeId_paramDstStep]
  simpa using ha

/-- If `(x, y)` is an edge of the split graph, neither end a muted node, then `x` comes before `y`
in the steps (when both are listed). -/
theorem order_topological_step (g : Graph) {x y : Step} (hxy : (x, y) ∈ stepEdges g)
    (hx : isMuted (mutedIds g) x = false) (hy : isMuted (mutedIds g) y = false) {i j : Nat}
    (hi : (order g).steps[i]? = some x) (hj : (order g).steps[j]? = some y) : i < j := by
  have hmem : (x, y) ∈ liveEdges (mutedIds g) (stepEdges g) := by
    simp only [liveEdges, List.mem_filter]
    exact ⟨hxy, by simp [hx, hy]⟩
  have hp : x ∈ predsOf (liveEdges (mutedIds g) (stepEdges g)) y := by
    simp only [predsOf, List.mem_map, List.mem_filter]
    exact ⟨(x, y), ⟨hmem, by simp⟩, rfl⟩
  have hg := order_good g
  unfold Good at hg
  obtain ⟨i', hi', hi'e⟩ := hg j _ hj _ hp
  have hil : i < (order g).steps.length := (List.getElem?_eq_some_iff.mp hi).1
  have : i = i' := (List.getElem?_inj hil (order_nodup g)).mp (by rw [hi, hi'e])
  omega

/-- Says: take an audio connection from `e.src` to `e.dst`, neither node muted. Let the source end
be `srcStep g e.src` (the node, or its `DelayReader` if it is a `DelayNode` on a cycle) and the
destination end be `dstStep g e.dst` (the node, or its `DelayWriter`). If the source end is at index
`i` and the destination end at index `j` of the steps, then `i < j`. Does not say: that both ends
are in the list (see `orderComplete`); anything about a connection with a muted end; anything
about the order of two steps that no connection relates. -/
theorem order_topological_edge (g : Graph) {e : Edge} (he : e ∈ g.edges)
    (ha : e.src ∉ (order g).muted) (hb : e.dst ∉ (order g).muted) {i j : Nat}
    (hi : (order g).steps[i]? = some (srcStep g e.src))
    (hj : (order g).steps[j]? = some (dstStep g e.dst)) : i < j :=
  order_topological_step g
    (by simp only [stepEdges, List.mem_append, List.mem_map]
        exact Or.inl ⟨e, he, rfl⟩)
    (isMuted_srcStep g ha) (isMuted_dstStep g hb) hi hj

/-- Says: the same for a parameter connection, whose destination end is `paramDstStep g e.dst`:
the node itself, or the `DelayReader` of a `DelayNode` on a cycle (where `delayTime` is used). The
node that feeds an `AudioParam` comes before the step that uses the parameter. Does not say: that
both ends are listed, or that the source comes before the `DelayWriter` of the same delay. -/
theorem order_topological_param (g : Graph) {e : ParamEdge} (he : e ∈ g.paramEdges)
    (ha : e.src ∉ (order g).muted) (hb : e.dst ∉ (order g).muted) {i j : Nat}
    (hi : (order g).steps[i]? = some (srcStep g e.src))
    (hj : (order g).steps[j]? = some (paramDstStep g e.dst)) : i < j :=
  order_topological_step g
    (by simp only [stepEdges, List.mem_append, List.mem_map]
        exact Or.inr ⟨e, he, rfl⟩)
    (isMuted_srcStep g ha) (isMuted_paramDstStep g hb) hi hj

/-! ### Completeness of the order -/

/-- Every connection joins two nodes of the graph. `connect` and `connectParam` keep this true
(`connect_wellFormed`, `connectParam_wellFormed`), and so do the `disconnect` functions, which only
remove connections. -/
def WellFormed (g : Graph) : Prop :=
  (∀ e ∈ g.edges, e.src < g.kinds.size ∧ e.dst < g.kinds.size) ∧
  (∀ e ∈ g.paramEdges, e.src < g.kinds.size ∧ e.dst < g.kinds.size)

theorem mem_predsOf {es : List (Step × Step)} {p v : Step} : p ∈ predsOf es v ↔ (p, v) ∈ es := by
  simp only [predsOf, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨hm, hb⟩, rfl⟩
    simp only at hb ⊢
    subst hb
    exact hm
  · intro h
    exact ⟨(p, v), ⟨h, rfl⟩, rfl⟩

theorem nodeSteps_lt {g : Graph} {s : Step} (h : s ∈ nodeSteps g) : s.nodeId < g.kinds.size := by
  simp only [nodeSteps, List.mem_flatMap, List.mem_range] at h
  obtain ⟨i, hi, hs⟩ := h
  by_cases hc : isCycleDelay g i = true
  · rw [if_pos hc] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> simpa [Step.nodeId] using hi
  · rw [if_neg hc] at hs
    simp only [List.mem_singleton] at hs
    subst hs
    simpa [Step.nodeId] using hi

theorem srcStep_mem {g : Graph} {i : NodeId} (hi : i < g.kinds.size) : srcStep g i ∈ nodeSteps g := by
  simp only [nodeSteps, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  unfold srcStep
  by_cases hc : isCycleDelay g i = true <;> simp [hc]

theorem dstStep_mem {g : Graph} {i : NodeId} (hi : i < g.kinds.size) : dstStep g i ∈ nodeSteps g := by
  simp only [nodeSteps, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  unfold dstStep
  by_cases hc : isCycleDelay g i = true <;> simp [hc]

theorem paramDstStep_mem {g : Graph} {i : NodeId} (hi : i < g.kinds.size) :
    paramDstStep g i ∈ nodeSteps g := by
  simp only [nodeSteps, List.mem_flatMap, List.mem_range]
  refine ⟨i, hi, ?_⟩
  unfold paramDstStep
  by_cases hc : isCycleDelay g i = true <;> simp [hc]

/-- Both ends of a step edge are vertices of the split graph. -/
theorem stepEdge_mem_nodeSteps {g : Graph} (hwf : WellFormed g) {x y : Step}
    (h : (x, y) ∈ stepEdges g) : x ∈ nodeSteps g ∧ y ∈ nodeSteps g := by
  simp only [stepEdges, List.mem_append, List.mem_map] at h
  rcases h with ⟨e, he, hxy⟩ | ⟨e, he, hxy⟩
  · obtain ⟨h1, h2⟩ := hwf.1 e he
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact ⟨srcStep_mem h1, dstStep_mem h2⟩
  · obtain ⟨h1, h2⟩ := hwf.2 e he
    simp only [Prod.mk.injEq] at hxy
    obtain ⟨rfl, rfl⟩ := hxy
    exact ⟨srcStep_mem h1, paramDstStep_mem h2⟩

/-- No step edge starts at a `DelayWriter`: it has no output. -/
theorem no_delayWrite_src (g : Graph) {i : NodeId} {y : Step} : (Step.delayWrite i, y) ∉ stepEdges g := by
  intro h
  simp only [stepEdges, List.mem_append, List.mem_map, Prod.mk.injEq] at h
  rcases h with ⟨e, _, h1, _⟩ | ⟨e, _, h1, _⟩ <;>
    (unfold srcStep at h1; split at h1 <;> simp at h1)

theorem isMuted_mono {M0 M : List NodeId} (h : ∀ i ∈ M0, i ∈ M) {s : Step}
    (hs : isMuted M0 s = true) : isMuted M s = true := by
  simp only [isMuted, List.contains_iff_mem] at hs ⊢
  exact h _ hs

theorem liveEdges_mono {M0 M : List NodeId} (h : ∀ i ∈ M0, i ∈ M) (es : List (Step × Step)) :
    ∀ e ∈ liveEdges M es, e ∈ liveEdges M0 es := by
  intro e he
  simp only [liveEdges, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at he ⊢
  obtain ⟨h1, h2, h3⟩ := he
  refine ⟨h1, ?_, ?_⟩
  · cases hh : isMuted M0 e.1
    · rfl
    · have := isMuted_mono h hh
      rw [h2] at this
      cases this
  · cases hh : isMuted M0 e.2
    · rfl
    · have := isMuted_mono h hh
      rw [h3] at this
      cases this

/-- Says: the graph of the steps that are not muted has no cycle: no live step has a path of one or
more live connections back to itself. A cycle through a live node step would put the node on a cycle
of `stepEdges`, which `mutedIds` lists (this uses `reach_complete`); a `DelayWriter` has no output;
a cycle through a `DelayReader` alone is listed by the second condition of `mutedIds`. Does not
say: anything about a graph that is not well formed (none is needed: the steps considered are
vertices). -/
theorem live_acyclic (g : Graph) :
    ∀ x ∈ liveVerts (mutedIds g) (nodeSteps g), ¬ Path (liveEdges (mutedIds g) (stepEdges g)) x x := by
  intro x hx hp
  simp only [liveVerts, List.mem_filter, Bool.not_eq_true'] at hx
  obtain ⟨hxn, hxm⟩ := hx
  have hsub : ∀ e ∈ liveEdges (mutedIds g) (stepEdges g), e ∈ stepEdges g :=
    fun e he => (List.mem_filter.mp he).1
  have hM0 : ∀ i ∈ mutedNodes g, i ∈ mutedIds g := by
    intro i hi
    simp only [mutedNodes, mutedIds, List.mem_filter, Bool.or_eq_true] at hi ⊢
    exact ⟨hi.1, Or.inl hi.2⟩
  have hlt := nodeSteps_lt hxn
  cases x with
  | node i =>
    have hc : onCycle (stepEdges g) (Step.node i) = true := onCycle_iff.mpr (path_mono hsub hp)
    have hi : i ∈ mutedIds g := by
      simp only [mutedIds, List.mem_filter, List.mem_range, Bool.or_eq_true]
      exact ⟨hlt, Or.inl hc⟩
    simp only [isMuted, List.contains_eq_mem, decide_eq_false_iff_not] at hxm
    exact hxm hi
  | delayWrite i =>
    cases hp with
    | edge h => exact no_delayWrite_src g (hsub _ h)
    | step h _ => exact no_delayWrite_src g (hsub _ h)
  | delayRead i =>
    have hc : onCycle (liveEdges (mutedNodes g) (stepEdges g)) (Step.delayRead i) = true :=
      onCycle_iff.mpr (path_mono (liveEdges_mono hM0 _) hp)
    have hi : i ∈ mutedIds g := by
      simp only [mutedIds, List.mem_filter, List.mem_range, Bool.or_eq_true]
      exact ⟨hlt, Or.inr hc⟩
    simp only [isMuted, List.contains_eq_mem, decide_eq_false_iff_not] at hxm
    exact hxm hi

/-- Says: in a well-formed graph, every step of the split graph (`nodeSteps`) that does not belong to
a muted node is in `(order g).steps`. Together with `order_nodup` and the topological theorems, the
steps are exactly the live steps, each once, in an order that respects the connections. Does not say:
which topological order is chosen (the specification does not fix one); anything about a graph with
a connection to a node number outside the graph (such a connection cannot be made with `connect`,
`connectParam`: see `connect_wellFormed`). -/
theorem order_complete (g : Graph) (hwf : WellFormed g) {s : Step} (hs : s ∈ nodeSteps g)
    (hm : isMuted (mutedIds g) s = false) : s ∈ (order g).steps := by
  have hsv : s ∈ liveVerts (mutedIds g) (nodeSteps g) := by
    simp only [liveVerts, List.mem_filter, Bool.not_eq_true']
    exact ⟨hs, hm⟩
  unfold order
  simp only
  refine kahn_complete (predsOf (liveEdges (mutedIds g) (stepEdges g)))
    (fun x => x ∈ liveVerts (mutedIds g) (nodeSteps g)) ?_ _ _ [] (Nat.le_refl _)
    (fun w hw => hw) (by simp) ?_ s (Or.inl hsv)
  · intro R hR hQ
    obtain ⟨v, hv, hmin⟩ := path_minimal (E := liveEdges (mutedIds g) (stepEdges g)) R hR
      (fun x hx => live_acyclic g x (hQ x hx))
    refine ⟨v, hv, fun p hp hpR => hmin p hpR (Path.edge (mem_predsOf.mp hp))⟩
  · intro w hw p hp
    left
    have hmem := mem_predsOf.mp hp
    simp only [liveEdges, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hmem
    obtain ⟨hse, hp1, _⟩ := hmem
    simp only [liveVerts, List.mem_filter, Bool.not_eq_true']
    exact ⟨(stepEdge_mem_nodeSteps hwf hse).1, hp1⟩

/-! ### Connecting twice -/

/-- Says: if `connect g a o b i` succeeds with result `g'`, connecting the same output to the same
input in `g'` succeeds and gives `g'` again (the specification: "Multiple connections with the
same termini are ignored"). Does not say: that two different connect calls commute. -/
theorem connect_idempotent {g g' : Graph} {a o b i : Nat} (h : connect g a o b i = .ok g') :
    connect g' a o b i = .ok g' := by
  unfold connect at h ⊢
  split at h
  · rename_i ks kd hks hkd
    by_cases hb : o < ks.numOutputs ∧ i < kd.numInputs
    · simp only [hb, and_self, if_true] at h
      by_cases hm : (⟨a, o, b, i⟩ : Edge) ∈ g.edges
      · simp only [hm, if_true] at h
        cases h
        simp [hks, hkd, hb, hm]
      · simp only [hm, if_false] at h
        cases h
        simp [hks, hkd, hb]
    · simp [hb] at h
  · simp at h

/-- Says: the same for `connectParam`. Does not say: anything about parameters of other nodes. -/
theorem connectParam_idempotent {g g' : Graph} {a o b p : Nat}
    (h : connectParam g a o b p = .ok g') : connectParam g' a o b p = .ok g' := by
  unfold connectParam at h ⊢
  split at h
  · rename_i ks kd hks hkd
    by_cases hb : o < ks.numOutputs ∧ p < kd.numParams
    · simp only [hb, and_self, if_true] at h
      by_cases hm : (⟨a, o, b, p⟩ : ParamEdge) ∈ g.paramEdges
      · simp only [hm, if_true] at h
        cases h
        simp [hks, hkd, hb, hm]
      · simp only [hm, if_false] at h
        cases h
        simp [hks, hkd, hb]
    · simp [hb] at h
  · simp at h

theorem idx_lt {ks : Array Kind} {a : Nat} {k : Kind} (h : ks[a]? = some k) : a < ks.size :=
  (Array.getElem?_eq_some_iff.mp h).1

/-- Says: `connect` keeps a well-formed graph well formed. Does not say: that the connection is
made (it can fail with an error, and then there is no new graph). -/
theorem connect_wellFormed {g g' : Graph} (hwf : WellFormed g) {a o b i : Nat}
    (h : connect g a o b i = .ok g') : WellFormed g' := by
  unfold connect at h
  split at h
  · rename_i ks kd hks hkd
    have ha := idx_lt hks
    have hb' := idx_lt hkd
    by_cases hb : o < ks.numOutputs ∧ i < kd.numInputs
    · simp only [hb, and_self, if_true] at h
      by_cases hm : (⟨a, o, b, i⟩ : Edge) ∈ g.edges
      · simp only [hm, if_true] at h
        cases h
        exact hwf
      · simp only [hm, if_false] at h
        cases h
        refine ⟨?_, hwf.2⟩
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hwf.1 e he
        · exact ⟨ha, hb'⟩
    · simp [hb] at h
  · simp at h

/-- Says: the same for `connectParam`. -/
theorem connectParam_wellFormed {g g' : Graph} (hwf : WellFormed g) {a o b p : Nat}
    (h : connectParam g a o b p = .ok g') : WellFormed g' := by
  unfold connectParam at h
  split at h
  · rename_i ks kd hks hkd
    have ha := idx_lt hks
    have hb' := idx_lt hkd
    by_cases hb : o < ks.numOutputs ∧ p < kd.numParams
    · simp only [hb, and_self, if_true] at h
      by_cases hm : (⟨a, o, b, p⟩ : ParamEdge) ∈ g.paramEdges
      · simp only [hm, if_true] at h
        cases h
        exact hwf
      · simp only [hm, if_false] at h
        cases h
        refine ⟨hwf.1, ?_⟩
        intro e he
        simp only [List.mem_append, List.mem_singleton] at he
        rcases he with he | rfl
        · exact hwf.2 e he
        · exact ⟨ha, hb'⟩
    · simp [hb] at h
  · simp at h

theorem empty_wellFormed : WellFormed Graph.empty := by
  simp [WellFormed, Graph.empty]

/-- Says: adding a node keeps a graph well formed. -/
theorem addNode_wellFormed (g : Graph) (k : Kind) (hwf : WellFormed g) :
    WellFormed (g.addNode k).1 := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · obtain ⟨h1, h2⟩ := hwf.1 e he
    show e.src < (g.kinds.push k).size ∧ e.dst < (g.kinds.push k).size
    rw [Array.size_push]
    exact ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2⟩
  · obtain ⟨h1, h2⟩ := hwf.2 e he
    show e.src < (g.kinds.push k).size ∧ e.dst < (g.kinds.push k).size
    rw [Array.size_push]
    exact ⟨Nat.lt_succ_of_lt h1, Nat.lt_succ_of_lt h2⟩

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

-- 23b. Parameter edge into a split delay goes to the reader. The cycle: delay 1 -> gain 0 ->
-- delay 1 (input). Source 3 (a constant source numbered after the delay) feeds `delayTime` of 1.
-- Order: 3, delayRead 1, node 0, delayWrite 1, node 2. Before the fix, 3 was ordered after the
-- reader only by number, and the reader did not wait for it.
#guard
  let g := mk [gain, delay, destination, constantSource] [(0,0,1,0), (1,0,0,0), (0,0,2,0)]
    [(3,0,1,0)]
  (order g).muted == [] && (order g).steps == [node 3, delayRead 1, node 0, delayWrite 1, node 2]
    && before g (node 3) (delayRead 1)
-- 23c. A node of the cycle that feeds `delayTime` of its own delay: the loop delay-out -> gain ->
-- delayTime is not cut by the split (the reader needs the gain, the gain needs the reader), so the
-- gain is muted and its edges are dropped; no step precedes the writer or the reader, so they
-- keep the order of `nodeSteps` (writer, reader).
#guard
  let g := mk [gain, delay, destination] [(0,0,1,0), (1,0,0,0), (0,0,2,0)] [(0,0,1,0)]
  (order g).muted == [0] && (order g).steps == [delayWrite 1, delayRead 1, node 2]

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
