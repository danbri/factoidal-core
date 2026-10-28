/-
L4Factoidal.Dataflow.Graph — pipelines as acyclic graphs of stages with
named, typed input ports (https://github.com/danbri/factoidal/issues/1130,
stage 1 of https://github.com/danbri/factoidal/issues/1129).

Owner, 2026-10-28, verbatim: "Merged
https://github.com/danbri/factoidal-core/pull/185 - do it!", approving the
proposals of `docs/designissues/2026-10-28-dataflow-and-xproc.md`. Proposal 1:
a graph of stages with named ports in place of the list of
`Dataflow/Pipeline.lean`, as XProc 3.1 steps have named ports
(https://spec.xproc.org/3.1/xproc/).

## The model

* `PortSig W N`: a stage's name, its input ports (a name and a wire each, in
  order), its output wire, its contract name and its named assumptions.
* `PortComponent S A`: a signature, a run from the values of its input ports
  (`Vals S ws`, one value per wire of `ws`) to a value of its output wire, a
  contract, and `sound` under the stage's named assumptions, as `Component`
  of `Pipeline.lean`.
* `Src`: where a port's value comes from: graph input `k`, or the output of
  node `j`.
* `Graph S A`: a list of nodes, each a component and one `Src` per port. A
  node may read only graph inputs and the outputs of nodes BEFORE it; so the
  list order is a topological order and a graph has no cycle. A reference to
  the node itself or to a later node is the static error `forwardRef`, the
  counterpart of XProc's err:XS0001 (a loop in the connections).

`Graph.run inputs` runs the nodes in order and returns the value of every
node (`env`); the last value is the graph's output. A port's value reaches
its wire through `arrive` (`Pipeline.lean`): as it is, or by one of the
conversions of the wire system.

## The guarantee

`Graph.contract inputs env`: every node's contract holds on the values its
sources give it in `env` (and `inputs`), and its value is on its output wire.
It is the conjunction of the node contracts over the graph's edges; for a
graph that is a chain it is the composed contract of the list.

`Graph.guarantee_sound`: if every named assumption of every node holds, a
successful run satisfies `Graph.contract`. One theorem for every graph.

## The static check

`graphIssues conv inW sigs`: for a graph whose inputs are on the wires `inW`,
each issue of each node: `unknownInput` (no graph input `k`), `forwardRef`
(the node itself or a later node), `portCount` (sources and ports differ in
number), `wireMismatch` (the source's wire neither equals nor converts to the
port's wire). It reads signatures only, so the wasm op can call it on registry
entries.

`Graph.run_stage_error_only`: when `graphIssues` is empty and the inputs are
on the wires `inW`, a run that fails, fails in a stage's own run: never on a
source, a port count or a wire. Type errors are found before the run (XProc
3.1 raises them only when the step runs).

What the theorems do not say: a run that fails is not described further, and
a stage's termination is not in its contract.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Pipeline

set_option linter.unusedSectionVars false

namespace L4Factoidal.Dataflow

/-! ## Signatures, sources, issues -/

/-- A stage with named input ports. -/
structure PortSig (W N : Type) where
  name : String
  ins : List (String × W)
  outW : W
  contract : Option N
  assumptions : List N

/-- The wires of the input ports, in order. -/
def PortSig.inWires {W N : Type} (s : PortSig W N) : List W := s.ins.map (·.2)

/-- The signature of a one-port stage of `Pipeline.lean`, with port `in`. -/
def StageSig.toPortSig {W N : Type} (s : StageSig W N) : PortSig W N :=
  { name := s.name, ins := [("in", s.inW)], outW := s.outW, contract := s.contract,
    assumptions := s.assumptions }

/-- Where a port's value comes from. -/
inductive Src where
  | input (k : Nat)
  | node (j : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A problem found by the static check, with the node and port indices. -/
inductive GraphIssue (W : Type) where
  | unknownInput (node port k : Nat)
  | forwardRef (node port j : Nat)
  | portCount (node ports sources : Nat)
  | wireMismatch (node port : Nat) (source port_ : W)
  deriving DecidableEq, Repr

section Check

variable {W N : Type} [DecidableEq W]

/-- The wire of a source, for node `outs.length` (`outs`: the output wires of
the nodes before it); none for an unknown input or a forward reference. -/
def srcWire (inW outs : List W) : Src → Option W
  | .input k => inW[k]?
  | .node j => outs[j]?

/-- The issue of a source that has no wire. -/
def missingIssue (node port : Nat) : Src → GraphIssue W
  | .input k => .unknownInput node port k
  | .node j => .forwardRef node port j

/-- The issues of the sources of one node, port `p` onwards. -/
def srcIssues (conv : W → W → Bool) (inW outs : List W) (node : Nat) :
    Nat → List Src → List W → List (GraphIssue W)
  | _, [], [] => []
  | p, s :: ss, w :: ws =>
    (match srcWire inW outs s with
     | none => [missingIssue node p s]
     | some v => if Feeds conv v w then [] else [.wireMismatch node p v w]) ++
    srcIssues conv inW outs node (p + 1) ss ws
  | p, ss, ws => [.portCount node (p + ws.length) (p + ss.length)]

/-- The issues of the nodes from index `outs.length` on. -/
def graphIssuesAux (conv : W → W → Bool) (inW : List W) :
    List W → List (PortSig W N × List Src) → List (GraphIssue W)
  | _, [] => []
  | outs, (sig, srcs) :: rest =>
    srcIssues conv inW outs outs.length 0 srcs sig.inWires ++
    graphIssuesAux conv inW (outs ++ [sig.outW]) rest

/-- **The static check** of a graph whose inputs are on the wires `inW`. -/
def graphIssues (conv : W → W → Bool) (inW : List W) (g : List (PortSig W N × List Src)) :
    List (GraphIssue W) :=
  graphIssuesAux conv inW [] g

/-- The output wire of a graph: that of its last node. -/
def graphOutWire (g : List (PortSig W N × List Src)) : Option W :=
  g.getLast?.map (·.1.outW)

end Check

/-! ## Components and runs -/

section Run

variable {W N : Type} [DecidableEq W] [DecidableEq N]
variable (S : WireSystem W) (A : N → Prop)

/-- One value per wire of a list. -/
inductive Vals : List W → Type
  | nil : Vals []
  | cons {w : W} {ws : List W} : S.Carrier w → Vals ws → Vals (w :: ws)

/-- A stage with input ports: a signature, a run, a contract, and soundness
under the stage's named assumptions. -/
structure PortComponent where
  sig : PortSig W N
  run : Vals S sig.inWires → Except String (S.Carrier sig.outW)
  contract : Vals S sig.inWires → S.Carrier sig.outW → Prop
  sound : (∀ n ∈ sig.assumptions, A n) → ∀ a b, run a = .ok b → contract a b

/-- A node of a graph: a component and one source per port. -/
structure GNode where
  comp : PortComponent S A
  srcs : List Src

/-- A graph: nodes in a topological order (module comment). -/
structure Graph where
  nodes : List (GNode S A)

/-- Why a graph run stopped. -/
inductive GraphError where
  | source (stage : String)
  | wire (stage : String)
  | ports (stage : String)
  | stage (stage : String) (msg : String)
  deriving Repr, DecidableEq

variable {S A}

/-- The component of a one-port `Component` of `Pipeline.lean`. -/
def PortComponent.ofComponent (c : Component S A) : PortComponent S A where
  sig := c.sig.toPortSig
  run := fun | .cons a .nil => c.run a
  contract := fun | .cons a .nil => c.contract a
  sound h := fun | .cons a .nil, b, hr => c.sound h a b hr

/-- The value of a source. -/
def lookupSrc (inputs env : List (Packed S)) : Src → Option (Packed S)
  | .input k => inputs[k]?
  | .node j => env[j]?

/-- The values of a node's ports, at the ports' wires. -/
def gather (inputs env : List (Packed S)) (name : String) :
    List Src → (ws : List W) → Except GraphError (Vals S ws)
  | [], [] => .ok .nil
  | s :: ss, w :: ws =>
    match lookupSrc inputs env s with
    | none => .error (.source name)
    | some x =>
      match arrive S x w with
      | none => .error (.wire name)
      | some a =>
        match gather inputs env name ss ws with
        | .ok r => .ok (.cons a r)
        | .error e => .error e
  | _, _ => .error (.ports name)

/-- Run one node on the graph inputs and the values of the nodes before it. -/
def GNode.step (n : GNode S A) (inputs env : List (Packed S)) : Except GraphError (Packed S) :=
  match gather inputs env n.comp.sig.name n.srcs n.comp.sig.inWires with
  | .error e => .error e
  | .ok a =>
    match n.comp.run a with
    | .ok b => .ok ⟨n.comp.sig.outW, b⟩
    | .error e => .error (.stage n.comp.sig.name e)

/-- The contract of one node: its sources gather to `a`, its value is `b` on
its output wire, and its contract holds of `a` and `b`. -/
def GNode.holds (n : GNode S A) (inputs env : List (Packed S)) (y : Packed S) : Prop :=
  ∃ a b, gather inputs env n.comp.sig.name n.srcs n.comp.sig.inWires = .ok a ∧
    y = ⟨n.comp.sig.outW, b⟩ ∧ n.comp.contract a b

def runAux (inputs : List (Packed S)) :
    List (GNode S A) → List (Packed S) → Except GraphError (List (Packed S))
  | [], env => .ok env
  | n :: ns, env =>
    match n.step inputs env with
    | .ok y => runAux inputs ns (env ++ [y])
    | .error e => .error e

def holdsAux (inputs : List (Packed S)) :
    List (GNode S A) → List (Packed S) → List (Packed S) → Prop
  | [], env, out => out = env
  | n :: ns, env, out => ∃ y, n.holds inputs env y ∧ holdsAux inputs ns (env ++ [y]) out

namespace Graph

/-- The signatures and sources, for the static check. -/
def sigs (g : Graph S A) : List (PortSig W N × List Src) :=
  g.nodes.map fun n => (n.comp.sig, n.srcs)

/-- Run the nodes in order; the value of every node, or the first error. -/
def run (g : Graph S A) (inputs : List (Packed S)) : Except GraphError (List (Packed S)) :=
  runAux inputs g.nodes []

/-- The graph's contract: every node's contract holds on its sources. -/
def contract (g : Graph S A) (inputs env : List (Packed S)) : Prop :=
  holdsAux inputs g.nodes [] env

/-- The union of the nodes' named assumptions (first-seen order). -/
def assumptions (g : Graph S A) : List N :=
  (g.nodes.flatMap (·.comp.sig.assumptions)).eraseDups

end Graph

/-! ## Soundness -/

theorem GNode.step_ok {n : GNode S A} {inputs env : List (Packed S)} {y : Packed S}
    (h : n.step inputs env = .ok y) (hA : ∀ m ∈ n.comp.sig.assumptions, A m) :
    n.holds inputs env y := by
  unfold GNode.step at h
  split at h
  · cases h
  · rename_i a ha
    split at h
    · rename_i b hb
      cases h
      exact ⟨a, b, ha, rfl, n.comp.sound hA a b hb⟩
    · cases h

theorem runAux_sound (inputs : List (Packed S)) :
    ∀ (ns : List (GNode S A)) (env out : List (Packed S)),
      (∀ n ∈ ns, ∀ m ∈ n.comp.sig.assumptions, A m) →
      runAux inputs ns env = .ok out → holdsAux inputs ns env out
  | [], env, out, _, h => by
    simp only [runAux, Except.ok.injEq] at h
    exact h.symm
  | n :: ns, env, out, hA, h => by
    simp only [runAux] at h
    split at h
    · rename_i y hy
      exact ⟨y, GNode.step_ok hy (hA n List.mem_cons_self),
        runAux_sound inputs ns (env ++ [y]) out
          (fun m hm => hA m (List.mem_cons_of_mem n hm)) h⟩
    · cases h

theorem Graph.mem_assumptions {g : Graph S A} {m : N} :
    m ∈ g.assumptions ↔ ∃ n ∈ g.nodes, m ∈ n.comp.sig.assumptions := by
  unfold Graph.assumptions
  rw [List.mem_eraseDups, List.mem_flatMap]

/-- **The guarantee of any graph.** If every named assumption of the graph
holds, a successful run satisfies the graph's contract: every node's contract
holds on the values of its sources. -/
theorem Graph.guarantee_sound (g : Graph S A) (hA : ∀ m ∈ g.assumptions, A m)
    (inputs env : List (Packed S)) (h : g.run inputs = .ok env) : g.contract inputs env :=
  runAux_sound inputs g.nodes [] env
    (fun n hn m hm => hA m (Graph.mem_assumptions.mpr ⟨n, hn, hm⟩)) h

/-! ## The static check rules out every error but a stage's own -/

theorem lookupSrc_wire {inputs env : List (Packed S)} {inW outs : List W}
    (hi : inputs.map (·.1) = inW) (he : env.map (·.1) = outs) {s : Src} {v : W}
    (h : srcWire inW outs s = some v) : ∃ x, lookupSrc inputs env s = some x ∧ x.1 = v := by
  cases s with
  | input k =>
    simp only [srcWire, ← hi, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨x, hx, rfl⟩
  | node j =>
    simp only [srcWire, ← he, List.getElem?_map, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    exact ⟨x, hx, rfl⟩

theorem gather_ok_of_noIssues {inputs env : List (Packed S)}
    {inW outs : List W} (hi : inputs.map (·.1) = inW) (he : env.map (·.1) = outs)
    (name : String) (node : Nat) :
    ∀ (p : Nat) (ss : List Src) (ws : List W),
      srcIssues S.conv inW outs node p ss ws = [] →
      ∃ a, gather inputs env name ss ws = .ok a
  | _, [], [], _ => ⟨.nil, rfl⟩
  | p, s :: ss, w :: ws, h => by
    simp only [srcIssues, List.append_eq_nil_iff] at h
    obtain ⟨h1, h2⟩ := h
    cases hv : srcWire inW outs s with
    | none => rw [hv] at h1; cases h1
    | some v =>
      rw [hv] at h1
      have hf : Feeds S.conv v w = true := by
        by_cases hf : Feeds S.conv v w = true
        · exact hf
        · simp [hf] at h1
      obtain ⟨x, hx, hxv⟩ := lookupSrc_wire hi he hv
      have hsome := arrive_isSome S (x := x) (i := w) (by rw [hxv]; exact hf)
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨r, hr⟩ := gather_ok_of_noIssues hi he name node (p + 1) ss ws h2
      exact ⟨.cons a r, by simp [gather, hx, ha, hr]⟩
  | _, [], _ :: _, h => by simp [srcIssues] at h
  | _, _ :: _, [], h => by simp [srcIssues] at h

theorem runAux_stage_error_only {inputs : List (Packed S)} {inW : List W}
    (hi : inputs.map (·.1) = inW) :
    ∀ (ns : List (GNode S A)) (env : List (Packed S)),
      graphIssuesAux S.conv inW (env.map (·.1)) (ns.map fun n => (n.comp.sig, n.srcs)) = [] →
      ∀ e, runAux inputs ns env = .error e → ∃ name msg, e = .stage name msg
  | [], _, _, e, h => by simp [runAux] at h
  | n :: ns, env, hI, e, h => by
    simp only [List.map_cons, graphIssuesAux, List.append_eq_nil_iff, List.length_map] at hI
    obtain ⟨h1, h2⟩ := hI
    obtain ⟨a, ha⟩ := gather_ok_of_noIssues hi rfl n.comp.sig.name env.length 0 n.srcs
      n.comp.sig.inWires h1
    simp only [runAux, GNode.step, ha] at h
    split at h
    · rename_i y hy
      split at hy
      · rename_i b hb
        cases hy
        refine runAux_stage_error_only hi ns (env ++ [⟨n.comp.sig.outW, b⟩]) ?_ e h
        simpa using h2
      · cases hy
    · rename_i e' he'
      split at he'
      · cases he'
      · rename_i msg _
        cases he'
        cases h
        exact ⟨_, _, rfl⟩

/-- **A checked graph fails only in a stage.** When the static check finds no
issue and the inputs are on the wires `inW`, a run that fails, fails in a
stage's own run: never on a source, a port count or a wire. -/
theorem Graph.run_stage_error_only (g : Graph S A) {inputs : List (Packed S)} {inW : List W}
    (hc : graphIssues S.conv inW g.sigs = []) (hi : inputs.map (·.1) = inW)
    (e : GraphError) (h : g.run inputs = .error e) : ∃ name msg, e = .stage name msg :=
  runAux_stage_error_only hi g.nodes [] (by simpa [graphIssues, Graph.sigs] using hc) e h

end Run

#print axioms Graph.guarantee_sound
#print axioms Graph.run_stage_error_only

end L4Factoidal.Dataflow
