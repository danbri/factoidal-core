import L4Factoidal.GpuDomainSpecificLanguage.GpuPlan
import L4Factoidal.GpuDomainSpecificLanguage.MapZipGrid

/-!
# From successful serialised graph compilation to actual shader execution

This is the per-step boundary in issue
https://github.com/danbri/factoidal-core/issues/802. `runJsonGrid?` reads the
original emitted JSON, resolves its actual selected shader and source buffer
names, constructs its actual u32 config packet, parses the selected WGSL bytes,
and executes those parsed stores. It never delegates execution to GraphWords.

The theorem assumes the host bound immutable arrays corresponding to the named
inputs, a distinct destination with sufficient physical space, and a permutation
of the declared dispatch. It proves the logical output prefix agrees with the
existing GraphWords primitive. Driver execution, input snapshots across awaits,
whole-graph scheduling and readback transport remain outside this theorem.
-/

namespace L4Factoidal.GpuDomainSpecificLanguage.MapZipCompileRefinement

open Lean Graph GraphJson MapZipKind MapZipPlan
open L4Factoidal.Paralliverse.WGSL

/-- Host-side buffer-name correspondence. The captured arrays are immutable;
    the separate destination argument represents a fresh physical allocation. -/
abbrev Buffers := String → Option (Array UInt32)

def selectedShader? (plan : Json) (step : Step) : Except String String := do
  string? (← plan.getObjVal? "shaders") step.shader

/-- Execute the actual JSON-selected shader and bindings. Physical invocation
    order is supplied separately and constrained by `StepRefines` below. -/
def runJsonGrid? (plan candidate : Json) (buffers : Buffers)
    (prior : Array UInt32) (lanes : List UInt32) : Option (Array UInt32) := do
  let step ← (readStep? candidate).toOption
  let source ← (selectedShader? plan step).toOption
  let xs ← buffers step.a
  let ys ← buffers step.b
  MapZipGrid.runText source ⟨xs,ys,(step.config.map UInt32.ofNat).toArray⟩ prior lanes

/-- Explicit physical-buffer and dispatch correspondence, followed by a semantic
    conclusion. No equality to a reference answer appears among the premises. -/
def StepRefines (plan candidate : Json) (kind : Kind) (step : Step) : Prop :=
  ∀ (buffers : Buffers) (xs ys prior : Array UInt32) (lanes : List UInt32),
    buffers step.a = some xs → buffers step.b = some ys →
    xs.size = step.words → ys.size = step.words → step.words ≤ prior.size →
    (lanes.map UInt32.toNat).Perm (List.range (step.workgroups * 64)) →
    ∃ out, runJsonGrid? plan candidate buffers prior lanes = some out ∧
      out.toList = kind.result xs.toList ys.toList (UInt32.ofNat step.constant) ++
        prior.toList.drop step.words ∧
      GraphWords.execute kind.operator (kind.inputs xs.toList ys.toList)
        (kind.parameter (UInt32.ofNat step.constant)) =
          .ok (.buffer (out.toList.take step.words))

/-- Kind: actual emitted-step refinement.
Says: a structurally matched real JSON step executes its actual selected shader,
config and bindings to the existing GraphWords result, for every valid rounded
dispatch order and every corresponding finite input/destination allocation.
Does not say: these immutable arrays describe a particular device, that inputs
were snapshotted at API entry, or that the host has completed the graph. -/
theorem step_refines {doc : Document} {node : Node} {raw plan candidate : Json}
    {kind : Kind} {preceding : List Json} {step : Step}
    (read : readStep? candidate = .ok step)
    (source : shader? plan = .ok MapZipShader.source)
    (matching : StepMatches doc node raw kind preceding step) :
    StepRefines plan candidate kind step := by
  rcases matching with ⟨_,_,_,_,shader,_,_,_,_,_,_,_,small,_,_,_,config,groups,_⟩
  have selected : selectedShader? plan step = .ok MapZipShader.source := by
    unfold selectedShader?
    rw [shader]
    exact source
  intro buffers xs ys prior lanes aBound bBound aSize bSize room order
  have small' : xs.size ≤ 4194240 := by omega
  have lengths : xs.size = ys.size := by omega
  have room' : xs.size ≤ prior.size := by omega
  have order' : (lanes.map UInt32.toNat).Perm (List.range (MapZipGrid.grid xs.size)) := by
    simpa [MapZipGrid.grid,groups,aSize] using order
  have packet :
      (⟨xs,ys,(step.config.map UInt32.ofNat).toArray⟩ : MapZipSurface.Inputs) =
      MapZipRefinement.inputs kind xs ys (UInt32.ofNat xs.size)
        (UInt32.ofNat step.constant) := by
    rw [config,aSize]
    rfl
  obtain ⟨out,executed,result⟩ := MapZipGrid.run_source_grid kind xs ys
    (UInt32.ofNat step.constant) small' lengths prior room' lanes order'
  have resultLength :
      (kind.result xs.toList ys.toList (UInt32.ofNat step.constant)).length = step.words := by
    simpa [aSize] using result_length kind xs.toList ys.toList
      (UInt32.ofNat step.constant) (by simpa using lengths)
  refine ⟨out,?_,?_,?_⟩
  · unfold runJsonGrid?
    rw [read]
    dsimp only [Except.toOption,Bind.bind,Option.bind]
    rw [selected]
    dsimp only [Except.toOption,Bind.bind,Option.bind]
    rw [aBound,bBound]
    dsimp only [Bind.bind,Option.bind]
    rw [packet]
    exact executed
  · simpa [aSize] using result
  · have logical : out.toList.take step.words =
        kind.result xs.toList ys.toList (UInt32.ofNat step.constant) := by
      rw [result,← resultLength]
      exact List.take_left
    rw [logical]
    exact reference kind xs.toList ys.toList (UInt32.ofNat step.constant)
      (by simpa using lengths)

/-- Kind: serialised source-to-emitted-shader refinement.
Says: successful shipping `compile?`, tied to the actual certified graph decode,
provides an actual indexed JSON step for every covered source node. That step
preserves raw operator/parameter, source ports, buffer names and lengths,
destination, config, shader bytes and workgroups; executing those actual fields
has the existing wrapping-u32 GraphWords result under `StepRefines`'s explicit
host/device correspondence assumptions.
Does not say: the other GPU operators, whole-graph execution, driver, device or
readback implementation are formally verified. -/
theorem compiled_mapzip {rawGraph inputSizes plan : Json} {graph : AdmittedGraph}
    {rawNodes : Array Json} {node : Node} {raw : Json} {kind : Kind}
    (compiled : GpuPlan.compile? rawGraph inputSizes = .ok plan)
    (decoded : GraphJson.decodeCertified? rawGraph = .ok graph)
    (nodesRead : array? rawGraph "nodes" = .ok rawNodes)
    (member : (node,raw) ∈ graph.graph.nodes.zip rawNodes.toList)
    (selected : MapZipKind.ofName? node.op = some kind) :
    ∃ (steps : Array Json) (index : Nat) (candidate : Json) (step : Step),
      array? plan "steps" = .ok steps ∧
      steps.toList[index]? = some candidate ∧ readStep? candidate = .ok step ∧
      StepMatches graph.graph node raw kind (steps.toList.take index) step ∧
      GraphWords.Operator.fromName? node.op = some kind.operator ∧
      StepRefines plan candidate kind step := by
  obtain ⟨checked⟩ := GpuPlan.compile_checked compiled
  have sameGraph : checked.graph = graph := by
    have := checked.decoded.symm.trans decoded
    exact Except.ok.inj this
  have sameNodes : checked.rawNodes = rawNodes := by
    have := checked.nodesRead.symm.trans nodesRead
    exact Except.ok.inj this
  have member' : (node,raw) ∈ checked.graph.graph.nodes.zip checked.rawNodes.toList := by
    simpa [sameGraph,sameNodes] using member
  obtain ⟨index,candidate,step,indexed,read,matching⟩ := checked.node_step node raw kind member' selected
  refine ⟨checked.steps,index,candidate,step,checked.stepsRead,indexed,read,?_,
    selected_operator selected,?_⟩
  · simpa [sameGraph] using matching
  · exact step_refines read checked.sourceRead matching

#print axioms step_refines
#print axioms compiled_mapzip

end L4Factoidal.GpuDomainSpecificLanguage.MapZipCompileRefinement
