import L4Factoidal.Dataflow.Stage
import L4Factoidal.Paralliverse.ProgramCPU

/-!
An optional adapter into the existing Dataflow contracts. Applications can use
`Dataflow.Component.ofStage` and `Dataflow.PortComponent.ofComponent` for their
own wire systems. The generic program syntax and interpreters do not import Dataflow.
-/

namespace L4Factoidal.Paralliverse.Program

variable {Atom : Type} {sig : Signature Atom} {a b : Shape Atom}

/-- A total Dataflow stage whose executable path uses the fused CPU program and
whose contract names the source's sequential result. -/
def asStage (ε : Type) (base : Atom → Type) (reference implementation : PrimitiveEval base sig)
    (agree : ∀ {i o} (op : sig i o) (x : Shape.Value base i),
      implementation op x = reference op x)
    (workers : Nat) (p : Program sig a b) :
    Dataflow.Stage ε (Shape.Value base a) (Shape.Value base b) :=
  Dataflow.Stage.ofFun (runCPU base implementation workers (fuseMaps p))
    (fun x y => y = eval base reference p x)
    (congrFun (runCPU_fuseMaps_eq_eval base reference implementation agree workers p))

/-- Kind: existing stage interface refinement.
Says: a successful result of the fused CPU Dataflow stage is exactly the source
denotation, and that result is always available in the pure stage model.
Does not say: that other graph ports, host operations or IO stages satisfy their own
contracts or make progress. -/
theorem asStage_run_iff (ε : Type) (base : Atom → Type) (reference implementation : PrimitiveEval base sig)
    (agree : ∀ {i o} (op : sig i o) (x : Shape.Value base i),
      implementation op x = reference op x)
    (workers : Nat) (p : Program sig a b) (x : Shape.Value base a) (y : Shape.Value base b) :
    (asStage ε base reference implementation agree workers p).run x = .ok y ↔
      y = eval base reference p x := by
  change (Except.ok (runCPU base implementation workers (fuseMaps p) x) : Except ε _) = .ok y ↔ _
  rw [runCPU_fuseMaps_eq_eval base reference implementation agree workers]
  exact ⟨fun h => (Except.ok.inj h).symm, fun h => congrArg Except.ok h.symm⟩

#print axioms asStage_run_iff

end L4Factoidal.Paralliverse.Program
