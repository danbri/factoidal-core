import L4Factoidal.Paralliverse.WordMapGPUGrid

/-! Sequencing proved word shaders by reusing the complete returned intermediate. -/

namespace L4Factoidal.Paralliverse.WordMapGPU

open WGSL

/-- The second dispatch binds the entire destination returned by the first. -/
def runTwo (first second : Pass) (n : Nat) (src intermediate prior : Array UInt32)
    (firstOrder secondOrder : List UInt32) : Option (TextPipeline.GridState × TextPipeline.GridState) := do
  let mid ← runGrid first n src intermediate firstOrder
  let out ← runGrid second n mid.dst prior secondOrder
  return (mid, out)

/-- Kind: compositional shader refinement.
Says: two selected passes run in independently ordered grids. The first returned
array, including its original header and spare tail, is the second pass's actual
source. Both logged traces and the complete final frame agree with the typed source.
Does not say: device bindings are disjoint or that a host made the first pass visible. -/
theorem selected_two_grid {p : Program WordProgram.Op WordProgram.words WordProgram.words} {first second : Pass}
    (selected : select? p = some (.two first second)) (xs tail : List UInt32)
    (src intermediate prior : Array UInt32) (firstOrder secondOrder : List UInt32)
    (small : xs.length ≤ maxWords)
    (layout : src.toList = UInt32.ofNat xs.length :: first.coefficient :: (xs ++ tail))
    (seed : intermediate.toList.take 2 = [UInt32.ofNat xs.length, second.coefficient])
    (middleRoom : 2 + xs.length ≤ intermediate.size) (room : 2 + xs.length ≤ prior.size)
    (order₁ : CountTarget.ValidGrid xs.length firstOrder) (order₂ : CountTarget.ValidGrid xs.length secondOrder) :
    ∃ mid out,
      runTwo first second xs.length src intermediate prior firstOrder secondOrder = some (mid, out) ∧
      runGrid first xs.length src intermediate firstOrder = some mid ∧
      runGrid second xs.length mid.dst prior secondOrder = some out ∧
      mid.dst.toList = intermediate.toList.take 2 ++ xs.map first.apply ++
        intermediate.toList.drop (2 + xs.length) ∧
      out.dst.toList = (prior.toList.take 2).append (Program.eval WordProgram.base (@WordProgram.reference) p xs) ++
        prior.toList.drop (2 + xs.length) ∧
      mid.trace = firstOrder.map (footprint first xs) ∧
      out.trace = secondOrder.map (footprint second (xs.map first.apply)) := by
  have chosen₁ : select? first.program = some (.unary first) := (select?_eq_some_iff _ _).mpr rfl
  have chosen₂ : select? second.program = some (.unary second) := (select?_eq_some_iff _ _).mpr rfl
  obtain ⟨mid, ran₁, midFrame, trace₁⟩ :=
    selected_grid chosen₁ xs tail src intermediate firstOrder small layout middleRoom order₁
  rw [eval_pass] at midFrame
  let ys := xs.map first.apply
  have length : ys.length = xs.length := List.length_map _
  have intoSecond : mid.dst.toList =
      UInt32.ofNat ys.length :: second.coefficient :: (ys ++ intermediate.toList.drop (2 + xs.length)) := by
    rw [midFrame, seed, length]
    rfl
  obtain ⟨out, ran₂, finalFrame, trace₂⟩ :=
    selected_grid chosen₂ ys (intermediate.toList.drop (2 + xs.length)) mid.dst prior secondOrder
      (by rw [length]; exact small) intoSecond (by rw [length]; exact room)
      (by rw [length]; exact order₂)
  rw [length] at ran₂ finalFrame
  have meaning : Program.eval WordProgram.base (@WordProgram.reference) p xs =
      Program.eval WordProgram.base (@WordProgram.reference) second.program ys := by
    rw [(select?_eq_some_iff p _).mp selected]
    change Program.eval WordProgram.base (@WordProgram.reference) second.program
      (Program.eval WordProgram.base (@WordProgram.reference) first.program xs) = _
    rw [eval_pass first xs]
  refine ⟨mid, out, ?_, ran₁, ran₂, midFrame, ?_, trace₁, trace₂⟩
  · unfold runTwo
    rw [ran₁]
    change (runGrid second xs.length mid.dst prior secondOrder).bind (fun result => some (mid, result)) = _
    rw [ran₂] <;> rfl
  · rw [meaning]
    exact finalFrame

/-- Kind: CPU and shader correspondence.
Says: the two parsed affine shaders produce exactly the payload of the actual
fused CPU task interpreter, with modular arithmetic, for every worker count and
coefficient, while preserving every word of the destination outside the payload.
Does not say: the CPU task scheduler and device driver make the same progress. -/
theorem affine_grid_eq_cpu (factor offset : UInt32) (initial : DSL.Initial) (workers : Nat)
    (xs tail : List UInt32) (src intermediate prior : Array UInt32) (firstOrder secondOrder : List UInt32)
    (small : xs.length ≤ maxWords)
    (layout : src.toList = UInt32.ofNat xs.length :: factor :: (xs ++ tail))
    (seed : intermediate.toList.take 2 = [UInt32.ofNat xs.length, offset])
    (middleRoom : 2 + xs.length ≤ intermediate.size) (room : 2 + xs.length ≤ prior.size)
    (order₁ : CountTarget.ValidGrid xs.length firstOrder) (order₂ : CountTarget.ValidGrid xs.length secondOrder) :
    ∃ mid out,
      runTwo ⟨.multiply, factor⟩ ⟨.add, offset⟩ xs.length src intermediate prior firstOrder secondOrder =
        some (mid, out) ∧
      out.dst.toList = (prior.toList.take 2).append
        (Program.runCPU WordProgram.base (WordProgram.implementation initial) workers
          (Program.fuseMaps (WordProgram.affine factor offset)) xs) ++ prior.toList.drop (2 + xs.length) := by
  obtain ⟨mid, out, ran, _, _, _, finalFrame, _, _⟩ :=
    selected_two_grid (select_affine factor offset) xs tail src intermediate prior firstOrder secondOrder
      small layout seed middleRoom room order₁ order₂
  refine ⟨mid, out, ran, ?_⟩
  have arithmetic : Program.eval WordProgram.base (@WordProgram.reference) (WordProgram.affine factor offset) xs =
      xs.map (fun x => x * factor + offset) := by
    simp only [WordProgram.affine, Program.eval]
    change (xs.map (fun x : UInt32 => x * factor)).map (fun x : UInt32 => x + offset) = _
    exact List.map_map (f := fun x : UInt32 => x * factor) (g := fun x : UInt32 => x + offset) (l := xs)
  rw [arithmetic] at finalFrame
  rw [WordProgram.runCPU_affine]
  exact finalFrame

#print axioms selected_two_grid
#print axioms affine_grid_eq_cpu

end L4Factoidal.Paralliverse.WordMapGPU

