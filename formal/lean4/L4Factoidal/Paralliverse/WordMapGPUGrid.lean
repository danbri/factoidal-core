import L4Factoidal.Paralliverse.WordMapGPUFrame
import L4Factoidal.Paralliverse.CountTarget
import L4Factoidal.Paralliverse.WGSL.Dispatch

/-! End-to-end finite dispatch of typed word maps, from the actual exported
shader bytes to every output word and every chronological lane record. -/

namespace L4Factoidal.Paralliverse.WordMapGPU

open WGSL

/-- Kind: launch geometry.
Says: the rounded 64-wide launch covers an admitted scalar payload with at most
1,024 lanes, and the runtime workgroup count gives that physical grid exactly.
Does not say: the host used that geometry. -/
theorem word_grid_bounds (n : Nat) (small : n ≤ maxWords) :
    n ≤ CountTarget.grid n ∧ CountTarget.grid n ≤ 1024 ∧ workgroups n * 64 = CountTarget.grid n := by
  change n ≤ 1024 at small
  unfold CountTarget.grid workgroups
  omega

/-- Kind: schedule existence.
Says: each admitted word count has a valid canonical lane schedule, including zero.
Does not say: a device must use that particular order. -/
theorem word_canonical_valid (n : Nat) (small : n ≤ maxWords) :
    CountTarget.ValidGrid n (CountTarget.canonicalLanes n) := by
  apply List.Perm.of_eq
  apply List.ext_getElem
  · simp [CountTarget.canonicalLanes]
  · intro i _ hi
    have good : i < CountTarget.grid n := by simpa using hi
    have bound := (word_grid_bounds n small).2.1
    simp only [CountTarget.canonicalLanes, List.getElem_map, List.getElem_range]
    apply UInt32.toNat_ofNat_of_lt'
    change i < 4294967296
    omega

private def asOutcome (r : Surface.Outcome) : ScanSurface.Outcome := ⟨r.dst, r.writes, false⟩

private def parsedStep (m : Surface.Module) (src prior : Array UInt32) (gid : UInt32) :
    Option ScanSurface.Outcome :=
  (Surface.run m src prior gid).map asOutcome

/-- Parse the exported module once, then run each physical ID on the current
finite destination. The fuel is the actual rounded launch size. -/
def runGrid (pass : Pass) (n : Nat) (src prior : Array UInt32) (lanes : List UInt32) :
    Option TextPipeline.GridState := do
  let m ← Surface.parseShader pass.tag.shader.toUTF8
  TextPipeline.dispatch (parsedStep m src) lanes (CountTarget.grid n) ⟨prior, []⟩

/-- The only permitted store for this lane names its physical binding, word
address and the transformed source word. The if-body has no early-return statement. -/
def footprint (pass : Pass) (xs : List UInt32) (gid : UInt32) : TextPipeline.LaneTrace :=
  ⟨gid, false, if h : gid.toNat < xs.length then
    [((0, 2), ((2 + gid : UInt32).toNat, pass.apply xs[gid.toNat]))] else []⟩

private theorem observed_effect (pass : Pass) (xs : List UInt32) (prior : Array UInt32) (gid : UInt32) :
    TextPipeline.observed gid (asOutcome (laneEffect pass xs prior gid)) = footprint pass xs gid := by
  by_cases active : gid.toNat < xs.length
  · simp only [laneEffect, dif_pos active, footprint, TextPipeline.observed, asOutcome,
      List.map_cons, List.map_nil, scatterEvent]
  · simp only [laneEffect, dif_neg active, footprint, TextPipeline.observed, asOutcome, List.map_nil]

private theorem simulate (pass : Pass) (xs tail : List UInt32) (src : Array UInt32)
    (small : xs.length ≤ maxWords)
    (layout : src.toList = UInt32.ofNat xs.length :: pass.coefficient :: (xs ++ tail))
    (lanes : List UInt32) (fuel : Nat) (s : TextPipeline.GridState)
    (bounded : lanes.length ≤ fuel) (room : 2 + xs.length ≤ s.dst.size) :
    ∃ out, TextPipeline.dispatch (parsedStep (shaderModule pass.tag) src) lanes fuel s = some out ∧
      out.dst = foldLanes pass xs s.dst lanes ∧ out.trace = s.trace ++ lanes.map (footprint pass xs) := by
  induction lanes generalizing fuel s with
  | nil => exact ⟨s, rfl, rfl, by simp⟩
  | cons gid rest ih =>
    cases fuel with
    | zero => simp at bounded
    | succ k =>
      let r := asOutcome (laneEffect pass xs s.dst gid)
      have ran : parsedStep (shaderModule pass.tag) src s.dst gid = some r := by
        unfold parsedStep
        rw [run_module_lane pass xs tail src s.dst small layout room gid]
        rfl
      have nextRoom : 2 + xs.length ≤ (s.record gid r).dst.size := by
        change 2 + xs.length ≤ (laneEffect pass xs s.dst gid).dst.size
        rw [lane_size]
        exact room
      have nextTrace : (s.record gid r).trace = s.trace ++ [footprint pass xs gid] := by
        change (TextPipeline.observed gid r :: s.reversed).reverse = s.reversed.reverse ++ _
        rw [List.reverse_cons, observed_effect]
      obtain ⟨out, tailRun, dst, trace⟩ :=
        ih k (s.record gid r) (by simpa using bounded) nextRoom
      refine ⟨out, ?_, dst, ?_⟩
      · change (parsedStep (shaderModule pass.tag) src s.dst gid).bind
          (fun r => TextPipeline.dispatch (parsedStep (shaderModule pass.tag) src) rest k
            (s.record gid r)) = _
        rw [ran]
        exact tailRun
      · rw [trace, nextTrace]
        simp [List.append_assoc]

private theorem grid_pass (pass : Pass) (xs tail : List UInt32) (src prior : Array UInt32)
    (lanes : List UInt32) (small : xs.length ≤ maxWords)
    (layout : src.toList = UInt32.ofNat xs.length :: pass.coefficient :: (xs ++ tail))
    (room : 2 + xs.length ≤ prior.size) (order : CountTarget.ValidGrid xs.length lanes) :
    ∃ out, runGrid pass xs.length src prior lanes = some out ∧
      out.dst.toList = prior.toList.take 2 ++ xs.map pass.apply ++ prior.toList.drop (2 + xs.length) ∧
      out.trace = lanes.map (footprint pass xs) := by
  have perm : (lanes.map UInt32.toNat).Perm (List.range (CountTarget.grid xs.length)) := order
  have length : lanes.length = CountTarget.grid xs.length := by
    simpa only [List.length_map, List.length_range] using perm.length_eq
  have cover : ∀ i : Nat, i < xs.length → i ∈ lanes.map UInt32.toNat := by
    intro i active
    exact perm.mem_iff.mpr (List.mem_range.mpr (Nat.lt_of_lt_of_le active (word_grid_bounds _ small).1))
  obtain ⟨out, actual, dst, trace⟩ :=
    simulate pass xs tail src small layout lanes (CountTarget.grid xs.length) ⟨prior, []⟩ (by omega) room
  refine ⟨out, ?_, ?_, trace⟩
  · unfold runGrid
    rw [parse_shader]
    exact actual
  · rw [dst]
    exact foldLanes_frame pass xs prior lanes room cover

/-- Kind: selected byte-to-grid refinement.
Says: every selected unary word program runs successfully in the parsed shader
model for every admitted input and valid lane order. Its whole finite output is
the source result between the untouched header and spare tail. Its chronological
trace records exactly the active stores and all padded invocations.
Does not say: that a WebGPU driver compiled, scheduled or completed the submission. -/
theorem selected_grid {p : Program WordProgram.Op WordProgram.words WordProgram.words} {pass : Pass}
    (selected : select? p = some (.unary pass)) (xs tail : List UInt32) (src prior : Array UInt32)
    (lanes : List UInt32) (small : xs.length ≤ maxWords)
    (layout : src.toList = UInt32.ofNat xs.length :: pass.coefficient :: (xs ++ tail))
    (room : 2 + xs.length ≤ prior.size) (order : CountTarget.ValidGrid xs.length lanes) :
    ∃ out, runGrid pass xs.length src prior lanes = some out ∧
      out.dst.toList = (prior.toList.take 2).append (Program.eval WordProgram.base (@WordProgram.reference) p xs) ++
        prior.toList.drop (2 + xs.length) ∧ out.trace = lanes.map (footprint pass xs) := by
  have source := (select?_eq_some_iff p _).mp selected
  rw [source]
  change ∃ out, runGrid pass xs.length src prior lanes = some out ∧
    out.dst.toList = (prior.toList.take 2).append
      (Program.eval WordProgram.base (@WordProgram.reference) pass.program xs) ++
      prior.toList.drop (2 + xs.length) ∧ out.trace = lanes.map (footprint pass xs)
  rw [eval_pass]
  exact grid_pass pass xs tail src prior lanes small layout room order

#print axioms word_grid_bounds
#print axioms word_canonical_valid
#print axioms selected_grid

end L4Factoidal.Paralliverse.WordMapGPU

