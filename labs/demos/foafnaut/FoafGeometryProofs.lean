import FoafNaut

/- Runtime connections for the shared drawing records. These statements concern
integer geometry and the layout checker, not GPU execution, raster rounding,
pixel visibility, or enforcement of the overlap budget by layout transitions. -/
namespace NativeFoafNaut

private theorem pick_find (m : Model) (x y : Int) (part : PaintedPart)
    (picked : m.pick x y = some part) :
    m.parts.reverse.find? (fun p => p.visible && NativeGeometry.hit p.shape x y == some true) = some part := by
  unfold Model.pick at picked
  split at picked
  · contradiction
  · exact picked

theorem Model.pick_mem_parts (m : Model) (x y : Int) (part : PaintedPart)
    (picked : m.pick x y = some part) : part ∈ m.parts := by
  have member := List.mem_of_find?_eq_some (pick_find m x y part picked)
  simpa using member

theorem Model.pick_visible (m : Model) (x y : Int) (part : PaintedPart)
    (picked : m.pick x y = some part) : part.visible = true := by
  have matched := List.find?_some (pick_find m x y part picked)
  simp only [Bool.and_eq_true] at matched
  exact matched.1

theorem Model.pick_hit (m : Model) (x y : Int) (part : PaintedPart)
    (picked : m.pick x y = some part) : NativeGeometry.hit part.shape x y = some true := by
  have matched := List.find?_some (pick_find m x y part picked)
  simp only [Bool.and_eq_true] at matched
  simpa using matched.2

theorem Model.pick_shape_mem_scene (m : Model) (x y : Int) (part : PaintedPart)
    (picked : m.pick x y = some part) : part.shape ∈ m.scene.shapes := by
  change part.shape ∈ m.parts.map (·.shape)
  exact List.mem_map.mpr ⟨part, m.pick_mem_parts x y part picked, rfl⟩

-- The identifier attached by the runtime does not change checker semantics.
theorem Model.layoutChecks_accepted_iff (m : Model) (id : Nat) (report : NativeGeometry.NodeCheck)
    (member : (id,report) ∈ m.layoutChecks) :
    report.accepted = true ↔ 0 < report.area ∧ 10000*report.overlapSum ≤ m.policy.overlapBps*report.area := by
  unfold Model.layoutChecks at member
  have checkMember := (List.of_mem_zip member).2
  exact L4Factoidal.UI.LayoutPolicy.checkFootprints_accepted_iff _ _ _ checkMember

end NativeFoafNaut
