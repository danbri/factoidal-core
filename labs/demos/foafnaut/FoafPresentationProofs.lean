import FoafPresentation
import FoafGeometryProofs

/- Connections to the actual displayed model. These concern integer geometry
and the shared box policy, not pixels, WGSL execution or callback liveness. -/
namespace NativeFoafPresentation
open NativeFoafNaut L4Factoidal.UI.LayoutPolicy L4Factoidal.UI.Presentation

theorem shown_certified (s : Session) (m : Model) (h : shown s = some m) :
    LayoutAccepted s.cfg m.footprints := by
  unfold shown at h
  cases hp : s.presentation.shown with
  | none => simp [hp] at h
  | some approved =>
    simp only [hp,Option.map_some,Option.some.injEq] at h
    subst m
    exact approved.valid

theorem displayed_certified (s : Session) (m : Model) (h : displayed s = some m) :
    LayoutAccepted s.cfg m.footprints := by
  unfold displayed at h
  cases hp : s.acknowledged with
  | none => simp [hp] at h
  | some approved =>
    simp only [hp,Option.map_some,Option.some.injEq] at h
    subst m
    exact approved.valid

theorem picked_displayed_geometry (s : Session) (x y : Int) (part : PaintedPart)
    (h : pick s x y = some part) :
    ∃ m, displayed s = some m ∧ LayoutAccepted s.cfg m.footprints ∧
      part ∈ m.parts ∧ part.visible = true ∧ NativeGeometry.hit part.shape x y = some true ∧
      part.shape ∈ m.scene.shapes := by
  unfold pick at h
  split at h
  · contradiction
  cases visible : displayed s with
  | none => simp [visible] at h
  | some m =>
    simp only [visible,Option.bind_some] at h
    exact ⟨m,rfl,displayed_certified s m visible,m.pick_mem_parts x y part h,
      m.pick_visible x y part h,m.pick_hit x y part h,m.pick_shape_mem_scene x y part h⟩

theorem shown_application_budget (s : Session) (m : Model) (shownEq : shown s = some m)
    (report : NodeCheck) (member : report ∈ checkFootprints s.cfg m.footprints) :
    0 < report.area ∧ 10000*report.overlapSum ≤ s.cfg.application.maxOverlapBps*report.area :=
  certify_application_bound s.cfg m.footprints ((certify_iff _ _).mpr (shown_certified s m shownEq)) report member

theorem displayed_application_budget (s : Session) (m : Model) (shownEq : displayed s = some m)
    (report : NodeCheck) (member : report ∈ checkFootprints s.cfg m.footprints) :
    0 < report.area ∧ 10000*report.overlapSum ≤ s.cfg.application.maxOverlapBps*report.area :=
  certify_application_bound s.cfg m.footprints ((certify_iff _ _).mpr (displayed_certified s m shownEq)) report member

end NativeFoafPresentation
