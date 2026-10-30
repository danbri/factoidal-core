import L4Factoidal.UI.LayoutPolicy

/- Renderer-independent admission of complete scenes. A renderer can retain
the last approved scene between checks, but cannot obtain an unapproved
candidate from this interface. A changed rendering context (viewport, font
metrics, etc.) invalidates that retained scene. The caller supplies a monotonic
clock; context changes retain the global check timestamp. Requested cadence
sets minimum check spacing, not a guarantee of callbacks. Empty footprint
lists satisfy the every-node predicate vacuously; no nonempty-scene claim. -/
namespace L4Factoidal.UI.Presentation
open Geometry LayoutPolicy

structure Approved (Scene : Type) (cfg : Config) (footprints : Scene → List (Option Box)) where
  scene : Scene
  valid : LayoutAccepted cfg (footprints scene)

def inspect (cfg : Config) (footprints : Scene → List (Option Box)) (scene : Scene) :
    Option (Approved Scene cfg footprints) :=
  if h : certify cfg (footprints scene) = true then
    some ⟨scene,(certify_iff cfg (footprints scene)).mp h⟩
  else none

structure State (Scene : Type) (cfg : Config) (footprints : Scene → List (Option Box)) where
  context : String
  shown : Option (Approved Scene cfg footprints) := none
  lastCheckMs : Option Nat := none

inductive Status where
  | accepted | rejected | deferred | clockWentBack
  deriving Repr, BEq, DecidableEq

structure Decision (Scene : Type) (cfg : Config) (footprints : Scene → List (Option Box)) where
  state : State Scene cfg footprints
  status : Status

def due (cfg : Config) (last now : Nat) : Bool :=
  decide (last ≤ now ∧ 1000 ≤ (now-last)*cfg.checkHz)

theorem due_iff (cfg : Config) (last now : Nat) :
    due cfg last now = true ↔ last ≤ now ∧ 1000 ≤ (now-last)*cfg.checkHz := by
  simp [due]

/-- Only an approved candidate can replace `shown`. An unchanged approved
scene remains geometrically valid between checks; this is stronger than
sampling arbitrary independently changing renderer state at the chosen Hz. -/
def submit (cfg : Config) (footprints : Scene → List (Option Box))
    (state : State Scene cfg footprints) (context : String) (now : Nat) (candidate : Scene) :
    Decision Scene cfg footprints :=
  let current := if context == state.context then state else {state with context,shown:=none}
  match current.lastCheckMs with
  | some last =>
    if now < last then ⟨current,.clockWentBack⟩
    else if !due cfg last now then ⟨current,.deferred⟩
    else
      match inspect cfg footprints candidate with
      | some approved => ⟨{current with shown:=some approved,lastCheckMs:=some now},.accepted⟩
      | none => ⟨{current with lastCheckMs:=some now},.rejected⟩
  | none =>
    match inspect cfg footprints candidate with
    | some approved => ⟨{current with shown:=some approved,lastCheckMs:=some now},.accepted⟩
    | none => ⟨{current with lastCheckMs:=some now},.rejected⟩

theorem inspect_scene (cfg : Config) (footprints : Scene → List (Option Box))
    (candidate : Scene) (approved : Approved Scene cfg footprints)
    (h : inspect cfg footprints candidate = some approved) : approved.scene = candidate := by
  unfold inspect at h
  split at h
  · cases h; rfl
  · contradiction

-- This is an operational property of submit: accepting cannot substitute a
-- different scene, and it certifies the candidate actually submitted.
theorem submit_accepted_candidate (cfg : Config) (footprints : Scene → List (Option Box))
    (state : State Scene cfg footprints) (context : String) (now : Nat) (candidate : Scene)
    (accepted : (submit cfg footprints state context now candidate).status = .accepted) :
    ∃ approved : Approved Scene cfg footprints,
      (submit cfg footprints state context now candidate).state.shown = some approved ∧
      approved.scene = candidate ∧ LayoutAccepted cfg (footprints candidate) := by
  unfold submit at accepted ⊢
  generalize hc : (if context == state.context then state else {state with context,shown:=none}) = current at accepted ⊢
  dsimp only at accepted ⊢
  cases hl : current.lastCheckMs with
  | none =>
    simp only [hl] at accepted ⊢
    cases inspected : inspect cfg footprints candidate with
    | none => simp [inspected] at accepted
    | some approved =>
      have sceneEq := inspect_scene cfg footprints candidate approved inspected
      exact ⟨approved,rfl,sceneEq,sceneEq ▸ approved.valid⟩
  | some last =>
    by_cases rollback : now < last
    · simp [hl,rollback] at accepted
    · by_cases waiting : (!due cfg last now) = true
      · simp [hl,rollback,waiting] at accepted
      · simp only [hl, if_neg rollback, if_neg waiting] at accepted ⊢
        cases inspected : inspect cfg footprints candidate with
        | none => simp [inspected] at accepted
        | some approved =>
          have sceneEq := inspect_scene cfg footprints candidate approved inspected
          exact ⟨approved,rfl,sceneEq,sceneEq ▸ approved.valid⟩

-- No transition, including context invalidation or rollback, moves a known
-- global check timestamp backwards. This does not assert callback liveness.
theorem submit_timestamp_monotonic (cfg : Config) (footprints : Scene → List (Option Box))
    (state : State Scene cfg footprints) (context : String) (now : Nat) (candidate : Scene)
    (previous : Nat) (known : state.lastCheckMs = some previous) :
    ∃ next, (submit cfg footprints state context now candidate).state.lastCheckMs = some next ∧
      previous ≤ next := by
  cases contextEq : (context == state.context)
  all_goals
    by_cases rollback : now < previous
    · exact ⟨previous,by simp [submit,contextEq,known,rollback],Nat.le_refl _⟩
    · by_cases waiting : (!due cfg previous now) = true
      · exact ⟨previous,by simp [submit,contextEq,known,rollback,waiting],Nat.le_refl _⟩
      · refine ⟨now,?_,by omega⟩
        cases inspected : inspect cfg footprints candidate <;>
          simp [submit,contextEq,known,rollback,waiting,inspected]

theorem shown_is_certified (cfg : Config) (footprints : Scene → List (Option Box))
    (state : State Scene cfg footprints) (approved : Approved Scene cfg footprints)
    (_ : state.shown = some approved) : LayoutAccepted cfg (footprints approved.scene) :=
  approved.valid

theorem submitted_scene_is_certified (cfg : Config) (footprints : Scene → List (Option Box))
    (state : State Scene cfg footprints) (context : String) (now : Nat) (candidate : Scene)
    (approved : Approved Scene cfg footprints)
    (_ : (submit cfg footprints state context now candidate).state.shown = some approved) :
    LayoutAccepted cfg (footprints approved.scene) := approved.valid

end L4Factoidal.UI.Presentation
