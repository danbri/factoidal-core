import L4Factoidal.UI.Geometry

/- Experimental renderer-independent graph-browser policy. The ranges and
500 basis-point / 12 Hz defaults are HUMAN-CHOSEN EXPERIMENTAL parameters;
no theorem establishes UX usefulness or OS scheduling. A requested frequency
is configuration metadata, not a clock guarantee. Aggregate pairwise bounding
box areas may double count the same region; no exact union/pixel area claim.
Adapters supply authoritative visible footprints in a common coordinate space. -/
namespace L4Factoidal.UI.LayoutPolicy
open L4Factoidal.UI.Geometry

structure Profile where
  name : String
  minOverlapBps : Nat
  maxOverlapBps : Nat
  minCheckHz : Nat
  maxCheckHz : Nat
  deriving Repr

def experimentalGraphBrowserV1 : Profile :=
  ⟨"experimental-graph-browser-v1",300,700,12,24⟩

abbrev InProfile (overlapBps checkHz : Nat) : Prop :=
  experimentalGraphBrowserV1.minOverlapBps ≤ overlapBps ∧
  overlapBps ≤ experimentalGraphBrowserV1.maxOverlapBps ∧
  experimentalGraphBrowserV1.minCheckHz ≤ checkHz ∧
  checkHz ≤ experimentalGraphBrowserV1.maxCheckHz

abbrev ApplicationBounds (minBps maxBps minHz maxHz : Nat) : Prop :=
  experimentalGraphBrowserV1.minOverlapBps ≤ minBps ∧ minBps ≤ maxBps ∧
  maxBps ≤ experimentalGraphBrowserV1.maxOverlapBps ∧
  experimentalGraphBrowserV1.minCheckHz ≤ minHz ∧ minHz ≤ maxHz ∧
  maxHz ≤ experimentalGraphBrowserV1.maxCheckHz

-- Applications may narrow the experimental envelope; callers cannot widen it.
structure ApplicationPolicy where
  minOverlapBps : Nat
  maxOverlapBps : Nat
  minCheckHz : Nat
  maxCheckHz : Nat
  valid : ApplicationBounds minOverlapBps maxOverlapBps minCheckHz maxCheckHz
  deriving Repr, DecidableEq

def validatePolicy (minBps maxBps minHz maxHz : Nat) : Except String ApplicationPolicy :=
  if h : ApplicationBounds minBps maxBps minHz maxHz then .ok ⟨minBps,maxBps,minHz,maxHz,h⟩
  else .error "application bounds must be ordered subintervals of overlapBps 300..700 and checkHz 12..24"

theorem validatePolicy_rejects_outside (minBps maxBps minHz maxHz : Nat)
    (h : ¬ ApplicationBounds minBps maxBps minHz maxHz) :
    ∃ message, validatePolicy minBps maxBps minHz maxHz = .error message := by
  simp [validatePolicy, h]

def fullEnvelope : ApplicationPolicy := ⟨300,700,12,24,by decide⟩

abbrev InApplication (app : ApplicationPolicy) (overlapBps checkHz : Nat) : Prop :=
  app.minOverlapBps ≤ overlapBps ∧ overlapBps ≤ app.maxOverlapBps ∧
  app.minCheckHz ≤ checkHz ∧ checkHz ≤ app.maxCheckHz

structure Config where
  application : ApplicationPolicy
  overlapBps : Nat
  checkHz : Nat
  valid : InApplication application overlapBps checkHz
  deriving Repr, DecidableEq

def validateFor (app : ApplicationPolicy) (overlapBps checkHz : Nat) : Except String Config :=
  if h : InApplication app overlapBps checkHz then .ok ⟨app,overlapBps,checkHz,h⟩
  else .error "chosen overlapBps/checkHz must stay within application bounds"

-- Convenience entry for the full experimental envelope, not an application
-- override. Apps with a tighter contract must use validateFor their policy.
def validate (overlapBps checkHz : Nat) : Except String Config :=
  validateFor fullEnvelope overlapBps checkHz

def defaultConfig : Config := ⟨fullEnvelope,500,12,by decide⟩

theorem Config.within_application (cfg : Config) :
    InApplication cfg.application cfg.overlapBps cfg.checkHz := cfg.valid

theorem Config.within_profile (cfg : Config) : InProfile cfg.overlapBps cfg.checkHz := by
  have h := cfg.valid
  have outer := cfg.application.valid
  simp only [InApplication, ApplicationBounds, InProfile] at *
  omega

theorem validateFor_preserves_values (app : ApplicationPolicy) (bps hz : Nat) (cfg : Config)
    (h : validateFor app bps hz = .ok cfg) :
    cfg.application = app ∧ cfg.overlapBps = bps ∧ cfg.checkHz = hz := by
  unfold validateFor at h
  split at h
  · cases h; exact ⟨rfl,rfl,rfl⟩
  · contradiction

theorem validate_preserves_values (bps hz : Nat) (cfg : Config)
    (h : validate bps hz = .ok cfg) : cfg.overlapBps = bps ∧ cfg.checkHz = hz :=
  (validateFor_preserves_values fullEnvelope bps hz cfg h).2

theorem validateFor_rejects_outside (app : ApplicationPolicy) (bps hz : Nat)
    (h : ¬ InApplication app bps hz) :
    ∃ message, validateFor app bps hz = .error message := by simp [validateFor, h]

theorem validate_rejects_outside (bps hz : Nat) (h : ¬ InProfile bps hz) :
    ∃ message, validate bps hz = .error message := by
  apply validateFor_rejects_outside
  simpa only [InApplication, fullEnvelope, InProfile, experimentalGraphBrowserV1] using h

-- Sum deliberately counts overlapping regions repeatedly.
def overlapSum (b : Box) (others : List Box) : Nat :=
  (others.map fun other => (b.intersection other).area).sum

abbrev Budget (cfg : Config) (area sum : Nat) : Prop :=
  0 < area ∧ 10000*sum ≤ cfg.overlapBps*area

def withinBudget (cfg : Config) (area sum : Nat) : Bool := decide (Budget cfg area sum)

theorem withinBudget_iff (cfg : Config) (area sum : Nat) :
    withinBudget cfg area sum = true ↔ 0 < area ∧ 10000*sum ≤ cfg.overlapBps*area := by
  simp [withinBudget]

theorem overlapSum_member_le (b other : Box) (others : List Box) (h : other ∈ others) :
    (b.intersection other).area ≤ overlapSum b others := by
  induction others with
  | nil => simp at h
  | cons a rest ih =>
    simp only [List.mem_cons] at h
    simp only [overlapSum, List.map_cons, List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; unfold overlapSum at this; omega

structure NodeCheck where
  index : Nat
  footprint : Option Box
  area : Nat
  overlapSum : Nat
  accepted : Bool
  deriving Repr

-- Missing/empty footprints retain a report and fail positive area. Each node
-- excludes its own index, so duplicate boxes still count as distinct nodes.
def checkFootprints (cfg : Config) (boxes : List (Option Box)) : List NodeCheck :=
  boxes.zipIdx |>.map fun (box,i) =>
    let others := boxes.zipIdx.filterMap fun (other,j) => if i == j then none else other
    let area := box.map Box.area |>.getD 0
    let sum := box.map (fun b => overlapSum b others) |>.getD 0
    ⟨i,box,area,sum,withinBudget cfg area sum⟩

theorem checkFootprints_length (cfg : Config) (boxes : List (Option Box)) :
    (checkFootprints cfg boxes).length = boxes.length := by simp [checkFootprints]

theorem checkFootprints_accepted_iff (cfg : Config) (boxes : List (Option Box)) (report : NodeCheck)
    (member : report ∈ checkFootprints cfg boxes) :
    report.accepted = true ↔ 0 < report.area ∧ 10000*report.overlapSum ≤ cfg.overlapBps*report.area := by
  simp only [checkFootprints, List.mem_map] at member
  obtain ⟨entry, _, rfl⟩ := member
  exact withinBudget_iff _ _ _

-- One reusable predicate/certifier for every renderer adapter.
def LayoutAccepted (cfg : Config) (boxes : List (Option Box)) : Prop :=
  ∀ report ∈ checkFootprints cfg boxes, Budget cfg report.area report.overlapSum

def certify (cfg : Config) (boxes : List (Option Box)) : Bool :=
  (checkFootprints cfg boxes).all (·.accepted)

theorem certify_iff (cfg : Config) (boxes : List (Option Box)) :
    certify cfg boxes = true ↔ LayoutAccepted cfg boxes := by
  simp only [certify, List.all_eq_true, LayoutAccepted]
  constructor
  · intro accepted report member
    exact (checkFootprints_accepted_iff cfg boxes report member).mp (accepted report member)
  · intro accepted report member
    exact (checkFootprints_accepted_iff cfg boxes report member).mpr (accepted report member)

theorem certify_sound (cfg : Config) (boxes : List (Option Box)) (h : certify cfg boxes = true) :
    InProfile cfg.overlapBps cfg.checkHz ∧
    ∀ report ∈ checkFootprints cfg boxes,
      0 < report.area ∧ 10000*report.overlapSum ≤ cfg.overlapBps*report.area :=
  ⟨cfg.within_profile, (certify_iff cfg boxes).mp h⟩

theorem certify_application_bound (cfg : Config) (boxes : List (Option Box))
    (certified : certify cfg boxes = true) (report : NodeCheck)
    (member : report ∈ checkFootprints cfg boxes) :
    0 < report.area ∧ 10000*report.overlapSum ≤ cfg.application.maxOverlapBps*report.area := by
  have budget := (certify_sound cfg boxes certified).2 report member
  exact ⟨budget.1, Nat.le_trans budget.2 (Nat.mul_le_mul_right _ cfg.valid.2.1)⟩

end L4Factoidal.UI.LayoutPolicy
