/-
Private-history grouping policy: a pure scheduling component, not a journal,
Git writer, RDF configuration parser or background service.

Durations and timestamps are integer milliseconds from ONE monotonic clock
epoch. UTC is not accepted here. Persisted windows cannot be resumed under a
reset clock without a separate recovery protocol. Configuration is frozen in
the Pending type; changing it requires flushing or an explicit migration.

Application-selected caps bound the allowed quiet period and maximum delay.
The clock/scheduler/IO obligations remain external: tick must actually be called,
and a flush decision must be delivered. A deadline theorem means flush becomes
the decision by that time; it does not mean a Git/disk/network write completes.

Principal/application/session labels only partition groups. They are supplied
from the authenticated context and are not credentials or access decisions.
When onRevision requests a flush, the incoming revision has NOT been consumed.
The durable journal must keep it until the consumer completes or retries.
-/
import Std

namespace L4Factoidal.LWS.HistoryPolicy

structure Bounds where
  minQuietMs : Nat
  maxQuietMs : Nat
  minDelayMs : Nat
  maxDelayMs : Nat
  deriving DecidableEq, Repr

structure Config where
  quietMs : Nat
  maxDelayMs : Nat
  deriving DecidableEq, Repr

def Bounds.Valid (b : Bounds) : Prop :=
  0 < b.minQuietMs ∧ b.minQuietMs ≤ b.maxQuietMs ∧
  0 < b.minDelayMs ∧ b.minDelayMs ≤ b.maxDelayMs ∧
  b.minQuietMs ≤ b.maxDelayMs

instance (b : Bounds) : Decidable b.Valid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- Meaningful numeric caps come from an application, not a universal claim
that one set of durations is useful for every history destination. -/
def Config.Valid (b : Bounds) (c : Config) : Prop :=
  b.Valid ∧ b.minQuietMs ≤ c.quietMs ∧ c.quietMs ≤ b.maxQuietMs ∧
  b.minDelayMs ≤ c.maxDelayMs ∧ c.maxDelayMs ≤ b.maxDelayMs ∧
  c.quietMs ≤ c.maxDelayMs

instance (b : Bounds) (c : Config) : Decidable (c.Valid b) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

abbrev CheckedConfig (b : Bounds) := {c : Config // c.Valid b}

inductive ConfigError where
  | invalidBounds | invalidConfig
  deriving DecidableEq, Repr

def validate (b : Bounds) (c : Config) : Except ConfigError (CheckedConfig b) :=
  if b.Valid then
    if h : c.Valid b then .ok ⟨c, h⟩ else .error .invalidConfig
  else .error .invalidBounds

theorem validate_preserves {b : Bounds} {c : Config} {checked : CheckedConfig b}
    (h : validate b c = .ok checked) : checked.val = c := by
  unfold validate at h
  split at h
  · split at h
    · cases h; rfl
    · cases h
  · cases h

theorem validate_rejects_invalid {b : Bounds} {c : Config} (invalid : ¬ c.Valid b) :
    ∃ error, validate b c = .error error := by
  unfold validate
  split
  · exact ⟨.invalidConfig, rfl⟩
  · exact ⟨.invalidBounds, rfl⟩

theorem validate_accepts_valid {b : Bounds} {c : Config} (valid : c.Valid b) :
    validate b c = .ok ⟨c, valid⟩ := by
  simp [validate, valid, valid.1]

theorem checked_positive {b : Bounds} (c : CheckedConfig b) :
    0 < c.val.quietMs ∧ c.val.quietMs ≤ c.val.maxDelayMs ∧ 0 < c.val.maxDelayMs := by
  have valid := c.property
  rcases valid with ⟨hb, hq, _, hd, _, hqd⟩
  rcases hb with ⟨hminq, _, hmind, _, _⟩
  exact ⟨by omega, hqd, by omega⟩

structure Scope where
  principal : String
  application : String
  session : Option String
  deriving DecidableEq, Repr

/-- A pending group's immutable first timestamp fixes its maximum deadline.
No accepted extension can advance last to or beyond that deadline. -/
structure Pending {b : Bounds} (c : CheckedConfig b) where
  scope : Scope
  firstMs : Nat
  lastMs : Nat
  ordered : firstMs ≤ lastMs
  beforeMaximum : lastMs < firstMs + c.val.maxDelayMs

def start {b : Bounds} (c : CheckedConfig b) (scope : Scope) (nowMs : Nat) : Pending c :=
  ⟨scope, nowMs, nowMs, Nat.le_refl _, by have h := (checked_positive c).2.2; omega⟩

def maximumDeadline {b : Bounds} {c : CheckedConfig b} (pending : Pending c) : Nat :=
  pending.firstMs + c.val.maxDelayMs

def quietDeadline {b : Bounds} {c : CheckedConfig b} (pending : Pending c) : Nat :=
  pending.lastMs + c.val.quietMs

def nextDeadline {b : Bounds} {c : CheckedConfig b} (pending : Pending c) : Nat :=
  min (quietDeadline pending) (maximumDeadline pending)

inductive Reason where
  | maximumDelay | quietPeriod | scopeChange
  deriving DecidableEq, Repr

inductive Decision where
  | wait (deadlineMs : Nat)
  | flush (reason : Reason)
  deriving DecidableEq, Repr

inductive ClockError where
  | backwards
  deriving DecidableEq, Repr

/-- Tick refuses a timestamp earlier than the last accepted revision. Maximum
delay wins when both conditions hold, giving stable diagnostic precedence. -/
def tick {b : Bounds} {c : CheckedConfig b} (pending : Pending c) (nowMs : Nat) :
    Except ClockError Decision :=
  if nowMs < pending.lastMs then .error .backwards
  else if maximumDeadline pending ≤ nowMs then .ok (.flush .maximumDelay)
  else if quietDeadline pending ≤ nowMs then .ok (.flush .quietPeriod)
  else .ok (.wait (nextDeadline pending))

theorem deadline_bounded {b : Bounds} {c : CheckedConfig b} (pending : Pending c) :
    nextDeadline pending ≤ maximumDeadline pending := Nat.min_le_right _ _

/-- Continuous writes cannot postpone the decision past the first timestamp's
maximum deadline. This is conditional on a tick reaching that timestamp. -/
theorem tick_at_maximum {b : Bounds} {c : CheckedConfig b} (pending : Pending c)
    (nowMs : Nat) (reached : maximumDeadline pending ≤ nowMs) :
    tick pending nowMs = .ok (.flush .maximumDelay) := by
  have before := pending.beforeMaximum
  have notBackwards : ¬ nowMs < pending.lastMs := by
    unfold maximumDeadline at reached
    omega
  simp [tick, notBackwards, reached]

/-- The minimum of the quiet and maximum deadlines always requests a flush
once reached; it cannot return wait or a backwards-clock error then. -/
theorem tick_at_deadline {b : Bounds} {c : CheckedConfig b} (pending : Pending c)
    (nowMs : Nat) (reached : nextDeadline pending ≤ nowMs) :
    ∃ reason, tick pending nowMs = .ok (.flush reason) := by
  have hp := (checked_positive c).1
  have hb := pending.beforeMaximum
  have hn : ¬ nowMs < pending.lastMs := by
    unfold nextDeadline quietDeadline maximumDeadline at reached
    omega
  by_cases hm : maximumDeadline pending ≤ nowMs
  · exact ⟨.maximumDelay, tick_at_maximum pending nowMs hm⟩
  · have hq : quietDeadline pending ≤ nowMs := by unfold nextDeadline at reached; omega
    exact ⟨.quietPeriod, by simp [tick, hn, hm, hq]⟩

inductive RevisionDecision {b : Bounds} (c : CheckedConfig b) where
  | extend (pending : Pending c)
  | flush (reason : Reason)

/-- Derive a new pending window only before all flush conditions. A scope
change requests a boundary; no user-supplied session can erase the deadline.
Flush leaves the incoming revision for the caller to retry in a new group. -/
def onRevision {b : Bounds} {c : CheckedConfig b} (pending : Pending c)
    (scope : Scope) (nowMs : Nat) : Except ClockError (RevisionDecision c) :=
  if hclock : nowMs < pending.lastMs then .error .backwards
  else if hmax : maximumDeadline pending ≤ nowMs then .ok (.flush .maximumDelay)
  else if quietDeadline pending ≤ nowMs then .ok (.flush .quietPeriod)
  else if scope ≠ pending.scope then .ok (.flush .scopeChange)
  else .ok (.extend ⟨pending.scope, pending.firstMs, nowMs,
    by have ordered := pending.ordered; omega,
    by unfold maximumDeadline at hmax; omega⟩)

theorem extension_preserves {b : Bounds} {c : CheckedConfig b}
    {old next : Pending c} {scope : Scope} {nowMs : Nat}
    (h : onRevision old scope nowMs = .ok (.extend next)) :
    next.firstMs = old.firstMs ∧ next.scope = old.scope ∧
    scope = old.scope ∧ next.lastMs = nowMs ∧ old.lastMs ≤ nowMs := by
  unfold onRevision at h
  split at h
  · cases h
  · rename_i hclock
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · rename_i hscope
          cases h
          exact ⟨rfl, rfl, by simpa using hscope, rfl, by omega⟩

/-- Actual accepted debounce updates retain the original maximum deadline. -/
theorem extension_cannot_postpone_maximum {b : Bounds} {c : CheckedConfig b}
    {old next : Pending c} {scope : Scope} {nowMs : Nat}
    (h : onRevision old scope nowMs = .ok (.extend next)) :
    maximumDeadline next = maximumDeadline old ∧ nextDeadline next ≤ maximumDeadline old := by
  have first := (extension_preserves h).1
  have same : maximumDeadline next = maximumDeadline old := by simp [maximumDeadline, first]
  exact ⟨same, by rw [← same]; exact deadline_bounded next⟩

theorem revision_at_maximum {b : Bounds} {c : CheckedConfig b} (pending : Pending c)
    (scope : Scope) (nowMs : Nat) (reached : maximumDeadline pending ≤ nowMs) :
    onRevision pending scope nowMs = .ok (.flush .maximumDelay) := by
  have before := pending.beforeMaximum
  have notBackwards : ¬ nowMs < pending.lastMs := by
    unfold maximumDeadline at reached
    omega
  simp [onRevision, notBackwards, reached]

/-- Clock cursor for callers that poll repeatedly between revisions. Preserve
the returned cursor across calls; retaining an earlier cursor invalidates the
cross-call monotonicity guarantee. It is local to the same clock epoch. -/
structure ClockCursor where
  observedMs : Nat
  deriving DecidableEq, Repr

def withMonotonicTime {α : Type} (cursor : ClockCursor) (nowMs : Nat)
    (operation : Unit → Except ClockError α) : Except ClockError (α × ClockCursor) :=
  if nowMs < cursor.observedMs then .error .backwards
  else (operation ()).map fun value => (value, ⟨nowMs⟩)

theorem withMonotonicTime_preserves {α : Type} {cursor next : ClockCursor}
    {nowMs : Nat} {operation : Unit → Except ClockError α} {value : α}
    (h : withMonotonicTime cursor nowMs operation = .ok (value, next)) :
    cursor.observedMs ≤ nowMs ∧ next.observedMs = nowMs ∧ operation () = .ok value := by
  unfold withMonotonicTime at h
  split at h
  · cases h
  · rename_i hn
    cases ho : operation () with
    | error error => simp [ho, Except.map] at h
    | ok result =>
      simp only [ho, Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨sameValue, sameCursor⟩ := h
      subst value
      subst next
      exact ⟨by omega, rfl, rfl⟩

def poll {b : Bounds} {c : CheckedConfig b} (cursor : ClockCursor)
    (pending : Pending c) (nowMs : Nat) : Except ClockError (Decision × ClockCursor) :=
  withMonotonicTime cursor nowMs fun _ => tick pending nowMs

def recordRevision {b : Bounds} {c : CheckedConfig b} (cursor : ClockCursor)
    (pending : Pending c) (scope : Scope) (nowMs : Nat) :
    Except ClockError (RevisionDecision c × ClockCursor) :=
  withMonotonicTime cursor nowMs fun _ => onRevision pending scope nowMs

/-- If a monotonic observation reaches the maximum deadline, the public poll
operation returns a flush and advances its clock cursor to that timestamp. -/
theorem poll_at_maximum {b : Bounds} {c : CheckedConfig b} (cursor : ClockCursor)
    (pending : Pending c) (nowMs : Nat) (monotonic : cursor.observedMs ≤ nowMs)
    (reached : maximumDeadline pending ≤ nowMs) :
    poll cursor pending nowMs = .ok (.flush .maximumDelay, ⟨nowMs⟩) := by
  have hn : ¬ nowMs < cursor.observedMs := by omega
  simp [poll, withMonotonicTime, hn, tick_at_maximum pending nowMs reached, Except.map]

/-! Kernel-evaluated examples: explicit application bounds, not global defaults. -/
private def exampleBounds : Bounds := ⟨100, 5000, 1000, 60000⟩
private def exampleConfig : CheckedConfig exampleBounds := ⟨⟨2000, 30000⟩, by decide⟩
private def exampleScope : Scope := ⟨"alice", "compositor", some "session-1"⟩
private def examplePending := start exampleConfig exampleScope 10000
private def exampleLatePending : Pending exampleConfig :=
  ⟨exampleScope, 10000, 39000, by decide, by decide⟩

example : validate exampleBounds ⟨0, 30000⟩ = .error .invalidConfig := by rfl
example : validate exampleBounds ⟨5001, 30000⟩ = .error .invalidConfig := by rfl
example : validate exampleBounds ⟨2000, 1000⟩ = .error .invalidConfig := by rfl
example : validate exampleBounds ⟨2000, 60001⟩ = .error .invalidConfig := by rfl
example : validate ⟨0, 5000, 1000, 60000⟩ ⟨2000, 30000⟩ = .error .invalidBounds := by rfl
example : tick examplePending 9999 = .error .backwards := by rfl
example : tick examplePending 11999 = .ok (.wait 12000) := by rfl
example : tick examplePending 12000 = .ok (.flush .quietPeriod) := by rfl
example : tick examplePending 40000 = .ok (.flush .maximumDelay) := by rfl
example : onRevision examplePending {exampleScope with principal := "bob"} 11000 =
    .ok (.flush .scopeChange) := by rfl
example : onRevision examplePending exampleScope 12000 = .ok (.flush .quietPeriod) := by rfl
example : poll ⟨11500⟩ examplePending 11400 = .error .backwards := by rfl
example : poll ⟨11500⟩ examplePending 12000 = .ok (.flush .quietPeriod, ⟨12000⟩) := by rfl
example : recordRevision ⟨11500⟩ examplePending exampleScope 11400 = .error .backwards := by rfl
example : nextDeadline exampleLatePending = 40000 := by rfl
example : tick exampleLatePending 39999 = .ok (.wait 40000) := by rfl
example : tick exampleLatePending 40000 = .ok (.flush .maximumDelay) := by rfl
example : (match onRevision examplePending exampleScope 11000 with
    | .ok (.extend next) => (next.firstMs, next.lastMs, maximumDeadline next, nextDeadline next)
    | _ => (0, 0, 0, 0)) = (10000, 11000, 40000, 13000) := by rfl

#print axioms validate_rejects_invalid
#print axioms validate_accepts_valid
#print axioms tick_at_maximum
#print axioms tick_at_deadline
#print axioms extension_cannot_postpone_maximum
#print axioms revision_at_maximum
#print axioms withMonotonicTime_preserves
#print axioms poll_at_maximum

end L4Factoidal.LWS.HistoryPolicy
