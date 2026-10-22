/-
Capability-aware planner, KR 2.4: the execution state machine.

OKR batch 2, KR 2.4: https://github.com/danbri/factoidal/issues/801
(epic https://github.com/danbri/factoidal/issues/800). Design record:
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 11.

The execution of a plan family (`Planner.Search`) as a state machine, in
the manner of TLA+: a state, an initial predicate `Init`, one predicate
per action on a pair of states, and `Next`, the disjunction of the
actions. The inductive invariant `Inv` is proved for `Init` (`init_inv`)
and kept by `Next` (`next_inv`), so it holds in every reachable state
(`reachable_inv`, induction on traces).

State: the current plan (a rewriting of the family), the alternatives
not yet tried, the step index (the access of the plan that runs now), the
rows of the plan prefix that still need a call of that access
(`pending`), the rows that the access gave so far (`next`), the phase of
the call (`idle`, `waiting`, `failed`), the retries of the current call,
the number of calls made to each source of the catalog (`calls`, by
catalog index), the output, and the status (`running`, `done`,
`stopped`). Each row carries the approximation marker of `Plan.exec`.

Actions:

* `Call`: call the current access for the head pending row. Enabled only
  when every required input of the access is bound in that row
  (`Access.inputs?` gives a value) and the call quota of the source is
  not exhausted (`quotaOk`). It counts the call.
* `Receive`: the call answers with the tuples of the source's
  implementation, when they are within the source's row quota
  (`rowQuotaOk`); the rows they give (exactly as `Plan.exec` gives them
  for the access) are added to `next`. The observed-cost record
  (`answered`, `rows`, `latency`) and the cache of call results are
  updated.
* `Hit` (OKR batch 3, KR 4.2): the head pending row's call is in the
  cache; its rows are added to `next` with no call.
* `Fail`: the call fails (an action of the environment).
* `Retry`: call again after a failure, at most `Config.maxRetries` times
  for one row, and only within the quota. It counts the call.
* `Advance`: when no pending row is left, the next access runs over the
  rows of `next`.
* `Adapt`: choose another plan of the admitted family and start it. The
  call counts are kept: calls already made count against the quotas.
* `Finish`: after the last access, apply the requirement's filters and
  projection; the status becomes `done`.
* `Stop`: give up; the status becomes `stopped` and there is no output.

Invariants (`Inv`), proved for every reachable state:

* (I1) `reachable_sound`: no unmarked output row is outside the
  requirement's answers over the declared graph of the catalog (reuses
  `rewriting_sound`).
* (I2) `reachable_quota`: no source's call count exceeds its call quota;
  `reachable_rowQuota`: no source returns more tuples than its row quota.
* `reachable_cache`, `reachable_cache_hit`: every cache entry is the
  call's result (the implementation's tuples for the recorded input), so
  the rows of a cache hit are the rows `Plan.exec` gives for the access.
* `reachable_output`: when the status is `done`, the output IS the run
  (`Plan.run`) of the current plan, as a list, and that plan is a member
  of the admitted family. So the machine loses no answer of the plan it
  finishes with, and adaptation chooses only inside the family.
* `Inv.retries_le`: the retries of one call never exceed the bound.

Termination: every action decreases the measure `measure` in the
lexicographic order (`next_measure_lt`), so `Next` has no infinite
chain (`next_wf`). The executable driver `runFrom` (a deterministic
choice among the enabled actions, with a fault schedule and a latency
schedule for the environment) makes one step of `Next` per iteration
(`stepExec_next`); when it must leave a plan it takes the alternative of
least `adaptScore` (measured rows per call, measured latency per
location, known calls, and the remaining quotas),
is defined by well-founded recursion on that measure, and ends with the
status `done` or `stopped` (`runFrom_final`). `run_spec` collects the
results for a run over the admitted family (`searchAdmitted`: the members
of `search` whose estimated calls and tuples are within the quotas).

Hypotheses (anti-pattern 29): `ExactSourcesSound` (each exact source
returns only tuples of its declared extension) and the rewriting check
of each family member (`search_check` discharges it for the search's
family). Neither mentions the output or the requirement's answers.

Limits: capability implementations are pure functions here
(https://github.com/danbri/factoidal/issues/933, expected-failure case
`exec-driver-io` of `lake exe l4planner-test`). The cache is a list
searched from the front. No theorem is about the costs or about the
choice of the alternative: any member of the family keeps `Inv`.

Recursion: `runFrom` is a tail call (a loop in the compiled code). No
`partial`.
-/
import L4Factoidal.Planner.Search
import L4Factoidal.Planner.ExecM

namespace L4Factoidal.Planner.Exec

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner

/-! ## State -/

structure Config where
  /-- The number of retries allowed for one call after a failure. -/
  maxRetries : Nat := 1
  /-- The estimate's rows for each new variable when a source has no
  statistic and no measurement (`Planner.Search.statModel`). -/
  fanout : Nat := 10
  deriving Repr

/-- The phase of the call for the head pending row. -/
inductive Phase where
  | idle
  | waiting
  | failed
  deriving DecidableEq, Repr

inductive Status where
  | running
  | done
  | stopped
  deriving DecidableEq, Repr

/-- A call whose answer is known: the source (catalog index), the input
binding, and the tuples the call returned. -/
structure CacheEntry where
  src : Nat
  inp : InputBinding
  tuples : List Tuple

/-- The empty solution mapping, unmarked: the row a plan starts from. -/
def row0 : Row := { binding := [], approx := false }

structure State where
  plan : Rewriting
  /-- The plans of the family that were not tried yet. -/
  alts : List Rewriting
  /-- The index of the access of `plan` that runs now. -/
  step : Nat
  /-- Rows of the plan prefix that still need a call of the access. -/
  pending : List Row
  /-- Rows the access gave so far. -/
  next : List Row
  phase : Phase
  /-- Retries made for the current call. -/
  retries : Nat
  /-- Calls made to each source, by catalog index. -/
  calls : Nat → Nat
  output : List Row
  status : Status
  /-- The number of adaptations (plan switches). -/
  switches : Nat
  /-- The observed-cost record, by catalog index: calls answered, tuples
  received (the count for the row quota), and the sum of the latencies of
  the answered calls. Each `Receive` updates it. -/
  answered : Nat → Nat
  rows : Nat → Nat
  latency : Nat → Nat
  /-- The answers of the calls made so far. -/
  cache : List CacheEntry
  /-- Rows of a plan answered from the cache, with no call. -/
  hits : Nat

/-- The call quota of the source allows one more call after `n` calls. -/
def quotaOk (s : Source) (n : Nat) : Bool :=
  match s.cap.cost.callQuota with
  | some q => decide (n < q)
  | none   => true

/-- The row quota of the source allows `m` more tuples after `n`. -/
def rowQuotaOk (s : Source) (n m : Nat) : Bool :=
  match s.cap.cost.rowQuota with
  | some q => decide (n + m ≤ q)
  | none   => true

/-- Count one more call of source `i`. -/
def bump (f : Nat → Nat) (i : Nat) : Nat → Nat :=
  fun j => if j = i then f j + 1 else f j

/-- Add `n` to the count of source `i`. -/
def addAt (f : Nat → Nat) (i n : Nat) : Nat → Nat :=
  fun j => if j = i then f j + n else f j

/-- The cache entry of a call of source `i` with input `inp`. -/
def cacheFind (cache : List CacheEntry) (i : Nat) (inp : InputBinding) : Option CacheEntry :=
  cache.find? (fun e => decide (e.src = i) && decide (e.inp = inp))

def finalRow (req : Requirement) (x : Row) : Row :=
  { binding := projectBinding req.projection x.binding, approx := x.approx }

/-- The requirement's filters and projection over the rows of the last
access (the same filters and projection as `Rewriting.toPlan`). -/
def finalRows (req : Requirement) (rows : List Row) : List Row :=
  (rows.filter (fun x => req.filters.all (fun f => f.test x.binding))).map (finalRow req)

def initState (rw : Rewriting) (alts : List Rewriting) : State where
  plan := rw
  alts := alts
  step := 0
  pending := [row0]
  next := []
  phase := .idle
  retries := 0
  calls := fun _ => 0
  output := []
  status := .running
  switches := 0
  answered := fun _ => 0
  rows := fun _ => 0
  latency := fun _ => 0
  cache := []
  hits := 0

/-! ## Init, the actions and Next -/

/-- The run starts with the first plan of the family; the others are
the alternatives. -/
def Init (fam : List Rewriting) (st : State) : Prop :=
  ∃ rw alts, fam = rw :: alts ∧ st = initState rw alts

def Call (cat : Catalog) (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .idle ∧
  ∃ x rest a s inp, st.pending = x :: rest ∧ st.plan.steps[st.step]? = some a ∧
    cat[a.src]? = some s ∧ a.inputs? s.cap x.binding = some inp ∧
    quotaOk s (st.calls a.src) = true ∧
    st' = { st with phase := .waiting, calls := bump st.calls a.src }

/-- The call answers with the tuples of the source's implementation, if
they are within the row quota. The rows they give (`accessRows`, the
access case of `Plan.exec`) are added to `next`; the observed-cost record
and the cache are updated; `lat` is the call's latency (the environment
chooses it). -/
def Receive (cat : Catalog) (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .waiting ∧
  ∃ x rest a s inp lat, st.pending = x :: rest ∧ st.plan.steps[st.step]? = some a ∧
    cat[a.src]? = some s ∧ a.inputs? s.cap x.binding = some inp ∧
    rowQuotaOk s (st.rows a.src) (s.sem.impl inp).length = true ∧
    st' = { st with phase := .idle, pending := rest,
                    next := st.next ++ accessRows s a x (s.sem.impl inp), retries := 0,
                    answered := bump st.answered a.src,
                    rows := addAt st.rows a.src (s.sem.impl inp).length,
                    latency := addAt st.latency a.src lat,
                    cache := ⟨a.src, inp, s.sem.impl inp⟩ :: st.cache }

/-- The head pending row's call is in the cache: its rows are added to
`next` with no call. -/
def Hit (cat : Catalog) (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .idle ∧
  ∃ x rest a s inp e, st.pending = x :: rest ∧ st.plan.steps[st.step]? = some a ∧
    cat[a.src]? = some s ∧ a.inputs? s.cap x.binding = some inp ∧
    e ∈ st.cache ∧ e.src = a.src ∧ e.inp = inp ∧
    st' = { st with pending := rest, next := st.next ++ accessRows s a x e.tuples,
                    hits := st.hits + 1 }

def Fail (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .waiting ∧ st' = { st with phase := .failed }

def Retry (cat : Catalog) (cfg : Config) (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .failed ∧ st.retries < cfg.maxRetries ∧
  ∃ x rest a s, st.pending = x :: rest ∧ st.plan.steps[st.step]? = some a ∧
    cat[a.src]? = some s ∧ quotaOk s (st.calls a.src) = true ∧
    st' = { st with phase := .waiting, retries := st.retries + 1,
                    calls := bump st.calls a.src }

def Advance (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .idle ∧ st.pending = [] ∧
  st.step < st.plan.steps.length ∧
  st' = { st with step := st.step + 1, pending := st.next, next := [] }

def Adapt (st st' : State) : Prop :=
  st.status = .running ∧
  ∃ rw ∈ st.alts,
    st' = { st with plan := rw, alts := st.alts.erase rw, step := 0, pending := [row0],
                    next := [], phase := .idle, retries := 0, switches := st.switches + 1 }

def Finish (req : Requirement) (st st' : State) : Prop :=
  st.status = .running ∧ st.phase = .idle ∧ st.plan.steps.length ≤ st.step ∧
  st' = { st with output := finalRows req st.pending, status := .done }

def Stop (st st' : State) : Prop :=
  st.status = .running ∧ st' = { st with status := .stopped }

/-- The next-state relation: the disjunction of the actions. -/
def Next (cat : Catalog) (req : Requirement) (cfg : Config) (st st' : State) : Prop :=
  Call cat st st' ∨ Receive cat st st' ∨ Fail st st' ∨ Retry cat cfg st st' ∨
  Advance st st' ∨ Adapt st st' ∨ Finish req st st' ∨ Stop st st' ∨ Hit cat st st'

/-- The states that a trace from `Init` by `Next` reaches. -/
inductive Reachable (cat : Catalog) (req : Requirement) (cfg : Config) (fam : List Rewriting) :
    State → Prop where
  | init {st : State} : Init fam st → Reachable cat req cfg fam st
  | step {st st' : State} : Reachable cat req cfg fam st → Next cat req cfg st st' →
      Reachable cat req cfg fam st'

/-! ## The inductive invariant -/

/-- A call in flight (phase `waiting` or `failed`) is a call of the
current access for the head pending row, with every required input
bound. -/
def InflightOk (cat : Catalog) (st : State) : Prop :=
  st.phase ≠ .idle → ∃ x rest a s inp, st.pending = x :: rest ∧
    st.plan.steps[st.step]? = some a ∧ cat[a.src]? = some s ∧ a.inputs? s.cap x.binding = some inp

/-- The rows of the plan prefix before the current access are the rows
already processed (`P`) followed by `pending`, and `next` is what the
access gave for `P`. After the last access, `pending` is the whole run of
the access chain. -/
def Frontier (cat : Catalog) (st : State) : Prop :=
  ∃ P : List Row, (chainPlan (st.plan.steps.take st.step)).run cat = P ++ st.pending ∧
    (∀ a, st.plan.steps[st.step]? = some a →
      st.next = P.flatMap (fun y => (Plan.access a).exec cat y)) ∧
    (st.plan.steps[st.step]? = none → P = [] ∧ st.next = [])

structure Inv (cat : Catalog) (req : Requirement) (cfg : Config) (fam : List Rewriting)
    (st : State) : Prop where
  plan_mem : st.plan ∈ fam
  alts_sub : ∀ rw ∈ st.alts, rw ∈ fam
  frontier : Frontier cat st
  output_done : st.status = .done → st.output = (st.plan.toPlan req).run cat
  output_nil : st.status ≠ .done → st.output = []
  quota : ∀ i s q, cat[i]? = some s → s.cap.cost.callQuota = some q → st.calls i ≤ q
  rowQuota : ∀ i s q, cat[i]? = some s → s.cap.cost.rowQuota = some q → st.rows i ≤ q
  retries_le : st.retries ≤ cfg.maxRetries
  inflight : InflightOk cat st
  /-- Every cache entry is the answer of the call it records. -/
  cacheOk : ∀ e ∈ st.cache, ∃ s, cat[e.src]? = some s ∧ e.tuples = s.sem.impl e.inp

/-! ## Lemmas about the plan -/

theorem chainPlan_snoc_exec (cat : Catalog) (a : Access) :
    ∀ (l : List Access) (r : Row),
      (chainPlan (l ++ [a])).exec cat r =
        ((chainPlan l).exec cat r).flatMap (fun y => (Plan.access a).exec cat y)
  | [], r => by
    simp [chainPlan, Plan.exec]
  | b :: l, r => by
    have ih := chainPlan_snoc_exec cat a l
    show ((Plan.access b).exec cat r).flatMap (fun y => (chainPlan (l ++ [a])).exec cat y) =
      (((Plan.access b).exec cat r).flatMap (fun y => (chainPlan l).exec cat y)).flatMap
        (fun y => (Plan.access a).exec cat y)
    simp only [ih, List.flatMap_assoc]

theorem chain_take_succ_run (cat : Catalog) {steps : List Access} {i : Nat} {a : Access}
    (h : steps[i]? = some a) :
    (chainPlan (steps.take (i + 1))).run cat =
      ((chainPlan (steps.take i)).run cat).flatMap (fun y => (Plan.access a).exec cat y) := by
  rw [List.take_add_one, h]
  exact chainPlan_snoc_exec cat a _ _

theorem filtersPlan_exec_eq (cat : Catalog) :
    ∀ (fs : List RowFilter) (p : Plan) (r : Row),
      (filtersPlan fs p).exec cat r =
        (p.exec cat r).filter (fun x => fs.all (fun f => f.test x.binding))
  | [], p, r => by
    simp only [filtersPlan, List.foldr, List.all_nil]
    exact (List.filter_eq_self.mpr (fun _ _ => rfl)).symm
  | f :: fs, p, r => by
    have ih := filtersPlan_exec_eq cat fs p r
    show ((filtersPlan fs p).exec cat r).filter (fun x => f.test x.binding) = _
    rw [ih, List.filter_filter]
    simp only [List.all_cons]

/-- The run of a rewriting's plan is the filters and the projection over
the run of its access chain. -/
theorem toPlan_run_eq (cat : Catalog) (req : Requirement) (rw : Rewriting) :
    (rw.toPlan req).run cat = finalRows req ((chainPlan rw.steps).run cat) := by
  simp only [Rewriting.toPlan, Plan.run, Plan.exec, filtersPlan_exec_eq, finalRows]
  rfl

/-! ## Init → Inv -/

theorem initState_frontier (cat : Catalog) (rw : Rewriting) (alts : List Rewriting) :
    Frontier cat (initState rw alts) := by
  refine ⟨[], ?_, ?_, ?_⟩
  · simp [initState, chainPlan, Plan.run, Plan.exec, row0]
  · intro a _; simp [initState]
  · intro _; simp [initState]

theorem init_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st : State} (h : Init fam st) : Inv cat req cfg fam st := by
  obtain ⟨rw, alts, hfam, rfl⟩ := h
  subst hfam
  exact {
    plan_mem := List.mem_cons_self
    alts_sub := fun r hr => List.mem_cons_of_mem _ hr
    frontier := initState_frontier cat rw alts
    output_done := by intro h; cases h
    output_nil := fun _ => rfl
    quota := fun _ _ _ _ _ => Nat.zero_le _
    rowQuota := fun _ _ _ _ _ => Nat.zero_le _
    cacheOk := by intro e he; cases he
    retries_le := Nat.zero_le _
    inflight := by intro h; exact absurd rfl h }

/-! ## Inv ∧ Next → Inv' -/

theorem quota_bump {cat : Catalog} {calls : Nat → Nat} {i0 : Nat} {s0 : Source}
    (hq : ∀ i s q, cat[i]? = some s → s.cap.cost.callQuota = some q → calls i ≤ q)
    (hs0 : cat[i0]? = some s0) (hok : quotaOk s0 (calls i0) = true) :
    ∀ i s q, cat[i]? = some s → s.cap.cost.callQuota = some q → bump calls i0 i ≤ q := by
  intro i s q hs hcq
  unfold bump
  by_cases hi : i = i0
  · subst hi
    rw [hs0] at hs
    cases hs
    simp only [if_true]
    unfold quotaOk at hok
    rw [hcq] at hok
    have := of_decide_eq_true hok
    omega
  · simp only [hi, if_false]
    exact hq i s q hs hcq

theorem call_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Call cat st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨hrun, _, x, rest, a, s, inp, hpend, hstep, hs, hinp, hok, rfl⟩ := h
  exact {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hi.frontier
    output_done := hi.output_done
    output_nil := hi.output_nil
    quota := quota_bump hi.quota hs hok
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hi.retries_le
    inflight := fun _ => ⟨x, rest, a, s, inp, hpend, hstep, hs, hinp⟩ }

theorem rowQuota_add {cat : Catalog} {rows : Nat → Nat} {i0 n : Nat} {s0 : Source}
    (hq : ∀ i s q, cat[i]? = some s → s.cap.cost.rowQuota = some q → rows i ≤ q)
    (hs0 : cat[i0]? = some s0) (hok : rowQuotaOk s0 (rows i0) n = true) :
    ∀ i s q, cat[i]? = some s → s.cap.cost.rowQuota = some q → addAt rows i0 n i ≤ q := by
  intro i s q hs hcq
  unfold addAt
  by_cases hi : i = i0
  · subst hi
    rw [hs0] at hs
    cases hs
    simp only [if_true]
    unfold rowQuotaOk at hok
    rw [hcq] at hok
    exact of_decide_eq_true hok
  · simp only [hi, if_false]
    exact hq i s q hs hcq

/-- The access case of `Plan.exec` is `accessRows` over the source's
implementation. -/
theorem exec_access_of {cat : Catalog} {a : Access} {s : Source} {inp : InputBinding} {x : Row}
    (hs : cat[a.src]? = some s) (hinp : a.inputs? s.cap x.binding = some inp) :
    (Plan.access a).exec cat x = accessRows s a x (s.sem.impl inp) := by
  rw [exec_access_eq]
  simp only [hs, hinp]

/-- A cache entry for the call of access `a` on row `x` gives the rows
that `Plan.exec` gives for that access and row. -/
theorem cache_rows_eq {cat : Catalog} {cache : List CacheEntry}
    (hc : ∀ e ∈ cache, ∃ s, cat[e.src]? = some s ∧ e.tuples = s.sem.impl e.inp)
    {e : CacheEntry} {a : Access} {s : Source} {inp : InputBinding} {x : Row}
    (he : e ∈ cache) (hsrc : e.src = a.src) (hinpe : e.inp = inp)
    (hs : cat[a.src]? = some s) (hinp : a.inputs? s.cap x.binding = some inp) :
    accessRows s a x e.tuples = (Plan.access a).exec cat x := by
  obtain ⟨s', hs', ht⟩ := hc e he
  rw [hsrc, hs] at hs'
  cases hs'
  rw [ht, hinpe, exec_access_of hs hinp]

/-- `Receive` and `Hit` add to `next` the rows of the access for the head
pending row. -/
theorem frontier_pop {cat : Catalog} {st : State} {x : Row} {rest : List Row} {a : Access}
    (hf : Frontier cat st) (hpend : st.pending = x :: rest) (hstep : st.plan.steps[st.step]? = some a)
    (rows : List Row) (hrows : rows = (Plan.access a).exec cat x) :
    Frontier cat { st with pending := rest, next := st.next ++ rows } := by
  obtain ⟨P, hP, hnext, _⟩ := hf
  have hn := hnext a hstep
  refine ⟨P ++ [x], ?_, ?_, ?_⟩
  · show (chainPlan (st.plan.steps.take st.step)).run cat = (P ++ [x]) ++ rest
    rw [hP, hpend]; simp
  · intro a' ha'
    show st.next ++ rows = _
    have haa : a' = a := by
      have : (some a' : Option Access) = some a := ha'.symm.trans hstep
      exact Option.some.inj this
    subst haa
    rw [hn, hrows]; simp
  · intro hnone
    exact absurd (hnone.symm.trans hstep) (by simp)

theorem receive_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Receive cat st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨hrun, _, x, rest, a, s, inp, lat, hpend, hstep, hs, hinp, hrq, rfl⟩ := h
  have hfr := frontier_pop hi.frontier hpend hstep _ (exec_access_of hs hinp).symm
  exact {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hfr
    output_done := hi.output_done
    output_nil := hi.output_nil
    quota := hi.quota
    rowQuota := rowQuota_add hi.rowQuota hs hrq
    cacheOk := by
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨s, hs, rfl⟩
      · exact hi.cacheOk e he
    retries_le := Nat.zero_le _
    inflight := by intro h; exact absurd rfl h }

theorem hit_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Hit cat st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨_, hidle, x, rest, a, s, inp, e, hpend, hstep, hs, hinp, he, hsrc, hinpe, rfl⟩ := h
  have hfr := frontier_pop hi.frontier hpend hstep _
    (cache_rows_eq hi.cacheOk he hsrc hinpe hs hinp)
  exact {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hfr
    output_done := hi.output_done
    output_nil := hi.output_nil
    quota := hi.quota
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hi.retries_le
    inflight := by intro h; exact absurd hidle h }

theorem fail_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Fail st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨_, hw, rfl⟩ := h
  exact {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hi.frontier
    output_done := hi.output_done
    output_nil := hi.output_nil
    quota := hi.quota
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hi.retries_le
    inflight := fun _ => hi.inflight (by rw [hw]; exact fun h => Phase.noConfusion h) }

theorem retry_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Retry cat cfg st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨_, hf, hr, x, rest, a, s, hpend, hstep, hs, hok, rfl⟩ := h
  exact {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hi.frontier
    output_done := hi.output_done
    output_nil := hi.output_nil
    quota := quota_bump hi.quota hs hok
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hr
    inflight := fun _ => hi.inflight (by rw [hf]; exact fun h => Phase.noConfusion h) }

theorem advance_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Advance st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨_, hidle, hpend, hlt, rfl⟩ := h
  obtain ⟨P, hP, hnext, _⟩ := hi.frontier
  obtain ⟨a, ha⟩ : ∃ a, st.plan.steps[st.step]? = some a :=
    ⟨st.plan.steps[st.step], List.getElem?_eq_getElem hlt⟩
  have hn := hnext a ha
  rw [hpend, List.append_nil] at hP
  refine {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := ?_
    output_done := hi.output_done
    output_nil := hi.output_nil
    quota := hi.quota
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hi.retries_le
    inflight := by intro h; exact absurd hidle h }
  refine ⟨[], ?_, ?_, ?_⟩
  · show (chainPlan (st.plan.steps.take (st.step + 1))).run cat = [] ++ st.next
    rw [chain_take_succ_run cat ha, hP, hn, List.nil_append]
  · intro _ _; rfl
  · intro _; exact ⟨rfl, rfl⟩

theorem adapt_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Adapt st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨hrun, rw, hrw, rfl⟩ := h
  have hnd : st.status ≠ .done := by rw [hrun]; exact fun h => Status.noConfusion h
  refine {
    plan_mem := hi.alts_sub rw hrw
    alts_sub := fun r hr => hi.alts_sub r (List.mem_of_mem_erase hr)
    frontier := ?_
    output_done := fun h => absurd h hnd
    output_nil := fun _ => hi.output_nil hnd
    quota := hi.quota
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := Nat.zero_le _
    inflight := by intro h; exact absurd rfl h }
  refine ⟨[], ?_, ?_, ?_⟩
  · show (chainPlan (rw.steps.take 0)).run cat = [] ++ [row0]
    simp [chainPlan, Plan.run, Plan.exec, row0]
  · intro _ _; rfl
  · intro _; exact ⟨rfl, rfl⟩

theorem finish_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Finish req st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨_, hidle, hle, rfl⟩ := h
  obtain ⟨P, hP, _, hnone⟩ := hi.frontier
  have hP0 := (hnone (List.getElem?_eq_none hle)).1
  rw [hP0, List.nil_append, List.take_of_length_le hle] at hP
  refine {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hi.frontier
    output_done := ?_
    output_nil := fun h => absurd rfl h
    quota := hi.quota
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hi.retries_le
    inflight := hi.inflight }
  intro _
  show finalRows req st.pending = (st.plan.toPlan req).run cat
  rw [toPlan_run_eq, hP]

theorem stop_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Stop st st') :
    Inv cat req cfg fam st' := by
  obtain ⟨hrun, rfl⟩ := h
  have hnd : st.status ≠ .done := by rw [hrun]; exact fun h => Status.noConfusion h
  exact {
    plan_mem := hi.plan_mem
    alts_sub := hi.alts_sub
    frontier := hi.frontier
    output_done := fun h => Status.noConfusion h
    output_nil := fun _ => hi.output_nil hnd
    quota := hi.quota
    rowQuota := hi.rowQuota
    cacheOk := hi.cacheOk
    retries_le := hi.retries_le
    inflight := hi.inflight }

/-- `Next` keeps the invariant. -/
theorem next_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st st' : State} (hi : Inv cat req cfg fam st) (h : Next cat req cfg st st') :
    Inv cat req cfg fam st' := by
  rcases h with h | h | h | h | h | h | h | h | h
  · exact call_inv hi h
  · exact receive_inv hi h
  · exact fail_inv hi h
  · exact retry_inv hi h
  · exact advance_inv hi h
  · exact adapt_inv hi h
  · exact finish_inv hi h
  · exact stop_inv hi h
  · exact hit_inv hi h

/-- Every reachable state satisfies the invariant (induction on traces). -/
theorem reachable_inv {cat : Catalog} {req : Requirement} {cfg : Config} {fam : List Rewriting}
    {st : State} (h : Reachable cat req cfg fam st) : Inv cat req cfg fam st := by
  induction h with
  | init hinit => exact init_inv hinit
  | step _ hnext ih => exact next_inv ih hnext

/-! ## The invariants I1 and I2 -/

/-- (I1) No unmarked output row is outside the requirement's answers
over the declared graph. -/
theorem reachable_sound {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State}
    (hsound : ExactSourcesSound cat) (hfam : ∀ rw ∈ fam, rw.check cat req = true)
    (h : Reachable cat req cfg fam st) :
    ∀ x ∈ st.output, x.approx = false →
      ∃ ρ ∈ req.answers (declaredGraph cat), SolEquiv x.binding ρ := by
  intro x hx happ
  have hi := reachable_inv h
  by_cases hd : st.status = .done
  · rw [hi.output_done hd] at hx
    exact rewriting_sound hsound ⟨st.plan, hfam _ hi.plan_mem, rfl⟩ x hx happ
  · rw [hi.output_nil hd] at hx
    cases hx

/-- (I2) No source's call count exceeds its call quota. -/
theorem reachable_quota {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State} (h : Reachable cat req cfg fam st) :
    ∀ i s q, cat[i]? = some s → s.cap.cost.callQuota = some q → st.calls i ≤ q :=
  (reachable_inv h).quota

/-- (I2, rows) No source returns more tuples than its row quota. -/
theorem reachable_rowQuota {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State} (h : Reachable cat req cfg fam st) :
    ∀ i s q, cat[i]? = some s → s.cap.cost.rowQuota = some q → st.rows i ≤ q :=
  (reachable_inv h).rowQuota

/-- Every cache entry of a reachable state is the call's result: the
tuples of the source's implementation for the recorded input. -/
theorem reachable_cache {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State} (h : Reachable cat req cfg fam st) :
    ∀ e ∈ st.cache, ∃ s, cat[e.src]? = some s ∧ e.tuples = s.sem.impl e.inp :=
  (reachable_inv h).cacheOk

/-- The cache never changes an answer: in a reachable state, the rows
that a cache entry gives for access `a` on row `x` are the rows that
`Plan.exec` gives (the rows of the call). -/
theorem reachable_cache_hit {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State} (h : Reachable cat req cfg fam st)
    {e : CacheEntry} {a : Access} {s : Source} {inp : InputBinding} {x : Row}
    (he : e ∈ st.cache) (hsrc : e.src = a.src) (hinpe : e.inp = inp)
    (hs : cat[a.src]? = some s) (hinp : a.inputs? s.cap x.binding = some inp) :
    accessRows s a x e.tuples = (Plan.access a).exec cat x :=
  cache_rows_eq (reachable_cache h) he hsrc hinpe hs hinp

/-- When the status is `done`, the output is the run of the current plan,
and the current plan is a member of the family. -/
theorem reachable_output {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State} (h : Reachable cat req cfg fam st)
    (hd : st.status = .done) :
    st.plan ∈ fam ∧ st.output = (st.plan.toPlan req).run cat :=
  ⟨(reachable_inv h).plan_mem, (reachable_inv h).output_done hd⟩

/-- With only exact sources, no output row is marked. -/
theorem reachable_unmarked_of_allExact {cat : Catalog} {req : Requirement} {cfg : Config}
    {fam : List Rewriting} {st : State}
    (hex : ∀ s ∈ cat, s.cap.exactness = .exact) (h : Reachable cat req cfg fam st) :
    ∀ x ∈ st.output, x.approx = false := by
  intro x hx
  have hi := reachable_inv h
  by_cases hd : st.status = .done
  · rw [hi.output_done hd] at hx
    exact run_unmarked_of_allExact hex _ x hx
  · rw [hi.output_nil hd] at hx
    cases hx

/-! ## Termination: every action decreases a measure -/

def statusRank : Status → Nat
  | .running => 1
  | _        => 0

def phaseRank : Phase → Nat
  | .idle    => 2
  | .waiting => 1
  | .failed  => 0

/-- The measure, compared lexicographically: running before terminal,
the alternatives left, the accesses left, the pending rows, the retries
left, the phase. -/
def measure (cfg : Config) (st : State) : Nat × Nat × Nat × Nat × Nat × Nat :=
  (statusRank st.status, st.alts.length, st.plan.steps.length - st.step, st.pending.length,
   cfg.maxRetries - st.retries, phaseRank st.phase)

/-- The lexicographic order on the measure (the `WellFoundedRelation` of
the product type). -/
abbrev MeasureLt (m m' : Nat × Nat × Nat × Nat × Nat × Nat) : Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·) (Prod.Lex (· < ·)
    (Prod.Lex (· < ·) (· < ·))))) m m'

theorem next_measure_lt {cat : Catalog} {req : Requirement} {cfg : Config} {st st' : State}
    (h : Next cat req cfg st st') : MeasureLt (measure cfg st') (measure cfg st) := by
  rcases h with h | h | h | h | h | h | h | h | h
  · -- Call: the phase goes from idle to waiting
    obtain ⟨_, hidle, -, -, -, -, -, -, -, -, -, -, rfl⟩ := h
    simp only [measure, hidle]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _
      (Prod.Lex.right _ (by simp [phaseRank])))))
  · -- Receive: one pending row less
    obtain ⟨_, _, x, rest, a, -, -, -, hpend, -, -, -, -, rfl⟩ := h
    simp only [measure, hpend]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _
      (by simp))))
  · -- Fail: the phase goes from waiting to failed
    obtain ⟨_, hw, rfl⟩ := h
    simp only [measure, hw]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _
      (Prod.Lex.right _ (by simp [phaseRank])))))
  · -- Retry: one retry less
    obtain ⟨_, _, hr, -, -, -, -, -, -, -, -, rfl⟩ := h
    simp only [measure]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _
      (Prod.Lex.left _ _ (by omega)))))
  · -- Advance: one access less
    obtain ⟨_, _, _, hlt, rfl⟩ := h
    simp only [measure]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ (by omega)))
  · -- Adapt: one alternative less
    obtain ⟨_, rw, hrw, rfl⟩ := h
    simp only [measure]
    have hlen := List.length_erase_of_mem hrw
    have hpos : 0 < st.alts.length := List.length_pos_of_mem hrw
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))
  · -- Finish: the status leaves running
    obtain ⟨hrun, _, _, rfl⟩ := h
    simp only [measure, hrun]
    exact Prod.Lex.left _ _ (by simp [statusRank])
  · -- Stop: the status leaves running
    obtain ⟨hrun, rfl⟩ := h
    simp only [measure, hrun]
    exact Prod.Lex.left _ _ (by simp [statusRank])
  · -- Hit: one pending row less
    obtain ⟨_, _, x, rest, a, -, -, -, hpend, -, -, -, -, -, -, rfl⟩ := h
    simp only [measure, hpend]
    exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _
      (by simp))))

/-- The relation "one step of `Next` back" is well-founded: the state
machine has no infinite trace. -/
theorem next_wf (cat : Catalog) (req : Requirement) (cfg : Config) :
    WellFounded (fun st' st => Next cat req cfg st st') :=
  Subrelation.wf (fun h => next_measure_lt h)
    (InvImage.wf (measure cfg) (invImage id inferInstance).wf)

/-! ## The executable driver

A deterministic choice among the enabled actions. The environment's
failures come from a fault schedule: `faults i n` is `true` when call
number `n` (counted from 1) of source `i` fails; its latencies from
`lat i n`. When the head pending row's call is in the cache, the driver
takes `Hit` (no call). When the current call cannot be made (an input is
unbound, the call quota is exhausted, the retries are used up) or its
answer is over the row quota, the driver switches to the alternative of
least score (`adaptScore`, from the observed-cost record), or stops when
none is left. -/

abbrev Faults := Nat → Nat → Bool

def noFaults : Faults := fun _ _ => false

/-- The latency of call `n` of source `i`, in the units of
`CostModel.perCall`. -/
abbrev Latency := Nat → Nat → Nat

def noLatency : Latency := fun _ _ => 0

/-! ### The choice of the next alternative from measured costs -/

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

/-- The measured latency per answered call at a location: over every
source of the catalog with that location. `none` before the first answer
there. -/
def locLatency (cat : Catalog) (st : State) (loc : String) : Option Nat :=
  let acc := (List.range cat.length).foldl (fun (acc : Nat × Nat) i =>
    match cat[i]? with
    | some s => if s.cap.location = loc then (acc.1 + st.latency i, acc.2 + st.answered i) else acc
    | none => acc) (0, 0)
  if acc.2 = 0 then none else some (acc.1 / acc.2)

/-- The estimate model of the run so far: the measured tuples per call of
a source that has answered (its statistic, or the fanout, otherwise); the
measured latency of the source's location as the cost of a call (its
`perCall` before any answer there); and, for an access whose inputs are
all constants, the tuple count of its call when that call is in the
cache (it makes no call), and otherwise one call (the later rows are
cache hits). -/
def obsModel (cat : Catalog) (cfg : Config) (st : State) : EstModel where
  rowsPerCall := fun i s nv =>
    if st.answered i = 0 then s.cap.cost.rowsPerCall.getD (cfg.fanout ^ nv)
    else ceilDiv (st.rows i) (st.answered i)
  callCost := fun _ s => (locLatency cat st s.cap.location).getD s.cap.cost.perCall
  known := fun a =>
    match cat[a.src]? with
    | none => none
    | some s =>
      match a.inputs? s.cap [] with
      | none => none
      | some inp => (cacheFind st.cache a.src inp).map (·.tuples.length)
  cacheScans := true

/-- The score of an alternative: first 0 when its estimated use, added to
the calls and tuples already used, is within every quota, and 1 when it
is not; then its estimated cost. -/
def adaptScore (cat : Catalog) (cfg : Config) (st : State) (rw : Rewriting) : Nat × Nat :=
  let us := estUse cat (obsModel cat cfg st) rw.steps
  (if withinQuotas cat us st.calls st.rows then 0 else 1, totalCost us)

def scoreLt (p q : Nat × Nat) : Bool :=
  decide (p.1 < q.1) || (decide (p.1 = q.1) && decide (p.2 < q.2))

def pickMinGo (f : Rewriting → Nat × Nat) : Rewriting → List Rewriting → Rewriting
  | b, [] => b
  | b, x :: xs => pickMinGo f (if scoreLt (f x) (f b) then x else b) xs

/-- The first alternative of least score; `none` for no alternative. A
loop. -/
def pickMin (f : Rewriting → Nat × Nat) : List Rewriting → Option Rewriting
  | [] => none
  | x :: xs => some (pickMinGo f x xs)

theorem pickMinGo_mem (f : Rewriting → Nat × Nat) :
    ∀ (b : Rewriting) (l : List Rewriting), pickMinGo f b l ∈ b :: l
  | b, [] => List.mem_cons_self
  | b, x :: xs => by
    show pickMinGo f (if scoreLt (f x) (f b) then x else b) xs ∈ b :: x :: xs
    rcases List.mem_cons.mp (pickMinGo_mem f (if scoreLt (f x) (f b) then x else b) xs) with h | h
    · rw [h]
      split
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ h)

theorem pickMin_mem {f : Rewriting → Nat × Nat} {l : List Rewriting} {rw : Rewriting}
    (h : pickMin f l = some rw) : rw ∈ l := by
  cases l with
  | nil => cases h
  | cons x xs =>
    simp only [pickMin, Option.some.injEq] at h
    rw [← h]
    exact pickMinGo_mem f x xs

theorem cacheFind_some {cache : List CacheEntry} {i : Nat} {inp : InputBinding} {e : CacheEntry}
    (h : cacheFind cache i inp = some e) : e ∈ cache ∧ e.src = i ∧ e.inp = inp := by
  unfold cacheFind at h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp.1, hp.2⟩

/-! ### The steps -/

def adaptOrStop (cat : Catalog) (cfg : Config) (st : State) : State :=
  match pickMin (adaptScore cat cfg st) st.alts with
  | some rw =>
    { st with plan := rw, alts := st.alts.erase rw, step := 0, pending := [row0], next := [],
              phase := .idle, retries := 0, switches := st.switches + 1 }
  | none => { st with status := .stopped }

def stepIdle (cat : Catalog) (req : Requirement) (cfg : Config) (st : State) : State :=
  if st.plan.steps.length ≤ st.step then
    { st with output := finalRows req st.pending, status := .done }
  else
    match st.pending with
    | [] => { st with step := st.step + 1, pending := st.next, next := [] }
    | x :: rest =>
      match st.plan.steps[st.step]? with
      | none => adaptOrStop cat cfg st
      | some a =>
        match cat[a.src]? with
        | none => adaptOrStop cat cfg st
        | some s =>
          match a.inputs? s.cap x.binding with
          | none => adaptOrStop cat cfg st
          | some inp =>
            match cacheFind st.cache a.src inp with
            | some e =>
              { st with pending := rest, next := st.next ++ accessRows s a x e.tuples,
                        hits := st.hits + 1 }
            | none =>
              if quotaOk s (st.calls a.src) then
                { st with phase := .waiting, calls := bump st.calls a.src }
              else adaptOrStop cat cfg st

def stepWaiting (cat : Catalog) (cfg : Config) (faults : Faults) (lat : Latency) (st : State) :
    State :=
  match st.pending, st.plan.steps[st.step]? with
  | x :: rest, some a =>
    if faults a.src (st.calls a.src) then { st with phase := .failed }
    else
      match cat[a.src]? with
      | none => { st with phase := .failed }
      | some s =>
        match a.inputs? s.cap x.binding with
        | none => { st with phase := .failed }
        | some inp =>
          if rowQuotaOk s (st.rows a.src) (s.sem.impl inp).length then
            { st with phase := .idle, pending := rest,
                      next := st.next ++ accessRows s a x (s.sem.impl inp), retries := 0,
                      answered := bump st.answered a.src,
                      rows := addAt st.rows a.src (s.sem.impl inp).length,
                      latency := addAt st.latency a.src (lat a.src (st.calls a.src)),
                      cache := ⟨a.src, inp, s.sem.impl inp⟩ :: st.cache }
          else adaptOrStop cat cfg st
  | _, _ => { st with phase := .failed }

def stepFailed (cat : Catalog) (cfg : Config) (st : State) : State :=
  match st.pending, st.plan.steps[st.step]? with
  | _ :: _, some a =>
    match cat[a.src]? with
    | some s =>
      if decide (st.retries < cfg.maxRetries) && quotaOk s (st.calls a.src) then
        { st with phase := .waiting, retries := st.retries + 1, calls := bump st.calls a.src }
      else adaptOrStop cat cfg st
    | none => adaptOrStop cat cfg st
  | _, _ => adaptOrStop cat cfg st

/-- One step of the driver; `none` when the status is not `running`. -/
def stepExec (cat : Catalog) (req : Requirement) (cfg : Config) (faults : Faults) (lat : Latency)
    (st : State) : Option State :=
  match st.status with
  | .running =>
    match st.phase with
    | .idle    => some (stepIdle cat req cfg st)
    | .waiting => some (stepWaiting cat cfg faults lat st)
    | .failed  => some (stepFailed cat cfg st)
  | _ => none

theorem adaptOrStop_next {cat : Catalog} {req : Requirement} {cfg : Config} {st : State}
    (hrun : st.status = .running) : Next cat req cfg st (adaptOrStop cat cfg st) := by
  unfold adaptOrStop
  split
  · rename_i rw hpick
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hrun, rw, pickMin_mem hpick, rfl⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hrun, rfl⟩)))))))

theorem stepIdle_next {cat : Catalog} {req : Requirement} {cfg : Config} {st : State}
    (hrun : st.status = .running) (hidle : st.phase = .idle) :
    Next cat req cfg st (stepIdle cat req cfg st) := by
  unfold stepIdle
  split
  · rename_i hle
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hrun, hidle, hle, rfl⟩))))))
  · rename_i hlt
    split
    · rename_i hpend
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hrun, hidle, hpend, by omega, rfl⟩))))
    · rename_i x rest hpend
      split
      · exact adaptOrStop_next hrun
      · rename_i a hstep
        split
        · exact adaptOrStop_next hrun
        · rename_i s hs
          split
          · exact adaptOrStop_next hrun
          · rename_i inp hinp
            split
            · rename_i e he
              obtain ⟨hmem, hsrc, hinpe⟩ := cacheFind_some he
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                ⟨hrun, hidle, x, rest, a, s, inp, e, hpend, hstep, hs, hinp, hmem, hsrc, hinpe,
                 rfl⟩)))))))
            · split
              · rename_i hq
                exact Or.inl ⟨hrun, hidle, x, rest, a, s, inp, hpend, hstep, hs, hinp, hq, rfl⟩
              · exact adaptOrStop_next hrun

theorem stepWaiting_next {cat : Catalog} {req : Requirement} {cfg : Config} {faults : Faults}
    {lat : Latency} {st : State} (hrun : st.status = .running) (hw : st.phase = .waiting) :
    Next cat req cfg st (stepWaiting cat cfg faults lat st) := by
  unfold stepWaiting
  split
  · rename_i x rest a hpend hstep
    split
    · exact Or.inr (Or.inr (Or.inl ⟨hrun, hw, rfl⟩))
    · split
      · exact Or.inr (Or.inr (Or.inl ⟨hrun, hw, rfl⟩))
      · rename_i s hs
        split
        · exact Or.inr (Or.inr (Or.inl ⟨hrun, hw, rfl⟩))
        · rename_i inp hinp
          split
          · rename_i hrq
            exact Or.inr (Or.inl ⟨hrun, hw, x, rest, a, s, inp, lat a.src (st.calls a.src),
              hpend, hstep, hs, hinp, hrq, rfl⟩)
          · exact adaptOrStop_next hrun
  · exact Or.inr (Or.inr (Or.inl ⟨hrun, hw, rfl⟩))

theorem stepFailed_next {cat : Catalog} {req : Requirement} {cfg : Config} {st : State}
    (hrun : st.status = .running) (hf : st.phase = .failed) :
    Next cat req cfg st (stepFailed cat cfg st) := by
  unfold stepFailed
  split
  · rename_i x rest a hpend hstep
    split
    · rename_i s hs
      split
      · rename_i hok
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        exact Or.inr (Or.inr (Or.inr (Or.inl
          ⟨hrun, hf, hok.1, x, rest, a, s, hpend, hstep, hs, hok.2, rfl⟩)))
      · exact adaptOrStop_next hrun
    · exact adaptOrStop_next hrun
  · exact adaptOrStop_next hrun

/-- Each step of the driver is a step of `Next`. -/
theorem stepExec_next {cat : Catalog} {req : Requirement} {cfg : Config} {faults : Faults}
    {lat : Latency} {st st' : State} (h : stepExec cat req cfg faults lat st = some st') :
    Next cat req cfg st st' := by
  unfold stepExec at h
  split at h
  · rename_i hrun
    split at h
    · rename_i hp; cases h; exact stepIdle_next hrun hp
    · rename_i hp; cases h; exact stepWaiting_next hrun hp
    · rename_i hp; cases h; exact stepFailed_next hrun hp
  · cases h

/-- The driver stops only when the status is not `running`. -/
theorem stepExec_none {cat : Catalog} {req : Requirement} {cfg : Config} {faults : Faults}
    {lat : Latency} {st : State} (h : stepExec cat req cfg faults lat st = none) :
    st.status ≠ .running := by
  intro hrun
  cases hp : st.phase <;> simp [stepExec, hrun, hp] at h

/-- Run the driver until no action is chosen. A tail call; it terminates
because every step decreases `measure` (`next_measure_lt`). -/
def runFrom (cat : Catalog) (req : Requirement) (cfg : Config) (faults : Faults) (lat : Latency)
    (st : State) : State :=
  match _hs : stepExec cat req cfg faults lat st with
  | none => st
  | some st' => runFrom cat req cfg faults lat st'
termination_by measure cfg st
decreasing_by exact next_measure_lt (stepExec_next _hs)

theorem runFrom_reachable {cat : Catalog} {req : Requirement} {cfg : Config} {faults : Faults}
    {lat : Latency} {fam : List Rewriting} :
    ∀ st, Reachable cat req cfg fam st →
      Reachable cat req cfg fam (runFrom cat req cfg faults lat st) := by
  intro st
  induction st using (invImage (measure cfg) (inferInstance :
      WellFoundedRelation (Nat × Nat × Nat × Nat × Nat × Nat))).wf.induction with
  | _ st ih =>
    intro hr
    rw [runFrom]
    split
    · exact hr
    · rename_i st' h
      exact ih st' (next_measure_lt (stepExec_next h)) (Reachable.step hr (stepExec_next h))

/-- The driver ends with the status `done` or `stopped`. -/
theorem runFrom_final {cat : Catalog} {req : Requirement} {cfg : Config} {faults : Faults}
    {lat : Latency} :
    ∀ st, (runFrom cat req cfg faults lat st).status ≠ .running := by
  intro st
  induction st using (invImage (measure cfg) (inferInstance :
      WellFoundedRelation (Nat × Nat × Nat × Nat × Nat × Nat))).wf.induction with
  | _ st ih =>
    rw [runFrom]
    split
    · rename_i h; exact stepExec_none h
    · rename_i st' h
      exact ih st' (next_measure_lt (stepExec_next h))

/-! ## A run over the admitted plan family -/

/-- The admitted plan family (`searchAdmitted`), as rewritings. -/
def family (cat : Catalog) (req : Requirement) (k : Nat) (fanout : Nat := 10) : List Rewriting :=
  (searchAdmitted cat req k fanout).map (·.rewriting)

theorem family_check {cat : Catalog} {req : Requirement} {k fanout : Nat} :
    ∀ rw ∈ family cat req k fanout, rw.check cat req = true := by
  intro rw hrw
  simp only [family, List.mem_map] at hrw
  obtain ⟨r, hr, rfl⟩ := hrw
  exact search_check (searchAdmitted_mem hr).1

/-- Run the admitted family of `search cat req k`; `none` when it is
empty (not answerable with at most `k` accesses within the estimated
quotas). -/
def run (cat : Catalog) (req : Requirement) (k : Nat) (cfg : Config) (faults : Faults)
    (lat : Latency := noLatency) : Option State :=
  match family cat req k cfg.fanout with
  | [] => none
  | rw :: alts => some (runFrom cat req cfg faults lat (initState rw alts))

theorem run_reachable {cat : Catalog} {req : Requirement} {k : Nat} {cfg : Config}
    {faults : Faults} {lat : Latency} {st : State} (h : run cat req k cfg faults lat = some st) :
    Reachable cat req cfg (family cat req k cfg.fanout) st := by
  unfold run at h
  split at h
  · cases h
  · rename_i rw alts hfam
    cases h
    exact runFrom_reachable _ (Reachable.init ⟨rw, alts, hfam, rfl⟩)

/-- The results for a run of the driver over the admitted family: it ends
`done` or `stopped`; no call quota and no row quota is exceeded (I2); no
unmarked output row is outside the requirement's answers (I1); every
cache entry is the call's result; and a `done` output is the run of an
admitted member of the family of `search`. -/
theorem run_spec {cat : Catalog} {req : Requirement} {k : Nat} {cfg : Config}
    {faults : Faults} {lat : Latency} {st : State} (hsound : ExactSourcesSound cat)
    (h : run cat req k cfg faults lat = some st) :
    (st.status = .done ∨ st.status = .stopped) ∧
    (∀ i s q, cat[i]? = some s → s.cap.cost.callQuota = some q → st.calls i ≤ q) ∧
    (∀ i s q, cat[i]? = some s → s.cap.cost.rowQuota = some q → st.rows i ≤ q) ∧
    (∀ x ∈ st.output, x.approx = false →
      ∃ ρ ∈ req.answers (declaredGraph cat), SolEquiv x.binding ρ) ∧
    (∀ e ∈ st.cache, ∃ s, cat[e.src]? = some s ∧ e.tuples = s.sem.impl e.inp) ∧
    (st.status = .done → ∃ r ∈ searchAdmitted cat req k cfg.fanout,
      st.output = (r.rewriting.toPlan req).run cat) := by
  have hr := run_reachable h
  have hfinal : st.status ≠ .running := by
    unfold run at h
    split at h
    · cases h
    · cases h; exact runFrom_final _
  refine ⟨?_, reachable_quota hr, reachable_rowQuota hr, reachable_sound hsound family_check hr,
    reachable_cache hr, ?_⟩
  · cases hs : st.status with
    | running => exact absurd hs hfinal
    | done => exact Or.inl rfl
    | stopped => exact Or.inr rfl
  · intro hd
    obtain ⟨hmem, hout⟩ := reachable_output hr hd
    simp only [family, List.mem_map] at hmem
    obtain ⟨r, hr', hrw⟩ := hmem
    exact ⟨r, hr', by rw [hout, hrw]⟩

end L4Factoidal.Planner.Exec
