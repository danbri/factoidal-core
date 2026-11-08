import L4Factoidal.EventLoop.Model
import L4Factoidal.EventLoop.Dispatch

/-!
# Theorems of the event loop model

1. `checkpoint_empties`, `checkpoint_fifo`, `checkpoint_empties_or_fuel`: the
   microtask checkpoint empties the microtask queue, in the order queued.
2. `trace_fired_sorted`: over any sequence of inputs, timers fire in order of
   `(due, seq)`: non-decreasing due time, and equal due times in the order set
   (`seq` is the count of arms before, `setTimer_armed`).
3. `cleared_never_fires`: after `clearTimer id`, no input sequence runs a
   callback of timer `id`.
4. `setTimer_armed` with `clamp_shallow`, `clamp_deep` (in `Timers`): the
   timeout clamp of HTML §8.6.
5. `plan_ordered`, `plan_node`, `plan_no_bubbles`, `afterStop_same_node`:
   dispatch visits capture listeners root first, then the target, then bubble
   listeners target first; `stopPropagation` ends the walk at the next node.
6. `Driver.advanceGo_frames`, `Driver.advanceGo_no_slot`, `Driver.frameSlot_between`,
   `Driver.frameSlot_ne_last`: one advance of a host runs at most one animation frame
   batch, at a frame time between the clock and the target, never twice at one time.
-/
namespace L4Factoidal.EventLoop

/-! ## 1. Microtask checkpoint -/

def Call.isMicro : Call → Bool
  | .queueMicrotask _ => true
  | _ => false

theorem Call.apply_microtasks {c : Call} (h : c.isMicro = false) (st : State) :
    (c.apply st).microtasks = st.microtasks := by
  cases c <;> simp_all [Call.apply, Call.isMicro, State.queueTask, State.setTimer, State.arm,
    State.clearTimer, State.requestFrame, State.cancelFrame]

theorem applyAll_microtasks {calls : List Call} (h : ∀ c ∈ calls, c.isMicro = false) (st : State) :
    (applyAll calls st).microtasks = st.microtasks := by
  induction calls generalizing st with
  | nil => rfl
  | cons c cs ih =>
    show (applyAll cs (c.apply st)).microtasks = st.microtasks
    rw [ih (fun c' h' => h c' (.tail _ h')), Call.apply_microtasks (h c (.head _))]

/-- A checkpoint whose microtasks queue no microtasks, with fuel for the queue,
ends with the queue empty. -/
theorem checkpointGo_empties (effects : Handle → List Call)
    (hE : ∀ m, ∀ c ∈ effects m, c.isMicro = false) :
    ∀ (fuel : Nat) (st : State) (acc : List Handle), st.microtasks.length ≤ fuel →
      (checkpointGo effects fuel st acc).1.microtasks = [] ∧
      (checkpointGo effects fuel st acc).2 = acc.reverse ++ st.microtasks
  | 0, st, acc, h => by
    have : st.microtasks = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [checkpointGo, this]
  | fuel + 1, st, acc, h => by
    unfold checkpointGo
    cases hm : st.microtasks with
    | nil => simp [hm]
    | cons m rest =>
      simp only
      have hlen : (applyAll (effects m) { st with microtasks := rest }).microtasks.length ≤ fuel := by
        rw [applyAll_microtasks (hE m)]; rw [hm] at h; simp at h; simp; omega
      have ih := checkpointGo_empties effects hE fuel _ (m :: acc) hlen
      refine ⟨ih.1, ?_⟩
      rw [ih.2, applyAll_microtasks (hE m)]
      simp

theorem checkpoint_empties (effects : Handle → List Call)
    (hE : ∀ m, ∀ c ∈ effects m, c.isMicro = false) {fuel : Nat} {st : State}
    (h : st.microtasks.length ≤ fuel) : (checkpoint effects fuel st).1.microtasks = [] :=
  (checkpointGo_empties effects hE fuel st [] h).1

/-- The checkpoint runs the microtasks in the order queued. -/
theorem checkpoint_fifo (effects : Handle → List Call)
    (hE : ∀ m, ∀ c ∈ effects m, c.isMicro = false) {fuel : Nat} {st : State}
    (h : st.microtasks.length ≤ fuel) : (checkpoint effects fuel st).2 = st.microtasks := by
  have := (checkpointGo_empties effects hE fuel st [] h).2
  simpa [checkpoint] using this

/-- With any effects, the checkpoint either empties the queue or uses all its fuel. -/
theorem checkpointGo_empties_or_fuel (effects : Handle → List Call) :
    ∀ (fuel : Nat) (st : State) (acc : List Handle),
      (checkpointGo effects fuel st acc).1.microtasks = [] ∨
      (checkpointGo effects fuel st acc).2.length = acc.length + fuel
  | 0, st, acc => by simp [checkpointGo]
  | fuel + 1, st, acc => by
    unfold checkpointGo
    cases hm : st.microtasks with
    | nil => simp [hm]
    | cons m rest =>
      simp only
      rcases checkpointGo_empties_or_fuel effects fuel _ (m :: acc) with h | h
      · exact .inl h
      · right; rw [h]; simp; omega

theorem checkpoint_empties_or_fuel (effects : Handle → List Call) (fuel : Nat) (st : State) :
    (checkpoint effects fuel st).1.microtasks = [] ∨ (checkpoint effects fuel st).2.length = fuel := by
  have := checkpointGo_empties_or_fuel effects fuel st []
  simpa [checkpoint] using this

/-! ## 2. Timers fire in order -/

/-- Armed timers are in firing order, and each was armed before `nextSeq`. -/
def Inv (st : State) : Prop := Sorted st.timers ∧ ∀ t ∈ st.timers, t.seq < st.nextSeq

/-- `st'` comes after `st`: the clock and `nextSeq` do not go back, and each
timer of `st'` was armed in `st` or armed later. -/
def Grows (st st' : State) : Prop :=
  st.clock ≤ st'.clock ∧ st.nextSeq ≤ st'.nextSeq ∧
  ∀ t ∈ st'.timers, t ∈ st.timers ∨ (st.clock ≤ t.due ∧ st.nextSeq ≤ t.seq)

theorem Grows.trans {a b c : State} (h₁ : Grows a b) (h₂ : Grows b c) : Grows a c := by
  refine ⟨Nat.le_trans h₁.1 h₂.1, Nat.le_trans h₁.2.1 h₂.2.1, fun t ht => ?_⟩
  rcases h₂.2.2 t ht with ht | ⟨d, s⟩
  · exact h₁.2.2 t ht
  · exact .inr ⟨Nat.le_trans h₁.1 d, Nat.le_trans h₁.2.1 s⟩

/-- A step that only removes timers keeps `Inv` and `Grows`. -/
theorem keep_of_sub {st st' : State} (hc : st.clock ≤ st'.clock) (hs : st.nextSeq = st'.nextSeq)
    (sub : st'.timers.Sublist st.timers) (h : Inv st) : Inv st' ∧ Grows st st' := by
  refine ⟨⟨List.Pairwise.sublist sub h.1, fun t ht => hs ▸ h.2 t (sub.subset ht)⟩,
    hc, Nat.le_of_eq hs, fun t ht => .inl (sub.subset ht)⟩

theorem arm_keep {st : State} {id cb timeout : Nat} {p : Bool} {level : Nat} (h : Inv st) :
    Inv (st.arm id cb timeout p level) ∧ Grows st (st.arm id cb timeout p level) := by
  refine ⟨⟨insert_sorted h.1, fun t ht => ?_⟩, Nat.le_refl _, Nat.le_succ _, fun t ht => ?_⟩
  · rcases mem_insert.1 ht with e | ht
    · subst e; simp [State.arm]
    · have := h.2 t ht; simp only [State.arm]; omega
  · rcases mem_insert.1 ht with e | ht
    · subst e; exact .inr ⟨Nat.le_add_right _ _, Nat.le_refl _⟩
    · exact .inl ht

theorem finish_keep {st : State} (h : Inv st) : Inv st.finish ∧ Grows st st.finish := by
  have base : Inv st.done ∧ Grows st st.done :=
    keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h
  unfold State.finish
  split
  · exact base
  · split
    · exact base
    · split
      · split
        · exact ⟨(arm_keep base.1).1, base.2.trans (arm_keep base.1).2⟩
        · exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h
      · exact base

theorem step_keep {st : State} (h : Inv st) : Inv st.step.1 ∧ Grows st st.step.1 := by
  have f := finish_keep h
  unfold State.step
  simp only
  split
  · exact ⟨f.1, f.2⟩
  · split
    · exact ⟨f.1, f.2⟩
    · exact ⟨f.1, f.2⟩

theorem fire_parts (st : State) :
    (st.fire).1.timers = (due st.clock st.timers).2 ∧ (st.fire).2 = (due st.clock st.timers).1 ∧
    (st.fire).1.clock = st.clock ∧ (st.fire).1.nextSeq = st.nextSeq := by
  simp [State.fire]

theorem advance_clock (st : State) (target : Nat) : st.clock ≤ (st.advanceTo target).1.clock := by
  unfold State.advanceTo
  rw [(fire_parts _).2.2.1]
  show st.clock ≤ st.nextClock target
  unfold State.nextClock
  split
  · split <;> exact Nat.le_max_left _ _
  · exact Nat.le_max_left _ _

theorem advance_keep {st : State} {target : Nat} (h : Inv st) :
    Inv (st.advanceTo target).1 ∧ Grows st (st.advanceTo target).1 := by
  have hc := advance_clock st target
  obtain ⟨p1, -, -, p4⟩ := fire_parts { st with clock := st.nextClock target }
  refine keep_of_sub hc (by unfold State.advanceTo; rw [p4]) ?_ h
  unfold State.advanceTo; rw [p1]
  exact List.dropWhile_sublist _

/-- The fired timers of an advance are armed timers, in firing order, each due,
and each fires no later than every timer still armed. -/
theorem advance_fired {st : State} {target : Nat} (h : Inv st) :
    Sorted (st.advanceTo target).2 ∧
    ∀ a ∈ (st.advanceTo target).2, a ∈ st.timers ∧
      (∀ t ∈ (st.advanceTo target).1.timers, keyLe a t = true) ∧
      a.due ≤ (st.advanceTo target).1.clock ∧ a.seq < (st.advanceTo target).1.nextSeq := by
  unfold State.advanceTo
  obtain ⟨p1, p2, p3, p4⟩ := fire_parts { st with clock := st.nextClock target }
  have d := due_sorted (clock := st.nextClock target) (l := st.timers) h.1
  rw [p1, p2, p3, p4]
  refine ⟨d.1, fun a ha => ?_⟩
  have mem : a ∈ st.timers := by
    rw [← due_parts (clock := st.nextClock target) (l := st.timers)]
    exact List.mem_append_left _ ha
  exact ⟨mem, fun t htt => d.2.2.1 a ha t htt, d.2.2.2 a ha, h.2 a mem⟩

theorem Call.apply_keep {c : Call} {st : State} (h : Inv st) : Inv (c.apply st) ∧ Grows st (c.apply st) := by
  cases c with
  | queueTask s cb => exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h
  | queueMicrotask cb => exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h
  | setTimer cb timeout p =>
    exact arm_keep (st := { st with active := st.nextTimer :: st.active, nextTimer := st.nextTimer + 1 }) h
  | clearTimer id => exact keep_of_sub (Nat.le_refl _) rfl List.filter_sublist h
  | requestFrame cb => exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h
  | cancelFrame id => exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h

theorem Input.apply_keep {i : Input} {st : State} (h : Inv st) :
    Inv (i.apply st).1 ∧ Grows st (i.apply st).1 := by
  cases i with
  | call c => exact Call.apply_keep h
  | advance target => exact advance_keep h
  | step => exact step_keep h
  | render => exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h
  | frameStep =>
    simp only [Input.apply, State.frameStep]
    split <;> exact keep_of_sub (Nat.le_refl _) rfl (List.Sublist.refl _) h

/-- Timer `a` has fired in the past of `st`. -/
def Past (a : Timer) (st : State) : Prop :=
  (∀ t ∈ st.timers, keyLe a t = true) ∧ a.due ≤ st.clock ∧ a.seq < st.nextSeq

theorem Past.grows {a : Timer} {st st' : State} (h : Past a st) (g : Grows st st') : Past a st' := by
  refine ⟨fun t ht => ?_, Nat.le_trans h.2.1 g.1, Nat.lt_of_lt_of_le h.2.2 g.2.1⟩
  rcases g.2.2 t ht with ht | ⟨d, s⟩
  · exact h.1 t ht
  · rw [keyLe_iff]; have := h.2.1; have := h.2.2; omega

theorem Input.apply_fired {i : Input} {st : State} (h : Inv st) :
    Sorted (i.apply st).2.fired ∧
    ∀ a ∈ (i.apply st).2.fired, a ∈ st.timers ∧ Past a (i.apply st).1 := by
  cases i with
  | advance target =>
    have := advance_fired (target := target) h
    exact ⟨this.1, fun a ha => ⟨(this.2 a ha).1, (this.2 a ha).2⟩⟩
  | call c => exact ⟨List.Pairwise.nil, fun a ha => by simp [Input.apply] at ha⟩
  | step =>
    refine ⟨?_, fun a ha => ?_⟩ <;> simp [Input.apply] at * <;> exact List.Pairwise.nil
  | render => exact ⟨List.Pairwise.nil, fun a ha => by simp [Input.apply] at ha⟩
  | frameStep =>
    refine ⟨?_, fun a ha => ?_⟩ <;> simp [Input.apply] at * <;> exact List.Pairwise.nil

/-- The timers fired over a sequence of inputs. For proofs only. -/
noncomputable def trace : State → List Input → State × List Timer
  | st, [] => (st, [])
  | st, i :: rest => ((trace (i.apply st).1 rest).1, (i.apply st).2.fired ++ (trace (i.apply st).1 rest).2)

theorem trace_after {a : Timer} : ∀ {st : State} (rest : List Input), Inv st → Past a st →
    ∀ b ∈ (trace st rest).2, keyLe a b = true
  | st, [], _, _, b, hb => by simp [trace] at hb
  | st, i :: rest, h, p, b, hb => by
    simp only [trace, List.mem_append] at hb
    have k := Input.apply_keep (i := i) h
    rcases hb with hb | hb
    · exact p.1 b ((Input.apply_fired h).2 b hb).1
    · exact trace_after rest k.1 (p.grows k.2) b hb

/-- Over any sequence of inputs, timers fire in order of due time, and timers
with equal due times in the order in which they were armed. -/
theorem trace_fired_sorted : ∀ {st : State} (inputs : List Input), Inv st → Sorted (trace st inputs).2
  | st, [], _ => List.Pairwise.nil
  | st, i :: rest, h => by
    simp only [trace]
    have k := Input.apply_keep (i := i) h
    have f := Input.apply_fired (i := i) h
    unfold Sorted
    rw [List.pairwise_append]
    exact ⟨f.1, trace_fired_sorted rest k.1,
      fun a ha b hb => trace_after rest k.1 (f.2 a ha).2 b hb⟩

theorem initial_inv : Inv ({} : State) := ⟨List.Pairwise.nil, fun _ h => by simp at h⟩

/-- `setTimeout` and `setInterval` arm a timer with the next id, due after the
clamped timeout, with `seq` equal to the arms before it and nesting level one
more than that of the running task. -/
theorem setTimer_armed (st : State) (cb timeout : Nat) (p : Bool) :
    ∃ t ∈ (st.setTimer cb timeout p).1.timers,
      t.id = st.nextTimer ∧ (st.setTimer cb timeout p).2 = st.nextTimer ∧
      t.due = st.clock + clamp st.nesting timeout ∧ t.seq = st.nextSeq ∧
      t.nesting = st.nesting + 1 ∧ t.periodic = p := by
  refine ⟨_, mem_insert.2 (.inl rfl), ?_⟩
  simp [State.setTimer, State.arm]

/-! ## 3. A cleared timer never fires -/

/-- Timer `id` was allocated and is not in the map of active timers. -/
def Gone (id : Nat) (st : State) : Prop := id ∉ st.active ∧ id < st.nextTimer

theorem clearTimer_gone {id : Nat} {st : State} (h : id < st.nextTimer) : Gone id (st.clearTimer id) := by
  refine ⟨?_, h⟩
  simp [State.clearTimer]

theorem finish_gone {id : Nat} {st : State} (h : Gone id st) : Gone id st.finish := by
  unfold State.finish
  split
  · exact h
  · split
    · exact h
    · split
      · split
        · exact h
        · refine ⟨?_, h.2⟩
          intro m; exact h.1 (List.mem_filter.1 m).1
      · exact h

theorem takeTask_runnable {active : List Nat} :
    ∀ {tasks : List Task} {t : Task} {rest : List Task},
      State.takeTask active tasks = some (t, rest) → State.runnable active t = true
  | [], _, _, e => by simp [State.takeTask] at e
  | x :: xs, t, rest, e => by
    unfold State.takeTask at e
    split at e
    · cases e; assumption
    · exact takeTask_runnable e

theorem step_gone {id : Nat} {st : State} (h : Gone id st) :
    Gone id st.step.1 ∧ ∀ r, st.step.2 = some r → r.timer ≠ some id := by
  have f := finish_gone h
  unfold State.step
  simp only
  split
  · exact ⟨f, fun r e => by cases e; simp⟩
  · split
    · exact ⟨f, fun r e => by cases e⟩
    · rename_i t rest e
      refine ⟨f, fun r er => ?_⟩
      cases er
      have run := takeTask_runnable e
      intro bad
      simp only [Task.run, Option.map_eq_some_iff] at bad
      obtain ⟨tm, htm, hid⟩ := bad
      simp only [State.runnable, htm] at run
      exact f.1 (hid ▸ List.contains_iff_mem.1 run)

theorem Input.apply_gone {id : Nat} {i : Input} {st : State} (h : Gone id st) :
    Gone id (i.apply st).1 ∧ ∀ r, (i.apply st).2.run = some r → r.timer ≠ some id := by
  cases i with
  | call c =>
    refine ⟨?_, fun r e => by simp [Input.apply] at e⟩
    cases c with
    | setTimer cb timeout p =>
      refine ⟨?_, ?_⟩
      · simp only [Input.apply, Call.apply, State.setTimer, State.arm, List.mem_cons, not_or]
        exact ⟨by have := h.2; omega, h.1⟩
      · simp only [Input.apply, Call.apply, State.setTimer, State.arm]; have := h.2; omega
    | clearTimer x =>
      refine ⟨fun m => h.1 (List.mem_filter.1 m).1, h.2⟩
    | _ => exact h
  | advance target =>
    refine ⟨?_, fun r e => by simp [Input.apply] at e⟩
    exact h
  | step =>
    have := step_gone h
    exact ⟨this.1, fun r e => this.2 r (by simpa [Input.apply] using e)⟩
  | render => exact ⟨h, fun r e => by simp [Input.apply] at e⟩
  | frameStep =>
    simp only [Input.apply, State.frameStep]
    split
    · exact ⟨h, fun r e => by simp at e⟩
    · exact ⟨h, fun r e => by simp at e; subst e; simp⟩

/-- The callbacks run over a sequence of inputs. For proofs only. -/
noncomputable def runs : State → List Input → List Run
  | _, [] => []
  | st, i :: rest => (i.apply st).2.run.toList ++ runs (i.apply st).1 rest

theorem runs_gone {id : Nat} : ∀ {st : State} (inputs : List Input), Gone id st →
    ∀ r ∈ runs st inputs, r.timer ≠ some id
  | _, [], _, r, hr => by simp [runs] at hr
  | st, i :: rest, h, r, hr => by
    simp only [runs, List.mem_append, Option.mem_toList] at hr
    have g := Input.apply_gone (i := i) h
    rcases hr with hr | hr
    · exact g.2 r hr
    · exact runs_gone rest g.1 r hr

/-- After `clearTimeout(id)` or `clearInterval(id)` of an allocated id, no
sequence of inputs runs a callback of that timer. -/
theorem cleared_never_fires {id : Nat} {st : State} (h : id < st.nextTimer) (inputs : List Input) :
    ∀ r ∈ runs (st.clearTimer id) inputs, r.timer ≠ some id :=
  runs_gone inputs (clearTimer_gone h)

/-! ## 5. Event dispatch -/

namespace Dispatch

theorem mem_invoke {ls : List Listener} {t node d : Nat} {c : Bool} {v : Visit}
    (h : v ∈ invoke ls t node d c) :
    v.node = node ∧ v.depth = d ∧ v.capture = c ∧
    v.phase = (if d == t then .atTarget else if c then .capturing else .bubbling) := by
  unfold invoke at h
  simp only [List.mem_map] at h
  obtain ⟨l, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem mem_bubble {ls : List Listener} {t node d : Nat} {b : Bool} {v : Visit}
    (h : v ∈ (if b then invoke ls t node d false else [])) :
    v.node = node ∧ v.depth = d ∧ v.capture = false ∧ b = true := by
  split at h
  · have := mem_invoke h; exact ⟨this.1, this.2.1, this.2.2.1, by assumption⟩
  · simp at h

theorem invoke_flat {ls : List Listener} {t node d : Nat} {c : Bool} (n : Nat) :
    (invoke ls t node d c).Pairwise (fun a b => rank n a ≤ rank n b) :=
  List.pairwise_of_forall_mem_list fun a ha b hb => by
    have x := mem_invoke ha; have y := mem_invoke hb
    simp [rank, x.2.1, x.2.2.1, y.2.1, y.2.2.1]

/-- Visits come in walk order: capture invokes root first (rank = depth), then
bubbling invokes target first (rank = 2·target + 1 − depth). Each capture visit
comes before each bubbling visit. -/
theorem plan_ordered (path : List Nat) (ls : List Listener) (bubbles : Bool) :
    (plan path ls bubbles).Pairwise
      (fun a b => rank (path.length - 1) a ≤ rank (path.length - 1) b) := by
  unfold plan
  rw [List.pairwise_append, List.pairwise_flatMap, List.pairwise_flatMap, List.pairwise_reverse]
  refine ⟨⟨fun _ _ => invoke_flat _, ?_⟩, ⟨fun _ _ => ?_, ?_⟩, ?_⟩
  · refine List.Pairwise.imp (fun {d e} hde x hx y hy => ?_) List.pairwise_lt_range
    have a := mem_invoke hx; have b := mem_invoke hy
    simp [rank, a.2.1, a.2.2.1, b.2.1, b.2.2.1]; omega
  · split
    · exact invoke_flat _
    · exact List.Pairwise.nil
  · refine List.Pairwise.imp (fun {d e} hde x hx y hy => ?_) List.pairwise_lt_range
    have a := mem_bubble hx; have b := mem_bubble hy
    simp [rank, a.2.1, a.2.2.1, b.2.1, b.2.2.1]; omega
  · intro x hx y hy
    simp only [List.mem_flatMap, List.mem_reverse, List.mem_range] at hx hy
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    have a := mem_invoke hx; have b := mem_bubble hy
    simp [rank, a.2.1, a.2.2.1, b.2.1, b.2.2.1]; omega

/-- Each visit is at the node of the path at its depth. -/
theorem plan_node {path : List Nat} {ls : List Listener} {bubbles : Bool} {v : Visit}
    (h : v ∈ plan path ls bubbles) : path[v.depth]? = some v.node := by
  unfold plan at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range] at h
  rcases h with ⟨d, hd, hv⟩ | ⟨d, hd, hv⟩
  · have a := mem_invoke hv
    rw [a.2.1, a.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd]; rfl
  · have a := mem_bubble hv
    rw [a.2.1, a.1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd]; rfl

/-- The event phase is `AT_TARGET` exactly at the target. -/
theorem plan_phase {path : List Nat} {ls : List Listener} {bubbles : Bool} {v : Visit}
    (h : v ∈ plan path ls bubbles) :
    v.phase = (if v.depth == path.length - 1 then .atTarget
               else if v.capture then .capturing else .bubbling) := by
  unfold plan at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range] at h
  rcases h with ⟨d, hd, hv⟩ | ⟨d, hd, hv⟩
  · have a := mem_invoke hv; rw [a.2.1, a.2.2.1, a.2.2.2]
  · split at hv
    · have a := mem_invoke hv; rw [a.2.1, a.2.2.1, a.2.2.2]
    · simp at hv

/-- An event that does not bubble visits no non-capture listener of an ancestor. -/
theorem plan_no_bubbles {path : List Nat} {ls : List Listener} {v : Visit}
    (h : v ∈ plan path ls false) (hc : v.capture = false) : v.depth = path.length - 1 := by
  unfold plan at h
  simp only [List.mem_append, List.mem_flatMap, List.mem_reverse, List.mem_range] at h
  rcases h with ⟨d, hd, hv⟩ | ⟨d, hd, hv⟩
  · have a := mem_invoke hv; rw [a.2.2.1] at hc; cases hc
  · have a := mem_bubble hv
    simp at a; rw [a.2.1]; exact a.2.2.2

theorem afterStop_immediate (visits : List Visit) (i : Nat) : afterStop visits i true = [] := by
  unfold afterStop; split <;> simp

theorem afterStop_prefix (visits : List Visit) (i : Nat) (immediate : Bool) :
    afterStop visits i immediate <+: visits.drop (i + 1) := by
  unfold afterStop
  split
  · exact List.nil_prefix
  · split
    · exact List.nil_prefix
    · exact List.takeWhile_prefix _

/-- After `stopPropagation` in visit `i`, only the rest of the same invoke
runs: same depth and same pass. -/
theorem afterStop_same_invoke {visits : List Visit} {i : Nat} {immediate : Bool} {v w : Visit}
    (hv : visits[i]? = some v) (hw : w ∈ afterStop visits i immediate) :
    w.depth = v.depth ∧ w.capture = v.capture := by
  unfold afterStop at hw
  rw [hv] at hw
  simp only at hw
  split at hw
  · simp at hw
  · have := mem_takeWhile_imp hw
    simp at this
    exact this

/-- In a dispatch plan, the walk stops at the next node: every visit that
still runs after `stopPropagation` is at the same node as the stopping one. -/
theorem afterStop_same_node {path : List Nat} {ls : List Listener} {bubbles : Bool} {i : Nat}
    {immediate : Bool} {v w : Visit}
    (hv : (plan path ls bubbles)[i]? = some v) (hw : w ∈ afterStop (plan path ls bubbles) i immediate) :
    w.node = v.node := by
  have same := afterStop_same_invoke hv hw
  have wIn : w ∈ plan path ls bubbles :=
    List.mem_of_mem_drop ((afterStop_prefix _ i immediate).subset hw)
  have vIn : v ∈ plan path ls bubbles := List.mem_of_getElem? hv
  have a := plan_node wIn
  have b := plan_node vIn
  rw [same.1, b] at a
  exact (Option.some.inj a).symm

end Dispatch

/-! ## 6. One animation frame per advance -/

namespace Driver
variable {σ : Type} (d : Driver σ)

/-- An advance runs at most one frame batch: the frames it counts are at most one more
than it started with, and none more once its frame slot is used (`slot = none`). -/
theorem advanceGo_frames (target : Nat) :
    ∀ (fuel : Nat) (slot : Option Nat) (s : σ) (frames : Nat),
      (d.advanceGo target fuel slot s frames).2.1 ≤ frames + (if slot.isSome then 1 else 0) := by
  intro fuel
  induction fuel with
  | zero => intro slot s frames; simp [advanceGo]
  | succ fuel ih =>
    intro slot s frames
    cases slot with
    | none =>
      simp only [advanceGo]
      split
      · exact ih _ _ _
      · split
        · next h => exact absurd h.2 (by simp)
        · split
          · simp
          · exact ih _ _ _
    | some f =>
      simp only [advanceGo]
      split
      · exact ih _ _ _
      · split
        · split
          · exact Nat.le_trans (ih _ _ _) (by simp)
          · exact Nat.le_trans (ih _ _ _) (by simp)
        · split
          · simp
          · exact ih _ _ _

/-- With no frame slot, an advance runs no frame batch. -/
theorem advanceGo_no_slot (target fuel : Nat) (s : σ) (frames : Nat) :
    (d.advanceGo target fuel none s frames).2.1 = frames := by
  have := d.advanceGo_frames target fuel none s frames
  have h2 : frames ≤ (d.advanceGo target fuel none s frames).2.1 := by
    clear this
    induction fuel generalizing s frames with
    | zero => simp [advanceGo]
    | succ fuel ih =>
      simp only [advanceGo]
      split
      · exact ih _ _
      · split
        · split
          · exact ih _ _
          · exact Nat.le_trans (Nat.le_succ _) (ih _ _)
        · split
          · simp
          · exact ih _ _
  simp at this; omega

/-- The frame slot is at most the target, and at least the clock. -/
theorem frameSlot_between {clock target f : Nat} {last : Option Nat}
    (h : frameSlot clock target last = some f) : clock ≤ f ∧ f ≤ target := by
  simp only [frameSlot] at h
  split at h
  · rename_i hc; cases h
    exact ⟨hc.1, Nat.div_mul_le_self target frameInterval⟩
  · cases h

/-- A slot is never the time of the last frame: two advances never run a frame at the
same time. -/
theorem frameSlot_ne_last {clock target f : Nat} {last : Option Nat}
    (h : frameSlot clock target last = some f) : last ≠ some f := by
  simp only [frameSlot] at h
  split at h
  · rename_i hc; cases h; exact hc.2
  · cases h

end Driver

end L4Factoidal.EventLoop
