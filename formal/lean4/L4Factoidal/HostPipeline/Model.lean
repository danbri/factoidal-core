/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
Released under the Apache 2.0 license.
-/

/-!
# The native host's frame pipeline as a transition system

A TLA-style model (states, `init`, a next-state relation, invariants, a progress property) of
the threads of the desktop browser's frame pipeline (issue 398):

- the **main thread** pumps the window's events (`pump`: every queued input is taken), asks the
  engine worker for a frame (`request`), submits a computed frame to the GPU (`submit`), and
  asks the GPU whether its work is done (`ask` ... `answer`). Deno's `onSubmittedWorkDone`
  blocks the calling thread until the GPU has finished everything submitted (measured on Deno
  2.9.4, and its `queue.rs` polls with a blocking wait), so between `ask` and `answer` the
  main thread takes no input;
- the **engine worker** computes the frame (`compiled`);
- the **GPU** finishes submitted work in its own time (`gpuFinish`);
- **input** arrives at any time (`arrive`).

The host's rule (`gpu_pacing.ts`, the gate driven by the event loop): at most `bound`
submissions unanswered, and at most one blocking wait between two pumps (the gate asks only
from the loop's turn, right after a pump).

Proved, for every bound:
- `reachable_inv`: in every reachable state, at most `bound` frames are in flight, the GPU's
  unfinished work is within them, and the main thread has blocked at most once since it last
  took input (`waits ≤ 1`): input never waits behind more than one GPU wait, and that wait
  covers at most `bound` frames.
- `no_deadlock`: every reachable state has a next step (`pump`, `gpuFinish` or `answer`).
- `answer_frees`, `submit_after_answer`: the end of a blocking wait frees every submission, and
  a ready frame is submitted in the next step: the host need not wait for anything after the
  answer (it counts the answer when the call returns).
- `drain`: from every reachable state, a state in which all input has been taken and the main
  thread is not blocked is reached in at most `gpuLeft + 2` steps (the GPU's remaining
  submissions, the answer, one pump): the progress property, under fairness of the GPU and the
  main thread (stated as the existence of that run, not as a temporal formula).

Host traces: a host records only what the main thread sees (`Obs`: pumps, submits, the start
and end of each blocking wait). `check` replays such a trace and lists every step the rule
forbids; `check_nil_refines` proves that a trace with no violation is the main-thread
projection of a run of this model, so every invariant above holds along the host's real
run. `test.sh` checks traces of real pages (`pipeline_trace_check.ts`).

What is not proved: that the host records every event (the recording is in `gpu_pacing.ts`
and `run_html.ts`), and timings (the model counts steps, not milliseconds).

Only core imports.
-/

namespace L4Factoidal.HostPipeline

/-- The host's limits: submissions unanswered at most (`gpu_pacing.ts` gate). -/
structure Config where
  bound : Nat
  deriving DecidableEq, Repr

structure State where
  /-- Input events queued in the window, not yet taken. -/
  queued : Nat := 0
  /-- The engine worker is computing a frame. -/
  engine : Bool := false
  /-- A computed frame waits to be submitted. -/
  ready : Bool := false
  /-- Submissions the main thread has not had answered. -/
  inFlight : Nat := 0
  /-- Submissions the GPU has not finished. -/
  gpuLeft : Nat := 0
  /-- Blocking GPU waits started since the main thread last took input. -/
  waits : Nat := 0
  /-- The main thread is inside a blocking GPU wait. -/
  blocked : Bool := false
  deriving DecidableEq, Repr, Inhabited

def init : State := {}

inductive Act where
  | arrive | pump | request | compiled | submit | ask | answer | gpuFinish
  deriving DecidableEq, Repr

/-- The next-state relation, as a function: `none` when the action is not enabled. -/
def step (c : Config) (s : State) : Act → Option State
  | .arrive => some { s with queued := s.queued + 1 }
  | .pump => if s.blocked then none else some { s with queued := 0, waits := 0 }
  | .request => if s.blocked || s.engine || s.ready then none else some { s with engine := true }
  | .compiled => if s.engine then some { s with engine := false, ready := true } else none
  | .submit =>
    if s.blocked || !s.ready || c.bound ≤ s.inFlight then none
    else some { s with ready := false, inFlight := s.inFlight + 1, gpuLeft := s.gpuLeft + 1 }
  | .ask => if s.blocked || s.inFlight == 0 || s.waits != 0 then none else some { s with blocked := true, waits := 1 }
  | .answer => if s.blocked && s.gpuLeft == 0 then some { s with blocked := false, inFlight := 0 } else none
  | .gpuFinish => if s.gpuLeft == 0 then none else some { s with gpuLeft := s.gpuLeft - 1 }

/-- Reachable states. -/
inductive Reachable (c : Config) : State → Prop where
  | init : Reachable c init
  | step {s t : State} (a : Act) : Reachable c s → step c s a = some t → Reachable c t

/-- The invariant. -/
def Inv (c : Config) (s : State) : Prop :=
  s.inFlight ≤ c.bound ∧ s.gpuLeft ≤ s.inFlight ∧ s.waits ≤ 1 ∧ (s.blocked = true → s.waits = 1)

theorem inv_init (c : Config) : Inv c init := by simp [Inv, init]

theorem inv_step (c : Config) {s t : State} (a : Act) (h : Inv c s) (hs : step c s a = some t) : Inv c t := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  cases a <;> simp only [step] at hs
  · cases hs; exact ⟨h1, h2, h3, h4⟩
  · split at hs
    · cases hs
    · cases hs; refine ⟨h1, h2, by simp, ?_⟩; simp_all
  · split at hs
    · cases hs
    · cases hs; exact ⟨h1, h2, h3, h4⟩
  · split at hs
    · cases hs; exact ⟨h1, h2, h3, h4⟩
    · cases hs
  · split at hs
    · cases hs
    · cases hs
      rename_i hg
      simp at hg
      obtain ⟨⟨_, _⟩, hlt⟩ := hg
      exact ⟨by simp; omega, by simp; omega, h3, h4⟩
  · split at hs
    · cases hs
    · cases hs; exact ⟨h1, h2, by simp, by simp⟩
  · split at hs
    · cases hs; refine ⟨by simp, ?_, h3, by simp⟩
      rename_i hg; simp only [Bool.and_eq_true, beq_iff_eq] at hg; simp [hg.2]
    · cases hs
  · split at hs
    · cases hs
    · cases hs; exact ⟨h1, by simp; omega, h3, h4⟩

/-- The safety property: at most `bound` frames in flight, and at most one blocking wait
between two pumps. -/
theorem reachable_inv (c : Config) {s : State} (h : Reachable c s) : Inv c s := by
  induction h with
  | init => exact inv_init c
  | step a _ hs ih => exact inv_step c a ih hs

/-- No reachable state is stuck. -/
theorem no_deadlock (c : Config) (s : State) : ∃ a t, step c s a = some t := by
  cases hb : s.blocked
  · exact ⟨.pump, { s with queued := 0, waits := 0 }, by simp [step, hb]⟩
  · cases hg : s.gpuLeft with
    | zero => exact ⟨.answer, { s with blocked := false, inFlight := 0 }, by simp [step, hb, hg]⟩
    | succ n => exact ⟨.gpuFinish, { s with gpuLeft := n }, by simp [step, hg]⟩

/-- Runs: the reflexive, transitive closure of `step`, counting steps. -/
inductive Steps (c : Config) : State → Nat → State → Prop where
  | refl (s : State) : Steps c s 0 s
  | cons {s t u : State} {n : Nat} (a : Act) : step c s a = some t → Steps c t n u → Steps c s (n + 1) u

theorem Steps.trans {c : Config} {s t u : State} {m n : Nat} (h1 : Steps c s m t) (h2 : Steps c t n u) :
    Steps c s (m + n) u := by
  induction h1 with
  | refl => simpa using h2
  | cons a hs _ ih => rw [Nat.add_right_comm]; exact .cons a hs (ih h2)

theorem Steps.reachable {c : Config} {s t : State} {n : Nat} (h : Steps c s n t) (hs : Reachable c s) : Reachable c t := by
  induction h with
  | refl => exact hs
  | cons a st _ ih => exact ih (.step a hs st)

/-- The GPU finishes its `gpuLeft` submissions in that many steps. -/
theorem finish_all (c : Config) : ∀ (s : State), Steps c s s.gpuLeft { s with gpuLeft := 0 } := by
  intro s
  induction hg : s.gpuLeft generalizing s with
  | zero =>
    have : ({ s with gpuLeft := 0 } : State) = s := by cases s; simp_all
    rw [this]; exact .refl s
  | succ n ih =>
    have st : step c s .gpuFinish = some { s with gpuLeft := n } := by simp [step, hg]
    have := ih { s with gpuLeft := n } rfl
    exact .cons .gpuFinish st (by simpa using this)

/-- Progress: from any state, all queued input is taken and the main thread is free within
`gpuLeft + 2` steps. -/
theorem drain (c : Config) (s : State) :
    ∃ t n, Steps c s n t ∧ n ≤ s.gpuLeft + 2 ∧ t.queued = 0 ∧ t.blocked = false := by
  cases hb : s.blocked
  · exact ⟨{ s with queued := 0, waits := 0 }, 1, .cons .pump (by simp [step, hb]) (.refl _), by omega, rfl, hb⟩
  · have h1 := finish_all c s
    let s1 : State := { s with gpuLeft := 0 }
    let s2 : State := { s1 with blocked := false, inFlight := 0 }
    have st2 : step c s1 .answer = some s2 := by simp [s1, s2, step, hb]
    have st3 : step c s2 .pump = some { s2 with queued := 0, waits := 0 } := by simp [s2, step]
    refine ⟨{ s2 with queued := 0, waits := 0 }, s.gpuLeft + 2, ?_, by omega, rfl, rfl⟩
    exact h1.trans (.cons .answer st2 (.cons .pump st3 (.refl _)))

/-! ## The answer frees the pipeline

The host counts its submissions as answered at the end of the blocking wait (`answer`: when
`onSubmittedWorkDone` returns), not at a later event (Deno answers the promise of that call
about 11 ms after the call returned; a frame that waited for the promise was held that long
for nothing). In the model that is what `answer` already is; these say that nothing more is
needed between the end of a wait and the next submission. -/

/-- The end of a blocking wait leaves nothing in flight, nothing on the GPU, and the main
thread free; it starts no new wait. -/
theorem answer_frees (c : Config) {s t : State} (h : step c s .answer = some t) :
    t.inFlight = 0 ∧ t.gpuLeft = 0 ∧ t.blocked = false ∧ t.waits = s.waits := by
  simp only [step] at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, beq_iff_eq] at hg
    cases h
    exact ⟨rfl, hg.2, rfl, rfl⟩
  · cases h

/-- A frame that is ready when a wait ends can be submitted in the very next step (no pump and
no other event between), and is then the only one in flight: the next frame's GPU work does
not wait for anything after the answer. -/
theorem submit_after_answer (c : Config) (hb : 0 < c.bound) {s t : State}
    (h : step c s .answer = some t) (hr : t.ready = true) :
    ∃ u, step c t .submit = some u ∧ u.inFlight = 1 ∧ u.blocked = false := by
  obtain ⟨h1, _, h3, _⟩ := answer_frees c h
  have hlt : ¬ c.bound ≤ t.inFlight := by omega
  exact ⟨{ t with ready := false, inFlight := t.inFlight + 1, gpuLeft := t.gpuLeft + 1 },
    by simp [step, h3, hr, hlt], by simp [h1], h3⟩

/-! ## The host before this rule

Asks started on their own (a promise continuation), not from the loop's turn: two blocking
waits could follow each other with no pump between them. In this model that is `step` with no
`waits` guard on `ask`. A run of it reaches `waits = 2`: the property fails. -/

def stepFree (c : Config) (s : State) : Act → Option State
  | .ask => if s.blocked || s.inFlight == 0 then none else some { s with blocked := true, waits := s.waits + 1 }
  | a => step c s a

def runFree (c : Config) : State → List Act → Option State
  | s, [] => some s
  | s, a :: as => match stepFree c s a with
    | some t => runFree c t as
    | none => none

theorem free_breaks_one_wait :
    (runFree ⟨3⟩ init [.request, .compiled, .submit, .ask, .gpuFinish, .answer,
      .request, .compiled, .submit, .ask]).map (·.waits) = some 2 := by decide

/-! ## Host traces -/

/-- What the main thread records (`gpu_pacing.ts`, `run_html.ts`). -/
inductive Obs where
  | pump | submit | askBegin | askEnd
  deriving DecidableEq, Repr

/-- The main thread's part of the state. -/
structure Main where
  inFlight : Nat := 0
  waits : Nat := 0
  blocked : Bool := false
  deriving DecidableEq, Repr

def obsStep (c : Config) (m : Main) : Obs → Option Main
  | .pump => if m.blocked then none else some { m with waits := 0 }
  | .submit => if m.blocked || c.bound ≤ m.inFlight then none else some { m with inFlight := m.inFlight + 1 }
  | .askBegin => if m.blocked || m.inFlight == 0 || m.waits != 0 then none else some { m with blocked := true, waits := 1 }
  | .askEnd => if m.blocked then some { m with blocked := false, inFlight := 0 } else none

/-- Why a trace breaks the rule, at which event (0-based). -/
inductive Violation where
  /-- input was taken during a blocking wait (the trace is not of one main thread) -/
  | pumpWhileBlocked (i : Nat)
  /-- a submission over the bound, or during a wait -/
  | overBound (i : Nat) (inFlight : Nat)
  /-- a second blocking wait with no pump since the last, or a wait with nothing in flight -/
  | secondWait (i : Nat)
  | askEndWithoutAsk (i : Nat)
  deriving DecidableEq, Repr

def violationOf (i : Nat) (m : Main) : Obs → Violation
  | .pump => .pumpWhileBlocked i
  | .submit => .overBound i m.inFlight
  | .askBegin => .secondWait i
  | .askEnd => .askEndWithoutAsk i

/-- Replay a trace; stop at the first violation (a loop: no stack per event). -/
def checkFrom (c : Config) : Nat → Main → List Obs → List Violation
  | _, _, [] => []
  | i, m, o :: os => match obsStep c m o with
    | some m' => checkFrom c (i + 1) m' os
    | none => [violationOf i m o]

/-- The violations of a host trace (empty: it keeps the rule). -/
def check (c : Config) (tr : List Obs) : List Violation := checkFrom c 0 {} tr

/-- Full states that match a main-thread state, with the worker and GPU idle-or-finishing. -/
def Matches (m : Main) (s : State) : Prop :=
  s.inFlight = m.inFlight ∧ s.waits = m.waits ∧ s.blocked = m.blocked ∧ s.engine = false ∧ s.ready = false ∧
  s.gpuLeft ≤ s.inFlight

/-- One main-thread event is a run of the model: the hidden steps of the worker and the GPU
(`request`, `compiled` before a submit; the GPU's remaining `gpuFinish` before an answer) and
the event's own step. -/
theorem obsStep_refines (c : Config) {m m' : Main} {s : State} (o : Obs)
    (hm : Matches m s) (ho : obsStep c m o = some m') : ∃ t n, Steps c s n t ∧ Matches m' t := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hm
  cases o <;> simp only [obsStep] at ho
  · split at ho
    · cases ho
    · cases ho; rename_i hb
      refine ⟨{ s with queued := 0, waits := 0 }, 1, .cons .pump (by simp [step, h3, hb]) (.refl _), ?_⟩
      exact ⟨h1, rfl, h3, h4, h5, h6⟩
  · split at ho
    · cases ho
    · cases ho; rename_i hg
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Bool.not_eq_true] at hg
      let s1 : State := { s with engine := true }
      let s2 : State := { s1 with engine := false, ready := true }
      let s3 : State := { s2 with ready := false, inFlight := s2.inFlight + 1, gpuLeft := s2.gpuLeft + 1 }
      have a1 : step c s .request = some s1 := by simp [s1, step, h3, hg.1, h4, h5]
      have a2 : step c s1 .compiled = some s2 := by simp [s1, s2, step]
      have a3 : step c s2 .submit = some s3 := by
        simp [s1, s2, s3, step, h3, hg.1]; omega
      refine ⟨s3, 3, .cons .request a1 (.cons .compiled a2 (.cons .submit a3 (.refl _))), ?_⟩
      refine ⟨by simp [s1, s2, s3, h1], by simp [s1, s2, s3, h2], by simp [s1, s2, s3, h3], rfl, rfl, ?_⟩
      simp [s1, s2, s3]; omega
  · split at ho
    · cases ho
    · cases ho; rename_i hg
      have a : step c s .ask = some { s with blocked := true, waits := 1 } := by
        simp only [step, h3, h1, h2]; simp only [hg]; simp
      exact ⟨_, 1, .cons .ask a (.refl _), by simp [h1], rfl, rfl, h4, h5, by simpa using h6⟩
  · split at ho
    · cases ho; rename_i hb
      let s1 : State := { s with gpuLeft := 0 }
      have hf := finish_all c s
      have a : step c s1 .answer = some { s1 with blocked := false, inFlight := 0 } := by
        simp [s1, step, h3, hb]
      refine ⟨_, s.gpuLeft + 1, hf.trans (.cons .answer a (.refl _)), ?_⟩
      exact ⟨rfl, by simp [s1, h2], rfl, h4, h5, by simp [s1]⟩
    · cases ho

/-- A host trace with no violation is the main-thread projection of a run of the model from
`init`: the reached state is `Reachable`, so `reachable_inv` holds along it. -/
theorem check_nil_refines (c : Config) :
    ∀ (i : Nat) (m : Main) (s : State) (tr : List Obs), Reachable c s → Matches m s → checkFrom c i m tr = [] →
      ∃ t, Reachable c t ∧ ∃ m', Matches m' t := by
  intro i m s tr hr hm hc
  induction tr generalizing i m s with
  | nil => exact ⟨s, hr, m, hm⟩
  | cons o os ih =>
    simp only [checkFrom] at hc
    split at hc
    · rename_i m' ho
      obtain ⟨t, n, ht, hm'⟩ := obsStep_refines c o hm ho
      exact ih (i + 1) m' t (ht.reachable hr) hm' hc
    · cases hc

theorem checkFrom_nil_prefix (c : Config) : ∀ (tr : List Obs) (i : Nat) (m : Main) (k : Nat),
    checkFrom c i m tr = [] → checkFrom c i m (tr.take k) = []
  | [], _, _, _, _ => by simp [checkFrom]
  | _ :: _, _, _, 0, _ => by simp [checkFrom]
  | o :: os, i, m, k + 1, h => by
    simp only [List.take_succ_cons, checkFrom] at h ⊢
    cases ho : obsStep c m o with
    | none => rw [ho] at h; cases h
    | some m' => rw [ho] at h; exact checkFrom_nil_prefix c os (i + 1) m' k h

/-- Every prefix of a trace with no violation is a run of the model too, so the invariant holds
at every event of the host's run, not only at the end. -/
theorem check_nil_prefix (c : Config) (tr : List Obs) (h : check c tr = []) (k : Nat) :
    check c (tr.take k) = [] := checkFrom_nil_prefix c tr 0 {} k h

theorem init_matches : Matches {} init := by simp [Matches, init]

/-- The theorem `test.sh` relies on: a host trace `check` accepts ends in a reachable state of
the model, so it never had more than `bound` frames in flight or two blocking waits between
pumps. -/
theorem check_nil_sound (c : Config) (tr : List Obs) (h : check c tr = []) :
    ∃ t, Reachable c t ∧ Inv c t :=
  let ⟨t, ht, _⟩ := check_nil_refines c 0 {} init tr .init init_matches h
  ⟨t, ht, reachable_inv c ht⟩

/-! ## Parsing a recorded trace -/

/-- One event a line: `pump`, `submit`, `ask`, `answer` (other lines are ignored). -/
def parseObs (line : String) : Option Obs :=
  match line.trimAscii.toString with
  | "pump" => some .pump
  | "submit" => some .submit
  | "ask" => some .askBegin
  | "answer" => some .askEnd
  | _ => none

/-- The largest trace checked: a defined refusal past it. -/
def maxEvents : Nat := 1000000

#guard check ⟨1⟩ [.pump, .submit, .askBegin, .askEnd, .pump, .submit] == []
#guard check ⟨1⟩ [.submit, .submit] == [.overBound 1 1]
#guard check ⟨3⟩ [.submit, .askBegin, .askEnd, .submit, .askBegin] == [.secondWait 4]
#guard check ⟨3⟩ [.submit, .askBegin, .pump] == [.pumpWhileBlocked 2]
#guard check ⟨3⟩ [.submit, .askBegin, .askEnd, .pump, .submit, .askBegin, .askEnd] == []
-- Submissions right after the end of a wait, up to the bound, with no pump between.
#guard check ⟨3⟩ [.pump, .submit, .submit, .submit, .askBegin, .askEnd, .submit, .submit, .submit, .pump, .askBegin, .askEnd] == []
#guard check ⟨3⟩ [.pump, .submit, .askBegin, .askEnd, .submit, .submit, .submit, .submit] == [.overBound 7 3]

end L4Factoidal.HostPipeline
