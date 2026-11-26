/-
# Web Audio output: the ring between the rendering task and the audio consumer, as a state machine

Stage D1 of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, section 13.5.

The C ring of `ffi/audio_sink.c` (one writer thread, one reader thread, `capacity` frames) follows
this model. A frame is identified by its number: frame `i` is the `i`-th frame ever written and is
stored in slot `i % capacity`. The model carries frame numbers, not sample values, so that the
theorems say what is read, and in which order, without a sample type.

- `write k` is all or nothing: when `k` frames fit in the free space, all `k` are taken; otherwise
  none is taken. (The rendering task writes whole render quanta.)
- `read k` takes `a = min k available` frames, in order, and gives `k - a` frames of silence for
  the rest. When it gives any silence, it counts one under-run event and adds the silent frames
  to `silent`.

What this file does not model: threads and memory order. The C ring makes each side write only its
own counter (`written` by the writer, `read` by the reader), so each operation sees the other
side's counter at some earlier or equal value; a stale `written` only makes the reader take fewer
frames, a stale `read` only makes the writer see less free space. The stress test under
ThreadSanitizer (`tests/audio/run.sh`) checks the C against these rules by running both sides at
once. Imports `Init` only.
-/
namespace L4Factoidal.WebAudio.Ring

/-- The state of a ring. `underruns` counts events, `silent` counts frames of silence given. -/
structure State where
  capacity : Nat
  written : Nat
  read : Nat
  underruns : Nat
  silent : Nat
deriving Repr, DecidableEq

/-- The empty ring. -/
def State.empty (capacity : Nat) : State := ⟨capacity, 0, 0, 0, 0⟩

/-- Frames written and not yet read. -/
def State.avail (s : State) : Nat := s.written - s.read

/-- Frames that can still be written. -/
def State.free (s : State) : Nat := s.capacity - (s.written - s.read)

/-- `write s k`: all or nothing. Answers the new state and the number of frames taken
(`k` or `0`). -/
def write (s : State) (k : Nat) : State × Nat :=
  if k ≤ s.free then ({ s with written := s.written + k }, k) else (s, 0)

/-- What a read gives: the new state, the numbers of the frames taken (in order), and the number of
frames of silence that follow them. -/
structure ReadResult where
  state : State
  frames : List Nat
  silence : Nat

/-- `read s k`: gives `min k avail` frames, then silence for the rest. -/
def read (s : State) (k : Nat) : ReadResult :=
  let a := min k s.avail
  { state := { s with read := s.read + a,
                      underruns := s.underruns + (if a < k then 1 else 0),
                      silent := s.silent + (k - a) },
    frames := List.range' s.read a,
    silence := k - a }

/-- One operation on the ring. -/
inductive Op where
  | write (k : Nat)
  | read (k : Nat)
deriving Repr, DecidableEq

/-- One step: the new state and the numbers of the non-silent frames the step gave out. -/
def step (s : State) : Op → State × List Nat
  | .write k => ((write s k).1, [])
  | .read k => ((read s k).state, (read s k).frames)

/-- A sequence of operations: the final state and the concatenation of the non-silent output of its
reads. -/
def run : State → List Op → State × List Nat
  | s, [] => (s, [])
  | s, op :: ops =>
    let r1 := step s op
    let r2 := run r1.1 ops
    (r2.1, r1.2 ++ r2.2)

/-- The states reachable from the empty ring of a capacity by writes and reads. -/
inductive Reachable (cap : Nat) : State → Prop where
  | empty : Reachable cap (State.empty cap)
  | ofWrite {s : State} (k : Nat) : Reachable cap s → Reachable cap (write s k).1
  | ofRead {s : State} (k : Nat) : Reachable cap s → Reachable cap (read s k).state

/-- The invariant of section 13.5. -/
def Inv (s : State) : Prop := s.read ≤ s.written ∧ s.written ≤ s.read + s.capacity

theorem write_capacity (s : State) (k : Nat) : (write s k).1.capacity = s.capacity := by
  unfold write; split <;> rfl

theorem write_read (s : State) (k : Nat) : (write s k).1.read = s.read := by
  unfold write; split <;> rfl

theorem write_written (s : State) (k : Nat) :
    (write s k).1.written = (if k ≤ s.free then s.written + k else s.written) := by
  unfold write; split <;> simp_all

/-- Says: in every state reachable from the empty ring by any sequence of writes and reads,
`read ≤ written` and `written ≤ read + capacity`, and the capacity is the one the ring started
with. Does not say: that the writer or the reader is ever not blocked (a full ring refuses a
write, an empty ring gives silence), and nothing about the threads of the C code. -/
theorem reachable_inv {cap : Nat} {s : State} (h : Reachable cap s) :
    Inv s ∧ s.capacity = cap := by
  induction h with
  | empty => simp [Inv, State.empty]
  | @ofWrite s' k _ ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih
    refine ⟨?_, by rw [write_capacity]; exact h3⟩
    by_cases hk : k ≤ s'.free
    · have e : (write s' k).1 = { s' with written := s'.written + k } := by simp [write, hk]
      rw [e]
      simp only [State.free] at hk
      exact ⟨by dsimp only; omega, by dsimp only; omega⟩
    · have e : (write s' k).1 = s' := by simp [write, hk]
      rw [e]
      exact ⟨h1, h2⟩
  | ofRead k _ ih =>
    obtain ⟨⟨h1, h2⟩, h3⟩ := ih
    simp only [read, State.avail, Inv] at *
    refine ⟨?_, h3⟩
    omega

/-- A run keeps a state reachable. -/
theorem run_reachable {cap : Nat} (ops : List Op) :
    ∀ {s : State}, Reachable cap s → Reachable cap (run s ops).1 := by
  induction ops with
  | nil => intro s h; exact h
  | cons op ops ih =>
    intro s h
    simp only [run]
    apply ih
    cases op with
    | write k => exact Reachable.ofWrite k h
    | read k => exact Reachable.ofRead k h

/-- Says: the invariant holds after any sequence of operations from the empty ring. Does not say:
anything about a ring made in another way (for example one with `read > written`). -/
theorem run_inv (cap : Nat) (ops : List Op) :
    Inv (run (State.empty cap) ops).1 :=
  (reachable_inv (run_reachable ops Reachable.empty)).1

theorem run_read_mono (ops : List Op) :
    ∀ s : State, s.read ≤ (run s ops).1.read := by
  induction ops with
  | nil => intro s; simp [run]
  | cons op ops ih =>
    intro s
    simp only [run]
    have h := ih (step s op).1
    have : s.read ≤ (step s op).1.read := by
      cases op with
      | write k => simp [step, write_read]
      | read k => simp [step, read]
    omega

theorem run_frames_aux (ops : List Op) :
    ∀ s : State, (run s ops).2 = List.range' s.read ((run s ops).1.read - s.read) := by
  induction ops with
  | nil => intro s; simp [run]
  | cons op ops ih =>
    intro s
    simp only [run]
    rw [ih (step s op).1]
    have hm := run_read_mono ops (step s op).1
    cases op with
    | write k =>
      simp only [step, write_read] at *
      simp
    | read k =>
      simp only [step, read] at *
      generalize (run _ ops).1.read = n at *
      rw [show n - s.read = min k s.avail + (n - (s.read + min k s.avail)) by omega]
      exact List.range'_append_1 ..

/-- Says: over any sequence of writes and reads from the empty ring, the non-silent frames that the
reads gave, put one after another, are exactly frames `0, 1, 2, ..., r - 1` in order, where `r` is
the final `read`: no frame twice, none skipped, none out of order. Does not say: that every frame
written is read (frames still in the ring are not read yet), and nothing about the sample values
(the model carries frame numbers). -/
theorem run_frames (cap : Nat) (ops : List Op) :
    (run (State.empty cap) ops).2 = List.range (run (State.empty cap) ops).1.read := by
  rw [run_frames_aux]
  simp [State.empty, List.range_eq_range']

/-- Says: the frames that a read gives are frames `s.read, s.read + 1, ...` (`min k avail` of them),
followed by `k - min k avail` frames of silence; the sum is `k`. A read counts one under-run event
when it gives any silence, and none when it does not, and adds its silent frames to `silent`.
Does not say: that a reader that gets silence is wrong (an empty ring is a normal state at the
start, and while the rendering task is late). -/
theorem read_silence (s : State) (k : Nat) :
    (read s k).frames = List.range' s.read (min k s.avail) ∧
    (read s k).frames.length + (read s k).silence = k ∧
    (read s k).silence = k - (read s k).frames.length ∧
    (read s k).state.underruns = s.underruns + (if 0 < (read s k).silence then 1 else 0) ∧
    (read s k).state.silent = s.silent + (read s k).silence := by
  by_cases h : s.avail < k
  · have e : min k s.avail = s.avail := by omega
    simp [read, e, h, List.length_range']
    omega
  · have e : min k s.avail = k := by omega
    simp [read, e, List.length_range']

/-- Says: a write takes all `k` frames or none; it takes them exactly when `k` is at most the free
space. Does not say: that a refused write may be retried with fewer frames (the rendering task
writes whole render quanta and waits instead). -/
theorem write_all_or_nothing (s : State) (k : Nat) :
    ((write s k).2 = k ∧ (write s k).1.written = s.written + k ∧ k ≤ s.free) ∨
    ((write s k).2 = 0 ∧ (write s k).1 = s ∧ s.free < k) := by
  unfold write
  by_cases h : k ≤ s.free
  · simp [h]
  · simp [h]; omega

/-- Says: a write that is accepted never overwrites a frame that has not been read. If frame `i` is written and not yet read (`s.read ≤ i < s.written`), and `j`
is one of the frames the write adds (`s.written ≤ j < s.written + k`), then slot `j % capacity` is
not slot `i % capacity`. Does not say: that the slot of a frame that was read is free for any
frame (only the frames the write adds are covered), or that two frames that were both read share
no slot (they may). -/
theorem write_no_overwrite (s : State) (k : Nat) (hk : k ≤ s.free)
    (i j : Nat) (hi : s.read ≤ i ∧ i < s.written) (hj : s.written ≤ j ∧ j < s.written + k) :
    j % s.capacity ≠ i % s.capacity := by
  intro heq
  have hdvd : s.capacity ∣ j - i := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq heq)
  simp only [State.free] at hk
  have hpos : 0 < j - i := by omega
  have := Nat.le_of_dvd hpos hdvd
  omega


-- Small traces. Capacity 4: write 3, read 2, write 3, write 2 (refused: 0 free), read 5 (4 frames,
-- 1 silent), read 1 (all silent).
private def trace : List Op := [.write 3, .read 2, .write 3, .write 2, .read 5, .read 1]
#guard (run (State.empty 4) trace).2 = [0, 1, 2, 3, 4, 5]
#guard (run (State.empty 4) trace).1 = ⟨4, 6, 6, 2, 2⟩
#guard (write (State.empty 4) 5) = (State.empty 4, 0)
#guard (write (State.empty 4) 4).2 = 4
#guard (read (State.empty 4) 3).silence = 3
#guard (read (State.empty 4) 3).state.underruns = 1
#guard (read { State.empty 4 with written := 2 } 2).state.underruns = 0

end L4Factoidal.WebAudio.Ring
