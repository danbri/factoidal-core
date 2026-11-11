import L4Factoidal.EventLoop.Model

/-!
# Agents: a window and its dedicated workers (WHATWG HTML §8.1.2, §10)

HTML runs each worker in an agent of its own, with its own event loop. Agents meet only
through messages: posting a message queues a task on the receiver's event loop (the
"posted message" task source), which delivers the message's data there. This model
extends `EventLoop.State` (one agent's loop) to a system of agents:

- each agent has its own loop and an inbox, a queue of `(sender, data)`; a message is a
  task (`deliverHandle`, source `postedMessage`) plus its entry in the inbox;
- `post a b m` queues `m` from `a` on `b`; `take b` is the delivery task's step, which takes
  the inbox's first entry; `terminate b` (HTML `terminate()` and `close()`) empties `b`'s
  queues and closes it.

Theorems:

- `channel_prefix` (per-channel FIFO): whatever posts, deliveries and terminations happen,
  the messages delivered on a channel `a → b` are a prefix of the messages posted on it,
  in the same order;
- `step_isolated`, `post_other`, `take_other`: a step of agent `i` and a message to `b`
  change no other agent; `step_own`: what agent `i` becomes depends on its own state only
  (so a worker cannot read or write the page's state, nor the page a worker's);
- `terminated_no_step`: after `terminate b`, agent `b` runs no task again, whatever
  happens after.

`WasmVM.Hosts.LeanJSWorkers` is this model with BubblePopJS sessions as agents: a
worker's session is a value of its own, its runs take only that value, and the only
things that cross are the serialized bytes of `JS.Clone`.
-/

namespace L4Factoidal.EventLoop.Agents

/-- The callback of a message's delivery task (prelude.js `WORKER_EVENT`). -/
def deliverHandle : Handle := 0x7FFFFFF0

structure Agent (α : Type) where
  loop : State := {}
  inbox : List (Nat × α) := []
  closed : Bool := false

/-- A window (agent 0) and its workers, by number. -/
abbrev System (α : Type) := Nat → Agent α

variable {α : Type}

def set (sys : System α) (i : Nat) (x : Agent α) : System α := fun j => if j = i then x else sys j

@[simp] theorem set_same (sys : System α) (i : Nat) (x : Agent α) : set sys i x i = x := by simp [set]
@[simp] theorem set_other (sys : System α) (i j : Nat) (x : Agent α) (h : j ≠ i) : set sys i x j = sys j := by
  simp [set, h]

/-- `postMessage` from `a` to `b`: a task on `b`'s loop, and the data in its inbox. A
closed agent receives nothing. -/
def post (a b : Nat) (m : α) (sys : System α) : System α :=
  if (sys b).closed then sys
  else set sys b { sys b with inbox := (sys b).inbox ++ [(a, m)], loop := (sys b).loop.queueTask .postedMessage deliverHandle }

/-- The delivery task's step on `b`: the inbox's first entry. -/
def take (b : Nat) (sys : System α) : System α × Option (Nat × α) :=
  match (sys b).inbox with
  | [] => (sys, none)
  | e :: rest => (set sys b { sys b with inbox := rest }, some e)

/-- `terminate()` (and a worker's `close()`): its task queues and inbox are emptied, and
it is closed for good. -/
def stopped (l : State) : State :=
  { l with tasks := [], microtasks := [], timers := [], active := [], frames := [], frameBatch := [], current := none }

def terminate (b : Nat) (sys : System α) : System α :=
  set sys b { loop := stopped (sys b).loop, inbox := [], closed := true }

/-- One step of agent `i`'s event loop; a closed agent runs nothing. -/
def step (i : Nat) (sys : System α) : System α × Option Run :=
  if (sys i).closed then (sys, none)
  else (set sys i { sys i with loop := (sys i).loop.step.1 }, (sys i).loop.step.2)

/-! ## Isolation -/

theorem step_isolated (i j : Nat) (sys : System α) (h : j ≠ i) : (step i sys).1 j = sys j := by
  unfold step; split <;> simp [h]

/-- What agent `i` becomes in its step is a function of its own state: two systems that
agree on agent `i` give it the same state and run. -/
theorem step_own (i : Nat) (sys sys' : System α) (same : sys i = sys' i) :
    (step i sys).1 i = (step i sys').1 i ∧ (step i sys).2 = (step i sys').2 := by
  unfold step; rw [same]; split <;> simp_all

theorem post_other (a b j : Nat) (m : α) (sys : System α) (h : j ≠ b) : post a b m sys j = sys j := by
  unfold post; split <;> simp [h]

theorem take_other (b j : Nat) (sys : System α) (h : j ≠ b) : (take b sys).1 j = sys j := by
  unfold take; split <;> simp [h]

theorem terminate_other (b j : Nat) (sys : System α) (h : j ≠ b) : terminate b sys j = sys j := by
  simp [terminate, h]

/-! ## Termination -/

/-- What happens in a system: posts, deliveries, terminations and steps. -/
inductive Op (α : Type) where
  | post (a b : Nat) (m : α)
  | take (b : Nat)
  | terminate (b : Nat)
  | step (i : Nat)

/-- Apply an op; the answer also gives the delivered message of a `take`, with its
receiver. -/
def Op.apply : Op α → System α → System α × Option (Nat × Nat × α)
  | .post a b m, sys => (Agents.post a b m sys, none)
  | .take b, sys => ((Agents.take b sys).1, (Agents.take b sys).2.map fun (a, m) => (a, b, m))
  | .terminate b, sys => (Agents.terminate b sys, none)
  | .step i, sys => ((Agents.step i sys).1, none)

/-- Run ops; the system after, and the deliveries in order (sender, receiver, data). -/
def run : List (Op α) → System α → System α × List (Nat × Nat × α)
  | [], sys => (sys, [])
  | op :: ops, sys =>
    let (s, d) := op.apply sys
    let (s', ds) := run ops s
    (s', d.toList ++ ds)

theorem closed_stays (op : Op α) (b : Nat) (sys : System α) (h : (sys b).closed) :
    ((op.apply sys).1 b).closed := by
  cases op with
  | post a c m =>
    simp only [Op.apply, post]
    split
    · exact h
    · by_cases hb : b = c
      · subst hb; simp_all
      · simp [hb, h]
  | take c =>
    simp only [Op.apply, take]
    split
    · exact h
    · by_cases hb : b = c
      · subst hb; simp_all
      · simp [hb, h]
  | terminate c =>
    simp only [Op.apply, terminate]
    by_cases hb : b = c
    · subst hb; simp
    · simp [hb, h]
  | step i =>
    simp only [Op.apply, step]
    split
    · exact h
    · by_cases hb : b = i
      · subst hb; simp_all
      · simp [hb, h]

theorem run_closed (ops : List (Op α)) (b : Nat) (sys : System α) (h : (sys b).closed) :
    ((run ops sys).1 b).closed := by
  induction ops generalizing sys with
  | nil => exact h
  | cons op ops ih => exact ih _ (closed_stays op b sys h)

/-- After `terminate b`, whatever happens, agent `b` runs no task. -/
theorem terminated_no_step (b : Nat) (ops : List (Op α)) (sys : System α) :
    (step b (run ops (terminate b sys)).1).2 = none := by
  have h : ((run ops (terminate b sys)).1 b).closed := run_closed ops b _ (by simp [terminate])
  simp [step, h]

/-! ## Per-channel FIFO -/

/-- The data posted on channel `a → b` by ops. -/
def posted (a b : Nat) : List (Op α) → List α
  | [] => []
  | .post a' b' m :: ops => if a' = a ∧ b' = b then m :: posted a b ops else posted a b ops
  | _ :: ops => posted a b ops

/-- The data of the deliveries on channel `a → b`. -/
def onChannel (a b : Nat) (ds : List (Nat × Nat × α)) : List α :=
  ds.filterMap fun (a', b', m) => if a' = a ∧ b' = b then some m else none

/-- The entries from `a` in an inbox. -/
def from_ (a : Nat) (inbox : List (Nat × α)) : List α :=
  inbox.filterMap fun (a', m) => if a' = a then some m else none

theorem from_append (a : Nat) (xs ys : List (Nat × α)) : from_ a (xs ++ ys) = from_ a xs ++ from_ a ys := by
  simp [from_, List.filterMap_append]

/-- The invariant of channel `a → b`: what is still to be posted on it, put after its
deliveries so far and its inbox entries, is what will be posted; and it only ever loses
messages once `b` is closed. -/
theorem channel_go (a b : Nat) (ops : List (Op α)) (sys : System α) (pend : List α)
    (hpend : pend ≠ [] → (sys b).closed) :
    ∃ rest, from_ a (sys b).inbox ++ pend ++ posted a b ops =
      onChannel a b (run ops sys).2 ++ rest := by
  induction ops generalizing sys pend with
  | nil => exact ⟨from_ a (sys b).inbox ++ pend, by simp [posted, run, onChannel]⟩
  | cons op ops ih =>
    cases op with
    | post a' b' m =>
      simp only [run, Op.apply, Option.toList, List.nil_append]
      by_cases hc : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := hc
        simp only [posted, and_self, if_true]
        by_cases cl : (sys b').closed
        · -- closed: the message is lost, after the pending ones
          have e : post a' b' m sys = sys := by simp [post, cl]
          obtain ⟨rest, hr⟩ := ih sys (pend ++ [m]) (fun _ => cl)
          rw [e]
          exact ⟨rest, by simpa [List.append_assoc] using hr⟩
        · have hp : pend = [] := by
            by_cases hq : pend = []
            · exact hq
            · exact absurd (hpend hq) cl
          subst hp
          obtain ⟨rest, hr⟩ := ih (post a' b' m sys) [] (by simp)
          refine ⟨rest, ?_⟩
          have hi : (post a' b' m sys b').inbox = (sys b').inbox ++ [(a', m)] := by simp [post, cl]
          rw [hi, from_append] at hr
          simpa [from_, List.append_assoc] using hr
      · have hpost : posted a b (Op.post a' b' m :: ops) = posted a b ops := by simp [posted, hc]
        rw [hpost]
        by_cases hb : b' = b
        · subst hb
          have ha : a' ≠ a := fun h => hc ⟨h, rfl⟩
          by_cases cl : (sys b').closed
          · have e : post a' b' m sys = sys := by simp [post, cl]
            rw [e]; exact ih sys pend hpend
          · have hi : (post a' b' m sys b').inbox = (sys b').inbox ++ [(a', m)] := by simp [post, cl]
            have hcl : (post a' b' m sys b').closed = (sys b').closed := by simp [post, cl]
            obtain ⟨rest, hr⟩ := ih (post a' b' m sys) pend (by rw [hcl]; exact hpend)
            rw [hi, from_append] at hr
            exact ⟨rest, by simpa [from_, ha] using hr⟩
        · have e := post_other a' b' b m sys (Ne.symm hb)
          obtain ⟨rest, hr⟩ := ih (post a' b' m sys) pend (by rw [e]; exact hpend)
          rw [e] at hr
          exact ⟨rest, hr⟩
    | take c =>
      simp only [run, Op.apply]
      have hpost : posted a b (Op.take c :: ops) = posted a b ops := by simp [posted]
      rw [hpost]
      by_cases hc : c = b
      · subst hc
        unfold take
        cases hx : (sys c).inbox with
        | nil =>
          simp only [Option.map, Option.toList, List.nil_append]
          simpa [hx] using ih sys pend hpend
        | cons e es =>
          obtain ⟨a', m⟩ := e
          simp only [Option.map, Option.toList, List.singleton_append]
          obtain ⟨rest, hr⟩ := ih (set sys c { sys c with inbox := es }) pend (by simpa using hpend)
          simp only [set_same] at hr
          refine ⟨rest, ?_⟩
          by_cases ha : a' = a
          · subst ha
            simp only [onChannel, List.filterMap_cons, and_self, if_true] at hr ⊢
            simpa [from_] using hr
          · simp only [onChannel, List.filterMap_cons, ha, false_and, if_false] at hr ⊢
            simpa [from_, ha] using hr
      · have e := take_other c b sys (Ne.symm hc)
        obtain ⟨rest, hr⟩ := ih (take c sys).1 pend (by rw [e]; exact hpend)
        rw [e] at hr
        refine ⟨rest, ?_⟩
        rw [hr]
        cases ht : (take c sys).2 with
        | none => simp
        | some p =>
          obtain ⟨a', m⟩ := p
          simp [onChannel, hc]
    | terminate c =>
      simp only [run, Op.apply, Option.toList, List.nil_append]
      have hpost : posted a b (Op.terminate c :: ops) = posted a b ops := by simp [posted]
      rw [hpost]
      by_cases hc : c = b
      · subst hc
        -- the inbox's entries become lost ones: still after the deliveries
        obtain ⟨rest, hr⟩ := ih (terminate c sys) (from_ a (sys c).inbox ++ pend) (by simp [terminate])
        refine ⟨rest, ?_⟩
        simpa [terminate, from_, List.append_assoc] using hr
      · have e := terminate_other c b sys (Ne.symm hc)
        obtain ⟨rest, hr⟩ := ih (terminate c sys) pend (by rw [e]; exact hpend)
        rw [e] at hr
        exact ⟨rest, hr⟩
    | step i =>
      simp only [run, Op.apply, Option.toList, List.nil_append]
      have hpost : posted a b (Op.step i :: ops) = posted a b ops := by simp [posted]
      rw [hpost]
      have hsame : (step i sys).1 b = sys b ∨ ((step i sys).1 b).inbox = (sys b).inbox ∧
          ((step i sys).1 b).closed = (sys b).closed := by
        unfold step
        split
        · exact Or.inl rfl
        · by_cases hb : b = i
          · subst hb; right; simp
          · left; simp [hb]
      have hi : ((step i sys).1 b).inbox = (sys b).inbox := by rcases hsame with h | h <;> simp [h]
      have hcl : ((step i sys).1 b).closed = (sys b).closed := by rcases hsame with h | h <;> simp [h]
      obtain ⟨rest, hr⟩ := ih (step i sys).1 pend (by rw [hcl]; exact hpend)
      rw [hi] at hr
      exact ⟨rest, hr⟩

/-- Per-channel FIFO: on each channel `a → b`, starting from empty inboxes, the messages
delivered are a prefix of the messages posted, in order. -/
theorem channel_prefix (a b : Nat) (ops : List (Op α)) (sys : System α) (empty : (sys b).inbox = []) :
    ∃ rest, posted a b ops = onChannel a b (run ops sys).2 ++ rest := by
  obtain ⟨rest, h⟩ := channel_go a b ops sys [] (by simp)
  exact ⟨rest, by simpa [empty, from_] using h⟩

end L4Factoidal.EventLoop.Agents
