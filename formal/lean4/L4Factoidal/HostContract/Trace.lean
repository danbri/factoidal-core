import L4Factoidal.HostContract.Model

/-! Boundary traces: what a host gave the engine and what it got back, checked against the
contract (`Model.lean`) and against another host's trace.

A host in test mode (`FOAFNAUT_HOST_TRACE`) records one `Call` per crossing of the engine's C ABI:
the export, the request's operation, digests of the HTML, the request and the answer, the viewport,
and the relaxation fields the request set. Digests are enough: the checker never needs the bytes.

Two results:

- `violations t tr` lists every call of `tr` that target `t` may not make (an export it does not
  link, an unknown operation, an operation needing a capability it lacks, a relaxation field it
  may not set, a viewport over the bound). `violations_nil_iff` says an empty list is exactly
  `Conforms t tr`.
- `disagreements a b` lists pairs of compared calls of two traces that had the same input and
  the same contract-visible history (`annotate`) but different answers.
  `recorded_disagreements_nil` proves that two recordings of runs of one engine have none,
  under the engine assumptions of `Engine.Assumptions`. A disagreement therefore shows one of:
  two builds of the engine that differ (native and Wasm), a host that altered an answer or
  dropped a call from its trace, or an assumption about an operation's kind that is wrong. The
  checker says which pair.

Assumptions, listed, not proved here:
- A1 (`Engine.Assumptions.neutral`): a call of a `query`, `counter` or `hostFact` operation
  changes nothing a later answer depends on (`obs`).
- A2 (`stateful_congr`, `answer_congr`): what a `state` call does, and what a compared call
  answers, depends only on `obs` and the call. Caches (layouts kept, `FrameCost.Lru`) and
  counters are outside `obs`.
- A3: the native and Wasm builds compute the same Lean functions (the compilers are correct);
  the trace check of the two builds on one page tests it.
- A4 (host): each host calls the mutable document engine from one thread (the independent pure
  presenter entry may run concurrently after serial initialisation), passes each answer on unaltered, frees
  each answer once, and records every call in test mode. Not checkable from Lean; the trace
  checker catches an altered or missing answer only when another host made the same call.
- A5 (host resources): the host has the memory for the answers (bounded by the engine:
  16 MiB a source, `WebDocument` bounds) and does not end the engine mid-call. -/
namespace L4Factoidal.HostContract

/-- What a host gives the engine in one call: the contract-visible input. -/
structure Input where
  sym : Export
  op : String
  html : String
  request : String
  width : Nat
  height : Nat
  deriving DecidableEq, Repr

/-- One recorded call. -/
structure Call where
  input : Input
  answer : String
  /-- Relaxation fields the request set (any field of `relaxFields` present). -/
  fields : List String := []
  deriving DecidableEq, Repr

/-- The largest viewport side the engine lays out (`WebDocument`), and the bound on one trace. -/
def maxSide : Nat := 16384
def maxCalls : Nat := 4096

/-- Does a call of operation `op` change the state later answers depend on? -/
def affects (op : String) : Bool := kindOf op == .state

/-- Are a call's answers compared between traces? Counters and host facts are not. -/
def compared (op : String) : Bool := match kindOf op with
  | .counter | .hostFact => false
  | _ => true

/-! ## Conformance -/

/-- Why a call breaks the contract of a target. -/
inductive Violation where
  | export_ (i : Nat) (e : Export)
  | unknownOp (i : Nat) (op : String)
  | capability (i : Nat) (op : String) (c : Cap)
  | relaxation (i : Nat) (field : String)
  | viewport (i : Nat)
  | tooLong (n : Nat)
  deriving DecidableEq, Repr

def callViolations (t : Target) (i : Nat) (c : Call) : List Violation :=
  (if t.exports.contains c.input.sym then [] else [.export_ i c.input.sym]) ++
  (if (opSpec? c.input.op).isSome then
    (needsOf c.input.op).filterMap fun cap => if t.caps.contains cap then none else some (.capability i c.input.op cap)
   else [.unknownOp i c.input.op]) ++
  (c.fields.filterMap fun f => if t.relax.contains f then none else some (.relaxation i f)) ++
  (if c.input.width ≤ maxSide && c.input.height ≤ maxSide then [] else [.viewport i])

def violationsFrom (t : Target) : Nat → List Call → List Violation
  | _, [] => []
  | i, c :: cs => callViolations t i c ++ violationsFrom t (i + 1) cs

/-- `violationsFrom` with an accumulator: the compiled form (a loop, no stack per call). -/
def violationsAcc (t : Target) : Nat → List Call → List Violation → List Violation
  | _, [], acc => acc
  | i, c :: cs, acc => violationsAcc t (i + 1) cs (acc ++ callViolations t i c)

theorem violationsAcc_eq (t : Target) : ∀ (i : Nat) (cs : List Call) (acc : List Violation),
    violationsAcc t i cs acc = acc ++ violationsFrom t i cs
  | _, [], acc => by simp [violationsAcc, violationsFrom]
  | i, c :: cs, acc => by simp [violationsAcc, violationsFrom, violationsAcc_eq t (i + 1) cs]

def violationsFromTR (t : Target) (i : Nat) (cs : List Call) : List Violation := violationsAcc t i cs []

@[csimp] theorem violationsFrom_eq_TR : @violationsFrom = @violationsFromTR := by
  funext t i cs; simp [violationsFromTR, violationsAcc_eq]

/-- Every violation of a trace; a trace past `maxCalls` is refused as a whole (a defined answer at
the bound, not a long run). -/
def violations (t : Target) (tr : List Call) : List Violation :=
  if tr.length > maxCalls then [.tooLong tr.length] else violationsFrom t 0 tr

/-- A call within target `t`'s contract. -/
def CallOk (t : Target) (c : Call) : Prop :=
  c.input.sym ∈ t.exports ∧ allowedOp t c.input.op = true ∧ (∀ f ∈ c.fields, f ∈ t.relax) ∧
  c.input.width ≤ maxSide ∧ c.input.height ≤ maxSide

def Conforms (t : Target) (tr : List Call) : Prop := tr.length ≤ maxCalls ∧ ∀ c ∈ tr, CallOk t c

theorem callViolations_nil_iff {t : Target} {i : Nat} {c : Call} :
    callViolations t i c = [] ↔ CallOk t c := by
  unfold callViolations CallOk allowedOp
  by_cases hs : (opSpec? c.input.op).isSome = true
  · simp [hs, List.filterMap_eq_nil_iff, List.all_eq_true]
  · simp [hs]

theorem violationsFrom_nil_iff {t : Target} : ∀ {i : Nat} {tr : List Call},
    violationsFrom t i tr = [] ↔ ∀ c ∈ tr, CallOk t c
  | _, [] => by simp [violationsFrom]
  | i, c :: cs => by
    simp only [violationsFrom, List.append_eq_nil_iff, List.mem_cons, forall_eq_or_imp]
    rw [callViolations_nil_iff, violationsFrom_nil_iff]

/-- The checker decides conformance: no violation listed exactly when the trace conforms. -/
theorem violations_nil_iff {t : Target} {tr : List Call} : violations t tr = [] ↔ Conforms t tr := by
  unfold violations Conforms
  by_cases h : tr.length > maxCalls
  · simp [h]; omega
  · simp only [h, if_false, violationsFrom_nil_iff]
    constructor
    · intro hc; exact ⟨by omega, hc⟩
    · exact fun hc => hc.2

/-- A trace that conforms to a target conforms to any target that provides at least as much. -/
theorem Conforms.mono {t u : Target} {tr : List Call}
    (hc : ∀ c, c ∈ t.caps → c ∈ u.caps) (he : ∀ e, e ∈ t.exports → e ∈ u.exports)
    (hr : ∀ f, f ∈ t.relax → f ∈ u.relax) (h : Conforms t tr) : Conforms u tr := by
  refine ⟨h.1, fun c hmem => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := h.2 c hmem
  exact ⟨he _ h1, allowedOp_mono hc h2, fun f hf => hr f (h3 f hf), h4, h5⟩

/-- A target without a capability that an operation needs can not make a conforming call of it:
the feature is off at the boundary, never half on. -/
theorem refused_without_cap {t : Target} {c : Call} {cap : Cap}
    (hneed : cap ∈ needsOf c.input.op) (hmiss : cap ∉ t.caps) : ¬ CallOk t c :=
  fun h => hmiss (allowedOp_needs h.2.1 hneed)

/-! ## The engine, as the hosts see it -/

/-- The engine as a machine over calls. `σ` is its whole state; `obs` the part answers may depend
on (held fonts and images, script sessions, settings), without caches and counters. -/
structure Engine (σ ω : Type) where
  init : σ
  step : σ → Input → σ × String
  obs : σ → ω

/-- The assumptions A1 and A2 about the engine (see the module comment). -/
structure Engine.Assumptions {σ ω : Type} (e : Engine σ ω) : Prop where
  neutral : ∀ s i, affects i.op = false → e.obs (e.step s i).1 = e.obs s
  stateful_congr : ∀ s t i, e.obs s = e.obs t → e.obs (e.step s i).1 = e.obs (e.step t i).1
  answer_congr : ∀ s t i, compared i.op = true → e.obs s = e.obs t → (e.step s i).2 = (e.step t i).2

/-- The state after a list of inputs. -/
def Engine.after {σ ω : Type} (e : Engine σ ω) (s : σ) : List Input → σ
  | [] => s
  | i :: is => e.after (e.step s i).1 is

theorem Engine.after_append {σ ω : Type} (e : Engine σ ω) (s : σ) (l : List Input) (i : Input) :
    e.after s (l ++ [i]) = (e.step (e.after s l) i).1 := by
  induction l generalizing s with
  | nil => rfl
  | cons j js ih => exact ih _

/-- What answers may depend on after a run is fixed by its `state` calls alone (A1, A2). -/
theorem Engine.obs_after_filter {σ ω : Type} {e : Engine σ ω} (h : e.Assumptions) :
    ∀ (is : List Input) (s t : σ), e.obs s = e.obs t →
      e.obs (e.after s is) = e.obs (e.after t (is.filter (affects ·.op))) := by
  intro is
  induction is with
  | nil => intro s t hst; exact hst
  | cons i is ih =>
    intro s t hst
    by_cases ha : affects i.op = true
    · simp only [Engine.after, List.filter_cons, ha, if_true]
      exact ih _ _ (h.stateful_congr s t i hst)
    · have ha' : affects i.op = false := by simpa using ha
      simp only [Engine.after, List.filter_cons, ha', Bool.false_eq_true, if_false]
      exact ih _ _ (by rw [h.neutral s i ha']; exact hst)

/-- Two hosts, one engine: the same `state` calls in the same order, then the same compared call,
give the same answer, whatever queries, counters and host-fact calls each host made around them.
So two conforming hosts given the same contract-visible input trace see the same frames, trees and
answers. -/
theorem Engine.same_visible_same_answer {σ ω : Type} {e : Engine σ ω} (h : e.Assumptions)
    (s : σ) (a b : List Input) (hab : a.filter (affects ·.op) = b.filter (affects ·.op))
    (i : Input) (hi : compared i.op = true) :
    (e.step (e.after s a) i).2 = (e.step (e.after s b) i).2 := by
  apply h.answer_congr _ _ i hi
  rw [Engine.obs_after_filter h a s s rfl, Engine.obs_after_filter h b s s rfl, hab]

/-! ## Recorded traces and the cross-host check -/

/-- A trace is a recording of a run of `e` from `s`: every answer is the engine's answer. -/
def Recorded {σ ω : Type} (e : Engine σ ω) : σ → List Call → Prop
  | _, [] => True
  | s, c :: cs => (e.step s c.input).2 = c.answer ∧ Recorded e (e.step s c.input).1 cs

/-- Each call with its visible history: the `state` inputs before it, latest first. -/
def annotate : List Input → List Call → List (List Input × Call)
  | _, [] => []
  | acc, c :: cs => (acc, c) :: annotate (if affects c.input.op then c.input :: acc else acc) cs

/-- `annotate` with an accumulator: the compiled form. -/
def annotateAcc : List Input → List Call → List (List Input × Call) → List (List Input × Call)
  | _, [], out => out.reverse
  | acc, c :: cs, out => annotateAcc (if affects c.input.op then c.input :: acc else acc) cs ((acc, c) :: out)

theorem annotateAcc_eq : ∀ (cs : List Call) (acc : List Input) (out : List (List Input × Call)),
    annotateAcc acc cs out = out.reverse ++ annotate acc cs
  | [], _, out => by simp [annotateAcc, annotate]
  | c :: cs, acc, out => by simp [annotateAcc, annotate, annotateAcc_eq cs]

def annotateTR (acc : List Input) (cs : List Call) : List (List Input × Call) := annotateAcc acc cs []

@[csimp] theorem annotate_eq_TR : @annotate = @annotateTR := by
  funext acc cs; simp [annotateTR, annotateAcc_eq]

/-- Two calls that must agree: compared, same input, same visible history. -/
def mustAgree (x y : List Input × Call) : Bool :=
  compared x.2.input.op && x.2.input == y.2.input && x.1 == y.1

/-- The pairs that must agree and do not. -/
def disagreementsOf (a b : List (List Input × Call)) : List (Call × Call) :=
  a.flatMap fun x => (b.filter fun y => mustAgree x y && x.2.answer != y.2.answer).map fun y => (x.2, y.2)

/-- How many pairs were compared (the check means little when this is 0). -/
def matchedOf (a b : List (List Input × Call)) : Nat :=
  a.foldl (fun n x => n + (b.filter (mustAgree x)).length) 0

def disagreements (a b : List Call) : List (Call × Call) := disagreementsOf (annotate [] a) (annotate [] b)

theorem annotate_recorded {σ ω : Type} {e : Engine σ ω} (h : e.Assumptions) (s0 : σ) :
    ∀ (cs : List Call) (acc : List Input) (s : σ), Recorded e s cs →
      e.obs s = e.obs (e.after s0 acc.reverse) →
      ∀ p c, (p, c) ∈ annotate acc cs →
        ∃ t, e.obs t = e.obs (e.after s0 p.reverse) ∧ (e.step t c.input).2 = c.answer := by
  intro cs
  induction cs with
  | nil => intro _ _ _ _ p c hm; simp [annotate] at hm
  | cons d ds ih =>
    intro acc s hrec hobs p c hm
    simp only [annotate, List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨s, hobs, hrec.1⟩
    · apply ih _ _ hrec.2 _ p c hm
      by_cases ha : affects d.input.op = true
      · simp only [ha, if_true, List.reverse_cons, Engine.after_append]
        exact h.stateful_congr _ _ _ hobs
      · have ha' : affects d.input.op = false := by simpa using ha
        simp only [ha', Bool.false_eq_true, if_false]
        rw [h.neutral s _ ha']; exact hobs

/-- Two recordings of runs of one engine from one start never disagree: the checker's reports
are sound (A1, A2; A3 when the two runs are two builds). -/
theorem recorded_disagreements_nil {σ ω : Type} {e : Engine σ ω} (h : e.Assumptions) (s0 : σ)
    (a b : List Call) (ha : Recorded e s0 a) (hb : Recorded e s0 b) : disagreements a b = [] := by
  unfold disagreements disagreementsOf
  simp only [List.flatMap_eq_nil_iff, List.map_eq_nil_iff, List.filter_eq_nil_iff]
  rintro ⟨p, c⟩ hx ⟨q, d⟩ hy hbad
  simp only [mustAgree, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hbad
  obtain ⟨⟨⟨hcmp, hin⟩, hpq⟩, hne⟩ := hbad
  obtain ⟨t, ht, hta⟩ := annotate_recorded h s0 a [] s0 ha rfl p c hx
  obtain ⟨u, hu, hua⟩ := annotate_recorded h s0 b [] s0 hb rfl q d hy
  apply hne
  rw [← hta, ← hua, hin]
  apply h.answer_congr _ _ _ (hin ▸ hcmp)
  rw [ht, hu, hpq]

/-! ## Samples -/

private def call (op : String) (req answer : String) (fields : List String := []) : Call :=
  ⟨⟨.documentCallBin, op, "h1", req, 800, 600⟩, answer, fields⟩

private def tgt (n : String) : Target := match target? n with
  | some t => t
  | none => ⟨n, none, "", [], [], [], []⟩
private def hubTarget : Target := tgt "hub"

-- The Hub may hand CORS to itself; Textnaut may not; nobody sends a GPU layer without a GPU.
#guard violations hubTarget [call "inspect" "r" "a" ["hostCors"]] == []
#guard violations (tgt "textnaut") [call "inspect" "r" "a" ["hostCors"]] == [.relaxation 0 "hostCors"]
#guard violations (tgt "textnaut") [call "chromeLayer" "r" "a"] == [.capability 0 "chromeLayer" .gpu]
#guard violations hubTarget [call "launchMissiles" "r" "a"] == [.unknownOp 0 "launchMissiles"]
-- A counter between two renders does not stop them being compared; a font load does.
#guard disagreements [call "render" "r" "A"] [call "frameWork" "f" "7", call "render" "r" "A"] == []
#guard (disagreements [call "render" "r" "A"] [call "frameWork" "f" "7", call "render" "r" "B"]).length == 1
#guard disagreements [call "render" "r" "A"] [call "fontLoad" "f" "ok", call "render" "r" "B"] == []
#guard matchedOf (annotate [] [call "render" "r" "A"]) (annotate [] [call "fontLoad" "f" "ok", call "render" "r" "B"]) == 0

end L4Factoidal.HostContract
