/-
Presenter: the part of the browser that turns finished layer frames and scroll input into
presented pictures, separated from the engine that makes the frames.

Design record: docs/designissues/2026-11-17-presenter-and-linked-instances.md.

Today the Deno host runs this on the thread that also runs engine turns, so a long script turn
delays a scroll inside the band that is already drawn. The step below is the one decision every
host runs: the Deno main thread with the engine in a worker (stage 1), a present thread in
`native_window.m` (stage 2), and the Hub's worker. Hosts move bytes; they make no decision of
their own. Equivalence between hosts reduces to each host's mailbox implementing the channels
named here (`Mailbox`), plus the fact that they all call this `step`.

Self-contained (imports nothing from the engine), so that it builds in seconds and a native host
can link the compiled `step` alone.
-/
namespace L4Factoidal.Presenter

/-- A frame of layers the engine finished: its number, the page rows its page layer covers
(`bandTop`, `bandHeight`), and the scrolls it shows with no new engine work (`keepFrom` to
`keepTo`, Lean's `WebDocument.layersJSON` band). The textures themselves are the host's
handles and are not part of the decision. -/
structure LayerFrame where
  id : Nat
  bandTop : Nat
  bandHeight : Nat
  keepFrom : Nat
  keepTo : Nat
  deriving Repr, DecidableEq

/-- What the presenter holds: the view height, the scroll the user asked for, the frame it
shows, and the scroll it last asked the engine a band for (none: nothing outstanding). -/
structure State where
  view : Nat
  scroll : Nat
  shown : Option LayerFrame := none
  asked : Option Nat := none
  deriving Repr, DecidableEq

/-- What reaches the presenter: input from the window, a frame from the engine, a display tick. -/
inductive Input where
  | scrollTo (y : Nat)
  | resize (h : Nat)
  | frame (f : LayerFrame)
  | vsync
  deriving Repr, DecidableEq

/-- What the presenter does: composite frame `frameId` at `offset` (the only GPU work it
starts), or ask the engine for the band around `scroll` (latest request wins). -/
inductive Output where
  | present (frameId offset : Nat)
  | needBand (scroll : Nat)
  deriving Repr, DecidableEq

/-- The composite offset: the band row at the top of the view, inside the band. The same
arithmetic as `clampOffset` in `layer_compositor.ts` (natural subtraction is its `max 0`), which
this replaces: the host no longer computes it. -/
def offsetOf (f : LayerFrame) (view scroll : Nat) : Nat :=
  min (f.bandHeight - view) (scroll - f.bandTop)

/-- The frame shows this scroll with no engine work. -/
def keeps (f : LayerFrame) (scroll : Nat) : Bool :=
  decide (f.keepFrom ≤ scroll) && decide (scroll ≤ f.keepTo)

/-- Ask for a band around `y` unless that request is already outstanding. -/
def ask (s : State) (y : Nat) : State × List Output :=
  if s.asked = some y then (s, []) else ({s with asked := some y}, [.needBand y])

/-- One presenter step. -/
def step (s : State) : Input → State × List Output
  | .scrollTo y =>
    let s := {s with scroll := y}
    match s.shown with
    | some f => if keeps f y then (s, []) else ask s y
    | none => ask s y
  | .resize h => ask {s with view := h, asked := none} s.scroll
  | .frame f =>
    match s.shown with
    | some g => if g.id < f.id then ({s with shown := some f}, []) else (s, [])
    | none => ({s with shown := some f}, [])
  | .vsync =>
    match s.shown with
    | some f => (s, [.present f.id (offsetOf f s.view s.scroll)])
    | none => (s, [])

/-- Run a trace of inputs; the outputs in order. -/
def run (s : State) : List Input → State × List Output
  | [] => (s, [])
  | i :: is =>
    let (s', o) := step s i
    let (s'', os) := run s' is
    (s'', o ++ os)

/-! ## Proved now -/

/-- Kind: cost. Says: a scroll the shown frame keeps needs no engine work and asks nothing:
the presenter answers it alone, however long the engine's current turn is. -/
theorem step_scroll_kept (s : State) (f : LayerFrame) (y : Nat)
    (hs : s.shown = some f) (hk : keeps f y = true) :
    step s (.scrollTo y) = ({s with scroll := y}, []) := by
  simp [step, hs, hk]

/-- Kind: property. Says: the composite offset stays inside the band (never reads past the
page layer's texture). -/
theorem offsetOf_le (f : LayerFrame) (view scroll : Nat) :
    offsetOf f view scroll ≤ f.bandHeight - view := Nat.min_le_left _ _

/-- Asking the engine leaves the shown frame alone. -/
theorem ask_shown (s : State) (y : Nat) : (ask s y).1.shown = s.shown := by
  unfold ask; split <;> rfl

/-- Kind: property. Says: the frame shown never goes back to an older one (frames that arrive
out of order are dropped). -/
theorem step_shown_mono (s : State) (i : Input) (g : LayerFrame) (hs : s.shown = some g) :
    ∃ f, (step s i).1.shown = some f ∧ g.id ≤ f.id := by
  cases i with
  | scrollTo y =>
    refine ⟨g, ?_, Nat.le_refl _⟩
    by_cases hk : keeps g y = true
    · simp [step, hs, hk]
    · simp [step, hs, hk, ask_shown]
  | resize h => exact ⟨g, by simp [step, ask_shown, hs], Nat.le_refl _⟩
  | frame f =>
    by_cases hlt : g.id < f.id
    · exact ⟨f, by simp [step, hs, hlt], Nat.le_of_lt hlt⟩
    · exact ⟨g, by simp [step, hs, hlt], Nat.le_refl _⟩
  | vsync => exact ⟨g, by simp [step, hs], Nat.le_refl _⟩

/-- Kind: property. Says: a display tick presents exactly the shown frame at its offset, and
changes no state (presenting is not a decision). -/
theorem step_vsync (s : State) (f : LayerFrame) (hs : s.shown = some f) :
    step s .vsync = (s, [.present f.id (offsetOf f s.view s.scroll)]) := by
  simp [step, hs]

/-- Kind: property. Says: the presenter never asks twice for the same band in a row. -/
theorem ask_once (s : State) (y : Nat) : (ask (ask s y).1 y).2 = [] := by
  unfold ask; split <;> simp_all

/-! ## Channels between the presenter and the engine (stated; each host proves or tests its
mailbox against these). -/

/-- The engine-to-presenter frame slot: a read gets the newest frame posted before it (older
ones may be skipped, never reordered). -/
def LatestWins (posted : List LayerFrame) (read : Option LayerFrame) : Prop :=
  read = posted.getLast?

/-- The presenter-to-engine request slot: the engine eventually sees the last `needBand` sent;
earlier ones may be dropped. Same shape as `LatestWins`. -/
def LastRequestSeen (sent : List Nat) (seen : Option Nat) : Prop :=
  seen = sent.getLast?

/-- A host's mailbox implements the channels: every frame read is `LatestWins` of the frames
posted so far, and the engine's view of requests is `LastRequestSeen`. Stage 1 (Deno worker plus
main thread) and stage 2 (`native_window.m` present thread) each discharge this; with `step`
shared, their presented outputs then agree on every interleaving the mailbox allows. -/
structure Mailbox (postedAt : Nat → List LayerFrame) (readAt : Nat → Option LayerFrame)
    (sentAt : Nat → List Nat) (seenAt : Nat → Option Nat) : Prop where
  frames : ∀ t, LatestWins (postedAt t) (readAt t)
  requests : ∀ t, LastRequestSeen (sentAt t) (seenAt t)

/-! ## Synchronous stage-0 model

This model makes a requested band before it takes the next external input. It has its own
transition definition; the refinement below relates it to the presenter's input trace.
-/

/-- External events of the synchronous host; completed frames are internal to that host. -/
inductive SyncInput where
  | scrollTo (y : Nat)
  | resize (h : Nat)
  | vsync
  deriving Repr, DecidableEq

/-- The presenter's corresponding external input. -/
def SyncInput.toInput : SyncInput → Input
  | .scrollTo y => .scrollTo y
  | .resize h => .resize h
  | .vsync => .vsync

/-- One synchronous turn, including the frame inputs which happened during it. -/
structure SyncTurn where
  state : State
  outputs : List Output
  frames : List Input

/-- A synchronous producer returns a frame newer than the frame on screen, if any.
This is an assumption on the engine's id assignment, not on page content. -/
def FreshEngine (engine : State → Nat → LayerFrame) : Prop :=
  ∀ s y g, s.shown = some g → g.id < (engine s y).id

/-- The synchronous host fulfils a new request immediately. It retains the specification's
request suppression, including the remembered request after its answer. -/
def stage0Request (engine : State → Nat → LayerFrame) (s : State) (y : Nat) : SyncTurn :=
  if s.asked = some y then ⟨s, [], []⟩ else
    let f := engine s y
    ⟨{s with asked := some y, shown := some f}, [.needBand y], [.frame f]⟩

/-- Independent stage-0 transition: scroll/resize can synchronously draw a band; a display
tick composites the frame on screen. The renderer is the parameter `engine`. -/
def stage0Step (engine : State → Nat → LayerFrame) (s : State) : SyncInput → SyncTurn
  | .scrollTo y =>
    let next := {s with scroll := y}
    match s.shown with
    | some f => if keeps f y then ⟨next, [], []⟩ else stage0Request engine next y
    | none => stage0Request engine next y
  | .resize h => stage0Request engine {s with view := h, asked := none} s.scroll
  | .vsync =>
    match s.shown with
    | some f => ⟨s, [.present f.id (offsetOf f s.view s.scroll)], []⟩
    | none => ⟨s, [], []⟩

/-- Run the synchronous host directly, collecting its observable outputs. -/
def stage0Run (engine : State → Nat → LayerFrame) (s : State) : List SyncInput → State × List Output
  | [] => (s, [])
  | i :: inputs =>
    let t := stage0Step engine s i
    let rest := stage0Run engine t.state inputs
    (rest.1, t.outputs ++ rest.2)

/-- Expand a synchronous execution to presenter inputs. The answer to a request precedes the
next external input; no timing or scheduler assumption is hidden in this expansion. -/
def synchronousInputs (engine : State → Nat → LayerFrame) (s : State) : List SyncInput → List Input
  | [] => []
  | i :: inputs =>
    let t := stage0Step engine s i
    i.toInput :: (t.frames ++ synchronousInputs engine t.state inputs)

/-- Kind: refinement. Says: running two traces in sequence concatenates their outputs.
Does not say: an arbitrary reordering of inputs preserves outputs. -/
theorem run_append (s : State) (xs ys : List Input) :
    run s (xs ++ ys) =
      let first := run s xs
      let second := run first.1 ys
      (second.1, first.2 ++ second.2) := by
  induction xs generalizing s with
  | nil => simp [run]
  | cons i xs ih => simp [run, ih, List.append_assoc]

/-- Kind: property. Says: a fresh completed frame replaces the shown frame without output.
Does not say: the frame's pixels agree with the layout or the requested scroll. -/
theorem step_fresh_frame (s : State) (f : LayerFrame)
    (fresh : ∀ g, s.shown = some g → g.id < f.id) :
    step s (.frame f) = ({s with shown := some f}, []) := by
  cases hs : s.shown with
  | none => simp [step, hs]
  | some g => simp [step, hs, fresh g hs]

/-- Kind: refinement. Says: immediate fulfilment of a synchronous request is its `ask`
followed by delivery of the completed frame. Does not say: the concrete engine is synchronous. -/
theorem stage0Request_refines (engine : State → Nat → LayerFrame) (fresh : FreshEngine engine)
    (s : State) (y : Nat) :
    let t := stage0Request engine s y
    let a := ask s y
    let r := run a.1 t.frames
    (r.1, a.2 ++ r.2) = (t.state, t.outputs) := by
  by_cases h : s.asked = some y
  · simp [stage0Request, ask, h, run]
  · simp only [stage0Request, ask, h, ↓reduceIte]
    rw [run, step_fresh_frame _ _ (fun g hg => fresh s y g hg)]
    simp [run]

/-- Kind: refinement. Says: a synchronous stage-0 turn equals the presenter on its expanded
input-and-frame trace. Does not say: either host implementation or raster is proved. -/
theorem stage0Step_refines (engine : State → Nat → LayerFrame) (fresh : FreshEngine engine)
    (s : State) (i : SyncInput) :
    let t := stage0Step engine s i
    run s (i.toInput :: t.frames) = (t.state, t.outputs) := by
  cases i with
  | scrollTo y =>
    cases hs : s.shown with
    | none => simpa [stage0Step, SyncInput.toInput, run, step, hs] using
        stage0Request_refines engine fresh {s with scroll := y} y
    | some f =>
      by_cases hk : keeps f y = true
      · simp [stage0Step, SyncInput.toInput, run, step, hs, hk]
      · simpa [stage0Step, SyncInput.toInput, run, step, hs, hk] using
          stage0Request_refines engine fresh {s with scroll := y} y
  | resize h => simpa [stage0Step, SyncInput.toInput, run, step] using
      stage0Request_refines engine fresh {s with view := h, asked := none} s.scroll
  | vsync => cases hs : s.shown <;> simp [stage0Step, SyncInput.toInput, run, step, hs]

/-- Kind: refinement. Says: with a synchronous fresh-frame engine, `run` presents exactly
what the independent stage-0 model presents, and ends in the same state. Every requested
frame arrives before the next external input in `synchronousInputs`.
Does not say: JavaScript, FFI, pixels, wall-clock latency or asynchronous schedules are proved. -/
theorem run_synchronous_eq_stage0 (engine : State → Nat → LayerFrame)
    (fresh : FreshEngine engine) (s : State) (inputs : List SyncInput) :
    run s (synchronousInputs engine s inputs) = stage0Run engine s inputs := by
  induction inputs generalizing s with
  | nil => rfl
  | cons i inputs ih =>
    rw [synchronousInputs, show i.toInput :: ((stage0Step engine s i).frames ++
        synchronousInputs engine (stage0Step engine s i).state inputs) =
        (i.toInput :: (stage0Step engine s i).frames) ++
          synchronousInputs engine (stage0Step engine s i).state inputs from rfl]
    rw [run_append, stage0Step_refines engine fresh]
    simp only [ih, stage0Run]

/-- Kind: property. Says: publishing a frame last makes that frame the latest-wins value.
Does not say: a concrete shared-memory read is atomic or linearises at publication. -/
theorem latestWins_append (posted : List LayerFrame) (f : LayerFrame) :
    LatestWins (posted ++ [f]) (some f) := by
  simp [LatestWins]

/-- Kind: property. Says: publishing a request last makes it the last-request-seen value.
Does not say: the host eventually schedules a reader; fairness is external to this list model. -/
theorem lastRequestSeen_append (sent : List Nat) (y : Nat) :
    LastRequestSeen (sent ++ [y]) (some y) := by
  simp [LastRequestSeen]

#print axioms run_append
#print axioms step_fresh_frame
#print axioms stage0Request_refines
#print axioms stage0Step_refines
#print axioms run_synchronous_eq_stage0
#print axioms latestWins_append
#print axioms lastRequestSeen_append

/-! ## Tests -/

private def f1 : LayerFrame := ⟨1, 0, 3000, 0, 2200⟩
private def f2 : LayerFrame := ⟨2, 2000, 3000, 2000, 4200⟩
private def s0 : State := {view := 800, scroll := 0}

private def synchronousTestEngine (s : State) (y : Nat) : LayerFrame :=
  ⟨(s.shown.map LayerFrame.id).getD 0 + 1, y, s.view + 2200, y, y + 2200⟩

-- The freshness hypothesis is inhabited for every state, including a shown frame.
private theorem synchronousTestEngine_fresh : FreshEngine synchronousTestEngine := by
  intro s y g h
  simp [synchronousTestEngine, h]

#guard (stage0Run synchronousTestEngine s0
  [.scrollTo 0, .vsync, .scrollTo 1500, .vsync, .scrollTo 2500, .vsync]).2 ==
  [.needBand 0, .present 1 0, .present 1 1500, .needBand 2500, .present 2 0]
#guard run s0 (synchronousInputs synchronousTestEngine s0
  [.scrollTo 0, .vsync, .resize 900, .vsync]) ==
  stage0Run synchronousTestEngine s0 [.scrollTo 0, .vsync, .resize 900, .vsync]

-- a scroll inside the kept range: presented at the next tick with no engine request
#guard (run s0 [.frame f1, .scrollTo 1500, .vsync]).2 == [.present 1 1500]
-- past the range: one request, the old frame still presented (clamped to the band's end)
#guard (run s0 [.frame f1, .scrollTo 2500, .scrollTo 2500, .vsync]).2 == [.needBand 2500, .present 1 2200]
-- the new band arrives; an older frame arriving late is dropped
#guard (run s0 [.frame f1, .scrollTo 2500, .frame f2, .frame f1, .vsync]).2 == [.needBand 2500, .present 2 500]
-- same arithmetic as clampOffset: scroll above the band gives 0
#guard offsetOf f2 800 100 == 0

end L4Factoidal.Presenter
