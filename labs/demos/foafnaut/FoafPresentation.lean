import FoafNaut

/- Pure live admission controller. The fixed session config is authoritative;
model config fields are normalized after every transition. Pointer-down bases
its transition on the last host-acknowledged approved model, discarding pending
unshown edits, with a revision fence against rollback. No acknowledged model means
no pointer target or clipboard action. Admission retries are independent of
the animation clock; no callback scheduling or Float/GPU equivalence claim. -/
namespace NativeFoafPresentation
open NativeFoafNaut L4Factoidal.UI.LayoutPolicy L4Factoidal.UI.Presentation

structure Session where
  cfg : Config
  candidate : Model
  candidatePolicy : candidate.policy = cfg
  presentation : State Model cfg Model.footprints
  status : Status
  acknowledged : Option (Approved Model cfg Model.footprints) := none
  renderToken : Nat := 0
  commands : List String := []
  clipboardWrite : Option String := none
  clipboardRead : Bool := false

def shown (s : Session) : Option Model := s.presentation.shown.map (·.scene)
def displayed (s : Session) : Option Model := s.acknowledged.map (·.scene)
def pick (s : Session) (x y : Int) : Option PaintedPart :=
  if s.candidate.closed then none else (displayed s).bind (·.pick x y)

-- A pipeline-compatible clearing frame, not an approved graph. Hidden graph
-- slots remain offscreen; chrome may draw but is never picked while unavailable.
def blankModel (s : Session) : Model :=
  {s.candidate with
    policy:=s.cfg,hidden:=Array.replicate s.candidate.graph.people.size true,
    selection:=0,dragging:=false,editing:=false,address:="",cursor:=0,anchor:=0,
    message:="Waiting for approved layout",animating:=false}

private def context (m : Model) : String := s!"foafnaut:{m.width}x{m.height}"
private def quiet (s : Session) : Session :=
  {s with commands:=[],clipboardWrite:=none,clipboardRead:=false}

-- The host calls this only after successful surface submission of this token.
-- It does not establish GPU completion or pixel equality. Stale acks cannot
-- approve a newer offer; an acknowledged blank has no pointer targets.
def acknowledge (s : Session) (token : Nat) : Session :=
  quiet {s with acknowledged:=if token == s.renderToken then s.presentation.shown else s.acknowledged}

theorem acknowledge_current (s : Session) :
    (acknowledge s s.renderToken).acknowledged = s.presentation.shown := by
  simp [acknowledge,quiet]

theorem acknowledge_stale (s : Session) (token : Nat) (stale : token ≠ s.renderToken) :
    (acknowledge s token).acknowledged = s.acknowledged := by
  simp [acknowledge,quiet,stale]

theorem acknowledge_preserves_token (s : Session) (token : Nat) :
    (acknowledge s token).renderToken = s.renderToken := by
  rfl

private def admit (s : Session) (result : Result) (now : Nat) : Session :=
  let candidate := {result.model with policy:=s.cfg}
  let effects := result.commands.filter (· != "render")
  if candidate.closed then
    {s with
      candidate,candidatePolicy:=rfl,commands:=effects,
      clipboardWrite:=result.clipboardWrite,clipboardRead:=result.clipboardRead}
  else
    let decision := submit s.cfg Model.footprints s.presentation (context candidate) now candidate
    let contextChanged := context candidate != s.presentation.context
    let changed := contextChanged || (decision.state.shown.map (·.scene)) != shown s
    {
      cfg:=s.cfg,candidate,candidatePolicy:=rfl,presentation:=decision.state,status:=decision.status,
      acknowledged:=if contextChanged then none else s.acknowledged,
      renderToken:=s.renderToken+(if changed then 1 else 0),
      commands:=(if changed then ["render"] else []) ++ effects,
      clipboardWrite:=result.clipboardWrite,clipboardRead:=result.clipboardRead}

-- Retry the pending candidate even when physics is paused. A closed session is
-- quiescent and does not continually recheck, render, or repeat clipboard effects.
def present (s : Session) (now : Nat) : Session :=
  if s.candidate.closed then quiet s else admit s {model:=s.candidate} now

def create (graph : FoafGraph.Data) (width height : Nat) (cfg : Config) (now : Nat) : Session :=
  let candidate := initial graph width height cfg
  let s : Session := {
    cfg,candidate,candidatePolicy:=rfl,
    presentation:={context:=context candidate},status:=.deferred}
  let admitted := admit s {model:=candidate,commands:=["startClock"]} now
  -- Initial rejection must actively clear a reused surface too.
  {admitted with renderToken:=1,commands:=["render","startClock"]}

def step (s : Session) (kind : Nat) (a b : Int) (now : Nat) : Session :=
  if s.candidate.closed then quiet s
  else if kind == 2 then
    match displayed s with
    | none => present s now
    | some visible =>
      let base := {visible with revision:=s.candidate.revision,policy:=s.cfg}
      let result := transitionModel base kind a b
      let model := {result.model with revision:=max result.model.revision (s.candidate.revision+1)}
      admit s {result with model} now
  else admit s (transitionModel s.candidate kind a b) now

def insert (s : Session) (text : String) (now : Nat) : Session :=
  if s.candidate.closed then quiet s
  else if text.length > 65536 then
    let model := {s.candidate with
      message:="Clipboard too large - limit 65536 Unicode scalars",
      revision:=s.candidate.revision+1}
    admit s {model} now
  else admit s (insertText s.candidate text) now

-- Empty graph footprint is deliberate clearing, not proof of a nonempty graph.
theorem blankModel_footprints (s : Session) : (blankModel s).footprints = [] := by
  have empty : (blankModel s).visibleDrawings = [] := by
    simp only [Model.visibleDrawings,blankModel,List.filterMap_eq_nil_iff]
    intro i member
    have bound := List.mem_range.mp member
    simp [bound]
  simp [Model.footprints,empty]

theorem blankModel_certifies (s : Session) : certify s.cfg (blankModel s).footprints = true := by
  rw [blankModel_footprints]
  rfl

private theorem admit_revision (s : Session) (result : Result) (now : Nat) :
    (admit s result now).candidate.revision = result.model.revision := by
  unfold admit
  dsimp only
  split <;> rfl

theorem pointer_down_revision (s : Session) (m : Model) (x y : Int) (now : Nat)
    (openSession : s.candidate.closed = false) (visible : displayed s = some m) :
    s.candidate.revision < (step s 2 x y now).candidate.revision := by
  simp only [step,openSession,Bool.false_eq_true,if_false,BEq.rfl,if_true,visible]
  rw [admit_revision]
  dsimp only
  omega

end NativeFoafPresentation
