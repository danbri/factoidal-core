import FoafPresentation

/- The C bridge retains this Lean value, opaque to JavaScript. Candidate and
approved state never round-trip through caller-editable JSON. Only admitted
geometry (or the empty-node placeholder after invalidation) leaves this API. -/
namespace NativeFoafLiveBridge
open L4Factoidal.JSON L4Factoidal.UI
open NativeFoafNaut NativeFoafPresentation

structure Engine where
  session : Session
  prepared : Json

abbrev Live := Except String Engine

/-- Invalid transport input reports an error without destroying the last
valid controller state. The C holder only follows this Lean decision. -/
@[export foafnaut_live_commit]
def commit (previous proposed : Live) : Live :=
  match proposed with
  | .ok session => .ok session
  | .error _ => previous

private def clock (wire : String) : Except String Nat := do
  if wire.isEmpty || wire.length > 16 || !wire.toList.all Char.isDigit then
    throw "invalid monotonic millisecond clock"
  let some now := wire.toNat? | throw "invalid monotonic millisecond clock"
  if now > 9007199254740991 then throw "clock exceeds exact host integer range"
  return now

private def statusName : Presentation.Status → String
  | .accepted => "accepted"
  | .rejected => "rejected"
  | .deferred => "deferred"
  | .clockWentBack => "clockWentBack"

private def replace (object : Json) (name : String) (value : Json) : Json :=
  match object with
  | .object fields => .object (fields.map fun (key,old) => (key,if key == name then value else old))
  | _ => object

private def natJson (n : Nat) : Json := .number (toString n)

private def prepare (session : Session) : Json :=
  let displayed := { (shown session).getD (blankModel session) with policy := session.cfg }
  let report := replace (displayed.layoutReport true) "timing"
    (.string "live admission; retained approved geometry; no callback-liveness claim")
  responseJson displayed [] true none false (some report)

-- Admission changes the render token whenever its offered scene or viewport
-- changes. Geometry and diagnostics are prepared once per offer, not on every
-- input, deferred retry, or acknowledgment. This cache stays inside Lean.
private def update (engine : Engine) (session : Session) : Engine :=
  {session,prepared:=if session.renderToken == engine.session.renderToken
    then engine.prepared else prepare session}

def frame (engine : Engine) (shader : Bool) : Json :=
  let session := engine.session
  let available := (shown session).isSome
  let base := replace engine.prepared "commands" (.array (session.commands.map Json.string))
  -- Effects and the animation clock follow pending input state. Draw buffers,
  -- selected labels and the public model describe the displayed state only.
  let base := replace base "animating" (.bool session.candidate.animating)
  let base := replace base "closed" (.bool session.candidate.closed)
  let base := replace base "dragging" (.bool session.candidate.dragging)
  match base with
  | .object fields => .object ((fields.filter fun (key,_) => shader || key != "wgsl") ++
      (session.clipboardWrite.toList.map fun text => ("clipboardWrite",.string text)) ++
      (if session.clipboardRead then [("clipboardRead",.bool true)] else []) ++ [("presentation",.object [
      ("abi",.string "lean-foafnaut-live-v1"),
      ("available",.bool available),("status",.string (statusName session.status)),
      ("renderToken",natJson session.renderToken),
      ("candidateRevision",natJson session.candidate.revision),
      ("lastCheckMs",session.presentation.lastCheckMs.map natJson |>.getD .null),
      ("targetIntervalMs",natJson (PolicyProtocol.targetIntervalMs session.cfg))])])
  | _ => base

@[export foafnaut_live_create]
def createResponse (rdf : String) (width height : UInt32) (policy time : String) : Live := do
  let now ← clock time
  let cfg ← if policy.isEmpty then pure LayoutPolicy.defaultConfig else PolicyProtocol.readConfigText policy
  let graph ← FoafGraph.fromTurtle rdf none graphLimits
  if graph.people.isEmpty then throw "No FOAF people or resource-valued foaf:knows links found"
  let session := create graph width.toNat height.toNat cfg now
  return {session,prepared:=prepare session}

@[export foafnaut_live_transition]
def transitionResponse (live : Live) (kind : UInt32) (a b : Int32) (time : String) : Live := do
  let engine ← live
  let now ← clock time
  return update engine (step engine.session kind.toNat a.toInt b.toInt now)

@[export foafnaut_live_insert]
def insertResponse (live : Live) (text time : String) : Live := do
  let engine ← live
  let now ← clock time
  if text.toList.any (fun c => c.toNat == 0) then
    throw "invalid committed text input"
  return update engine (insert engine.session text now)

@[export foafnaut_live_present]
def presentResponse (live : Live) (time : String) : Live := do
  let engine ← live
  let now ← clock time
  return update engine (present engine.session now)

@[export foafnaut_live_ack]
def acknowledgeResponse (live : Live) (token : String) : Live := do
  let engine ← live
  let value ← clock token
  return update engine (acknowledge engine.session value)

@[export foafnaut_live_frame]
def frameResponse (live : Live) (shader : UInt8) : String :=
  toStringCompact (match live with
    | .error error => .object [("error",.string error)]
    | .ok session => frame session (shader != 0))

@[export foafnaut_live_svg]
def svgResponse (live : Live) : String :=
  match live with
  | .error error => toStringCompact (.object [("error",.string error)])
  | .ok engine =>
    let session := engine.session
    match session.presentation.shown with
    | none => "{\"error\":\"no approved frame is available\"}"
    | some approved =>
      match NativeSceneSVG.serialize approved.scene.scene with
      | .error error => toStringCompact (.object [("error",.string error)])
      | .ok svg =>
        let displayed := {approved.scene with policy := session.cfg}
        toStringCompact (.object [("svg",.string svg),("checked",.bool true),
          ("width",natJson displayed.width),("height",natJson displayed.height),
          ("layout",displayed.layoutReport true)])

end NativeFoafLiveBridge
