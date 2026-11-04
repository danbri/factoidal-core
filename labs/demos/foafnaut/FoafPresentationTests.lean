import FoafPresentationProofs

namespace NativeFoafPresentation.Tests
open NativeFoafNaut NativeFoafPresentation L4Factoidal.UI.LayoutPolicy
private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
private def atShown (s : Session) (i : Nat) : Option Position := (shown s).map (·.positions[i]!)

def tests (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  let graph ← match FoafGraph.fromTurtle text none graphLimits with
    | .error e => throw (IO.userError e) | .ok graph => pure graph
  check (graph.people.size >= 2) "RDF fixture must contain at least two people"
  let fresh := create graph 1000 700 defaultConfig 1000
  check ((pick fresh 500 350).isNone && (displayed fresh).isNone) "unsubmitted initial frame acquired pointer"
  let ignoredFresh := step fresh 2 500 350 1001
  check (ignoredFresh.candidate.selection == 0 && !ignoredFresh.candidate.dragging) "click before first host acknowledgment"
  let s := acknowledge fresh fresh.renderToken
  check (s.status == .accepted && (shown s).isSome) "initial RDF scene admission"
  check (fresh.commands == ["render","startClock"] && s.commands.isEmpty) "initial/ack effects"
  check ((pick s 500 350).map (·.target) == some (.person 0 0)) "shown body pick"
  let pressed := step s 2 500 350 1001
  check (pressed.candidate.dragging && pressed.candidate.selection == 1) "visible person capture"
  check (pressed.status == .deferred && shown pressed == shown s && !pressed.commands.contains "render") "deferred capture leaked rendering"
  let target := s.candidate.positions[1]!
  let bad := step pressed 3 target.x target.y 1002
  check (bad.candidate.positions[0]! == target && shown bad == shown s) "pending drag/certified retention"
  let rejected := present bad 1084
  check (rejected.status == .rejected && shown rejected == shown s && !rejected.commands.contains "render") "overlapping drag was shown"
  IO.println "PASS actual RDF deferred/rejected drag retains certified scene"

  let clicked := step rejected 2 500 350 1085
  check (clicked.candidate.selection == 1 && clicked.candidate.dragging) "click did not use visible body"
  check (clicked.candidate.positions[0]! == s.candidate.positions[0]!) "pointer down retained rejected geometry"
  check (clicked.candidate.revision > rejected.candidate.revision) "visible click rolled revision backwards"
  let recovered := present clicked 1168
  check (recovered.status == .accepted && recovered.commands.contains "render" && atShown recovered 0 == some s.candidate.positions[0]!) "pending candidate did not recover"
  IO.println "PASS shown click semantics, revision fence and independent cadence recovery"

  let safeMove := step pressed 3 600 350 1002
  let offered := present safeMove 1084
  check (offered.status == .accepted && atShown offered 0 == some ⟨600,350⟩) "new approved offer"
  check ((displayed offered).map (·.positions[0]!) == some ⟨500,350⟩ &&
    (pick offered 500 350).map (·.target) == some (.person 0 0)) "unsubmitted offer changed hit geometry"
  let stale := acknowledge offered s.renderToken
  check ((displayed stale).map (·.positions[0]!) == some ⟨500,350⟩) "stale render token changed acknowledgment"
  let submitted := acknowledge offered offered.renderToken
  check ((displayed submitted).map (·.positions[0]!) == some ⟨600,350⟩ &&
    (pick submitted 600 350).map (·.target) == some (.person 0 0)) "current render acknowledgment did not switch picks"
  IO.println "PASS explicit host acknowledgment and stale-token refusal"

  let resized := step s 1 800 600 1001
  check (resized.status == .deferred && (shown resized).isNone && resized.commands.contains "render") "resize did not clear old geometry"
  check ((displayed resized).isNone) "resize retained submitted pointer geometry"
  check (resized.presentation.lastCheckMs == some 1000) "resize reset global timestamp"
  check ((blankModel resized).footprints.isEmpty && (blankModel resized).scene.shapes.length == resized.candidate.scene.shapes.length) "blank graph/shape topology"
  let ignored := step resized 2 400 300 1002
  check (ignored.candidate.selection == resized.candidate.selection && !ignored.candidate.dragging && (pick ignored 400 300).isNone) "blank click acquired hidden candidate target"
  let backwards := present resized 999
  check (backwards.status == .clockWentBack && (shown backwards).isNone && backwards.presentation.lastCheckMs == some 1000) "context rollback not flagged"
  check ((present resized 1084).status == .accepted) "resized scene failed next-due recovery"
  let initialBlank := create graph 16 16 defaultConfig 1000
  check ((shown initialBlank).isNone && initialBlank.commands == ["render","startClock"]) "initial rejection must clear/start retries"
  IO.println "PASS resize invalidation, blank pointer refusal and global clock rollback"

  let editing := step s 5 37 2 1001
  check (editing.candidate.editing && shown editing == shown s) "deferred editor exposed candidate"
  let copied := step editing 5 8 2 1002
  check (copied.clipboardWrite == some s.candidate.address && shown copied == shown s) "clipboard effect lost or editor geometry leaked"
  let pasted := step copied 5 9 2 1003
  check (pasted.clipboardRead && shown pasted == shown s) "paste effect lost or geometry leaked"
  let inserted := insert pasted "typed pending text" 1004
  check (inserted.candidate.address == "typed pending text" && shown inserted == shown s && !inserted.commands.contains "render") "text insertion exposed unapproved frame"
  let oversized := insert inserted (String.ofList (List.replicate 65537 'x')) 1005
  check (oversized.candidate.address == inserted.candidate.address && oversized.candidate.message == "Clipboard too large - limit 65536 Unicode scalars") "oversized clipboard poisoned edits"
  let retried := present oversized 1084
  check (retried.clipboardWrite.isNone && !retried.clipboardRead) "clipboard effect replayed on retry"
  IO.println "PASS clipboard/editor effects stay separate from admitted geometry"

  let tight : Config := ⟨⟨300,500,12,12,by decide⟩,300,12,by decide⟩
  let fixed := create graph 1000 700 tight 1000
  let reset := step fixed 5 15 0 1001
  check (reset.candidate.policy == tight) "reset replaced fixed session config"
  let closed := step s 6 0 0 1001
  check (closed.candidate.closed && closed.commands == ["close"]) "close effect"
  let quiet := present closed 100000
  check (quiet.commands.isEmpty && quiet.presentation.lastCheckMs == closed.presentation.lastCheckMs) "closed session kept checking"
  check ((step closed 2 500 350 1002).candidate.closed) "shown click resurrected closed session"
  IO.println "PASS fixed policy and terminal closed-session quiescence"
end NativeFoafPresentation.Tests

#eval NativeFoafPresentation.Tests.tests "../../labs/demos/foafnaut/foaf/fixtures/people.ttl"
