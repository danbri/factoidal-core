import L4Factoidal.UI.Presentation

namespace L4Factoidal.UI.PresentationTests
open Geometry LayoutPolicy Presentation

private def cfg := defaultConfig
private def good : List (Option Box) := [some ⟨0,0,100,100⟩,some ⟨100,0,200,100⟩]
private def bad : List (Option Box) := [some ⟨0,0,100,100⟩,some ⟨0,0,100,100⟩]
private def initial : State (List (Option Box)) cfg id := {context:="viewport-a"}
private def first := submit cfg id initial "viewport-a" 1000 good

#guard first.status == .accepted
#guard first.state.shown.isSome
#guard (submit cfg id first.state "viewport-a" 1083 bad).status == .deferred
#guard (submit cfg id first.state "viewport-a" 1084 bad).status == .rejected
#guard (submit cfg id first.state "viewport-a" 1084 bad).state.shown.isSome
#guard (submit cfg id first.state "viewport-a" 1084 bad).state.shown.map (·.scene) == some good
#guard (submit cfg id first.state "viewport-a" 999 bad).status == .clockWentBack
#guard (submit cfg id first.state "viewport-b" 1001 bad).status == .deferred
#guard (submit cfg id first.state "viewport-b" 1001 bad).state.shown.isNone
#guard (submit cfg id first.state "viewport-b" 1001 good).status == .deferred
#guard (submit cfg id first.state "viewport-a" 100000000000 good).status == .accepted
#guard due cfg 1000 1084
#guard !due cfg 1000 1083
#guard !due cfg 1000 999

#guard (submit cfg id first.state "viewport-b" 1001 good).state.shown.isNone
#guard (submit cfg id first.state "viewport-b" 1001 good).state.lastCheckMs == some 1000
#guard (submit cfg id first.state "viewport-b" 999 good).status == .clockWentBack
#guard (submit cfg id first.state "viewport-b" 999 good).state.shown.isNone
#guard (submit cfg id first.state "viewport-b" 999 good).state.lastCheckMs == some 1000
#guard (submit cfg id first.state "viewport-b" 1084 good).status == .accepted
#guard (submit cfg id first.state "viewport-b" 1084 bad).status == .rejected
#guard (submit cfg id first.state "viewport-b" 1084 bad).state.shown.isNone
#guard (submit cfg id first.state "viewport-b" 1084 good).state.shown.map (·.scene) == some good
-- An empty every-node layout is valid; frequency is a ceiling on checking,
-- not evidence of a guaranteed minimum callback rate.
#guard (submit cfg id initial "viewport-a" 1000 []).status == .accepted
example (state : State (List (Option Box)) cfg id) (context : String) (now : Nat)
    (candidate : List (Option Box))
    (h : (submit cfg id state context now candidate).status = .accepted) :
    ∃ shown, (submit cfg id state context now candidate).state.shown = some shown ∧
      shown.scene = candidate ∧ LayoutAccepted cfg candidate :=
  submit_accepted_candidate cfg id state context now candidate h
end L4Factoidal.UI.PresentationTests
