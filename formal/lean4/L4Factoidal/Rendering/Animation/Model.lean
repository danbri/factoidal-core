/-
L4Factoidal.Rendering.Animation.Model: the playback of one animation (Web Animations 1
§4.4 "animations"): start time, hold time, playback rate, pending play and pause tasks,
and the procedures `play`, `pause`, `finish`, `cancel`, `reverse`, setting the current
time, the start time and the playback rate, and "update an animation's finished state".

Each procedure is a function of the player, the timeline time (`none`: no timeline, or an
inactive one) and the end time of the associated effect. What a procedure does to the
animation's promises and which events it queues are `Act`s in the player's outbox
(`out`), in order: the page's script objects apply them, so the decisions are here.

Theorems: `cancel` makes the animation idle (`cancel_idle`); a paused animation's current
time does not depend on the timeline time (`hold_fixed`); the play state `idle` is
exactly "no current time, no start time, nothing pending" (`idle_iff`); after `finish`
with a positive rate and a finite effect end the current time is the effect end
(`finish_at_end`).
-/
import L4Factoidal.Rendering.Animation.Timing

namespace L4Factoidal.Rendering.Animation
open Fix (one)

inductive Pending where
  | none | play | pause
  deriving DecidableEq, Repr, Inhabited

inductive PlayState where
  | idle | running | paused | finished
  deriving DecidableEq, Repr, Inhabited

def PlayState.toText : PlayState → String
  | .idle => "idle" | .running => "running" | .paused => "paused" | .finished => "finished"

/-- What a procedure did to the animation's promises and events, for the script objects. -/
inductive Act where
  /-- The current ready promise is a new pending promise. -/
  | readyNew
  | readyResolve
  /-- The current ready promise is rejected (AbortError) and replaced by a resolved one. -/
  | readyReject
  /-- The current finished promise is a new pending promise. -/
  | finishedNew
  | finishedResolve
  /-- The current finished promise is rejected (AbortError) and replaced by a new one. -/
  | finishedReject
  /-- Queue a microtask that runs the finish notification steps. -/
  | notify
  /-- Queue an animation playback event: type, current time, timeline time. -/
  | event (type : String) (currentTime timelineTime : Option Int)
  deriving DecidableEq, Repr, Inhabited

structure Player where
  startTime : Option Int := none
  holdTime : Option Int := none
  rate : Int := one
  pendingRate : Option Int := none
  pending : Pending := .none
  prevCurrentTime : Option Int := none
  /-- The current ready promise is pending. -/
  readyPending : Bool := false
  /-- The current finished promise is resolved. -/
  finishedResolved : Bool := false
  /-- A microtask for the finish notification steps is queued. -/
  notifyQueued : Bool := false
  /-- Acts not yet applied by the script objects, oldest first. -/
  out : List Act := []
  deriving DecidableEq, Repr, Inhabited

namespace Player

def emit (a : Player) (x : Act) : Player := { a with out := a.out ++ [x] }

/-- §4.4.3 the current time. -/
def currentTime (a : Player) (tl : Option Int) : Option Int :=
  match a.holdTime with
  | some h => some h
  | none =>
    match tl, a.startTime with
    | some t, some s => some (Fix.mul (t - s) a.rate)
    | _, _ => none

/-- §4.4.15.1 the effective playback rate. -/
def effRate (a : Player) : Int := a.pendingRate.getD a.rate

def applyPendingRate (a : Player) : Player :=
  match a.pendingRate with
  | some r => { a with rate := r, pendingRate := none }
  | none => a

/-- `c ≥ end`. -/
def atOrAfter (eff : Ext) (c : Int) : Bool := !eff.gtInt c

/-- The current time is at or past the end the effective playback rate runs to. -/
def atLimit (a : Player) (tl : Option Int) (eff : Ext) : Bool :=
  match a.currentTime tl with
  | some c => (a.effRate > 0 && atOrAfter eff c) || (a.effRate < 0 && c ≤ 0)
  | none => false

/-- §4.4.17 play states. -/
def playState (a : Player) (tl : Option Int) (eff : Ext) : PlayState :=
  if a.currentTime tl = none ∧ a.startTime = none ∧ a.pending = .none then .idle
  else if a.pending = .pause ∨ (a.startTime = none ∧ a.pending ≠ .play) then .paused
  else if a.atLimit tl eff then .finished
  else .running

/-- §4.4.14 finish notification steps. -/
def finishNotify (a : Player) (tl : Option Int) (eff : Ext) : Player :=
  let a := { a with notifyQueued := false }
  if a.playState tl eff != .finished || a.finishedResolved then a
  else ({ a with finishedResolved := true }.emit .finishedResolve).emit (.event "finish" (a.currentTime tl) tl)

/-- §4.4.14 update an animation's finished state. -/
def updateFinished (a : Player) (tl : Option Int) (eff : Ext) (didSeek sync : Bool) : Player :=
  let unconstrained := if didSeek then a.currentTime tl else ({ a with holdTime := none }).currentTime tl
  let a : Player := match unconstrained, a.startTime, a.pending with
    | some u, some _, .none =>
      if a.rate > 0 && atOrAfter eff u then
        match eff with
        | .fin e =>
          { a with holdTime := some (if didSeek then u else match a.prevCurrentTime with
              | some pv => max pv e
              | none => e) }
        | .inf => a
      else if a.rate < 0 && u ≤ 0 then
        { a with holdTime := some (if didSeek then u else match a.prevCurrentTime with
            | some pv => min pv 0
            | none => 0) }
      else if a.rate != 0 && tl.isSome then
        let a := match didSeek, a.holdTime, tl with
          | true, some h, some t => { a with startTime := some (t - (Fix.div h a.rate).getD 0) }
          | _, _, _ => a
        { a with holdTime := none }
      else a
    | _, _, _ => a
  let a := { a with prevCurrentTime := a.currentTime tl }
  let finished := a.playState tl eff == .finished
  if finished && !a.finishedResolved then
    if sync then a.finishNotify tl eff
    else if a.notifyQueued then a
    else { a with notifyQueued := true }.emit .notify
  else if !finished && a.finishedResolved then
    { a with finishedResolved := false }.emit .finishedNew
  else a

/-- A new pending ready promise, unless the current one is pending. -/
def newReady (a : Player) : Player :=
  if a.readyPending then a else { a with readyPending := true }.emit .readyNew

def resolveReady (a : Player) : Player :=
  if a.readyPending then { a with readyPending := false }.emit .readyResolve else a

/-- §4.4.8 play an animation; an error is the name of the exception. -/
def play (a : Player) (tl : Option Int) (eff : Ext) (autoRewind : Bool) : Except String Player := do
  let abortedPause := a.pending == .pause
  let ct := a.currentTime tl
  let er := a.effRate
  let seek : Option Int ←
    if er > 0 && autoRewind && (match ct with | none => true | some c => c < 0 || atOrAfter eff c) then pure (some 0)
    else if er < 0 && autoRewind && (match ct with | none => true | some c => c ≤ 0 || eff.gtInt c == false && (match eff with | .fin e => c > e | .inf => false)) then
      match eff with
      | .inf => throw "InvalidStateError"
      | .fin e => pure (some e)
    else if er == 0 && ct.isNone then pure (some 0)
    else pure none
  let a := match seek with
    | some s => { a with holdTime := some s }
    | none => a
  let a := if a.holdTime.isSome then { a with startTime := none } else a
  let hadPending := a.pending != .none
  let a := { a with pending := .none }
  if a.holdTime.isNone && seek.isNone && !abortedPause && a.pendingRate.isNone then
    -- nothing to do: a pending play task that was cancelled is scheduled again
    return (if hadPending then { a with pending := .play } else a)
  let a := if hadPending then a else a.newReady
  let a := { a with pending := .play, readyPending := true }
  return a.updateFinished tl eff false false

/-- §4.4.9 pause an animation. -/
def pause (a : Player) (tl : Option Int) (eff : Ext) : Except String Player := do
  if a.pending == .pause then return a
  if a.playState tl eff == .paused then return a
  let a ← match a.currentTime tl with
    | some _ => pure a
    | none =>
      if a.rate ≥ 0 then pure { a with holdTime := some 0 }
      else match eff with
        | .inf => throw "InvalidStateError"
        | .fin e => pure { a with holdTime := some e }
  let hadPlay := a.pending == .play
  let a := if hadPlay then a else a.newReady
  let a := { a with pending := .pause, readyPending := true }
  return a.updateFinished tl eff false false

/-- The pending play or pause task runs: the animation is ready at timeline time `t`
(§4.4.8 "pending play task", §4.4.9 "pending pause task"). -/
def ready (a : Player) (t : Int) (eff : Ext) : Player :=
  match a.pending with
  | .none => a
  | .play =>
    let a := match a.holdTime with
      | some h =>
        let a := a.applyPendingRate
        let newStart := if a.rate == 0 then t else t - (Fix.div h a.rate).getD 0
        let a := { a with startTime := some newStart }
        if a.rate != 0 then { a with holdTime := none } else a
      | none =>
        match a.startTime, a.pendingRate with
        | some s, some _ =>
          let toMatch := Fix.mul (t - s) a.rate
          let a := a.applyPendingRate
          if a.rate == 0 then { a with holdTime := some toMatch, startTime := some t }
          else { a with startTime := some (t - (Fix.div toMatch a.rate).getD 0) }
        | _, _ => a
    let a := { a with pending := .none }.resolveReady
    a.updateFinished (some t) eff false false
  | .pause =>
    let a := match a.startTime, a.holdTime with
      | some s, none => { a with holdTime := some (Fix.mul (t - s) a.rate) }
      | _, _ => a
    let a := a.applyPendingRate
    let a := { a with startTime := none, pending := .none }.resolveReady
    a.updateFinished (some t) eff false false

/-- §4.4.4 silently set the current time. -/
def silentlySetCurrentTime (a : Player) (tl : Option Int) (seek : Int) : Player :=
  let a := if a.holdTime.isSome || a.startTime.isNone || tl.isNone || a.rate == 0 then { a with holdTime := some seek }
    else match tl with
      | some t => { a with startTime := some (t - (Fix.div seek a.rate).getD 0) }
      | none => a
  let a := if tl.isNone then { a with startTime := none } else a
  { a with prevCurrentTime := none }

/-- §4.4.4 set the current time. Setting it to unresolved when it is resolved is a
TypeError. -/
def setCurrentTime (a : Player) (tl : Option Int) (eff : Ext) (seek : Option Int) : Except String Player :=
  match seek with
  | none => if (a.currentTime tl).isSome then .error "TypeError" else .ok a
  | some s =>
    let a := a.silentlySetCurrentTime tl s
    let a := if a.pending == .pause then
        let b := ({ a with holdTime := some s } : Player).applyPendingRate
        ({ b with startTime := none, pending := .none } : Player).resolveReady
      else a
    .ok (a.updateFinished tl eff true false)

/-- §4.4.5 set the start time. -/
def setStartTime (a : Player) (tl : Option Int) (eff : Ext) (new : Option Int) : Player :=
  let a := if tl.isNone && new.isSome then { a with holdTime := none } else a
  let previous := a.currentTime tl
  let a := a.applyPendingRate
  let a := { a with startTime := new }
  let a := match new with
    | some _ => if a.rate != 0 then { a with holdTime := none } else a
    | none => { a with holdTime := previous }
  let a := if a.pending != .none then { a with pending := .none }.resolveReady else a
  a.updateFinished tl eff true false

/-- §4.4.12 finish an animation. -/
def finish (a : Player) (tl : Option Int) (eff : Ext) : Except String Player := do
  let er := a.effRate
  if er == 0 || (er > 0 && eff == .inf) then throw "InvalidStateError"
  let a := a.applyPendingRate
  let limit : Int := if a.rate > 0 then (match eff with | .fin e => e | .inf => 0) else 0
  let a := a.silentlySetCurrentTime tl limit
  let a := match a.startTime, tl with
    | none, some t => { a with startTime := some (t - (Fix.div limit a.rate).getD 0) }
    | _, _ => a
  let a := if a.pending == .pause && a.startTime.isSome then
      { a with holdTime := none, pending := .none }.resolveReady
    else a
  let a := if a.pending == .play && a.startTime.isSome then { a with pending := .none }.resolveReady else a
  return a.updateFinished tl eff true true

/-- §4.4.10 reset an animation's pending tasks. -/
def resetPending (a : Player) : Player :=
  if a.pending == .none then a
  else
    let a := { a with pending := .none }.applyPendingRate
    { a with readyPending := false }.emit .readyReject

/-- §4.4.13 cancel an animation. -/
def cancel (a : Player) (tl : Option Int) (eff : Ext) : Player :=
  if a.playState tl eff = .idle then { a with holdTime := none, startTime := none }
  else
    let a := a.resetPending
    let a := ({ a with finishedResolved := false, notifyQueued := false }.emit .finishedReject).emit (.event "cancel" none tl)
    { a with holdTime := none, startTime := none, pending := .none }

/-- §4.4.15 set the playback rate (the `playbackRate` setter). -/
def setRate (a : Player) (tl : Option Int) (eff : Ext) (r : Int) : Player :=
  let previous := a.currentTime tl
  let a := { a with pendingRate := none, rate := r }
  match previous with
  | some p => (a.setCurrentTime tl eff (some p)).toOption.getD a
  | none => a

/-- §4.4.15.1 seamlessly update the playback rate (`updatePlaybackRate`). -/
def updateRate (a : Player) (tl : Option Int) (eff : Ext) (r : Int) : Except String Player := do
  let previous := a.playState tl eff
  let a := { a with pendingRate := some r }
  if a.pending != .none then return a
  match previous with
  | .idle | .paused => return a.applyPendingRate
  | .finished =>
    let unconstrained := ({ a with holdTime := none }).currentTime tl
    let a := match tl, unconstrained with
      | some t, some u => { a with startTime := some (if r == 0 then t else t - (Fix.div u r).getD 0) }
      | some t, none => if r == 0 then { a with startTime := some t } else a
      | none, _ => a
    return (a.applyPendingRate).updateFinished tl eff false false
  | .running => a.play tl eff false

/-- §4.4.16 reverse an animation. -/
def reverse (a : Player) (tl : Option Int) (eff : Ext) : Except String Player := do
  if tl.isNone then throw "InvalidStateError"
  let b := { a with pendingRate := some (-a.effRate) }
  b.play tl eff true

/-! ## Theorems -/

/-- Kind: characterisation (Web Animations 1 §4.4.17). Says: the play state is `idle`
exactly when the animation has no current time, no start time and no pending task. Does
not say: which of the other three states holds otherwise. -/
theorem idle_iff (a : Player) (tl : Option Int) (eff : Ext) :
    a.playState tl eff = .idle ↔ (a.currentTime tl = none ∧ a.startTime = none ∧ a.pending = .none) := by
  unfold playState
  constructor
  · intro h
    by_cases hc : a.currentTime tl = none ∧ a.startTime = none ∧ a.pending = .none
    · exact hc
    · rw [if_neg hc] at h
      split at h
      · cases h
      · split at h <;> cases h
  · intro hc
    rw [if_pos hc]

/-- Kind: effect of a procedure (Web Animations 1 §4.4.13). Says: after `cancel` the
animation is idle: no start time, no hold time, no pending task, whatever its state was
and whatever the timeline time is. Does not say: which promises were rejected (the acts
say that). -/
theorem cancel_idle (a : Player) (tl : Option Int) (eff : Ext) (tl' : Option Int) (eff' : Ext) :
    (a.cancel tl eff).playState tl' eff' = .idle := by
  rw [idle_iff]
  unfold cancel
  split
  · rename_i hi
    have := (idle_iff a tl eff).mp hi
    exact ⟨by cases tl' <;> simp [currentTime], rfl, this.2.2⟩
  · exact ⟨by cases tl' <;> simp [currentTime], rfl, rfl⟩

/-- Kind: independence. Says: an animation with a hold time (paused, or finished and
held) has that hold time as its current time at every timeline time. Does not say:
anything of an animation with no hold time, whose current time moves with the timeline. -/
theorem hold_fixed (a : Player) (h : Int) (hh : a.holdTime = some h) (tl : Option Int) :
    a.currentTime tl = some h := by
  simp [currentTime, hh]

/-- Kind: arithmetic of the current time (Web Animations 1 §4.4.3). Says: with no hold
time, a start time `s` and rate 1, the current time at timeline time `t` is `t - s`,
exactly. Does not say: anything for other rates, where the product is rounded to 10⁻⁹ ms. -/
theorem running_time (a : Player) (s t : Int) (hh : a.holdTime = none) (hs : a.startTime = some s)
    (hr : a.rate = one) : a.currentTime (some t) = some (t - s) := by
  simp [currentTime, hh, hs, hr, Fix.mul_one]

/-! ## Tests: the sequences of the interpolation tests and of web-animations/timing-model -/

private def ms (n : Int) : Int := Fix.ofInt n
private def eff100 : Ext := .fin (ms 100000)
private def get (r : Except String Player) : Player := r.toOption.getD {}

-- element.animate(): play at timeline time 10
private def p1 : Player := get (({} : Player).play (some (ms 10)) eff100 true)
#guard p1.pending == .play && p1.holdTime == some 0 && p1.startTime == none
#guard p1.playState (some (ms 10)) eff100 == .running
#guard p1.currentTime (some (ms 10)) == some 0
#guard p1.out == [.readyNew]
-- animation.pause() while the play is pending: one ready promise, hold time kept
private def p2 : Player := get (p1.pause (some (ms 10)) eff100)
#guard p2.pending == .pause && p2.out == [.readyNew] && p2.playState (some (ms 10)) eff100 == .paused
-- animation.currentTime = 50000 completes the pause
private def p3 : Player := get (p2.setCurrentTime (some (ms 10)) eff100 (some (ms 50000)))
#guard p3.pending == .none && p3.holdTime == some (ms 50000) && p3.startTime == none
#guard p3.out == [.readyNew, .readyResolve]
#guard p3.currentTime (some (ms 999)) == some (ms 50000)
#guard p3.playState (some (ms 999)) eff100 == .paused
-- a play becomes ready at the next frame: start time = ready time - hold time
private def p4 : Player := p1.ready (ms 26) eff100
#guard p4.startTime == some (ms 26) && p4.holdTime == none && p4.pending == .none
#guard p4.currentTime (some (ms 126)) == some (ms 100)
#guard p4.playState (some (ms 126)) eff100 == .running
-- the animation finishes when the timeline passes the end: hold at the end, notify
private def p5 : Player := p4.updateFinished (some (ms 100050)) eff100 false false
#guard p5.holdTime == some (ms 100000) && p5.playState (some (ms 100050)) eff100 == .finished
#guard p5.out == [.readyNew, .readyResolve, .notify]
private def p6 : Player := p5.finishNotify (some (ms 100050)) eff100
#guard p6.finishedResolved && p6.out.getLast? == some (.event "finish" (some (ms 100000)) (some (ms 100050)))
-- finish(): at once, synchronously
private def p7 : Player := get (p4.finish (some (ms 30)) eff100)
#guard p7.currentTime (some (ms 30)) == some (ms 100000) && p7.finishedResolved
-- seek back from finished: a new finished promise
private def p8 : Player := get (p7.setCurrentTime (some (ms 30)) eff100 (some 0))
#guard !p8.finishedResolved && p8.out.getLast? == some .finishedNew && p8.playState (some (ms 30)) eff100 == .running
-- cancel: rejected promises, idle
private def p9 : Player := p1.cancel (some (ms 10)) eff100
#guard p9.playState (some (ms 10)) eff100 == .idle && p9.currentTime (some (ms 10)) == none
#guard p9.out == [.readyNew, .readyReject, .finishedReject, .event "cancel" none (some (ms 10))]
-- reverse from the start: seeks to the end with rate -1 pending
private def p10 : Player := get (p4.reverse (some (ms 26)) eff100)
#guard p10.pendingRate == some (-one) && p10.holdTime == some (ms 100000) && p10.pending == .play
#guard (({} : Player).reverse none eff100).toOption.isNone
#guard (({ rate := -one } : Player).play (some 0) .inf true).toOption.isNone
#guard (({} : Player).finish (some 0) .inf).toOption.isNone
#guard (({ rate := 0 } : Player).finish (some 0) eff100).toOption.isNone
-- setting the start time
private def p11 : Player := p3.setStartTime (some (ms 100)) eff100 (some (ms 40))
#guard p11.currentTime (some (ms 100)) == some (ms 60) && p11.playState (some (ms 100)) eff100 == .running
-- updatePlaybackRate on a running animation keeps the current time when it becomes ready
private def p12 : Player := get (p4.updateRate (some (ms 126)) eff100 (2 * one))
#guard p12.pending == .play
#guard (p12.ready (ms 126) eff100).currentTime (some (ms 126)) == some (ms 100)
#guard (p12.ready (ms 126) eff100).currentTime (some (ms 136)) == some (ms 120)
-- the playbackRate setter keeps the current time
#guard (p4.setRate (some (ms 126)) eff100 (2 * one)).currentTime (some (ms 126)) == some (ms 100)
#guard ({} : Player).playState none eff100 == .idle
#guard (({} : Player).setCurrentTime none eff100 none).toOption.isSome
#guard (p3.setCurrentTime (some 0) eff100 none).toOption.isNone

end Player
end L4Factoidal.Rendering.Animation
