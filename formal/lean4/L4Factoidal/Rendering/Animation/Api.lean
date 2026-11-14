/-
L4Factoidal.Rendering.Animation.Api: the Web Animations interfaces over the engine's
state (Web Animations 1 §6: `Animation`, `KeyframeEffect`, `Animatable.animate`,
`getAnimations`, `DocumentTimeline`), as text in and text out for the page's script
objects.

The page's objects hold only a number (the effect or the animation) and their promises.
Everything the specification decides is decided here: the conversion and checks of the
timing dictionaries (§6.5.3 "updating the timing of an AnimationEffect"), "processing a
keyframes argument" (§6.6.3), the playback procedures (`Model`), and the timing answers
(`getTiming`, `getComputedTiming`). A request is JSON; an answer is JSON; an error
answer is `{"error": name, "message": text}`, which the object throws as that
exception.
-/
import L4Factoidal.Rendering.Animation.Engine
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.Rendering.Animation.Api
open L4Factoidal.JSON (Json)
open L4Factoidal.Rendering.Animation
open L4Factoidal.Rendering

def err (name message : String) : String :=
  (Json.object [("error", .string name), ("message", .string message)]).toString

def jnum (x : Int) : Json := .number (Fix.format x)
def jopt : Option Int → Json
  | some x => jnum x
  | none => .null
def jext : Ext → Json
  | .fin x => jnum x
  | .inf => .string "Infinity"

/-- The text of a request member: a string as it is, a number as its text, none for
null or absent. -/
def member (j : Json) (key : String) : Option String :=
  match j.field? key with
  | some (.string s) => some s
  | some (.number n) => some n
  | some (.bool b) => some (if b then "true" else "false")
  | _ => none

/-! ## Timing dictionaries -/

def fillText : Fill → String
  | .none => "none" | .forwards => "forwards" | .backwards => "backwards" | .both => "both" | .auto => "auto"

def directionText : Direction → String
  | .normal => "normal" | .reverse => "reverse" | .alternate => "alternate" | .alternateReverse => "alternate-reverse"

/-- A finite number of a dictionary member (Web IDL `double`): `NaN` and the infinities
are a TypeError. -/
def finite (name text : String) : Except String Int :=
  match Fix.parse text with
  | some v => .ok v
  | none => .error s!"{name} must be a finite number"

/-- A number that may be `Infinity` and may not be negative or `NaN` (Web IDL
`unrestricted double`, with the range checks of §6.5.3). -/
def countOrInfinity (name text : String) : Except String Ext :=
  if text == "Infinity" then .ok .inf
  else match Fix.parse text with
    | some v => if v < 0 then .error s!"{name} must not be negative" else .ok (.fin v)
    | none => .error s!"{name} must be a number that is not negative"

/-- Web Animations 1 §6.5.3 "update the timing properties of an animation effect": the
members present in `opt` replace those of `base`; a value out of range is a TypeError
(the message). A duration is `n:` and a number, or `s:` and a string (only `auto`). -/
def timingOf (base : Timing) (opt : Json) : Except String Timing := do
  let mut t := base
  if let some v := member opt "delay" then t := { t with delay := ← finite "delay" v }
  if let some v := member opt "endDelay" then t := { t with endDelay := ← finite "endDelay" v }
  if let some v := member opt "fill" then
    t := { t with fill := ← match v with
      | "none" => pure Fill.none | "forwards" => pure .forwards | "backwards" => pure .backwards
      | "both" => pure .both | "auto" => pure .auto
      | _ => throw s!"'{v}' is not a valid fill mode" }
  if let some v := member opt "iterationStart" then
    let x ← finite "iterationStart" v
    if x < 0 then throw "iterationStart must not be negative"
    t := { t with iterationStart := x }
  if let some v := member opt "iterations" then t := { t with iterations := ← countOrInfinity "iterations" v }
  if let some v := member opt "duration" then
    if v == "s:auto" then t := { t with duration := none }
    else if v.startsWith "n:" then t := { t with duration := some (← countOrInfinity "duration" (v.drop 2).toString) }
    else throw "duration must be a number or 'auto'"
  if let some v := member opt "direction" then
    t := { t with direction := ← match v with
      | "normal" => pure Direction.normal | "reverse" => pure .reverse | "alternate" => pure .alternate
      | "alternate-reverse" => pure .alternateReverse
      | _ => throw s!"'{v}' is not a valid direction" }
  if let some v := member opt "easing" then
    match Easing.parse v with
    | some e => t := { t with easing := e }
    | none => throw s!"'{v}' is not a valid easing function"
  return t

/-- `getTiming()` (§6.5.2 `EffectTiming`). -/
def timingJson (t : Timing) : List (String × Json) :=
  [("delay", jnum t.delay), ("endDelay", jnum t.endDelay), ("fill", .string (fillText t.fill)),
   ("iterationStart", jnum t.iterationStart), ("iterations", jext t.iterations),
   ("duration", match t.duration with | none => .string "auto" | some d => jext d),
   ("direction", .string (directionText t.direction)), ("easing", .string t.easing.toText)]

/-- `getComputedTiming()` (§6.5.4 `ComputedEffectTiming`): `fill: auto` is `none`,
`duration: auto` is 0, with the end time, the active duration, the local time, the
progress and the current iteration. -/
def computedJson (t : Timing) (localTime : Option Int) (backwards : Bool) : List (String × Json) :=
  [("delay", jnum t.delay), ("endDelay", jnum t.endDelay), ("fill", .string (fillText t.fillOf)),
   ("iterationStart", jnum t.iterationStart), ("iterations", jext t.iterations),
   ("duration", jext t.iterationDuration),
   ("direction", .string (directionText t.direction)), ("easing", .string t.easing.toText),
   ("endTime", jext t.endTime), ("activeDuration", jext t.activeDuration), ("startTime", jnum 0),
   ("localTime", jopt localTime), ("progress", jopt (t.progress localTime backwards)),
   ("currentIteration", match t.currentIteration localTime backwards with
      | some (.fin n) => .number (toString n)
      | some .inf => .string "Infinity"
      | none => .null)]

/-! ## Keyframes -/

/-- The CSS property of an IDL attribute name of a keyframe (§6.6.3 "animation property
name to IDL attribute name", inverted): `cssFloat` is `float`, `cssOffset` is `offset`, a
custom property is itself, `marginLeft` is `margin-left`. A name with a dash that is not
a custom property, and `float` and `offset` themselves, name no property. -/
def cssName (idl : String) : Option String :=
  if idl.startsWith "--" then some idl
  else if idl == "cssFloat" then some "float"
  else if idl == "cssOffset" then some "offset"
  else if idl == "float" || idl == "offset" || idl == "easing" || idl == "composite" then none
  else if idl.any (· == '-') || idl.isEmpty then none
  else some (String.ofList (idl.toList.flatMap fun c => if c.isUpper then ['-', c.toLower] else [c]))

/-- The inverse, for `getKeyframes()`. -/
def idlName (css : String) : String :=
  if css.startsWith "--" then css
  else if css == "float" then "cssFloat"
  else if css == "offset" then "cssOffset"
  else Id.run do
    let mut out := ""
    let mut up := false
    for c in css.toList do
      if c == '-' then up := true
      else
        out := out.push (if up then c.toUpper else c)
        up := false
    return out

/-- §6.6.3 "process a keyframe-like object" step 5: which of the names (the own enumerable
names of a keyframe object, separated by U+0000) are animatable properties of this
engine or custom properties: "1" or "0" for each, in order. Only those are read from the
object. -/
def animatableNames (supports : String → String → Bool) (q : String) : String :=
  String.ofList ((q.splitOn "\x00").map fun idl =>
    match cssName idl with
    | some css => if css.startsWith "--" || (animatable css && supports css "initial") then '1' else '0'
    | none => '0')

/-- A keyframe's offset member: null, or a number in [0, 1]. -/
def offsetOf (j : Option Json) : Except String (Option Int) :=
  match j with
  | none | some .null => .ok none
  | some (.string s) | some (.number s) =>
    match Fix.parse s with
    | some v => if 0 ≤ v && v ≤ Fix.one then .ok (some v) else .error "a keyframe offset must be between 0 and 1"
    | none => .error "a keyframe offset must be a number"
  | _ => .error "a keyframe offset must be a number"

def compositeOf (text : Option String) : Except String (Option Composite) :=
  match text with
  | none | some "auto" => .ok none
  | some v => match Composite.parse v with
    | some c => .ok (some c)
    | none => .error s!"'{v}' is not a valid composite operation"

def easingOf (text : Option String) : Except String Easing :=
  match text with
  | none => .ok .linear
  | some v => match Easing.parse v with
    | some e => .ok e
    | none => .error s!"'{v}' is not a valid easing function"

/-- The property-value pairs of a keyframe: the names that are properties, with the
values the property takes (§6.6.3 step 8: "if the property value is invalid according to
the syntax for the property, discard the property-value pair"). The pair is the
longhands of the property table for it (`CssValues.expand`), and the pair as given for
`getKeyframes()`. -/
def pairsOf (supports : String → String → Bool) (ps : List (String × String)) :
    List (String × String) × List (String × String) :=
  ps.foldl (fun (props, shown) (idl, value) =>
    match cssName idl with
    | none => (props, shown)
    | some css =>
      if !supports css value then (props, shown)
      else
        let longs := if css.startsWith "--" then [(css, value)]
          else Css.expandDecl css value
        (longs.foldl (fun acc (k, v) => Css.setProp acc k v) props, shown ++ [(idl, value)])) ([], [])

def stringPairs (j : Option Json) : List (String × String) :=
  match j with
  | some (.array items) => items.filterMap fun it =>
      match it with
      | .array [.string k, .string v] => some (k, v)
      | _ => none
  | _ => []

/-- §6.6.3 for a sequence of keyframes: each with its offset, easing, composite and
pairs; the offsets must not go down ("loosely sorted"). -/
def listKeyframes (supports : String → String → Bool) (frames : List Json) :
    Except String (List Keyframe × List (List (String × String))) := do
  let mut out : List Keyframe := []
  let mut shown : List (List (String × String)) := []
  let mut last : Int := 0
  for f in frames do
    let offset ← offsetOf (f.field? "offset")
    if let some o := offset then
      if o < last then throw "keyframe offsets must not go down"
      last := o
    let easing ← easingOf (member f "easing")
    let composite ← compositeOf (member f "composite")
    let (props, sh) := pairsOf supports (stringPairs (f.field? "p"))
    out := out ++ [{ offset, easing, composite, props }]
    shown := shown ++ [sh]
  return (Effect.withOffsets out, shown)

def stringList (j : Option Json) : List String :=
  match j with
  | some (.array items) => items.filterMap fun it => match it with
    | .string s => some s
    | .number s => some s
    | _ => none
  | _ => []

/-- §6.6.3 for a property-indexed keyframe: each property's values spread evenly from 0
to 1, the keyframes of all properties merged by that offset, then the `offset`, `easing`
and `composite` members given to the keyframes in order (easings and composites repeat). -/
def indexedKeyframes (supports : String → String → Bool) (obj : Json) :
    Except String (List Keyframe × List (List (String × String))) := do
  let entries : List (String × List String) := match obj.field? "p" with
    | some (.array items) => items.filterMap fun it => match it with
      | .array [.string k, vs] => some (k, stringList (some vs))
      | _ => none
    | _ => []
  -- (computed offset, idl name, value), every property
  let points : List (Int × String × String) := entries.flatMap fun (k, vs) =>
    (vs.zip (Effect.spread (vs.map fun _ => none))).map fun (v, o) => (o, k, v)
  let offsets := (points.map (·.1)).eraseDups.mergeSort (· ≤ ·)
  let merged : List (List (String × String)) := offsets.map fun o =>
    (points.filter (·.1 == o)).map fun (_, k, v) => (k, v)
  let offsetMember : List (Option Json) := match obj.field? "offset" with
    | some (.array items) => items.map some
    | some .null | none => []
    | some j => [some j]
  let easings := stringList (obj.field? "easing")
  let composites := stringList (obj.field? "composite")
  let mut out : List Keyframe := []
  let mut shown : List (List (String × String)) := []
  let mut last : Int := 0
  for i in [0:merged.length] do
    let offset ← offsetOf (offsetMember.getD i none)
    if let some o := offset then
      if o < last then throw "keyframe offsets must not go down"
      last := o
    let easing ← easingOf (if easings.isEmpty then none else some (Css.nth easings "linear" i))
    let composite ← compositeOf (if composites.isEmpty then none else some (Css.nth composites "auto" i))
    let (props, sh) := pairsOf supports (merged.getD i [])
    out := out ++ [{ offset, easing, composite, props }]
    shown := shown ++ [sh]
  -- an easing or composite list longer than the keyframes is still checked
  for e in easings do let _ ← easingOf (some e)
  for c in composites do let _ ← compositeOf (some c)
  return (Effect.withOffsets out, shown)

/-- §6.6.3 "process a keyframes argument": `{"list": [...]}` (a sequence), `{"obj": {...}}`
(a property-indexed keyframe) or null (no keyframes). An error is a TypeError's message. -/
def keyframesOf (supports : String → String → Bool) (kf : Option Json) :
    Except String (List Keyframe × List (List (String × String))) :=
  match kf with
  | none | some .null => .ok ([], [])
  | some j =>
    match j.field? "list", j.field? "obj" with
    | some (.array frames), _ => listKeyframes supports frames
    | _, some obj => indexedKeyframes supports obj
    | _, _ => .ok ([], [])

/-- `getKeyframes()` (§6.6.2): each keyframe with its offset, computed offset, easing,
composite and pairs. -/
def keyframesJson (e : EffectRec) : Json :=
  .array ((List.range e.keyframes.length).map fun i =>
    let k := e.keyframes.getD i {}
    let pairs := match e.shown[i]? with
      | some sh => sh
      | none => k.props.map fun (css, v) => (idlName css, v)
    .object [("offset", jopt k.offset), ("computedOffset", jnum k.computedOffset),
      ("easing", .string k.easing.toText),
      ("composite", .string (match k.composite with | some c => c.toText | none => "auto")),
      ("p", .array (pairs.map fun (n, v) => .array [.string n, .string v]))])

/-! ## Effects -/

/-- A new effect (`new KeyframeEffect(target, keyframes, options)`, §6.6.1): `{"kf":
keyframes, "opt": options}`; the options hold the timing members and `composite`. The
answer is `{"id": n}`. -/
def createEffect (supports : String → String → Bool) (s : State) (target : Option Nat) (q : String) : State × String :=
  let j := (JSON.parseJson? q).getD (.object [])
  let opt := (j.field? "opt").getD (.object [])
  match timingOf {} opt, keyframesOf supports (j.field? "kf"), compositeOf (member opt "composite") with
  | .error m, _, _ | _, .error m, _ | _, _, .error m => (s, err "TypeError" m)
  | .ok timing, .ok (keyframes, shown), .ok composite =>
    let rec_ : EffectRec := {
      target, keyframes, shown, timing, composite := composite.getD .replace,
      pseudo := (member opt "pseudoElement").getD "" }
    let (s, i) := addEffect s rec_
    (s, (Json.object [("id", .number (toString i))]).toString)

/-- A change of an effect: `{"op": "timing", "opt": {...}}` (`updateTiming`), `{"op":
"keyframes", "kf": ...}` (`setKeyframes`), `{"op": "composite", "v": text}`, `{"op":
"target", "node": n or null}`, `{"op": "pseudo", "v": text}`. -/
def setEffect (supports : String → String → Bool) (s : State) (id : Nat) (q : String) : State × String :=
  match s.effects[id]? with
  | none => (s, err "TypeError" "no such effect")
  | some e =>
    let j := (JSON.parseJson? q).getD (.object [])
    let put := fun (e' : EffectRec) => ({ s with effects := s.effects.set! id e' }, "{}")
    match member j "op" with
    | some "timing" =>
      match timingOf e.timing ((j.field? "opt").getD (.object [])) with
      | .ok timing => put { e with timing }
      | .error m => (s, err "TypeError" m)
    | some "keyframes" =>
      match keyframesOf supports (j.field? "kf") with
      | .ok (keyframes, shown) => put { e with keyframes, shown }
      | .error m => (s, err "TypeError" m)
    | some "composite" =>
      match compositeOf (member j "v") with
      | .ok (some c) => put { e with composite := c }
      | .ok none => (s, err "TypeError" "'auto' is not a composite operation of an effect")
      | .error m => (s, err "TypeError" m)
    | some "target" => put { e with target := (member j "node").bind String.toNat? }
    | some "pseudo" => put { e with pseudo := (member j "v").getD "" }
    | _ => (s, err "TypeError" "unknown effect operation")

/-- The local time of an effect: the current time of its animation. -/
def localTime (s : State) (e : EffectRec) : Option Int × Bool :=
  match e.anim.bind (s.anims[·]?) with
  | some a => (a.player.currentTime (s.tl a), a.player.rate < 0)
  | none => (none, false)

/-- A read of an effect: `timing`, `computed`, `keyframes` or `info` (target, pseudo,
composite). -/
def getEffect (s : State) (id : Nat) (q : String) : String :=
  match s.effects[id]? with
  | none => err "TypeError" "no such effect"
  | some e =>
    match q with
    | "timing" => (Json.object (timingJson e.timing)).toString
    | "computed" =>
      let (lt, back) := localTime s e
      (Json.object (computedJson e.timing lt back)).toString
    | "keyframes" => (keyframesJson e).toString
    | _ => (Json.object [("target", match e.target with | some t => .number (toString t) | none => .null),
        ("pseudo", .string e.pseudo), ("composite", .string e.composite.toText)]).toString

/-! ## Animations -/

def actJson : Act → Json
  | .readyNew => .array [.string "readyNew"]
  | .readyResolve => .array [.string "readyResolve"]
  | .readyReject => .array [.string "readyReject"]
  | .finishedNew => .array [.string "finishedNew"]
  | .finishedResolve => .array [.string "finishedResolve"]
  | .finishedReject => .array [.string "finishedReject"]
  | .notify => .array [.string "notify"]
  | .event type ct tl => .array [.string "event", .string type, jopt ct, jopt tl]

/-- What a script object shows of an animation, with the acts since the last answer
(which this answer takes: they are given once). -/
def snapshot (s : State) (id : Nat) : State × String :=
  match s.anims[id]? with
  | none => (s, err "TypeError" "no such animation")
  | some a =>
    let tl := s.tl a
    let eff := s.effEnd a
    let (kind, name) := match a.origin with
      | .script => ("script", "")
      | .cssAnimation n => ("animation", n)
      | .cssTransition p => ("transition", p)
    let j := Json.object [
      ("currentTime", jopt (a.player.currentTime tl)), ("startTime", jopt a.player.startTime),
      ("playState", .string (a.player.playState tl eff).toText),
      ("pending", .bool (a.player.pending != .none)), ("playbackRate", jnum a.player.rate),
      ("effect", match a.effect with | some e => .number (toString e) | none => .null),
      ("timeline", .bool a.timeline), ("kind", .string kind), ("name", .string name),
      ("id", .string a.idText),
      ("owner", match a.owner with | some o => .number (toString o) | none => .null),
      -- Web Animations 2 §4.4.4 overall progress: the current time over the effect end, in [0, 1]
      ("overallProgress", match a.player.currentTime tl, s.effectOf a with
        | some c, some e =>
          match e.timing.endTime with
          | .fin en =>
            if en == 0 then jnum (if c < 0 then 0 else Fix.one)
            else jnum (Fix.clamp 0 Fix.one ((Fix.div c en).getD 0))
          | .inf => jnum 0
        | _, _ => .null),
      ("acts", .array (a.player.out.map actJson))]
    ({ s with anims := s.anims.modify id fun a => { a with player := { a.player with out := [] } } }, j.toString)

/-- A new animation (`new Animation(effect, timeline)`, §6.4.1): `{"effect": n or null,
"timeline": true or false}`. An effect that another animation has leaves that one. -/
def createAnim (s : State) (q : String) : State × String :=
  let j := (JSON.parseJson? q).getD (.object [])
  let effect := (member j "effect").bind String.toNat?
  let timeline := (j.getBool? "timeline").getD true
  let s := match effect.bind (s.effects[·]?) with
    | some e => match e.anim with
      | some old => { s with anims := s.anims.modify old fun a => { a with effect := none } }
      | none => s
    | none => s
  let (s, i) := addAnim s { effect, timeline }
  (s, (Json.object [("id", .number (toString i))]).toString)

/-- A time of a request: a number of milliseconds, or none for null. A text that is
not a finite number is a TypeError. -/
def timeOf (j : Json) (key : String) : Except String (Option Int) :=
  match j.field? key with
  | none | some .null => .ok none
  | some (.string v) | some (.number v) =>
    match Fix.parse v with
    | some x => .ok (some x)
    | none => .error "a time must be a finite number or null"
  | _ => .error "a time must be a finite number or null"

/-- A method or a setter of an animation: `{"m": name, "v": value}`. The answer is the
snapshot after it, or the error. -/
def callAnim (s : State) (id : Nat) (q : String) : State × String :=
  match s.anims[id]? with
  | none => (s, err "TypeError" "no such animation")
  | some a =>
    let j := (JSON.parseJson? q).getD (.object [])
    let tl := s.tl a
    let eff := s.effEnd a
    let done := fun (r : Except String Player) =>
      match r with
      | .ok p => snapshot (s.setPlayer id p) id
      | .error name => (s, err name "the animation can not do that in its current state")
    match member j "m" with
    | some "play" => done (a.player.play tl eff true)
    | some "pause" => done (a.player.pause tl eff)
    | some "finish" => done (a.player.finish tl eff)
    | some "cancel" => done (.ok (a.player.cancel tl eff))
    | some "reverse" => done (a.player.reverse tl eff)
    | some "notify" => done (.ok (a.player.finishNotify tl eff))
    | some "currentTime" =>
      match timeOf j "v" with
      | .ok t => done (a.player.setCurrentTime tl eff t)
      | .error m => (s, err "TypeError" m)
    | some "startTime" =>
      match timeOf j "v" with
      | .ok t => done (.ok (a.player.setStartTime tl eff t))
      | .error m => (s, err "TypeError" m)
    | some "playbackRate" =>
      match timeOf j "v" with
      | .ok (some r) => done (.ok (a.player.setRate tl eff r))
      | _ => (s, err "TypeError" "a playback rate must be a finite number")
    | some "updatePlaybackRate" =>
      match timeOf j "v" with
      | .ok (some r) => done (a.player.updateRate tl eff r)
      | _ => (s, err "TypeError" "a playback rate must be a finite number")
    | some "effect" =>
      -- §4.4.7 set the associated effect: the new effect leaves its old animation; the
      -- finished state is updated
      let new := (member j "v").bind String.toNat?
      let s := match a.effect with
        | some old => { s with effects := s.effects.modify old fun e => { e with anim := none } }
        | none => s
      let s := match new.bind (s.effects[·]?) with
        | some e => match e.anim with
          | some other => { s with anims := s.anims.modify other fun x => { x with effect := none } }
          | none => s
        | none => s
      let s := match new with
        | some e => { s with effects := s.effects.modify e fun r => { r with anim := some id } }
        | none => s
      let s := { s with anims := s.anims.modify id fun x => { x with effect := new } }
      let a := s.anims[id]!
      snapshot (s.setPlayer id (a.player.updateFinished (s.tl a) (s.effEnd a) false false)) id
    | some "timeline" =>
      let on := (j.getBool? "v").getD true
      let s := { s with anims := s.anims.modify id fun x => { x with timeline := on } }
      let a := s.anims[id]!
      -- §4.4.2 set the timeline: with none, the start time is unresolved and the hold time kept
      let p := if on then a.player else { a.player with startTime := none }
      snapshot (s.setPlayer id (p.updateFinished (s.tl a) (s.effEnd a) false false)) id
    | some "id" =>
      snapshot { s with anims := s.anims.modify id fun x => { x with idText := (member j "v").getD "" } } id
    | some "refresh" =>
      -- after a change of the effect's timing: §4.4.14 with no seek
      snapshot (s.setPlayer id (a.player.updateFinished tl eff false false)) id
    | _ => (s, err "TypeError" "unknown animation operation")

/-- `getAnimations()` (§6.8, §6.9): the animations whose effect is current or in effect
(§4.6.6 "relevant") and whose target `wanted` holds of, in composite order, by number. -/
def listAnimations (s : State) (wanted : Nat → Bool) : String :=
  let relevant := (ordered s).filter fun (_, a) =>
    match s.effectOf a with
    | some e =>
      (match e.target with | some t => wanted t | none => false) &&
      -- relevant: in effect (a progress), or current: before the end with a rate that reaches it
      ((s.progressOf a).isSome ||
        (match a.player.currentTime (s.tl a) with
         | some c => a.player.playState (s.tl a) (s.effEnd a) != .finished && a.player.playState (s.tl a) (s.effEnd a) != .idle
             && (a.player.rate > 0 && (e.timing.endTime.gtInt c) || a.player.rate < 0 && c > 0)
         | none => false))
    | none => false
  (Json.array (relevant.map fun (i, _) => .number (toString i))).toString

/-- The answer of the frame's part (op 67), after `tick`: the events of CSS animations
and transitions queued since the last frame, each `[type, target node, name, elapsed
ms]`, given once; the animations that have acts for their script objects (`snapshot`
gives and takes them); and whether the animations need another frame. -/
def frameAnswer (s : State) : State × String :=
  let s' : State := { s with events := #[], frameAsked := false }
  let withActs := (List.range s.anims.size).filter fun i =>
    match s.anims[i]? with
    | some a => !a.player.out.isEmpty
    | none => false
  let j := Json.object [
    ("events", .array (s.events.toList.map fun e =>
      .array [.string e.type, .number (toString e.target), .string e.name, jnum e.elapsed])),
    ("acts", .array (withActs.map fun i => .number (toString i))),
    ("again", .bool (needsFrame s'))]
  (s', j.toString)

/-! ## Tests -/

private def yes : String → String → Bool := fun _ _ => true
private def frames (q : String) : Option (List (Option Int × Int × List (String × String))) :=
  ((keyframesOf yes (JSON.parseJson? q)).map fun (ks, _) => ks.map fun k => (k.offset, k.computedOffset, k.props)).toOption

#guard animatableNames (fun p _ => p == "margin-left" || p == "transition-duration") "marginLeft\x00margin-left\x00--x\x00transitionDuration\x00top" == "10100"
#guard cssName "marginLeft" == some "margin-left"
#guard cssName "cssFloat" == some "float"
#guard cssName "--my-angle" == some "--my-angle"
#guard cssName "margin-left" == none
#guard cssName "offset" == none
#guard idlName "margin-left" == "marginLeft" && idlName "float" == "cssFloat" && idlName "--x-y" == "--x-y"
-- the keyframes the interpolation tests give Element.animate
#guard frames "{\"list\":[{\"offset\":\"0\",\"composite\":\"replace\",\"p\":[[\"width\",\"10px\"]]},{\"offset\":\"1\",\"composite\":\"replace\",\"p\":[[\"width\",\"20px\"]]}]}"
  == some [(some 0, 0, [("width", "10px")]), (some Fix.one, Fix.one, [("width", "20px")])]
#guard frames "{\"list\":[{\"p\":[[\"width\",\"10px\"]]},{\"p\":[[\"width\",\"15px\"]]},{\"p\":[[\"width\",\"20px\"]]}]}"
  == some [(none, 0, [("width", "10px")]), (none, Fix.half, [("width", "15px")]), (none, Fix.one, [("width", "20px")])]
#guard (frames "{\"list\":[{\"offset\":\"0.5\",\"p\":[]},{\"offset\":\"0.2\",\"p\":[]}]}").isNone
#guard (frames "{\"list\":[{\"offset\":\"1.5\",\"p\":[]}]}").isNone
#guard (frames "{\"list\":[{\"easing\":\"bounce\",\"p\":[]}]}").isNone
#guard frames "{\"obj\":{\"p\":[[\"opacity\",[\"0\",\"1\"]],[\"width\",[\"0px\",\"50px\",\"100px\"]]]}}"
  == some [(none, 0, [("opacity", "0"), ("width", "0px")]), (none, Fix.half, [("width", "50px")]),
          (none, Fix.one, [("opacity", "1"), ("width", "100px")])]
#guard frames "null" == some []
#guard (timingOf {} (.object [("duration", .string "n:100000"), ("fill", .string "forwards"),
  ("easing", .string "steps(1, start)")])).toOption.map (fun t => (t.duration, t.fill, t.easing))
  == some (some (.fin (Fix.ofInt 100000)), .forwards, .steps 1 .start)
#guard (timingOf {} (.object [("duration", .string "n:-1")])).toOption.isNone
#guard (timingOf {} (.object [("duration", .string "s:1000")])).toOption.isNone
#guard (timingOf {} (.object [("iterations", .string "Infinity")])).toOption.map (·.iterations) == some .inf
#guard (timingOf {} (.object [("delay", .string "NaN")])).toOption.isNone
#guard (timingOf {} (.object [("fill", .string "sideways")])).toOption.isNone

-- Element.animate(...); pause(); currentTime = 50000: the Web Animations path of the tests
private def run : State × String :=
  let (s, _) := createEffect yes {} (some 5)
    "{\"kf\":{\"list\":[{\"offset\":\"0\",\"p\":[[\"width\",\"10px\"]]},{\"offset\":\"1\",\"p\":[[\"width\",\"20px\"]]}]},\"opt\":{\"fill\":\"forwards\",\"duration\":\"n:100000\",\"easing\":\"cubic-bezier(0, 0.23333333333333334, 1, 0.23333333333333334)\"}}"
  let (s, _) := createAnim s "{\"effect\":\"0\",\"timeline\":true}"
  let (s, _) := callAnim s 0 "{\"m\":\"play\"}"
  let (s, _) := callAnim s 0 "{\"m\":\"pause\"}"
  callAnim s 0 "{\"m\":\"currentTime\",\"v\":\"50000\"}"
private def acW : Access :=
  { connected := fun _ => true, base := fun _ p => if p == "width" then some "50px" else none,
    prev := fun _ _ => none, changed := fun _ => [],
    compute := fun _ _ t => some t, decls := fun _ => [], candidates := [], sheet := fun _ => "" }
#guard overrides run.1 acW == [{ node := 5, property := "width", value := "13px" }]
#guard listAnimations run.1 (· == 5) == "[0]"
#guard listAnimations run.1 (· == 6) == "[]"
#guard (JSON.parseJson? run.2).bind (·.getString? "playState") == some "paused"

end L4Factoidal.Rendering.Animation.Api
