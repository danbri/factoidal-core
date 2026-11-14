/-
L4Factoidal.Rendering.Animation.Engine: the animations of one page: the table of
effects and animations, the style change that starts, updates and cancels CSS
animations (CSS Animations 1 §4) and CSS transitions (CSS Transitions 1 §3), and the
animated values the cascade then takes (Web Animations 1 §5.4 "the effect stack").

The engine reads the page through `Access`: the computed style without animations
(`base`), the style of the last style change (`prev`, the before-change style), an
element's cascaded animation and transition longhands, the text of the page's sheets,
and the computed value of a specified value in an element's context. It answers with
the next state and the list of `Override`s: element, longhand, computed text, and
whether a transition wrote it. The cascade applies them above the author's normal
declarations (animations) or above everything (transitions): CSS Cascade 4 §6.1.

A page with no animation and no transition declaration makes no call here
(`State.idle`).
-/
import L4Factoidal.Rendering.Animation.Css
import L4Factoidal.Rendering.Animation.Model
import Std.Data.HashMap

namespace L4Factoidal.Rendering.Animation
open Fix (one)

/-- Where an animation is from (Web Animations 1 §5.4.1 composite order classes). -/
inductive Origin where
  | script
  | cssAnimation (name : String)
  | cssTransition (property : String)
  deriving DecidableEq, Repr, Inhabited

structure EffectRec where
  target : Option Nat := none
  pseudo : String := ""
  keyframes : List Keyframe := []
  /-- The keyframes as `getKeyframes()` shows them: the names a script gave, with values. -/
  shown : List (List (String × String)) := []
  composite : Composite := .replace
  timing : Timing := {}
  /-- The animation the effect is associated with. -/
  anim : Option Nat := none
  /-- The easing of a neutral keyframe at offset 0 (the element's timing function for a
  CSS animation). -/
  neutralEasing : Easing := .linear
  deriving Repr, Inhabited

structure AnimRec where
  player : Player := {}
  effect : Option Nat := none
  /-- Associated with the document timeline. -/
  timeline : Bool := true
  origin : Origin := .script
  /-- The owning element of a CSS animation or transition. -/
  owner : Option Nat := none
  /-- Creation order (composite order within a class). -/
  seq : Nat := 0
  idText : String := ""
  /-- A transition's start and end values, as computed text. -/
  fromText : String := ""
  toText : String := ""
  /-- Removed from the page: cancelled by style, never listed again. -/
  dead : Bool := false
  /-- The phase, the iteration and the active time (ms) when the events of a CSS animation
  or transition were last looked for (`phaseEvents`). -/
  phase : Phase := .idle
  iteration : Int := 0
  activeTime : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- An animation or transition event for the page (CSS Animations 1 §4.2, CSS Transitions
1 §6): the type, the target element, the animation's name or the transition's property,
and the elapsed time in ms. -/
structure CssEvent where
  type : String
  target : Nat
  name : String
  elapsed : Int
  deriving DecidableEq, Repr, Inhabited

/-- An animated value for the cascade. -/
structure Override where
  node : Nat
  property : String
  value : String
  transition : Bool := false
  deriving DecidableEq, Repr, Inhabited

structure State where
  /-- The time of the document timeline, in ms. It moves only between tasks. -/
  now : Int := 0
  effects : Array EffectRec := #[]
  anims : Array AnimRec := #[]
  nextSeq : Nat := 0
  /-- The sheet text whose `@keyframes` rules are `rules`. -/
  sheet : String := ""
  rules : List (String × List Css.CssKeyframe) := []
  /-- The events of CSS animations and transitions not yet given to the page. -/
  events : Array CssEvent := #[]
  /-- An animation frame is asked for (`frameHandle`). -/
  frameAsked : Bool := false
  /-- The element and longhand pairs that an animation (not a transition) gave a value at
  the last style change: the before-change style holds those values, so a difference
  from the style without animations starts no transition there. -/
  lastAnimated : List (Nat × String) := []
  /-- The CSS animations and transitions that style has not cancelled or retired, by
  number: what a style change looks at, so that its work does not grow with the
  animations a page has had. -/
  liveCss : List Nat := []
  deriving Inhabited

/-- What the engine reads of the page at a style change. -/
structure Access where
  connected : Nat → Bool
  /-- The computed text of a longhand of an element, without animations; none for a
  property the engine does not compute. -/
  base : Nat → String → Option String
  /-- The same at the last style change, with the animations of then (the before-change
  style); none also for an element that had no style then. -/
  prev : Nat → String → Option String
  /-- Longhands of an element whose computed text may differ between `prev` and `base`:
  every one that differs is here when it is a property of the layout profile or one the
  element's rules or `style` attribute declare, then or now. -/
  changed : Nat → List String
  /-- The computed text of a specified value of a longhand in the element's context. -/
  compute : Nat → String → String → Option String
  /-- The element's cascaded animation and transition longhands. -/
  decls : Nat → List (String × String)
  /-- The elements that have such declarations. -/
  candidates : List Nat
  /-- The text of the page's style sheets. -/
  sheet : Unit → String
  /-- The longhands of a property name: those of a shorthand, or the name itself. -/
  longhands : String → List String := fun p => [p]

namespace State

/-- No animation exists: a style change with no animation declaration has nothing to do. -/
def idle (s : State) : Bool := s.anims.all (·.dead)

def effectOf (s : State) (a : AnimRec) : Option EffectRec := a.effect.bind (s.effects[·]?)

/-- The timeline time of an animation. -/
def tl (s : State) (a : AnimRec) : Option Int := if a.timeline then some s.now else none

/-- Web Animations 1 §4.6.4: the associated effect end; 0 with no effect. -/
def effEnd (s : State) (a : AnimRec) : Ext :=
  match s.effectOf a with
  | some e => e.timing.endTime
  | none => .fin 0

/-- The progress of an animation's effect now (Web Animations 1 §4.10.1); none when the
effect is not in effect. -/
def progressOf (s : State) (a : AnimRec) : Option Int :=
  match s.effectOf a with
  | some e => e.timing.progress (a.player.currentTime (s.tl a)) (a.player.rate < 0)
  | none => none

def setPlayer (s : State) (i : Nat) (p : Player) : State :=
  { s with anims := s.anims.modify i fun a => { a with player := p } }

end State

/-! ## Animation types of properties -/

/-- Properties that do not animate (CSS Animations 1 §3: the animation properties; CSS
Writing Modes 4 §2: `direction`, `unicode-bidi`). -/
def animatable (property : String) : Bool :=
  !(property.startsWith "animation" || property.startsWith "transition"
    || property == "direction" || property == "unicode-bidi")

/-- The animation type of a property beyond its value's shape. -/
def kindOf (property : String) : Value.Kind :=
  if ["width", "height", "min-width", "min-height", "max-width", "max-height", "padding-top", "padding-right",
      "padding-bottom", "padding-left", "border-top-width", "border-right-width", "border-bottom-width",
      "border-left-width", "font-size", "line-height", "border-spacing", "flex-basis", "outline-width",
      "column-width", "column-gap", "row-gap", "perspective", "shape-margin", "flex-grow", "flex-shrink", "tab-size", "text-decoration-thickness",
      "block-size", "inline-size", "min-block-size", "min-inline-size", "max-block-size", "max-inline-size",
      "padding-block-start", "padding-block-end", "padding-inline-start", "padding-inline-end",
      "stroke-width", "stroke-miterlimit", "r", "rx", "ry", "font-size-adjust", "zoom",
      "contain-intrinsic-width", "contain-intrinsic-height",
      "scroll-padding-top", "scroll-padding-right", "scroll-padding-bottom", "scroll-padding-left",
      "font-stretch", "font-width"].contains property then .nonNegative
  else if ["z-index", "order", "math-depth"].contains property then .integer
  else if ["column-count", "orphans", "widows"].contains property then .positiveInteger
  else if ["opacity", "fill-opacity", "stroke-opacity", "stop-opacity", "flood-opacity",
      "shape-image-threshold"].contains property then .unit
  else if property == "font-weight" then .fontWeight
  else if property == "visibility" then .visibility
  else if property == "transform" then .transformList
  else if property == "filter" || property == "backdrop-filter" then .filterList
  else if property == "box-shadow" then .shadowList 4
  else if property == "text-shadow" then .shadowList 3
  else if property == "translate" then .translate
  else if property == "scale" then .scale
  else if property == "rotate" then .rotate
  else if ["border-image-slice", "border-image-width", "border-image-outset", "mask-border-slice",
      "mask-border-width", "mask-border-outset"].contains property then .sides
  else if property == "grid-template-columns" || property == "grid-template-rows" then .gridTracks
  else if ["background-position", "background-position-x", "background-position-y", "background-size",
      "mask-position", "mask-size", "-webkit-mask-position", "-webkit-mask-size", "stroke-dasharray"].contains property then .repeatable
  else if property == "aspect-ratio" then .ratio
  else if property == "font-style" then .fontStyle
  else if ["column-rule-color", "column-rule-width", "row-rule-color", "row-rule-width"].contains property then .gapList
  else if ["border-top-left-radius", "border-top-right-radius", "border-bottom-left-radius",
      "border-bottom-right-radius"].contains property then .radius
  else if property.startsWith "corner-" && property.endsWith "-shape" then .cornerShape
  else if property == "transform-origin" then .origin
  else if property == "letter-spacing" then .zeroWord "normal" true
  else if property == "word-spacing" then .zeroWord "normal" false
  else if property == "vertical-align" then .zeroWord "baseline" false
  else if property == "offset-rotate" then .offsetRotate
  else if property == "clip-path" || property == "shape-outside" || property == "offset-path" then .shape
  -- images, counters and the clip margin do not interpolate (CSS Images 3 §6, CSS Lists 3 §4)
  else if ["border-image-source", "mask-border-source", "list-style-image", "background-image", "mask-image",
      "-webkit-mask-image", "content", "cursor", "counter-increment", "counter-reset", "counter-set",
      "overflow-clip-margin"].contains property then .discrete
  else if property == "display" || property == "overlay" then .avoid "none"
  else if property == "content-visibility" then .avoid "hidden"
  else .generic

/-- The properties whose computed value is a line width (CSS Backgrounds 3 §4.3, CSS UI 4
§5.2, CSS Gaps 1 §3): an animated value of one is snapped as a declared one is
(`Value.snapWidths`). -/
def lineWidth (property : String) : Bool :=
  ["border-top-width", "border-right-width", "border-bottom-width", "border-left-width", "outline-width",
   "column-rule-width", "row-rule-width"].contains property

/-- A value with each `currentcolor` as the element's colour: `currentcolor` computes to
itself (CSS Color 4 §4.5) and is the used colour of `color`, so a value with it
interpolates with a colour as that colour does. `color` itself has no `currentcolor`. -/
def withCurrentColor (ac : Access) (e : Nat) (property : String) (v : Value) : Value :=
  if property == "color" || !v.contains (.ident "currentcolor") then v
  else match (ac.base e "color").map Value.parse with
    | some [c] => v.map fun t => if t == .ident "currentcolor" then c else t
    | _ => v

/-- Kind: zero cost and identity. Says: a value with no `currentcolor` is itself, whatever
the element's colour (it is not read). -/
theorem withCurrentColor_plain (ac : Access) (e : Nat) (property : String) (v : Value)
    (h : v.contains (.ident "currentcolor") = false) : withCurrentColor ac e property v = v := by
  unfold withCurrentColor
  rw [h]
  simp

/-! ## The style change -/

/-- The `@keyframes` rules of the page's sheets, read again only when the text changed. -/
def withSheet (s : State) (text : String) : State :=
  if text == s.sheet then s else { s with sheet := text, rules := Css.keyframesOf text }

/-- The most animations, and the most effects, the state of one page holds, counting
those that ended (none is freed while the page lives). At the bound the page makes no new
one: the script constructors and `Element.animate` throw (`Api.createEffect`,
`Api.createAnim`), and a CSS animation or transition does not start
(`updateAnimations`, `startTransition`). The work of a style change and of a frame is a
pass over these records, so it is bounded with them. -/
def maxAnimations : Nat := 65536

/-- The page is at the bound of `maxAnimations`: nothing more is added. -/
def State.full (s : State) : Bool := s.anims.size ≥ maxAnimations || s.effects.size ≥ maxAnimations

/-- The index of the effect of a new record. -/
def addEffect (s : State) (e : EffectRec) : State × Nat :=
  ({ s with effects := s.effects.push e }, s.effects.size)

/-- Kind: resource bound (one step). Says: a new effect is one more record, and the
animations stay as they were. -/
theorem addEffect_size (s : State) (e : EffectRec) :
    (addEffect s e).1.effects.size = s.effects.size + 1 ∧ (addEffect s e).1.anims.size = s.anims.size := by
  simp [addEffect]

def addAnim (s : State) (a : AnimRec) : State × Nat :=
  let i := s.anims.size
  let s := { s with anims := s.anims.push { a with seq := s.nextSeq }, nextSeq := s.nextSeq + 1,
                    liveCss := if a.owner.isSome then i :: s.liveCss else s.liveCss }
  let s := match a.effect with
    | some e => { s with effects := s.effects.modify e fun r => { r with anim := some i } }
    | none => s
  (s, i)

/-- Kind: resource bound (one step). Says: a new animation is one more record, and no
effect is added. So a state whose additions are all made when it is not `full` never
holds more than `maxAnimations` animations or effects. -/
theorem addAnim_size (s : State) (a : AnimRec) :
    (addAnim s a).1.anims.size = s.anims.size + 1 ∧ (addAnim s a).1.effects.size = s.effects.size := by
  unfold addAnim
  cases a.effect <;> simp

/-- Cancel an animation of style and take it off the page. -/
def kill (s : State) (i : Nat) : State :=
  { s with liveCss := s.liveCss.erase i
           anims := s.anims.modify i fun a =>
      { a with player := a.player.cancel (s.tl a) (s.effEnd a), dead := true } }

/-- The animations of class `pick` owned by element `e`, by index. -/
def owned (s : State) (e : Nat) (pick : Origin → Bool) : List Nat :=
  (s.liveCss.filter fun i =>
    match s.anims[i]? with
    | some a => !a.dead && a.owner == some e && pick a.origin
    | none => false).reverse

def isCssAnimation : Origin → Bool
  | .cssAnimation _ => true
  | _ => false

def isCssTransition : Origin → Bool
  | .cssTransition _ => true
  | _ => false

/-- CSS Animations 1 §4: the animations of element `e` follow its `animation-name` list:
a name with a `@keyframes` rule and no animation yet starts one (playing, paused when
`animation-play-state` says so); an animation whose name left the list, or whose element
left the document, is cancelled; one that stays takes the current timing and keyframes
and follows `animation-play-state`. -/
def updateAnimations (s : State) (ac : Access) (e : Nat) : State := Id.run do
  let specs := if ac.connected e then Css.animations (ac.decls e) else []
  let mut s := s
  let mut free := owned s e isCssAnimation
  for spec in specs do
    let rule := s.rules.reverse.lookup spec.name
    let existing := free.find? fun i => match s.anims[i]? with
      | some a => a.origin == .cssAnimation spec.name
      | none => false
    match existing, rule with
    | some i, some ks =>
      free := free.erase i
      let a := s.anims[i]!
      -- the current timing and keyframes
      if let some ei := a.effect then
        let kfs := Css.toKeyframes spec.easing ks
        s := { s with effects := s.effects.modify ei fun r =>
          { r with timing := spec.timing, keyframes := kfs, composite := spec.composite, neutralEasing := spec.easing } }
      let a := s.anims[i]!
      let tl := s.tl a
      let eff := s.effEnd a
      let pausedNow := a.player.pending == .pause || a.player.playState tl eff == .paused
      if spec.paused && !pausedNow then
        s := s.setPlayer i ((a.player.pause tl eff).toOption.getD a.player)
      else if !spec.paused && pausedNow then
        s := s.setPlayer i ((a.player.play tl eff false).toOption.getD a.player)
    | some i, none => free := free.erase i; s := kill s i
    | none, some ks =>
      -- at the bound of `maxAnimations` the animation does not start
      if s.full then continue
      let rec_ : EffectRec := {
        target := some e, keyframes := Css.toKeyframes spec.easing ks,
        composite := spec.composite, timing := spec.timing, neutralEasing := spec.easing }
      let (s1, ei) := addEffect s rec_
      let (s2, i) := addAnim s1 { effect := some ei, origin := .cssAnimation spec.name, owner := some e }
      s := s2
      let a := s.anims[i]!
      let tl := s.tl a
      let eff := s.effEnd a
      let p := (a.player.play tl eff true).toOption.getD a.player
      let p := if spec.paused then (p.pause tl eff).toOption.getD p else p
      s := s.setPlayer i p
    | none, none => pure ()
  for i in free do s := kill s i
  return s

/-- A new transition of `property` on `e` from `before` to `after` (computed text): the
keyframes `from` and `to`, fill `backwards`, playing (CSS Transitions 2 §5). -/
def startTransition (s : State) (e : Nat) (property before after : String) (spec : Css.TransitionSpec) : State :=
  -- at the bound of `maxAnimations` the transition does not start
  if s.full then s else
  -- CSS Transitions 2 §5: the timing function is the effect's; the two keyframes are linear
  let timing : Timing := { delay := spec.delay, duration := some (.fin spec.duration), fill := .backwards, easing := spec.easing }
  let (s, ei) := addEffect s { target := some e, keyframes := Effect.fromTo property before after, timing }
  let rec_ : AnimRec := {
    effect := some ei, origin := .cssTransition property, owner := some e,
    fromText := before, toText := after }
  let (s, i) := addAnim s rec_
  let a := s.anims[i]!
  s.setPlayer i ((a.player.play (s.tl a) (s.effEnd a) true).toOption.getD a.player)

/-- Kind: defined refusal at the bound. Says: on a page at its bound of animations a
transition does not start: the state is unchanged. -/
theorem startTransition_full (s : State) (e : Nat) (property before after : String) (spec : Css.TransitionSpec)
    (h : s.full = true) : startTransition s e property before after spec = s := by
  simp [startTransition, h]

/-- CSS Transitions 1 §3 "starting of transitions" for element `e`: for each property
with a matching transition whose computed value changed since the last style change, a
transition from the old value to the new one, when they interpolate (or the transition
allows discrete values) and the duration and delay give it time; a running transition
whose end value is no longer the property's value is cancelled, and replaced from the
current value when the new value interpolates with it. -/
def updateTransitions (s : State) (ac : Access) (e : Nat) : State := Id.run do
  let connected := ac.connected e
  -- a transition of a shorthand is one of each of its longhands (CSS Transitions 1 §2.1)
  let specs := (if connected then Css.transitions (ac.decls e) else []).flatMap fun t =>
    if t.property == "all" || t.property == "none" then [t]
    else (ac.longhands t.property).map fun l => { t with property := l }
  let mut s := s
  let running := owned s e isCssTransition
  -- running transitions: keep, cancel or replace
  for i in running do
    let a := s.anims[i]!
    let property := match a.origin with
      | .cssTransition p => p
      | _ => ""
    let spec := Css.transitionFor specs property
    let after := if connected then ac.base e property else none
    match spec, after with
    | some sp, some after =>
      if a.toText == after then
        -- still going to this value (a frame retires it after its end: `tick`)
        pure ()
      else
        let current := (ac.prev e property).getD a.toText
        s := kill s i
        let kind := kindOf property
        if current != after && (Value.interpolable kind (withCurrentColor ac e property (Value.parse current))
              (withCurrentColor ac e property (Value.parse after)) || sp.allowDiscrete)
            && sp.duration + sp.delay > 0 then
          s := startTransition s e property current after sp
    | _, _ => s := kill s i
  if specs.isEmpty then return s
  -- new transitions: properties whose value changed
  let stillRunning : List String := (owned s e isCssTransition).filterMap fun i =>
    match (s.anims[i]?).map (·.origin) with
    | some (Origin.cssTransition p) => some p
    | _ => none
  -- CSS Transitions 1 §3: the before-change and after-change styles both hold the values
  -- of animations, so a property an animation gave a value starts no transition
  let animatedBefore := (s.lastAnimated.filter (·.1 == e)).map (·.2)
  -- the properties to look at: those the element's transitions name, and, when one of them
  -- is `all`, those whose value is known to differ (found only then: it compares the two
  -- styles of the element)
  let named := specs.filterMap fun t => if t.property == "all" || t.property == "none" then none else some t.property
  let others := if specs.any (·.property == "all") then ac.changed e else []
  for property in (named ++ others).eraseDups do
    if !animatable property || stillRunning.contains property || animatedBefore.contains property then continue
    let some sp := Css.transitionFor specs property | continue
    let some before := ac.prev e property | continue
    let some after := ac.base e property | continue
    if before == after then continue
    if sp.duration + sp.delay ≤ 0 then continue
    let kind := kindOf property
    if Value.interpolable kind (withCurrentColor ac e property (Value.parse before))
        (withCurrentColor ac e property (Value.parse after)) || sp.allowDiscrete then
      s := startTransition s e property before after sp
  return s

/-- Web Animations 1 §5.4.1 composite order: transitions, then CSS animations, then
script animations, each by creation. -/
def orderKey (a : AnimRec) : Nat × Nat :=
  (match a.origin with | .cssTransition _ => 0 | .cssAnimation _ => 1 | .script => 2, a.seq)

def orderLE (a b : Nat × Nat) : Bool := a.1 < b.1 || (a.1 == b.1 && a.2 ≤ b.2)

/-- The animations with an effect whose target `keep` holds of, in composite order. -/
def ordered (s : State) (keep : Nat → Bool := fun _ => true) : List (Nat × AnimRec) :=
  let live := (List.range s.anims.size).filterMap fun i =>
    match s.anims[i]? with
    | some a =>
      if a.dead then none
      else match (s.effectOf a).bind (·.target) with
        | some t => if keep t then some (i, a) else none
        | none => none
    | none => none
  live.mergeSort fun x y => orderLE (orderKey x.2) (orderKey y.2)

/-- Web Animations 1 §5.4.2 the effect stack: each animation in composite order gives
the value of each property of its keyframes at its progress, over the value below it
(the computed style without animations at the bottom). The answer is the top of each
stack. `keep` picks the target elements: the stack of an
element reads that element's animations alone, so the answer for some elements is the
part of the whole answer on those elements. -/
def overridesWhere (s : State) (ac : Access) (keep : Nat → Bool) : List Override := Id.run do
  let mut stack : Std.HashMap (Nat × String) (Value × Bool) := {}
  let mut keys : Array (Nat × String) := #[]
  for (_, a) in ordered s (fun t => ac.connected t && keep t) do
    let some eff := s.effectOf a | continue
    let some e := eff.target | continue
    let some p := s.progressOf a | continue
    for property in Effect.properties eff.keyframes do
      if !animatable property then continue
      let underlying : Value ← match stack[(e, property)]? with
        | some (v, _) => pure v
        | none =>
          -- a property the engine does not compute is not animated
          let some baseText := ac.base e property | continue
          pure (withCurrentColor ac e property (Value.parse baseText))
      let compute := fun (text : String) =>
        (ac.compute e property text).map fun t => withCurrentColor ac e property (Value.parse t)
      match Effect.value eff.keyframes eff.composite property (kindOf property) p underlying compute eff.neutralEasing with
      | some v =>
        if !stack.contains (e, property) then keys := keys.push (e, property)
        stack := stack.insert (e, property) (v, isCssTransition a.origin)
      | none => pure ()
  return keys.toList.filterMap fun k =>
    (stack[k]?).map fun (v, t) =>
      -- a transform's matrices keep six significant digits (their small entries matter)
      { node := k.1, property := k.2, transition := t,
        value := if kindOf k.2 == .transformList then Value.toTextPrecise v
          else if lineWidth k.2 then Value.toText (Value.snapWidths v) else Value.toText v }

/-- The effect stack of every element (`overridesWhere`). -/
def overrides (s : State) (ac : Access) : List Override := overridesWhere s ac fun _ => true

/-- The state with the animated values of this style change noted (`lastAnimated`). -/
def noteAnimated (s : State) (ovs : List Override) : State :=
  { s with lastAnimated := ovs.filterMap fun o => if o.transition then none else some (o.node, o.property) }

/-- A style change (CSS Transitions 1 §3 "style change event"): the `@keyframes` rules of
the sheets as they are now, then the CSS animations and the transitions of every element
that declares one or owns one. The answer is the state after it. -/
def styleChange (s : State) (ac : Access) : State := Id.run do
  let owners := s.liveCss.filterMap fun i => (s.anims[i]?).bind fun a => if a.dead then none else a.owner
  let elements := (ac.candidates ++ owners).eraseDups
  if elements.isEmpty then return s
  let mut s := withSheet s (ac.sheet ())
  for e in elements do
    s := updateAnimations s ac e
    s := updateTransitions s ac e
  return s

/-- A style change in which only the styles of the elements that `keep` holds of can
have changed, and the sheets are as they were: the CSS animations and the transitions of
`elements` (those of them that declare one now) and of the owners of live ones among the
kept. The other elements' animations stay as they are: their declarations and their
before-change and after-change styles are the same. -/
def styleChangeOn (s : State) (ac : Access) (keep : Nat → Bool) (elements : List Nat) : State :=
  let owners := s.liveCss.filterMap fun i =>
    (s.anims[i]?).bind fun a => if a.dead then none else a.owner.bind fun o => if keep o then some o else none
  ((elements ++ owners).eraseDups).foldl (fun s e => updateTransitions (updateAnimations s ac e) ac e) s

/-- Kind: correctness (the empty case). Says: a style change that names no element and
finds no live CSS animation or transition leaves the state as it is. Does not say: that a
style change of some elements equals the whole style change when only those elements
changed (tested below, not proved). -/
theorem styleChangeOn_none (s : State) (ac : Access) (keep : Nat → Bool) (h : s.liveCss = []) :
    styleChangeOn s ac keep [] = s := by
  simp [styleChangeOn, h]

/-- The callback number of the animation frame the engine asks for (the page's script
objects answer it with op 67). -/
def frameHandle : Nat := 0x7FFFFFF2

/-- The events of one CSS animation or transition since they were last looked for (CSS
Animations 2 §4.1, CSS Transitions 2 §6.1: the tables of "previous phase" and "current
phase"), with the record of the phase it has now. The elapsed time of a start is the
interval start, max(min(-delay, active duration), 0); of an end, the interval end; of an
iteration, the time of the iteration boundary; of a cancel, the active time last seen. -/
def phaseEvents (s : State) (a : AnimRec) : AnimRec × List CssEvent :=
  match a.owner, s.effectOf a, a.origin with
  | _, _, .script => (a, [])
  | some e, some eff, origin =>
    let ct := a.player.currentTime (s.tl a)
    let back := a.player.rate < 0
    let now : Phase := if a.dead || ct.isNone then .idle else eff.timing.phase ct back
    let iterNow : Int := match eff.timing.currentIteration ct back with
      | some (.fin n) => n
      | _ => a.iteration
    let activeDur : Int := match eff.timing.activeDuration with
      | .fin d => d
      | .inf => 0
    let iterDur : Int := match eff.timing.iterationDuration with
      | .fin d => d
      | .inf => 0
    let startAt : Int := max (min (-eff.timing.delay) activeDur) 0
    let endAt : Int := match eff.timing.endTime with
      | .fin t => max (min (t - eff.timing.delay) activeDur) 0
      | .inf => activeDur
    let activeNow : Int := (eff.timing.activeTime ct back).getD a.activeTime
    let (isAnimation, name) := match origin with
      | .cssAnimation n => (true, n)
      | .cssTransition p => (false, p)
      | .script => (false, "")
    let ev := fun (type : String) (elapsed : Int) => ({ type, target := e, name, elapsed } : CssEvent)
    let evs : List CssEvent :=
      if isAnimation then
        match a.phase, now with
        | .idle, .active | .before, .active => [ev "animationstart" startAt]
        | .idle, .after | .before, .after => [ev "animationstart" startAt, ev "animationend" endAt]
        | .active, .after => [ev "animationend" endAt]
        | .active, .before => [ev "animationend" startAt]
        | .after, .active => [ev "animationstart" endAt]
        | .after, .before => [ev "animationstart" endAt, ev "animationend" startAt]
        | .active, .active =>
          if iterNow != a.iteration then
            [ev "animationiteration" ((if iterNow > a.iteration then iterNow else iterNow + 1) * iterDur)]
          else []
        | .before, .idle | .active, .idle => [ev "animationcancel" a.activeTime]
        | _, _ => []
      else
        match a.phase, now with
        | .idle, .before => [ev "transitionrun" startAt]
        | .idle, .active => [ev "transitionrun" startAt, ev "transitionstart" startAt]
        | .idle, .after => [ev "transitionrun" startAt, ev "transitionstart" startAt, ev "transitionend" endAt]
        | .before, .active => [ev "transitionstart" startAt]
        | .before, .after => [ev "transitionstart" startAt, ev "transitionend" endAt]
        | .active, .after => [ev "transitionend" endAt]
        | .active, .before => [ev "transitionend" startAt]
        | .after, .active => [ev "transitionstart" endAt]
        | .after, .before => [ev "transitionstart" endAt, ev "transitionend" startAt]
        | .before, .idle | .active, .idle => [ev "transitioncancel" a.activeTime]
        | _, _ => []
    ({ a with phase := now, iteration := iterNow, activeTime := activeNow }, evs)
  | _, _, _ => (a, [])

/-- The animation frame's part (HTML "update animations and send events", Web Animations
1 §4.4.18): each pending play or pause task runs at the timeline time, each animation's
finished state is updated, and the events of each CSS animation and transition are
queued (`phaseEvents`). A CSS animation or transition whose element left the document is
cancelled; a transition past its end is retired. -/
def tick (s : State) (connected : Nat → Bool := fun _ => true) : State := Id.run do
  let mut s := s
  for i in [0:s.anims.size] do
    let a := s.anims[i]!
    if a.dead && a.phase == .idle then continue
    if !a.dead && (match a.owner with | some e => !connected e | none => false) then s := kill s i
    let a := s.anims[i]!
    if !a.dead then
      match s.tl a with
      | some t =>
        let eff := s.effEnd a
        let p := if a.player.pending != .none then a.player.ready t eff else a.player
        let p := if p.startTime.isSome then p.updateFinished (some t) eff false false else p
        if p != a.player then s := s.setPlayer i p
      | none => pure ()
    let a := s.anims[i]!
    if a.origin != .script then
      let (a', evs) := phaseEvents s a
      -- a transition past its end is over: retired, with no further event
      let a' := if isCssTransition a'.origin && a'.phase == .after then { a' with dead := true, phase := .idle } else a'
      if a' != a || !evs.isEmpty then
        s := { s with anims := s.anims.set! i a', events := s.events ++ evs.toArray,
                      liveCss := if a'.dead then s.liveCss.erase i else s.liveCss }
  return s

/-- Whether the page needs another animation frame for its animations: an event waits, an
animation is pending or running, or a CSS animation or transition has events not yet
looked for. -/
def needsFrame (s : State) : Bool :=
  !s.events.isEmpty || s.anims.any fun a =>
    if a.dead then a.phase != .idle
    else
      let tl := s.tl a
      tl.isSome && (a.player.pending != .none || a.player.playState tl (s.effEnd a) == .running
        || (a.origin != .script && a.phase == .idle && (a.player.currentTime tl).isSome))

/-! ## Tests: the three paths of css/support/interpolation-testcommon.js -/

private def acOf (styles : List (Nat × List (String × String))) (decls : List (Nat × List (String × String)))
    (sheet : String) (prev : List (Nat × List (String × String)) := []) : Access :=
  { connected := fun _ => true
    base := fun e p => ((styles.lookup e).getD []).lookup p
    prev := fun e p => ((prev.lookup e).getD []).lookup p
    changed := fun e => ((styles.lookup e).getD []).filterMap fun (k, v) =>
      if ((prev.lookup e).getD []).lookup k != some v then some k else none
    compute := fun _ _ text => some text
    decls := fun e => (decls.lookup e).getD []
    candidates := decls.map (·.1)
    sheet := fun _ => sheet }

-- CSS Animations: @keyframes with a delay of minus half the duration
private def acA : Access := acOf [(5, [("width", "50px")])]
  [(5, [("animation-name", "a1"), ("animation-duration", "100s"), ("animation-delay", "-50s"),
        ("animation-timing-function", "cubic-bezier(0, 0.23333333333333334, 1, 0.23333333333333334)")])]
  "@keyframes a1 {from {width:10px;}to {width:20px;}}"
#guard overrides (styleChange {} acA) acA == [{ node := 5, property := "width", value := "13px" }]
-- the same animation at a later style change is the same animation
#guard (styleChange (styleChange {} acA) acA).anims.size == 1
-- the name leaves: cancelled
#guard overrides (styleChange (styleChange {} acA) (acOf [(5, [("width", "50px")])] [] "")) (acOf [(5, [("width", "50px")])] [] "") == []
-- a style change of one element (`styleChangeOn`) and its effect stack (`overridesWhere`):
-- two elements with the animation; element 6 alone is looked at again, element 5 keeps
-- the values it had, and the two parts are the whole answer
private def acTwo : Access := acOf [(5, [("width", "50px")]), (6, [("width", "70px")])]
  [(5, [("animation-name", "a1"), ("animation-duration", "100s"), ("animation-delay", "-50s"), ("animation-timing-function", "linear")]),
   (6, [("animation-name", "a1"), ("animation-duration", "100s"), ("animation-delay", "-50s"), ("animation-timing-function", "linear")])]
  "@keyframes a1 {from {width:10px;}to {width:20px;}}"
private def acOne : Access := { acTwo with decls := fun e => if e == 6 then [] else acTwo.decls e, candidates := [5] }
private def sTwo : State := styleChange {} acTwo
#guard (overrides sTwo acTwo).length == 2
#guard overridesWhere sTwo acTwo (· == 6) == (overrides sTwo acTwo).filter (·.node == 6)
#guard (overrides sTwo acTwo).filter (·.node != 6) ++ overridesWhere sTwo acTwo (· == 6) == overrides sTwo acTwo
-- element 6 no longer names the animation: the style change of element 6 alone cancels
-- it, as the whole style change does
#guard overrides (styleChangeOn sTwo acOne (· == 6) []) acOne == overrides (styleChange sTwo acOne) acOne
#guard overrides (styleChangeOn sTwo acOne (· == 6) []) acOne == [{ node := 5, property := "width", value := "15px" }]
-- a style change of no element changes nothing
#guard (styleChangeOn sTwo acTwo (fun _ => false) []).anims.size == sTwo.anims.size

-- a neutral `from` keyframe takes the underlying value and the element's timing function
private def acN : Access := acOf [(5, [("width", "50px")])]
  [(5, [("animation-name", "a1"), ("animation-duration", "100s"), ("animation-delay", "-50s"),
        ("animation-timing-function", "linear")])]
  "@keyframes a1 {to {width:20px;}}"
#guard overrides (styleChange {} acN) acN == [{ node := 5, property := "width", value := "35px" }]

-- CSS Transitions: the value changes between two style changes, with a delay of minus half
private def acT : Access := acOf [(7, [("width", "20px"), ("color", "rgb(0, 0, 0)")])]
  [(7, [("transition-property", "width"), ("transition-duration", "100s"), ("transition-delay", "-50s"),
        ("transition-timing-function", "linear")])]
  "" [(7, [("width", "10px"), ("color", "rgb(0, 0, 0)")])]
#guard overrides (styleChange {} acT) acT == [{ node := 7, property := "width", value := "15px", transition := true }]
-- no change, no transition; a value that does not interpolate starts none
#guard (styleChange {} (acOf [(7, [("width", "20px")])] [(7, [("transition-duration", "100s")])] "" [(7, [("width", "20px")])])).anims.size == 0
#guard (styleChange {} (acOf [(7, [("width", "auto")])] [(7, [("transition-duration", "100s")])] "" [(7, [("width", "20px")])])).anims.size == 0
-- transition-property: all (the initial value) with allow-discrete flips at 50%
private def acD : Access := acOf [(7, [("width", "auto")])]
  [(7, [("transition-duration", "100s"), ("transition-delay", "-50s"), ("transition-behavior", "allow-discrete"),
        ("transition-timing-function", "steps(1, end)")])] "" [(7, [("width", "20px")])]
#guard overrides (styleChange {} acD) acD == [{ node := 7, property := "width", value := "20px", transition := true }]

/-! ## Tests: animated values in the cascade (`CSS.withAnimated`; CSS Cascade 4 §6.1) -/

/-- The computed width and colour of the first `div` of a page, with animated values on
it, as `(width, colour of its first child)`. -/
private def cascadeOf (html css : String) (animated : List (String × String × Bool)) : Option (String × String) := do
  let dom := DOM.parseHtmlDocument html
  let rules ← (CSS.parse css).toOption
  let div ← (List.range dom.size).find? fun i => (dom.get i).lname == "div"
  let span ← (List.range dom.size).find? fun i => (dom.get i).lname == "span"
  let state : CSS.ElementState := { animated := animated.map fun (p, v, t) => (div, p, v, t) }
  let styles ← (CSS.computeAll dom rules 1 state).toOption
  let w := match (styles[div]?).map (·.width) with
    | some (.px x) => toString x.toUInt64
    | _ => "?"
  let c := match (styles[span]?).map (·.color) with
    | some c => toString (c.r * 255).toUInt64
    | none => "?"
  return (w, c)

private def pageHtml := "<div style=\"width: 10px\"><span>x</span></div>"
-- no animation: the style attribute
#guard cascadeOf pageHtml "div { width: 5px }" [] == some ("10", "0")
-- an animation is above the style attribute and the rules
#guard cascadeOf pageHtml "div { width: 5px }" [("width", "20px", false)] == some ("20", "0")
-- and below an important declaration
#guard cascadeOf pageHtml "div { width: 5px !important }" [("width", "20px", false)] == some ("5", "0")
-- a transition is above an important declaration
#guard cascadeOf pageHtml "div { width: 5px !important }" [("width", "20px", true)] == some ("20", "0")
-- an animated inherited property reaches the descendants
#guard cascadeOf pageHtml "" [("color", "rgb(255, 0, 0)", false)] == some ("10", "255")
-- the animated values of another element do not apply
#guard ((CSS.withAnimated { animated := [(3, "width", "1px", false)] } (fun _ => [])) 4).isEmpty
#guard ((CSS.withAnimated { animated := [(3, "width", "1px", false)] } (fun _ => [])) 3).length == 1

-- an animated value of the last style change starts no transition when the animation ends
#guard (styleChange (noteAnimated {} [{ node := 7, property := "width", value := "10px" }]) acT).anims.size == 0
-- events: a transition of 2 s is run and started at the first frame, ended after 2 s, then retired
private def acE : Access := acOf [(7, [("width", "20px")])]
  [(7, [("transition-property", "width"), ("transition-duration", "2s"), ("transition-timing-function", "linear")])]
  "" [(7, [("width", "10px")])]
private def sE0 : State := tick (styleChange {} acE)
#guard sE0.events.toList.map (fun e => (e.type, e.name, e.elapsed)) == [("transitionrun", "width", 0), ("transitionstart", "width", 0)]
#guard needsFrame sE0
private def sE1 : State := tick { sE0 with now := Fix.ofInt 1000, events := #[] }
#guard sE1.events.isEmpty && overrides sE1 acE == [{ node := 7, property := "width", value := "15px", transition := true }]
private def sE2 : State := tick { sE1 with now := Fix.ofInt 2500 }
#guard sE2.events.toList.map (fun e => (e.type, e.elapsed)) == [("transitionend", Fix.ofInt 2000)]
#guard overrides sE2 acE == [] && !needsFrame { sE2 with events := #[] }
-- a CSS animation: start at the first frame; its element leaves the document: cancel
private def sA0 : State := tick (styleChange {} acA)
#guard sA0.events.toList.map (fun e => (e.type, e.name, e.elapsed)) == [("animationstart", "a1", Fix.ofInt 50000)]
#guard ((tick { sA0 with events := #[] } (fun _ => false)).events.toList.map (·.type)) == ["animationcancel"]

end L4Factoidal.Rendering.Animation
