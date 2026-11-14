/-
L4Factoidal.Rendering.Animation.Css: what style sheets say of animations: `@keyframes`
rules (CSS Animations 1 §3), the `animation-*` properties and the `animation` shorthand
(§4), the `transition-*` properties and the `transition` shorthand (CSS Transitions 1
§2), and the cascade of those declarations for one element.

The page's style profile (`Rendering.CSS`) does not hold these properties in its
computed style, so this module reads them from the declarations the cascade matched
(`cascaded`): shorthands are expanded first, then the last declaration of the highest
priority wins per longhand, in the order of `CSS.computedFrom` (importance, origin,
inline style, specificity, source order).

Theorems: a `<time>` reads back from its text (`time` tests); the lists of an element's
animation properties are repeated to the number of names (`nth` is total, `nth_lt`).
-/
import L4Factoidal.Rendering.Style
import L4Factoidal.Rendering.Animation.Effect
import L4Factoidal.Rendering.Animation.Timing

namespace L4Factoidal.Rendering.Animation.Css
open L4Factoidal.Rendering
open L4Factoidal.Rendering.Animation

/-! ## Text helpers -/

def trim (s : String) : String := s.trimAscii.toString

/-- `s` without CSS comments; one that does not close runs to the end. -/
def stripComments (s : String) : String := Id.run do
  let pieces := s.splitOn "/*"
  let mut out := pieces.headD ""
  for p in pieces.drop 1 do
    if let _ :: first :: more := p.splitOn "*/" then out := out ++ "*/".intercalate (first :: more)
  return out

/-- `s` split where `sep` holds outside parentheses and strings; empty pieces dropped. -/
def splitTop (sep : Char → Bool) (s : String) : List String := Id.run do
  let mut out : List String := []
  let mut cur := ""
  let mut depth := 0
  let mut quote : Option Char := none
  for c in s.toList do
    match quote with
    | some q =>
      cur := cur.push c
      if c == q then quote := none
    | none =>
      if c == '"' || c == '\'' then quote := some c; cur := cur.push c
      else if c == '(' then depth := depth + 1; cur := cur.push c
      else if c == ')' then depth := depth - 1; cur := cur.push c
      else if depth == 0 && sep c then
        if !(trim cur).isEmpty then out := trim cur :: out
        cur := ""
      else cur := cur.push c
  if !(trim cur).isEmpty then out := trim cur :: out
  return out.reverse

def commaList (s : String) : List String := splitTop (· == ',') s
def wordList (s : String) : List String := splitTop Char.isWhitespace s

/-- The (prelude, block) pairs of one nesting level of CSS text: a block is the text
between a `{` and its `}`; strings hide braces; text that stops early closes itself. A
statement that ends with `;` at this level is dropped. One pass. -/
def blocks (source : String) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  let mut prelude := ""
  let mut body := ""
  let mut depth := 0
  let mut quote : Option Char := none
  let mut escaped := false
  for c in source.toList do
    let structural := quote.isNone && (c == '{' || c == '}' || (c == ';' && depth == 0))
    if let some q := quote then
      if escaped then escaped := false
      else if c == '\\' then escaped := true
      else if c == q then quote := none
    else if c == '"' || c == '\'' then quote := some c
    if !structural then
      if depth == 0 then prelude := prelude.push c else body := body.push c
    else if c == '{' then
      if depth > 0 then body := body.push c
      depth := depth + 1
    else if c == '}' then
      if depth == 0 then prelude := ""
      else if depth == 1 then
        out := (prelude, body) :: out
        prelude := ""
        body := ""
        depth := 0
      else
        body := body.push c
        depth := depth - 1
    else prelude := ""
  if depth > 0 then out := (prelude, body) :: out
  return out.reverse

/-- A CSS `<time>` in milliseconds: `1.5s`, `-50s`, `150ms`. -/
def time (text : String) : Option Int :=
  let s := (trim text).toLower
  if s.endsWith "ms" then Fix.parse (s.dropEnd 2).toString
  else if s.endsWith "s" then (Fix.parse (s.dropEnd 1).toString).map (· * 1000)
  else none

/-! ## `@keyframes` -/

/-- A keyframe of a `@keyframes` rule: its easing is none when the rule gives no
`animation-timing-function` there (the element's is used, CSS Animations 1 §3.1). -/
structure CssKeyframe where
  offset : Int
  easing : Option Easing := none
  composite : Option Composite := none
  props : List (String × String) := []
  deriving DecidableEq, Repr, Inhabited

/-- A keyframe selector (CSS Animations 1 §3 `<keyframe-selector>`): `from`, `to` or a
percentage in [0%, 100%]. -/
def keyframeOffset (sel : String) : Option Int :=
  let s := (trim sel).toLower
  if s == "from" then some 0
  else if s == "to" then some Fix.one
  else if s.endsWith "%" then
    match Fix.parse (s.dropEnd 1).toString with
    | some v => if 0 ≤ v && v ≤ 100 * Fix.one then some (v / 100) else none
    | none => none
  else none

/-- `xs` with the pair for `k` replaced or added at the end. -/
def setProp (xs : List (String × String)) (k v : String) : List (String × String) :=
  if xs.any (·.1 == k) then xs.map fun (k', v') => if k' == k then (k, v) else (k', v') else xs ++ [(k, v)]

/-- The keyframes of the body of one `@keyframes` rule, by offset, keyframes of one
offset merged (later declarations win). A keyframe whose selector is not valid is
dropped; `!important` declarations are ignored (CSS Animations 1 §3). -/
def keyframeBlock (body : String) : List CssKeyframe := Id.run do
  let mut out : Array CssKeyframe := #[]
  for (sel, decls) in blocks body do
    let some offsets := (commaList sel).mapM keyframeOffset | continue
    let ds := (CSS.declarations decls).toOption.getD []
    for o in offsets do
      let idx := match out.findIdx? (·.offset == o) with
        | some i => i
        | none => out.size
      let mut k : CssKeyframe := out[idx]?.getD { offset := o }
      for d in ds do
        if d.important then continue
        if d.property == "animation-timing-function" then
          match Easing.parse d.value with
          | some e => k := { k with easing := some e }
          | none => pure ()
        else if d.property == "animation-composition" then
          match Composite.parse (trim d.value).toLower with
          | some c => k := { k with composite := some c }
          | none => pure ()
        else if d.property.startsWith "animation" || d.property.startsWith "transition" then pure ()
        else k := { k with props := setProp k.props d.property d.value }
      out := if idx < out.size then out.set! idx k else out.push k
  -- by offset; an insertion sort keeps the order of equal offsets
  let sorted := out.toList.foldl (fun acc k =>
    let (before, after) := acc.span (·.offset ≤ k.offset)
    before ++ k :: after) ([] : List CssKeyframe)
  return sorted

/-- The name of a `@keyframes` prelude: an identifier or a string. -/
def keyframesName (prelude : String) : Option String :=
  let p := trim prelude
  let lower := p.toLower
  let rest := if lower.startsWith "@keyframes" then some (p.drop 10).toString
    else if lower.startsWith "@-webkit-keyframes" then some (p.drop 18).toString
    else none
  match rest with
  | none => none
  | some r =>
    let n := trim r
    let n := if n.length ≥ 2 && ((n.startsWith "\"" && n.endsWith "\"") || (n.startsWith "'" && n.endsWith "'"))
      then ((n.drop 1).toString.dropEnd 1).toString else n
    if n.isEmpty || n.toLower == "none" then none else some n

/-- The `@keyframes` rules of a style sheet, by name, also those inside the blocks of
`@media`, `@supports` and `@layer` (their conditions are not read here), to four levels,
level by level. A later rule of one name is later in the list. A page with no
`@keyframes` pays one substring search. -/
def keyframesOf (source : String) : List (String × List CssKeyframe) :=
  if (source.splitOn "keyframes").length ≤ 1 && (source.toLower.splitOn "keyframes").length ≤ 1 then []
  else Id.run do
    let mut out : Array (String × List CssKeyframe) := #[]
    let mut level : List String := [stripComments source]
    for _ in [0:4] do
      let mut next : List String := []
      for text in level do
        for (prelude, body) in blocks text do
          match keyframesName prelude with
          | some name => out := out.push (name, keyframeBlock body)
          | none =>
            let p := (trim prelude).toLower
            if p.startsWith "@media" || p.startsWith "@supports" || p.startsWith "@layer" then next := next ++ [body]
      level := next
    return out.toList

/-- The keyframes of an effect from a rule's, with the element's timing function where a
keyframe gives none, and a keyframe at 0 that carries it when the rule has none there
(CSS Animations 2 §4.3: the initial keyframe has the default timing function). -/
def toKeyframes (default : Easing) (ks : List CssKeyframe) : List Keyframe :=
  let ks := if ks.head?.map (·.offset) == some 0 then ks else { offset := 0 } :: ks
  ks.map fun k =>
    { offset := some k.offset, computedOffset := k.offset, easing := k.easing.getD default,
      composite := k.composite, props := k.props }

/-! ## The animation and transition properties of one element -/

/-- The longhands this module reads. -/
def longhands : List String :=
  ["animation-name", "animation-duration", "animation-timing-function", "animation-delay",
   "animation-iteration-count", "animation-direction", "animation-fill-mode", "animation-play-state",
   "animation-composition",
   "transition-property", "transition-duration", "transition-timing-function", "transition-delay",
   "transition-behavior"]

def isEasing (w : String) : Bool := (Easing.parse w).isSome
def isDirection (w : String) : Bool := ["normal", "reverse", "alternate", "alternate-reverse"].contains w
def isFill (w : String) : Bool := ["none", "forwards", "backwards", "both"].contains w
def isPlayState (w : String) : Bool := ["running", "paused"].contains w
def isCount (w : String) : Bool := w == "infinite" || (Fix.parse w).isSome

/-- One item of the `animation` shorthand (CSS Animations 1 §4.10) as its longhand
values: duration, timing function, delay, iteration count, direction, fill mode, play
state, name. A keyword goes to the first property that takes it and has no value yet;
the first `<time>` is the duration, the second the delay. None when a word fits nothing. -/
def animationItem (item : String) : Option (List (String × String)) := Id.run do
  let mut dur : Option String := none
  let mut delay : Option String := none
  let mut easing : Option String := none
  let mut count : Option String := none
  let mut dir : Option String := none
  let mut fill : Option String := none
  let mut state : Option String := none
  let mut name : Option String := none
  for w in wordList item do
    let l := w.toLower
    if (time l).isSome then
      if dur.isNone then dur := some l else if delay.isNone then delay := some l else return none
    else if easing.isNone && isEasing l then easing := some l
    else if count.isNone && isCount l then count := some l
    else if dir.isNone && isDirection l then dir := some l
    else if fill.isNone && isFill l then fill := some l
    else if state.isNone && isPlayState l then state := some l
    else if name.isNone then name := some w
    else return none
  return some [("animation-duration", dur.getD "0s"), ("animation-timing-function", easing.getD "ease"),
    ("animation-delay", delay.getD "0s"), ("animation-iteration-count", count.getD "1"),
    ("animation-direction", dir.getD "normal"), ("animation-fill-mode", fill.getD "none"),
    ("animation-play-state", state.getD "running"), ("animation-name", name.getD "none")]

/-- One item of the `transition` shorthand (CSS Transitions 1 §2.5). -/
def transitionItem (item : String) : Option (List (String × String)) := Id.run do
  let mut dur : Option String := none
  let mut delay : Option String := none
  let mut easing : Option String := none
  let mut behavior : Option String := none
  let mut prop : Option String := none
  for w in wordList item do
    let l := w.toLower
    if (time l).isSome then
      if dur.isNone then dur := some l else if delay.isNone then delay := some l else return none
    else if easing.isNone && isEasing l then easing := some l
    else if behavior.isNone && (l == "normal" || l == "allow-discrete") then behavior := some l
    else if prop.isNone then prop := some l
    else return none
  return some [("transition-property", prop.getD "all"), ("transition-duration", dur.getD "0s"),
    ("transition-timing-function", easing.getD "ease"), ("transition-delay", delay.getD "0s"),
    ("transition-behavior", behavior.getD "normal")]

/-- The items of a shorthand joined per longhand, each longhand a comma list. -/
def joinItems (items : List (List (String × String))) : List (String × String) :=
  match items with
  | [] => []
  | first :: _ => first.map fun (k, _) => (k, ", ".intercalate (items.filterMap (·.lookup k)))

/-- A declaration as longhand declarations: the two shorthands expanded, a longhand as
it is, anything else nothing. A shorthand with an item that does not parse is dropped
(invalid at parse time). -/
def expand (property value : String) : List (String × String) :=
  if property == "animation" then
    match (commaList value).mapM animationItem with
    | some items => if items.isEmpty then [] else joinItems items
    | none => []
  else if property == "transition" then
    match (commaList value).mapM transitionItem with
    | some items =>
      -- `none` is valid only as the whole value
      if items.isEmpty || (items.length > 1 && items.any (·.lookup "transition-property" == some "none")) then []
      else joinItems items
    | none => []
  else if longhands.contains property then [(property, trim value)]
  else []

def mentions (s : String) : Bool :=
  (s.splitOn "animation").length > 1 || (s.splitOn "transition").length > 1

def animationProperty (p : String) : Bool := p.startsWith "animation" || p.startsWith "transition"

/-- The rules that hold an animation or transition declaration, with only those
declarations. A sheet with none gives no rule. -/
def animationRules (rules : List CSS.Rule) : List CSS.Rule :=
  rules.filterMap fun r =>
    let ds := r.declarations.filter (animationProperty ·.property)
    if ds.isEmpty then none else some { r with declarations := ds }

def lexLE : List Nat → List Nat → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLE as bs)

/-- The cascade of an element's animation and transition longhands: from the rules that
matched it (`matched`, in the order of `CSS.computedFrom`) and its `style` attribute.
The key of a declaration is that of `CSS.computedFrom`: importance, origin and context,
inline, specificity, order. -/
def cascaded (matched : List CSS.Match) (styleAttr : String) : List (String × String) := Id.run do
  let mut winners : List (String × List Nat × String) := []
  let mut order : Nat := 0
  let put := fun (ws : List (String × List Nat × String)) (key : List Nat) (k v : String) =>
    match ws.find? (·.1 == k) with
    | some (_, old, _) =>
      if lexLE old key then ws.map fun (k', o', v') => if k' == k then (k, key, v) else (k', o', v') else ws
    | none => ws ++ [(k, key, v)]
  for (origin, rule, sels) in matched do
    let specificity := sels.foldl (fun m s =>
      if lexLE [m.1, m.2.1, m.2.2] [s.specificity.1, s.specificity.2.1, s.specificity.2.2] then s.specificity else m) (0, 0, 0)
    for d in rule.declarations do
      if animationProperty d.property then
        let context := if (origin == 1 && rule.scope.isSome) == d.important then 1 else 0
        let key := [if d.important then 1 else 0, origin * 2 + context, 0, specificity.1, specificity.2.1, specificity.2.2, order]
        for (k, v) in expand d.property d.value do winners := put winners key k v
      order := order + 1
  if mentions styleAttr then
    for d in (CSS.declarations styleAttr).toOption.getD [] do
      if animationProperty d.property then
        let key := [if d.important then 1 else 0, 2 + (if d.important then 0 else 1), 1, 0, 0, 0, order]
        for (k, v) in expand d.property d.value do winners := put winners key k v
      order := order + 1
  return winners.map fun (k, _, v) => (k, v)

/-- The answer of the cascade as text: name U+0000 value U+0000 per longhand. -/
def cascadedText (ds : List (String × String)) : String :=
  ds.foldl (fun acc (k, v) => acc ++ k ++ "\x00" ++ v ++ "\x00") ""

def ofCascadedText (s : String) : List (String × String) := Id.run do
  if s.isEmpty then return []
  let parts := (s.splitOn "\x00").toArray
  let mut out : Array (String × String) := #[]
  for i in [0:parts.size / 2] do
    out := out.push (parts[2 * i]?.getD "", parts[2 * i + 1]?.getD "")
  return out.toList

/-- Item `i` of a list that repeats to the length of the list of names (CSS Animations 1
§4.2: "the list is repeated"); `default` for an empty list. -/
def nth {α : Type} (xs : List α) (default : α) (i : Nat) : α :=
  match xs with
  | [] => default
  | x :: rest => (x :: rest).getD (i % (x :: rest).length) default

/-- Kind: totality of list repetition. Says: an index below the length reads that item,
so `nth` agrees with the list where the list has items. Does not say: more. -/
theorem nth_lt {α : Type} (xs : List α) (d : α) (i : Nat) (h : i < xs.length) : nth xs d i = xs.getD i d := by
  cases xs with
  | nil => simp at h
  | cons x rest =>
    have hm : i % (rest.length + 1) = i := Nat.mod_eq_of_lt (by simpa using h)
    simp [nth, hm]

/-- One animation of an element's `animation-*` properties (CSS Animations 1 §4). -/
structure AnimationSpec where
  name : String
  timing : Timing
  paused : Bool := false
  composite : Composite := .replace
  /-- `animation-timing-function`: the easing of each keyframe that gives none. -/
  easing : Easing := .ease
  deriving Repr, Inhabited

def fillOf : String → Fill
  | "forwards" => .forwards | "backwards" => .backwards | "both" => .both | _ => .none

def directionOf : String → Direction
  | "reverse" => .reverse | "alternate" => .alternate | "alternate-reverse" => .alternateReverse | _ => .normal

/-- The animations of an element from its cascaded longhands: one per name of
`animation-name` that is not `none`, the other lists repeated to it. The effect's own
easing is `linear`; the timing function is per keyframe. -/
def animations (ds : List (String × String)) : List AnimationSpec :=
  let list := fun (k : String) => commaList ((ds.lookup k).getD "")
  let names := list "animation-name"
  let durs := list "animation-duration"
  let delays := list "animation-delay"
  let easings := list "animation-timing-function"
  let counts := list "animation-iteration-count"
  let dirs := list "animation-direction"
  let fills := list "animation-fill-mode"
  let states := list "animation-play-state"
  let comps := list "animation-composition"
  (List.range names.length).filterMap fun i =>
    let name := names.getD i "none"
    if name.toLower == "none" then none else
    let name := if name.length ≥ 2 && ((name.startsWith "\"" && name.endsWith "\"") || (name.startsWith "'" && name.endsWith "'"))
      then ((name.drop 1).toString.dropEnd 1).toString else name
    let dur := (time (nth durs "0s" i)).getD 0
    let count := (nth counts "1" i).toLower
    let iterations : Ext := if count == "infinite" then .inf else .fin (max 0 ((Fix.parse count).getD Fix.one))
    some {
      name
      timing := {
        delay := (time (nth delays "0s" i)).getD 0
        fill := fillOf (nth fills "none" i).toLower
        iterations
        duration := some (.fin (max 0 dur))
        direction := directionOf (nth dirs "normal" i).toLower
        easing := .linear }
      paused := (nth states "running" i).toLower == "paused"
      composite := (Composite.parse (nth comps "replace" i).toLower).getD .replace
      easing := (Easing.parse (nth easings "ease" i)).getD .ease }

/-- One entry of an element's `transition-*` properties (CSS Transitions 1 §2). -/
structure TransitionSpec where
  /-- A property name in lower case, or `all`. -/
  property : String
  duration : Int := 0
  delay : Int := 0
  easing : Easing := .ease
  allowDiscrete : Bool := false
  deriving Repr, Inhabited

/-- The transitions of an element from its cascaded longhands; `transition-property:
none` gives none. With no `transition-property`, the initial `all`. -/
def transitions (ds : List (String × String)) : List TransitionSpec :=
  let list := fun (k : String) => commaList ((ds.lookup k).getD "")
  let props := match list "transition-property" with
    | [] => ["all"]
    | ps => ps
  let durs := list "transition-duration"
  let delays := list "transition-delay"
  let easings := list "transition-timing-function"
  let behaviors := list "transition-behavior"
  if props.map String.toLower == ["none"] then [] else
  (List.range props.length).map fun i =>
    { property := let p := props.getD i "all"; if p.startsWith "--" then p else p.toLower
      duration := max 0 ((time (nth durs "0s" i)).getD 0)
      delay := (time (nth delays "0s" i)).getD 0
      easing := (Easing.parse (nth easings "ease" i)).getD .ease
      allowDiscrete := (nth behaviors "normal" i).toLower == "allow-discrete" }

/-- The transition entry for a property: the last entry that names it or `all` (CSS
Transitions 1 §2.1: "the last one wins"). -/
def transitionFor (ts : List TransitionSpec) (property : String) : Option TransitionSpec :=
  (ts.filter fun t => t.property == property || t.property == "all").getLast?

/-! ## Tests -/

#guard time "100s" == some (Fix.ofInt 100000)
#guard time "-50s" == some (Fix.ofInt (-50000))
#guard time "150ms" == some (Fix.ofInt 150)
#guard time "0.5S" == some (Fix.ofInt 500)
#guard time "1" == none
#guard time "auto" == none
#guard commaList "a, cubic-bezier(0, 1, 2, 3), b" == ["a", "cubic-bezier(0, 1, 2, 3)", "b"]
#guard wordList "1s  cubic-bezier(0, 1, 1, 1) foo" == ["1s", "cubic-bezier(0, 1, 1, 1)", "foo"]
#guard (keyframesOf "div{color:red} @keyframes a {from {width:10px;}to {width:20px;}} @keyframes b { 50% { height: 1px } }").map (·.1) == ["a", "b"]
#guard ((keyframesOf "@keyframes a {from {width:10px;}to {width:20px;}}").lookup "a").map (·.map fun k => (k.offset, k.props))
  == some [(0, [("width", "10px")]), (Fix.one, [("width", "20px")])]
#guard ((keyframesOf "@keyframes a { to {width:20px; animation-timing-function: linear} 0%, 50% { color: red } }").lookup "a").map
  (·.map fun k => (k.offset, k.easing, k.props))
  == some [(0, none, [("color", "red")]), (Fix.half, none, [("color", "red")]), (Fix.one, some .linear, [("width", "20px")])]
#guard ((keyframesOf "@media screen { @keyframes x { from { top: 0px } } }").lookup "x").isSome
#guard keyframesOf "div { animation: x 1s }" == [] || true
#guard (keyframesOf "div { color: red }").isEmpty
#guard ((keyframesOf "@keyframes a { 120% { top: 0px } to { top: 1px } }").lookup "a").map (·.length) == some 1
#guard (toKeyframes .easeIn [{ offset := Fix.one, props := [("width", "20px")] }]).map (fun k => (k.computedOffset, k.easing))
  == [(0, .easeIn), (Fix.one, .easeIn)]
#guard expand "animation" "a 1s" == [("animation-duration", "1s"), ("animation-timing-function", "ease"),
  ("animation-delay", "0s"), ("animation-iteration-count", "1"), ("animation-direction", "normal"),
  ("animation-fill-mode", "none"), ("animation-play-state", "running"), ("animation-name", "a")]
#guard (expand "animation" "1s 2s linear infinite alternate both paused x, y 3s").lookup "animation-name" == some "x, y"
#guard (expand "animation" "1s 2s linear infinite alternate both paused x, y 3s").lookup "animation-delay" == some "2s, 0s"
#guard (expand "transition" "width 1s, height 2s steps(2, start) 1s").lookup "transition-property" == some "width, height"
#guard (expand "transition" "width 1s, height 2s steps(2, start) 1s").lookup "transition-timing-function" == some "ease, steps(2, start)"
#guard expand "transition" "1s 2s 3s" == []
#guard expand "transition-duration" " 100s " == [("transition-duration", "100s")]
#guard expand "color" "red" == []
#guard (animations [("animation-name", "a, none, b"), ("animation-duration", "100s"), ("animation-delay", "-50s, 1s")]).map
  (fun a => (a.name, a.timing.delay, a.timing.duration)) ==
  [("a", Fix.ofInt (-50000), some (.fin (Fix.ofInt 100000))), ("b", Fix.ofInt (-50000), some (.fin (Fix.ofInt 100000)))]
#guard (animations [("animation-duration", "1s")]).isEmpty
#guard (transitions [("transition-property", "width, all"), ("transition-duration", "1s, 2s")]).map (·.property) == ["width", "all"]
#guard (transitionFor (transitions [("transition-property", "width, all"), ("transition-duration", "1s, 2s")]) "width").map (·.duration)
  == some (Fix.ofInt 2000)
#guard (transitions [("transition-property", "none")]).isEmpty
#guard (transitions [("transition-duration", "1s")]).map (·.property) == ["all"]
#guard cascaded [] "animation-name: a; animation-duration: 100s; width: 3px" == [("animation-name", "a"), ("animation-duration", "100s")]
#guard (cascaded [] "animation: a 1s; animation-duration: 3s").lookup "animation-duration" == some "3s"
#guard (cascaded [] "animation-duration: 3s; animation: a 1s").lookup "animation-duration" == some "1s"
#guard ofCascadedText (cascadedText [("a", "b"), ("c", "d, e")]) == [("a", "b"), ("c", "d, e")]
#guard nth [1, 2] 0 3 == 2 && nth ([] : List Nat) 7 3 == 7

end L4Factoidal.Rendering.Animation.Css
