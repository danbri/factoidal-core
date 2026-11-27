import SVG
import L4Factoidal.Rendering.Smil

/-! # SVG Tiny 1.2 animation at a document time

SVG Tiny 1.2 chapter 16 (Animation), which takes its timing from SMIL 2.1: the
document at document time `t` (milliseconds; the document begin is 0) is the
document with each animated attribute set to its presentation value at `t`, and with
no animation element. `snapshot t root` computes that document. The strict reader
(`NativeSVG`) then draws it as a static document.

What is computed:

* targets: `xlink:href` (or `href`) to an element of the document, or the parent
  element (§16.2.4);
* timing (§16.2.8, SMIL 2.1 §10): `begin` and `end` lists of offsets, syncbase values
  (`id.begin`, `id.end`, also `id.beginEvent` and `id.endEvent`, which fire at the same
  times), `load` (at 0), user-interface events (no event occurs, so they give no
  instance), `indefinite`; `dur`, `repeatCount`, `repeatDur`, `min`, `max`; the
  intervals that `restart` (`always`, `whenNotActive`, `never`) allows; `fill`
  (`remove`, `freeze`);
* the animation function (§16.2.10 to §16.2.15): `values`, `from`, `to`, `by` (and
  to-animation from the underlying value), `calcMode` (`discrete`, `linear`, `paced`,
  `spline` with `keySplines`), `keyTimes`, `additive`, `accumulate`;
* the sandwich (SMIL 2.1 §3.5.4): animations of one attribute are applied in order of
  the begin of their current interval, then of document order; `replace` sets the
  value, `sum` adds to the value below;
* `animateTransform` (§16.2.16): its value is a transform function appended to the
  attribute (`sum`) or put in its place (`replace`);
* `discard` (§16.2.19): its target is not in the document from its begin on.

Every other feature is refused with a named reason (`throw`), never passed over:
`animateMotion`, repeat events, path-data interpolation, units on values, `inherit` in
values, a property animated while a `style` attribute also sets it, and attributes this
table does not name. -/
namespace NativeSVGAnimate

open L4Factoidal.XML

def svgNS := "http://www.w3.org/2000/svg"
def xlinkNS := "http://www.w3.org/1999/xlink"
def xmlNS := "http://www.w3.org/XML/1998/namespace"

/-- The animation elements of §16.2. -/
def animationTags : List String := ["set","animate","animateColor","animateTransform","animateMotion"]

private def trim (s : String) : String := s.trimAscii.toString

private def plain (attrs : List NamespaceAttribute) (key : String) : Option String :=
  (attrs.find? fun a => a.name.namespace_.isNone && a.name.localPart == key).map (·.value)

private def hrefOf (attrs : List NamespaceAttribute) : Option String :=
  match attrs.find? (fun a => a.name.namespace_ == some xlinkNS && a.name.localPart == "href") with
  | some a => some a.value
  | none => plain attrs "href"

private def isSvg (name : ExpandedName) (tag : String) : Bool :=
  name.namespace_ == some svgNS && name.localPart == tag

/-! ## The element index -/

/-- One element of the document, with its source path. -/
structure Entry where
  path : List Nat
  name : ExpandedName
  attrs : List NamespaceAttribute
  children : List NamespaceNode
  /-- Index of the parent element in the index; `none` for the root. -/
  parent : Option Nat
  deriving Inhabited

/-- The elements of `root` in document order (a loop over a list of open frames; no stack
frame per element), at most `maxNodes`. -/
def index (root : NamespaceNode) (maxNodes : Nat := 200000) : Except String (Array Entry) := do
  let mut out : Array Entry := #[]
  let mut pending : List (NamespaceNode × List Nat × Option Nat) := [(root,[],none)]
  for _ in [:maxNodes] do
    match pending with
    | [] => return out
    | (node,path,parent)::rest =>
      pending := rest
      match node with
      | .other _ => pure ()
      | .element name attrs children =>
        let me := out.size
        out := out.push {path,name,attrs,children,parent}
        pending := (children.zipIdx.map fun (child,i) => (child,path ++ [i],some me)) ++ pending
  if pending.isEmpty then return out
  throw "animation: document has more elements than the animation pass reads"

/-! ## Times (SMIL 2.1 §10.4.1, SVG Tiny 1.2 §16.2.7) -/

/-- A signed clock value in milliseconds. -/
def signedClock (source : String) : Option Int :=
  let s := trim source
  if s.startsWith "-" then (L4Factoidal.Rendering.Smil.clockValue (s.drop 1).toString).map fun v => -(Int.ofNat v)
  else (L4Factoidal.Rendering.Smil.clockValue (if s.startsWith "+" then (s.drop 1).toString else s)).map Int.ofNat

/-- One item of a `begin` or `end` list, resolved against the index. -/
inductive TimeItem where
  | offset (ms : Int)
  /-- The begin (`isEnd = false`) or end of each interval of animation `element`, plus `ms`. -/
  | sync (element : Nat) (isEnd : Bool) (ms : Int)
  /-- The begin of repetition `n` of each interval of animation `element` (`id.repeat(n)`), plus
  `ms`; `n = none`: every repetition (`id.repeatEvent`). -/
  | repeat_ (element : Nat) (n : Option Nat) (ms : Int)
  /-- A time that is never resolved in a snapshot: `indefinite`, or an event of user input. -/
  | unresolved
  deriving Inhabited, BEq

/-- Events of user input (SVG Tiny 1.2 §13.3 and appendix A): none occurs while a
document is drawn at a time, so a time that waits for one is not resolved. -/
def userEvents : List String :=
  ["click","activate","DOMActivate","focusin","focusout","DOMFocusIn","DOMFocusOut","mousedown","mouseup",
   "mouseover","mouseout","mousemove","mousewheel","keydown","keyup","textInput","resize","scroll","zoom",
   "SVGResize","SVGScroll","SVGZoom","error","abort","unload","SVGUnload","SVGAbort","SVGError"]

/-- Split `base[+|-clock]` at the last sign whose rest is a clock value. -/
private def splitOffset (item : String) : String × Int := Id.run do
  let chars := item.toList
  let mut best : Option (Nat × Int) := none
  for i in [1:chars.length] do
    let c := chars[i]!
    if c == '+' || c == '-' then
      let rest := String.ofList (chars.drop (i+1))
      if let some v := L4Factoidal.Rendering.Smil.clockValue rest then
        best := some (i,if c == '-' then -(Int.ofNat v) else Int.ofNat v)
  match best with
  | some (i,v) => (trim (String.ofList (chars.take i)),v)
  | none => (item,0)

/-- A `begin` or `end` value list (§16.2.7). `self` is the animation's own index (an event
with no id is on the target, which only matters for user input here). -/
def timeList (ids : String → Option Nat) (source : String) : Except String (List TimeItem) := do
  let mut out : List TimeItem := []
  for raw in source.splitOn ";" do
    let item := trim raw
    if item.isEmpty then continue
    if item == "indefinite" then out := out ++ [.unresolved]; continue
    if let some ms := signedClock item then out := out ++ [.offset ms]; continue
    if item.startsWith "accessKey(" then out := out ++ [.unresolved]; continue
    if item.startsWith "wallclock(" then throw "animation: wallclock time values unsupported"
    -- An offset that is not a clock value is a syntax error: the list as a whole is in error,
    -- which is the same as `indefinite` (SVG Tiny 1.2 §16.2.7; W3C test animate-elem-225-t).
    if item.startsWith "+" || item.startsWith "-" || item.startsWith "." || item.front.isDigit then
      return [.unresolved]
    let (base,ms) := splitOffset item
    -- `Id-value "." name`: the id is all before the last full stop.
    let (id,event) := match base.splitOn "." with
      | [e] => (none,e)
      | parts => (some (String.intercalate "." (parts.dropLast)),parts.getLast!)
    let id := id.map trim
    let event := trim event
    if event == "begin" || event == "end" || event == "beginEvent" || event == "endEvent" then
      let some name := id | throw s!"animation: {event} with no element id"
      let some element := ids name | throw s!"animation: syncbase id not in the document: {name}"
      out := out ++ [.sync element (event == "end" || event == "endEvent") ms]
    else if event == "load" || event == "SVGLoad" then out := out ++ [.offset ms]
    else if userEvents.contains event then out := out ++ [.unresolved]
    else if event == "repeatEvent" || (event.startsWith "repeat(" && event.endsWith ")") then
      let some name := id | throw s!"animation: {event} with no element id"
      let some element := ids name | throw s!"animation: syncbase id not in the document: {name}"
      if event == "repeatEvent" then out := out ++ [.repeat_ element none ms]
      else
        let some n := ((event.drop 7).dropEnd 1).toString.trimAscii.toString.toNat? | throw s!"animation: invalid repeat value: {item}"
        out := out ++ [.repeat_ element (some n) ms]
    else throw s!"animation: time value unsupported: {item}"
  return out

/-- A duration attribute (`dur`, `repeatDur`, `min`, `max`): `some none` is `indefinite`. -/
private def durationOf (key : String) (source : Option String) (allowMedia : Bool := false) :
    Except String (Option (Option Int)) := do
  let some s := source.map trim | return none
  if s == "indefinite" || (allowMedia && s == "media") then return some none
  match L4Factoidal.Rendering.Smil.clockValue s with
  | some v => return some (some (Int.ofNat v))
  | none => throw s!"animation: invalid {key}: {s}"

/-- The timing attributes of one animation element. -/
structure Timing where
  begins : List TimeItem
  ends : List TimeItem
  endGiven : Bool
  /-- The simple duration; `none`: indefinite. -/
  dur : Option Int
  repeatCount : Option (Option Float)
  repeatDur : Option (Option Int)
  minDur : Int
  maxDur : Option Int
  restart : String
  freeze : Bool
  deriving Inhabited

def timingOf (ids : String → Option Nat) (attrs : List NamespaceAttribute) (discard : Bool := false) :
    Except String Timing := do
  let begins ← match plain attrs "begin" with
    | none => pure [.offset 0]
    | some b => timeList ids b
  if discard then
    return ({
      begins := begins, ends := [], endGiven := false, dur := some 0, repeatCount := none,
      repeatDur := none, minDur := 0, maxDur := none, restart := "never", freeze := false } : Timing)
  let endGiven := (plain attrs "end").isSome
  let ends ← timeList ids ((plain attrs "end").getD "")
  let dur ← match ← durationOf "dur" (plain attrs "dur") true with
    | none => pure none
    | some none => pure none
    | some (some 0) => throw "animation: dur of 0 is in error"
    | some (some d) => pure (some d)
  let repeatCount ← match (plain attrs "repeatCount").map trim with
    | none => pure none
    | some "indefinite" => pure (some none)
    | some s => match L4Factoidal.Rendering.CSS.number s |>.toOption with
      | some k => if k > 0 then pure (some (some k)) else throw "animation: repeatCount must be more than 0"
      | none => throw s!"animation: invalid repeatCount: {s}"
  let repeatDur ← durationOf "repeatDur" (plain attrs "repeatDur")
  -- An invalid or negative `min` or `max` is ignored (SMIL 2.0 §10.3.3; W3C animate-elem-65-t).
  let clock := fun (key : String) => (plain attrs key).bind fun v => L4Factoidal.Rendering.Smil.clockValue (trim v)
  let minDur : Int := ((clock "min").map Int.ofNat).getD 0
  let maxDur : Option Int := (clock "max").map Int.ofNat
  let (minDur,maxDur) := match maxDur with
    | some m => if minDur > m then (0,none) else (minDur,some m)
    | none => (minDur,none)
  let restart := trim ((plain attrs "restart").getD "always")
  if !["always","whenNotActive","never"].contains restart then throw s!"animation: invalid restart: {restart}"
  let fillV := trim ((plain attrs "fill").getD "remove")
  if !["remove","freeze"].contains fillV then throw s!"animation: invalid fill: {fillV}"
  return {begins,ends,endGiven,dur,repeatCount,repeatDur,minDur,maxDur,restart,freeze:=fillV == "freeze"}

private def minOpt (a b : Option Int) : Option Int :=
  match a, b with
  | some x, some y => some (min x y)
  | some x, none => some x
  | none, y => y

/-- The active duration of an interval that begins at `b` with end `e` (SMIL 2.1 §10.3.4). -/
def activeDuration (tm : Timing) (b : Int) (e : Option Int) : Option Int :=
  let iad : Option Int :=
    if tm.repeatCount.isNone && tm.repeatDur.isNone then tm.dur else
    let byCount : Option Int := match tm.repeatCount, tm.dur with
      | some (some k), some d => some (Float.toInt64 (Float.floor (Float.ofInt d * k)) |>.toInt)
      | _, _ => none
    let byCount := if tm.repeatCount.isNone then none else byCount
    match tm.repeatCount.isSome, tm.repeatDur with
    | true, some rd => minOpt byCount rd
    | true, none => byCount
    | false, some rd => rd
    | false, none => tm.dur
  let pad := match e with
    | some e => minOpt iad (some (e-b))
    | none => iad
  let clampedMax := match pad, tm.maxDur with
    | some p, some m => some (min p m)
    | none, some m => some m
    | p, none => p
  clampedMax.map (max tm.minDur)

/-- One interval: its begin and its end (`none`: indefinite). -/
structure Interval where
  b : Int
  e : Option Int
  deriving Inhabited, Repr, BEq

private def insertSorted (x : Int) : List Int → List Int
  | [] => [x]
  | y::ys => if x < y then x::y::ys else if x == y then y::ys else y::insertSorted x ys

private def sortUnique (xs : List Int) : List Int := xs.foldl (fun acc x => insertSorted x acc) []

/-- The intervals of an element (SMIL 2.1 §10.4.3) from its resolved begin and end instance
times, in begin order. -/
def intervals (tm : Timing) (begins ends : List Int) : List Interval := Id.run do
  let ends := sortUnique ends
  let endUnresolved := tm.ends.any (· == .unresolved)
  let mut out : Array Interval := #[]
  for b in sortUnique begins do
    if let some last := out.back? then
      let during := match last.e with | none => true | some e => b < e
      if during then
        if b ≤ last.b || tm.restart != "always" then continue
        -- `restart="always"`: a begin in the active interval ends it there.
        out := out.pop.push {last with e := some b}
      else if tm.restart == "never" then break
    let e := ends.find? (· ≥ b)
    -- An end list of resolved times only, none at or after this begin: no interval.
    if e.isNone && tm.endGiven && !endUnresolved && !ends.isEmpty then continue
    let ad := activeDuration tm b e
    out := out.push {b,e:=ad.map (b+·)}
  return out.toList

/-! ## Attributes and values -/

inductive Kind where
  | number
  | numberList
  | colour
  /-- `fill`, `stroke`, `viewport-fill`: a colour, or a value that is not interpolated. -/
  | paint
  | transform
  /-- Path data: interpolated number by number when two values have the same commands. -/
  | pathData
  /-- A value that is not interpolated: `animate` steps through it as `discrete`. -/
  | discrete
  deriving Inhabited, BEq

/-- An animatable attribute: its kind, whether it is inherited, its initial value, and its
namespace (`xlink:href`). -/
structure AttrInfo where
  kind : Kind
  inherited : Bool
  initial : String
  ns : Option String := none
  deriving Inhabited

/-- The attributes this pass animates (SVG Tiny 1.2 appendix C, property index; the
"Animatable" column of each element's attribute table). -/
def attrInfo (name : String) : Option AttrInfo :=
  match name with
  | "x" | "y" | "cx" | "cy" | "r" | "rx" | "ry" | "x1" | "y1" | "x2" | "y2" | "width" | "height" =>
    some {kind:=.number,inherited:=false,initial:="0"}
  | "opacity" => some {kind:=.number,inherited:=false,initial:="1"}
  | "fill-opacity" | "stroke-opacity" => some {kind:=.number,inherited:=true,initial:="1"}
  | "stop-opacity" | "solid-opacity" | "viewport-fill-opacity" => some {kind:=.number,inherited:=false,initial:="1"}
  | "stroke-width" => some {kind:=.number,inherited:=true,initial:="1"}
  | "stroke-miterlimit" => some {kind:=.number,inherited:=true,initial:="4"}
  | "stroke-dashoffset" => some {kind:=.number,inherited:=true,initial:="0"}
  | "offset" => some {kind:=.number,inherited:=false,initial:="0"}
  | "points" | "viewBox" => some {kind:=.numberList,inherited:=false,initial:=""}
  | "fill" => some {kind:=.paint,inherited:=true,initial:="#000000"}
  | "stroke" => some {kind:=.paint,inherited:=true,initial:="none"}
  | "viewport-fill" => some {kind:=.paint,inherited:=false,initial:="none"}
  | "color" => some {kind:=.colour,inherited:=true,initial:="#000000"}
  | "stop-color" | "solid-color" => some {kind:=.colour,inherited:=false,initial:="#000000"}
  | "transform" => some {kind:=.transform,inherited:=false,initial:=""}
  | "visibility" => some {kind:=.discrete,inherited:=true,initial:="visible"}
  | "display" => some {kind:=.discrete,inherited:=false,initial:="inline"}
  | "fill-rule" => some {kind:=.discrete,inherited:=true,initial:="nonzero"}
  | "stroke-linecap" => some {kind:=.discrete,inherited:=true,initial:="butt"}
  | "stroke-linejoin" => some {kind:=.discrete,inherited:=true,initial:="miter"}
  | "stroke-dasharray" => some {kind:=.numberList,inherited:=true,initial:="none"}
  -- The initial value `medium` is 16 user units, as the text lowering takes it (`TextState`).
  | "font-size" => some {kind:=.number,inherited:=true,initial:="16"}
  | "text-anchor" => some {kind:=.discrete,inherited:=true,initial:="start"}
  | "pointer-events" => some {kind:=.discrete,inherited:=true,initial:="visiblePainted"}
  | "font-family" => some {kind:=.discrete,inherited:=true,initial:="sans-serif"}
  | "font-style" => some {kind:=.discrete,inherited:=true,initial:="normal"}
  | "font-weight" => some {kind:=.discrete,inherited:=true,initial:="normal"}
  | "font-variant" => some {kind:=.discrete,inherited:=true,initial:="normal"}
  | "display-align" => some {kind:=.discrete,inherited:=true,initial:="auto"}
  | "focusable" => some {kind:=.discrete,inherited:=false,initial:="auto"}
  | "d" => some {kind:=.pathData,inherited:=false,initial:=""}
  | "xlink:href" => some {kind:=.discrete,inherited:=false,initial:="",ns:=some xlinkNS}
  | _ => none

/-- A value of the animation function. -/
inductive AValue where
  | nums (v : Array Float)
  /-- Red, green, blue on 0 to 255 (sums may leave the range; it is clamped on output). -/
  | rgb (r g b : Float)
  | str (s : String)
  /-- Path data: its tokens with `none` at each number, and the numbers. -/
  | path (shape : List (Option Char)) (v : Array Float)
  /-- `inherit`: the value of the parent element, read when the animation is applied. -/
  | inherit
  deriving Inhabited, Repr

private def numList (s : String) : Except String (Array Float) := do
  let items := ((s.replace "," " ").splitOn " ").map trim |>.filter (!·.isEmpty)
  let out ← items.mapM fun item => do
    if item.toList.any (fun ch => ch.isAlpha && ch != 'e' && ch != 'E') then
      throw s!"animation: value with a unit unsupported: {item}"
    NativeSVG.number item
  return out.toArray

/-- Parameters of each path command (SVG Tiny 1.2 §9.3.1). -/
private def pathArity (c : Char) : Option Nat :=
  match c.toUpper with
  | 'M' | 'L' | 'T' => some 2
  | 'H' | 'V' => some 1
  | 'C' => some 6
  | 'S' | 'Q' => some 4
  | 'A' => some 7
  | 'Z' => some 0
  | _ => none

/-- Path data in absolute commands, one command for each segment (the implicit repetition of a
command made explicit): the form in which two path values are compatible when they have the
same command letters, whatever the case of the source (W3C test animate-elem-83-t mixes `L`
and `l`, `S` and `s`, `T` and `t`). -/
def absolutePath (source : String) : Except String (List (Char × Array Float)) := do
  let tokens ← NativeSVGPath.tokenList source
  let mut out : Array (Char × Array Float) := #[]
  let mut cmd : Option Char := none
  let mut args : Array Float := #[]
  let mut cx : Float := 0
  let mut cy : Float := 0
  let mut sx : Float := 0
  let mut sy : Float := 0
  -- The token list ends with a sentinel command so the last command is emitted.
  for tok in tokens ++ [.inl '!'] do
    match tok with
    | .inr n =>
      let some c := cmd | throw "animation: path data begins with a number"
      args := args.push (← NativeSVG.number n)
      let some k := pathArity c | throw s!"animation: unknown path command {c}"
      if k == 0 then throw "animation: numbers after Z in path data"
      if args.size == k then
        let rel := c.isLower
        let ox : Float := if rel then cx else 0
        let oy : Float := if rel then cy else 0
        let up := c.toUpper
        let abs : Array Float := match up with
          | 'H' => #[args[0]!+ox]
          | 'V' => #[args[0]!+oy]
          | 'A' => #[args[0]!,args[1]!,args[2]!,args[3]!,args[4]!,args[5]!+ox,args[6]!+oy]
          | _ => args.mapIdx fun i v => v + (if i % 2 == 0 then ox else oy)
        out := out.push (up,abs)
        match up with
        | 'H' => cx := abs[0]!
        | 'V' => cy := abs[0]!
        | _ => cx := abs[abs.size-2]!; cy := abs[abs.size-1]!
        if up == 'M' then sx := cx; sy := cy
        args := #[]
        -- After a moveto, further pairs are lineto (relative after `m`).
        if up == 'M' then cmd := some (if rel then 'l' else 'L')
    | .inl c =>
      if !args.isEmpty then throw "animation: path command with too few numbers"
      if c == '!' then break
      let some k := pathArity c | throw s!"animation: unknown path command {c}"
      if k == 0 then
        out := out.push ('Z',#[]); cx := sx; cy := sy; cmd := none
      else cmd := some c
  return out.toList

/-- Read one value of attribute `info`. A paint that is not a colour is a string. -/
def readValue (info : AttrInfo) (source : String) : Except String AValue := do
  let s := trim source
  if s == "inherit" then return .inherit
  match info.kind with
  | .number =>
    let v ← numList s
    if v.size != 1 then throw s!"animation: one number expected: {s}"
    return .nums v
  | .numberList => if s == "none" then return .str s else return .nums (← numList s)
  | .pathData =>
    let commands ← absolutePath s
    let shape := commands.flatMap fun (c,p) => some c :: p.toList.map fun _ => none
    return .path shape (commands.foldl (fun acc (_,p) => acc ++ p) #[])
  | .transform => return .nums (← numList s)
  | .colour =>
    let c ← NativeSVG.colourOf s
    return .rgb (c.r*255) (c.g*255) (c.b*255)
  | .paint =>
    match NativeSVG.colourOf s with
    | .ok c => if s.toLower == "currentcolor" then return .str s else return .rgb (c.r*255) (c.g*255) (c.b*255)
    | .error _ => return .str s
  | .discrete => return .str s

private def fmt (x : Float) : String :=
  let r := (x*1000000).round/1000000
  if r == r.round && r.abs < 1e15 then toString (r.toInt64.toInt) else toString r

private def clamp255 (x : Float) : Nat := (max 0 (min 255 x.round)).toUInt32.toNat

private def hex2 (n : Nat) : String :=
  let d := "0123456789abcdef".toList
  String.ofList [d[n/16]!,d[n%16]!]

/-- A value written back as attribute text. -/
def writeValue (kind : Kind) (typ : String) : AValue → String
  | .nums v =>
    let items := String.intercalate " " (v.toList.map fmt)
    if kind == .transform then s!"{typ}({items})" else items
  | .rgb r g b => "#" ++ hex2 (clamp255 r) ++ hex2 (clamp255 g) ++ hex2 (clamp255 b)
  | .str s => s
  | .path shape v => Id.run do
    let mut out : Array String := #[]
    let mut i := 0
    let mut command := ' '
    let mut k := 0
    for item in shape do
      match item with
      | some c => out := out.push (String.singleton c); command := c; k := 0
      | none =>
        -- The two flags of an arc are 0 or 1 (§9.3.8): an interpolated flag is 1 when not 0.
        let x := v.getD i 0
        out := out.push (if command == 'A' && (k == 3 || k == 4) then (if x != 0 then "1" else "0") else fmt x)
        i := i+1; k := k+1
    return String.intercalate " " out.toList
  | .inherit => "inherit"

def interpolable : AValue → Bool
  | .str _ => false
  | .inherit => false
  | _ => true

def add : AValue → AValue → Except String AValue
  | .nums a, .nums b =>
    if a.size != b.size then throw "animation: sum of number lists of different lengths" else
    pure (.nums ((a.zip b).map fun (x,y) => x+y))
  | .rgb a b c, .rgb x y z => pure (.rgb (a+x) (b+y) (c+z))
  | .path s a, .path t b =>
    if s != t || a.size != b.size then throw "animation: path data with different commands"
    else pure (.path s ((a.zip b).map fun (x,y) => x+y))
  | _, _ => throw "animation: sum of values that are not numbers or colours"

def scale (k : Float) : AValue → AValue
  | .nums a => .nums (a.map (·*k))
  | .rgb a b c => .rgb (a*k) (b*k) (c*k)
  | .path s a => .path s (a.map (·*k))
  | v => v

def lerp (a b : AValue) (t : Float) : Except String AValue := do
  let d ← add b (scale (-1) a)
  add a (scale t d)

def distance (typ : String) : AValue → AValue → Float
  | .nums a, .nums b =>
    let d := (a.zip b).map fun (x,y) => (y-x)*(y-x)
    -- `rotate` paces on the angle alone (§16.2.16); the centre is not a distance.
    if typ == "rotate" then (b.getD 0 0 - a.getD 0 0).abs else Float.sqrt (d.foldl (·+·) 0)
  | .rgb a b c, .rgb x y z => Float.sqrt ((x-a)*(x-a)+(y-b)*(y-b)+(z-c)*(z-c))
  | .path _ a, .path _ b => Float.sqrt (((a.zip b).map fun (x,y) => (y-x)*(y-x)).foldl (·+·) 0)
  | _, _ => 0

/-- Parameter count rules of `animateTransform` values (§16.2.16). -/
private def transformArity (typ : String) (n : Nat) : Bool :=
  match typ with
  | "translate" | "scale" => n == 1 || n == 2
  | "rotate" => n == 1 || n == 3
  | "skewX" | "skewY" => n == 1
  | _ => false

/-! ## The animation function -/

/-- One animation, read. -/
structure Anim where
  /-- Index of the animation element. -/
  element : Nat
  target : Nat
  attrName : String
  info : AttrInfo
  /-- `animateTransform` type; empty for other elements. -/
  typ : String
  timing : Timing
  /-- The values; for a to-animation, the second value only (the first is the underlying value). -/
  values : Array AValue
  toAnimation : Bool
  byAnimation : Bool
  calcMode : String
  keyTimes : Option (Array Float)
  keySplines : Array (Float × Float × Float × Float)
  additive : Bool
  accumulate : Bool
  isSet : Bool
  deriving Inhabited

private def floats (s : String) (sep : String) : Except String (Array Float) := do
  let items := (s.splitOn sep).map trim |>.filter (!·.isEmpty)
  return (← items.mapM NativeSVG.number).toArray

def allowedAttributes (tag : String) : List String :=
  ["id","attributeName","attributeType","begin","dur","end","min","max","restart","repeatCount","repeatDur",
   "fill","calcMode","values","keyTimes","keySplines","from","to","by","additive","accumulate","href"] ++
  (if tag == "animateTransform" then ["type"] else [])

private def checkAttrs (tag : String) (attrs : List NamespaceAttribute) : Except String Unit := do
  for a in attrs do
    match a.name.namespace_ with
    | none => if !(allowedAttributes tag).contains a.name.localPart then throw s!"unsupported attribute on {tag}: {a.name.localPart}"
    | some ns =>
      if ns == xmlNS && ["id","space","lang","base"].contains a.name.localPart then continue
      -- XLink attributes other than href say nothing about the animation (§16.2.4).
      if ns == xlinkNS then continue
      throw s!"qualified attribute unsupported on {tag}: {a.name.localPart}"

/-- Read animation element `i` of `entries`. `none`: it has no effect (its target is not in
the document). -/
def readAnim (entries : Array Entry) (ids : String → Option Nat) (i : Nat) : Except String (Option Anim) := do
  let e := entries[i]!
  let tag := e.name.localPart
  if tag == "animateMotion" then throw "animation: animateMotion unsupported"
  checkAttrs tag e.attrs
  let target ← match hrefOf e.attrs with
    | some h =>
      let h := trim h
      if !h.startsWith "#" then throw "animation: target outside the document unsupported"
      match ids (h.drop 1).toString with
      | some t => pure (some t)
      | none => pure none
    | none => pure e.parent
  let some target := target | return none
  let some attrName := (plain e.attrs "attributeName").map trim | throw s!"{tag} without attributeName"
  let attributeKey := if attrName == "href" then "xlink:href" else attrName
  let some info := attrInfo attributeKey | throw s!"animation of attribute unsupported: {attrName}"
  -- On `text` and `tspan`, `x`, `y` and `rotate` are lists of coordinates (§10.4).
  let info := if ["x","y"].contains attributeKey && (isSvg entries[target]!.name "text" ||
      isSvg entries[target]!.name "tspan") then {info with kind := .numberList} else info
  if (info.kind == .transform) != (tag == "animateTransform") then
    throw s!"animation of {attrName} by {tag} unsupported"
  if tag == "animateColor" && !(info.kind == .colour || info.kind == .paint) then
    throw s!"animateColor of a non-colour attribute: {attrName}"
  let targetEntry := entries[target]!
  if info.inherited || info.kind == .colour || info.kind == .paint then
    if let some style := plain targetEntry.attrs "style" then
      if (style.splitOn ";").any fun d => trim ((d.splitOn ":").headD "") == attrName then
        throw s!"animation: {attrName} is also set by a style attribute"
  let timing ← timingOf ids e.attrs
  let typ := if tag == "animateTransform" then trim ((plain e.attrs "type").getD "translate") else ""
  if tag == "animateTransform" && !["translate","scale","rotate","skewX","skewY"].contains typ then
    throw s!"animateTransform type unsupported: {typ}"
  let isSet := tag == "set"
  let read := readValue info
  let (values,toAnimation,byAnimation) ← if isSet then do
      let some v := plain e.attrs "to" | throw "set without to"
      pure (#[← read v],false,false)
    else match plain e.attrs "values" with
      | some vs =>
        let items := (vs.splitOn ";").map trim |>.filter (!·.isEmpty)
        if items.isEmpty then throw "animation: empty values"
        pure ((← items.mapM read).toArray,false,false)
      | none =>
        match plain e.attrs "from", plain e.attrs "to", plain e.attrs "by" with
        | some f, some t, _ => pure (#[← read f,← read t],false,false)
        | some f, none, some b => do
          let fv ← read f; let bv ← read b
          pure (#[fv,← add fv bv],false,false)
        | none, some t, _ => pure (#[← read t],true,false)
        | none, none, some b => do
          let bv ← read b
          pure (#[scale 0 bv,bv],false,true)
        | _, _, _ => throw s!"{tag} without values, to or by"
  if info.kind == .transform then
    for v in values do
      match v with
      | .nums p => if !transformArity typ p.size then throw s!"animateTransform {typ} value with {p.size} parameters"
      | _ => pure ()
  let interp := values.all fun v => interpolable v || (match v with | .inherit => true | _ => false)
  let authorMode := trim ((plain e.attrs "calcMode").getD "linear")
  if !["discrete","linear","paced","spline"].contains authorMode then throw s!"invalid calcMode: {authorMode}"
  let calcMode := if isSet || !interp then "discrete" else authorMode
  if interp && values.size > 1 then
    for v in values.toList.drop 1 do
      match values[0]!, v with
      | .nums a, .nums b => if a.size != b.size then throw "animation: values of different lengths"
      | .path s _, .path t _ => if s != t then throw "animation: path data values with different commands"
      | _, _ => pure ()
  if info.kind == .transform && toAnimation then throw "animateTransform to-animation unsupported"
  let n := if toAnimation then 2 else values.size
  let keyTimes ← match plain e.attrs "keyTimes" with
    | none => pure none
    | some k =>
      if calcMode == "paced" then pure none else do
      let k ← floats k ";"
      let ok := k.size == n && k[0]! == 0 && (calcMode == "discrete" || k[k.size-1]! == 1) &&
        (List.range (k.size-1)).all (fun j => k[j]! ≤ k[j+1]!) && k.all (fun x => 0 ≤ x && x ≤ 1)
      if !ok then throw "animation: keyTimes in error"
      pure (some k)
  let keySplines ← if calcMode != "spline" then pure #[] else do
    let some ks := plain e.attrs "keySplines" | throw "animation: spline without keySplines"
    let groups := (ks.splitOn ";").map trim |>.filter (!·.isEmpty)
    let out ← groups.mapM fun g => do
      let v ← numList g
      if v.size != 4 || v.any (fun x => x < 0 || x > 1) then throw "animation: keySplines in error"
      pure (v[0]!,v[1]!,v[2]!,v[3]!)
    if out.length != n-1 then throw "animation: keySplines count in error"
    pure out.toArray
  let additiveV := trim ((plain e.attrs "additive").getD "replace")
  let accumulateV := trim ((plain e.attrs "accumulate").getD "none")
  if !["replace","sum"].contains additiveV then throw s!"invalid additive: {additiveV}"
  if !["none","sum"].contains accumulateV then throw s!"invalid accumulate: {accumulateV}"
  let numeric := interp && info.kind != .discrete
  return some {
    element:=i,target,attrName:=attributeKey,info,typ,timing,values,toAnimation,byAnimation,
    calcMode,keyTimes,keySplines,
    additive := numeric && !isSet && !toAnimation && (additiveV == "sum" || byAnimation),
    accumulate := numeric && !isSet && !toAnimation && accumulateV == "sum",
    isSet}

/-- The y of a cubic Bézier timing curve from (0,0) to (1,1) at x = `t` (§16.2.11
`keySplines`), by bisection on the curve parameter. -/
def spline (x1 y1 x2 y2 t : Float) : Float := Id.run do
  let bez := fun (a b u : Float) => 3*a*u*(1-u)*(1-u) + 3*b*u*u*(1-u) + u*u*u
  let mut lo := 0.0
  let mut hi := 1.0
  for _ in [:40] do
    let mid := (lo+hi)/2
    if bez x1 x2 mid < t then lo := mid else hi := mid
  return bez y1 y2 ((lo+hi)/2)

/-- The value of the simple animation function at fraction `f` (0 to 1) of the simple
duration, with the full value list `vs`. -/
def simpleValue (a : Anim) (vs : Array AValue) (f : Float) : Except String AValue := do
  let n := vs.size
  if n == 0 then throw "animation: no values"
  if n == 1 then return vs[0]!
  if a.calcMode == "discrete" || !(vs.all interpolable) then
    let k := a.keyTimes.getD ((Array.range n).map fun j => Float.ofNat j/Float.ofNat n)
    let j := (List.range n).foldl (fun acc j => if k[j]! ≤ f then j else acc) 0
    return vs[j]!
  let k : Array Float ← if a.calcMode == "paced" then do
      let ds := (Array.range (n-1)).map fun j => distance a.typ vs[j]! vs[j+1]!
      let total := ds.foldl (·+·) 0
      if total ≤ 0 then return vs[0]!
      let cum := ds.foldl (fun (acc : Array Float) d => acc.push (acc.back!+d)) #[0]
      pure (cum.map (·/total))
    else pure (a.keyTimes.getD ((Array.range n).map fun j => Float.ofNat j/Float.ofNat (n-1)))
  if f ≥ 1 then return vs[n-1]!
  let j := (List.range (n-1)).foldl (fun acc j => if k[j]! ≤ f then j else acc) 0
  let span := k[j+1]!-k[j]!
  let t := if span ≤ 0 then 0 else max 0 (min 1 ((f-k[j]!)/span))
  let t := if a.calcMode == "spline" then
      let (x1,y1,x2,y2) := a.keySplines[j]!
      spline x1 y1 x2 y2 t
    else t
  lerp vs[j]! vs[j+1]! t

/-- Where an animation is at time `t`: the begin of its current interval, the iteration, and
the fraction of the simple duration; `none`: no effect at `t`. -/
def stateAt (timing : Timing) (ivs : List Interval) (t : Int) : Option (Int × Nat × Float) := do
  let iv ← ivs.foldl (fun acc iv => if iv.b ≤ t then some iv else acc) none
  let elapsed ← match iv.e with
    | some e => if t < e then some (t - iv.b) else if timing.freeze then some (e - iv.b) else none
    | none => some (t - iv.b)
  let ended := match iv.e with | some e => t ≥ e | none => false
  match timing.dur with
  | none => some (iv.b,0,0)
  | some d =>
    let el := elapsed.toNat
    let dn := d.toNat
    if ended && el % dn == 0 && el > 0 then some (iv.b,el/dn-1,1)
    else some (iv.b,el/dn,Float.ofNat (el%dn)/Float.ofNat dn)

/-- The value of animation `a` in state (iteration `i`, fraction `f`) over `under`. -/
def valueOver (a : Anim) (i : Nat) (f : Float) (under : AValue) (parent : AValue := .inherit) :
    Except String AValue := do
  let resolve := fun (v : AValue) => match v with | .inherit => parent | v => v
  let a := {a with values := a.values.map resolve}
  if a.values.any (fun v => match v with | .inherit => true | _ => false) then
    throw "animation: inherit with no parent value"
  let vs := if a.toAnimation then #[under,a.values[0]!] else a.values
  if a.toAnimation && !(interpolable under) then
    -- A to-animation of a value that is not interpolated: discrete over two values.
    return if f < 0.5 then under else a.values[0]!
  let v ← simpleValue a vs f
  let v ← if a.accumulate && i > 0 then add v (scale (Float.ofNat i) vs[vs.size-1]!) else pure v
  if a.additive then add under v else pure v

/-! ## `animateMotion` (§16.2.17) -/

inductive Rotate where
  | angle (degrees : Float)
  | auto
  | autoReverse
  deriving Inhabited

/-- One `animateMotion`: a polyline (points with the distance along it), and the map from
the fraction of the simple duration to the distance (`times`, `distances`). -/
structure Motion where
  element : Nat
  target : Nat
  timing : Timing
  points : Array (Float × Float × Float)
  times : Array Float
  distances : Array Float
  discrete : Bool
  keySplines : Array (Float × Float × Float × Float)
  rotate : Rotate
  additive : Bool
  accumulate : Bool
  deriving Inhabited

/-- Points of a polyline with the distance along it; a move to a new subpath adds no
distance (SVG Tiny 1.2 §16.2.17 measures the path as `getTotalLength` does). -/
private def withDistances (parts : List (List (Float × Float))) : Array (Float × Float × Float) := Id.run do
  let mut out : Array (Float × Float × Float) := #[]
  let mut total := 0.0
  for part in parts do
    let mut first := true
    for (x,y) in part do
      if !first then
        if let some (px,py,_) := out.back? then
          total := total + Float.sqrt ((x-px)*(x-px)+(y-py)*(y-py))
      out := out.push (x,y,total)
      first := false
  return out

/-- The point at distance `d` and the direction there in degrees (that of the segment that
holds `d`; at a vertex, the segment that starts there, and at the end the last one). -/
def pointAt (pts : Array (Float × Float × Float)) (d : Float) : Float × Float × Float := Id.run do
  if pts.isEmpty then return (0,0,0)
  if pts.size == 1 then return (pts[0]!.1,pts[0]!.2.1,0)
  let mut j := 0
  for i in [:pts.size-1] do
    -- The last segment with length whose start is at or before `d`.
    if pts[i]!.2.2 ≤ d && pts[i+1]!.2.2 > pts[i]!.2.2 then j := i
  let (x0,y0,d0) := pts[j]!
  let (x1,y1,d1) := pts[j+1]!
  let span := d1-d0
  let t := if span ≤ 0 then 0 else max 0 (min 1 ((d-d0)/span))
  let angle := Float.atan2 (y1-y0) (x1-x0) * 180 / 3.141592653589793
  return (x0+(x1-x0)*t,y0+(y1-y0)*t,angle)

private def segmentEnd : L4Factoidal.Rendering.PathSegment → L4Factoidal.Rendering.Point
  | .line e => e
  | .quadratic _ e => e
  | .cubic _ _ e => e
  | .arc _ _ _ _ _ e => e

/-- The path flattened one segment at a time, and the index in the joined point list of the
start of the path and of the end of each segment. A `Z` is a segment (a line to the start of
the subpath); a moveto is not (SVG 1.1 §19.2.12, which SVG Tiny 1.2 §16.2.17 follows: "A
moveto command does not count as an additional point when dividing up the duration"). -/
def segmentParts (contours : List L4Factoidal.Rendering.Contour) :
    Except String (List (List (Float × Float)) × Array Nat) := do
  let mut parts : Array (List (Float × Float)) := #[]
  let mut ends : Array Nat := #[]
  let mut count := 0
  for c in contours do
    match c with
    | .empty _ => pure ()
    | .path start segs closed =>
      let mut pts : Array (Float × Float) := #[(start.x,start.y)]
      if ends.isEmpty then ends := ends.push count
      let mut cur := start
      let segs := if closed then segs ++ [.line start] else segs
      for seg in segs do
        let lines ← NativeSVGCurves.flatten ⟨1,0,0,1,0,0⟩ [.path cur [seg] false] 0.05
        for q in (lines.flatMap (·.points)).drop 1 do
          pts := pts.push (q.x,q.y)
        ends := ends.push (count + pts.size - 1)
        cur := segmentEnd seg
      parts := parts.push pts.toList
      count := count + pts.size
  return (parts.toList,ends)

private def pointList (s : String) : Except String (Float × Float) := do
  let v ← numList s
  if v.size != 2 then throw s!"animateMotion: a point needs two numbers: {s}"
  return (v[0]!,v[1]!)

/-- Read `animateMotion` element `i`; `none`: its target is not in the document. -/
def readMotion (entries : Array Entry) (ids : String → Option Nat) (i : Nat) : Except String (Option Motion) := do
  let e := entries[i]!
  for a in e.attrs do
    match a.name.namespace_ with
    | none =>
      if !(["id","begin","dur","end","min","max","restart","repeatCount","repeatDur","fill","calcMode","values",
            "keyTimes","keySplines","from","to","by","additive","accumulate","path","keyPoints","rotate","origin","href"].contains
            a.name.localPart) then throw s!"unsupported attribute on animateMotion: {a.name.localPart}"
    | some ns => if !(ns == xlinkNS || (ns == xmlNS && ["id","space","lang","base"].contains a.name.localPart)) then
        throw s!"qualified attribute unsupported on animateMotion: {a.name.localPart}"
  if let some o := plain e.attrs "origin" then
    if trim o != "default" then throw s!"animateMotion origin unsupported: {o}"
  let target ← match hrefOf e.attrs with
    | some h =>
      let h := trim h
      if !h.startsWith "#" then throw "animation: target outside the document unsupported"
      pure (ids (h.drop 1).toString)
    | none => pure e.parent
  let some target := target | return none
  let timing ← timingOf ids e.attrs
  let authorMode := trim ((plain e.attrs "calcMode").getD "paced")
  if !["discrete","linear","paced","spline"].contains authorMode then throw s!"invalid calcMode: {authorMode}"
  let keyTimes ← (plain e.attrs "keyTimes").mapM fun k => floats k ";"
  -- The path: an `mpath` child, else `path`, else `values`, else from/to/by (§16.2.17).
  let mpath := e.children.findSome? fun
    | .element n a _ => if n.namespace_ == some svgNS && n.localPart == "mpath" then some a else none
    | _ => none
  let pathData ← match mpath with
    | some a =>
      let some h := hrefOf a | throw "mpath without href"
      let h := trim h
      if !h.startsWith "#" then throw "mpath: reference outside the document unsupported"
      let some pi := ids (h.drop 1).toString | throw s!"mpath: no element {h}"
      let pe := entries[pi]!
      if !isSvg pe.name "path" then throw s!"mpath: {h} is not a path"
      if (plain pe.attrs "transform").isSome then throw "mpath: a path with a transform unsupported"
      pure (some ((plain pe.attrs "d").getD ""))
    | none => pure (plain e.attrs "path")
  let (parts,vertexCount,segmentEnds) ← match pathData with
    | some d => do
      let contours ← NativeSVGPath.parse NativeSVG.number d
      let (parts,ends) ← segmentParts contours
      pure (parts,none,some ends)
    | none => do
      let pts ← match plain e.attrs "values" with
        | some vs => ((vs.splitOn ";").map trim |>.filter (!·.isEmpty)).mapM pointList
        | none => match plain e.attrs "from", plain e.attrs "to", plain e.attrs "by" with
          | some f, some t, _ => do pure [← pointList f,← pointList t]
          | some f, none, some b => do
            let (fx,fy) ← pointList f; let (bx,by_) ← pointList b
            pure [(fx,fy),(fx+bx,fy+by_)]
          | none, some _, _ => throw "animateMotion to-animation unsupported"
          | none, none, some b => do
            let (bx,by_) ← pointList b
            pure [(0,0),(bx,by_)]
          | _, _, _ => throw "animateMotion without path, values, to or by"
      pure ([pts],some pts.length,none)
  let pts := withDistances parts
  if pts.isEmpty then throw "animateMotion with an empty path"
  let total := pts.back!.2.2
  let byOnly := mpath.isNone && pathData.isNone && (plain e.attrs "values").isNone && (plain e.attrs "from").isNone &&
    (plain e.attrs "by").isSome
  -- The map from simple time to distance.
  let (times,distances,discrete) ← match plain e.attrs "keyPoints", vertexCount with
    | some kp, _ => do
      let kp ← floats kp ";"
      let some k := keyTimes | throw "animateMotion: keyPoints without keyTimes"
      if kp.size != k.size || kp.any (fun x => x < 0 || x > 1) then throw "animateMotion: keyPoints in error"
      pure (k,kp.map (·*total),authorMode == "discrete")
    | none, some n =>
      -- `values` points: each value is one vertex of the polyline.
      let cum := (Array.range n).map fun j => (pts[j]!).2.2
      if authorMode == "paced" then pure (#[0,1],#[0,total],false)
      else
        let k := keyTimes.getD ((Array.range n).map fun j =>
          Float.ofNat j/Float.ofNat (if authorMode == "discrete" then n else n-1))
        if k.size != n then throw "animation: keyTimes in error"
        pure (k,cum,authorMode == "discrete")
    | none, none =>
      if authorMode == "paced" then pure (#[0,1],#[0,total],false)
      else
        -- Each segment of the path gets an equal share of the time (or its keyTimes).
        let ends := segmentEnds.getD #[]
        let n := ends.size
        if n < 2 then pure (#[0,1],#[0,total],false) else
        let cum := ends.map fun j => (pts[j]!).2.2
        let k := keyTimes.getD ((Array.range n).map fun j =>
          Float.ofNat j/Float.ofNat (if authorMode == "discrete" then n else n-1))
        if k.size != n then throw "animation: keyTimes in error"
        pure (k,cum,authorMode == "discrete")
  if times.size > 0 && (times[0]! != 0 || (!discrete && times[times.size-1]! != 1) ||
      (List.range (times.size-1)).any (fun j => times[j]! > times[j+1]!)) then throw "animation: keyTimes in error"
  let keySplines ← if authorMode != "spline" then pure #[] else do
    let some ks := plain e.attrs "keySplines" | throw "animation: spline without keySplines"
    let groups := (ks.splitOn ";").map trim |>.filter (!·.isEmpty)
    let out ← groups.mapM fun g => do
      let v ← numList g
      if v.size != 4 || v.any (fun x => x < 0 || x > 1) then throw "animation: keySplines in error"
      pure (v[0]!,v[1]!,v[2]!,v[3]!)
    if out.length + 1 != times.size then throw "animation: keySplines count in error"
    pure out.toArray
  let rotate ← match (plain e.attrs "rotate").map trim with
    | none => pure (Rotate.angle 0)
    | some "auto" => pure .auto
    | some "auto-reverse" => pure .autoReverse
    | some a => match (NativeSVG.number a).toOption with
      | some v => pure (.angle v)
      | none => throw s!"animateMotion: invalid rotate: {a}"
  let additiveV := trim ((plain e.attrs "additive").getD "replace")
  let accumulateV := trim ((plain e.attrs "accumulate").getD "none")
  if !["replace","sum"].contains additiveV then throw s!"invalid additive: {additiveV}"
  if !["none","sum"].contains accumulateV then throw s!"invalid accumulate: {accumulateV}"
  return some {
    element:=i,target,timing,points:=pts,times,distances,discrete,keySplines,rotate,
    additive := additiveV == "sum" || byOnly, accumulate := accumulateV == "sum"}

/-- The motion of `m` at iteration `i`, fraction `f`: a translation and a rotation. -/
def motionAt (m : Motion) (i : Nat) (f : Float) : String := Id.run do
  let n := m.times.size
  let d : Float :=
    if n == 0 then 0
    else if m.discrete then
      let j := (List.range n).foldl (fun acc j => if m.times[j]! ≤ f then j else acc) 0
      m.distances[j]!
    else if f ≥ 1 then m.distances[n-1]!
    else
      let j := (List.range (n-1)).foldl (fun acc j => if m.times[j]! ≤ f then j else acc) 0
      let span := m.times[j+1]!-m.times[j]!
      let t := if span ≤ 0 then 0 else max 0 (min 1 ((f-m.times[j]!)/span))
      let t := match m.keySplines[j]? with
        | some (x1,y1,x2,y2) => spline x1 y1 x2 y2 t
        | none => t
      m.distances[j]!+(m.distances[j+1]!-m.distances[j]!)*t
  let (x,y,angle) := pointAt m.points d
  let (ex,ey,_) := pointAt m.points (m.distances.back?.getD 0)
  let (x,y) := if m.accumulate && i > 0 then (x+Float.ofNat i*ex,y+Float.ofNat i*ey) else (x,y)
  let a := match m.rotate with
    | .angle v => v
    | .auto => angle
    | .autoReverse => angle+180
  let rot := if a == 0 then "" else s!" rotate({fmt a})"
  return s!"translate({fmt x} {fmt y}){rot}"

/-! ## The snapshot -/

/-- Resolve the instance times of every animation, to a fixed point over syncbase values. -/
def resolveIntervals (anims : Array (Nat × Timing)) (horizon : Int) : Except String (Std.TreeMap Nat (List Interval)) := do
  let durs : Std.TreeMap Nat (Option Int) := anims.foldl (fun m (el,tm) => m.insert el tm.dur) {}
  let mut table : Std.TreeMap Nat (List Interval) := {}
  -- Only begins at or before the time of the snapshot can change it, so a sequence of
  -- intervals with no end (`begin="0s; a.end+1s"` on `a`) stops at the horizon.
  for _ in [:anims.size+2+horizon.toNat] do
    let mut next : Std.TreeMap Nat (List Interval) := {}
    for (el,tm) in anims do
      let times := fun (items : List TimeItem) => items.flatMap fun
        | .offset ms => [ms]
        | .sync other isEnd ms => ((table.get? other).getD []).filterMap fun iv =>
            if isEnd then iv.e.map (·+ms) else some (iv.b+ms)
        | .repeat_ other n ms =>
          match (durs.get? other).join with
          | none => []
          | some d =>
            if d ≤ 0 then [] else
            ((table.get? other).getD []).flatMap fun iv =>
              -- Repetition k begins at b + k·d, while the interval is active, up to the horizon.
              let last : Int := match iv.e with
                | some e => min e (horizon+1)
                | none => horizon+1
              let count := ((last - iv.b) / d).toNat
              let ks : List Int := match n with
                | some k => if k ≥ 1 && iv.b + (k : Int)*d < last then [(k : Int)] else []
                | none => ((List.range (count+1)).filter (· ≥ 1)).map Int.ofNat
              ks.filterMap fun k => let at_ := iv.b + k*d; if at_ < last then some (at_+ms) else none
        | .unresolved => []
      next := next.insert el (intervals tm ((times tm.begins).filter (· ≤ horizon)) (times tm.ends))
    if next.toList == table.toList then return table
    table := next
  throw "animation: syncbase times do not settle (a cycle)"

/-- The value of attribute `key` that an element has before its own animations: its own
attribute, else (inherited) that of the nearest ancestor that sets it, else the initial value. -/
private def underlying (info : AttrInfo) (key : String) (own : List NamespaceAttribute)
    (ancestors : List (List NamespaceAttribute)) : String :=
  let get := fun (attrs : List NamespaceAttribute) =>
    match info.ns with
    | some ns => (attrs.find? fun a => a.name.namespace_ == some ns && a.name.localPart == "href").map (·.value)
    | none => (plain attrs key).filter (trim · != "inherit")
  match get own with
  | some v => v
  | none =>
    if !info.inherited then info.initial else
    (ancestors.findSome? get).getD info.initial

private def setAttr (info : AttrInfo) (key : String) (value : String) (attrs : List NamespaceAttribute) :
    List NamespaceAttribute :=
  let local_ := if info.ns.isSome then "href" else key
  let same := fun (a : NamespaceAttribute) => a.name.namespace_ == info.ns && a.name.localPart == local_
  if attrs.any same then attrs.map fun a => if same a then {a with value} else a
  else attrs ++ [{name:={namespace_:=info.ns,localPart:=local_},value}]

/-- One layer of the sandwich of an element: an animation in its state at `t`. -/
structure Layer where
  anim : Anim
  begin_ : Int
  iteration : Nat
  fraction : Float
  deriving Inhabited

/-- Apply the layers of one element to its attributes (in sandwich order). -/
def applyLayers (layers : List Layer) (attrs : List NamespaceAttribute)
    (ancestors : List (List NamespaceAttribute)) : Except String (List NamespaceAttribute) := do
  let mut attrs := attrs
  for l in layers do
    let a := l.anim
    let under := underlying a.info a.attrName attrs ancestors
    let value ← if a.info.kind == .transform then do
        let p ← match ← valueOver {a with additive := false} l.iteration l.fraction (.nums #[]) with
          | .nums p => pure (.nums p)
          | v => pure v
        let fn := writeValue .transform a.typ p
        -- `sum`: the function is appended to the transform list below (post-multiplied).
        pure (if a.additive then trim (under ++ " " ++ fn) else fn)
      else do
        let u ← match readValue a.info under with
          | .ok v => pure v
          | .error err =>
            if [Kind.number,Kind.numberList,Kind.colour].contains a.info.kind then
              throw s!"animation: underlying value of {a.attrName} not read: {err}"
            else pure (.str under)
        -- `inherit` (SMIL 2.1 §3.6.2): the value of the parent element.
        let parentText := match ancestors with
          | p::rest => underlying {a.info with inherited := true} a.attrName p rest
          | [] => a.info.initial
        let parent := match readValue a.info parentText with
          | .ok v => v
          | .error _ => .str parentText
        let v ← valueOver a l.iteration l.fraction u parent
        pure (writeValue a.info.kind a.typ v)
    attrs := setAttr a.info a.attrName value attrs
  return attrs

/-- Whether the document has an animation or `discard` element (to a depth of 256). -/
def animates (root : NamespaceNode) : Bool :=
  go 256 root
where
  go : Nat → NamespaceNode → Bool
    | 0, _ => false
    | _, .other _ => false
    | fuel+1, .element name _ children =>
      (name.namespace_ == some svgNS && (animationTags.contains name.localPart || name.localPart == "discard")) ||
        children.any (go fuel)

/-- The document at time `t`: animated attributes set, animation elements and the targets of
`discard` elements that have begun replaced by comments (so the source paths of the other
elements stay the same). -/
def snapshot (t : Int) (root : NamespaceNode) : Except String NamespaceNode := do
  let entries ← index root
  let mut idTable : Std.TreeMap String Nat := {}
  for i in [:entries.size] do
    if let some id := NativeSVGReferences.elementId entries[i]!.attrs then
      if !idTable.contains id then idTable := idTable.insert id i
  let ids := fun (name : String) => idTable.get? name
  let mut anims : Array Anim := #[]
  let mut motions : Array Motion := #[]
  let mut discards : Array (Nat × Nat × Timing) := #[]
  let mut removed : Std.TreeMap (List Nat) Unit := {}
  for i in [:entries.size] do
    let e := entries[i]!
    if e.name.namespace_ != some svgNS then continue
    if animationTags.contains e.name.localPart then
      removed := removed.insert e.path ()
      if e.name.localPart == "animateMotion" then
        if let some m ← readMotion entries ids i then motions := motions.push m
      else if let some a ← readAnim entries ids i then anims := anims.push a
    else if e.name.localPart == "discard" then
      removed := removed.insert e.path ()
      for a in e.attrs do
        if a.name.namespace_.isNone && !["id","begin","href"].contains a.name.localPart then
          throw s!"unsupported attribute on discard: {a.name.localPart}"
      let target := match hrefOf e.attrs with
        | some h => if (trim h).startsWith "#" then ids ((trim h).drop 1).toString else none
        | none => e.parent
      if let some target := target then
        discards := discards.push (i,target,← timingOf ids e.attrs (discard := true))
  if anims.isEmpty && motions.isEmpty && discards.isEmpty then return root
  let table ← resolveIntervals ((anims.map fun a => (a.element,a.timing)) ++ (motions.map fun m => (m.element,m.timing)) ++
    discards.map fun (i,_,tm) => (i,tm)) t
  for (i,target,_) in discards do
    let ivs := (table.get? i).getD []
    if ivs.any (·.b ≤ t) then
      if entries[target]!.parent.isNone then throw "animation: discard of the root element unsupported"
      removed := removed.insert entries[target]!.path ()
  -- The layers of each target, in sandwich order: begin of the current interval, then
  -- document order of the animation element.
  let mut layers : Std.TreeMap (List Nat) (List Layer) := {}
  for a in anims do
    let ivs := (table.get? a.element).getD []
    let some (b,iter,f) := stateAt a.timing ivs t | continue
    let path := entries[a.target]!.path
    let l : Layer := {anim:=a,begin_:=b,iteration:=iter,fraction:=f}
    let before := (layers.get? path).getD []
    let (lo,hi) := before.partition fun x => x.begin_ < b || (x.begin_ == b && x.anim.element < a.element)
    layers := layers.insert path (lo ++ [l] ++ hi)
  -- Motions of each target, in the same order; each is a transform function list.
  let mut moves : Std.TreeMap (List Nat) (List (Int × Nat × Bool × String)) := {}
  for m in motions do
    let ivs := (table.get? m.element).getD []
    let some (b,iter,f) := stateAt m.timing ivs t | continue
    let path := entries[m.target]!.path
    let before := (moves.get? path).getD []
    let (lo,hi) := before.partition fun (b',el,_,_) => b' < b || (b' == b && el < m.element)
    moves := moves.insert path (lo ++ [(b,m.element,m.additive,motionAt m iter f)] ++ hi)
  -- The sandwich of motions: `replace` drops the motions below it, `sum` adds to them.
  let motionOf : Std.TreeMap (List Nat) String := moves.foldl (fun acc path ls =>
    acc.insert path (String.intercalate " " (ls.foldl (fun out (_,_,add,fn) => if add then out ++ [fn] else [fn]) []))) {}
  rewrite layers motionOf removed 256 [] [] root
where
  rewrite (layers : Std.TreeMap (List Nat) (List Layer)) (motionOf : Std.TreeMap (List Nat) String)
      (removed : Std.TreeMap (List Nat) Unit) :
      Nat → List Nat → List (List NamespaceAttribute) → NamespaceNode → Except String NamespaceNode
    | 0, _, _, _ => throw "animation: nesting deeper than the animation pass reads"
    | _, _, _, .other raw => pure (.other raw)
    | fuel+1, path, ancestors, .element name attrs children => do
      if removed.contains path && !path.isEmpty then return .other (.comment "removed by animation")
      let attrs ← match layers.get? path with
        | some ls => applyLayers ls attrs ancestors
        | none => pure attrs
      -- §16.2.17: the motion is applied before (to the left of) the `transform` attribute.
      let attrs := match motionOf.get? path with
        | some m =>
          let info : AttrInfo := (attrInfo "transform").get!
          setAttr info "transform" (trim (m ++ " " ++ (plain attrs "transform").getD "")) attrs
        | none => attrs
      let kids ← children.zipIdx.mapM fun (child,i) => rewrite layers motionOf removed fuel (path ++ [i]) (attrs :: ancestors) child
      return .element name attrs kids

end NativeSVGAnimate
