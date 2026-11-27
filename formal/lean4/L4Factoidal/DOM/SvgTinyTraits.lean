/-
L4Factoidal.DOM.SvgTinyTraits — the TraitAccess interface of the SVG Tiny 1.2 uDOM
(https://www.w3.org/TR/SVGTiny12/svgudom.html, Appendix A.8.13 and A.8.14): which traits an
element has, the type of each getter and setter, the lacuna values, the computed value of a
property (inherited from the parent when not specified, or `inherit`), and the checks that a
setter makes. `web_api` ops 210 and 211 (`WasmVM.Hosts.WebApi`).

The page's `getTrait`, `getFloatTrait`, ..., `setRGBColorTrait` (prelude.js) are the WebIDL
surface: they pass the node, the namespace, the name and the type to Lean, and write the
attribute text that Lean answers with the DOM's own `setAttributeNS` (a typed command of the
arena). The answers are text: a number as its own decimal text, a colour as "r g b", a
rectangle as "x y w h", a matrix as the transform list of `SvgValues.parseTransformList`
(the prelude composes it, as it does for `SVGTransformList`), a path as its normalized
segments. "\u0000" is null.

Errors are negative DOMException codes: -9 NOT_SUPPORTED_ERR, -15 INVALID_ACCESS_ERR,
-17 TYPE_MISMATCH_ERR.

Every loop is a core list combinator or a tail call on a shorter list or a smaller fuel.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.DOM.SvgValues
import L4Factoidal.PageCanvas.Color
import L4Factoidal.Rendering.FloatFormat

namespace L4Factoidal.DOM.SvgTinyTraits

/-- The types of the trait accessors. -/
inductive Kind where
  | string | float | floatList | matrix | rect | path | rgb
  deriving BEq, Repr, Inhabited, DecidableEq

def Kind.ofCode : Nat → Option Kind
  | 0 => some .string | 1 => some .float | 2 => some .floatList | 3 => some .matrix
  | 4 => some .rect | 5 => some .path | 6 => some .rgb | _ => none

def notSupported : Int := -9
def invalidAccess : Int := -15
def typeMismatch : Int := -17

/-- The text that stands for null. -/
def nullText : String := "\u0000"

/-- One row of the table "Traits supported in this specification" (A.8.13). -/
structure Trait where
  /-- A property (CSS-like, may be `inherit`), or an attribute. -/
  property : Bool := false
  /-- An inherited property (SVG Tiny 1.2 Appendix C, "Inherited"). -/
  inherited : Bool := false
  gets : List Kind
  sets : List Kind
  /-- The keywords that `setTrait` takes (empty: any text); `inherit` is added for a property. -/
  keywords : List String := []
  /-- Range of a float value: at least `lo`, at most `hi`. -/
  lo : Option Float := none
  hi : Option Float := none
  deriving Inhabited

def graphics : List String :=
  ["rect","circle","ellipse","line","polyline","polygon","path","image","text","textArea","use","video","animation","g","a","switch","foreignObject","tspan"]
def animations : List String := ["animate","animateColor","animateMotion","animateTransform","set","discard"]
def media : List String := ["audio","video","animation"]

/-- Whether attribute `name` belongs to element `el` (SVG Tiny 1.2 attribute table, for the
attributes of the trait table). Properties apply to every SVG element. -/
def attributeOn (el name : String) : Bool :=
  match name with
  | "cx" | "cy" => ["circle","ellipse","radialGradient"].contains el
  | "r" => ["circle","radialGradient"].contains el
  | "rx" | "ry" => ["rect","ellipse"].contains el
  | "x" | "y" => ["rect","image","text","use","textArea","video","animation","foreignObject"].contains el
  | "width" | "height" => ["rect","image","svg","use","textArea","video","animation","foreignObject"].contains el
  | "x1" | "y1" | "x2" | "y2" => ["line","linearGradient"].contains el
  | "d" => el == "path"
  | "path" => el == "animateMotion"
  | "points" => ["polyline","polygon"].contains el
  | "transform" => graphics.contains el && el != "tspan"
  | "viewBox" => el == "svg"
  | "offset" => el == "stop"
  | "gradientUnits" => ["linearGradient","radialGradient"].contains el
  | "version" | "baseProfile" | "zoomAndPan" | "snapshotTime" => el == "svg"
  | "target" => el == "a"
  | "editable" => ["text","textArea"].contains el
  | "focusable" | "focusHighlight" => graphics.contains el || el == "svg"
  | "accumulate" | "additive" | "attributeName" | "calcMode" | "from" | "to" | "values" | "keyTimes"
  | "keySplines" | "keyPoints" => animations.contains el && el != "discard"
  | "begin" => animations.contains el || media.contains el
  | "dur" | "end" | "max" | "min" | "repeatCount" | "repeatDur" | "restart" =>
    (animations.contains el && el != "discard") || media.contains el
  | "type" => el == "animateTransform"
  | "id" => true
  | _ => name.startsWith "nav-" && (graphics.contains el || el == "svg")

/-- The trait table (A.8.13). `fill` is the property on a graphics element and the attribute
of an animation element. -/
def traitOf (el name : String) : Option Trait :=
  let p (inh : Bool) (gets sets : List Kind) (kw : List String := []) (lo hi : Option Float := none) : Option Trait :=
    some { property := true, inherited := inh, gets, sets, keywords := kw, lo, hi }
  let a (gets sets : List Kind) (kw : List String := []) (lo hi : Option Float := none) : Option Trait :=
    if attributeOn el name then some { gets, sets, keywords := kw, lo, hi } else none
  let unit : Option Float := some 1
  let zero : Option Float := some 0
  match name with
  -- properties
  | "audio-level" => p true [.float] [.float, .string] [] zero unit
  | "color" => p true [.rgb] [.rgb, .string]
  | "display" => p false [.string] [.string] ["inline","none"]
  | "fill" =>
    if animations.contains el then a [.string] [.string] ["freeze","remove"] |>.or (some { gets := [.string], sets := [.string], keywords := ["freeze","remove"] })
    else p true [.rgb, .string] [.rgb, .string]
  | "fill-opacity" | "stroke-opacity" | "opacity" | "solid-opacity" | "stop-opacity" | "viewport-fill-opacity" =>
    p (name == "fill-opacity" || name == "stroke-opacity") [.float] [.float, .string] [] zero unit
  | "fill-rule" => p true [.string] [.string] ["nonzero","evenodd"]
  | "font-family" => if el == "font-face" then none else p true [.string] [.string]
  | "font-size" => p true [.float] [.float, .string]
      ["xx-small","x-small","small","medium","large","x-large","xx-large","larger","smaller"] zero none
  | "font-style" => if el == "font-face" then none else p true [.string] [.string] ["normal","italic","oblique"]
  | "font-weight" => if el == "font-face" then none else
      p true [.string] [.string] ["normal","bold","bolder","lighter","100","200","300","400","500","600","700","800","900"]
  | "solid-color" => p false [.rgb] [.rgb, .string]
  | "stop-color" => p false [.rgb, .string] [.rgb, .string]
  | "stroke" => p true [.rgb, .string] [.rgb, .string]
  | "stroke-dasharray" => p true [.floatList, .string] [.floatList, .string] ["none"]
  | "stroke-dashoffset" => p true [.float] [.float, .string]
  | "stroke-linecap" => p true [.string] [.string] ["butt","round","square"]
  | "stroke-linejoin" => p true [.string] [.string] ["miter","round","bevel"]
  | "stroke-miterlimit" => p true [.float] [.float, .string] [] unit none
  | "stroke-width" => p true [.float] [.float, .string] [] zero none
  | "text-anchor" => p true [.string] [.string] ["start","middle","end"]
  | "vector-effect" => p false [.string] [.string] ["none","non-scaling-stroke"]
  | "viewport-fill" => p false [.rgb, .string] [.rgb, .string]
  | "visibility" => p true [.string] [.string] ["visible","hidden"]
  -- attributes
  | "accumulate" => a [.string] [.string] ["none","sum"]
  | "additive" => a [.string] [.string] ["replace","sum"]
  | "calcMode" => a [.string] [.string] ["discrete","linear","paced","spline"]
  | "restart" => a [.string] [.string] ["always","whenNotActive","never"]
  | "attributeName" | "baseProfile" | "version" | "id" | "target" => a [.string] [.string]
  | "begin" | "dur" | "end" | "from" | "to" | "values" | "keyTimes" | "keySplines" | "keyPoints"
  | "max" | "min" | "repeatCount" | "repeatDur" => a [] [.string]
  | "editable" => a [.string] [.string] ["simple","none"]
  | "focusable" => a [.string] [.string] ["true","false","auto"]
  | "focusHighlight" => a [.string] [.string] ["auto","none"]
  | "gradientUnits" => a [.string] [.string] ["userSpaceOnUse","objectBoundingBox"]
  | "zoomAndPan" => a [.string] [.string] ["disable","magnify"]
  | "type" => a [.string] [.string] ["translate","scale","rotate","skewX","skewY"]
  | "cx" | "cy" | "x1" | "y1" | "x2" | "y2" | "stroke-dashoffset-attr" => a [.float] [.float]
  | "x" | "y" => a (if el == "text" then [.float, .floatList] else [.float]) (if el == "text" then [.float, .floatList] else [.float])
  | "r" | "rx" | "ry" | "snapshotTime" => a [.float] [.float] [] zero none
  | "width" | "height" =>
    a (if el == "textArea" then [.float, .string] else [.float]) (if el == "textArea" then [.float, .string] else [.float])
      (if el == "textArea" then ["auto"] else []) zero none
  | "offset" => a [.float] [.float] [] zero unit
  | "d" | "path" => a [.path] [.path]
  | "points" => a [.floatList] [.floatList]
  | "transform" => a [.matrix, .string] [.matrix, .string]
  | "viewBox" => a [.rect] [.rect, .string] ["none"]
  | _ => if name.startsWith "nav-" then a [.string] [.string] else none

/-- `xlink:href`, the one trait in a namespace (A.8.13: `getTraitNS(xlink, "href")`). -/
def xlinkHrefOn (el : String) : Bool :=
  ["a","image","use","animation","audio","video","script","handler","prefetch","foreignObject"].contains el ||
    animations.contains el

/-- The lacuna value of a trait on an element, when the table gives one. -/
def lacuna (el name : String) : Option String :=
  match name with
  | "audio-level" | "fill-opacity" | "stroke-opacity" | "opacity" | "solid-opacity" | "stop-opacity"
  | "viewport-fill-opacity" | "stroke-width" => some "1"
  | "stroke-miterlimit" => some "4"
  | "color" | "solid-color" | "stop-color" => some "rgb(0,0,0)"
  | "fill" => some (if animations.contains el then "remove" else "rgb(0,0,0)")
  | "stroke" | "stroke-dasharray" | "vector-effect" | "viewport-fill" | "accumulate" | "editable" => some "none"
  | "display" => some "inline"
  | "fill-rule" => some "nonzero"
  | "font-style" | "font-weight" => some "normal"
  | "stroke-linecap" => some "butt"
  | "stroke-linejoin" => some "miter"
  | "text-anchor" => some "start"
  | "visibility" => some "visible"
  | "additive" => some "replace"
  | "calcMode" => some (if el == "animateMotion" then "paced" else "linear")
  | "restart" => some "always"
  | "focusable" | "focusHighlight" => some "auto"
  | "gradientUnits" => some "objectBoundingBox"
  | "zoomAndPan" => some "magnify"
  | "baseProfile" => some "none"
  | "target" => some "_self"
  | "cx" | "cy" | "r" => some (if el == "radialGradient" then "0.5" else "0")
  | "x2" => some (if el == "linearGradient" then "1" else "0")
  | "width" | "height" => some (if el == "textArea" then "auto" else "0")
  | "x" | "y" | "x1" | "y1" | "y2" | "rx" | "ry" | "offset" | "snapshotTime" | "stroke-dashoffset" => some "0"
  | "d" | "path" => some ""
  | "transform" => some ""
  | _ => if name.startsWith "nav-" then some "auto" else none

/-- The specified value of attribute `name` (namespace `ns`) on node `n`. -/
def specified (d : Dom) (n : NodeId) (ns : Option String) (name : String) : Option String :=
  ((d.get n).attrs.find? fun a => a.ns == ns && a.lname == name).map (·.value)

def trimS (s : String) : String := String.ofList (SvgValues.trim s.toList)

/-- The parent element of `n`, if any. -/
def parentElement (d : Dom) (n : NodeId) : Option NodeId :=
  (d.get n).parent.bind fun p => if (d.get p).type == .element then some p else none

/-- The computed value of a property (A.8.13: "for inherited properties the value on the
parent is used. For non-inherited values, or on the root element, the initial value"), and
of an attribute (its specified value, else the lacuna value). `fuel` bounds the walk to the
root (the arena's size is enough: each step goes to a parent). -/
def computed (d : Dom) (t : Trait) (name : String) : Nat → NodeId → Option String
  | 0, _ => none
  | fuel + 1, n =>
    let el := (d.get n).lname
    match specified d n none name with
    | some v =>
      if t.property && trimS v == "inherit" then
        match parentElement d n with
        | some p => computed d t name fuel p
        | none => lacuna el name
      else some v
    | none =>
      if t.inherited then
        match parentElement d n with
        | some p => computed d t name fuel p
        | none => lacuna el name
      else lacuna el name

/-- A number of the trait syntax (`SvgValues.parseNumber`), or a length in user units with
`px`. A percentage or another unit is a type mismatch (A.8.14, width and height). -/
def numberText (v : String) : Except Int String :=
  match SvgValues.parseNumber v with
  | some n => .ok n
  | none =>
    match SvgValues.parseLength v with
    | some (n, u, _) => if u == "" || u == "px" then .ok n else .error typeMismatch
    | none => .error typeMismatch

/-- A colour as "r g b" (A.8.21 SVGRGBColor: three components 0 to 255); null for `none`
and for a paint server reference (`url(...)`); `currentColor` is the computed `color`. -/
def rgbText (d : Dom) (n : NodeId) (v : String) : Except Int String :=
  let s := trimS v
  if s == "none" || s.startsWith "url(" then .ok nullText else
  let s := if s.toLower == "currentcolor" then
      (computed d { property := true, inherited := true, gets := [.rgb], sets := [] } "color" (d.size + 1) n).getD "rgb(0,0,0)"
    else s
  match PageCanvas.Color.parse? s with
  | some c => .ok s!"{c.r.toUInt8.toNat} {c.g.toUInt8.toNat} {c.b.toUInt8.toNat}"
  | none => .error typeMismatch

/-- `viewBox` as "x y w h" (A.8.13: null for `none`). -/
def rectText (v : String) : Except Int String :=
  if trimS v == "none" || trimS v == "" then .ok nullText else
  match SvgValues.parseNumberList v with
  | some [x, y, w, h] => .ok s!"{x} {y} {w} {h}"
  | _ => .ok nullText

/-! ### Path data, normalized (A.8.14 "Accessing rules for path attributes"; A.8.19 SVGPath)

SVGPath has the commands M, L, C, Q and Z, all absolute. H and V become L, S becomes C, T
becomes Q (with the reflected control point), relative commands become absolute. At the first
error the segments before it are the value. -/

/-- One parsed number, after optional separators. -/
def pathNumber (cs : List Char) : Option (Float × List Char) :=
  let (cs, _) := SvgValues.skipSeparator cs
  match SvgValues.takeNumber cs with
  | some (t, rest) => (numberOf (String.ofList t)).map (·, rest)
  | none => none
where
  numberOf (t : String) : Option Float :=
    (PageCanvas.Color.number? t)

def fmt (x : Float) : String := Rendering.FloatFormat.format x

structure PathState where
  out : Array String := #[]
  cx : Float := 0
  cy : Float := 0
  sx : Float := 0
  sy : Float := 0
  /-- The last control point of a C (for S) or of a Q (for T), and which. -/
  lastC : Option (Float × Float) := none
  lastQ : Option (Float × Float) := none

/-- Read `k` numbers, consed onto `acc` in reverse; a tail call, so one stack frame for any `k`
(tail-recursion gate, `tools/lean-tail-recursion-audit.py`). -/
def numbersGo : Nat → List Char → List Float → Option (List Float × List Char)
  | 0, cs, acc => some (acc.reverse, cs)
  | k + 1, cs, acc =>
    match pathNumber cs with
    | none => none
    | some (x, cs) => numbersGo k cs (x :: acc)

/-- Read `k` numbers. -/
def numbers (k : Nat) (cs : List Char) : Option (List Float × List Char) := numbersGo k cs []

def isCmd (c : Char) : Bool := "MmLlHhVvCcSsQqTtZz".toList.contains c

/-- One segment of command `c` (already known), its numbers read from `cs`. -/
def segment (st : PathState) (c : Char) (cs : List Char) : Option (PathState × List Char) := do
  let rel := c.isLower
  let ox := if rel then st.cx else 0
  let oy := if rel then st.cy else 0
  match c.toUpper with
  | 'Z' =>
    pure ({ st with out := st.out.push "Z", cx := st.sx, cy := st.sy, lastC := none, lastQ := none }, cs)
  | 'M' | 'L' =>
    let (ns, cs) ← numbers 2 cs
    let x := ox + ns[0]!; let y := oy + ns[1]!
    let st := if c.toUpper == 'M' then { st with sx := x, sy := y } else st
    pure ({ st with out := st.out.push s!"{c.toUpper} {fmt x} {fmt y}", cx := x, cy := y, lastC := none, lastQ := none }, cs)
  | 'H' =>
    let (ns, cs) ← numbers 1 cs
    let x := ox + ns[0]!
    pure ({ st with out := st.out.push s!"L {fmt x} {fmt st.cy}", cx := x, lastC := none, lastQ := none }, cs)
  | 'V' =>
    let (ns, cs) ← numbers 1 cs
    let y := oy + ns[0]!
    pure ({ st with out := st.out.push s!"L {fmt st.cx} {fmt y}", cy := y, lastC := none, lastQ := none }, cs)
  | 'C' =>
    let (ns, cs) ← numbers 6 cs
    let p := ns.toArray
    let (x1, y1, x2, y2, x, y) := (ox + p[0]!, oy + p[1]!, ox + p[2]!, oy + p[3]!, ox + p[4]!, oy + p[5]!)
    pure ({ st with out := st.out.push s!"C {fmt x1} {fmt y1} {fmt x2} {fmt y2} {fmt x} {fmt y}", cx := x, cy := y, lastC := some (x2, y2), lastQ := none }, cs)
  | 'S' =>
    let (ns, cs) ← numbers 4 cs
    let p := ns.toArray
    let (x1, y1) := match st.lastC with
      | some (qx, qy) => (2 * st.cx - qx, 2 * st.cy - qy)
      | none => (st.cx, st.cy)
    let (x2, y2, x, y) := (ox + p[0]!, oy + p[1]!, ox + p[2]!, oy + p[3]!)
    pure ({ st with out := st.out.push s!"C {fmt x1} {fmt y1} {fmt x2} {fmt y2} {fmt x} {fmt y}", cx := x, cy := y, lastC := some (x2, y2), lastQ := none }, cs)
  | 'Q' =>
    let (ns, cs) ← numbers 4 cs
    let p := ns.toArray
    let (x1, y1, x, y) := (ox + p[0]!, oy + p[1]!, ox + p[2]!, oy + p[3]!)
    pure ({ st with out := st.out.push s!"Q {fmt x1} {fmt y1} {fmt x} {fmt y}", cx := x, cy := y, lastQ := some (x1, y1), lastC := none }, cs)
  | 'T' =>
    let (ns, cs) ← numbers 2 cs
    let (x1, y1) := match st.lastQ with
      | some (qx, qy) => (2 * st.cx - qx, 2 * st.cy - qy)
      | none => (st.cx, st.cy)
    let (x, y) := (ox + ns[0]!, oy + ns[1]!)
    pure ({ st with out := st.out.push s!"Q {fmt x1} {fmt y1} {fmt x} {fmt y}", cx := x, cy := y, lastQ := some (x1, y1), lastC := none }, cs)
  | _ => none

/-- The segments of path data `cs`, with fuel (one step per segment); a command letter may
be followed by several coordinate groups (implicit repetition; after M, an implicit L). -/
def pathGo : Nat → PathState → Option Char → List Char → Array String
  | 0, st, _, _ => st.out
  | fuel + 1, st, last, cs =>
    let cs := cs.dropWhile SvgValues.isWs
    match cs with
    | [] => st.out
    | c :: rest =>
      if isCmd c then
        if st.out.isEmpty && c.toUpper != 'M' then st.out else
        match segment st c rest with
        | some (st', rest') =>
          let next := if c == 'M' then some 'L' else if c == 'm' then some 'l' else some c
          pathGo fuel st' (if c.toUpper == 'Z' then none else next) rest'
        | none => st.out
      else
        match last with
        | some l =>
          match segment st l cs with
          | some (st', rest') => pathGo fuel st' (some l) rest'
          | none => st.out
        | none => st.out

/-- The normalized segments of path data `v`, one per line. -/
def pathText (v : String) : String :=
  "\n".intercalate (pathGo (v.length + 1) {} none v.toList).toList

#guard pathText "m 10 20 l 5 5 h 10 v -5 z" == "M 10 20\nL 15 25\nL 25 25\nL 25 20\nZ"
#guard pathText "M0,0 Q 10 0 10 10 T 10 30" == "M 0 0\nQ 10 0 10 10\nQ 10 20 10 30"
#guard pathText "M 0 0 L 10 10 X 3" == "M 0 0\nL 10 10"

/-- A trait getter (A.8.13): node `n`, namespace `ns` (empty: none), `name`, type `k`. -/
def get (d : Dom) (n : NodeId) (ns : String) (name : String) (k : Kind) : Except Int String := do
  if n ≥ d.size then throw notSupported
  let node := d.get n
  if node.type != .element || node.ns != some svgNS then throw notSupported
  let el := node.lname
  if ns != "" then
    if ns == xlinkNS && name == "href" && xlinkHrefOn el && k == .string then
      return (specified d n (some xlinkNS) "href").getD ""
    throw notSupported
  if name == "#text" && k == .string then
    return (d.textContent n).getD ""
  let some t := traitOf el name | throw notSupported
  if t.gets.isEmpty then throw notSupported
  if !t.gets.contains k then throw typeMismatch
  let v := computed d t name (d.size + 1) n
  match k with
  | .string =>
    match v with
    | none => return nullText
    | some v =>
      let v := trimS v
      if name == "display" then return (if v == "none" then "none" else "inline")
      if name == "font-weight" then
        return (if v == "normal" then "400" else if v == "bold" then "700" else v)
      return v
  | .float =>
    let some v := v | throw typeMismatch
    if (name == "x" || name == "y") && el == "text" then
      match SvgValues.parseNumberList v with
      | some [x] => return x
      | _ => throw typeMismatch
    numberText v
  | .floatList =>
    let some v := v | throw typeMismatch
    if trimS v == "none" then return ""
    match SvgValues.parseNumberList v with
    | some xs => return " ".intercalate xs
    | none => throw typeMismatch
  | .rgb =>
    let some v := v | throw typeMismatch
    rgbText d n v
  | .rect =>
    match v with
    | none => return nullText
    | some v => rectText v
  | .path => return pathText (v.getD "")
  | .matrix =>
    let v := trimS (v.getD "")
    if v == "" || v == "none" then return ""
    if v.startsWith "ref(" then return ""
    match SvgValues.parseTransformList v with
    | some ts => return "\n".intercalate (ts.map fun (f, xs) => " ".intercalate (f :: xs))
    | none => return ""

/-- Whether animation or media timing of node `n` may still be changed through traits
(A.8.14: not once the element is in the tree). -/
def inTree (d : Dom) (n : NodeId) : Bool := d.isInclusiveAncestor 0 n

/-- The prelude's text for a setter argument that is not of the setter's type, and for null. -/
def typeMark : String := "\u0001type"
def nullMark : String := "\u0001null"

/-- A trait setter (A.8.13): the attribute text to write for value `v` (the prelude's text
of the typed value), or the DOMException code. -/
def set (d : Dom) (n : NodeId) (ns : String) (name : String) (k : Kind) (v : String) : Except Int String := do
  if n ≥ d.size then throw notSupported
  let node := d.get n
  if node.type != .element || node.ns != some svgNS then throw notSupported
  let el := node.lname
  if ns != "" then
    if ns == xlinkNS && name == "href" && xlinkHrefOn el && k == .string then return v
    throw notSupported
  if name == "#text" && k == .string then return v
  let some t := traitOf el name | throw notSupported
  if (animations.contains el || (media.contains el && !t.property)) && inTree d n then throw notSupported
  if !t.sets.contains k then throw typeMismatch
  -- the prelude's marks for an argument of another type and for null (`BAD_TYPE`, `BAD_NULL`)
  if v == typeMark then throw typeMismatch
  if v == nullMark then throw invalidAccess
  let s := trimS v
  match k with
  | .string =>
    if t.property && s == "inherit" then return s
    if !t.keywords.isEmpty then
      if t.keywords.contains s then return s
      -- a typed trait also takes its own syntax as text (`setTrait("width", "auto")` and numbers)
      if t.sets.contains .float then
        match SvgValues.parseNumber s with
        | some x => return x
        | none => throw invalidAccess
      throw invalidAccess
    if t.sets.contains .rgb then
      if s == "none" || s.startsWith "url(" || s.toLower == "currentcolor" || (PageCanvas.Color.parse? s).isSome then return s
      throw invalidAccess
    if t.sets.contains .float then
      match SvgValues.parseNumber s with
      | some x => return x
      | none => throw invalidAccess
    if name == "transform" then
      if s == "none" || s.startsWith "ref(" || (SvgValues.parseTransformList s).isSome then return s
      throw invalidAccess
    return v
  | .float =>
    let some x := SvgValues.parseNumber s | throw invalidAccess
    let some f := PageCanvas.Color.number? x | throw invalidAccess
    if f.isNaN || f.isInf then throw invalidAccess
    if let some lo := t.lo then if f < lo then throw invalidAccess
    if let some hi := t.hi then if f > hi then throw invalidAccess
    return x
  | .floatList =>
    let some xs := SvgValues.parseNumberList s | throw invalidAccess
    if name == "points" && xs.length % 2 == 1 then throw invalidAccess
    return " ".intercalate xs
  | .rgb =>
    match SvgValues.parseNumberList s with
    | some [r, g, b] => return s!"rgb({r},{g},{b})"
    | _ => throw invalidAccess
  | .rect =>
    match SvgValues.parseNumberList s with
    | some [x, y, w, h] =>
      if w.startsWith "-" || h.startsWith "-" then throw invalidAccess
      return s!"{x} {y} {w} {h}"
    | _ => throw invalidAccess
  | .matrix =>
    match SvgValues.parseNumberList s with
    | some [a, b, c, e, f, g] => return s!"matrix({a},{b},{c},{e},{f},{g})"
    | _ => throw invalidAccess
  | .path =>
    -- the prelude's segments ("M x y\nL x y..."): every command is M, L, C, Q or Z
    let lines := (s.splitOn "\n").filter (· != "")
    let ok := lines.all fun line =>
      match line.splitOn " " with
      | ["Z"] => true
      | c :: xs => (((c == "M" || c == "L") && xs.length == 2) || (c == "C" && xs.length == 6) || (c == "Q" && xs.length == 4)) &&
          xs.all fun x => (SvgValues.parseNumber x).isSome
      | [] => false
    if !ok then throw invalidAccess
    return " ".intercalate lines

/-- `web_api` op 210 (`get`: node, namespace, name, type code) and 211 (`set`: the same and
the value text). -/
def op (code : Nat) (fs : Array ByteArray) (d : Dom) : Except Int ByteArray := do
  let str := SvgValues.strAt fs
  let some n := (str 0).toNat? | throw notSupported
  let some k := (str 3).toNat?.bind Kind.ofCode | throw notSupported
  match code with
  | 210 => return (← get d n (str 1) (str 2) k).toUTF8
  | 211 => return (← set d n (str 1) (str 2) k (str 4)).toUTF8
  | _ => throw (-2)

end L4Factoidal.DOM.SvgTinyTraits
