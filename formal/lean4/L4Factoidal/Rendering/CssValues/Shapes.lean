/-
Canonical and computed forms of values whose serialisation is more than the order of their
grammar: path data, the basic shapes, `rotate`, shadows.

The grammar (`Grammar.matchText`) gives a value in the order of its grammar, with each leaf
in its canonical form. A few values are written in another way than they are read:

* `path("M10,10h80z")` is `path("M 10 10 h 80 Z")`, and as a computed value its commands are
  absolute (CSS Shapes 1 §3.1; SVG 2 §9.3);
* `rect()` and `xywh()` compute to `inset()` (CSS Shapes 1 §3.1: "computes to the
  equivalent inset() function");
* a shape's default box, the fill rule `nonzero` and a rounding of zero are left out;
* a `rotate` about a coordinate axis is written with the axis name (CSS Transforms 2 §5.1);
* a computed shadow is its colour, then all its lengths, then `inset` (CSS Backgrounds 3
  §6.1.1).

Everything here is a function from component values to component values, or to text.
Lists are folds; the one loop (`pathLoop`) is a tail call per character.
-/
import L4Factoidal.Rendering.CssValues.Numeric

namespace L4Factoidal.Rendering.CssValues

/-! ### Path data -/

/-- The number of arguments of a path command, by its lower-case letter (SVG 2 §9.3). -/
def pathArity : Char → Option Nat
  | 'm' => some 2 | 'l' => some 2 | 't' => some 2
  | 'h' => some 1 | 'v' => some 1
  | 'c' => some 6 | 's' => some 4 | 'q' => some 4
  | 'a' => some 7 | 'z' => some 0
  | _ => none

/-- A path segment: its command letter and its arguments. -/
abbrev PathSeg := Char × List Rat

/-- The reading of path data so far. -/
structure PathState where
  segs : Array PathSeg := #[]
  /-- The command the next arguments belong to; `none` at the start and after `Z`. -/
  cmd : Option Char := none
  /-- The arguments of the group being read, last first. -/
  args : List Rat := []
  /-- A command letter was read and none of its argument groups is complete yet. -/
  pending : Bool := false
  bad : Bool := false

def pathSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c' || c == ','

/-- Read path data, one character or one number at a step (each step is a tail call; the
fuel is the length of the text). After `M x y` further pairs are `L`; the two flags of an
arc are single digits. -/
def pathLoop : Nat → List Char → PathState → PathState
  | 0, _, st => st
  | _, [], st => st
  | fuel + 1, c :: rest, st =>
    if pathSpace c then pathLoop fuel rest st
    else if c.isAlpha then
      match pathArity c.toLower with
      | none => {st with bad := true}
      | some n =>
        if st.pending || !st.args.isEmpty || (st.segs.isEmpty && c.toLower != 'm') then {st with bad := true}
        else if n == 0 then pathLoop fuel rest {st with segs := st.segs.push ('Z', []), cmd := none}
        else pathLoop fuel rest {st with cmd := some c, pending := true}
    else
      match st.cmd with
      | none => {st with bad := true}
      | some k =>
        let flag := k.toLower == 'a' && (st.args.length == 3 || st.args.length == 4)
        let read : Option (Rat × List Char) :=
          if flag then (if c == '0' then some (0, rest) else if c == '1' then some (1, rest) else none)
          else if startsNumber (c :: rest) then
            let (v, _, more) := consumeNumber (c :: rest)
            some (v, more)
          else none
        match read with
        | none => {st with bad := true}
        | some (v, more) =>
          let args := v :: st.args
          if some args.length == pathArity k.toLower then
            let next := if k == 'M' then 'L' else if k == 'm' then 'l' else k
            pathLoop fuel more {st with segs := st.segs.push (k, args.reverse), args := [], pending := false, cmd := some next}
          else pathLoop fuel more {st with args := args}

/-- The segments of path data; `none` when it is not path data, or is empty. -/
def pathParse (s : String) : Option (Array PathSeg) :=
  let st := pathLoop (s.length + 1) s.toList {}
  if st.bad || st.pending || !st.args.isEmpty || st.segs.isEmpty then none else some st.segs

/-- Path data as text: each command and each number apart by one space. -/
def pathText (segs : Array PathSeg) : String :=
  " ".intercalate (segs.toList.map fun (c, args) => " ".intercalate (String.singleton c :: args.map fmtRat))

/-- The current point and the start of the subpath. -/
structure PathPos where
  x : Rat := 0
  y : Rat := 0
  sx : Rat := 0
  sy : Rat := 0

/-- The same path with every command absolute. -/
def pathAbsolute (segs : Array PathSeg) : Array PathSeg :=
  (segs.foldl (fun (acc : Array PathSeg × PathPos) (seg : PathSeg) =>
    let p := acc.2
    let c := seg.1
    let dx := if c.isLower then p.x else 0
    let dy := if c.isLower then p.y else 0
    match c.toLower, seg.2 with
    | 'z', _ => (acc.1.push ('Z', []), {p with x := p.sx, y := p.sy})
    | 'm', [x, y] => (acc.1.push ('M', [x + dx, y + dy]), {x := x + dx, y := y + dy, sx := x + dx, sy := y + dy})
    | 'h', [x] => (acc.1.push ('H', [x + dx]), {p with x := x + dx})
    | 'v', [y] => (acc.1.push ('V', [y + dy]), {p with y := y + dy})
    | 'c', [a, b, c2, d, x, y] =>
      (acc.1.push ('C', [a + dx, b + dy, c2 + dx, d + dy, x + dx, y + dy]), {p with x := x + dx, y := y + dy})
    | 'a', [rx, ry, rot, large, sweep, x, y] =>
      (acc.1.push ('A', [rx, ry, rot, large, sweep, x + dx, y + dy]), {p with x := x + dx, y := y + dy})
    | _, [a, b, x, y] => (acc.1.push (c.toUpper, [a + dx, b + dy, x + dx, y + dy]), {p with x := x + dx, y := y + dy})
    | _, [x, y] => (acc.1.push (c.toUpper, [x + dx, y + dy]), {p with x := x + dx, y := y + dy})
    | _, _ => (acc.1.push seg, p)) (#[], {})).1

/-- The arguments of `path()` in canonical form: the fill rule `nonzero` left out, the data
with single spaces, absolute when `absolute`. `none`: the data is not a path. -/
def pathArgs (absolute : Bool) (args : List CV) : Option (List CV) :=
  let groups := (splitCommas (stripWs args)).filter (!·.isEmpty)
  let rule : List CV := match groups with
    | [.tok (.ident r)] :: _ :: _ => if lower r == "evenodd" then [.tok (.ident "evenodd"), .tok .comma] else []
    | _ => []
  match groups.getLast? with
  | some [.tok (.str s)] =>
    (pathParse s).map fun segs => rule ++ [.tok (.str (pathText (if absolute then pathAbsolute segs else segs)))]
  | _ => none

/-! ### Lengths and percentages of the inset of a shape -/

/-- `pct% + px`, and whether a percentage is part of it (so it is written even when 0). -/
structure LP where
  pct : Rat := 0
  px : Rat := 0
  hasPct : Bool := false

/-- A computed `<length-percentage>` as a sum: `Npx`, `N%`, `0`, or `calc()` of a sum of
those. -/
def LP.ofCV : CV → Option LP
  | .tok (.dim v _ u) => if lower u == "px" then some {px := v} else none
  | .tok (.pct v) => some {pct := v, hasPct := true}
  | .tok (.num v _) => if v == 0 then some {} else none
  | .fn name args =>
    if lower name != "calc" then none
    else
      (stripWs args).foldl (fun (acc : Option (LP × Rat)) cv =>
        match acc with
        | none => none
        | some (lp, sign) =>
          match cv with
          | .tok (.delim '+') => some (lp, 1)
          | .tok (.delim '-') => some (lp, -1)
          | .tok (.dim v _ u) => if lower u == "px" then some ({lp with px := lp.px + sign * v}, 1) else none
          | .tok (.pct v) => some ({lp with pct := lp.pct + sign * v, hasPct := true}, 1)
          | _ => none) (some ({}, 1)) |>.map (·.1)
  | _ => none

def LP.add (a b : LP) : LP := {pct := a.pct + b.pct, px := a.px + b.px, hasPct := a.hasPct || b.hasPct}

/-- `100% - a`. -/
def LP.fromFull (a : LP) : LP := {pct := 100 - a.pct, px := -a.px, hasPct := true}

/-- The component value of a sum: a length, a percentage (a length of 0 beside it is left
out), or `calc(P% + Npx)`. -/
def LP.cv (a : LP) : CV :=
  if !a.hasPct then .tok (.dim a.px true "px")
  else if a.px == 0 then .tok (.pct a.pct)
  else if a.px < 0 then .raw ("calc(" ++ fmtRat a.pct ++ "% - " ++ fmtRat (-a.px) ++ "px)")
  else .raw ("calc(" ++ fmtRat a.pct ++ "% + " ++ fmtRat a.px ++ "px)")

/-- `calc(P% + 0px)` is `P%` as a computed value (the sum has no length left). -/
def dropZeroLength (cv : CV) : CV :=
  match cv with
  | .fn name args =>
    if lower name == "calc" then
      match stripWs args with
      | [.tok (.pct p), .tok (.delim '+'), .tok (.dim v _ u)] => if v == 0 && lower u == "px" then .tok (.pct p) else cv
      | _ => cv
    else cv
  | cv => cv

/-- `dropZeroLength` on every `calc()` of a value. The recursion is on the nesting of
functions. -/
def dropZeroLengths : Nat → List CV → List CV
  | 0, cvs => cvs
  | fuel + 1, cvs => cvs.map fun cv =>
    match dropZeroLength cv with
    | .fn name args => .fn name (dropZeroLengths fuel args)
    | cv => cv

/-! ### Basic shapes -/

def isZeroLength : CV → Bool
  | .tok (.dim v _ _) => v == 0
  | .tok (.num v _) => v == 0
  | _ => false

def isIdent (name : String) : CV → Bool
  | .tok (.ident s) => lower s == name
  | _ => false

/-- The values before `round` and the radii after it (with `round`), when the radii are not
all zero lengths. -/
def splitRound (args : List CV) : List CV × List CV :=
  let before := args.takeWhile (!isIdent "round" ·)
  let after := args.drop (before.length + 1)
  if after.isEmpty || after.all isZeroLength then (before, [])
  else (before, .tok (.ident "round") :: after)

/-- Four sides in the shortest form (top, right, bottom, left), compared by their text. -/
def shortestSides (sides : List CV) : List CV :=
  match sides with
  | [t, r, b, l] =>
    let s := fun (cv : CV) => serialize [cv]
    if s r == s l then
      if s t == s b then (if s t == s r then [t] else [t, r])
      else [t, r, b]
    else sides
  | _ => sides

/-- `rect(top right bottom left)` as the sides of an `inset()`: `auto` is the edge. -/
def rectSides (sides : List CV) : Option (List CV) :=
  match sides with
  | [t, r, b, l] =>
    let edge : CV → Bool → Option CV := fun cv far =>
      if isIdent "auto" cv then some (.tok (.pct 0))
      else if far then (LP.ofCV cv).map fun lp => lp.fromFull.cv
      else some (dropZeroLength cv)
    match edge t false, edge r true, edge b true, edge l false with
    | some t', some r', some b', some l' => some [t', r', b', l']
    | _, _, _, _ => none
  | _ => none

/-- `xywh(x y width height)` as the sides of an `inset()`. -/
def xywhSides (sides : List CV) : Option (List CV) :=
  match sides with
  | [x, y, w, h] =>
    match LP.ofCV x, LP.ofCV y, LP.ofCV w, LP.ofCV h with
    | some lx, some ly, some lw, some lh =>
      some [dropZeroLength y, (lx.add lw).fromFull.cv, (ly.add lh).fromFull.cv, dropZeroLength x]
    | _, _, _, _ => none
  | _ => none

/-- A polygon's first argument without the fill rule `nonzero` and without a rounding of
zero; `[]` when nothing of it is left. -/
def polygonHead (head : List CV) : List CV :=
  let head := head.filter (!isIdent "nonzero" ·)
  match head.reverse with
  | z :: r :: more => if isIdent "round" r && isZeroLength z then more.reverse else head
  | _ => head

/-- One shape function in canonical form (`computed`: in computed form). `none`: a `path()`
whose text is not path data. Any other function is as it was. -/
def shapeFn (computed : Bool) (name : String) (args : List CV) : Option CV :=
  let n := lower name
  let args := stripWs args
  if n == "path" then (pathArgs computed args).map (.fn name ·)
  else if n == "polygon" then
    match splitCommas args with
    | head :: more =>
      let isHead := head.any fun cv => isIdent "nonzero" cv || isIdent "evenodd" cv || isIdent "round" cv
      let head' := if isHead then polygonHead head else head
      let groups := if head'.isEmpty then more else head' :: more
      some (.fn name (groups.foldl (fun (acc : List CV) g => if acc.isEmpty then g else acc ++ [.tok .comma] ++ g) []))
    | [] => some (.fn name args)
  else if n == "inset" || n == "rect" || n == "xywh" then
    let (sides, round) := splitRound args
    if !computed then some (.fn name (sides ++ round))
    else if n == "inset" then some (.fn name (shortestSides (sides.map dropZeroLength) ++ round))
    else
      match (if n == "rect" then rectSides sides else xywhSides sides) with
      | some sides' => some (.fn "inset" (shortestSides sides' ++ round))
      | none => some (.fn name (sides ++ round))
  else some (.fn name args)

/-- The box that a shape is in when the property names none. -/
def defaultShapeBox : String → String
  | "shape-outside" => "margin-box"
  | _ => "border-box"

/-- The properties whose value is a basic shape with a box. -/
def shapeProperties : List String := ["clip-path", "shape-outside", "offset-path", "-webkit-clip-path", "-webkit-shape-outside"]

/-- A shape value in canonical form: the shape first, then its box, the default box left
out beside a shape. `none`: a `path()` that is not path data. A value with no shape
function at the top (a keyword, a box alone, an image, a url) is as it was. -/
def shapeValue (computed : Bool) (p v : String) : Option String :=
  let top := stripWs (CV.parse v)
  let shapes := ["path", "polygon", "inset", "rect", "xywh", "circle", "ellipse", "shape", "ray"]
  let isShape := fun (cv : CV) => match cv with
    | .fn name _ => shapes.contains (lower name)
    | _ => false
  if !top.any isShape then some v
  else
    let fns := top.filter isShape
    let rest := top.filter fun cv => !isShape cv && !isIdent (defaultShapeBox p) cv
    let fns' := fns.map fun cv => match cv with
      | .fn name args => shapeFn computed name args
      | cv => some cv
    if fns'.any (·.isNone) then none
    else some (serialize (fns'.filterMap id ++ rest))

/-! ### `rotate` -/

/-- The canonical form of a `rotate` value (CSS Transforms 2 §5.1): a vector along one
coordinate axis is the name of the axis (and the angle is negated when the vector points
the other way), and a rotation about z is the angle alone. -/
def rotateCanon (v : String) : String :=
  let top := stripWs (CV.parse v)
  let negated : CV → Option CV := fun cv => match cv with
    | .tok (.dim a int u) => some (.tok (.dim (-a) int u))
    | _ => none
  let about := fun (axis : String) (sign : Rat) (angle : CV) =>
    let angle' := if sign < 0 then negated angle else some angle
    match angle' with
    | some a => if axis == "z" then serialize [a] else axis ++ " " ++ serialize [a]
    | none => v
  match top with
  | [.tok (.ident axis), angle] => if lower axis == "z" then serialize [angle] else v
  | [.tok (.num x _), .tok (.num y _), .tok (.num z _), angle] =>
    if x != 0 && y == 0 && z == 0 then about "x" x angle
    else if x == 0 && y != 0 && z == 0 then about "y" y angle
    else if x == 0 && y == 0 && z != 0 then about "z" z angle
    else v
  | _ => v

/-- The computed form of `offset-rotate` (Motion Path 1 §5.4): `reverse` is `auto` with
half a turn more. -/
def offsetRotateComputed (v : String) : String :=
  match stripWs (CV.parse v) with
  | [.tok (.ident k)] => if lower k == "reverse" then "auto 180deg" else v
  | [.tok (.ident k), .tok (.dim a _ u)] =>
    if lower k == "reverse" && lower u == "deg" then "auto " ++ fmtRat (a + 180) ++ "deg" else v
  | _ => v

/-- The computed form of `zoom` (CSS Viewport 1 §10): a number; `normal` and 0 are 1. -/
def zoomComputed (v : String) : String :=
  let number := fun (x : Rat) => if x == 0 then "1" else fmtRat x
  match stripWs (CV.parse v) with
  | [.tok (.ident k)] => if lower k == "normal" then "1" else v
  | [.tok (.pct x)] => number (x / 100)
  | [.tok (.num x _)] => number x
  | _ => v

/-! ### Shadows -/

/-- A computed shadow list (`box-shadow` with four lengths, `text-shadow` with three): each
shadow is its colour (the element's colour when it names none), its lengths with those
left out as `0px`, then `inset`. -/
def shadowComputed (lengths : Nat) (current : Option String) (v : String) : String :=
  let top := stripWs (CV.parse v)
  if top.length == 1 && top.all (isIdent "none") then v
  else
    let isLength := fun (cv : CV) => match cv with
      | .tok (.dim _ _ _) => true
      | .tok (.num _ _) => true
      | .fn name _ => mathFunctions.contains (lower name) || lower name == "calc"
      | _ => false
    let shadows := (splitCommas top).map fun item =>
      let inset := item.filter (isIdent "inset")
      let lens := item.filter isLength
      let colour := item.filter fun cv => !isLength cv && !isIdent "inset" cv
      let colour' : List CV := if colour.isEmpty then (match current with | some c => [.raw c] | none => []) else colour
      let pad := (List.replicate (lengths - lens.length) (CV.tok (.dim 0 true "px")))
      serialize (colour' ++ lens ++ pad ++ inset)
    ", ".intercalate shadows

/-! ### Tests -/

#guard (pathParse "M10,10h80v80h-80z").map pathText == some "M 10 10 h 80 v 80 h -80 Z"
#guard (pathParse "M10,10h80v80h-80z").map (pathText ∘ pathAbsolute) == some "M 10 10 H 90 V 90 H 10 Z"
#guard (pathParse "m 10 170 h 90 v 30 m 0 0 s 1 2 3 4 z c 9 8 7 6 5 4").map (pathText ∘ pathAbsolute) ==
  some "M 10 170 H 100 V 200 M 100 200 S 101 202 103 204 Z C 109 208 107 206 105 204"
#guard (pathParse "M0,0A25,25,0,0,1,50,0").map pathText == some "M 0 0 A 25 25 0 0 1 50 0"
#guard (pathParse "M0 0a25 25 0 01 50 0").map pathText == some "M 0 0 a 25 25 0 0 1 50 0"
#guard (pathParse "M 0 0 10 10 20 0").map pathText == some "M 0 0 L 10 10 L 20 0"
#guard (pathParse "M0 0L1.5.5-3-4").map pathText == some "M 0 0 L 1.5 0.5 L -3 -4"
#guard pathParse "" == none && pathParse " " == none && pathParse "not-a-path" == none
#guard pathParse "M 20 30 A 60 70 80" == none && pathParse "L 1 2" == none && pathParse "M 1 2 Z 3 4" == none
#guard shapeValue false "clip-path" "path(nonzero, \"M20,20h60 v60 h-60z\")" == some "path(\"M 20 20 h 60 v 60 h -60 Z\")"
#guard shapeValue true "clip-path" "path(evenodd, \"M10,10h80\")" == some "path(evenodd, \"M 10 10 H 90\")"
#guard shapeValue false "clip-path" "path(\"x\")" == none
#guard shapeValue false "clip-path" "polygon(nonzero round 1px, 1px 2px, 3em 4em)" == some "polygon(round 1px, 1px 2px, 3em 4em)"
#guard shapeValue false "clip-path" "polygon(round 0px, 1px 2px, 3px 4px)" == some "polygon(1px 2px, 3px 4px)"
#guard shapeValue false "clip-path" "polygon(evenodd, 1px 2px, 3px 4px)" == some "polygon(evenodd, 1px 2px, 3px 4px)"
#guard shapeValue false "clip-path" "circle(7% at 8% 9%) border-box" == some "circle(7% at 8% 9%)"
#guard shapeValue false "shape-outside" "border-box circle(7% at 8% 9%)" == some "circle(7% at 8% 9%) border-box"
#guard shapeValue false "shape-outside" "margin-box circle()" == some "circle()"
#guard shapeValue false "shape-outside" "margin-box" == some "margin-box"
#guard shapeValue false "clip-path" "xywh(0px 1% 2px 3em round 0px)" == some "xywh(0px 1% 2px 3em)"
#guard shapeValue true "clip-path" "rect(auto auto auto auto)" == some "inset(0%)"
#guard shapeValue true "clip-path" "rect(0px 1% 2px 20px)" == some "inset(0px 99% calc(100% - 2px) 20px)"
#guard shapeValue true "clip-path" "rect(-10% -20% -15% -12%)" == some "inset(-10% 120% 115% -12%)"
#guard shapeValue true "clip-path" "rect(0px 0px 0px 0px)" == some "inset(0px 100% 100% 0px)"
#guard shapeValue true "shape-outside" "rect(0px calc(100% - 20px) 2% 48px)" == some "inset(0px calc(0% + 20px) 98% 48px)"
#guard shapeValue true "clip-path" "xywh(0px calc(1% + 1px) calc(2% + 2px) calc(3% + 3px))" ==
  some "inset(calc(1% + 1px) calc(98% - 2px) calc(96% - 4px) 0px)"
#guard shapeValue true "clip-path" "xywh(0px 1% 2px 3% round 0px 1px)" == some "inset(1% calc(100% - 2px) 96% 0px round 0px 1px)"
#guard shapeValue true "clip-path" "inset(50% 20% 30% 20%)" == some "inset(50% 20% 30%)"
#guard shapeValue true "shape-outside" "circle(at calc(75% + 0px) calc(75% + 0px))" == some "circle(at calc(75% + 0px) calc(75% + 0px))"
#guard rotateCanon "1 0 0 400grad" == "x 400grad" && rotateCanon "0 -0.5 0 400grad" == "y -400grad"
#guard rotateCanon "0 0 1 30deg" == "30deg" && rotateCanon "z 30deg" == "30deg" && rotateCanon "0 0 -1 30deg" == "-30deg"
#guard rotateCanon "100 200 300 400grad" == "100 200 300 400grad" && rotateCanon "0 0 0 1deg" == "0 0 0 1deg"
#guard rotateCanon "x 30deg" == "x 30deg" && rotateCanon "none" == "none" && rotateCanon "30deg" == "30deg"
#guard shadowComputed 4 (some "rgb(0, 0, 255)") "1px 2px" == "rgb(0, 0, 255) 1px 2px 0px 0px"
#guard shadowComputed 4 none "rgb(0, 255, 0) 1px 2px 3px 4px inset" == "rgb(0, 255, 0) 1px 2px 3px 4px inset"
#guard shadowComputed 3 (some "rgb(0, 0, 255)") "10px 20px, rgb(255, 0, 0) 30px 40px" ==
  "rgb(0, 0, 255) 10px 20px 0px, rgb(255, 0, 0) 30px 40px 0px"
#guard shadowComputed 4 none "none" == "none"
#guard offsetRotateComputed "reverse" == "auto 180deg" && offsetRotateComputed "reverse -45deg" == "auto 135deg"
#guard offsetRotateComputed "auto 30deg" == "auto 30deg" && offsetRotateComputed "auto" == "auto"
#guard zoomComputed "normal" == "1" && zoomComputed "150%" == "1.5" && zoomComputed "0%" == "1" && zoomComputed "0.5" == "0.5"
#guard serialize (dropZeroLengths 8 (CV.parse "circle(at calc(75% + 0px) calc(0% + 10px))")) == "circle(at 75% calc(0% + 10px))"

end L4Factoidal.Rendering.CssValues
