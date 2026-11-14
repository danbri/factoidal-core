/-
L4Factoidal.Rendering.Animation.Value: the computed value of a property as component
tokens, and interpolation, addition and accumulation of two such values (CSS Values 4
§3 "combining values"; Web Animations 1 §5.2 "animation types").

The cascade gives a property's computed value as canonical CSS text (lengths in px,
colours as `rgb()`/`rgba()`, `calc(P% + Lpx)` for a mixed length-percentage). `parse`
reads that text into a flat list of tokens: numbers and dimensions as `Animation.Fix`
integers, a colour as one token, a mixed length-percentage as one token, and the
function names, parentheses, commas and slashes that give the value its shape.

Two values interpolate when they have the same shape (`lerpList`): the numeric
components move by the progress, everything else must be equal. Values of different
shapes are not interpolable and flip at 50% (Web Animations 1 §5.2 "discrete"). A
property's `Kind` adds what its definition says of the result: not negative, a whole
number, in [0, 1], or `visibility`'s rule.

Theorems: at progress 0 each component of a component-wise result is the start value's
component, and at 1 the end value's, exactly, or that component written as a mixed
length-percentage with the other part 0 (`lerpTok_zero`, `lerpTok_one`: the form CSS
Values 4 §3.1 gives a length interpolated with a percentage); a value interpolated with
itself is itself (`interpolate_self`); a non-negative kind gives no negative number
(`nonNegative_range`); a number token interpolates between its ends for a progress in
[0, 1] (`lerpTok_num`, with `Fix.lerp_between`).
-/
import L4Factoidal.Rendering.Animation.Fix
import L4Factoidal.Rendering.Animation.Matrix

namespace L4Factoidal.Rendering.Animation

/-- One component of a computed value. -/
inductive Tok where
  | num (n : Int)
  /-- A dimension or a percentage (unit "%"); the unit in lower case. -/
  | dim (n : Int) (unit : String)
  /-- A length-percentage with both parts: `calc(pct% + px px)`. -/
  | lp (px pct : Int)
  /-- An sRGB colour: channels 0 to 255, alpha 0 to 1. -/
  | color (r g b a : Int)
  | ident (s : String)
  /-- A string or a `url()`, verbatim. -/
  | str (s : String)
  | hash (s : String)
  /-- `name(`; the name in lower case, "" for a plain parenthesis. -/
  | op (name : String)
  | close | comma | slash
  deriving DecidableEq, Repr, Inhabited

abbrev Value := List Tok

namespace Value
open Fix (one half)

/-! ## Reading computed text -/

def isNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat ≥ 0x80
def isNameChar (c : Char) : Bool := isNameStart c || c.isDigit || c == '-'

/-- The text of a number at the start of `cs` (sign, digits, fraction, exponent) and the
rest; none when `cs` does not start with a number. -/
def takeNumber (cs : List Char) : Option (List Char × List Char) :=
  let (sign, r) := match cs with
    | '-' :: r => (['-'], r)
    | '+' :: r => (['+'], r)
    | r => ([], r)
  let whole := r.takeWhile Char.isDigit
  let r1 := r.drop whole.length
  let (frac, r2) := match r1 with
    | '.' :: d :: r' => if d.isDigit then
        let f := (d :: r').takeWhile Char.isDigit
        ('.' :: f, (d :: r').drop f.length)
      else ([], r1)
    | _ => ([], r1)
  if whole.isEmpty && frac.isEmpty then none else
  let (exp, r3) := match r2 with
    | e :: r' =>
      if e == 'e' || e == 'E' then
        let (es, r'') := match r' with
          | '-' :: x => (['-'], x)
          | '+' :: x => (['+'], x)
          | x => ([], x)
        let ds := r''.takeWhile Char.isDigit
        if ds.isEmpty then ([], r2) else ('e' :: es ++ ds, r''.drop ds.length)
      else ([], r2)
    | [] => ([], r2)
  some (sign ++ whole ++ frac ++ exp, r3)

/-- The tokens of CSS text. Unknown characters become one-character identifiers, so every
text has tokens; a string that does not close runs to the end. -/
def tokenize (text : String) : List Tok := Id.run do
  let mut rest := text.toList
  let mut out : Array Tok := #[]
  for _ in [0:text.length + 1] do
    match rest with
    | [] => break
    | c :: r =>
      if c.isWhitespace then rest := r
      else if c == ',' then out := out.push .comma; rest := r
      else if c == '/' then out := out.push .slash; rest := r
      else if c == ')' then out := out.push .close; rest := r
      else if c == '(' then out := out.push (.op ""); rest := r
      else if c == '"' || c == '\'' then
        -- a string: to the same quote not after a backslash
        let mut body : List Char := [c]
        let mut rr := r
        let mut escaped := false
        for _ in [0:r.length + 1] do
          match rr with
          | [] => break
          | x :: xs =>
            body := x :: body
            rr := xs
            if escaped then escaped := false
            else if x == '\\' then escaped := true
            else if x == c then break
        out := out.push (.str (String.ofList body.reverse))
        rest := rr
      else if c == '#' then
        let name := r.takeWhile isNameChar
        out := out.push (.hash (String.ofList name))
        rest := r.drop name.length
      else match takeNumber rest with
        | some (numText, r') =>
          match Fix.parse (String.ofList numText) with
          | some n =>
            match r' with
            | '%' :: r'' => out := out.push (.dim n "%"); rest := r''
            | u :: _ =>
              if isNameStart u then
                let unit := r'.takeWhile isNameChar
                out := out.push (.dim n (String.ofList unit).toLower)
                rest := r'.drop unit.length
              else out := out.push (.num n); rest := r'
            | [] => out := out.push (.num n); rest := r'
          | none => out := out.push (.ident (String.ofList numText)); rest := r'
        | none =>
          if isNameStart c || (c == '-' && (match r with | d :: _ => isNameStart d || d == '-' | [] => false)) then
            let name := rest.takeWhile isNameChar
            let after := rest.drop name.length
            match after with
            | '(' :: r'' =>
              let lname := (String.ofList name).toLower
              if lname == "url" then
                -- url(...) verbatim to the closing parenthesis
                let body := r''.takeWhile (· != ')')
                out := out.push (.str ("url(" ++ String.ofList body ++ ")"))
                rest := (r''.drop body.length).drop 1
              else out := out.push (.op lname); rest := r''
            | _ => out := out.push (.ident (String.ofList name)); rest := after
          else out := out.push (.ident (String.singleton c)); rest := r
  return out.toList

/-- A length-percentage from its two parts. A part that is 0 stays: a length interpolated
with a percentage is `calc(0% + 10px)` at the length's end (CSS Values 4 §3.1), which is
what a browser serializes. -/
def mkLp (px pct : Int) : Tok := .lp px pct

/-- A colour function or a `calc(P% ± Lpx)` at the head of `ts`, as one token, with the
number of tokens it takes: `rgb(r, g, b)`, `rgba(r, g, b, a)` (CSS Color 4 §15.2
serialization of sRGB) and the computed form of a mixed length-percentage (CSS Values 4
§10.12). -/
def headGroup : List Tok → Option (Tok × Nat)
  | .op f :: .num r :: .comma :: .num g :: .comma :: .num b :: .close :: _ =>
    if f == "rgb" || f == "rgba" then some (.color r g b one, 7) else none
  | .op f :: .num r :: .comma :: .num g :: .comma :: .num b :: .comma :: .num a :: .close :: _ =>
    if f == "rgb" || f == "rgba" then some (.color r g b a, 9) else none
  | .op f :: .dim x u :: .ident sign :: .dim y v :: .close :: _ =>
    let y' := if sign == "-" then -y else y
    if f != "calc" || !(sign == "+" || sign == "-") then none
    else if u == "%" && v == "px" then some (mkLp y' x, 5)
    else if u == "px" && v == "%" then some (mkLp x y', 5)
    else none
  | _ => none

/-- Each group of `headGroup` as its one token; other tokens stay. One pass, no
recursion. -/
def collapse (ts : List Tok) : List Tok := Id.run do
  let mut rest := ts
  let mut out : Array Tok := #[]
  for _ in [0:ts.length + 1] do
    match rest with
    | [] => break
    | t :: r =>
      match rest with
      | .op "repeat" :: .num n :: r' =>
        -- the count of `repeat()` (CSS Grid 2 §7.2.3) is part of the shape, not a quantity
        out := (out.push (.op "repeat")).push (.ident (Fix.formatCss n))
        rest := r'
      | _ =>
        match headGroup rest with
        | some (g, k) => out := out.push g; rest := rest.drop k
        | none => out := out.push t; rest := r
  return out.toList

/-- The tokens of a computed value. -/
def parse (text : String) : Value := collapse (tokenize text)

/-! ## Writing -/

/-- The slack of a rounding boundary: a thousandth. A number of a declaration kept as
text carries six decimals (CSSOM writes a number so), so an easing function read back
from a `style` attribute gives a progress within 10⁻⁶ of the one that was set, and a
result that should be on a boundary (76.5 of a colour channel, a whole pixel of a line
width) may arrive a hair under it. Results within the slack of a boundary are taken as on
it. -/
def slack : Int := 1000000

/-- A colour channel as a whole number 0 to 255 (a half rounds up, within `slack`). -/
def channel (c : Int) : Int := Fix.clamp 0 255 (Fix.roundDiv (c + slack) Fix.scale)

/-- Kind: range. Says: a written colour channel is in 0 to 255, for every number. -/
theorem channel_range (c : Int) : 0 ≤ channel c ∧ channel c ≤ 255 :=
  Fix.clamp_between 0 255 _ (by decide)

def tokText : Tok → String
  | .num n => Fix.formatCss n
  | .dim n u => Fix.formatCss n ++ u
  | .lp px pct =>
    -- with no length part the value is the percentage; with a 0% part it stays a
    -- `calc()`, which depends on the percentage basis (as browsers serialize it)
    if px == 0 then Fix.formatCss pct ++ "%"
    else if px < 0 then s!"calc({Fix.formatCss pct}% - {Fix.formatCss (-px)}px)"
    else s!"calc({Fix.formatCss pct}% + {Fix.formatCss px}px)"
  | .color r g b a =>
    if a ≥ one then s!"rgb({channel r}, {channel g}, {channel b})"
    else s!"rgba({channel r}, {channel g}, {channel b}, {Fix.formatCss (max 0 a)})"
  | .ident s => s
  | .str s => s
  | .hash s => "#" ++ s
  | .op name => name ++ "("
  | .close => ")"
  | .comma => ","
  | .slash => "/"

/-- The text of a value: one space between components, none after `(` or before `)` and
`,`. -/
def toTextGo : Option Tok → List Tok → String → String
  | _, [], acc => acc
  | prev, t :: rest, acc =>
    let space : Bool := match prev, t with
      | none, _ => false
      | some (.op _), _ => false
      | _, .close => false
      | _, .comma => false
      | _, _ => true
    toTextGo (some t) rest (acc ++ (if space then " " else "") ++ tokText t)

def toText (v : Value) : String := toTextGo none v ""

/-! ## Interpolation -/

/-- Premultiplied interpolation of two sRGB colours (CSS Color 4 §12.3; legacy colours
interpolate in sRGB). A result with alpha 0 is transparent black. -/
def lerpColor (p r1 g1 b1 a1 r2 g2 b2 a2 : Int) : Tok :=
  -- the ends are the colours themselves (premultiplying and dividing again rounds)
  if p == 0 then .color r1 g1 b1 a1 else if p == one then .color r2 g2 b2 a2 else
  let a := Fix.clamp 0 one (Fix.lerp a1 a2 p)
  if a == 0 then .color 0 0 0 0 else
  let ch := fun (c1 c2 : Int) =>
    Fix.clamp 0 (Fix.ofInt 255) ((Fix.div (Fix.lerp (Fix.mul c1 a1) (Fix.mul c2 a2) p) a).getD 0)
  .color (ch r1 r2) (ch g1 g2) (ch b1 b2) a

/-- Two components at progress `p`; none when they do not combine. A length and a
percentage combine to a length-percentage (CSS Values 4 §3.1). -/
def lerpTok (p : Int) : Tok → Tok → Option Tok
  | .num a, .num b => some (.num (Fix.lerp a b p))
  | .dim a u, .dim b v =>
    if u == v then some (.dim (Fix.lerp a b p) u)
    else if u == "px" && v == "%" then some (mkLp (Fix.lerp a 0 p) (Fix.lerp 0 b p))
    else if u == "%" && v == "px" then some (mkLp (Fix.lerp 0 b p) (Fix.lerp a 0 p))
    else none
  | .lp x y, .lp x' y' => some (mkLp (Fix.lerp x x' p) (Fix.lerp y y' p))
  | .lp x y, .dim b v =>
    if v == "px" then some (mkLp (Fix.lerp x b p) (Fix.lerp y 0 p))
    else if v == "%" then some (mkLp (Fix.lerp x 0 p) (Fix.lerp y b p))
    else none
  | .dim a u, .lp x y =>
    if u == "px" then some (mkLp (Fix.lerp a x p) (Fix.lerp 0 y p))
    else if u == "%" then some (mkLp (Fix.lerp 0 x p) (Fix.lerp a y p))
    else none
  | .color r1 g1 b1 a1, .color r2 g2 b2 a2 => some (lerpColor p r1 g1 b1 a1 r2 g2 b2 a2)
  | a, b => if a == b then some a else none

/-- Two values of the same shape at progress `p`, component by component; `acc` holds
the components done, last first. A loop: each call is a tail call. -/
def lerpGo (p : Int) : List Tok → List Tok → List Tok → Option (List Tok)
  | [], [], acc => some acc.reverse
  | a :: as, b :: bs, acc =>
    match lerpTok p a b with
    | some t => lerpGo p as bs (t :: acc)
    | none => none
  | _, _, _ => none

/-- Two values of the same shape at progress `p`; none when the shapes differ. -/
def lerpList (p : Int) (a b : List Tok) : Option (List Tok) := lerpGo p a b []

/-- What a property's definition says of an animated value beyond its components. -/
inductive Kind where
  /-- By computed value: component-wise when the shapes agree, else discrete. -/
  | generic
  /-- As generic, and no number, length or percentage below 0 (`width`, `padding`). -/
  | nonNegative
  /-- Whole numbers (`z-index`, `order`). -/
  | integer
  /-- Whole numbers of at least 1 (`column-count`, `orphans`). -/
  | positiveInteger
  /-- Numbers in [0, 1] (`opacity`). -/
  | unit
  /-- Numbers in [1, 1000] (`font-weight`). -/
  | fontWeight
  /-- CSS 2.1 `visibility`: between `visible` and another value, `visible` inside (0, 1). -/
  | visibility
  /-- Never component-wise: flips at 50%. -/
  | discrete
  /-- Discrete, but between the keyword `off` and another value the other value holds
  for the whole of (0, 1): `display` with `none` (CSS Display 4 §2.9),
  `content-visibility` with `hidden` (CSS Containment 2 §4.2), `overlay` with `none`. -/
  | avoid (off : String)
  /-- A list of transform functions (CSS Transforms 1 §11): functions of one name pair up;
  the shorter list is padded with identity functions; `none` is the empty list. -/
  | transformList
  /-- A list of filter functions (Filter Effects 1 §2.1): as transform lists, with each
  function's own neutral value and range. -/
  | filterList
  /-- A comma list of shadows (CSS Backgrounds 3 §6.2.1) of `lengths` lengths each (4 for
  `box-shadow`, 3 for `text-shadow`): the shorter list is padded with transparent shadows
  of zero size; a blur radius is not negative. -/
  | shadowList (lengths : Nat)
  /-- `translate` (CSS Transforms 2 §5): up to three lengths; missing ones are 0. -/
  | translate
  /-- `scale` (CSS Transforms 2 §5): up to three numbers; missing ones are the first, then 1. -/
  | scale
  /-- `rotate` (CSS Transforms 2 §5): an angle, about one axis; `none` is 0 about the
  other value's axis. -/
  | rotate
  /-- One to four values for the four sides, with an optional `fill` (`border-image-slice`,
  `border-image-width`, `border-image-outset` and the `mask-border-*` ones): each side by
  itself, none below 0. -/
  | sides
  /-- Grid track lists (CSS Grid 2 §7.2.4): lists of one shape; each track size by itself,
  discrete where two sizes do not combine; none below 0. -/
  | gridTracks
  /-- A comma list that repeats (CSS Backgrounds 3 §3.6.1 "repeatable list"): both lists are
  repeated to their least common multiple. -/
  | repeatable
  /-- A ratio (CSS Sizing 4 §5.1 `aspect-ratio`): by the logarithm of the ratio. -/
  | ratio
  /-- `offset-rotate` (Motion Path 1 §4.5): `auto` or not, and an angle; `reverse` is
  `auto` with 180deg more. -/
  | offsetRotate
  /-- Basic shapes (CSS Shapes 1 §3.2): component-wise, but a circle or an ellipse with a
  keyword radius does not interpolate. -/
  | shape
  /-- A comma list of gap rule values (CSS Gaps 1 §3): an integer `repeat()` is its items,
  then as a repeatable list; no number below 0. -/
  | gapList
  /-- A corner radius (CSS Backgrounds 3 §5.1): one or two values, none below 0; two equal
  values are written once. -/
  | radius
  /-- `font-style` (CSS Fonts 4 §2.4): `normal` is `oblique 0deg`; the angle stays in
  [-90deg, 90deg]; `italic` is discrete. -/
  | fontStyle
  /-- A corner shape (CSS Borders 4 §4.2): by the half corner of its superellipse
  parameter; never added. -/
  | cornerShape
  /-- `transform-origin` (CSS Transforms 1 §8): two lengths or percentages and an optional
  length z; a missing z is 0px, and a z of 0px is not written. -/
  | origin
  /-- A length whose keyword `word` is the length 0 (`letter-spacing: normal`,
  `vertical-align: baseline`): the keyword interpolates and adds as 0px. With `keep`, a
  result of 0 at an end whose value was the keyword is the keyword (the computed value of
  `letter-spacing` keeps `normal`). -/
  | zeroWord (word : String) (keep : Bool)
  deriving DecidableEq, Repr, Inhabited

/-- A number of a non-negative kind. -/
def clampTok0 : Tok → Tok
  | .num n => .num (max 0 n)
  | .dim n u => .dim (max 0 n) u
  | t => t

def roundTok (lo : Option Int) : Tok → Tok
  | .num n => .num (match lo with | some l => max l (Fix.round n) | none => Fix.round n)
  | t => t

def rangeTok (lo hi : Int) : Tok → Tok
  | .num n => .num (Fix.clamp lo hi n)
  | t => t

/-- The result of a component-wise interpolation, as the kind requires. -/
def finish : Kind → List Tok → List Tok
  | .nonNegative, ts => ts.map clampTok0
  | .integer, ts => ts.map (roundTok none)
  | .positiveInteger, ts => ts.map (roundTok (some one))
  | .unit, ts => ts.map (rangeTok 0 one)
  | .fontWeight, ts => ts.map (rangeTok one (Fix.ofInt 1000))
  | _, ts => ts

/-- A line width snapped (CSS Values 4 §5.4 "snap a length as a border width", with one
device pixel taken as one CSS pixel): a whole number of pixels stays; a width above 0 and
below 1px is 1px; any other is rounded down. A negative number is left as it is (the
kinds of these properties clamp at 0 first). -/
def snapWidth (n : Int) : Int :=
  if n ≤ 0 then n else if n < one then one else Fix.floor (n + slack)

/-- The px lengths of a value snapped as line widths: the computed value of a border,
outline or gap rule width. -/
def snapWidths (v : List Tok) : List Tok :=
  v.map fun t => match t with
    | .dim n u => if u == "px" then .dim (snapWidth n) u else t
    | t => t

/-! ### Sums of components (for `add` and `accumulate`, below) -/

def addColor (r1 g1 b1 a1 r2 g2 b2 a2 : Int) : Tok :=
  let a := Fix.clamp 0 one (a1 + a2)
  if a == 0 then .color 0 0 0 0 else
  let ch := fun (c1 c2 : Int) =>
    Fix.clamp 0 (Fix.ofInt 255) ((Fix.div (Fix.mul c1 a1 + Fix.mul c2 a2) a).getD 0)
  .color (ch r1 r2) (ch g1 g2) (ch b1 b2) a

/-- The sum of two components; none when they do not add. -/
def addTok : Tok → Tok → Option Tok
  | .num a, .num b => some (.num (a + b))
  | .dim a u, .dim b v =>
    if u == v then some (.dim (a + b) u)
    else if u == "px" && v == "%" then some (mkLp a b)
    else if u == "%" && v == "px" then some (mkLp b a)
    else none
  | .lp x y, .lp x' y' => some (mkLp (x + x') (y + y'))
  | .lp x y, .dim b v =>
    if v == "px" then some (mkLp (x + b) y) else if v == "%" then some (mkLp x (y + b)) else none
  | .dim a u, .lp x y =>
    if u == "px" then some (mkLp (a + x) y) else if u == "%" then some (mkLp x (a + y)) else none
  | .color r1 g1 b1 a1, .color r2 g2 b2 a2 => some (addColor r1 g1 b1 a1 r2 g2 b2 a2)
  | a, b => if a == b then some a else none

def addGo : List Tok → List Tok → List Tok → Option (List Tok)
  | [], [], acc => some acc.reverse
  | a :: as, b :: bs, acc =>
    match addTok a b with
    | some t => addGo as bs (t :: acc)
    | none => none
  | _, _, _ => none

def addList (a b : List Tok) : Option (List Tok) := addGo a b []

/-- As `lerpLoose`, for addition: a pair that does not add is the second value's. -/
def addLoose (a b : List Tok) : Option (List Tok) :=
  if a.length != b.length then none else
  (a.zip b).mapM fun (x, y) =>
    match x, y with
    | .op n, .op m => if n == m then some x else none
    | .op _, _ | _, .op _ => none
    | .close, .close => some x
    | .close, _ | _, .close => none
    | _, _ => match addTok x y with
      | some t => some t
      | none => some y

/-! ### Lists of functions and of shadows -/

/-- The top-level items of a value: a function with its arguments is one item, any other
token is one item. One pass. -/
def items (v : List Tok) : List (List Tok) := Id.run do
  let mut out : Array (List Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut depth : Nat := 0
  for t in v do
    match t with
    | .op _ =>
      depth := depth + 1
      cur := cur.push t
    | .close =>
      cur := cur.push t
      depth := depth - 1
      if depth == 0 then
        out := out.push cur.toList
        cur := #[]
    | _ => if depth == 0 then out := out.push [t] else cur := cur.push t
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

/-- The parts of a value between its top-level commas. -/
def commaItems (v : List Tok) : List (List Tok) := Id.run do
  let mut out : Array (List Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut depth : Nat := 0
  for t in v do
    match t with
    | .op _ =>
      depth := depth + 1
      cur := cur.push t
    | .close =>
      depth := depth - 1
      cur := cur.push t
    | .comma =>
      if depth == 0 then
        out := out.push cur.toList
        cur := #[]
      else cur := cur.push t
    | _ => cur := cur.push t
  if !cur.isEmpty then out := out.push cur.toList
  return out.toList

def isNone (v : List Tok) : Bool := v == [.ident "none"]

/-- The items joined again; `none` for no item. -/
def joinItems (xs : List (List Tok)) : List Tok := if xs.isEmpty then [.ident "none"] else xs.flatten

/-- The parts joined with commas; `none` for no part. -/
def joinCommas (xs : List (List Tok)) : List Tok :=
  match xs with
  | [] => [.ident "none"]
  | first :: rest => rest.foldl (fun acc x => acc ++ [.comma] ++ x) first

/-- The identity function of a transform function's name and arguments (CSS Transforms 1
§11: "the identity transform function" that pads a shorter list): 1 for a scale, 0
otherwise, the axis of `rotate3d` kept. None for `perspective`. -/
def transformIdentity (item : List Tok) : Option (List Tok) :=
  match item with
  | .op name :: rest =>
    if name == "matrix" then some (parse "matrix(1, 0, 0, 1, 0, 0)")
    else if name == "matrix3d" then some (parse "matrix3d(1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)")
    else if name == "perspective" then none
    else if name == "rotate3d" then
      some (.op name :: rest.map fun t => match t with
        | .dim _ u => .dim 0 u
        | t => t)
    else
      let unit : Int := if name.startsWith "scale" then one else 0
      some (.op name :: rest.map fun t => match t with
        | .num _ => .num unit
        | .dim _ u => .dim 0 u
        | .lp _ _ => .dim 0 "px"
        | t => t)
  | _ => none

/-- The neutral value of a filter function (Filter Effects 1 §2.1 "the initial value for
interpolation"): 1 for `brightness`, `contrast`, `opacity` and `saturate`; 0 for the
others; a transparent shadow of zero size for `drop-shadow`. None for a `url()`. -/
def filterNeutral (item : List Tok) : Option (List Tok) :=
  match item with
  | .op name :: rest =>
    if ["brightness", "contrast", "opacity", "saturate"].contains name then
      some (.op name :: rest.map fun t => match t with
        | .num _ => .num one
        | .dim _ u => if u == "%" then .dim (100 * one) u else .dim 0 u
        | t => t)
    else if ["blur", "grayscale", "invert", "sepia", "hue-rotate", "drop-shadow"].contains name then
      some (.op name :: rest.map fun t => match t with
        | .num _ => .num 0
        | .dim _ u => .dim 0 u
        | .color _ _ _ _ => .color 0 0 0 0
        | t => t)
    else none
  | _ => none

/-- The arguments of a `drop-shadow()` with the blur radius (the third length) not below
0 (Filter Effects 1 §2.1: a negative blur is invalid). One pass. -/
def dropShadowBlur (rest : List Tok) : List Tok := Id.run do
  let mut seen : Nat := 0
  let mut out : Array Tok := #[]
  for t in rest do
    match t with
    | .dim n u =>
      seen := seen + 1
      out := out.push (if seen == 3 then .dim (max 0 n) u else t)
    | _ => out := out.push t
  return out.toList

/-- Each `drop-shadow()` of a filter list that names no colour, with `currentcolor` as its
colour (Filter Effects 1 §2.1: the colour left out is the value of `color`). -/
def dropShadowColors (v : List Tok) : List Tok :=
  if !v.contains (.op "drop-shadow") then v else
  joinItems ((items v).map fun item =>
    match item with
    | .op "drop-shadow" :: rest =>
      let colour := rest.any fun t => match t with
        | .color _ _ _ _ => true
        | .ident "currentcolor" => true
        | .op _ => true
        | _ => false
      if colour then item else .op "drop-shadow" :: .ident "currentcolor" :: rest
    | _ => item)

/-- The numbers of a filter function in the range the function takes (Filter Effects 1
§2: no negative amount or radius; `grayscale`, `invert`, `opacity` and `sepia` at most 1). -/
def filterClamp (item : List Tok) : List Tok :=
  match item with
  | .op name :: rest =>
    if name == "hue-rotate" then item
    else if name == "drop-shadow" then .op name :: dropShadowBlur rest
    else
      let top : Option Int := if ["grayscale", "invert", "opacity", "sepia"].contains name then some one else none
      .op name :: rest.map fun t => match t with
        | .num n => .num (match top with | some hi => Fix.clamp 0 hi n | none => max 0 n)
        | .dim n u => .dim (max 0 n) u
        | t => t
  | _ => item

/-- A shadow with no effect, of the shape of `item`: zero lengths, a transparent colour. -/
def shadowNeutral (item : List Tok) : Option (List Tok) :=
  some (item.map fun t => match t with
    | .dim _ u => .dim 0 u
    | .lp _ _ => .dim 0 "px"
    | .color _ _ _ _ => .color 0 0 0 0
    | t => t)

/-- A shadow with its blur radius (the third length) not below 0. -/
def shadowClamp (item : List Tok) : List Tok := Id.run do
  let mut seen : Nat := 0
  let mut out : Array Tok := #[]
  for t in item do
    match t with
    | .dim n u =>
      seen := seen + 1
      out := out.push (if seen == 3 then .dim (max 0 n) u else t)
    | _ => out := out.push t
  return out.toList

/-- Two lists of items combined pairwise by `f`, the shorter padded with the `neutral` of
the other's item; none when a pair does not combine or an item has no neutral. -/
def zipItems (f : List Tok → List Tok → Option (List Tok)) (neutral : List Tok → Option (List Tok))
    (a b : List (List Tok)) : Option (List (List Tok)) := Id.run do
  let mut out : Array (List Tok) := #[]
  for i in [0:max a.length b.length] do
    let r := match a[i]?, b[i]? with
      | some x, some y => f x y
      | some x, none => (neutral x).bind fun z => f x z
      | none, some y => (neutral y).bind fun z => f z y
      | none, none => none
    match r with
    | some t => out := out.push t
    | none => return none
  return some out.toList

/-- The three components of `translate` (lengths or percentages) or `scale` (numbers):
`none` and missing components are `fill`. -/
def three (fill : Tok) (v : List Tok) : Option (Tok × Tok × Tok) :=
  if isNone v then some (fill, fill, fill)
  else match v with
    | [x] => some (x, fill, fill)
    | [x, y] => some (x, y, fill)
    | [x, y, z] => some (x, y, z)
    | _ => none

/-- A component of the shape of `t` with its number 0 (the missing component beside `t`). -/
def zeroLike (t : Tok) : Tok :=
  match t with
  | .dim _ u => .dim 0 u
  | _ => .dim 0 "px"

/-- `translate` as its three components, a missing one 0 in the unit of the other value's
component (so `none` beside `80%` is `0%`). -/
def translateOf (v other : List Tok) : Option (Tok × Tok × Tok) :=
  match three (.ident "") v, three (.ident "") other with
  | some (x, y, z), some (x', y', z') =>
    let fill := fun (t t' : Tok) => if t == .ident "" then zeroLike t' else t
    some (fill x x', fill y y', fill z z')
  | _, _ => none

/-- `translate` from its components (CSS Transforms 2 §5 serialization): a z of 0px is
left out, then a y of 0px. -/
def translateText (x y z : Tok) : List Tok :=
  if z == .dim 0 "px" then (if y == .dim 0 "px" then [x] else [x, y]) else [x, y, z]

/-- `scale` as three numbers: one number is both x and y; z is 1. -/
def scaleOf (v : List Tok) : Option (Int × Int × Int) :=
  if isNone v then some (one, one, one)
  else match v with
    | [.num x] => some (x, x, one)
    | [.num x, .num y] => some (x, y, one)
    | [.num x, .num y, .num z] => some (x, y, z)
    | _ => none

/-- `scale` from its numbers: a z of 1 is left out, then a y equal to x. -/
def scaleText (x y z : Int) : List Tok :=
  if z == one then (if x == y then [.num x] else [.num x, .num y]) else [.num x, .num y, .num z]

/-- A shadow with `n` lengths: the blur radius and the spread distance a shadow leaves out
are 0. -/
def shadowFull (n : Nat) (item : List Tok) : List Tok := Id.run do
  let dims := (item.filter fun t => match t with | .dim _ _ => true | .lp _ _ => true | _ => false).length
  if dims ≥ n || dims == 0 then return item
  -- after the last length
  let mut out : Array Tok := #[]
  let mut seen := 0
  for t in item do
    out := out.push t
    match t with
    | .dim _ _ | .lp _ _ =>
      seen := seen + 1
      if seen == dims then
        for _ in [0:n - dims] do out := out.push (.dim 0 "px")
    | _ => pure ()
  return out.toList

/-- A filter function with its argument: one left out is the function's default (Filter
Effects 1 §2: 1 for the amounts, 0px for `blur`, 0deg for `hue-rotate`). -/
def filterFull (item : List Tok) : List Tok :=
  match item with
  | [.op name, .close] =>
    if name == "blur" then [.op name, .dim 0 "px", .close]
    else if name == "hue-rotate" then [.op name, .dim 0 "deg", .close]
    else if ["brightness", "contrast", "opacity", "saturate", "grayscale", "invert", "sepia"].contains name then
      [.op name, .num one, .close]
    else item
  | .op "drop-shadow" :: rest =>
    -- a shadow's blur radius left out is 0px
    .op "drop-shadow" :: shadowFull 3 rest.dropLast ++ [.close]
  | _ => item

/-- `rotate` as an axis (tokens before the angle) and an angle in degrees; `none` is no
axis and 0. -/
def rotateOf (v : List Tok) : Option (List Tok × Int) :=
  if isNone v then some ([.ident "none"], 0)
  else match v.reverse with
    | .dim a "deg" :: axis => some (axis.reverse, a)
    | _ => none

def toFloat (n : Int) : Float := Float.ofInt n / Float.ofInt Fix.scale
def ofFloat (x : Float) : Int := if x.isFinite then (x * Float.ofInt Fix.scale).round.toInt64.toInt else 0

/-- The axis of a `rotate` value as a unit vector: three numbers, `x`, `y`, `z`, or no
axis (the z axis). None for a zero vector or other tokens. -/
def axisOf (axis : List Tok) : Option (Float × Float × Float) :=
  match axis with
  | [] | [.ident "none"] | [.ident "z"] => some (0, 0, 1)
  | [.ident "x"] => some (1, 0, 0)
  | [.ident "y"] => some (0, 1, 0)
  | [.num x, .num y, .num z] =>
    let (fx, fy, fz) := (toFloat x, toFloat y, toFloat z)
    let len := Float.sqrt (fx * fx + fy * fy + fz * fz)
    if len > 0 then some (fx / len, fy / len, fz / len) else none
  | _ => none

/-- `rotate` with a numeric axis, written with the axis as a unit vector. -/
def rotateText (x y z : Float) (deg : Int) : List Tok :=
  -- CSS Transforms 2 §5 serialization: about the z axis the value is the angle alone;
  -- about the x or the y axis the axis is its keyword
  let (ix, iy, iz) := (ofFloat x, ofFloat y, ofFloat z)
  if ix == 0 && iy == 0 && iz > 0 then [.dim deg "deg"]
  else if ix == one && iy == 0 && iz == 0 then [.ident "x", .dim deg "deg"]
  else if ix == 0 && iy == one && iz == 0 then [.ident "y", .dim deg "deg"]
  else [.num ix, .num iy, .num iz, .dim deg "deg"]

/-- Two rotations at progress `p` (CSS Transforms 2 §5.1; CSS Transforms 1 §11 for
`rotate3d`): about one axis, the angle moves; a rotation by 0 takes the other's axis; two
different axes turn through the shortest arc between the two rotations (spherical
interpolation of the quaternions). The axis of the result is as the values wrote it when
both wrote it the same way, else a unit vector. `Float` arithmetic: tested, not proved. -/
def lerpRotate (p : Int) (a b : List Tok) : Option (List Tok) :=
  match rotateOf a, rotateOf b with
  | some (ax, x), some (bx, y) =>
      match axisOf ax, axisOf bx with
      | some (x1, y1, z1), some (x2, y2, z2) =>
        let dot := x1 * x2 + y1 * y2 + z1 * z2
        if dot > 0.999999 || ax == [.ident "none"] || x == 0 then
          -- one direction, or nothing to turn from: the end's axis
          some (rotateText x2 y2 z2 (Fix.lerp x y p))
        else if bx == [.ident "none"] || y == 0 then some (rotateText x1 y1 z1 (Fix.lerp x y p))
        else
          let rad := fun (d : Int) => toFloat d * 3.141592653589793 / 180
          let h1 := rad x / 2
          let h2 := rad y / 2
          let (qx1, qy1, qz1, qw1) := (x1 * Float.sin h1, y1 * Float.sin h1, z1 * Float.sin h1, Float.cos h1)
          let (qx2, qy2, qz2, qw2) := (x2 * Float.sin h2, y2 * Float.sin h2, z2 * Float.sin h2, Float.cos h2)
          let d := qx1 * qx2 + qy1 * qy2 + qz1 * qz2 + qw1 * qw2
          let d := if d > 1 then 1 else if d < -1 then -1 else d
          let theta := Float.acos d
          let t := toFloat p
          let (w1, w2) := if Float.sin theta < 0.000001 && Float.sin theta > -0.000001 then (1 - t, t)
            else (Float.sin ((1 - t) * theta) / Float.sin theta, Float.sin (t * theta) / Float.sin theta)
          let (qx, qy, qz, qw) := (w1 * qx1 + w2 * qx2, w1 * qy1 + w2 * qy2, w1 * qz1 + w2 * qz2, w1 * qw1 + w2 * qw2)
          let qw := if qw > 1 then 1 else if qw < -1 then -1 else qw
          let angle := 2 * Float.acos qw
          let sn := Float.sqrt (1 - qw * qw)
          if sn < 0.000001 then some (rotateText 0 0 1 0)
          else some (rotateText (qx / sn) (qy / sn) (qz / sn) (ofFloat (angle * 180 / 3.141592653589793)))
      | _, _ => none
  | _, _ => none

/-- `font-style` as an oblique angle in degrees: `normal` is 0, `oblique` 14deg. -/
def obliqueOf (v : List Tok) : Option Int :=
  match v with
  | [.ident "normal"] => some 0
  | [.ident "oblique"] => some (Fix.ofInt 14)
  | [.ident "oblique", .dim a "deg"] => some a
  | _ => none

/-- Up to four values for the sides as four, and whether `fill` is there (CSS Backgrounds
3 §6.3: one value is all sides, two are top/bottom and left/right, three leave left as
right). -/
def sidesOf (v : List Tok) : Option (Tok × Tok × Tok × Tok × Bool) :=
  let fill := v.contains (.ident "fill")
  match v.filter (· != .ident "fill") with
  | [a] => some (a, a, a, a, fill)
  | [a, b] => some (a, b, a, b, fill)
  | [a, b, c] => some (a, b, c, b, fill)
  | [a, b, c, d] => some (a, b, c, d, fill)
  | _ => none

/-- Four sides in their shortest form, with `fill` after them. -/
def sidesText (t r b l : Tok) (fill : Bool) : List Tok :=
  let vs := if l == r then (if b == t then (if r == t then [t] else [t, r]) else [t, r, b]) else [t, r, b, l]
  if fill then vs ++ [.ident "fill"] else vs

/-- Two track lists of one shape at progress `p`: the parentheses, commas and slashes must
agree; a pair of sizes that does not combine is the nearer one (CSS Grid 2 §7.2.4). -/
def lerpLoose (p : Int) (a b : List Tok) : Option (List Tok) :=
  if a.length != b.length then none else
  (a.zip b).mapM fun (x, y) =>
    match x, y with
    | .op n, .op m => if n == m then some x else none
    | .op _, _ | _, .op _ => none
    | .close, .close => some x
    | .close, _ | _, .close => none
    | .comma, .comma => some x
    | .comma, _ | _, .comma => none
    | .slash, .slash => some x
    | .slash, _ | _, .slash => none
    | _, _ => match lerpTok p x y with
      | some t => some t
      | none => some (if p < half then x else y)

/-- The greatest common divisor, by Euclid's steps (at most `fuel`). -/
def gcdGo : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | fuel + 1, a, b => if b == 0 then a else gcdGo fuel b (a % b)

/-- A list repeated to `n` items. -/
def repeatTo {α : Type} (n : Nat) (xs : List α) : List α :=
  if xs.isEmpty then [] else (List.range n).filterMap fun i => xs[i % xs.length]?

/-- Two comma lists repeated to their least common multiple (at most 64 items). -/
def repeated (a b : List (List Tok)) : Option (List (List Tok) × List (List Tok)) :=
  if a.isEmpty || b.isEmpty then none
  else
    let n := a.length * b.length / gcdGo 64 a.length b.length
    if n > 64 then none else some (repeatTo n a, repeatTo n b)

/-- A ratio `w / h` (or one number, over 1) as a `Float`; none when it is not a ratio or
is not positive. -/
def ratioOf (v : List Tok) : Option Float :=
  let f := fun (n : Int) => Float.ofInt n / Float.ofInt Fix.scale
  match v with
  | [.num a] => if a > 0 then some (f a) else none
  | [.num a, .slash, .num b] => if a > 0 && b > 0 then some (f a / f b) else none
  | _ => none

/-! ### Path data (SVG 2 §9.3) inside `path()` -/

/-- The number of arguments of a path command (upper case). -/
def pathArgs : Char → Option Nat
  | 'M' | 'L' | 'T' => some 2
  | 'H' | 'V' => some 1
  | 'C' => some 6
  | 'S' | 'Q' => some 4
  | 'A' => some 7
  | 'Z' => some 0
  | _ => none

/-- Path data as commands with their numbers, each command absolute and in upper case
(SVG 2 §9.3: a relative command is its absolute one from the current point; numbers
after a command's own repeat it, a move then draws lines). None when the text is not path
data. One pass, no recursion. -/
def pathOf (text : String) : Option (List (Char × List Int)) := Id.run do
  let mut rest := text.toList
  let mut out : Array (Char × List Int) := #[]
  let mut cmd : Option Char := none
  let mut args : Array Int := #[]
  -- the current point and the start of the subpath
  let mut cx : Int := 0
  let mut cy : Int := 0
  let mut sx : Int := 0
  let mut sy : Int := 0
  let mut ok := true
  for _ in [0:text.length + 2] do
    -- a command with all its numbers is one segment
    match cmd with
    | some c =>
      let up := c.toUpper
      let rel := c.isLower
      match pathArgs up with
      | some n =>
        if args.size == n then
          let a := args.toList
          let seg : List Int := match up, a with
            | 'H', [x] => [if rel then x + cx else x]
            | 'V', [y] => [if rel then y + cy else y]
            | 'A', [rx, ry, rot, large, sweep, x, y] => [rx, ry, rot, large, sweep, if rel then x + cx else x, if rel then y + cy else y]
            | _, xs => (xs.zip (List.range xs.length)).map fun (v, i) => if rel then (if i % 2 == 0 then v + cx else v + cy) else v
          match up, seg.reverse with
          | 'H', x :: _ => cx := x
          | 'V', y :: _ => cy := y
          | 'Z', _ => cx := sx; cy := sy
          | _, y :: x :: _ => cx := x; cy := y
          | _, _ => pure ()
          if up == 'M' then sx := cx; sy := cy
          out := out.push (up, seg)
          args := #[]
          -- more numbers repeat the command; after a move they are lines
          cmd := if n == 0 then none else some (if c == 'M' then 'L' else if c == 'm' then 'l' else c)
      | none => ok := false
    | none => pure ()
    match rest with
    | [] => break
    | c :: r =>
      if c.isWhitespace || c == ',' then rest := r
      else if c.isAlpha && (pathArgs c.toUpper).isSome && c != 'e' && c != 'E' then
        if !args.isEmpty then ok := false
        cmd := some c
        rest := r
      else match takeNumber rest with
        | some (numText, r') =>
          match Fix.parse (String.ofList numText) with
          | some v => args := args.push v; rest := r'
          | none => ok := false; rest := r'
        | none => ok := false; rest := r
  if !ok || !args.isEmpty || out.isEmpty then return none
  return some out.toList

/-- The functions `path("…")` of a value with the path data as tokens: each command an
identifier, each number a number, so two paths of the same commands interpolate
component-wise (CSS Shapes 2 §3.1). A string that is not path data stays. -/
def expandPaths (v : List Tok) : List Tok := Id.run do
  let mut out : Array Tok := #[]
  let mut inPath := false
  for t in v do
    match t with
    | .op "path" => inPath := true; out := out.push t
    | .close => inPath := false; out := out.push t
    | .str body =>
      let inner := if body.length ≥ 2 then ((body.drop 1).toString.dropEnd 1).toString else body
      match (if inPath then pathOf inner else none) with
      | some segs =>
        for (c, args) in segs do
          out := out.push (.ident (String.singleton c))
          for a in args do out := out.push (.num a)
      | none => out := out.push t
    | _ => out := out.push t
  return out.toList

/-- The inverse of `expandPaths`: the command and number tokens of each `path(` as one
string, the two flags of an arc 0 or 1. -/
def collapsePaths (v : List Tok) : List Tok := Id.run do
  let mut out : Array Tok := #[]
  let mut inPath := false
  let mut text := ""
  let mut cmd := ""
  let mut k : Nat := 0
  for t in v do
    if inPath then
      match t with
      | .close =>
        if !text.isEmpty then out := out.push (.str ("\"" ++ text ++ "\""))
        out := out.push t
        inPath := false
        text := ""
      | .ident c =>
        if c.length == 1 && (c.toList.head?.bind pathArgs).isSome then
          text := (if text.isEmpty then "" else text ++ " ") ++ c
          cmd := c
          k := 0
        else out := out.push t
      | .num n =>
        if cmd.isEmpty then out := out.push t
        else
          -- a flag of an arc is set when its number is above 0 (SVG 2 §9.5.1: the flags
          -- interpolate as numbers, and a number that is not 0 is a set flag; below 0 it is unset)
          let n := if cmd == "A" && (k == 3 || k == 4) then (if n ≤ 0 then 0 else one) else n
          text := text ++ " " ++ Fix.formatCss n
          k := k + 1
      | _ => out := out.push t
    else
      out := out.push t
      if t == .op "path" then
        inPath := true
        text := ""
        cmd := ""
  return out.toList

/-! ### `inset()`, `rect()` and `xywh()` as one form (CSS Shapes 1 §3.1) -/

/-- 100% minus a length-percentage. -/
def fromFull (t : Tok) : Option Tok :=
  match t with
  | .dim n "%" => some (.dim (100 * one - n) "%")
  | .dim n "px" => some (if n == 0 then .dim (100 * one) "%" else .lp (-n) (100 * one))
  | .lp px pct => some (.lp (-px) (100 * one - pct))
  | _ => none

/-- The sum of two length-percentages. -/
def lpSum (a b : Tok) : Option Tok := addTok a b

/-- `inset()`, `rect()` or `xywh()` as `inset()` with four sides and its `round` part: the
function's tokens, canonical. `rect(top right bottom left)` gives the right and bottom
edges from the top left corner (`auto` is the edge itself); `xywh(x y w h)` gives a corner
and a size. None for another function or a form not read. -/
def insetOf (item : List Tok) : Option (List Tok) :=
  match item with
  | .op name :: rest =>
    let body := rest.dropLast
    let sides := body.takeWhile (· != .ident "round")
    let round := body.drop sides.length
    let round := if round.isEmpty then [.ident "round", .dim 0 "px"] else round
    let pack := fun (t r b l : Tok) => some (.op "inset" :: t :: r :: b :: l :: round ++ [.close])
    if name == "inset" then
      match sidesOf sides with
      | some (t, r, b, l, _) => pack t r b l
      | none => none
    else if name == "rect" then
      match sides with
      | [t, r, b, l] =>
        let zero := Tok.dim 0 "%"
        let t' := if t == .ident "auto" then zero else t
        let l' := if l == .ident "auto" then zero else l
        match (if r == .ident "auto" then some zero else fromFull r), (if b == .ident "auto" then some zero else fromFull b) with
        | some r', some b' => pack t' r' b' l'
        | _, _ => none
      | _ => none
    else if name == "xywh" then
      match sides with
      | [x, y, w, h] =>
        match (lpSum x w).bind fromFull, (lpSum y h).bind fromFull with
        | some r', some b' => pack y r' b' x
        | _, _ => none
      | _ => none
    else none
  | _ => none

/-- An `inset()` of `insetOf`'s form in its shortest form: equal sides once, a `round 0px`
left out. -/
def insetText (item : List Tok) : List Tok :=
  match item with
  | .op "inset" :: t :: r :: b :: l :: rest =>
    let round := rest.dropLast
    let round := if round == [.ident "round", .dim 0 "px"] then [] else round
    .op "inset" :: sidesText t r b l false ++ round ++ [.close]
  | _ => item

/-- The shapes of a value with each `inset()`, `rect()` and `xywh()` as a canonical
`inset()`; whether one was there. -/
def insetForm (v : List Tok) : List Tok × Bool :=
  let its := items v
  let conv := its.map fun it => (insetOf it).getD it
  (conv.flatten, its.any fun it => (insetOf it).isSome)

/-- An integer `repeat(n, …)` of a comma list as its items, `n` times (at most 64 items);
none for `repeat(auto, …)`. -/
def expandRepeats (v : List Tok) : Option (List (List Tok)) :=
  (commaItems v).foldlM (fun acc item =>
    match item with
    | .op "repeat" :: .ident n :: .comma :: rest =>
      match n.toNat? with
      | some k =>
        let inner := commaItems rest.dropLast
        if k * inner.length > 64 then none else some (acc ++ (List.replicate k inner).flatten)
      | none => none
    | _ => some (acc ++ [item])) []

/-- `offset-rotate` as whether it follows the path and its angle in degrees. -/
def offsetRotateOf (v : List Tok) : Option (Bool × Int) :=
  match v with
  | [.ident "auto"] => some (true, 0)
  | [.ident "reverse"] => some (true, Fix.ofInt 180)
  | [.ident "auto", .dim a "deg"] | [.dim a "deg", .ident "auto"] => some (true, a)
  | [.ident "reverse", .dim a "deg"] | [.dim a "deg", .ident "reverse"] => some (true, a + Fix.ofInt 180)
  | [.dim a "deg"] => some (false, a)
  | _ => none

def offsetRotateText (auto : Bool) (a : Int) : List Tok :=
  if auto then [.ident "auto", .dim a "deg"] else [.dim a "deg"]

/-- A track list without its line names (`[a b]`), and the names with the number of
tokens before each. One pass. -/
def stripLineNames (v : List Tok) : List Tok × List (Nat × List Tok) := Id.run do
  let mut tracks : Array Tok := #[]
  let mut names : Array (Nat × List Tok) := #[]
  let mut cur : Array Tok := #[]
  let mut inside := false
  for t in v do
    if inside then
      cur := cur.push t
      if t == .ident "]" then
        names := names.push (tracks.size, cur.toList)
        cur := #[]
        inside := false
    else if t == .ident "[" then
      inside := true
      cur := #[t]
    else tracks := tracks.push t
  return (tracks.toList, names.toList)

/-- The inverse of `stripLineNames`. -/
def withLineNames (tracks : List Tok) (names : List (Nat × List Tok)) : List Tok := Id.run do
  let mut out : Array Tok := #[]
  let arr := tracks.toArray
  for i in [0:arr.size + 1] do
    for (k, group) in names do
      if k == i then out := out ++ group.toArray
    match arr[i]? with
    | some t => out := out.push t
    | none => pure ()
  return out.toList

/-- The tokens that follow each `repeat(`: the counts of a track list. -/
def repeatHeads (v : List Tok) : List Tok :=
  (v.zip (v.drop 1)).filterMap fun (x, y) => if x == .op "repeat" then some y else none

/-! ### Transform lists (CSS Transforms 1 §11 to §13, CSS Transforms 2 §8 and §9)

Two lists pair up function by function while the functions share a primitive (the
`translate`, `scale`, `rotate` or `skew` family, a matrix, a perspective); from the first
pair that does not, the rest of each list is one matrix and the two matrices interpolate by
decomposition (`Matrix.blend`). -/

/-- A transform function read from its tokens: lengths as tokens (px, a percentage, or
both), numbers and angles (in degrees) as `Fix` integers. `three` says the function was
one of three dimensions. -/
inductive TF where
  | translate (x y z : Tok) (three : Bool)
  | scale (x y z : Int) (three : Bool)
  /-- The axis as written and the angle. -/
  | rotate (x y z : Int) (deg : Int) (three : Bool)
  /-- The two angles, and which function it was: 0 `skew()`, 1 `skewX()`, 2 `skewY()`.
  The three share no primitive (CSS Transforms 1 §13): a pair of two of them goes to the
  matrix path. -/
  | skew (ax ay : Int) (form : Nat)
  /-- 6 numbers (`matrix()`) or 16 (`matrix3d()`). -/
  | matrix (m : List Int)
  /-- The distance in px; none for `perspective(none)`. -/
  | perspective (d : Option Int)
  deriving DecidableEq, Repr, Inhabited

/-- An angle in degrees. -/
def angleDeg : Tok → Option Int
  | .dim n u =>
    if u == "deg" then some n
    else if u == "rad" then some (ofFloat (toFloat n * 180 / Matrix.pi))
    else if u == "grad" then some (Fix.roundDiv (n * 9) 10)
    else if u == "turn" then some (n * 360)
    else none
  | .num n => if n == 0 then some 0 else none
  | _ => none

def isLength : Tok → Bool
  | .dim _ u => u == "px" || u == "%"
  | .lp _ _ => true
  | _ => false

/-- A number, or a percentage as a number (`scale(50%)`). -/
def numberOf : Tok → Option Int
  | .num n => some n
  | .dim n u => if u == "%" then some (Fix.roundDiv n 100) else none
  | _ => none

/-- The identity matrix as the 16 numbers of `matrix3d()`. -/
def identity16 : List Int := [one, 0, 0, 0, 0, one, 0, 0, 0, 0, one, 0, 0, 0, 0, one]

/-- One transform function from the tokens of `name(arguments)`; none for anything else. -/
def readFn (item : List Tok) : Option TF :=
  match item with
  | .op name :: rest =>
    if rest.getLast? != some .close then none else
    let args := rest.dropLast.filter (· != .comma)
    let zero : Tok := .dim 0 "px"
    let lengths := args.all isLength
    let numbers := args.mapM numberOf
    let angles := args.mapM angleDeg
    if name == "translate" then
      match args with
      | [x] => if lengths then some (.translate x zero zero false) else none
      | [x, y] => if lengths then some (.translate x y zero false) else none
      | _ => none
    else if name == "translatex" then
      match args with
      | [x] => if lengths then some (.translate x zero zero false) else none
      | _ => none
    else if name == "translatey" then
      match args with
      | [y] => if lengths then some (.translate zero y zero false) else none
      | _ => none
    else if name == "translatez" then
      match args with
      | [z] => if lengths then some (.translate zero zero z true) else none
      | _ => none
    else if name == "translate3d" then
      match args with
      | [x, y, z] => if lengths then some (.translate x y z true) else none
      | _ => none
    else if name == "scale" then
      match numbers with
      | some [x] => some (.scale x x one false)
      | some [x, y] => some (.scale x y one false)
      | _ => none
    else if name == "scalex" then
      match numbers with
      | some [x] => some (.scale x one one false)
      | _ => none
    else if name == "scaley" then
      match numbers with
      | some [y] => some (.scale one y one false)
      | _ => none
    else if name == "scalez" then
      match numbers with
      | some [z] => some (.scale one one z true)
      | _ => none
    else if name == "scale3d" then
      match numbers with
      | some [x, y, z] => some (.scale x y z true)
      | _ => none
    else if name == "rotate" || name == "rotatez" then
      match angles with
      | some [a] => some (.rotate 0 0 one a false)
      | _ => none
    else if name == "rotatex" then
      match angles with
      | some [a] => some (.rotate one 0 0 a true)
      | _ => none
    else if name == "rotatey" then
      match angles with
      | some [a] => some (.rotate 0 one 0 a true)
      | _ => none
    else if name == "rotate3d" then
      match args with
      | [.num x, .num y, .num z, a] => (angleDeg a).map fun d => .rotate x y z d true
      | _ => none
    else if name == "skew" then
      match angles with
      | some [a] => some (.skew a 0 0)
      | some [a, b] => some (.skew a b 0)
      | _ => none
    else if name == "skewx" then
      match angles with
      | some [a] => some (.skew a 0 1)
      | _ => none
    else if name == "skewy" then
      match angles with
      | some [a] => some (.skew 0 a 2)
      | _ => none
    else if name == "matrix" then
      match numbers with
      | some m => if m.length == 6 then some (.matrix m) else none
      | none => none
    else if name == "matrix3d" then
      match numbers with
      | some m => if m.length == 16 then some (.matrix m) else none
      | none => none
    else if name == "perspective" then
      match args with
      | [.ident "none"] => some (.perspective none)
      | [.dim d "px"] => some (.perspective (some d))
      | _ => none
    else none
  | _ => none

/-- The functions of a transform list; `none` is the empty list. None when a function is
not one this reads. -/
def readTransforms (v : List Tok) : Option (List TF) :=
  if isNone v then some [] else (items v).mapM readFn

def fnTokens (name : String) (args : List Tok) : List Tok :=
  .op name :: args.intersperse .comma ++ [.close]

/-- A function as tokens, in the primitive's form. -/
def writeFn : TF → List Tok
  | .translate x y z three => if three then fnTokens "translate3d" [x, y, z] else fnTokens "translate" [x, y]
  | .scale x y z three =>
    if three then fnTokens "scale3d" [.num x, .num y, .num z] else fnTokens "scale" [.num x, .num y]
  | .rotate x y z d three =>
    if three then fnTokens "rotate3d" [.num x, .num y, .num z, .dim d "deg"] else fnTokens "rotate" [.dim d "deg"]
  | .skew ax ay form =>
    if form == 1 then fnTokens "skewx" [.dim ax "deg"]
    else if form == 2 then fnTokens "skewy" [.dim ay "deg"]
    else fnTokens "skew" [.dim ax "deg", .dim ay "deg"]
  | .matrix m => fnTokens (if m.length == 6 then "matrix" else "matrix3d") (m.map .num)
  | .perspective none => fnTokens "perspective" [.ident "none"]
  | .perspective (some d) => fnTokens "perspective" [.dim d "px"]

def writeTransforms (fs : List TF) : List Tok := joinItems (fs.map writeFn)

/-- A length in px: a percentage is of `basis` (the side of the reference box), when the
caller has one. -/
def lengthPx (basis : Option Float) : Tok → Option Float
  | .dim n u =>
    if u == "px" then some (toFloat n)
    else if u == "%" then (if n == 0 then some 0 else basis.map fun b => toFloat n * b / 100)
    else none
  | .lp px pct => if pct == 0 then some (toFloat px) else basis.map fun b => toFloat px + toFloat pct * b / 100
  | _ => none

/-- The matrix of a function (CSS Transforms 1 §13, CSS Transforms 2 §8); `box` is the
reference box's width and height for percentages. None for a percentage with no box. -/
def fnMatrix (box : Option (Float × Float)) : TF → Option Matrix.M
  | .translate x y z _ =>
    match lengthPx (box.map (·.1)) x, lengthPx (box.map (·.2)) y, lengthPx none z with
    | some a, some b, some c => some (Matrix.translate a b c)
    | _, _, _ => none
  | .scale x y z _ => some (Matrix.scale (toFloat x) (toFloat y) (toFloat z))
  | .rotate x y z d _ => some (Matrix.rotate (toFloat x) (toFloat y) (toFloat z) (toFloat d))
  | .skew ax ay _ => some (Matrix.skew (toFloat ax) (toFloat ay))
  | .matrix m =>
    match m with
    | [a, b, c, d, e, f] => some (Matrix.ofAffine (toFloat a) (toFloat b) (toFloat c) (toFloat d) (toFloat e) (toFloat f))
    | _ => if m.length == 16 then some (m.map toFloat).toArray else none
  | .perspective none => some Matrix.identity
  -- CSS Transforms 2 §8: a distance below 1px is 1px
  | .perspective (some d) => some (Matrix.perspective (toFloat (max d one)))

/-- The product of a list's matrices. -/
def listMatrix (box : Option (Float × Float)) (fs : List TF) : Option Matrix.M :=
  fs.foldl (fun acc f => match acc, fnMatrix box f with
    | some m, some n => some (Matrix.mul m n)
    | _, _ => none) (some Matrix.identity)

/-- A matrix as a function: `matrix()` when it is one of two dimensions. -/
def matrixFn (m : Matrix.M) : TF :=
  if Matrix.is2D m then
    .matrix ([m.at 0 0, m.at 0 1, m.at 1 0, m.at 1 1, m.at 3 0, m.at 3 1].map ofFloat)
  else .matrix ((List.range 16).map fun i => ofFloat (m.getD i 0))

/-- The function that does nothing, of the family of `f` (CSS Transforms 1 §11: what a
shorter list is padded with). -/
def identityFn : TF → TF
  | .translate x y z t => .translate (zeroLike x) (zeroLike y) (zeroLike z) t
  | .scale _ _ _ t => .scale one one one t
  | .rotate x y z _ t => .rotate x y z 0 t
  | .skew _ _ form => .skew 0 0 form
  | .matrix m => .matrix (if m.length == 6 then [one, 0, 0, one, 0, 0] else identity16)
  | .perspective _ => .perspective none

/-- Two functions share a primitive. -/
def samePrimitive : TF → TF → Bool
  | .translate .., .translate .. => true
  | .scale .., .scale .. => true
  | .rotate .., .rotate .. => true
  | .skew _ _ f, .skew _ _ g => f == g
  | .matrix _, .matrix _ => true
  | .perspective _, .perspective _ => true
  | _, _ => false

/-- Two axes point one way. -/
def sameDirection (x y z x' y' z' : Int) : Bool :=
  let (a, b, c, a', b', c') := (toFloat x, toFloat y, toFloat z, toFloat x', toFloat y', toFloat z')
  let (n, n') := (Float.sqrt (a * a + b * b + c * c), Float.sqrt (a' * a' + b' * b' + c' * c'))
  n > 0 && n' > 0 && (a * a' + b * b' + c * c') / (n * n') > 0.999999

/-- Two functions of one primitive at progress `p` (CSS Transforms 2 §9 "interpolation
of primitives and derived transform functions"): translations, scales and skews by
component; rotations about one direction by the angle (a rotation by 0 takes the other's
axis), about two directions as matrices; matrices by decomposition; perspectives by the
reciprocal of the distance (the entry of the matrix). None when a matrix has no
decomposition or two lengths do not combine. -/
def lerpFn (p : Int) : TF → TF → Option TF
  | .translate x y z t, .translate x' y' z' t' =>
    match lerpTok p x x', lerpTok p y y', lerpTok p z z' with
    | some rx, some ry, some rz => some (.translate rx ry rz (t || t'))
    | _, _, _ => none
  | .scale x y z t, .scale x' y' z' t' =>
    some (.scale (Fix.lerp x x' p) (Fix.lerp y y' p) (Fix.lerp z z' p) (t || t'))
  | .rotate x y z d t, .rotate x' y' z' d' t' =>
    if d == 0 then some (.rotate x' y' z' (Fix.lerp d d' p) t')
    else if d' == 0 || sameDirection x y z x' y' z' then some (.rotate x y z (Fix.lerp d d' p) t)
    else
      (Matrix.blend (Matrix.rotate (toFloat x) (toFloat y) (toFloat z) (toFloat d))
        (Matrix.rotate (toFloat x') (toFloat y') (toFloat z') (toFloat d')) (toFloat p)).map matrixFn
  | .skew a b f, .skew a' b' _ => some (.skew (Fix.lerp a a' p) (Fix.lerp b b' p) f)
  | .matrix m, .matrix m' =>
    match fnMatrix none (.matrix m), fnMatrix none (.matrix m') with
    | some x, some y => (Matrix.blend x y (toFloat p)).map matrixFn
    | _, _ => none
  | .perspective d, .perspective d' =>
    let inv := fun (d : Option Int) => match d with
      | some d => 1 / toFloat (max d one)
      | none => 0
    let r := Matrix.lerp (inv d) (inv d') (toFloat p)
    some (.perspective (if r > 0 then some (ofFloat (1 / r)) else none))
  | _, _ => none

/-- Two lists of functions at progress `p` (CSS Transforms 2 §9 "interpolation of
transforms"): the shorter list padded with identity functions; pairs of one primitive by
`lerpFn`; from the first pair of two primitives, the rest of each list as one matrix. -/
def lerpTransforms (p : Int) (a b : List TF) : Option (List TF) := Id.run do
  let a' := a ++ (b.drop a.length).map identityFn
  let b' := b ++ (a.drop b.length).map identityFn
  let mut out : Array TF := #[]
  for i in [0:a'.length] do
    match a'[i]?, b'[i]? with
    | some x, some y =>
      if samePrimitive x y then
        match lerpFn p x y with
        | some r => out := out.push r
        | none => return none
      else
        match listMatrix none (a'.drop i), listMatrix none (b'.drop i) with
        | some ma, some mb =>
          match Matrix.blend ma mb (toFloat p) with
          | some m => return some (out.toList ++ [matrixFn m])
          | none => return none
        | _, _ => return none
    | _, _ => return none
  return some out.toList

/-- `b` accumulated onto `a`, two functions of one primitive (Web Animations 1 §5.2;
CSS Transforms 2 §9): translations and skews add, scales add about 1, rotations about one
direction add their angles, perspectives add the reciprocals of their distances, matrices
accumulate by decomposition. -/
def accFn : TF → TF → Option TF
  | .translate x y z t, .translate x' y' z' t' =>
    match addTok x x', addTok y y', addTok z z' with
    | some rx, some ry, some rz => some (.translate rx ry rz (t || t'))
    | _, _, _ => none
  | .scale x y z t, .scale x' y' z' t' => some (.scale (x + x' - one) (y + y' - one) (z + z' - one) (t || t'))
  | .rotate x y z d t, .rotate x' y' z' d' t' =>
    if d == 0 then some (.rotate x' y' z' (d + d') t')
    else if d' == 0 || sameDirection x y z x' y' z' then some (.rotate x y z (d + d') t)
    else
      (Matrix.accumulate (Matrix.rotate (toFloat x) (toFloat y) (toFloat z) (toFloat d))
        (Matrix.rotate (toFloat x') (toFloat y') (toFloat z') (toFloat d'))).map matrixFn
  | .skew a b f, .skew a' b' _ => some (.skew (a + a') (b + b') f)
  | .matrix m, .matrix m' =>
    match fnMatrix none (.matrix m), fnMatrix none (.matrix m') with
    | some x, some y => (Matrix.accumulate x y).map matrixFn
    | _, _ => none
  | .perspective d, .perspective d' =>
    let inv := fun (d : Option Int) => match d with
      | some d => 1 / toFloat (max d one)
      | none => 0
    let r := inv d + inv d'
    some (.perspective (if r > 0 then some (ofFloat (1 / r)) else none))
  | _, _ => none

/-- Two lists accumulated: paired as in `lerpTransforms`. -/
def accTransforms (a b : List TF) : Option (List TF) := Id.run do
  let a' := a ++ (b.drop a.length).map identityFn
  let b' := b ++ (a.drop b.length).map identityFn
  let mut out : Array TF := #[]
  for i in [0:a'.length] do
    match a'[i]?, b'[i]? with
    | some x, some y =>
      if samePrimitive x y then
        match accFn x y with
        | some r => out := out.push r
        | none => return none
      else
        match listMatrix none (a'.drop i), listMatrix none (b'.drop i) with
        | some ma, some mb =>
          match Matrix.accumulate ma mb with
          | some m => return some (out.toList ++ [matrixFn m])
          | none => return none
        | _, _ => return none
    | _, _ => return none
  return some out.toList

/-- The names of the functions of a list. -/
def fnNames (v : List Tok) : List String :=
  (items v).filterMap fun it => match it with
    | .op name :: _ => some name
    | _ => none

/-- The functions that do not interpolate argument by argument. -/
def byMatrix (name : String) : Bool :=
  name == "matrix" || name == "matrix3d" || name == "perspective" || name == "rotate3d"

/-- A transform list at progress `p` between two: lists whose functions have the same
names and argument counts, none of them a matrix, a perspective or a `rotate3d()`, move
argument by argument and keep their names; any others go through `lerpTransforms`. -/
def lerpTransformList (p : Int) (a b : Value) : Option Value :=
  let plain := zipItems (lerpList p) transformIdentity (if isNone a then [] else items a) (if isNone b then [] else items b)
  let kept : Option Value := match plain with
    | some r => if (fnNames a ++ fnNames b).any byMatrix then none else some (joinItems r)
    | none => none
  match kept with
  | some r => some r
  | none =>
    match readTransforms a, readTransforms b with
    | some x, some y => (lerpTransforms p x y).map writeTransforms
    | _, _ => none

/-- The resolved value of `transform` (CSS Transforms 1 §15 with CSSOM §9.1 "resolved
value"): the list as one `matrix()` or `matrix3d()`; `box` is the reference box for
percentages. None for `none`, for a list this does not read and for a percentage with no
box: the computed value then stands. -/
def resolvedTransform (box : Option (Float × Float)) (v : Value) : Option Value :=
  if isNone v then none
  else match readTransforms v with
    | some fs => (listMatrix box fs).map fun m => writeFn (matrixFn m)
    | none => none

/-- The text of a value with numbers to six significant digits (`toText` writes six
decimal places): for matrices, whose small entries matter. -/
def toTextPrecise (v : Value) : String :=
  " ".intercalate ((toText (v.map fun t => match t with
    | .num n => .ident ("\x01" ++ Fix.formatSig 6 n)
    | t => t)).splitOn " \x01") |>.replace "\x01" ""

/-- The text `getComputedStyle` gives for the computed text of `transform`: one matrix
(`resolvedTransform`), or the text as it is. -/
def resolvedTransformText (text : String) (box : Option (Float × Float) := none) : String :=
  if text == "none" || text.isEmpty then text
  else match resolvedTransform box (parse text) with
    | some v => toTextPrecise v
    | none => text

/-- The text `getComputedStyle` gives for the computed text of `transform-origin` or
`perspective-origin` (CSSOM §9.1: the used value): the percentages of the first and the
second component are of the width and the height of the reference box. The text as it
is with no box, or for components that are not lengths. -/
def resolvedOriginText (text : String) (box : Option (Float × Float)) : String :=
  match box with
  | none => text
  | some (w, h) =>
    let v := parse text
    if v.length > 3 then text else
    let r := (v.zip [some w, some h, none]).mapM fun ((t, basis) : Tok × Option Float) => match t with
      | .dim n u =>
        if u == "px" then some t
        else if u == "%" then basis.map fun b => Tok.dim (ofFloat (toFloat n * b / 100)) "px"
        else none
      | .lp px pct => basis.map fun b => Tok.dim (ofFloat (toFloat px + toFloat pct * b / 100)) "px"
      | _ => none
    match r with
    | some r => toText r
    | none => text

#guard resolvedOriginText "50% 50%" (some (50, 80)) == "25px 40px"
#guard resolvedOriginText "calc(-25% + 30px) 10px 5px" (some (50, 80)) == "17.5px 10px 5px"
#guard resolvedOriginText "50% 50%" none == "50% 50%" && resolvedOriginText "left top" (some (50, 80)) == "left top"

/-! ### Colours outside legacy sRGB (CSS Color 4 §12.1)

Two colours interpolate in sRGB when both are legacy sRGB colours (`rgb()`, names, hex:
the `color` token), and in Oklab when one of them is not. The colour function read here is
`color(srgb r g b [/ a])`; the result is written `oklab(L a b)`. `Float` arithmetic
(the transfer function and a cube root): tested, not proved. Colours are not
premultiplied on this path (exact when the two alphas are equal). -/

/-- A value has a colour that is not a legacy sRGB one. -/
def modernColor (v : List Tok) : Bool := v.contains (.op "color") || v.contains (.op "oklab")

/-- sRGB components in [0, 1] as Oklab (CSS Color 4 §10.5 with §10.2: gamma decoded, then
the matrices from linear sRGB to LMS and from the cube roots to Lab). -/
def oklabOfSrgb (r g b : Float) : Float × Float × Float :=
  let lin := fun (c : Float) =>
    let a := c.abs
    let v := if a ≤ 0.04045 then a / 12.92 else Float.pow ((a + 0.055) / 1.055) 2.4
    if c < 0 then -v else v
  let (r, g, b) := (lin r, lin g, lin b)
  let l := Float.cbrt (0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b)
  let m := Float.cbrt (0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b)
  let s := Float.cbrt (0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b)
  (0.2104542553 * l + 0.7936177850 * m - 0.0040720468 * s,
   1.9779984951 * l - 2.4285922050 * m + 0.4505937099 * s,
   0.0259040371 * l + 0.7827717662 * m - 0.8086757660 * s)

/-- `oklab(L a b / alpha)` as tokens, always with its alpha (so two colours have one shape). -/
def oklabTokens (l a b alpha : Int) : List Tok :=
  [.op "oklab", .num l, .num a, .num b, .slash, .num alpha, .close]

/-- Every colour of a value as `oklab(L a b / alpha)`: legacy colours, `color(srgb …)`,
and `oklab()` itself with its alpha written. Other tokens stay. One pass. -/
def toOklab (v : List Tok) : List Tok := Id.run do
  let srgb := fun (r g b : Float) (alpha : Int) =>
    let (l, a, b') := oklabOfSrgb r g b
    oklabTokens (ofFloat l) (ofFloat a) (ofFloat b') alpha
  let mut rest := v
  let mut out : Array Tok := #[]
  for _ in [0:v.length + 1] do
    match rest with
    | [] => break
    | .color r g b a :: more =>
      out := out ++ (srgb (toFloat r / 255) (toFloat g / 255) (toFloat b / 255) a).toArray
      rest := more
    | .op "color" :: .ident "srgb" :: .num r :: .num g :: .num b :: .close :: more =>
      out := out ++ (srgb (toFloat r) (toFloat g) (toFloat b) one).toArray
      rest := more
    | .op "color" :: .ident "srgb" :: .num r :: .num g :: .num b :: .slash :: .num a :: .close :: more =>
      out := out ++ (srgb (toFloat r) (toFloat g) (toFloat b) a).toArray
      rest := more
    | .op "oklab" :: .num l :: .num a :: .num b :: .close :: more =>
      out := out ++ (oklabTokens l a b one).toArray
      rest := more
    | t :: more =>
      out := out.push t
      rest := more
  return out.toList

/-- The `oklab()` colours of a result in range and in their shortest form: the lightness
in [0, 1], the alpha in [0, 1] and left out when it is 1. One pass. -/
def fromOklab (v : List Tok) : List Tok := Id.run do
  let mut rest := v
  let mut out : Array Tok := #[]
  for _ in [0:v.length + 1] do
    match rest with
    | [] => break
    | .op "oklab" :: .num l :: .num a :: .num b :: .slash :: .num alpha :: .close :: more =>
      let l := Fix.clamp 0 one l
      let alpha := Fix.clamp 0 one alpha
      out := out ++ (if alpha == one then #[Tok.op "oklab", .num l, .num a, .num b, .close]
        else #[Tok.op "oklab", .num l, .num a, .num b, .slash, .num alpha, .close])
      rest := more
    | t :: more =>
      out := out.push t
      rest := more
  return out.toList

/-! ### Corner shapes (CSS Borders 4 §4.2 and its interpolation)

A corner shape is a superellipse parameter: `round` 1, `bevel` 0, `scoop` -1, `squircle` 2,
`square` ∞, `notch` -∞. Two shapes interpolate by their normalized half corner, a number
in [0, 1]. `Float` arithmetic (powers and logarithms of 2): tested, not proved. -/

/-- The superellipse parameter of a corner shape value; none for another value. -/
def cornerParam (v : List Tok) : Option Float :=
  match v with
  | [.ident "round"] => some 1
  | [.ident "bevel"] => some 0
  | [.ident "scoop"] => some (-1)
  | [.ident "squircle"] => some 2
  | [.ident "square"] => some (1 / 0)
  | [.ident "notch"] => some (-1 / 0)
  | [.op "superellipse", .num k, .close] => some (toFloat k)
  | [.op "superellipse", .ident "infinity", .close] => some (1 / 0)
  | [.op "superellipse", .ident "-infinity", .close] => some (-1 / 0)
  | _ => none

/-- The normalized half corner of a parameter: -∞ is 0 and ∞ is 1; else, with
k = 0.5^|s|, the number 0.5^k for s ≥ 0 and 1 - 0.5^k below 0. -/
def cornerHalf (s : Float) : Float :=
  if s.isInf then (if s > 0 then 1 else 0)
  else
    let c := Float.pow 0.5 (Float.pow 0.5 s.abs)
    if s < 0 then 1 - c else c

/-- The parameter of a half corner (the inverse of `cornerHalf`): 0 or less is -∞, 1 or
more is ∞. -/
def cornerOfHalf (x : Float) : Float :=
  if x ≤ 0 then -1 / 0 else if x ≥ 1 then 1 / 0
  else if x ≥ 0.5 then -(Float.log2 (-(Float.log2 x)))
  else Float.log2 (-(Float.log2 (1 - x)))

/-- A parameter as a corner shape: its keyword when it has one, else `superellipse()`. -/
def cornerTokens (s : Float) : List Tok :=
  if s.isNaN then [.ident "round"]
  else if s.isInf then [.ident (if s > 0 then "square" else "notch")]
  else
    let k := ofFloat s
    if k == one then [.ident "round"] else if k == 0 then [.ident "bevel"]
    else if k == -one then [.ident "scoop"] else if k == 2 * one then [.ident "squircle"]
    else [.op "superellipse", .num k, .close]

/-- Two corner shapes at progress `p`: the half corners interpolate, the result is the
shape of that half corner. -/
def lerpCorner (p : Int) (a b : List Tok) : Option (List Tok) :=
  match cornerParam a, cornerParam b with
  | some x, some y =>
    let hx := cornerHalf x
    let hy := cornerHalf y
    some (cornerTokens (cornerOfHalf (hx + (hy - hx) * toFloat p)))
  | _, _ => none

/-- The radii of basic shapes not below 0 (CSS Shapes 1 §3.1: a negative radius is
invalid): the radius of `circle()`, the two of `ellipse()` (up to `at`), and the corner
radii after `round` of `inset()` and `polygon()` (up to the comma or the end). One pass. -/
def clampShapeRadii (v : List Tok) : List Tok := Id.run do
  let mut out : Array Tok := #[]
  let mut radii := false
  for t in v do
    if t == .op "circle" || t == .op "ellipse" || t == .ident "round" then radii := true
    else if t == .ident "at" || t == .close || t == .comma then radii := false
    out := out.push (if radii then clampTok0 t else t)
  return out.toList

/-- Two components of which one is a zero of the other's type: a number 0 beside a
length is that length's 0, and a length of 0 beside a number is the number 0 (a side of
`border-image-outset` is a number or a length, and 0 is the same side either way). Other
pairs stay. -/
def alignZero (x y : Tok) : Tok × Tok :=
  match x, y with
  | .num a, .dim b u => if a == 0 then (.dim 0 u, .dim b u) else if b == 0 then (.num a, .num 0) else (x, y)
  | .dim a u, .num b => if b == 0 then (.dim a u, .dim 0 u) else if a == 0 then (.num 0, .num b) else (x, y)
  | _, _ => (x, y)

/-- The components of a `transform-origin`: x, y and z (0px when not written). -/
def originOf (v : List Tok) : Option (Tok × Tok × Tok) :=
  match v with
  | [x, y] => some (x, y, .dim 0 "px")
  | [x, y, z] => some (x, y, z)
  | _ => none

/-- A `transform-origin` in its shortest form: z is written unless it is 0px. -/
def originText (x y z : Tok) : List Tok := if z == .dim 0 "px" then [x, y] else [x, y, z]

/-- The keyword of a `zeroWord` kind as the length 0. -/
def zeroOf (word : String) (v : List Tok) : List Tok := if v == [.ident word] then [.dim 0 "px"] else v

/-- The interpolation of a kind that is a list or has components to fill in; none when
the values do not interpolate. -/
def lerpKind (k : Kind) (p : Int) (a b : Value) : Option Value :=
  match k with
  | .transformList => lerpTransformList p a b
  | .filterList =>
    (zipItems (lerpList p) filterNeutral
      (if isNone a then [] else (items a).map filterFull) (if isNone b then [] else (items b).map filterFull)).map
      fun r => joinItems (r.map filterClamp)
  | .shadowList n =>
    -- a shadow colour outside legacy sRGB: every colour in Oklab
    let modern := modernColor a || modernColor b
    let (a, b) := if modern then (toOklab a, toOklab b) else (a, b)
    (zipItems (lerpList p) shadowNeutral
      (if isNone a then [] else (commaItems a).map (shadowFull n)) (if isNone b then [] else (commaItems b).map (shadowFull n))).map
      fun r => let v := joinCommas (r.map shadowClamp); if modern then fromOklab v else v
  | .translate =>
    match translateOf a b, translateOf b a with
    | some (x, y, z), some (x', y', z') =>
      match lerpTok p x x', lerpTok p y y', lerpTok p z z' with
      | some rx, some ry, some rz => some (translateText rx ry rz)
      | _, _, _ => none
    | _, _ => none
  | .scale =>
    match scaleOf a, scaleOf b with
    | some (x, y, z), some (x', y', z') => some (scaleText (Fix.lerp x x' p) (Fix.lerp y y' p) (Fix.lerp z z' p))
    | _, _ => none
  | .rotate =>
    match rotateOf a, rotateOf b with
    | some _, some _ => lerpRotate p a b
    | _, _ => none
  | .fontStyle =>
    match obliqueOf a, obliqueOf b with
    | some x, some y =>
      let r := Fix.clamp (Fix.ofInt (-90)) (Fix.ofInt 90) (Fix.lerp x y p)
      some (if r == 0 then [.ident "normal"] else [.ident "oblique", .dim r "deg"])
    | _, _ => none
  | .origin =>
    match originOf a, originOf b with
    | some (x, y, z), some (x', y', z') =>
      match lerpTok p x x', lerpTok p y y', lerpTok p z z' with
      | some rx, some ry, some rz => some (originText rx ry rz)
      | _, _, _ => none
    | _, _ => none
  | .sides =>
    match sidesOf a, sidesOf b with
    | some (t, r, bo, l, f), some (t', r', bo', l', f') =>
      if f != f' then none else
      let (t, t') := alignZero t t'
      let (r, r') := alignZero r r'
      let (bo, bo') := alignZero bo bo'
      let (l, l') := alignZero l l'
      match lerpTok p t t', lerpTok p r r', lerpTok p bo bo', lerpTok p l l' with
      | some x1, some x2, some x3, some x4 => some (sidesText (clampTok0 x1) (clampTok0 x2) (clampTok0 x3) (clampTok0 x4) f)
      | _, _, _, _ => none
    | _, _ => none
  | .gridTracks =>
    -- CSS Grid 2 §7.2.4: lists with an auto-repeat, or whose repeats differ, do not interpolate
    let heads := repeatHeads a
    if heads != repeatHeads b || heads.any (fun t => t == .ident "auto-fill" || t == .ident "auto-fit") then none
    else
      -- the sizes interpolate; the line names are those of the nearer value
      let (ta, na) := stripLineNames a
      let (tb, nb) := stripLineNames b
      (lerpLoose p ta tb).map fun r => withLineNames (r.map clampTok0) (if p < half then na else nb)
  | .offsetRotate =>
    match offsetRotateOf a, offsetRotateOf b with
    | some (f, x), some (g, y) => if f == g then some (offsetRotateText f (Fix.lerp x y p)) else none
    | _, _ => none
  | .shape =>
    -- a circle or an ellipse with a keyword radius does not interpolate
    let round := fun (v : List Tok) => v.contains (.op "circle") || v.contains (.op "ellipse")
    let keyword := fun (v : List Tok) => round v && v.any fun t =>
      t == .ident "closest-side" || t == .ident "farthest-side" || t == .ident "closest-corner" || t == .ident "farthest-corner"
    if keyword a || keyword b then none
    else
      -- `inset()`, `rect()` and `xywh()` meet as `inset()`
      let (ia, ha) := insetForm a
      let (ib, hb) := insetForm b
      if ha && hb then (lerpList p (clampShapeRadii ia) (clampShapeRadii ib)).map fun r =>
        ((items (clampShapeRadii r)).map insetText).flatten
      else (lerpList p (expandPaths a) (expandPaths b)).map fun r => collapsePaths (clampShapeRadii r)
  | .gapList =>
    match expandRepeats a, expandRepeats b with
    | some xs, some ys =>
      match repeated xs ys with
      | some (xs, ys) => (zipItems (lerpList p) (fun _ => none) xs ys).map fun r => joinCommas (r.map fun it => it.map clampTok0)
      | none => none
    | _, _ => none
  | .radius =>
    let pair := fun (v : List Tok) => match v with
      | [x] => [x, x]
      | v => v
    (lerpList p (pair a) (pair b)).map fun r =>
      match r.map clampTok0 with
      | [x, y] => if x == y then [x] else [x, y]
      | r => r
  | .repeatable =>
    match repeated (commaItems a) (commaItems b) with
    | some (xs, ys) => (zipItems (lerpList p) (fun _ => none) xs ys).map joinCommas
    | none => none
  | .ratio =>
    match ratioOf a, ratioOf b with
    | some x, some y =>
      let t := Float.ofInt p / Float.ofInt Fix.scale
      let r := Float.exp (Float.log x + (Float.log y - Float.log x) * t)
      if r.isFinite && r > 0 then
        some [.num ((r * Float.ofInt Fix.scale).round.toInt64.toInt), .slash, .num one]
      else none
    | _, _ => none
  | .cornerShape => lerpCorner p a b
  | .zeroWord word keep =>
    (lerpList p (zeroOf word a) (zeroOf word b)).map fun r =>
      if keep && r == [.dim 0 "px"] && ((p == 0 && a == [.ident word]) || (p == one && b == [.ident word])) then
        [.ident word]
      else r
  | .generic =>
    -- a colour outside legacy sRGB: every colour of the two values in Oklab
    if modernColor a || modernColor b then (lerpList p (toOklab a) (toOklab b)).map fromOklab
    else lerpList p a b
  | _ => (lerpList p a b).map (finish k)

/-- Whether two values interpolate component-wise for the kind (Web Animations 1 §5.2;
CSS Transitions 2 §3.2 starts no transition between values that do not, unless
`transition-behavior: allow-discrete`). -/
def interpolable (k : Kind) (a b : Value) : Bool :=
  match k with
  | .discrete | .avoid _ => false
  | .visibility => a == b || a == [.ident "visible"] || b == [.ident "visible"]
  | _ => (lerpKind k half a b).isSome

/-- The value at progress `p` between `a` and `b` (Web Animations 1 §5.2): equal values
stay; shapes that agree move component-wise (also at 0 and 1, where a length that meets
a percentage is in its `calc()` form, as CSS Values 4 §3.1 computes it); others flip at
50%. -/
def interpolate (k : Kind) (a b : Value) (p : Int) : Value :=
  if a == b then a
  else match k with
    | .discrete => if p < half then a else b
    | .avoid off =>
      if a == [.ident off] then (if p ≤ 0 then a else b)
      else if b == [.ident off] then (if p ≥ one then b else a)
      else if p < half then a else b
    | .visibility =>
      if a == [.ident "visible"] || b == [.ident "visible"] then
        if p ≤ 0 then a else if p ≥ one then b else [.ident "visible"]
      else if p < half then a else b
    | _ =>
      match lerpKind k p a b with
      | some r => r
      | none => if p < half then a else b

/-! ## Addition and accumulation (Web Animations 1 §5.2, CSS Values 4 §3.2, §3.3) -/

/-- `x + y - n` of two components and the neutral component `n` between them (the sum
of two filter amounts counts the neutral value once). -/
def accTok (n x y : Tok) : Option Tok :=
  match n, x, y with
  | .num c, .num a, .num b => some (.num (a + b - c))
  | .dim c _, .dim a u, .dim b v => if u == v then some (.dim (a + b - c) u) else none
  | _, a, b => addTok a b

/-- Two items of one shape accumulated component by component over the neutral item. -/
def accItem (neutral : List Tok → Option (List Tok)) (x y : List Tok) : Option (List Tok) :=
  match neutral x with
  | some n =>
    if n.length == x.length && x.length == y.length then
      ((n.zip (x.zip y)).mapM fun (c, a, b) => accTok c a b)
    else none
  | none => none

/-- `value` added to `underlying` (composite operation `add`, Web Animations 1 §5.2):
lists of functions and of shadows are joined; `translate` adds, `scale` multiplies (the
product of two scales); other values add component-wise, or `value` replaces when they
do not add. -/
def add (k : Kind) (underlying value : Value) : Value :=
  match k with
  | .discrete | .visibility | .avoid _ => value
  | .transformList | .filterList =>
    joinItems ((if isNone underlying then [] else items underlying) ++ (if isNone value then [] else items value))
  | .shadowList _ =>
    joinCommas ((if isNone underlying then [] else commaItems underlying) ++ (if isNone value then [] else commaItems value))
  | .rotate =>
    match rotateOf underlying, rotateOf value with
    | some (ax, x), some (bx, y) =>
      let axis := if ax == bx then some ax else if ax == [.ident "none"] then some bx else if bx == [.ident "none"] then some ax else none
      match axis with
      | some ax => (if ax == [.ident "none"] then [] else ax) ++ [.dim (x + y) "deg"]
      | none =>
        -- two axes written differently: one direction adds the angles; two directions
        -- are one rotation after the other (the product of the quaternions)
        match axisOf ax, axisOf bx with
        | some (x1, y1, z1), some (x2, y2, z2) =>
          if x1 * x2 + y1 * y2 + z1 * z2 > 0.999999 then rotateText x1 y1 z1 (x + y)
          else
            let quat := fun (ux uy uz : Float) (deg : Int) =>
              let h := Matrix.radians (toFloat deg) / 2
              (ux * Float.sin h, uy * Float.sin h, uz * Float.sin h, Float.cos h)
            let (qx, qy, qz, qw) := Matrix.qmul (quat x1 y1 z1 x) (quat x2 y2 z2 y)
            let qw := if qw > 1 then 1 else if qw < -1 then -1 else qw
            let sn := Float.sqrt (1 - qw * qw)
            if sn < 0.000001 then rotateText 0 0 1 0
            else rotateText (qx / sn) (qy / sn) (qz / sn) (ofFloat (Matrix.degrees (2 * Float.acos qw)))
        | _, _ => value
    | _, _ => value
  | .origin =>
    match originOf underlying, originOf value with
    | some (x, y, z), some (x', y', z') =>
      match addTok x x', addTok y y', addTok z z' with
      | some rx, some ry, some rz => originText rx ry rz
      | _, _, _ => value
    | _, _ => value
  | .sides =>
    match sidesOf underlying, sidesOf value with
    | some (t, r, bo, l, f), some (t', r', bo', l', f') =>
      let (t, t') := alignZero t t'
      let (r, r') := alignZero r r'
      let (bo, bo') := alignZero bo bo'
      let (l, l') := alignZero l l'
      match addTok t t', addTok r r', addTok bo bo', addTok l l' with
      | some x1, some x2, some x3, some x4 => if f == f' then sidesText x1 x2 x3 x4 f else value
      | _, _, _, _ => value
    | _, _ => value
  | .gridTracks =>
    let (ta, _) := stripLineNames underlying
    let (tb, nb) := stripLineNames value
    ((addLoose ta tb).map fun r => withLineNames r nb).getD value
  | .repeatable =>
    match repeated (commaItems underlying) (commaItems value) with
    | some (xs, ys) => ((zipItems addList (fun _ => none) xs ys).map joinCommas).getD value
    | none => value
  | .ratio => value
  | .shape =>
    let (ia, ha) := insetForm underlying
    let (ib, hb) := insetForm value
    if ha && hb then ((addList ia ib).map fun r => ((items r).map insetText).flatten).getD value
    else ((addList (expandPaths underlying) (expandPaths value)).map collapsePaths).getD value
  | .gapList =>
    match expandRepeats underlying, expandRepeats value with
    | some xs, some ys =>
      match repeated xs ys with
      | some (xs, ys) => ((zipItems addList (fun _ => none) xs ys).map joinCommas).getD value
      | none => value
    | _, _ => value
  | .radius =>
    let pair := fun (v : List Tok) => match v with
      | [x] => [x, x]
      | v => v
    match addList (pair underlying) (pair value) with
    | some [x, y] => if x == y then [x] else [x, y]
    | some r => r
    | none => value
  | .offsetRotate =>
    match offsetRotateOf underlying, offsetRotateOf value with
    | some (f, x), some (g, y) => if f == g then offsetRotateText f (x + y) else value
    | _, _ => value
  | .translate =>
    match translateOf underlying value, translateOf value underlying with
    | some (x, y, z), some (x', y', z') =>
      match addTok x x', addTok y y', addTok z z' with
      | some rx, some ry, some rz => translateText rx ry rz
      | _, _, _ => value
    | _, _ => value
  | .scale =>
    match scaleOf underlying, scaleOf value with
    | some (x, y, z), some (x', y', z') => scaleText (Fix.mul x x') (Fix.mul y y') (Fix.mul z z')
    | _, _ => value
  | .cornerShape => value
  | .zeroWord word _ => (addList (zeroOf word underlying) (zeroOf word value)).getD value
  | _ => match addList underlying value with
    | some r => finish k r
    | none => value

/-- `value` accumulated onto `underlying` (composite operation `accumulate`, Web
Animations 1 §5.2): lists pair up as in interpolation and each pair accumulates over its
neutral value; `scale` is x + y - 1; other values as `add`. -/
def accumulate (k : Kind) (underlying value : Value) : Value :=
  match k with
  | .transformList =>
    let plain := zipItems (accItem transformIdentity) transformIdentity
        (if isNone underlying then [] else items underlying) (if isNone value then [] else items value)
    let kept : Option Value := match plain with
      | some r => if (fnNames underlying ++ fnNames value).any byMatrix then none else some (joinItems r)
      | none => none
    match kept with
    | some r => r
    | none =>
      match readTransforms underlying, readTransforms value with
      | some x, some y => ((accTransforms x y).map writeTransforms).getD value
      | _, _ => value
  | .filterList =>
    match zipItems (accItem filterNeutral) filterNeutral
        (if isNone underlying then [] else items underlying) (if isNone value then [] else items value) with
    | some r => joinItems r
    | none => value
  | .shadowList n =>
    match zipItems addList shadowNeutral
        (if isNone underlying then [] else (commaItems underlying).map (shadowFull n))
        (if isNone value then [] else (commaItems value).map (shadowFull n)) with
    | some r => joinCommas r
    | none => value
  | .scale =>
    match scaleOf underlying, scaleOf value with
    | some (x, y, z), some (x', y', z') => scaleText (x + x' - one) (y + y' - one) (z + z' - one)
    | _, _ => value
  | _ => add k underlying value

/-! ## Theorems -/

/-- `t` is the component `a`, or `a` written as a mixed length-percentage whose other
part is 0 (`10px` as `calc(0% + 10px)`, `50%` as `calc(50% + 0px)`). -/
def sameTok (t a : Tok) : Prop :=
  t = a ∨ (∃ x, a = .dim x "px" ∧ t = .lp x 0) ∨ (∃ y, a = .dim y "%" ∧ t = .lp 0 y)

/-- Kind: interpolation end point. Says: at progress 0 a component-wise interpolation
gives the start component, exactly, or that component in its mixed length-percentage form
with the other part 0 (when a length meets a percentage). Does not say: anything near 0;
nor that values of different shapes interpolate (they flip at 50%, so at 0 they are the
start value). -/
theorem lerpTok_zero (a b t : Tok) (h : lerpTok 0 a b = some t) : sameTok t a := by
  unfold sameTok
  cases a <;> cases b <;> simp only [lerpTok, mkLp, lerpColor, Fix.lerp_zero] at h <;>
    first
    | (injection h with h; subst h; simp)
    | (split at h <;> first
        | (injection h with h; subst h; simp_all)
        | (split at h <;> first
            | (injection h with h; subst h; simp_all)
            | (split at h <;> first
                | (injection h with h; subst h; simp_all)
                | simp at h)
            | simp at h)
        | simp at h)
    | simp at h

/-- Kind: interpolation end point. Says: at progress 1 a component-wise interpolation
gives the end component, exactly, or that component in its mixed length-percentage form
with the other part 0. Does not say: anything near 1. -/
theorem lerpTok_one (a b t : Tok) (h : lerpTok one a b = some t) : sameTok t b := by
  unfold sameTok
  have hone : (one == (0 : Int)) = false := by decide
  cases a <;> cases b <;> simp only [lerpTok, mkLp, lerpColor, Fix.lerp_one, hone] at h <;>
    first
    | (injection h with h; subst h; simp)
    | (split at h <;> first
        | (injection h with h; subst h; simp_all)
        | (split at h <;> first
            | (injection h with h; subst h; simp_all)
            | (split at h <;> first
                | (injection h with h; subst h; simp_all)
                | simp at h)
            | simp at h)
        | simp at h)
    | simp at h

/-- Kind: interpolation end point. Says: values of a discrete kind are the start value
at progress 0 and the end value at progress 1. Does not say: this of the other kinds
(`lerpTok_zero` and `lerpTok_one` say what their components are). -/
theorem discrete_ends (a b : Value) :
    interpolate .discrete a b 0 = a ∧ interpolate .discrete a b one = b := by
  unfold interpolate
  by_cases h : a = b
  · subst h; simp
  · have h' : (a == b) = false := by simpa using h
    simp [h', half, one, Fix.scale]

/-- Kind: interpolation identity. Says: a value interpolated with itself is itself, at
every progress and for every kind. Does not say: more. -/
theorem interpolate_self (k : Kind) (a : Value) (p : Int) : interpolate k a a p = a := by
  simp [interpolate]

/-- Kind: arithmetic of one component. Says: two number tokens interpolate to the number
`Fix.lerp` gives, so `Fix.lerp_zero`, `Fix.lerp_one`, `Fix.lerp_self` and
`Fix.lerp_between` hold of it with no end point test. Does not say: this of colours
(premultiplied) or of mixed units. -/
theorem lerpTok_num (p a b : Int) : lerpTok p (.num a) (.num b) = some (.num (Fix.lerp a b p)) := rfl

/-- Kind: arithmetic of one component. Says: two dimensions of one unit interpolate to
that unit with the number `Fix.lerp` gives. Does not say: more. -/
theorem lerpTok_dim (p a b : Int) (u : String) :
    lerpTok p (.dim a u) (.dim b u) = some (.dim (Fix.lerp a b p) u) := by
  simp [lerpTok]

theorem lerpGo_length (p : Int) : ∀ (a b acc r : List Tok), lerpGo p a b acc = some r →
    r.length = acc.length + a.length
  | [], [], acc, r, h => by simp [lerpGo] at h; simp [← h]
  | [], _ :: _, acc, r, h => by simp [lerpGo] at h
  | _ :: _, [], acc, r, h => by simp [lerpGo] at h
  | a :: as, b :: bs, acc, r, h => by
    unfold lerpGo at h
    split at h
    · rename_i t _
      have := lerpGo_length p as bs (t :: acc) r h
      simp at this ⊢
      omega
    · simp at h

/-- Kind: shape. Says: a component-wise interpolation has as many components as its
start value. Does not say: what they are. -/
theorem lerpList_length (p : Int) (a b r : List Tok) (h : lerpList p a b = some r) : r.length = a.length := by
  have := lerpGo_length p a b [] r h
  simpa using this

/-- A token that is not a number below 0. -/
def tokNonNeg : Tok → Prop
  | .num n => 0 ≤ n
  | .dim n _ => 0 ≤ n
  | _ => True

theorem clampTok0_nonNeg (t : Tok) : tokNonNeg (clampTok0 t) := by
  cases t <;> simp [clampTok0, tokNonNeg] <;> omega

/-- Kind: range (CSS Values 4 §10.12 range checking; a property whose value can not be
negative clamps an interpolated result). Says: for the non-negative kind, when the start
and end values hold no negative number or dimension, the value at every progress (also
outside [0, 1], where the arithmetic goes below 0) holds none. Does not say: anything of
a mixed length-percentage (`lp`), whose sign depends on the percentage basis. -/
theorem nonNegative_range (a b : Value) (p : Int)
    (ha : ∀ t ∈ a, tokNonNeg t) (hb : ∀ t ∈ b, tokNonNeg t) :
    ∀ t ∈ interpolate .nonNegative a b p, tokNonNeg t := by
  unfold interpolate
  split
  · exact ha
  · simp only [lerpKind]
    cases hl : lerpList p a b with
    | some r =>
      intro t ht
      simp only [Option.map, finish, List.mem_map] at ht
      obtain ⟨t', _, rfl⟩ := ht
      exact clampTok0_nonNeg t'
    | none =>
      simp only [Option.map]
      split
      · exact ha
      · exact hb

/-- Kind: range. Says: for `opacity`'s kind, a number of a component-wise result is in
[0, 1] after `finish`. Does not say: this of the start and end values themselves. -/
theorem unit_range (ts : List Tok) (n : Int) (h : Tok.num n ∈ finish .unit ts) : 0 ≤ n ∧ n ≤ one := by
  simp only [finish, List.mem_map] at h
  obtain ⟨t, _, ht⟩ := h
  cases t <;> simp [rangeTok] at ht
  subst ht
  exact Fix.clamp_between 0 one _ (by decide)

/-- Kind: visibility. Says: a line of positive width keeps a positive width when
snapped: it is never rounded away. -/
theorem snapWidth_pos (n : Int) (h : 0 < n) : 0 < snapWidth n := by
  unfold snapWidth Fix.floor
  have s : (0 : Int) < Fix.scale := by decide
  have o : one = Fix.scale := rfl
  have sl : (0 : Int) ≤ slack := by decide
  split
  · omega
  · split
    · omega
    · rename_i h1 h2
      have h3 : 1 * Fix.scale ≤ n + slack := by omega
      have : 1 ≤ (n + slack) / Fix.scale := Int.le_ediv_of_mul_le s h3
      have := Int.mul_le_mul_of_nonneg_right this (Int.le_of_lt s)
      omega

/-- Kind: bound. Says: snapping widens a line of 1px or more by no more than the slack
of a rounding boundary (a thousandth of a pixel). -/
theorem snapWidth_le (n : Int) (h : one ≤ n) : snapWidth n ≤ n + slack := by
  unfold snapWidth Fix.floor
  have s : (0 : Int) < Fix.scale := by decide
  have o : one = Fix.scale := rfl
  have sl : (0 : Int) ≤ slack := by decide
  have := Int.ediv_mul_le (n + slack) (Int.ne_of_gt s)
  split
  · omega
  · split <;> omega

/-- Kind: idempotence. Says: a snapped width is its own snap. -/
theorem snapWidth_idem (n : Int) : snapWidth (snapWidth n) = snapWidth n := by
  have s : (0 : Int) < Fix.scale := by decide
  have o : one = Fix.scale := rfl
  have sl : (0 : Int) ≤ slack := by decide
  have z0 : slack / Fix.scale = 0 := by decide
  -- a width that is not positive, or a whole number of px of at least 1, is its own snap
  have key : ∀ m : Int, (m ≤ 0 ∨ (∃ k : Int, 1 ≤ k ∧ m = k * Fix.scale)) → snapWidth m = m := by
    intro m hm
    rcases hm with h | ⟨k, hk, rfl⟩
    · simp [snapWidth, h]
    · have big := Int.mul_le_mul_of_nonneg_right hk (Int.le_of_lt s)
      have z : ¬ (k * Fix.scale ≤ 0) := by omega
      have y : ¬ (k * Fix.scale < one) := by omega
      simp only [snapWidth, Fix.floor, if_neg z, if_neg y]
      rw [Int.add_comm, Int.add_mul_ediv_right _ _ (Int.ne_of_gt s), z0, Int.zero_add]
  apply key
  by_cases h0 : n ≤ 0
  · left
    simp [snapWidth, h0]
  · by_cases h1 : n < one
    · right
      refine ⟨1, by omega, ?_⟩
      rw [show snapWidth n = one by simp [snapWidth, h0, h1]]
      omega
    · right
      have h3 : 1 * Fix.scale ≤ n + slack := by omega
      have q : 1 ≤ (n + slack) / Fix.scale := Int.le_ediv_of_mul_le s h3
      exact ⟨(n + slack) / Fix.scale, q, by simp [snapWidth, h0, h1, Fix.floor]⟩

/-- Kind: identity. Says: two numbers, and two lengths, are left as they are by
`alignZero`: only a number beside a length is touched. -/
theorem alignZero_same (a b : Int) (u v : String) :
    alignZero (.num a) (.num b) = (.num a, .num b) ∧ alignZero (.dim a u) (.dim b v) = (.dim a u, .dim b v) :=
  ⟨rfl, rfl⟩

/-- Kind: round trip. Says: the shortest form of a `transform-origin` reads back as the
three components it was written from, for all components. -/
theorem originOf_text (x y z : Tok) : originOf (originText x y z) = some (x, y, z) := by
  unfold originText
  split
  · rename_i h
    have hz := eq_of_beq h
    subst hz
    rfl
  · rfl

/-! ### Transform functions -/

theorem zeroLike_idem (t : Tok) : zeroLike (zeroLike t) = zeroLike t := by
  cases t <;> rfl

/-- Kind: structure. Says: the identity function that pads a shorter list is of the same
primitive as the function it stands beside, so padding alone never sends a pair to the
matrix path. Does not say: that the pair interpolates (two lengths may not combine). -/
theorem samePrimitive_identityFn (f : TF) : samePrimitive f (identityFn f) = true := by
  cases f <;> simp [samePrimitive, identityFn]

/-- Kind: structure. Says: the identity function of an identity function is itself.
Does not say: that its matrix is the identity matrix (`Float`; tested). -/
theorem identityFn_idem (f : TF) : identityFn (identityFn f) = identityFn f := by
  cases f with
  | translate x y z t => simp [identityFn, zeroLike_idem]
  | scale x y z t => rfl
  | rotate x y z d t => rfl
  | skew a b f => rfl
  | matrix m =>
    by_cases h : m.length = 6
    · simp [identityFn, h]
    · simp [identityFn, h, identity16]
  | perspective d => rfl

/-- Kind: end point. Says: two scales at progress 0 are the first, exactly. Does not
say: anything of the `three` flag beyond: it is set when either function had it. -/
theorem lerpFn_scale_zero (x y z x' y' z' : Int) (t t' : Bool) :
    lerpFn 0 (.scale x y z t) (.scale x' y' z' t') = some (.scale x y z (t || t')) := by
  simp [lerpFn, Fix.lerp_zero]

/-- Kind: end point. Says: two scales at progress 1 are the second, exactly. -/
theorem lerpFn_scale_one (x y z x' y' z' : Int) (t t' : Bool) :
    lerpFn one (.scale x y z t) (.scale x' y' z' t') = some (.scale x' y' z' (t || t')) := by
  simp [lerpFn, Fix.lerp_one]

/-- Kind: identity. Says: a scale interpolated with itself is itself at every progress,
in range or not. -/
theorem lerpFn_scale_self (x y z : Int) (t : Bool) (p : Int) :
    lerpFn p (.scale x y z t) (.scale x y z t) = some (.scale x y z t) := by
  simp [lerpFn, Fix.lerp_self]

/-- Kind: end points. Says: two skews at progress 0 and 1 are the first and the second. -/
theorem lerpFn_skew_ends (a b a' b' : Int) (f : Nat) :
    lerpFn 0 (.skew a b f) (.skew a' b' f) = some (.skew a b f) ∧
    lerpFn one (.skew a b f) (.skew a' b' f) = some (.skew a' b' f) := by
  simp [lerpFn, Fix.lerp_zero, Fix.lerp_one]

/-- Kind: bounds. Says: for a progress in [0, 1] each component of the scale between two
scales lies between the two components. Does not say: anything outside [0, 1] (an easing
may overshoot; scales are not clamped). -/
theorem lerpFn_scale_between (x y z x' y' z' : Int) (t t' : Bool) (p : Int) (hp0 : 0 ≤ p) (hp1 : p ≤ one) :
    ∃ rx ry rz, lerpFn p (.scale x y z t) (.scale x' y' z' t') = some (.scale rx ry rz (t || t')) ∧
      min x x' ≤ rx ∧ rx ≤ max x x' ∧ min y y' ≤ ry ∧ ry ≤ max y y' ∧ min z z' ≤ rz ∧ rz ≤ max z z' :=
  ⟨Fix.lerp x x' p, Fix.lerp y y' p, Fix.lerp z z' p, rfl,
    (Fix.lerp_between x x' p hp0 hp1).1, (Fix.lerp_between x x' p hp0 hp1).2,
    (Fix.lerp_between y y' p hp0 hp1).1, (Fix.lerp_between y y' p hp0 hp1).2,
    (Fix.lerp_between z z' p hp0 hp1).1, (Fix.lerp_between z z' p hp0 hp1).2⟩

/-- Kind: neutral element. Says: accumulating the identity scale onto a scale, or a
scale onto the identity scale, gives the scale (1 is counted once). -/
theorem accFn_scale_identity (x y z : Int) (t t' : Bool) :
    accFn (.scale x y z t) (identityFn (.scale x y z t')) = some (.scale x y z (t || t')) ∧
    accFn (identityFn (.scale x y z t')) (.scale x y z t) = some (.scale x y z (t' || t)) := by
  constructor <;> simp [accFn, identityFn] <;> omega

/-- Kind: additivity. Says: accumulating skews adds their angles, in either order and
grouped either way. Does not say: that the matrices commute (they do not; the sum is of
the angles, Web Animations 1 §5.2). -/
theorem accFn_skew_add (a b a' b' a'' b'' : Int) (f : Nat) :
    accFn (.skew a b f) (.skew a' b' f) = some (.skew (a + a') (b + b') f) ∧
    accFn (.skew a b f) (.skew a' b' f) = accFn (.skew a' b' f) (.skew a b f) ∧
    (accFn (.skew a b f) (.skew a' b' f)).bind (accFn · (.skew a'' b'' f)) =
      (accFn (.skew a' b' f) (.skew a'' b'' f)).bind (accFn (.skew a b f)) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [accFn] <;> omega

/-- Kind: additivity. Says: the sum of number components is the sum of the numbers:
commutative and associative, so the order in which effects of one property add their
numbers does not change the result. Does not say: the same of lists (a list of
functions is joined, and order matters there). -/
theorem addTok_num_assoc (a b c : Int) :
    addTok (.num a) (.num b) = some (.num (a + b)) ∧
    addTok (.num a) (.num b) = addTok (.num b) (.num a) ∧
    (addTok (.num a) (.num b)).bind (addTok · (.num c)) = (addTok (.num b) (.num c)).bind (addTok (.num a)) := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [addTok] <;> omega

/-! ## Tests: the cases of the interpolation tests (css/support/interpolation-testcommon.js) -/

private def at_ (k : Kind) (a b : String) (p : Int) : String := toText (interpolate k (parse a) (parse b) p)

#guard toText (parse "10px") == "10px"
#guard toText (parse "calc(50% + 10px)") == "calc(50% + 10px)"
#guard toText (parse "calc(50% - 10px)") == "calc(50% - 10px)"
#guard toText (parse "rgb(10, 20, 30)") == "rgb(10, 20, 30)"
#guard toText (parse "rgba(10, 20, 30, 0.5)") == "rgba(10, 20, 30, 0.5)"
#guard toText (parse "matrix(1, 0, 0, 1, 10.5, -3)") == "matrix(1, 0, 0, 1, 10.5, -3)"
#guard toText (parse "\"a b\", serif") == "\"a b\", serif"
#guard toText (parse "url(\"x.png\") 1 2 / 3px") == "url(\"x.png\") 1 2 / 3px"
#guard toText (parse "inset(10px 20px round 5px)") == "inset(10px 20px round 5px)"
#guard toText (parse "polygon(nonzero, 0px 0px, 10px 0px)") == "polygon(nonzero, 0px 0px, 10px 0px)"
#guard parse "1e3px" == [.dim (Fix.ofInt 1000) "px"]
#guard parse "-webkit-box" == [.ident "-webkit-box"]
#guard parse "--x" == [.ident "--x"]
#guard at_ .generic "10px" "20px" 300000000 == "13px"
#guard at_ .generic "10px" "20px" (-300000000) == "7px"
#guard at_ .generic "0px" "100%" half == "50%"
#guard at_ .generic "10px" "100%" 0 == "calc(0% + 10px)"
#guard at_ .generic "10px" "100%" one == "100%"
#guard at_ .generic "10px 20px 30px" "20% 30% 40px" 0 == "calc(0% + 10px) calc(0% + 20px) 30px"
#guard at_ .generic "repeat(2, 1fr 20px)" "repeat(2, 3fr 40px)" half == "repeat(2, 2fr 30px)"
#guard at_ .generic "repeat(2, 1fr)" "repeat(3, 1fr)" 400000000 == "repeat(2, 1fr)"
#guard toText (parse "calc(0% + 10px)") == "calc(0% + 10px)"
#guard at_ .generic "10px" "100%" half == "calc(50% + 5px)"
#guard at_ .generic "calc(50% - 25px)" "calc(100% - 10px)" 250000000 == "calc(62.5% - 21.25px)"
#guard at_ .nonNegative "10px" "20px" (-2 * one) == "0px"
#guard at_ .generic "auto" "20px" 300000000 == "auto"
#guard at_ .generic "auto" "20px" 600000000 == "20px"
#guard at_ .generic "rgb(0, 0, 0)" "rgb(255, 255, 255)" half == "rgb(128, 128, 128)"
#guard at_ .generic "rgba(0, 0, 0, 0)" "rgb(0, 128, 0)" half == "rgba(0, 128, 0, 0.5)"
#guard at_ .integer "1" "4" half == "3"
#guard at_ .integer "-2" "4" 300000000 == "0"
#guard at_ .positiveInteger "2" "8" (-one) == "1"
#guard at_ .unit "0.2" "1" (one + half) == "1"
#guard at_ .unit "0.2" "1" (-one) == "0"
#guard at_ .fontWeight "100" "900" half == "500"
#guard at_ .visibility "visible" "hidden" 900000000 == "visible"
#guard at_ .visibility "hidden" "visible" 100000000 == "visible"
#guard at_ .visibility "hidden" "collapse" 100000000 == "hidden"
#guard at_ .visibility "visible" "hidden" (one + half) == "hidden"
#guard at_ .visibility "visible" "hidden" (-half) == "visible"
#guard at_ .discrete "10px" "20px" 400000000 == "10px"
#guard at_ (.avoid "none") "none" "block" 100000000 == "block"
#guard at_ (.avoid "none") "block" "none" 900000000 == "block"
#guard at_ (.avoid "none") "block" "none" (one + half) == "none"
#guard at_ (.avoid "none") "none" "block" (-half) == "none"
#guard at_ (.avoid "none") "inline" "block" 400000000 == "inline"
#guard at_ .generic "circle(10px at 20px 30px)" "circle(20px at 40px 50px)" half == "circle(15px at 30px 40px)"
#guard at_ .generic "translate(10px, 20px)" "translate(30px, 40px)" half == "translate(20px, 30px)"
#guard at_ .generic "rotate(30deg)" "rotate(330deg)" 250000000 == "rotate(105deg)"
#guard at_ .generic "1px 2px" "3px" half == "3px"
#guard at_ .transformList "translate(100px)" "translate(200px) rotate(720deg)" 250000000 == "translate(125px) rotate(180deg)"
#guard at_ .transformList "none" "rotate(90deg)" half == "rotate(45deg)"
-- corner shapes by their half corner (css/css-borders/corner-shape/corner-shape-interpolation.html)
private def corner2 (a b : String) (p : Int) : String :=
  match interpolate .cornerShape (parse a) (parse b) p with
  | [.op "superellipse", .num k, .close] => "superellipse(" ++ Fix.formatPlaces 2 k ++ ")"
  | v => toText v
#guard [-300000000, 600000000, 1500000000].map (corner2 "round" "bevel") == ["superellipse(1.4)", "superellipse(0.36)", "superellipse(-0.46)"]
#guard [-300000000, half, 600000000, one, 1500000000].map (corner2 "round" "scoop") ==
  ["superellipse(1.91)", "bevel", "superellipse(-0.18)", "scoop", "superellipse(-2.95)"]
#guard [-300000000, 600000000, 1500000000].map (corner2 "bevel" "squircle") == ["superellipse(-0.45)", "superellipse(0.98)", "square"]
#guard [-300000000, 0, 600000000, one, 1500000000].map (corner2 "bevel" "square") ==
  ["superellipse(-0.69)", "bevel", "superellipse(1.64)", "square", "square"]
#guard [-300000000, 600000000, 1500000000].map (corner2 "bevel" "scoop") == ["superellipse(0.27)", "superellipse(-0.56)", "superellipse(-1.72)"]
#guard [-300000000, 600000000, 1500000000].map (corner2 "bevel" "notch") == ["superellipse(0.69)", "superellipse(-1.64)", "notch"]
#guard [-300000000, 0, half, 800000000, one].map (corner2 "notch" "square") == ["notch", "notch", "bevel", "superellipse(1.64)", "square"]
#guard [-300000000, half, 800000000, 1100000000].map (corner2 "superellipse(3)" "superellipse(-2)") ==
  ["square", "superellipse(0.16)", "superellipse(-0.9)", "superellipse(-2.99)"]
#guard corner2 "round" "round" half == "round" && corner2 "superellipse(infinity)" "superellipse(-infinity)" half == "bevel"
-- drop-shadow: the blur is not below 0; a colour left out is currentcolor
-- (css/filter-effects/animation/filter-interpolation-004.html)
#guard at_ .filterList "drop-shadow(rgb(0, 0, 255) 0px 0px)" "drop-shadow(rgb(0, 128, 0) 20px 10px 30px)" (-one) ==
  "drop-shadow(rgb(0, 0, 255) -20px -10px 0px)"
#guard at_ .filterList "drop-shadow(rgb(0, 0, 255) 0px 0px)" "drop-shadow(rgb(0, 128, 0) 20px 10px 30px)" half ==
  "drop-shadow(rgb(0, 64, 128) 10px 5px 15px)"
#guard toText (dropShadowColors (parse "blur(2px) drop-shadow(0px 0px)")) == "blur(2px) drop-shadow(currentcolor 0px 0px)"
#guard toText (dropShadowColors (parse "drop-shadow(rgb(0, 128, 0) 20px 10px 30px)")) == "drop-shadow(rgb(0, 128, 0) 20px 10px 30px)"
-- a side that is 0 is a number or a length as the other value's side is
-- (css/css-backgrounds/animations/border-image-outset-composition.html)
#guard at_ .sides "100px 100" "0px 0px" (-250000000) == "125px 125" && at_ .sides "100px 100" "0 0" (-250000000) == "125px 125"
#guard at_ .sides "100px 100" "0px 0 0px 0" 250000000 == "75px 75"
#guard at_ .sides "1 2" "3px 4px" half == "3px 4px"
-- transform-origin: a missing z is 0px (css/css-transforms/animation/transform-origin-composition.html)
#guard at_ .origin "100px 100px" "160px 140px 40px" (-250000000) == "85px 90px -10px"
#guard at_ .origin "100px 100px" "160px 140px 40px" 0 == "100px 100px"
#guard toText (add .origin (parse "40px 60px") (parse "60px 40px 10px")) == "100px 100px 10px"
-- a radius is not below 0 (css/css-masking/animations/clip-path-interpolation-002.html)
#guard at_ .shape "circle(10px at 25px 75%)" "circle(50px at 50px 50%)" (-300000000) == "circle(0px at 17.5px 82.5%)"
#guard at_ .shape "ellipse(10px 20px at 25px 75px)" "ellipse(50px 100px at 50px 50px)" (-300000000) == "ellipse(0px 0px at 17.5px 82.5px)"
#guard at_ .shape "circle(10px at 25px 75%)" "circle(50px at 50px 50%)" half == "circle(30px at 37.5px 62.5%)"
-- a keyword that is the length 0 (css/css-text/animations/letter-spacing-interpolation.html,
-- word-spacing-interpolation.html, css/css-transitions/animations/vertical-align-interpolation.html)
#guard [-300000000, 0, 300000000, one].map (at_ (.zeroWord "normal" true) "normal" "20px") == ["-6px", "normal", "6px", "20px"]
#guard [-300000000, 0, 300000000].map (at_ (.zeroWord "normal" false) "normal" "20px") == ["-6px", "0px", "6px"]
#guard [-half, 0, 600000000].map (at_ (.zeroWord "baseline" false) "baseline" "100px") == ["-50px", "0px", "60px"]
#guard at_ (.zeroWord "baseline" false) "super" "100px" 300000000 == "super" && at_ (.zeroWord "baseline" false) "super" "100px" 600000000 == "100px"
#guard toText (add (.zeroWord "normal" true) (parse "normal") (parse "10px")) == "10px"
-- the flags of an arc are set above 0 (css/motion/animation/offset-path-interpolation-002.html)
#guard at_ .shape "path(\"M 100 400 A 10 20 30 1 0 140 450\")" "path(\"M 300 200 A 50 60 70 0 1 380 290\")" (-one) ==
  "path(\"M -100 600 A -30 -20 -10 1 0 -100 610\")"
#guard at_ .shape "path(\"M 100 400 A 10 20 30 1 0 140 450\")" "path(\"M 300 200 A 50 60 70 0 1 380 290\")" 125000000 ==
  "path(\"M 125 375 A 15 25 35 1 1 170 430\")"
#guard at_ .shape "path(\"M 100 400 A 10 20 30 1 0 140 450\")" "path(\"M 300 200 A 50 60 70 0 1 380 290\")" (2 * one) ==
  "path(\"M 500 0 A 90 100 110 0 1 620 130\")"
-- a half of a colour channel rounds up also when it arrives a hair under (a progress read
-- back with six decimals); a whole pixel of a line width likewise
#guard toText (interpolate .generic (parse "rgb(0, 0, 0)") (parse "rgb(255, 165, 0)") 299999750) == "rgb(77, 50, 0)"
#guard toText (snapWidths (interpolate .nonNegative (parse "10px") (parse "20px") (-300000250))) == "7px"
#guard toText (snapWidths (interpolate .nonNegative (parse "10px") (parse "20px") 299999750)) == "13px"
#guard toText (snapWidths (parse "6.99px 7.5px")) == "6px 7px"
#guard at_ .transformList "scale(2)" "none" half == "scale(1.5)"
-- colours outside legacy sRGB meet in Oklab (css/css-color/animation/color-interpolation.html,
-- css/css-backgrounds/animations/box-shadow-interpolation.html)
#guard at_ .generic "rgb(0, 0, 0)" "color(srgb 1 1 1)" 300000000 == "oklab(0.3 0 0)"
#guard at_ .generic "color(srgb 0 0 0)" "color(srgb 1 1 1)" 600000000 == "oklab(0.6 0 0)"
#guard at_ .generic "color(srgb 0 0 0)" "rgb(255, 255, 255)" (-300000000) == "oklab(0 0 0)"
#guard at_ .generic "color(srgb 0 0 0)" "rgb(255, 255, 255)" 1500000000 == "oklab(1 0 0)"
#guard at_ (.shadowList 4) "rgb(0, 0, 0) 10px 10px 10px 10px" "color(srgb 1 1 1) 10px 10px 10px 10px" 300000000 ==
  "oklab(0.3 0 0) 10px 10px 10px 10px"
-- two legacy colours stay in sRGB
#guard at_ .generic "rgb(0, 0, 0)" "rgb(255, 255, 255)" 600000000 == "rgb(153, 153, 153)"
-- line widths (css/css-gaps/animation/row-rule-width-interpolation.html: 3px to 40px)
#guard toText (snapWidths (interpolate .nonNegative (parse "3px") (parse "40px") 300000000)) == "14px"
#guard toText (snapWidths (interpolate .nonNegative (parse "3px") (parse "40px") 1500000000)) == "58px"
#guard toText (snapWidths (parse "0.4px 0px 7.5px 12px 50%")) == "1px 0px 7px 12px 50%"
-- two primitives: the lists as matrices (css/css-transforms/animation/list-interpolation.html)
#guard at_ .transformList "rotate(0deg) translate(100px)" "rotate(720deg) scale(2) translate(200px)" 250000000 ==
  "rotate(180deg) matrix(1.25, 0, 0, 1.25, 175, 0)"
#guard at_ .transformList "scale(2) rotate(0deg) translate(100px)" "rotate(720deg) scale(2) translate(200px)" 250000000 ==
  "matrix(2, 0, 0, 2, 250, 0)"
#guard at_ .transformList "translateX(100px) scaleX(3) translate(500px) scale(2)" "translateY(200px) scale(5) translateX(100px) scaleY(3)"
  250000000 == "translate(75px, 50px) scale(3.5, 2) translate(400px, 0px) scale(1.75, 2.25)"
#guard at_ .transformList "rotateX(90deg) translateX(100px)" "rotate3d(50, 0, 0, 180deg) translateY(200px)" 250000000 ==
  "rotate3d(1, 0, 0, 112.5deg) translate(75px, 50px)"
#guard at_ .transformList "rotate(0deg) scaleX(1)" "rotate(720deg) translateX(0px) scaleX(2)" 250000000 ==
  "rotate(180deg) matrix(1.25, 0, 0, 1, 0, 0)"
-- a percentage keeps the functions as they are named (no matrix without a box)
#guard at_ .transformList "translateY(70%)" "translateY(90%) scaleZ(2)" 250000000 == "translatey(75%) scalez(1.25)"
-- perspective by the reciprocal of the distance; none is infinitely far
-- (css/css-transforms/animation/transform-interpolation-001.html)
#guard at_ .transformList "perspective(400px)" "perspective(500px)" (-one) == "perspective(333.333333px)"
#guard at_ .transformList "perspective(none)" "perspective(500px)" half == "perspective(1000px)"
#guard at_ .transformList "perspective(none)" "perspective(500px)" (-one) == "perspective(none)"
#guard at_ .transformList "scaleZ(2)" "scaleZ(2) perspective(500px)" (one + one) == "scale3d(1, 1, 2) perspective(250px)"
-- matrices by decomposition (transform-interpolation-005.html)
#guard toTextPrecise (interpolate .transformList (parse "matrix(1, 0, 0, 1, 0, -6)") (parse "matrix(0, 7, -1, 0, 6, 0)") (-one)) ==
  "matrix(0, 5, 1, 0, -6, -12)"
#guard toTextPrecise (interpolate .transformList (parse "matrix(1, 0, 0, 1, 0, -6)") (parse "matrix(0, 7, -1, 0, 6, 0)") 333333333) ==
  "matrix(2.59808, 1.5, -0.5, 0.866025, 2, -4)"
#guard toTextPrecise (interpolate .transformList (parse "matrix(1, 0.36, 0, 1, 200, 200)") (parse "matrix(1, 0, 0, 1, 200, 200)") (one + one)) ==
  "matrix(0.881775, -0.317439, 0, 1.12565, 200, 200)"
-- a matrix with no inverse does not interpolate: the values flip at 50%
#guard at_ .transformList "matrix(1, 1, 0, 0, 0, 0)" "matrix(1, 0, 0, 1, 0, 0)" 400000000 == "matrix(1, 1, 0, 0, 0, 0)"
-- the resolved value (css/css-transforms/parsing/transform-computed.html)
#guard resolvedTransformText "perspective(10px)" == "matrix3d(1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, -0.1, 0, 0, 0, 1)"
#guard resolvedTransformText "matrix3d(1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1)" == "matrix(1, 0, 0, 1, 0, 0)"
#guard resolvedTransformText "perspective(none)" == "matrix(1, 0, 0, 1, 0, 0)"
#guard resolvedTransformText "translate(50px) rotate(180deg)" == "matrix(-1, 0, 0, -1, 50, 0)"
#guard resolvedTransformText "none" == "none" && resolvedTransformText "translate(10%)" == "translate(10%)"
#guard (resolvedTransform (some (200, 100)) (parse "translate(10%, 50%)")).map toTextPrecise == some "matrix(1, 0, 0, 1, 20, 50)"
-- every function reads and writes back as its primitive
#guard ["translate(1px, 2px)", "translate3d(1px, 2px, 3px)", "scale(2, 3)", "scale3d(2, 3, 4)", "rotate(30deg)",
  "rotate3d(1, 2, 3, 30deg)", "skew(10deg, 20deg)", "matrix(1, 2, 3, 4, 5, 6)", "perspective(100px)", "perspective(none)"].all fun t =>
  ((readTransforms (parse t)).map fun fs => toText (writeTransforms fs)) == some t
#guard ((readTransforms (parse "translateX(5px) scaleY(2) rotateX(10deg) skewY(3deg) rotateZ(4deg)")).map fun fs => toText (writeTransforms fs)) ==
  some "translate(5px, 0px) scale(1, 2) rotate3d(1, 0, 0, 10deg) skewy(3deg) rotate(4deg)"
-- skewX() and skewY() share no primitive: they accumulate as matrices
-- (css/css-transforms/animation/transform-skew-composition.html)
#guard toTextPrecise (interpolate .transformList
    (accumulate .transformList (parse "skewX(45deg)") (parse "skewY(45deg)"))
    (accumulate .transformList (parse "skewX(45deg)") (parse "skewY(45deg)")) half) == "matrix(1, 1, 0.5, 1.5, 0, 0)"
#guard (readTransforms (parse "translate(1px, 2px, 3px)")).isNone && (readTransforms (parse "foo(1)")).isNone
-- accumulation (css/css-transforms/animation/transform-*-composition.html)
#guard toText (accumulate .transformList (parse "perspective(10px)") (parse "perspective(10px)")) == "perspective(5px)"
#guard toText (accumulate .transformList (parse "scaleX(2)") (parse "scaleX(3)")) == "scalex(4)"
#guard toText (accumulate .transformList (parse "skewX(45deg)") (parse "skewX(30deg)")) == "skewx(75deg)"
#guard toText (accumulate .transformList (parse "translateX(100px)") (parse "translateX(50px)")) == "translatex(150px)"
#guard toText (accumulate .transformList (parse "rotate3d(1, 1, 0, 45deg)") (parse "rotate3d(2, 2, 0, 45deg)")) == "rotate3d(1, 1, 0, 90deg)"
#guard toText (accumulate .transformList (parse "matrix(1, 0, 0, 1, 100, 0)") (parse "matrix(2, 0, 0, 2, 50, 0)")) == "matrix(2, 0, 0, 2, 150, 0)"
#guard at_ .filterList "none" "hue-rotate(20deg)" 300000000 == "hue-rotate(6deg)"
#guard at_ .filterList "blur(6px)" "blur(10px) hue-rotate(180deg)" half == "blur(8px) hue-rotate(90deg)"
#guard at_ .filterList "brightness(0.5)" "none" (one + one) == "brightness(1.5)"
#guard at_ .filterList "grayscale(0)" "grayscale(1)" (one + half) == "grayscale(1)"
#guard at_ .filterList "none" "drop-shadow(rgb(0, 128, 0) 20px 10px)" half == "drop-shadow(rgba(0, 128, 0, 0.5) 10px 5px 0px)"
#guard at_ (.shadowList 4) "none" "rgb(0, 0, 0) 20px 20px 20px 20px" 300000000 == "rgba(0, 0, 0, 0.3) 6px 6px 6px 6px"
#guard at_ (.shadowList 3) "rgb(0, 0, 0) 15px 10px 5px" "rgb(255, 165, 0) -15px -10px 25px" (-300000000) == "rgb(0, 0, 0) 24px 16px 0px"
#guard at_ (.shadowList 4) "rgba(255, 255, 0, 0.5) 10px 20px" "none" 600000000 == "rgba(255, 255, 0, 0.2) 4px 8px 0px 0px"
#guard at_ .filterList "contrast(0)" "contrast()" (one + half) == "contrast(1.5)"
#guard at_ .rotate "none" "30deg" 750000000 == "22.5deg"
#guard at_ .rotate "x 10deg" "x 50deg" half == "x 30deg"
#guard (at_ .rotate "1 -2.5 3.64 100deg" "1 -2.5 3.64 -100deg" 250000000).startsWith "0.22"
#guard (at_ .rotate "1 -2.5 3.64 100deg" "1 -2.5 3.64 -100deg" 250000000).endsWith " 50deg"
#guard at_ .rotate "10deg" "50deg" half == "30deg"
#guard at_ .rotate "none" "x 50deg" half == "x 25deg"
#guard (at_ .rotate "x 10deg" "y 50deg" half).startsWith "0."
#guard at_ .rotate "none" "7 -8 9 360deg" 125000000 == "0.502571 -0.574367 0.646162 45deg"
#guard at_ .rotate "1 0 0 0deg" "0 1 0 10deg" 250000000 == "y 2.5deg"
#guard at_ .rotate "45deg" "-1 1 0 60deg" 0 == "45deg"
#guard at_ .filterList "none" "drop-shadow(rgb(0, 128, 0) 20px 10px)" 0 == "drop-shadow(rgba(0, 0, 0, 0) 0px 0px 0px)"
#guard at_ .rotate "1 1 0 90deg" "0 1 1 135deg" 0 == "0.707107 0.707107 0 90deg"
#guard (at_ .rotate "45deg" "-1 1 0 60deg" 875000000).startsWith "-0.70246 0.70246 0.114452 53.199"
#guard at_ .fontStyle "normal" "oblique 10deg" 300000000 == "oblique 3deg"
#guard at_ .fontStyle "oblique -90deg" "oblique 90deg" half == "normal"
#guard at_ .fontStyle "oblique -90deg" "oblique 90deg" (-one) == "oblique -90deg"
#guard at_ .fontStyle "italic" "oblique 90deg" 400000000 == "italic"
#guard at_ .sides "190% 180% 290% 280%" "90% 80%" 250000000 == "165% 155% 240% 230%"
#guard at_ .sides "100 fill" "200 300 500 fill" one == "200 300 500 fill"
#guard at_ .sides "10" "30" half == "20"
#guard at_ .gridTracks "1fr 1fr 1fr" "2fr auto 2fr" 600000000 == "1.6fr auto 1.6fr"
#guard at_ .gridTracks "minmax(10px, 1fr) minmax(20px, 2fr)" "minmax(20px, 2fr) minmax(30px, auto)" 400000000
  == "minmax(14px, 1.4fr) minmax(24px, 2fr)"
#guard at_ .gridTracks "1fr 1fr" "1fr" 400000000 == "1fr 1fr"
#guard at_ .gridTracks "1fr [a b] 1fr [d] 1fr" "2fr [c] auto 2fr" 400000000 == "1.4fr [ a b ] 1fr [ d ] 1.4fr"
#guard at_ .gridTracks "1fr [a b] 1fr [d] 1fr" "2fr [c] auto 2fr" 600000000 == "1.6fr [ c ] auto 1.6fr"
#guard at_ .gridTracks "[a] 1fr" "2fr [b]" (2 * one) == "3fr [ b ]"
#guard at_ .repeatable "0px 0px, 80px 0px" "40px 40px, 80px 80px, 0px 80px" half
  == "20px 20px, 80px 40px, 0px 40px, 60px 20px, 40px 40px, 40px 40px"
#guard at_ .offsetRotate "auto 10deg" "reverse -130deg" one == "auto 50deg"
#guard at_ .offsetRotate "reverse -170deg" "reverse -130deg" 300000000 == "auto 22deg"
#guard at_ .offsetRotate "auto" "20deg" 400000000 == "auto"
#guard at_ .gridTracks "1fr repeat(2, 2fr 30px) 1fr" "2fr repeat(3, 3fr 40px) 2fr" 400000000 == "1fr repeat(2, 2fr 30px) 1fr"
#guard at_ .gridTracks "repeat(auto-fill, 10px)" "repeat(auto-fill, 30px)" 400000000 == "repeat(auto-fill, 10px)"
#guard at_ .shape "circle(farthest-side at 25px 75%)" "circle(farthest-side at 50px 50%)" 400000000 == "circle(farthest-side at 25px 75%)"
#guard at_ .shape "circle(10px at 25px 75%)" "circle(20px at 50px 50%)" half == "circle(15px at 37.5px 62.5%)"
#guard at_ .ratio "1 / 2" "2 / 1" half == "1 / 1"
#guard at_ .ratio "0.5" "2" 0 == "0.5 / 1"
#guard at_ .shape "inset(10% 20% 30% 40%) border-box" "xywh(20% 50% 60% 20%) border-box" half == "inset(30% 20% 30% 30%) border-box"
#guard at_ .shape "rect(auto auto auto auto)" "rect(80% 20% 20% 80%)" 875000000 == "inset(70%)"
#guard at_ .shape "xywh(0px 10% 100px 40% round 20px)" "rect(20% 50% 200px 20px)" 0 == "inset(10% calc(100% - 100px) 50% 0px round 20px)"
#guard at_ .shape "inset(1px 2px)" "inset(101px 102px 101px 102px)" one == "inset(101px 102px)"
#guard at_ .gapList "repeat(2, rgb(255, 0, 0))" "rgb(0, 0, 255)" 0 == "rgb(255, 0, 0), rgb(255, 0, 0)"
#guard at_ .gapList "repeat(1, 20px)" "repeat(2, 30px, 30px)" 600000000 == "26px, 26px, 26px, 26px"
#guard at_ .gapList "repeat(auto, 20px)" "30px" 400000000 == "repeat(auto, 20px)"
#guard at_ .radius "60px 60px" "160px 160px" 750000000 == "135px"
#guard at_ .radius "10px 20px" "30px 20px" half == "20px"
#guard at_ .radius "10px" "30px" (-one) == "0px"
#guard at_ .radius "20px" "10px 30px" 300000000 == "17px 23px"
#guard at_ .shape "path('M 12 34 S 45 67 89 123')" "path('M 20 26 S 61 51 113 99')" (2 * one) == "path(\"M 28 18 S 77 35 137 75\")"
#guard at_ .shape "path('m 100 400 a 10 20 30 1 0 40 50')" "path('m 300 200 a 50 60 70 0 1 80 90')" 875000000
  == "path(\"M 275 225 A 45 55 65 1 1 350 310\")"
#guard at_ .shape "path('m 10 20 l 40 50 z l 40 60 z m 60 70 l 90 60 z t 70 130')" "path('M 210 220 L 170 190 Z L 90 120 Z M 110 130 L 200 230 Z T 220 220')" 0
  == "path(\"M 10 20 L 50 70 Z L 50 80 Z M 70 90 L 160 150 Z T 140 220\")"
#guard at_ .shape "path('M 0 0 H 200')" "path('M 0 0 L 300 0')" 400000000 == "path('M 0 0 H 200')"
#guard at_ .shape "path('M0 0H 200')" "path('M0 0H 300')" (one + half) == "path(\"M 0 0 H 350\")"
#guard at_ .shape "ray(-10deg farthest-corner at 100% 100px)" "ray(-50deg farthest-corner at 100% 100px)" (2 * one)
  == "ray(-90deg farthest-corner at 100% 100px)"
#guard at_ .shape "url(\"#a\")" "path('M 0 0 H 300')" 600000000 == "path('M 0 0 H 300')"
#guard toText (add .sides (parse "100 200 300 400 fill") (parse "100 fill")) == "200 300 400 500 fill"
#guard at_ .translate "none" "100px" 250000000 == "25px"
#guard at_ .translate "0px" "-100px -50px 100px" 750000000 == "-75px -37.5px 75px"
#guard at_ .translate "none" "8px 80% 800px" 0 == "0px 0%"
#guard at_ .scale "none" "4 3 2" 125000000 == "1.375 1.25 1.125"
#guard at_ .scale "26 17 9" "2 1" 875000000 == "5 3 2"
#guard toText (add .filterList (parse "brightness(0)") (parse "brightness(1.5)")) == "brightness(0) brightness(1.5)"
#guard toText (accumulate .filterList (parse "blur(10px) saturate(0.75)") (parse "blur(90px)")) == "blur(100px) saturate(0.75)"
#guard toText (accumulate .filterList (parse "brightness(0.25)") (parse "brightness(0.5)")) == "brightness(-0.25)"
#guard toText (add .scale (parse "2 1") (parse "3 1")) == "6 1"
#guard toText (add .translate (parse "none") (parse "100px")) == "100px"
#guard toText (add (.shadowList 4) (parse "rgb(10, 20, 30) 1px 2px 3px 4px") (parse "rgb(100, 100, 100) 10px 20px 30px 40px"))
  == "rgb(10, 20, 30) 1px 2px 3px 4px, rgb(100, 100, 100) 10px 20px 30px 40px"
#guard interpolable .generic (parse "10px") (parse "50%")
#guard !interpolable .generic (parse "10px") (parse "auto")
#guard !interpolable .discrete (parse "10px") (parse "20px")
#guard interpolable .visibility (parse "visible") (parse "hidden")
#guard toText (add .generic (parse "10px") (parse "5px")) == "15px"
#guard toText (add .generic (parse "auto") (parse "5px")) == "5px"
#guard toText (add .unit (parse "0.7") (parse "0.6")) == "1"

end Value
end L4Factoidal.Rendering.Animation
