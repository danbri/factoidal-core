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

Theorems: at progress 0 the result is the start value and at 1 the end value
(`interpolate_zero`, `interpolate_one`); a value interpolated with itself is itself
(`interpolate_self`); a non-negative kind gives no negative number (`nonNegative_range`);
a number token interpolates between its ends for a progress in [0, 1] (`lerpTok_num`,
with `Fix.lerp_between`).
-/
import L4Factoidal.Rendering.Animation.Fix

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

/-- A length-percentage from its two parts, in its shortest form. -/
def mkLp (px pct : Int) : Tok :=
  if pct == 0 then .dim px "px" else if px == 0 then .dim pct "%" else .lp px pct

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
      match headGroup rest with
      | some (g, k) => out := out.push g; rest := rest.drop k
      | none => out := out.push t; rest := r
  return out.toList

/-- The tokens of a computed value. -/
def parse (text : String) : Value := collapse (tokenize text)

/-! ## Writing -/

/-- A colour channel as a whole number 0 to 255. -/
def channel (c : Int) : Int := Fix.clamp 0 255 (Fix.roundDiv c Fix.scale)

def tokText : Tok → String
  | .num n => Fix.formatCss n
  | .dim n u => Fix.formatCss n ++ u
  | .lp px pct =>
    if px < 0 then s!"calc({Fix.formatCss pct}% - {Fix.formatCss (-px)}px)"
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

/-- Whether two values interpolate component-wise for the kind (Web Animations 1 §5.2;
CSS Transitions 2 §3.2 starts no transition between values that do not, unless
`transition-behavior: allow-discrete`). -/
def interpolable (k : Kind) (a b : Value) : Bool :=
  match k with
  | .discrete | .avoid _ => false
  | .visibility => a == b || a == [.ident "visible"] || b == [.ident "visible"]
  | _ => (lerpList half a b).isSome

/-- The value at progress `p` between `a` and `b` (Web Animations 1 §5.2). At 0 it is
`a`, at 1 it is `b`; equal values stay; shapes that agree move component-wise; others
flip at 50%. -/
def interpolate (k : Kind) (a b : Value) (p : Int) : Value :=
  if p == 0 then a
  else if p == one then b
  else if a == b then a
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
      match lerpList p a b with
      | some r => finish k r
      | none => if p < half then a else b

/-! ## Addition and accumulation (Web Animations 1 §5.2, CSS Values 4 §3.2, §3.3) -/

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

/-- `value` added to `underlying` (composite operation `add` and `accumulate`, for
values that add component-wise): the sum, or `value` when they do not add (Web
Animations 1 §5.2: "not additive" values replace). -/
def add (k : Kind) (underlying value : Value) : Value :=
  match k with
  | .discrete | .visibility | .avoid _ => value
  | _ => match addList underlying value with
    | some r => finish k r
    | none => value

/-! ## Theorems -/

/-- Kind: interpolation end point. Says: at progress 0 the animated value is the start
value, for every kind and every pair of values. Does not say: anything near 0. -/
theorem interpolate_zero (k : Kind) (a b : Value) : interpolate k a b 0 = a := by
  simp [interpolate]

/-- Kind: interpolation end point. Says: at progress 1 the animated value is the end
value, for every kind and every pair of values. Does not say: anything near 1. -/
theorem interpolate_one (k : Kind) (a b : Value) : interpolate k a b one = b := by
  simp [interpolate, one, Fix.scale]

/-- Kind: interpolation identity. Says: a value interpolated with itself is itself, at
every progress and for every kind. Does not say: more. -/
theorem interpolate_self (k : Kind) (a : Value) (p : Int) : interpolate k a a p = a := by
  unfold interpolate
  split
  · rfl
  · split
    · rfl
    · simp

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
  · split
    · exact hb
    · split
      · exact ha
      · simp only
        split
        · intro t ht
          simp only [finish, List.mem_map] at ht
          obtain ⟨t', _, rfl⟩ := ht
          exact clampTok0_nonNeg t'
        · split
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
#guard at_ .generic "0px" "100%" half == "calc(50% + 0px)" || at_ .generic "0px" "100%" half == "50%"
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
#guard interpolable .generic (parse "10px") (parse "50%")
#guard !interpolable .generic (parse "10px") (parse "auto")
#guard !interpolable .discrete (parse "10px") (parse "20px")
#guard interpolable .visibility (parse "visible") (parse "hidden")
#guard toText (add .generic (parse "10px") (parse "5px")) == "15px"
#guard toText (add .generic (parse "auto") (parse "5px")) == "5px"
#guard toText (add .unit (parse "0.7") (parse "0.6")) == "1"

end Value
end L4Factoidal.Rendering.Animation
