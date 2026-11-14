/-
L4Factoidal.Rendering.CssValues.Numeric — numbers, dimensions, percentages and the math
functions of CSS Values 4 (§5–§7, §10): parsing, type checking (§10.2), simplification
(§10.10.1) and serialisation (§10.14), in exact rational arithmetic.

One function, `numeric`, reads a numeric component value against a request (`<length>`,
`<length-percentage [0,∞]>`, `<integer>` ...). With no context it gives the canonical
specified value; with a context (`Ctx`: font sizes and viewport) it gives the computed value:
absolute and font- or viewport-relative lengths in `px`, angles in `deg`, times in `s`,
and a `calc()` that no longer has anything to wait for as one value.

Not here yet: the trigonometric and exponential functions are type-checked and kept as
written (their values are not rational); `calc-size()`, `random()`, `sibling-index()`.
-/
import L4Factoidal.Rendering.CssValues.Token

namespace L4Factoidal.Rendering.CssValues

/-- The base types of CSS numeric values (CSS Values 4 §10.2). -/
inductive Kind where
  | number | length | percent | angle | time | frequency | resolution | flex
  deriving DecidableEq, Repr, Inhabited

/-- The kind of a unit (lower case). -/
def unitKind (u : String) : Option Kind :=
  if ["px", "em", "rem", "ex", "rex", "cap", "rcap", "ch", "rch", "ic", "ric", "lh", "rlh",
      "vw", "vh", "vi", "vb", "vmin", "vmax", "svw", "svh", "svi", "svb", "svmin", "svmax",
      "lvw", "lvh", "lvi", "lvb", "lvmin", "lvmax", "dvw", "dvh", "dvi", "dvb", "dvmin", "dvmax",
      "cqw", "cqh", "cqi", "cqb", "cqmin", "cqmax", "cm", "mm", "q", "in", "pt", "pc"].contains u then some .length
  else if ["deg", "grad", "rad", "turn"].contains u then some .angle
  else if ["s", "ms"].contains u then some .time
  else if ["hz", "khz"].contains u then some .frequency
  else if ["dpi", "dpcm", "dppx", "x"].contains u then some .resolution
  else if u == "fr" then some .flex
  else none

/-- π to 20 places, as a rational: the only irrational constant of the unit conversions. -/
def piRat : Rat := (314159265358979323846 : Rat) / 100000000000000000000

/-- Units with a fixed ratio to the canonical unit of their kind (CSS Values 4 §6.2, §7):
the factor and the canonical unit. -/
def absFactor (u : String) : Option (Rat × String) :=
  match u with
  | "px" => some (1, "px")
  | "cm" => some ((9600 : Rat) / 254, "px")
  | "mm" => some ((960 : Rat) / 254, "px")
  | "q" => some ((240 : Rat) / 254, "px")
  | "in" => some (96, "px")
  | "pt" => some ((4 : Rat) / 3, "px")
  | "pc" => some (16, "px")
  | "deg" => some (1, "deg")
  | "grad" => some ((9 : Rat) / 10, "deg")
  | "rad" => some (180 / piRat, "deg")
  | "turn" => some (360, "deg")
  | "s" => some (1, "s")
  | "ms" => some ((1 : Rat) / 1000, "s")
  | "hz" => some (1, "hz")
  | "khz" => some (1000, "hz")
  | "dppx" => some (1, "dppx")
  | "x" => some (1, "dppx")
  | "dpi" => some ((1 : Rat) / 96, "dppx")
  | "dpcm" => some ((254 : Rat) / 9600, "dppx")
  | _ => none

/-- What a computed value is computed against (CSS Values 4 §6.1): the element's font size,
the root's, the line height and the viewport, all in px. -/
structure Ctx where
  fontSize : Rat := 16
  rootFontSize : Rat := 16
  lineHeight : Rat := (96 : Rat) / 5
  rootLineHeight : Rat := (96 : Rat) / 5
  viewportW : Rat := 800
  viewportH : Rat := 600
  deriving Repr, Inhabited

def ratMin (a b : Rat) : Rat := if a ≤ b then a else b
def ratMax (a b : Rat) : Rat := if a ≤ b then b else a
def ratAbs (a : Rat) : Rat := if a < 0 then -a else a

/-- px in one font- or viewport-relative unit. `ex`, `ch` and `cap` use the fallbacks of
CSS Values 4 §6.1.1 (0.5em, 0.5em) and 0.7em: the engine does not read font metrics here.
Container query units fall back to the small viewport (§6.1.4 of CSS Containment 3). -/
def Ctx.pxPer (c : Ctx) (u : String) : Option Rat :=
  let vmin := ratMin c.viewportW c.viewportH
  let vmax := ratMax c.viewportW c.viewportH
  match u with
  | "em" => some c.fontSize
  | "rem" => some c.rootFontSize
  | "ex" => some (c.fontSize / 2)
  | "rex" => some (c.rootFontSize / 2)
  | "ch" => some (c.fontSize / 2)
  | "rch" => some (c.rootFontSize / 2)
  | "cap" => some (c.fontSize * 7 / 10)
  | "rcap" => some (c.rootFontSize * 7 / 10)
  | "ic" => some c.fontSize
  | "ric" => some c.rootFontSize
  | "lh" => some c.lineHeight
  | "rlh" => some c.rootLineHeight
  | "vw" | "svw" | "lvw" | "dvw" | "vi" | "svi" | "lvi" | "dvi" | "cqw" | "cqi" => some (c.viewportW / 100)
  | "vh" | "svh" | "lvh" | "dvh" | "vb" | "svb" | "lvb" | "dvb" | "cqh" | "cqb" => some (c.viewportH / 100)
  | "vmin" | "svmin" | "lvmin" | "dvmin" | "cqmin" => some (vmin / 100)
  | "vmax" | "svmax" | "lvmax" | "dvmax" | "cqmax" => some (vmax / 100)
  | _ => none

/-- A calculation tree (CSS Values 4 §10.9). A value has a unit: "" for a number, "%" for
a percentage, else the unit in lower case. -/
inductive Calc where
  | val (v : Rat) (unit : String)
  | sum (terms : List Calc)
  | prod (factors : List Calc)
  | neg (c : Calc)
  | inv (c : Calc)
  | fn (name : String) (args : List Calc)
  /-- `e`, `pi`, `infinity`, `-infinity`, `nan`; a rounding strategy; `none` in `clamp()`. -/
  | kw (name : String)
  -- no `Repr`: deriving it for a nested inductive makes a `partial def`
  deriving Inhabited

/-- The type of a calculation: the exponent of each base type (§10.2). A percentage is
typed as the kind it resolves against when the context mixes them. -/
structure Ty where
  len : Int := 0
  pct : Int := 0
  ang : Int := 0
  tim : Int := 0
  frq : Int := 0
  res : Int := 0
  flx : Int := 0
  deriving DecidableEq, Repr, Inhabited

def Ty.ofKind : Kind → Ty
  | .number => {}
  | .length => { len := 1 }
  | .percent => { pct := 1 }
  | .angle => { ang := 1 }
  | .time => { tim := 1 }
  | .frequency => { frq := 1 }
  | .resolution => { res := 1 }
  | .flex => { flx := 1 }

def Ty.mul (a b : Ty) : Ty :=
  ⟨a.len + b.len, a.pct + b.pct, a.ang + b.ang, a.tim + b.tim, a.frq + b.frq, a.res + b.res, a.flx + b.flx⟩

def Ty.inv (a : Ty) : Ty := ⟨-a.len, -a.pct, -a.ang, -a.tim, -a.frq, -a.res, -a.flx⟩

def mathFunctions : List String :=
  ["calc", "min", "max", "clamp", "round", "mod", "rem", "sin", "cos", "tan", "asin", "acos",
   "atan", "atan2", "pow", "sqrt", "hypot", "log", "exp", "abs", "sign"]

def roundingStrategies : List String := ["nearest", "up", "down", "to-zero"]

/-! ### Parsing -/

abbrev CalcItem := Sum Calc Char

/-- The operands and operators of a calc sum. `+` and `-` need white space on both sides
(§10.1). -/
def calcItems (operand : CV → Option Calc) : List CV → Bool → List CalcItem → Option (List CalcItem)
  | [], _, acc => some acc.reverse
  | cv :: rest, prevWs, acc =>
    match cv with
    | .tok .ws => calcItems operand rest true acc
    | .tok (.delim c) =>
      if c == '+' || c == '-' then
        if prevWs && (rest.head?.map CV.isWs).getD false then calcItems operand rest false (.inr c :: acc) else none
      else if c == '*' || c == '/' then calcItems operand rest false (.inr c :: acc)
      else none
    | _ =>
      match operand cv with
      | some x => calcItems operand rest false (.inl x :: acc)
      | none => none

/-- One product: operands joined by `*` and `/`; the items after it. -/
def calcProduct : Nat → List CalcItem → List Calc → Option (Calc × List CalcItem)
  | 0, _, _ => none
  | fuel + 1, items, acc =>
    match items with
    | .inr '*' :: .inl y :: rest => calcProduct fuel rest (y :: acc)
    | .inr '/' :: .inl y :: rest => calcProduct fuel rest (.inv y :: acc)
    | rest =>
      match acc.reverse with
      | [] => none
      | [x] => some (x, rest)
      | xs => some (.prod xs, rest)

/-- A sum of products from the items. -/
def calcSum : Nat → List CalcItem → List Calc → Option Calc
  | 0, _, _ => none
  | fuel + 1, items, acc =>
    let finish := fun (acc : List Calc) => match acc.reverse with
      | [] => none
      | [x] => some x
      | xs => some (.sum xs)
    match items with
    | [] => finish acc
    | .inl x :: rest =>
      if acc.isEmpty then
        match calcProduct (rest.length + 2) rest [x] with
        | some (p, rest') => calcSum fuel rest' [p]
        | none => none
      else none
    | .inr c :: .inl x :: rest =>
      if acc.isEmpty || !(c == '+' || c == '-') then none
      else match calcProduct (rest.length + 2) rest [x] with
        | some (p, rest') => calcSum fuel rest' ((if c == '-' then .neg p else p) :: acc)
        | none => none
    | _ => none

/-- Split at top-level commas. -/
def splitCommas (cvs : List CV) : List (List CV) :=
  let (groups, last) := cvs.foldl (fun (acc : List (List CV) × List CV) cv =>
    match cv with
    | .tok .comma => (acc.2.reverse :: acc.1, [])
    | cv => (acc.1, cv :: acc.2)) ([], [])
  (last.reverse :: groups).reverse

mutual
  /-- One calc value: a number, a dimension, a percentage, a keyword, a parenthesised sum
  or a math function. -/
  def calcOperand : Nat → CV → Option Calc
    | 0, _ => none
    | fuel + 1, cv =>
      match cv with
      | .tok (.num v _) => some (.val v "")
      | .tok (.pct v) => some (.val v "%")
      | .tok (.dim v _ u) => if (unitKind (lower u)).isSome then some (.val v (lower u)) else none
      | .tok (.ident s) =>
        let k := lower s
        if ["e", "pi", "infinity", "-infinity", "nan"].contains k then some (.kw k) else none
      | .block '(' body => calcExpr fuel body
      | .fn name args =>
        let n := lower name
        if n == "calc" then calcExpr fuel args
        else if mathFunctions.contains n then
          match calcArgs fuel n (splitCommas args) [] with
          | some xs => some (.fn n xs)
          | none => none
        else none
      | _ => none
  /-- A calc sum over component values (white space included). -/
  def calcExpr : Nat → List CV → Option Calc
    | 0, _ => none
    | fuel + 1, cvs =>
      match calcItems (calcOperand fuel) cvs true [] with
      | some items => if items.isEmpty then none else calcSum (items.length + 2) items []
      | none => none
  /-- The comma-separated arguments of a math function. A rounding strategy is the first
  argument of `round()`, and `none` may stand for the ends of `clamp()`. -/
  def calcArgs : Nat → String → List (List CV) → List Calc → Option (List Calc)
    | 0, _, _, _ => none
    | fuel + 1, name, groups, acc =>
      match groups with
      | [] => some acc.reverse
      | g :: rest =>
        let word := match stripWs g with
          | [.tok (.ident s)] => some (lower s)
          | _ => none
        match word with
        | some w =>
          if (name == "round" && acc.isEmpty && roundingStrategies.contains w) || (name == "clamp" && w == "none") then
            calcArgs fuel name rest (.kw w :: acc)
          else match calcExpr fuel g with
            | some x => calcArgs fuel name rest (x :: acc)
            | none => none
        | none =>
          match calcExpr fuel g with
          | some x => calcArgs fuel name rest (x :: acc)
          | none => none
end

/-- The calculation of a math function component value. -/
def Calc.parse (cv : CV) : Option Calc :=
  match cv with
  | .fn name args => if mathFunctions.contains (lower name) then calcOperand (cvSize 64 args + 8) cv else none
  | _ => none

/-! ### Types -/

def allSame : List Ty → Option Ty
  | [] => none
  | t :: rest => if rest.all (· == t) then some t else none

mutual
  /-- The type of a calculation (§10.2), with percentages typed as `pctAs`; `none` when the
  calculation is ill-typed. -/
  def Calc.type (pctAs : Kind) : Nat → Calc → Option Ty
    | 0, _ => none
    | fuel + 1, c =>
      match c with
      | .val _ "" => some {}
      | .val _ "%" => some (Ty.ofKind pctAs)
      | .val _ u => (unitKind u).map Ty.ofKind
      | .kw _ => some {}
      | .neg x => Calc.type pctAs fuel x
      | .inv x => (Calc.type pctAs fuel x).map Ty.inv
      | .sum xs => (typesOf pctAs fuel xs).bind allSame
      | .prod xs => (typesOf pctAs fuel xs).map fun ts => ts.foldl Ty.mul {}
      | .fn name args =>
        let args' := args.filter fun a => match a with
          | .kw k => !(roundingStrategies.contains k || k == "none")
          | _ => true
        match typesOf pctAs fuel args' with
        | none => none
        | some ts =>
          let n := ts.length
          let num : Ty := {}
          match name with
          | "min" | "max" | "hypot" => if n ≥ 1 then allSame ts else none
          | "clamp" => if args.length == 3 && n ≥ 1 then allSame ts else none
          | "round" => if n == 2 then allSame ts else if n == 1 && ts.head? == some num then some num else none
          | "mod" | "rem" => if n == 2 then allSame ts else none
          | "sin" | "cos" | "tan" => if n == 1 && (ts.head? == some num || ts.head? == some (Ty.ofKind .angle)) then some num else none
          | "asin" | "acos" | "atan" => if n == 1 && ts.head? == some num then some (Ty.ofKind .angle) else none
          | "atan2" => if n == 2 && (allSame ts).isSome then some (Ty.ofKind .angle) else none
          | "pow" => if n == 2 && ts.all (· == num) then some num else none
          | "log" => if (n == 1 || n == 2) && ts.all (· == num) then some num else none
          | "sqrt" | "exp" => if n == 1 && ts.all (· == num) then some num else none
          | "abs" => if n == 1 then ts.head? else none
          | "sign" => if n == 1 then some num else none
          | _ => none
  def typesOf (pctAs : Kind) : Nat → List Calc → Option (List Ty)
    | 0, _ => none
    | fuel + 1, xs =>
      match xs with
      | [] => some []
      | x :: rest =>
        match Calc.type pctAs fuel x, typesOf pctAs fuel rest with
        | some t, some ts => some (t :: ts)
        | _, _ => none
end

/-! ### Simplification -/

/-- The order of the terms of a serialised sum (§10.14): number, percentage, dimensions by
unit, then the rest. -/
def termRank : Calc → Nat × String
  | .val _ "" => (0, "")
  | .val _ "%" => (1, "")
  | .val _ u => (2, u)
  | _ => (3, "")

def termLe (a b : Calc) : Bool :=
  let (ra, ua) := termRank a
  let (rb, ub) := termRank b
  ra < rb || (ra == rb && ua ≤ ub)

/-- Add value `v` of unit `u` into the values kept by unit. -/
def addUnit (acc : List (String × Rat)) (u : String) (v : Rat) : List (String × Rat) :=
  if acc.any (·.1 == u) then acc.map fun (u', v') => if u' == u then (u', v' + v) else (u', v')
  else acc ++ [(u, v)]

/-- Bring a value to the canonical unit of its kind when the ratio is fixed, or when the
context gives it. -/
def canonVal (ctx : Option Ctx) (v : Rat) (u : String) : Calc :=
  match absFactor u with
  | some (f, cu) => .val (v * f) cu
  | none =>
    match ctx.bind (·.pxPer u) with
    | some f => .val (v * f) "px"
    | none => .val v u

def negate : Calc → Calc
  | .val v u => .val (-v) u
  | .sum xs => .sum (xs.map fun x => match x with
      | .val v u => .val (-v) u
      | .neg y => y
      | y => .neg y)
  | .neg x => x
  | x => .neg x

/-- Round `a` to a multiple of `b` by a strategy (§10.6.1); `b` is not zero. -/
def roundTo (strategy : String) (a b : Rat) : Rat :=
  let b := ratAbs b
  let q := a / b
  let lower := (q.floor : Rat) * b
  let upper := (q.ceil : Rat) * b
  match strategy with
  | "up" => upper
  | "down" => lower
  | "to-zero" => if a < 0 then upper else lower
  | _ => if a - lower < upper - a then lower else upper

/-- A math function over values that are all of one unit, when its answer is rational. -/
def evalFn (name : String) (strategy : String) (vs : List Rat) (unit : String) : Option Calc :=
  match name, vs with
  | "min", v :: rest => some (.val (rest.foldl ratMin v) unit)
  | "max", v :: rest => some (.val (rest.foldl ratMax v) unit)
  | "clamp", [lo, v, hi] => some (.val (ratMax lo (ratMin v hi)) unit)
  | "abs", [v] => some (.val (ratAbs v) unit)
  | "sign", [v] => some (.val (if v < 0 then -1 else if v == 0 then 0 else 1) "")
  | "round", [a, b] => if b == 0 then none else some (.val (roundTo strategy a b) unit)
  | "round", [a] => some (.val (roundTo strategy a 1) unit)
  | "mod", [a, b] => if b == 0 then none else some (.val (a - b * ((a / b).floor : Rat)) unit)
  | "rem", [a, b] =>
    if b == 0 then none
    else
      let q := a / b
      let t : Rat := if q < 0 then (q.ceil : Rat) else (q.floor : Rat)
      some (.val (a - b * t) unit)
  | _, _ => none

/-- The values of calculations that are all plain values of one unit. -/
def sameUnitValues (xs : List Calc) : Option (List Rat × String) :=
  match xs with
  | .val v u :: rest =>
    if rest.all (fun x => match x with | .val _ u' => u' == u | _ => false) then
      some (v :: rest.filterMap (fun x => match x with | .val v' _ => some v' | _ => none), u)
    else none
  | _ => none

mutual
  /-- Simplify a calculation (§10.10.1): units made canonical, numbers folded, sums and
  products flattened, like terms added, and functions over like values computed. -/
  def Calc.simp (ctx : Option Ctx) : Nat → Calc → Calc
    | 0, c => c
    | fuel + 1, c =>
      match c with
      | .val v u => canonVal ctx v u
      | .kw k => .kw k
      | .neg x => negate (Calc.simp ctx fuel x)
      | .inv x =>
        match Calc.simp ctx fuel x with
        | .val v "" => if v == 0 then .inv (.val v "") else .val (1 / v) ""
        | y => .inv y
      | .sum xs =>
        let ys := (simpList ctx fuel xs).flatMap fun y => match y with
          | .sum zs => zs
          | z => [z]
        let units := ys.foldl (fun acc y => match y with
          | .val v u => addUnit acc u v
          | _ => acc) []
        let others := ys.filter fun y => match y with
          | .val _ _ => false
          | _ => true
        let terms := (units.map fun (u, v) => Calc.val v u) ++ others
        match terms.mergeSort termLe with
        | [] => .val 0 ""
        | [t] => t
        | ts => .sum ts
      | .prod xs =>
        let ys := (simpList ctx fuel xs).flatMap fun y => match y with
          | .prod zs => zs
          | z => [z]
        let n := ys.foldl (fun acc y => match y with
          | .val v "" => acc * v
          | _ => acc) (1 : Rat)
        let rest : List Calc := ys.filter fun y => match y with
          | .val _ "" => false
          | _ => true
        match rest with
        | [] => .val n ""
        | [.val v u] => .val (n * v) u
        | [.sum ts] => .sum (ts.map fun t => match t with
            | .val v u => .val (n * v) u
            | t => if n == 1 then t else .prod [.val n "", t])
        | [.val v u, .inv (.val w u')] =>
          if u == u' && w != 0 then .val (n * v / w) "" else .prod ((if n == 1 then [] else [.val n ""]) ++ rest)
        | rest => .prod ((if n == 1 then [] else [.val n ""]) ++ rest)
      | .fn name args =>
        let ys := simpList ctx fuel args
        let strategy := match ys with
          | .kw k :: _ => if roundingStrategies.contains k then k else "nearest"
          | _ => "nearest"
        let operands := ys.filter fun y => match y with
          | .kw k => !roundingStrategies.contains k
          | _ => true
        match sameUnitValues operands with
        | some (vs, u) =>
          match evalFn name strategy vs u with
          | some r => r
          | none => .fn name ys
        | none => .fn name ys
  def simpList (ctx : Option Ctx) : Nat → List Calc → List Calc
    | 0, xs => xs
    | fuel + 1, xs =>
      match xs with
      | [] => []
      | x :: rest => Calc.simp ctx fuel x :: simpList ctx fuel rest
end

/-! ### Serialisation -/

mutual
  /-- The text of a calculation inside a math function (§10.14). `nested` puts a sum in
  parentheses. -/
  def Calc.css : Nat → Bool → Calc → String
    | 0, _, _ => ""
    | fuel + 1, nested, c =>
      match c with
      | .val v "" => fmtRat v
      | .val v u => fmtRat v ++ u
      | .kw k => k
      | .neg x => "-1 * " ++ Calc.css fuel true x
      | .inv x => "1 / " ++ Calc.css fuel true x
      | .sum xs =>
        let body := sumCss fuel xs true
        if nested then "(" ++ body ++ ")" else body
      | .prod xs => prodCss fuel xs true
      | .fn name args => name ++ "(" ++ argsCss fuel args true ++ ")"
  def sumCss : Nat → List Calc → Bool → String
    | 0, _, _ => ""
    | fuel + 1, xs, first =>
      match xs with
      | [] => ""
      | x :: rest =>
        let piece := match x with
          | .val v u =>
            if first then Calc.css fuel true (.val v u)
            else if v < 0 then " - " ++ Calc.css fuel true (.val (-v) u)
            else " + " ++ Calc.css fuel true (.val v u)
          | .neg y => (if first then "-1 * " else " - ") ++ Calc.css fuel true y
          | y => (if first then "" else " + ") ++ Calc.css fuel true y
        piece ++ sumCss fuel rest false
  def prodCss : Nat → List Calc → Bool → String
    | 0, _, _ => ""
    | fuel + 1, xs, first =>
      match xs with
      | [] => ""
      | x :: rest =>
        let piece := match x with
          | .inv y => (if first then "1 / " else " / ") ++ Calc.css fuel true y
          | y => (if first then "" else " * ") ++ Calc.css fuel true y
        piece ++ prodCss fuel rest false
  def argsCss : Nat → List Calc → Bool → String
    | 0, _, _ => ""
    | fuel + 1, xs, first =>
      match xs with
      | [] => ""
      | x :: rest => (if first then "" else ", ") ++ Calc.css fuel false x ++ argsCss fuel rest false
end

/-- A bound on the recursion over a calculation. -/
def Calc.depth : Nat → Calc → Nat
  | 0, _ => 0
  | fuel + 1, c =>
    match c with
    | .sum xs | .prod xs | .fn _ xs => xs.foldl (fun n x => n + Calc.depth fuel x) 2
    | .neg x | .inv x => Calc.depth fuel x + 2
    | _ => 2

/-- The text of a math function whose calculation is `c` (already simplified): a function
other than `calc()` stands as it is, anything else is wrapped in `calc()`. -/
def Calc.text (c : Calc) : String :=
  let fuel := Calc.depth 64 c + 4
  match c with
  | .fn _ _ => Calc.css fuel false c
  | _ => "calc(" ++ Calc.css fuel false c ++ ")"

/-! ### Reading a numeric component value -/

/-- What a grammar asks of a numeric value: the kind, whether a percentage may stand for
it or mix with it, whether it must be an integer, and the range of a literal. -/
structure NumReq where
  kind : Kind
  allowPct : Bool := false
  integer : Bool := false
  lo : Option Rat := none
  hi : Option Rat := none
  deriving Repr, Inhabited

def NumReq.inRange (r : NumReq) (v : Rat) : Bool :=
  (r.lo.map fun lo => decide (lo ≤ v)).getD true && (r.hi.map fun hi => decide (v ≤ hi)).getD true

def NumReq.clamp (r : NumReq) (v : Rat) : Rat :=
  let v := match r.lo with
    | some lo => ratMax lo v
    | none => v
  match r.hi with
  | some hi => ratMin hi v
  | none => v

/-- Round to the nearest integer, halves towards +∞ (CSS Values 4 §10.11). -/
def roundInt (v : Rat) : Rat := ((v + (1 : Rat) / 2).floor : Rat)

/-- A numeric component value read against `req`. With `ctx = none` the canonical specified
value; with a context the computed value. `none`: not a value of that type. -/
def numeric (ctx : Option Ctx) (req : NumReq) (cv : CV) : Option CV :=
  match cv with
  | .tok (.num v int) =>
    if req.kind == .number then
      if (!req.integer || int) && req.inRange v then some (.tok (.num v int)) else none
    else if req.kind == .length && v == 0 then some (.tok (.dim 0 true "px"))
    else none
  | .tok (.pct v) =>
    if (req.kind == .percent || req.allowPct) && !req.integer && req.inRange v then some (.tok (.pct v)) else none
  | .tok (.dim v int u) =>
    let u := lower u
    if unitKind u == some req.kind && req.kind != .number && req.inRange v then
      match ctx with
      | none => some (.tok (.dim v int u))
      | some c =>
        match canonVal (some c) v u with
        | .val v' u' => some (.tok (.dim v' false u'))
        | _ => none
    else none
  | .fn _ _ =>
    match Calc.parse cv with
    | none => none
    | some c =>
      let pctAs := if req.allowPct then req.kind else .percent
      let fuel := Calc.depth 64 c + 4
      if Calc.type pctAs fuel c != some (Ty.ofKind req.kind) then none
      else
        match Calc.simp ctx fuel c, ctx with
        | .val v u, some _ =>
          -- a computed value that is one value: in range, and an integer where one is wanted
          let v := req.clamp (if req.integer then roundInt v else v)
          some (.tok (if u == "" then .num v req.integer else if u == "%" then .pct v else .dim v false u))
        | s, _ => some (.raw (Calc.text s))
  | _ => none

/-! ### Tests and theorems -/

private def spec (req : NumReq) (s : String) : Option String :=
  match stripWs (CV.parse s) with
  | [cv] => (numeric none req cv).map fun o => serialize [o]
  | _ => none

private def comp (req : NumReq) (s : String) : Option String :=
  match stripWs (CV.parse s) with
  | [cv] => (numeric (some {}) req cv).map fun o => serialize [o]
  | _ => none

private def len : NumReq := { kind := .length }
private def lenPct : NumReq := { kind := .length, allowPct := true }
private def lenPos : NumReq := { kind := .length, lo := some 0 }

#guard spec len "1PX" == some "1px"
#guard spec len "0" == some "0px"
#guard spec len "1" == none
#guard spec len "10%" == none
#guard spec lenPct "10%" == some "10%"
#guard spec lenPos "-1px" == none
#guard spec lenPos "calc(-1px)" == some "calc(-1px)"
#guard comp lenPos "calc(-1px)" == some "0px"
#guard spec len "1in" == some "1in"
#guard comp len "1in" == some "96px"
#guard comp len "2em" == some "32px"
#guard comp len "10vw" == some "80px"
#guard spec len "calc(1px + 2px)" == some "calc(3px)"
#guard comp len "calc(1px + 2px)" == some "3px"
#guard spec len "calc(1px+2px)" == none
#guard spec len "calc(1px + 2)" == none
#guard spec len "calc(2 * 3px)" == some "calc(6px)"
#guard spec len "calc(1em + 2px)" == some "calc(1em + 2px)"
#guard spec len "calc(2px + 1em)" == some "calc(1em + 2px)"
#guard spec len "calc(1em - 2px)" == some "calc(1em - 2px)"
#guard comp len "calc(1em - 2px)" == some "14px"
#guard spec lenPct "calc(50% + 10px)" == some "calc(50% + 10px)"
#guard comp lenPct "calc(10px + 50%)" == some "calc(50% + 10px)"
#guard spec len "calc(50% + 10px)" == none
#guard spec len "min(1px, 2px)" == some "calc(1px)"
#guard spec len "min(1px, 2em)" == some "min(1px, 2em)"
#guard comp len "max(1px, 2em)" == some "32px"
#guard spec len "clamp(1px, 5px, 3px)" == some "calc(3px)"
#guard spec len "calc(1in + 1px)" == some "calc(97px)"
#guard spec len "calc((1px + 2px) * 2)" == some "calc(6px)"
#guard spec len "calc(10px / 2)" == some "calc(5px)"
#guard spec { kind := .number } "calc(10px / 2px)" == some "calc(5)"
#guard spec { kind := .number } "1.50" == some "1.5"
#guard spec { kind := .number, integer := true } "1.5" == none
#guard spec { kind := .number, integer := true } "3" == some "3"
#guard comp { kind := .number, integer := true } "calc(1.5)" == some "2"
#guard spec { kind := .angle } "90DEG" == some "90deg"
#guard comp { kind := .angle } "1turn" == some "360deg"
#guard comp { kind := .time } "500ms" == some "0.5s"
#guard spec { kind := .number } "round(up, 1.2, 1)" == some "calc(2)"
#guard spec { kind := .number } "mod(7, 3)" == some "calc(1)"
#guard spec { kind := .number } "sin(30deg)" == some "sin(30deg)"
#guard spec { kind := .number } "calc(pi)" == some "calc(pi)"

theorem ratMax_ge_left (a b : Rat) : a ≤ ratMax a b := by
  unfold ratMax
  split
  · assumption
  · exact Rat.le_refl

theorem ratMax_ge_right (a b : Rat) : b ≤ ratMax a b := by
  unfold ratMax
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem ratMin_le_left (a b : Rat) : ratMin a b ≤ a := by
  unfold ratMin
  split
  · exact Rat.le_refl
  · rename_i h
    exact Rat.le_of_lt (Rat.not_le.mp h)

theorem ratMin_le_right (a b : Rat) : ratMin a b ≤ b := by
  unfold ratMin
  split
  · assumption
  · exact Rat.le_refl

theorem le_ratMin (a b c : Rat) (ha : c ≤ a) (hb : c ≤ b) : c ≤ ratMin a b := by
  unfold ratMin
  split <;> assumption

/-- Kind: bounds. Says: a value clamped to a range with `lo ≤ hi` is in the range. Does
not say: that a literal out of range is accepted (it is refused at parse time; only a
computed `calc()` is clamped, CSS Values 4 §10.12). -/
theorem NumReq.clamp_inRange (r : NumReq) (v : Rat)
    (h : ∀ lo hi, r.lo = some lo → r.hi = some hi → lo ≤ hi) : r.inRange (r.clamp v) = true := by
  unfold NumReq.inRange NumReq.clamp
  cases hlo : r.lo <;> cases hhi : r.hi
  · simp
  · simp
    exact ratMin_le_left _ _
  · simp
    exact ratMax_ge_left _ _
  · rename_i lo hi
    simp
    exact ⟨le_ratMin _ _ _ (h lo hi hlo hhi) (ratMax_ge_left _ _), ratMin_le_left _ _⟩

/-- Kind: idempotence. Says: clamping twice is clamping once, when `lo ≤ hi`. Does not
say: anything about rounding to an integer. -/
theorem NumReq.clamp_idempotent (r : NumReq) (v : Rat)
    (h : ∀ lo hi, r.lo = some lo → r.hi = some hi → lo ≤ hi) : r.clamp (r.clamp v) = r.clamp v := by
  have hr := NumReq.clamp_inRange r v h
  unfold NumReq.inRange at hr
  generalize r.clamp v = w at hr
  unfold NumReq.clamp
  cases hlo : r.lo <;> cases hhi : r.hi <;> simp [hlo, hhi] at hr ⊢
  · unfold ratMin
    simp
    intro h'
    exact Rat.le_antisymm h' hr
  · unfold ratMax
    simp [hr]
  · unfold ratMax
    simp [hr.1]
    unfold ratMin
    simp
    intro h'
    exact Rat.le_antisymm h' hr.2

end L4Factoidal.Rendering.CssValues
