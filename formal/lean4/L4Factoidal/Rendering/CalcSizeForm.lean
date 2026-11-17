/-
L4Factoidal.Rendering.CalcSizeForm — `calc-size()` (CSS Values 5 §7.1) as a linear form, for
the layout and for interpolation.

A `calc-size(basis, calculation)` whose calculation is linear in `size` (sums, and products
and quotients by numbers, of `size`, lengths in px and percentages) is
`k × size + pct × (percentage basis) + px` over a basis that is a sizing keyword (`auto`,
`min-content`, `max-content`, `fit-content`, `stretch`) or `any` (no size: a length or
percentage basis is put in for `size` when read, and a nested `calc-size()` basis likewise),
so `calc-size(calc-size(auto, size / 2), size * 2)` is `1 × size` over `auto`.

The layout gives `size` its value from the basis (`Layout`, `CSS.Length.calcSize`). Two
forms interpolate (CSS Values 5 §7.1.1) when their bases are the same, or one is `any`: the
coefficients move linearly. A sizing keyword is its own form with `1 × size`, and a length
is a form over `any`, so `auto` interpolates with `calc-size(auto, size * 2)` and `0` with
`calc-size(max-content, size)`. `canonical` writes every value of an animation in one shape,
so that the animation engine's component-wise interpolation of tokens moves the three
coefficients (`Animation.Engine`).

Not here: calculations that are not linear in `size` (`sign(size) * size`), and other units
than px and %: such a value is no form, and keeps its old behaviour.
No imports beyond Lean's core.
-/

namespace L4Factoidal.Rendering.CalcSizeForm

/-- A linear form over a basis. `basis` is `auto`, `min-content`, `max-content`,
`fit-content`, `stretch` or `any`; `pct` is a fraction (50% is 0.5). -/
structure Form where
  basis : String
  k : Float
  pct : Float
  px : Float
  deriving Repr, Inhabited

/-- The basis keywords. -/
def keywords : List String := ["auto", "min-content", "max-content", "fit-content", "stretch"]

/-! ## Tokens -/

inductive T where
  | num (v : Float) (unit : String)
  | ident (s : String)
  /-- `name(`, lower case; `calc(` and a plain `(` are `fn ""`. -/
  | fn (name : String)
  | close | plus | minus | star | slash | comma
  deriving Repr, Inhabited

def isNameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_'

/-- The digits at the start of `cs`, as a mantissa and their count. -/
def digits : List Char → Nat → Nat → Nat × Nat × List Char
  | c :: cs, m, n => if c.isDigit then digits cs (m * 10 + (c.toNat - 48)) (n + 1) else (m, n, c :: cs)
  | [], m, n => (m, n, [])

/-- A number at the start of `cs` (digits, a fraction), and the rest. -/
def number (cs : List Char) : Option (Float × List Char) :=
  let (w, nw, r) := digits cs 0 0
  match r with
  | '.' :: r' =>
    let (f, nf, r'') := digits r' w 0
    if nw + nf == 0 then none else some (Float.ofScientific f true nf, r'')
  | _ => if nw == 0 then none else some (Float.ofNat w, r)

def asciiLower (s : String) : String := s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The tokens of `cs`; `none` at a character this reader does not know. `fuel` is the
length of the text: each step takes at least one character. -/
def tokenize : Nat → List Char → Array T → Option (Array T)
  | 0, _, _ => none
  | _, [], out => some out
  | fuel + 1, c :: cs, out =>
    if c == ' ' || c == '\t' || c == '\n' then tokenize fuel cs out
    else if c == '(' then tokenize fuel cs (out.push (.fn ""))
    else if c == ')' then tokenize fuel cs (out.push .close)
    else if c == '+' then tokenize fuel cs (out.push .plus)
    else if c == '-' && !(match cs with | d :: _ => d.isAlpha | [] => false) then tokenize fuel cs (out.push .minus)
    else if c == '*' then tokenize fuel cs (out.push .star)
    else if c == '/' then tokenize fuel cs (out.push .slash)
    else if c == ',' then tokenize fuel cs (out.push .comma)
    else if c.isDigit || c == '.' then
      match number (c :: cs) with
      | none => none
      | some (v, r) =>
        if r.head? == some '%' then tokenize fuel (r.drop 1) (out.push (.num v "%"))
        else
          let u := r.takeWhile Char.isAlpha
          tokenize fuel (r.drop u.length) (out.push (.num v (asciiLower (String.ofList u))))
    else if c.isAlpha || c == '-' then
      let name := (c :: cs).takeWhile isNameChar
      let r := (c :: cs).drop name.length
      let n := asciiLower (String.ofList name)
      match r with
      | '(' :: r' => tokenize fuel r' (out.push (.fn (if n == "calc" then "" else n)))
      | _ => tokenize fuel r (out.push (.ident n))
    else none

/-! ## Linear expressions -/

/-- A number, or a linear form `k × size + pct + px` (no basis yet). -/
inductive E where
  | n (v : Float)
  | lin (k pct px : Float)
  deriving Repr, Inhabited

def E.lin? : E → Option (Float × Float × Float)
  | .lin k p x => some (k, p, x)
  | .n v => if v == 0 then some (0, 0, 0) else none

def E.add (a b : E) (sign : Float) : Option E :=
  match a, b with
  | .n x, .n y => some (.n (x + sign * y))
  | _, _ => do
    let (k, p, x) ← a.lin?
    let (k', p', x') ← b.lin?
    some (.lin (k + sign * k') (p + sign * p') (x + sign * x'))

def E.mul (a b : E) : Option E :=
  match a, b with
  | .n x, .n y => some (.n (x * y))
  | .n s, .lin k p x | .lin k p x, .n s => some (.lin (s * k) (s * p) (s * x))
  | _, _ => none

def E.div (a b : E) : Option E :=
  match a, b with
  | .n x, .n y => if y == 0 then none else some (.n (x / y))
  | .lin k p x, .n s => if s == 0 then none else some (.lin (k / s) (p / s) (x / s))
  | _, _ => none

/-- Where the reader is: a sum, the rest of a sum after `acc`, a product, the rest of a
product, a factor. -/
inductive Mode where
  | sum | sumRest (acc : E) | term | termRest (acc : E) | factor

/-- A linear expression at the start of `ts` and the rest. `fuel` bounds the steps: each
step takes a token or goes down from a sum to a product to a factor. -/
def expr : Nat → Mode → List T → Option (E × List T)
  | 0, _, _ => none
  | f + 1, .sum, ts => do
    let (a, r) ← expr f .term ts
    expr f (.sumRest a) r
  | f + 1, .sumRest a, ts =>
    match ts with
    | .plus :: r => do let (b, r') ← expr f .term r; let c ← a.add b 1; expr f (.sumRest c) r'
    | .minus :: r => do let (b, r') ← expr f .term r; let c ← a.add b (-1); expr f (.sumRest c) r'
    | _ => some (a, ts)
  | f + 1, .term, ts => do
    let (a, r) ← expr f .factor ts
    expr f (.termRest a) r
  | f + 1, .termRest a, ts =>
    match ts with
    | .star :: r => do let (b, r') ← expr f .factor r; let c ← a.mul b; expr f (.termRest c) r'
    | .slash :: r => do let (b, r') ← expr f .factor r; let c ← a.div b; expr f (.termRest c) r'
    | _ => some (a, ts)
  | f + 1, .factor, ts =>
    match ts with
    | .num v "" :: r => some (.n v, r)
    | .num v "px" :: r => some (.lin 0 0 v, r)
    | .num v "%" :: r => some (.lin 0 (v / 100) 0, r)
    | .ident "size" :: r => some (.lin 1 0 0, r)
    | .minus :: r => do let (a, r') ← expr f .factor r; let c ← a.mul (.n (-1)); some (c, r')
    | .fn "" :: r => do
      let (a, r') ← expr f .sum r
      match r' with
      | .close :: r'' => some (a, r'')
      | _ => none
    | _ => none

/-! ## `calc-size()` -/

/-- `size` of the outer calculation replaced by the form of its basis. -/
def substitute (basis : Form) (k p x : Float) : Form :=
  { basis := basis.basis, k := k * basis.k, pct := k * basis.pct + p, px := k * basis.px + x }

/-- A `calc-size(` at the start of `ts` (after its `fn` token) read to its `)`, and the rest.
`fuel` bounds the nesting and the steps. -/
def calcSize : Nat → List T → Option (Form × List T)
  | 0, _ => none
  | f + 1, ts => do
    let (basis, r) ← match ts with
      | .fn "calc-size" :: r => calcSize f r
      | .ident b :: .comma :: r =>
        if keywords.contains b then some ({ basis := b, k := 1, pct := 0, px := 0 }, .comma :: r)
        else if b == "any" then some ({ basis := "any", k := 0, pct := 0, px := 0 }, .comma :: r)
        else none
      | _ => do
        let (e, r) ← expr (8 * (ts.length + 1)) .sum ts
        let (k, p, x) ← e.lin?
        if k != 0 then none else some ({ basis := "any", k := 0, pct := p, px := x }, r)
    match r with
    | .comma :: r' =>
      let (e, r'') ← expr (8 * (r'.length + 1)) .sum r'
      let (k, p, x) ← e.lin?
      match r'' with
      | .close :: rest => some (substitute basis k p x, rest)
      | _ => none
    | _ => none

/-- The longest text read as a form: the recursion of `expr` and `calcSize` is at most eight
steps a token deep, so this bounds the stack. A longer value is no form. -/
def maxLength : Nat := 1024

/-- The form of a value: a `calc-size()`, a basis keyword (`1 × size`), or a length or
percentage (over `any`). `none` for anything else. -/
def ofText (text : String) : Option Form := do
  if text.length > maxLength then none
  let ts ← tokenize (text.length + 1) text.toList #[]
  match ts.toList with
  | [.ident b] => if keywords.contains b then some { basis := b, k := 1, pct := 0, px := 0 } else none
  | .fn "calc-size" :: r =>
    let (f, rest) ← calcSize (ts.size + 1) r
    if rest.isEmpty then some f else none
  | l => do
    let (e, rest) ← expr (8 * (l.length + 1)) .sum l
    if !rest.isEmpty then none else
    let (k, p, x) ← e.lin?
    if k != 0 then none else some { basis := "any", k := 0, pct := p, px := x }

/-- Whether a text is a `calc-size()` value. -/
def isCalcSize (text : String) : Bool := (asciiLower (String.ofList (text.toList.dropWhile (· == ' ')))).startsWith "calc-size("

/-! ## Writing -/

/-- Six decimals, no exponent, no trailing zeros. -/
def fmt (x : Float) : String :=
  let neg := x < 0
  let a := if neg then -x else x
  let scaled := (a * 1000000).round.toUInt64.toNat
  let whole := scaled / 1000000
  let frac := scaled % 1000000
  let fracText := if frac == 0 then "" else
    let s := toString frac
    let s := String.ofList (List.replicate (6 - s.length) '0') ++ s
    "." ++ String.ofList ((s.toList.reverse.dropWhile (· == '0')).reverse)
  (if neg && scaled != 0 then "-" else "") ++ toString whole ++ fracText

/-- One fixed shape for every form: `calc-size(B, K * size + Xpx + Y%)`. -/
def text (f : Form) : String :=
  "calc-size(" ++ f.basis ++ ", " ++ fmt f.k ++ " * size + " ++ fmt f.px ++ "px + " ++ fmt (f.pct * 100) ++ "%)"

/-- The basis two or more forms share: their one basis that is not `any` (`any` when all
are `any`); `none` when two differ. -/
def commonBasis (fs : List Form) : Option String :=
  match (fs.map (·.basis)).filter (· != "any") |>.eraseDups with
  | [] => some "any"
  | [b] => some b
  | _ => none

/-- The values of an animation of one sizing property in one shape, when one of them is a
`calc-size()` and all of them are forms over one basis: each as `text` over that basis (a
form over `any` takes it, with no `size`). `none` otherwise: the values are left as they are. -/
def canonical (texts : List String) : Option (List String) :=
  if !texts.any isCalcSize then none else do
  let fs ← texts.mapM ofText
  let b ← commonBasis fs
  some (fs.map fun f => text { f with basis := b })

/-- The basis the values of an animation of a sizing property share when one of them is a
`calc-size()` (`canonical`); `none` otherwise. -/
def basisFor (texts : List String) (keywords : Bool := false) : Option String :=
  let sized := texts.any isCalcSize
  if !sized && !keywords then none else do
  let b ← commonBasis (← texts.mapM ofText)
  -- with `interpolate-size: allow-keywords` (`keywords`) and no `calc-size()`, only when a
  -- keyword meets a length: lengths alone interpolate as they always did
  if !sized && b == "any" then none else some b

/-- A value in the one shape over basis `b` (as `canonical` writes it); a value that is no
form over `b` or `any` is left as it is. -/
def normalizeWith (b text' : String) : String :=
  match ofText text' with
  | some f => if f.basis == "any" || f.basis == b then text { f with basis := b } else text'
  | none => text'

/-! ## Theorems and tests -/

/-- Kind: resource bound. Says: with no fuel the reader refuses (a defined answer at the
bound, never a loop). Does not say: that the fuel given is always enough (it is the
token count, times eight for the levels of a sum). -/
theorem expr_zero (m : Mode) (ts : List T) : expr 0 m ts = none := rfl

/-- Kind: property. Says: putting a basis in for `size` keeps the basis (a keyword stays
the basis of the result; a length basis leaves `any`). -/
theorem substitute_basis (b : Form) (k p x : Float) : (substitute b k p x).basis = b.basis := rfl

/-- Kind: property. Says: forms over two different keywords have no common basis, so they
do not interpolate (they are left as they are and flip at 50%). -/
theorem commonBasis_two (a b : Form) (ha : a.basis ≠ "any") (hb : b.basis ≠ "any") (hab : a.basis ≠ b.basis) :
    commonBasis [a, b] = none := by
  have h1 : (a.basis != "any") = true := by simp [ha]
  have h2 : (b.basis != "any") = true := by simp [hb]
  have hne : (b.basis == a.basis) = false := by simp [Ne.symm hab]
  simp [commonBasis, List.filter, h1, h2, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop, hne]

private def show_ (t : String) : String := (ofText t).elim "-" text

#guard show_ "calc-size(auto, size)" == "calc-size(auto, 1 * size + 0px + 0%)"
#guard show_ "calc-size(auto, 2 * size)" == "calc-size(auto, 2 * size + 0px + 0%)"
#guard show_ "calc-size(auto, size * 2)" == "calc-size(auto, 2 * size + 0px + 0%)"
#guard show_ "calc-size(min-content, 0 * size)" == "calc-size(min-content, 0 * size + 0px + 0%)"
#guard show_ "calc-size(fit-content, 30px + (0.5 * size))" == "calc-size(fit-content, 0.5 * size + 30px + 0%)"
#guard show_ "calc-size(any, 50px)" == "calc-size(any, 0 * size + 50px + 0%)"
#guard show_ "calc-size(50px, size)" == "calc-size(any, 0 * size + 50px + 0%)"
#guard show_ "calc-size(12.5%, size * 4)" == "calc-size(any, 0 * size + 0px + 50%)"
#guard show_ "calc-size(37px, size * 2 + 3% + 17px)" == "calc-size(any, 0 * size + 91px + 3%)"
#guard show_ "calc-size(calc-size(auto, size / 2), size * 2)" == "calc-size(auto, 1 * size + 0px + 0%)"
#guard show_ "calc-size(calc-size(100px, size / 2), size * 2)" == "calc-size(any, 0 * size + 100px + 0%)"
#guard show_ "calc-size(calc-size(2in, 30px), 25em)" == "-"
#guard show_ "calc-size(10px, sign(size) * size)" == "-"
#guard show_ "auto" == "calc-size(auto, 1 * size + 0px + 0%)"
#guard show_ "0" == "calc-size(any, 0 * size + 0px + 0%)"
#guard show_ "calc(50% + 10px)" == "calc-size(any, 0 * size + 10px + 50%)"
#guard show_ "calc-size(auto, 1.5 * size + -12.5px + 0%)" == "calc-size(auto, 1.5 * size + -12.5px + 0%)"
#guard canonical ["auto", "calc-size(auto, 2 * size)"] ==
  some ["calc-size(auto, 1 * size + 0px + 0%)", "calc-size(auto, 2 * size + 0px + 0%)"]
#guard canonical ["0", "calc-size(max-content, size)"] ==
  some ["calc-size(max-content, 0 * size + 0px + 0%)", "calc-size(max-content, 1 * size + 0px + 0%)"]
#guard canonical ["auto", "calc-size(min-content, size)"] == none
#guard canonical ["10px", "20px"] == none
#guard basisFor ["auto", "calc-size(auto, 2 * size)"] == some "auto" && basisFor ["auto", "10px"] == none
#guard basisFor ["auto", "10px"] (keywords := true) == some "auto" && basisFor ["5px", "10px"] (keywords := true) == none
#guard normalizeWith "auto" "0" == "calc-size(auto, 0 * size + 0px + 0%)"
#guard fmt 0.1 == "0.1" && fmt (-2.25) == "-2.25" && fmt 100 == "100"

end L4Factoidal.Rendering.CalcSizeForm
