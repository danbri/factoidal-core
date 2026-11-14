/-! Media queries: Media Queries Level 4 (W3C CR) and the preference features of Level 5.

A media query list is read into `Query` values and evaluated against an `Env` in Kleene's
three-valued logic (`Tri`: yes, no, unknown; MQ4 §3.4). What is read (MQ4 §2 to §4):

* the list: queries separated by commas at the top level; brackets nest, and a bracket
  still open at the end of the text is closed there (CSS Syntax §5.4.8);
* a query: `<media-condition>`, or `not`/`only`, a media type, and `and` with a condition
  that has no `or` at its top level. The types `all`, `screen`, `print` match as named;
  other names, the deprecated types included, match nothing (MQ4 §2.3);
* a condition: `not`, `and`, `or` (not mixed at one level), nested parentheses to 32
  levels, and `<general-enclosed>`, which is unknown: a function, or parentheses whose
  content is neither a condition nor a feature this module knows with a value of its type;
* a feature in the boolean form `(name)`, the plain form `(name: value)` with `min-` and
  `max-` on range features, and the range forms `(width >= 600px)`, `(600px > width)`,
  `(400px <= width < 800px)`;
* values: lengths in the absolute units and in `em`, `rem` (16 px, the initial font size,
  MQ4 §1.3), `ex`, `ch` (8 px); ratios `a/b` and `a`; resolutions in `dpi`, `dpcm`, `dppx`,
  `x` and `infinite`; integers; numbers; keywords; and `calc()` over one of these with
  `+`, `-`, `*`, `/` and parentheses.

A query with a syntax error is `not all` (MQ4 §3.2) and the other queries of its list still
count. `parse` and `holds` give none only for a list in which every query has a syntax
error: text that is not a media query list at all. An empty list is true (MQ4 §2.1).

A feature whose value the environment does not give (`Env.width = none`, `Env.dark = none`)
is unknown, and unknown at the top of a query is false, with `not` or without it.

Not read: the viewport units and the font units other than the four above (a feature with
such a value is unknown), comments, strings and escapes in a query, `@custom-media` names,
and the Level 5 features that are not in `kindOf`. -/
namespace L4Factoidal.Rendering.MediaQuery

/-- What a media query is evaluated against. Lengths are CSS pixels. The defaults past
`dark` are those of a desktop screen with a mouse. -/
structure Env where
  medium : String := "screen"
  width : Option Float := none
  height : Option Float := none
  /-- `prefers-color-scheme: dark` holds; `none` when the host does not say. -/
  dark : Option Bool := none
  /-- The screen; `none`: the size of the viewport. -/
  deviceWidth : Option Float := none
  deviceHeight : Option Float := none
  /-- Device pixels per CSS pixel (`resolution`, in dppx). -/
  resolution : Float := 1
  /-- Bits per colour component (`color`): 8 on a 24-bit display. -/
  colorBits : Nat := 8
  colorIndex : Nat := 0
  monochrome : Nat := 0
  grid : Bool := false
  pointer : String := "fine"
  hover : String := "hover"
  anyPointer : String := "fine"
  anyHover : String := "hover"
  scripting : String := "enabled"
  update : String := "fast"
  overflowBlock : String := "scroll"
  overflowInline : String := "scroll"
  colorGamut : String := "srgb"
  dynamicRange : String := "standard"
  invertedColors : String := "none"
  reducedMotion : String := "no-preference"
  reducedTransparency : String := "no-preference"
  contrast : String := "no-preference"
  reducedData : String := "no-preference"
  forcedColors : String := "none"
  displayMode : String := "browser"
  /-- `-webkit-transform-3d`: the engine draws 3D transforms. -/
  transform3d : Bool := false
  deriving Repr, Inhabited

inductive Cmp where
  | lt | le | eq | ge | gt
  deriving Repr, DecidableEq

def Cmp.flip : Cmp → Cmp
  | .lt => .gt | .le => .ge | .eq => .eq | .ge => .le | .gt => .lt

/-- `a cmp b`. Equality is `a <= b` and `b <= a`, so `0` and `-0` are equal and a NaN is
equal to nothing. -/
def Cmp.test (c : Cmp) (a b : Float) : Bool :=
  match c with
  | .lt => a < b | .le => a <= b | .eq => a <= b && b <= a | .ge => b <= a | .gt => b < a

/-- The direction of an ordering comparison: `<`, `<=` rise and `>`, `>=` fall. The two
comparisons of `a < width <= b` must have one direction (MQ4 §2.4.1). -/
def Cmp.rising : Cmp → Option Bool
  | .lt | .le => some true | .gt | .ge => some false | .eq => none

/-- Kind: structure. Says: turning a comparison round twice gives it back. Does not say:
anything about what a comparison tests (`Cmp.flip_test`). -/
theorem Cmp.flip_flip (c : Cmp) : c.flip.flip = c := by cases c <;> rfl

/-- Kind: structure. Says: the flipped comparison tests the operands the other way round,
for every pair of floats, NaN included; so `600px > width` may be read as `width < 600px`.
Does not say: that `Cmp.test` is a total order on floats (it is not, with NaN). -/
theorem Cmp.flip_test (c : Cmp) (a b : Float) : c.flip.test a b = c.test b a := by
  cases c <;> simp [Cmp.flip, Cmp.test, Bool.and_comm]

/-- A truth value of Kleene's strong three-valued logic (MQ4 §3.4). -/
inductive Tri where
  | yes | no | unknown
  deriving Repr, DecidableEq

def Tri.ofBool (b : Bool) : Tri := if b then .yes else .no
def Tri.not : Tri → Tri
  | .yes => .no | .no => .yes | .unknown => .unknown
def Tri.and : Tri → Tri → Tri
  | .no, _ => .no | _, .no => .no | .yes, .yes => .yes | _, _ => .unknown
def Tri.or : Tri → Tri → Tri
  | .yes, _ => .yes | _, .yes => .yes | .no, .no => .no | _, _ => .unknown
/-- The answer at the top of a query: unknown is false. -/
def Tri.holds : Tri → Bool
  | .yes => true | _ => false

/-- Kind: structure. Says: three-valued `not` twice is the identity, unknown included.
Does not say: that `not` flips the answer at the top of a query (unknown stays false). -/
theorem Tri.not_not (a : Tri) : a.not.not = a := by cases a <;> rfl

/-- Kind: structure. Says: three-valued `and` does not depend on the order of its operands.
Does not say: anything about a query that mixes `and` with `or` (that is a syntax error). -/
theorem Tri.and_comm (a b : Tri) : a.and b = b.and a := by cases a <;> cases b <;> rfl

/-- Kind: structure. Says: three-valued `or` does not depend on the order of its operands.
Does not say: that a list of queries is evaluated with it (a list uses the two-valued
answers of its queries). -/
theorem Tri.or_comm (a b : Tri) : a.or b = b.or a := by cases a <;> cases b <;> rfl

/-- Kind: structure. Says: De Morgan's law for `and` holds in the three-valued logic.
Does not say: the excluded middle (`a or not a` is unknown when `a` is). -/
theorem Tri.not_and (a b : Tri) : (a.and b).not = a.not.or b.not := by cases a <;> cases b <;> rfl

/-- Kind: structure. Says: De Morgan's law for `or` holds in the three-valued logic.
Does not say: the excluded middle (`a or not a` is unknown when `a` is). -/
theorem Tri.not_or (a b : Tri) : (a.or b).not = a.not.and b.not := by cases a <;> cases b <;> rfl

/-! ## Tokens and brackets -/

inductive Br where
  | paren | square | curly
  deriving Repr, DecidableEq

inductive Tok where
  /-- An identifier, a number or a dimension, in lower case. -/
  | word (s : String)
  | colon | comma | slash | op (c : Cmp)
  /-- An opening bracket; `fn` is the name of a function (`calc(`). -/
  | opening (fn : Option String) (br : Br)
  | closing (br : Br)
  | other (c : Char)
  deriving Repr, DecidableEq

private def wordChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '%' || c == '+' || c.toNat >= 128
private def space (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c'
private def flush (cur : String) (acc : List Tok) : List Tok := if cur.isEmpty then acc else .word cur :: acc

/-- Tokens of a query list. `>=` and `<=` are one token only with no space inside. Each
step is a tail call. -/
def tokenize : List Char → String → List Tok → List Tok
  | [], cur, acc => (flush cur acc).reverse
  | '<' :: '=' :: cs, cur, acc => tokenize cs "" (.op .le :: flush cur acc)
  | '>' :: '=' :: cs, cur, acc => tokenize cs "" (.op .ge :: flush cur acc)
  | c :: cs, cur, acc =>
    if wordChar c then tokenize cs (cur.push c.toLower) acc
    else if c == '(' then tokenize cs "" (.opening (if cur.isEmpty then none else some cur) .paren :: acc)
    else
      let acc := flush cur acc
      if space c then tokenize cs "" acc
      else if c == ')' then tokenize cs "" (.closing .paren :: acc)
      else if c == '[' then tokenize cs "" (.opening none .square :: acc)
      else if c == ']' then tokenize cs "" (.closing .square :: acc)
      else if c == '{' then tokenize cs "" (.opening none .curly :: acc)
      else if c == '}' then tokenize cs "" (.closing .curly :: acc)
      else if c == ':' then tokenize cs "" (.colon :: acc)
      else if c == ',' then tokenize cs "" (.comma :: acc)
      else if c == '/' then tokenize cs "" (.slash :: acc)
      else if c == '<' then tokenize cs "" (.op .lt :: acc)
      else if c == '>' then tokenize cs "" (.op .gt :: acc)
      else if c == '=' then tokenize cs "" (.op .eq :: acc)
      else tokenize cs "" (.other c :: acc)

/-- Tokens with the brackets matched. (No derived instances: the type is nested.) -/
inductive Node where
  | tok (t : Tok)
  | group (fn : Option String) (br : Br) (items : List Node)

private structure Frame where
  fn : Option String
  br : Br
  items : List Node

/-- The state of the bracket matcher: the open brackets (innermost first, items newest
first), the current query, whether it has a closing bracket that matches nothing, and the
queries before it. -/
private structure Build where
  stack : List Frame := []
  cur : List Node := []
  bad : Bool := false
  done : List (Bool × List Node) := []

private def Build.push (b : Build) (n : Node) : Build :=
  match b.stack with
  | [] => {b with cur := n :: b.cur}
  | f :: rest => {b with stack := {f with items := n :: f.items} :: rest}

private def Build.step (b : Build) (t : Tok) : Build :=
  match t with
  | .opening fn br => {b with stack := {fn, br, items := []} :: b.stack}
  | .closing br =>
    match b.stack with
    | f :: rest =>
      if f.br == br then ({b with stack := rest}).push (.group f.fn f.br f.items.reverse) else {b with bad := true}
    | [] => {b with bad := true}
  | .comma =>
    if b.stack.isEmpty then {b with cur := [], bad := false, done := (b.bad, b.cur.reverse) :: b.done}
    else b.push (.tok t)
  | _ => b.push (.tok t)

private def Build.finish (b : Build) : List (Bool × List Node) :=
  -- Brackets still open at the end are closed there, innermost first.
  let inner := b.stack.foldl (fun (inner : Option Node) f =>
    some (.group f.fn f.br (match inner with | some n => n :: f.items | none => f.items).reverse)) none
  let cur := match inner with | some n => n :: b.cur | none => b.cur
  ((b.bad, cur.reverse) :: b.done).reverse

/-- The queries of a list: for each, whether it has a stray closing bracket, and its
tokens with the brackets matched. A fold over the tokens. -/
def groups (ts : List Tok) : List (Bool × List Node) := (ts.foldl Build.step {}).finish

/-! ## Values -/

/-- A CSS number at the front of a word, and the unit after it. -/
structure Num where
  value : Float
  integer : Bool
  unit : String

private def digitsNat (ds : List Char) : Nat := ds.foldl (fun n d => n * 10 + (d.toNat - 48)) 0

/-- `[+-]? digits [. digits]? [e [+-]? digits]?` then a unit (CSS Syntax §4.3.12). At most
40 digits and a three-digit exponent are read. -/
def number (s : String) : Option Num :=
  let cs := s.toList
  let (neg, cs) := match cs with
    | '-' :: r => (true, r) | '+' :: r => (false, r) | _ => (false, cs)
  let (whole, cs) := cs.span Char.isDigit
  let (frac, cs) := match cs with
    | '.' :: r => let (f, r') := r.span Char.isDigit
                  if f.isEmpty then ([], cs) else (f, r')
    | _ => ([], cs)
  let (exp, cs) : Option Int × List Char := match cs with
    | 'e' :: r =>
      let (eneg, r') := match r with
        | '-' :: q => (true, q) | '+' :: q => (false, q) | _ => (false, r)
      let (ds, r'') := r'.span Char.isDigit
      if ds.isEmpty || ds.length > 3 then (none, cs)
      else (some (if eneg then -(digitsNat ds : Int) else (digitsNat ds : Int)), r'')
    | _ => (none, cs)
  if (whole.isEmpty && frac.isEmpty) || whole.length + frac.length > 40 then none else
  let mantissa := digitsNat (whole ++ frac)
  let e10 : Int := exp.getD 0 - frac.length
  let x := if e10 >= 0 then Float.ofScientific mantissa false e10.toNat
    else Float.ofScientific mantissa true (-e10).toNat
  some {value := if neg then -x else x, integer := frac.isEmpty && exp.isNone, unit := String.ofList cs}

inductive Dim where
  | number | length | resolution
  deriving Repr, DecidableEq

/-- A typed value: a number, a length in CSS px, or a resolution in dppx. -/
structure Qty where
  value : Float
  dim : Dim
  integer : Bool := false

/-- A unit as a dimension and a fraction: the value is `number * mul / div`. Font units are
those of the initial font, 16 px (MQ4 §1.3), with `ex` and `ch` half an em. -/
def unit : String → Option (Dim × Float × Float)
  | "px" => some (.length, 1, 1)
  | "cm" => some (.length, 96, 2.54)
  | "mm" => some (.length, 96, 25.4)
  | "q" => some (.length, 96, 101.6)
  | "in" => some (.length, 96, 1)
  | "pt" => some (.length, 4, 3)
  | "pc" => some (.length, 16, 1)
  | "em" | "rem" => some (.length, 16, 1)
  | "ex" | "ch" => some (.length, 8, 1)
  | "dppx" | "x" => some (.resolution, 1, 1)
  | "dpi" => some (.resolution, 1, 96)
  | "dpcm" => some (.resolution, 2.54, 96)
  | _ => none

def qtyOfWord (s : String) : Option Qty :=
  match number s with
  | none => none
  | some n =>
    if n.unit.isEmpty then some {value := n.value, dim := .number, integer := n.integer}
    else (unit n.unit).map fun (dim, mul, div) => {value := n.value * mul / div, dim}

private def Qty.mul (a b : Qty) : Option Qty :=
  if a.dim == .number then some {value := a.value * b.value, dim := b.dim}
  else if b.dim == .number then some {value := a.value * b.value, dim := a.dim}
  else none
private def Qty.div (a b : Qty) : Option Qty :=
  if b.dim == .number then some {value := a.value / b.value, dim := a.dim} else none
private def Qty.add (a b : Qty) : Option Qty :=
  if a.dim == b.dim then some {value := a.value + b.value, dim := a.dim} else none

/-- The state of a `calc()` sum: the sum so far, the product being built, whether that
product is subtracted, the pending `*` or `/`, and whether an operand comes next. -/
private structure CalcState where
  sum : Option Qty := none
  minus : Bool := false
  prod : Option Qty := none
  divide : Bool := false
  operand : Bool := true

private def CalcState.commit (st : CalcState) : Option Qty :=
  match st.prod with
  | none => none
  | some p =>
    let p := if st.minus then {p with value := -p.value} else p
    match st.sum with
    | none => some p
    | some s => s.add p

private def CalcState.step (sub : Node → Option Qty) (st : CalcState) (n : Node) : Option CalcState :=
  if st.operand then
    match sub n with
    | none => none
    | some q =>
      match st.prod with
      | none => some {st with prod := some q, operand := false}
      | some p => (if st.divide then p.div q else p.mul q).map fun r => {st with prod := some r, operand := false}
  else
    match n with
    | .tok (.other '*') => some {st with divide := false, operand := true}
    | .tok .slash => some {st with divide := true, operand := true}
    | .tok (.word w) =>
      if w == "+" || w == "-" then
        st.commit.map fun s => {sum := some s, minus := w == "-", prod := none, operand := true}
      else none
    | _ => none

/-- A `calc()` sum of products (CSS Values 4 §10.1), with `+` and `-` set off by spaces.
A fold over the operands; the recursion is on the nesting of parentheses, to `fuel`. -/
def calcValue : Nat → List Node → Option Qty
  | 0, _ => none
  | fuel+1, items =>
    let sub := fun (n : Node) => match n with
      | .tok (.word s) => qtyOfWord s
      | .group none .paren inner => calcValue fuel inner
      | .group (some "calc") .paren inner => calcValue fuel inner
      | _ => none
    match items.foldl (fun (st : Option CalcState) n => st.bind (·.step sub n)) (some {}) with
    | some st => if st.operand then none else st.commit
    | none => none

/-- One value: a word, or `calc()`. -/
def qty : List Node → Option Qty
  | [.tok (.word s)] => qtyOfWord s
  | [.group (some "calc") .paren inner] => calcValue 8 inner
  | _ => none

/-- The type of a feature's value. The first five are range features (MQ4 §2.4.3). -/
inductive Kind where
  | length | ratio | resolution | integer | number
  /-- A discrete feature with the values `0` and `1` (`grid`). -/
  | flag
  | keyword (values : List String)

def Kind.isRange : Kind → Bool
  | .length | .ratio | .resolution | .integer | .number => true
  | _ => false

/-- The features this module knows (MQ4 §4 to §9, MQ5 §11, and the two WebKit features
pages still use). -/
def kindOf : String → Option Kind
  | "width" | "height" | "device-width" | "device-height" => some .length
  | "aspect-ratio" | "device-aspect-ratio" => some .ratio
  | "resolution" => some .resolution
  | "color" | "color-index" | "monochrome" => some .integer
  | "-webkit-device-pixel-ratio" => some .number
  | "grid" | "-webkit-transform-3d" => some .flag
  | "orientation" => some (.keyword ["portrait","landscape"])
  | "scan" => some (.keyword ["interlace","progressive"])
  | "update" => some (.keyword ["none","slow","fast"])
  | "overflow-block" => some (.keyword ["none","scroll","paged"])
  | "overflow-inline" => some (.keyword ["none","scroll"])
  | "color-gamut" => some (.keyword ["srgb","p3","rec2020"])
  | "dynamic-range" => some (.keyword ["standard","high"])
  | "inverted-colors" => some (.keyword ["none","inverted"])
  | "pointer" | "any-pointer" => some (.keyword ["none","coarse","fine"])
  | "hover" | "any-hover" => some (.keyword ["none","hover"])
  | "scripting" => some (.keyword ["none","initial-only","enabled"])
  | "prefers-color-scheme" => some (.keyword ["light","dark"])
  | "prefers-reduced-motion" => some (.keyword ["no-preference","reduce"])
  | "prefers-reduced-transparency" => some (.keyword ["no-preference","reduce"])
  | "prefers-contrast" => some (.keyword ["no-preference","more","less","custom"])
  | "prefers-reduced-data" => some (.keyword ["no-preference","reduce"])
  | "forced-colors" => some (.keyword ["none","active"])
  | "display-mode" => some (.keyword ["fullscreen","standalone","minimal-ui","browser",
      "picture-in-picture","window-controls-overlay"])
  | _ => none

/-- A name with `min-` or `max-`: the feature and the comparison the prefix stands for. -/
def prefixed : String → Option (String × Cmp)
  | "-webkit-min-device-pixel-ratio" => some ("-webkit-device-pixel-ratio", .ge)
  | "-webkit-max-device-pixel-ratio" => some ("-webkit-device-pixel-ratio", .le)
  | name =>
    if name.startsWith "min-" then some ((name.drop 4).toString, .ge)
    else if name.startsWith "max-" then some ((name.drop 4).toString, .le)
    else none

private def infinity : Float := 1.0 / 0.0

/-- The value of a feature of kind `k`, as a fraction `num/den` (`den` is 1 but for a
ratio). A length may be negative; a ratio and a resolution may not (MQ4 §2.4.3). -/
def rangeValue (k : Kind) (nodes : List Node) : Option (Float × Float) :=
  -- a literal may not be negative; a math function's negative result is clamped to 0
  -- (CSS Values 4 §10.12: a calculation is clamped to the range the context allows)
  let nonNegative := fun (n : Node) => match qty [n] with
    | some q =>
      if q.dim != .number then none
      else if q.value >= 0 then some q.value
      else match n with
        | .group (some _) _ _ => some 0
        | _ => none
    | none => none
  match k with
  | .length =>
    match qty nodes, nodes with
    | some q, [.tok _] =>
      if q.dim == .length || (q.dim == .number && q.value == 0) then some (q.value, 1) else none
    | some q, _ => if q.dim == .length then some (q.value, 1) else none
    | none, _ => none
  | .ratio =>
    match nodes with
    | [a] => (nonNegative a).map (·, 1)
    | [a, .tok .slash, b] =>
      match nonNegative a, nonNegative b with
      | some x, some y => some (x, y)
      | _, _ => none
    | _ => none
  | .resolution =>
    match nodes with
    | [.tok (.word "infinite")] => some (infinity, 1)
    | _ =>
      match qty nodes with
      | some q => if q.dim == .resolution && q.value >= 0 then some (q.value, 1) else none
      | none => none
  | .integer =>
    match qty nodes with
    | some q => if q.dim == .number && q.integer then some (q.value, 1) else none
    | none => none
  | .number =>
    match qty nodes with
    | some q => if q.dim == .number then some (q.value, 1) else none
    | none => none
  | .flag =>
    match qty nodes with
    | some q => if q.dim == .number && q.integer && (q.value == 0 || q.value == 1) then some (q.value, 1) else none
    | none => none
  | .keyword _ => none

/-! ## Features, conditions, queries -/

inductive Feature where
  /-- A range or flag feature in the boolean form: its value is not zero. -/
  | nonzero (name : String)
  /-- A keyword feature in the boolean form: its value is not `none` (MQ4 §2.4.2). -/
  | present (name : String)
  /-- The value of the feature compared with `num/den`: `feature cmp num/den`. -/
  | range (name : String) (cmp : Cmp) (num den : Float)
  | is (name value : String)

/-- A media condition. `and` and `or` of more than two operands nest to the left. (No
derived instances: the type is recursive.) -/
inductive Cond where
  | feature (f : Feature)
  /-- `<general-enclosed>` (MQ4 §3.1). -/
  | unknown
  | not (c : Cond)
  | and (a b : Cond)
  | or (a b : Cond)

instance : Repr Cond := ⟨fun _ _ => "<media condition>"⟩

/-- One query: `not`, the media type (none: any) and the condition (none: true). A query
with a syntax error is `not all`, with `malformed` set. -/
structure Query where
  negated : Bool := false
  type : Option String := none
  cond : Option Cond := none
  malformed : Bool := false
  deriving Repr

private def boolean (name : String) : Option Cond :=
  match kindOf name with
  | some (.keyword _) => some (.feature (.present name))
  | some _ => some (.feature (.nonzero name))
  | none => none

/-- A feature of the `name: value` form. `min-` and `max-` go with range features only. -/
private def plain (name : String) (value : List Node) : Option Cond :=
  match kindOf name with
  | some (.keyword values) =>
    match value with
    | [.tok (.word v)] => if values.contains v then some (.feature (.is name v)) else none
    | _ => none
  | some k => (rangeValue k value).map fun (n, d) => .feature (.range name .eq n d)
  | none =>
    match prefixed name with
    | some (base, c) =>
      match kindOf base with
      | some k => if k.isRange then (rangeValue k value).map fun (n, d) => .feature (.range base c n d) else none
      | none => none
    | none => none

/-- The name of a range feature, with no prefix, standing alone. -/
private def rangeName : List Node → Option (String × Kind)
  | [.tok (.word n)] =>
    match kindOf n with
    | some k => if k.isRange then some (n, k) else none
    | none => none
  | _ => none

/-- The tokens between the comparison signs, and the signs. A fold. -/
private def splitOps (nodes : List Node) : List (List Node) × List Cmp :=
  let (cur, segs, ops) := nodes.foldl (fun (acc : List Node × List (List Node) × List Cmp) n =>
    match n with
    | .tok (.op c) => ([], acc.1.reverse :: acc.2.1, c :: acc.2.2)
    | _ => (n :: acc.1, acc.2.1, acc.2.2)) ([], [], [])
  ((cur.reverse :: segs).reverse, ops.reverse)

/-- The feature inside one pair of parentheses (MQ4 §2.4, `<media-feature>`). -/
def feature (nodes : List Node) : Option Cond :=
  match nodes with
  | [.tok (.word n)] => boolean n
  | .tok (.word n) :: .tok .colon :: value => plain n value
  | _ =>
    match splitOps nodes with
    | ([a, b], [c]) =>
      -- `width >= 600px`, or `600px <= width` read as `width >= 600px`.
      match rangeName a with
      | some (n, k) => (rangeValue k b).map fun (x, d) => .feature (.range n c x d)
      | none =>
        match rangeName b with
        | some (n, k) => (rangeValue k a).map fun (x, d) => .feature (.range n c.flip x d)
        | none => none
    | ([a, b, d], [c1, c2]) =>
      if c1.rising.isNone || c1.rising != c2.rising then none else
      match rangeName b with
      | some (n, k) =>
        match rangeValue k a, rangeValue k d with
        | some (x1, d1), some (x2, d2) =>
          some (.and (.feature (.range n c1.flip x1 d1)) (.feature (.range n c2 x2 d2)))
        | _, _ => none
      | none => none
    | _ => none

/-- `kw y kw z ...`: the operands, when every joining word is `kw`. Each step is a tail
call. -/
private def operands (kw : String) : List Node → List Node → Option (List Node)
  | [], acc => some acc.reverse
  | .tok (.word k) :: y :: rest, acc => if k == kw then operands kw rest (y :: acc) else none
  | _, _ => none

/-- The most operands `and` or `or` joins at one level. A longer chain is unknown: the
chain is a tree as deep as it is long, and `Cond.eval` uses a frame for each level. -/
def maxOperands : Nat := 32

/-- `<media-condition>` over the tokens of one level (MQ4 §3): `not x`, or `x`, `x and y
and ...`, `x or y or ...` (`or` only where `allowOr`). `sub` reads one `<media-in-parens>`.
A chain of more than `maxOperands` operands is unknown. -/
def condition (sub : Node → Option Cond) (allowOr : Bool) (items : List Node) : Option Cond :=
  match items with
  | [] => none
  | [.tok (.word "not"), x] => (sub x).map .not
  | x :: rest =>
    match sub x with
    | none => none
    | some first =>
      match rest with
      | [] => some first
      | .tok (.word kw) :: _ =>
        if kw == "and" || (kw == "or" && allowOr) then
          match (operands kw rest []).bind (·.mapM sub) with
          | some cs => if cs.length ≥ maxOperands then some .unknown
            else some (cs.foldl (if kw == "and" then Cond.and else Cond.or) first)
          | none => none
        else none
      | _ => none

/-- `<media-in-parens>`: a condition or a feature in parentheses, or `<general-enclosed>`
(a function, or parentheses around anything else), which is unknown. Square and curly
brackets and bare tokens are syntax errors. The recursion is on the nesting of
parentheses; past `fuel` levels the content is unknown. -/
def inParens (fuel : Nat) (n : Node) : Option Cond :=
  match n with
  | .group (some _) _ _ => some .unknown
  | .group none .paren items =>
    match fuel with
    | 0 => some .unknown
    | fuel+1 =>
      match condition (inParens fuel) true items with
      | some c => some c
      | none =>
        match feature items with
        | some c => some c
        | none => some .unknown
  | _ => none

private def reserved : List String := ["and","or","not","only","layer"]

/-- A word that can be a media type: an identifier that is not a reserved word. -/
private def typeName (s : String) : Bool :=
  let start := fun (c : Char) => c.isAlpha || c == '_' || c.toNat >= 128
  let ok := match s.toList with
    | c :: d :: _ => start c || (c == '-' && (start d || d == '-'))
    | [c] => start c
    | [] => false
  ok && s.all (fun c => c.isAlphanum || c == '-' || c == '_' || c.toNat >= 128) && !reserved.contains s

def notAll : Query := {negated := true, type := some "all", malformed := true}

/-- One query of a list (MQ4 §3, `<media-query>`); `bad`: it has a stray closing bracket. -/
def query (bad : Bool) (items : List Node) : Query :=
  if bad then notAll else
  let conditionOnly := match condition (inParens 32) true items with
    | some c => {cond := some c}
    | none => notAll
  let typed := fun (negated : Bool) (t : String) (rest : List Node) =>
    if !typeName t then notAll else
    match rest with
    | [] => {negated, type := some t}
    | .tok (.word "and") :: more =>
      match condition (inParens 32) false more with
      | some c => {negated, type := some t, cond := some c}
      | none => notAll
    | _ => notAll
  match items with
  | .tok (.word "not") :: .tok (.word t) :: rest => typed true t rest
  | .tok (.word "only") :: .tok (.word t) :: rest => typed false t rest
  | .tok (.word t) :: rest => if t == "not" then conditionOnly else typed false t rest
  | _ => conditionOnly

/-- A media query list. An empty or blank list is the empty list. None when every query
of the list has a syntax error: the text is not a media query list. -/
def parse (text : String) : Option (List Query) :=
  let ts := tokenize text.toList "" []
  if ts.isEmpty then some [] else
  let qs := (groups ts).map fun (bad, items) => query bad items
  if qs.all (·.malformed) then none else some qs

/-! ## Evaluation -/

/-- The value of a range or flag feature, as a fraction; none when the environment does
not give it. -/
def Env.quantity (env : Env) : String → Option (Float × Float)
  | "width" => env.width.map (·, 1)
  | "height" => env.height.map (·, 1)
  | "device-width" => (env.deviceWidth <|> env.width).map (·, 1)
  | "device-height" => (env.deviceHeight <|> env.height).map (·, 1)
  | "aspect-ratio" =>
    match env.width, env.height with
    | some w, some h => some (w, h)
    | _, _ => none
  | "device-aspect-ratio" =>
    match env.deviceWidth <|> env.width, env.deviceHeight <|> env.height with
    | some w, some h => some (w, h)
    | _, _ => none
  | "resolution" | "-webkit-device-pixel-ratio" => some (env.resolution, 1)
  | "color" => some (env.colorBits.toFloat, 1)
  | "color-index" => some (env.colorIndex.toFloat, 1)
  | "monochrome" => some (env.monochrome.toFloat, 1)
  | "grid" => some (if env.grid then 1 else 0, 1)
  | "-webkit-transform-3d" => some (if env.transform3d then 1 else 0, 1)
  | _ => none

/-- The value of a keyword feature; none when the environment does not give it, and the
empty string when the feature has no value here (`scan` off a television). -/
def Env.keyword (env : Env) : String → Option String
  | "orientation" =>
    match env.width, env.height with
    | some w, some h => some (if h >= w then "portrait" else "landscape")
    | _, _ => none
  | "scan" => some ""
  | "update" => some env.update
  | "overflow-block" => some env.overflowBlock
  | "overflow-inline" => some env.overflowInline
  | "color-gamut" => some env.colorGamut
  | "dynamic-range" => some env.dynamicRange
  | "inverted-colors" => some env.invertedColors
  | "pointer" => some env.pointer
  | "any-pointer" => some env.anyPointer
  | "hover" => some env.hover
  | "any-hover" => some env.anyHover
  | "scripting" => some env.scripting
  | "prefers-color-scheme" => env.dark.map fun d => if d then "dark" else "light"
  | "prefers-reduced-motion" => some env.reducedMotion
  | "prefers-reduced-transparency" => some env.reducedTransparency
  | "prefers-contrast" => some env.contrast
  | "prefers-reduced-data" => some env.reducedData
  | "forced-colors" => some env.forcedColors
  | "display-mode" => some env.displayMode
  | _ => none

private def gamutRank : String → Nat
  | "srgb" => 1 | "p3" => 2 | "rec2020" => 3 | _ => 0

/-- Whether the feature `name`, with the value `actual`, matches the keyword `asked`. A
wider gamut matches the narrower ones, and every display matches `dynamic-range: standard`
(MQ4 §6.4, MQ5 §6.5). -/
def keywordMatches (name actual asked : String) : Bool :=
  match name with
  | "color-gamut" => gamutRank asked != 0 && gamutRank asked <= gamutRank actual
  | "dynamic-range" => asked == "standard" || actual == asked
  | _ => actual == asked

/-- A feature in `env`. Fractions are compared by cross-multiplying, so `59/80` is equal
to `236/320` exactly and a ratio with a zero denominator needs no division. -/
def Feature.eval (env : Env) : Feature → Tri
  | .nonzero name =>
    match env.quantity name with
    | some (a, _) => .ofBool (a != 0)
    | none => .unknown
  | .present name =>
    match env.keyword name with
    | some v => .ofBool (v != "" && v != "none" && v != "no-preference")
    | none => .unknown
  | .range name c num den =>
    match env.quantity name with
    | some (a, b) => .ofBool (c.test (a * den) (num * b))
    | none => .unknown
  | .is name value =>
    match env.keyword name with
    | some v => .ofBool (keywordMatches name v value)
    | none => .unknown

def Cond.eval (env : Env) : Cond → Tri
  | .feature f => f.eval env
  | .unknown => .unknown
  | .not c => (c.eval env).not
  | .and a b => (a.eval env).and (b.eval env)
  | .or a b => (a.eval env).or (b.eval env)

def typeMatches (env : Env) : Option String → Bool
  | none => true
  | some t => t == "all" || t == env.medium

/-- The three-valued answer of a query: the type and the condition, negated by `not`. -/
def Query.tri (env : Env) (q : Query) : Tri :=
  let v := (Tri.ofBool (typeMatches env q.type)).and (match q.cond with
    | some c => c.eval env
    | none => .yes)
  if q.negated then v.not else v

/-- A query holds. Unknown is false, with `not` or without (MQ4 §3.4). -/
def Query.eval (env : Env) (q : Query) : Bool := (q.tri env).holds

/-- A list holds when it is empty or one of its queries holds. -/
def evalList (env : Env) (qs : List Query) : Bool := qs.isEmpty || qs.any (·.eval env)

/-- Whether `text` holds in `env`; none when it can not be read (`parse`). -/
def holds (env : Env) (text : String) : Option Bool := (parse text).map (evalList env)

/-- `holds`, with a list that can not be read false (an `@media` block that does not apply). -/
def applies (env : Env) (text : String) : Bool := (holds env text).getD false

/-- Kind: policy. Says: a list that applies was read, and its queries hold in the
environment; so a list that can not be read never applies. Does not say: that every list
that is read applies, or that the reading follows the specification (the guards test it). -/
theorem applies_readable (env : Env) (text : String) (h : applies env text = true) :
    ∃ qs, parse text = some qs ∧ evalList env qs = true := by
  unfold applies holds at h
  cases hp : parse text with
  | none => simp [hp] at h
  | some qs => exact ⟨qs, rfl, by simpa [hp] using h⟩

/-- Kind: policy. Says: text that can not be read as a media query list does not apply, in
any environment. Does not say: which texts can not be read. -/
theorem applies_unreadable (env : Env) (text : String) (h : holds env text = none) :
    applies env text = false := by
  simp [applies, h]

/-- Kind: structure. Says: the empty query list holds in every environment (MQ4 §2.1).
Does not say: which text is read as the empty list (`holds_empty` for the empty text). -/
theorem evalList_nil (env : Env) : evalList env [] = true := rfl

/-- Kind: structure. Says: the empty text (a `media` attribute with no value) is read, and
holds in every environment. Does not say: the same of text that is only white space (a
guard tests that). -/
theorem holds_empty (env : Env) : holds env "" = some true := rfl

/-- Kind: structure. Says: `not` before a query negates its three-valued answer, whatever
its type and condition. Does not say: that the two-valued answer flips (it does not when
the answer is unknown; `Query.negate_eval`). -/
theorem Query.negate_tri (env : Env) (q : Query) :
    ({q with negated := !q.negated} : Query).tri env = (q.tri env).not := by
  cases hn : q.negated <;> simp [Query.tri, hn, Tri.not_not]

/-- Kind: structure. Says: when the answer of a query is known, `not` before it flips
whether it holds. Does not say: anything of a query whose answer is unknown: it does not
hold, and neither does its negation. -/
theorem Query.negate_eval (env : Env) (q : Query) (h : q.tri env ≠ .unknown) :
    ({q with negated := !q.negated} : Query).eval env = !q.eval env := by
  unfold Query.eval
  rw [Query.negate_tri]
  cases ht : q.tri env <;> simp_all [Tri.not, Tri.holds]

/-- Kind: structure. Says: a query whose answer is unknown does not hold, and its negation
does not hold either (MQ4 §3.4). Does not say: which queries are unknown. -/
theorem Query.unknown_both_false (env : Env) (q : Query) (h : q.tri env = .unknown) :
    q.eval env = false ∧ ({q with negated := !q.negated} : Query).eval env = false := by
  refine ⟨by simp [Query.eval, h, Tri.holds], ?_⟩
  unfold Query.eval
  rw [Query.negate_tri, h]
  rfl

/-! ## Tests

The cases are those of WPT `css/mediaqueries/test_media_queries.html`, under its names:
`known` is `expression_is_known` (the list `(e), not all and (e)` applies: `e` is true or
false, not unknown) and `readable` is `query_is_parseable` (the query is not `not all` in
the list `screen, q`). -/

private def wide : Env := {width := some 800, height := some 600, dark := some false}
private def narrow : Env := {width := some 400, height := some 700, dark := some true}
/-- The frame of the test: 117 by 76 px, on a 1280 by 800 px screen. -/
private def frame : Env := {width := some 117, height := some 76, deviceWidth := some 1280, deviceHeight := some 800}
private def tall : Env := {width := some 236, height := some 320}
private def flat : Env := {width := some 100, height := some 0}
private def known (env : Env) (e : String) : Bool := applies env s!"({e}), not all and ({e})"
private def readable (q : String) : Bool :=
  match parse ("screen, " ++ q) with
  | some qs => (qs.drop 1).all (!·.malformed)
  | none => false
private def allApply (env : Env) (qs : List String) : Bool := qs.all (applies env ·)
private def noneApply (env : Env) (qs : List String) : Bool := qs.all (!applies env ·)
/-- `expression_should_be_unknown`: readable as `(e)`, and neither true nor false. -/
private def allUnknown (env : Env) (es : List String) : Bool := es.all fun e => readable s!"({e})" && !known env e

#guard holds wide "" == some true && holds wide " \n" == some true && holds wide "all" == some true && holds wide "screen" == some true
#guard holds wide "print" == some false && holds {wide with medium := "print"} "print" == some true
#guard holds wide "(min-width: 500px)" == some true && holds narrow "(min-width: 500px)" == some false
#guard holds wide "(max-width: 600px)" == some false && holds narrow "(max-width: 600px)" == some true
#guard holds wide "screen and (min-width: 31.25em)" == some true && holds narrow "screen and (min-width:31.25em)" == some false
#guard holds wide "only screen and (min-width: 500px) and (max-width: 1000px)" == some true
#guard holds wide "not print" == some true && holds wide "not screen" == some false
#guard holds wide "not screen and (min-width: 900px)" == some true
#guard holds wide "not (min-width: 500px)" == some false && holds narrow "not (min-width: 500px)" == some true
#guard holds wide "print, (min-width: 500px)" == some true && holds narrow "print, (min-width: 500px)" == some false
#guard holds wide "(prefers-color-scheme: dark)" == some false && holds narrow "(prefers-color-scheme: dark)" == some true
#guard holds wide "(prefers-color-scheme: light)" == some true && holds wide "(prefers-color-scheme)" == some true
#guard holds wide "(width >= 600px)" == some true && holds narrow "(width >= 600px)" == some false
#guard holds wide "(400px <= width < 900px)" == some true && holds narrow "(500px <= width < 900px)" == some false
#guard holds wide "(orientation: landscape)" == some true && holds narrow "(orientation: portrait)" == some true
#guard holds wide "tv" == some false && holds wide "speech" == some false && holds wide "SCREEN" == some true
-- `or`, the interaction, display and preference features, with the defaults of `Env`.
#guard holds wide "(min-width: 500px) or (max-width: 100px)" == some true && holds wide "(hover: hover)" == some true
#guard holds wide "(min-resolution: 2dppx)" == some false && holds {wide with resolution := 2} "(min-resolution: 2dppx)" == some true
#guard holds wide "(-webkit-min-device-pixel-ratio: 1.5)" == some false && holds wide "(-webkit-device-pixel-ratio: 1)" == some true
#guard holds wide "(pointer: fine) and (any-hover: hover)" == some true && holds wide "(scripting: enabled)" == some true
#guard holds wide "(prefers-reduced-motion)" == some false && holds wide "(prefers-reduced-motion: no-preference)" == some true
#guard holds {wide with reducedMotion := "reduce"} "(prefers-reduced-motion)" == some true
#guard holds wide "(prefers-contrast: more)" == some false && holds wide "(forced-colors: none)" == some true
#guard holds wide "(display-mode: browser)" == some true && holds wide "(display-mode: standalone)" == some false
#guard holds wide "(color-gamut: srgb)" == some true && holds wide "(color-gamut: p3)" == some false
#guard holds {wide with colorGamut := "p3"} "(color-gamut: srgb)" == some true
#guard holds wide "(dynamic-range: standard)" == some true && holds wide "(dynamic-range: high)" == some false
#guard holds wide "(inverted-colors)" == some false && holds wide "(-webkit-transform-3d)" == some false
-- Units, exponents and `calc()`.
#guard holds wide "(width: 600pt)" == some true && holds wide "(width >= 8.333in)" == some true && holds wide "(width: 8e2px)" == some true
#guard holds wide "(min-width: 100ex)" == some true && holds wide "(min-width: 101ch)" == some false
#guard holds wide "(min-width: calc(10px + 2em))" == some true && holds wide "(min-width: calc(1000px - 2 * (3em + 5px)))" == some false
#guard holds wide "(resolution: infinite)" == some false && holds wide "(max-resolution: infinite)" == some true
-- A query with a syntax error is `not all`; the rest of its list still counts.
#guard holds wide "screen," == some true && holds wide "screen or print, all" == some true && holds wide "print, [x]" == some false
-- Text in which every query has a syntax error is not a media query list: none.
#guard holds wide "screen or print" == none && holds wide "and" == none && holds wide "(min-width: 500px) and" == none
#guard holds wide "@#!" == none && holds wide "(a))" == none && holds wide "only (width)" == none && holds wide "," == none
-- An unknown feature is readable (`<general-enclosed>`) and false, with `not` too.
#guard holds wide "(bogus: 1)" == some false && holds wide "not (bogus: 1)" == some false && holds wide "(width: 1vw)" == some false
-- With no width (the environment does not say), a width query is false, with `not` too.
#guard holds {} "(min-width: 500px)" == some false && holds {} "not (min-width: 500px)" == some false
#guard holds {} "(prefers-color-scheme: dark)" == some false && holds {} "not (prefers-color-scheme: dark)" == some false
#guard holds {} "screen" == some true && holds {} "not print" == some true
#guard !applies wide "(bogus)" && applies wide "screen and (max-width: 900px)"

-- test_media_queries.html: the syntax of a query.
#guard ["(orientation)", "not (orientation)", "all and (orientation)", "not all and (orientation)",
  "only all and (orientation)", "(orientation) and (orientation)", "(orientation) or (orientation)",
  "(orientation) or ((orientation) and ((orientation) or (orientation) or (not (orientation))))",
  "all and (orientation) and (orientation)", "not unknown(width) "].all readable
#guard ["only (orientation)", "not not (orientation)", "all and (orientation) or (orientation)",
  "(orientation) and (orientation) or (orientation)", "(orientation) and not (orientation)",
  "all and color :", "all and color : 1", "screen or (width)", "screen and (width) or (height)",
  "not (width) and not (height)", "not not (width)"].all (!readable ·)
-- The length features: every form and sign of value is known, and `min-`/`max-` go with `:` only.
#guard ["(orientation)", "not (orientation)", "(orientation) or (orientation)", "width", "width : 0", "width > 0px",
  "width >= 0em", "width = -0", "width <= -0cm", "width < 1px", "width: 0.001mm", "width: 100000px",
  "min-width : -0", "max-width: -0", "min-width: -1px", "0px < width < 100000px", "0px >= width >= 100000px",
  "device-width > -0.00001mm", "device-height: -100000em", "0px <= width < 0px", "0px > height >= 0px"].all (known wide)
#guard allUnknown wide ["min-width", "max-height", "min-width > -0", "max-width = -0", "min-device-width >= -1px",
  "0px = width = 100000px", "width > = 0px", "height < = 0px", "0px < width > 0px", "0px : width : 0px",
  "0px = width = 0px", "0px <= width >= 0px"]
#guard allApply frame ["all and (width: 117px)", "all and (height = 76px)", "all and (min-width: 116px)",
  "all and (max-height: 77px)", "all and (min-width: 6em)", "all and (max-width: 9em)", "(0px < width <= 117px)",
  "(117px >= width > 0px)", "(116px < width)", "(116px < width < 118px)", "(117px >= width > 116px)",
  "(device-width: 1280px)", "(device-height >= 800px)", "all and (height)", "all and (width)"]
#guard noneApply frame ["all and (width: 118px)", "all and (width = 116px)", "all and (min-width: 118px)",
  "all and (max-width: 116px)", "all and (min-width: 9em)", "all and (max-width: 6em)", "(0px < width < 117px)",
  "(117px > width > 0px)", "(width > 117px)", "(116px >= width)", "(118px > width > 117px)"]
#guard applies flat "all and (width)" && !applies flat "all and (height)" && applies {flat with deviceHeight := some 800} "all and (device-height)"
-- a negative calc() in a ratio is clamped to 0; a degenerate ratio is valid
#guard holds wide "(min-aspect-ratio: calc(-1)/2)" == some true && holds wide "(min-aspect-ratio: 0/2)" == some true
#guard holds wide "(min-aspect-ratio: -1/2)" == none || holds wide "(min-aspect-ratio: -1/2)" == some false
-- Orientation and the ratios (the frame at 236 by 320 px: 59/80).
#guard allApply tall ["(orientation)", "not all and (orientation: landscape)", "(orientation: portrait)",
  "(aspect-ratio: 59/80)", "(aspect-ratio: 177/240)", "(aspect-ratio: 5900/8000)", "(aspect-ratio)",
  "(min-aspect-ratio: 58/80)", "(min-aspect-ratio: 59/81)", "(max-aspect-ratio: 59/80)", "(max-aspect-ratio: 59/79)"]
#guard noneApply tall ["(orientation: landscape)", "(aspect-ratio: 58/80)", "(aspect-ratio: 59/81)",
  "(aspect-ratio: 5901/8000)", "(aspect-ratio: 5900/7999)", "(min-aspect-ratio: 60/80)", "(max-aspect-ratio: 59/81)"]
#guard allApply frame ["(device-aspect-ratio: 1280/800)", "not all and (device-aspect-ratio: 1281/800)",
  "(device-aspect-ratio)", "(min-device-aspect-ratio: 1280/801)", "(max-device-aspect-ratio: 1280/799)"]
#guard ["max-aspect-ratio: 1/1", "device-aspect-ratio: 1  /1", "max-aspect-ratio: 1  / \t\n1", "max-aspect-ratio: 1/\r1",
  "max-aspect-ratio: 1", "max-aspect-ratio: 0.5", "max-aspect-ratio: 1.0/1.0", "max-aspect-ratio: 0/1",
  "max-aspect-ratio: 1/0", "device-aspect-ratio: 0/0", "orientation: portrait"].all (known wide)
#guard allUnknown wide ["min-orientation", "max-orientation: landscape", "min-aspect-ratio", "max-device-aspect-ratio",
  "max-aspect-ratio: -1/1", "max-aspect-ratio: 1/-1", "device-aspect-ratio: -1/-1", "max-aspect-ratio: invalid",
  "max-aspect-ratio: 1 / invalid", "max-aspect-ratio: 1 invalid"]
-- Colour, resolution, scan and grid.
#guard allApply frame ["(color: 8)", "(max-color: 9)", "(min-color: 1)", "all and (color)", "not all and (monochrome)",
  "(color-index: 0)", "(max-color-index: 157)", "(resolution: 96dpi)", "(resolution: 1x)", "(min-resolution: 95dpi)",
  "not all and (min-resolution: 97dpi)", "(min-resolution: 37dpcm)", "(max-resolution: 39dpcm)",
  "not all and (scan)", "not all and (scan: progressive)", "(grid: 0)"]
#guard noneApply frame ["(color: 7)", "(color: 9)", "all and (monochrome)", "not all and (color)", "(min-color-index: 1)",
  "(resolution: 97dpi)", "(resolution: 95dpi)", "(max-resolution: 37dpcm)", "(scan)", "(scan: interlace)", "(grid)",
  "(grid: 1)", "(grid: 2)", "(grid: -1)"]
#guard ["color: 327", "min-monochrome: 0", "max-color-index: -1", "resolution: 3dpi", "min-resolution:3dpi",
  "max-resolution: 3.4dpi", "resolution\t: 120dpcm", "resolution: 1.5x", "resolution: 0dpi", "resolution: calc(6x / 2)",
  "scan", "scan:interlace", "grid", "grid: 1"].all (known wide)
#guard allUnknown wide ["max-color", "min-monochrome", "color: 1.0", "color: 1/1", "resolution: -3dpi", "min-scan:interlace",
  "scan: 1", "max-scan: progressive", "min-grid", "max-grid: 1", "grid: 2", "grid: -1"]
-- Errors: a bracket open at the end is closed there; a bad query is `not all`.
#guard allApply frame ["(orientation", "all,(orientation:", "not all and (grid", "all,(grid", ",all", "all,", ",all,",
  "all,badmedium", "badmedium,all", "all,(badexpression)", "(badexpression),all", "all,[badsyntax]", "[badsyntax],all"]
#guard noneApply frame ["not all and (orientation", "(orientation:", "(orientation:)", "(orientation:,all",
  "only all and (grid", "(grid", "(grid,all", ",badmedium,", "(badexpression),badmedium", "badmedium,[badsyntax]",
  "[badsyntax],badmedium", "all and min-color : 1", "(bogus)", "not all and (bogus)", "only all and (bogus)"]
-- The Level 4 keyword features.
#guard ["overflow-block", "overflow-block: none", "overflow-block: paged", "overflow-inline: scroll", "update",
  "update: slow", "hover", "hover: none", "any-hover: hover", "pointer", "pointer: coarse", "any-pointer: none"].all (known wide)
#guard allUnknown wide ["overflow-block: optional-paged", "overflow-block: some-random-invalid-thing",
  "overflow-block = scroll", "overflow-block < scroll", "update: some-random-invalid-thing"]
#guard applies wide "(overflow-block)" != applies wide "(overflow-block: none)" && applies wide "(update)" != applies wide "(update: none)"
#guard applies wide "(hover)" == applies wide "(hover: hover)" && applies wide "(pointer)" != applies wide "(pointer: none)"
-- `or`, nesting, `not` and the three-valued logic (the frame at 100 by 0 px).
#guard allApply flat ["(width) or (height)", "(height) or (width) or (height)", "((width))", "(((((width)))))", "(((((width",
  "not (height)", "not ((width) and (height))", "not ((unknown) and (height))", "((unknown) or (width))",
  "(width) or (not ((unknown) and (width)))", "(width) or (not ((unknown) or (width)))",
  "(width) and (not ((unknown) and (height)))", "(width) or (not ((unknown) or (height)))",
  "not (unknown(width) and (height))"]
#guard noneApply flat ["(height) or (height)", "((height))", "not (width)", "not ((width) or (height))",
  "not ((width) and (not (height)))", "(unknown)", "not (unknown)", "((unknown) and (width))",
  "not ((unknown) and (width))", "((unknown) and (height))", "not ((unknown) or (width))", "((unknown) or (height))",
  "not ((unknown) or (height))", "(width) and (not ((unknown) and (width)))", "(width) and (not ((unknown) or (width)))",
  "(width) and (not ((unknown) or (height)))", "unknown(width)", "not unknown(width)", "not (unknown(width) or (height))"]
-- A chain past `maxOperands` is unknown: it does not apply, and neither does its negation.
private def chain (n : Nat) : String := " and ".intercalate (List.replicate n "(width)")
#guard applies flat (chain 30) && !applies flat ("not (" ++ chain 30 ++ ")")
#guard !applies flat (chain 40) && !applies flat ("not (" ++ chain 40 ++ ")") && (holds flat (chain 40)).isSome

end L4Factoidal.Rendering.MediaQuery
