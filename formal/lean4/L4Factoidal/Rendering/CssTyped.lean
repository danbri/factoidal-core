/-
L4Factoidal.Rendering.CssTyped — CSS Typed OM 1: what a CSS value is as a typed object
(§5 "reify"), what a typed object is as CSS text (§6 serialisation), and the arithmetic
and types of numeric values (§4.3).

The page's classes (`CSSUnitValue`, `CSSMathSum`, `CSSKeywordValue` ...) hold their fields;
every decision about them is here. A numeric value is the calculation tree of
`CssValues.Numeric` (`Calc`), so `calc()` in a property and a `CSSMathSum` in a script are
one type.

Wire forms. From the page to here, a typed value is CSS-like text read by the CSS
tokenizer: `u(3.14 "px")`, `sum(a, b)`, `product(a, b)`, `negate(a)`, `invert(a)`,
`min(a, b)`, `max(a, b)`, `clamp(a, b, c)`. From here to the page, a value is JSON.
-/
import L4Factoidal.Rendering.CssValues.Declaration
import L4Factoidal.Rendering.CssRegister

namespace L4Factoidal.Rendering.CssTyped
open L4Factoidal.Rendering.CssValues

/-! ### Units -/

/-- The unit of a `CSSUnitValue` as the unit of a `Calc` value: `number` is "", `percent`
is "%", any other must be a CSS unit. -/
def calcUnit (u : String) : Option String :=
  let l := lower u
  if l == "number" then some ""
  else if l == "percent" then some "%"
  else if (unitKind l).isSome then some l
  else none

def typedUnit (u : String) : String :=
  if u == "" then "number" else if u == "%" then "percent" else u

/-! ### Reading the page's wire form -/

/-- A typed numeric value from its wire form. The recursion is on the nesting. -/
def ofWire : Nat → CV → Option Calc
  | 0, _ => none
  | fuel + 1, cv =>
    match cv with
    | .fn name args =>
      let n := lower name
      if n == "u" then
        match stripWs args with
        | [.tok (.num v _), .tok (.str u)] => (calcUnit u).map fun cu => .val v cu
        | [.tok (.ident k), .tok (.str u)] =>
          -- a value that is not finite: kept as a keyword of the calculation
          if (calcUnit u).isSome && ["infinity", "-infinity", "nan"].contains (lower k) then some (.kw (lower k)) else none
        | _ => none
      else
        let parts := (splitCommas args).map stripWs
        let children := parts.mapM fun p => match p with
          | [x] => ofWire fuel x
          | _ => none
        match n, children with
        | "sum", some xs => if xs.isEmpty then none else some (.sum xs)
        | "product", some xs => if xs.isEmpty then none else some (.prod xs)
        | "negate", some [x] => some (.neg x)
        | "invert", some [x] => some (.inv x)
        | "min", some xs => if xs.isEmpty then none else some (.fn "min" xs)
        | "max", some xs => if xs.isEmpty then none else some (.fn "max" xs)
        | "clamp", some [a, b, c] => some (.fn "clamp" [a, b, c])
        | _, _ => none
    | _ => none

def parseWire (s : String) : Option Calc :=
  match stripWs (CV.parse s) with
  | [cv] => ofWire (maxNesting + 2) cv
  | _ => none

/-! ### JSON for the page -/

def jsonString (s : String) : String :=
  "\"" ++ s.toList.foldl (fun out c =>
    if c == '"' then out ++ "\\\""
    else if c == '\\' then out ++ "\\\\"
    else if c == '\n' then out ++ "\\n"
    else if c.toNat < 0x20 then out ++ "\\u00" ++ (if c.toNat < 16 then "0" else "") ++ hexDigits c.toNat
    else out.push c) "" ++ "\""

/-- A number for JSON: fifteen significant digits. -/
def jsonNumber (v : Rat) : String := fmtRatSig 15 v

/-- A calculation as the JSON of a typed numeric value (§5.4 "reify a math expression").
The recursion is on the nesting. -/
def calcJson : Nat → Calc → String
  | 0, _ => "null"
  | fuel + 1, c =>
    let list := fun (t : String) (xs : List Calc) =>
      "{\"t\":\"" ++ t ++ "\",\"a\":[" ++ ",".intercalate (xs.map (calcJson fuel)) ++ "]}"
    match c with
    | .val v u => "{\"t\":\"u\",\"v\":" ++ jsonNumber v ++ ",\"u\":" ++ jsonString (typedUnit u) ++ "}"
    | .kw k =>
      let v := if k == "infinity" then "\"Infinity\"" else if k == "-infinity" then "\"-Infinity\"" else if k == "nan" then "\"NaN\""
        else if k == "pi" then jsonNumber piRat else if k == "e" then "2.718281828459045" else "0"
      "{\"t\":\"u\",\"v\":" ++ v ++ ",\"u\":\"number\"}"
    | .sum xs => list "sum" xs
    | .prod xs => list "product" xs
    | .neg x => list "negate" [x]
    | .inv x => list "invert" [x]
    | .fn name args =>
      let operands := args.filter fun a => match a with
        | .kw k => !roundingStrategies.contains k
        | _ => true
      list name operands

def calcFuel (c : Calc) : Nat := Calc.depth 64 c + 4

/-- The text between `var()` functions, and the functions: the members of a
`CSSUnparsedValue` (§5.2), as JSON. -/
def unparsedJson : Nat → List CV → String
  | 0, _ => "[]"
  | fuel + 1, cvs =>
    let flush := fun (pending : List CV) (out : List String) =>
      if pending.isEmpty then out else jsonString (rawText' pending.reverse) :: out
    let (pending, out) := cvs.foldl (fun (acc : List CV × List String) cv =>
      let (pending, out) := acc
      match cv with
      | .fn name args =>
        if lower name == "var" then
          let groups := splitCommas args
          let varName := match stripWs (groups.headD []) with
            | [.tok (.ident s)] => s
            | _ => ""
          let fallback := match groups with
            | _ :: fb :: more =>
              let all := more.foldl (fun acc g => acc ++ [CV.tok .comma] ++ g) fb
              "{\"t\":\"unparsed\",\"a\":" ++ unparsedJson fuel all ++ "}"
            | _ => "null"
          ([], ("{\"t\":\"var\",\"v\":" ++ jsonString varName ++ ",\"f\":" ++ fallback ++ "}") :: flush pending out)
        else (cv :: pending, out)
      | cv => (cv :: pending, out)) ([], [])
    "[" ++ ",".intercalate (flush pending out).reverse ++ "]"
where
  /-- The text of values as written, white space kept (not trimmed). -/
  rawText' (cvs : List CV) : String :=
    String.join (cvs.map fun cv => match cv with
      | .tok t => t.css
      | cv => rawText [cv])

def styleJson (text : String) : String := "{\"t\":\"style\",\"c\":" ++ jsonString text ++ "}"

/-- The typed value of one CSS value text (§5 "reify a CSS value"): a keyword, a unit
value, a math value, an unparsed value, an image, or a value with no typed form (kept as
its text). -/
def reify (text : String) : String :=
  let cvs := CV.parse text
  if hasFn "var" 32 cvs then "{\"t\":\"unparsed\",\"a\":" ++ unparsedJson (cvSize 64 cvs + 2) cvs ++ "}"
  else
    match stripWs cvs with
    | [.tok (.ident s)] => "{\"t\":\"kw\",\"v\":" ++ jsonString s ++ "}"
    | [.tok (.num v _)] => calcJson 2 (.val v "")
    | [.tok (.pct v)] => calcJson 2 (.val v "%")
    | [.tok (.dim v _ u)] =>
      if (unitKind (lower u)).isSome then calcJson 2 (.val v (lower u)) else styleJson text
    | [.tok (.url _)] => "{\"t\":\"image\",\"c\":" ++ jsonString text ++ "}"
    | [.fn name args] =>
      if lower name == "url" then "{\"t\":\"image\",\"c\":" ++ jsonString text ++ "}"
      else
        match Calc.parse (.fn name args) with
        | some c =>
          -- a math function is a math value; `calc(x)` of one value is a sum of one
          let c := match c with
            | .val v u => Calc.sum [.val v u]
            | .kw k => Calc.sum [.kw k]
            | c => c
          calcJson (calcFuel c) c
        | none => styleJson text
    | _ => styleJson text

/-- Whether a property's value has no typed form of its own (§5.1: "a property with no
reification rule"): a shorthand, or a longhand of one or two values (`{1,2}` at the top of
its grammar: the corner radii, `scroll-snap-align` and the like). Such a value is a keyword
only when it is a CSS-wide keyword, an unparsed value when it has `var()`, else its text. -/
def opaqueProperty (property : String) : Bool :=
  match lookup (propertyName property) with
  | some row => !row.longhands.isEmpty || (trimText row.grammar).endsWith "{1,2}"
  | none => false

/-- The value of a custom property with no registration (or the universal syntax) as a
typed value: always an unparsed value (CSS Properties and Values API 1 §6.1). -/
def unparsedOf (text : String) : String :=
  let cvs := CV.parse text
  "{\"t\":\"unparsed\",\"a\":" ++ unparsedJson (cvSize 64 cvs + 2) cvs ++ "}"

/-- The typed value of a value text of a property; a custom property's is unparsed. -/
def reifyFor (property text : String) : String :=
  let cvs := CV.parse text
  if isCustom property then unparsedOf text
  else if opaqueProperty property && !hasFn "var" 32 cvs && (wideKeyword (stripWs cvs)).isNone then styleJson text
  else reify text

/-- The data types of a registered syntax whose values are numeric values (§6.2). -/
def numericTypes : List String :=
  ["length", "number", "percentage", "length-percentage", "integer", "angle", "time", "resolution"]

/-- One value of a syntax component as a typed value (§6.2): a numeric value as `reify`
reads it, an image or url as an image, a custom identifier or keyword as a keyword, and
anything else (a colour, a string, a transform) as a value with no typed form. -/
def reifyComponent (g : G) (item : List CV) : String :=
  let text := rawText item
  match g with
  | .ref name _ _ =>
    if numericTypes.contains name then reify text
    else if name == "image" || name == "url" then "{\"t\":\"image\",\"c\":" ++ jsonString text ++ "}"
    else if name == "custom-ident" then
      match stripWs item with
      | [.tok (.ident s)] => "{\"t\":\"kw\",\"v\":" ++ jsonString s ++ "}"
      | _ => styleJson text
    else styleJson text
  | .kw _ =>
    match stripWs item with
    | [.tok (.ident s)] => "{\"t\":\"kw\",\"v\":" ++ jsonString s ++ "}"
    | _ => styleJson text
  | _ => styleJson text

/-- The typed values of a registered custom property's value by its syntax (§6.2), as a
JSON array: one value, or one for each item of a `+` or `#` list; an unparsed value for the
universal syntax, a CSS-wide keyword, or a value of no alternative. -/
def reifyBySyntax (syn text : String) : String :=
  let cvs := CV.parse text
  let top := stripWs cvs
  match CssRegister.syntaxGrammar syn with
  | some (some g) =>
    let alts := match g with
      | .oneOf xs => xs
      | g => [g]
    match (wideKeyword top), alts.find? (fun a => (matchAll (env none) a top).isSome) with
    | none, some (.rep inner _ _ comma) =>
      let items : List (List CV) :=
        if comma then (splitCommas top).map stripWs else (top.filter fun cv => !cv.isWs).map fun cv => [cv]
      "[" ++ ",".intercalate (items.map fun item => reifyComponent inner item) ++ "]"
    | none, some a => "[" ++ reifyComponent a top ++ "]"
    | _, _ => "[" ++ unparsedOf text ++ "]"
  | _ => "[" ++ unparsedOf text ++ "]"

/-- Whether a value is one a property registered with `syn` takes as its specified value
(§2.3): a CSS-wide keyword, a value with `var()`, or a value of the syntax. -/
def syntaxAccepts (syn text : String) : Bool :=
  let cvs := CV.parse text
  let top := stripWs cvs
  if top.isEmpty then false
  else if (wideKeyword top).isSome || hasFn "var" 32 cvs then true
  else match CssRegister.syntaxGrammar syn with
    | some (some g) => (matchAll (env none) g top).isSome
    | some none => !badCustomValue top
    | none => false

#guard syntaxAccepts "<length>" "10px" && !syntaxAccepts "<length>" "red" && syntaxAccepts "<length>" "inherit"
#guard syntaxAccepts "<color> | none" "none" && syntaxAccepts "*" "if(){}" && !syntaxAccepts "<angle>" "10px"

#guard reifyBySyntax "<length>" "10px" == "[{\"t\":\"u\",\"v\":10,\"u\":\"px\"}]" ||
  (reifyBySyntax "<length>" "10px").startsWith "[{\"t\":\"u\""
#guard (reifyBySyntax "<length>+" "10px 20px").splitOn "\"t\":\"u\"" |>.length |> (· == 3)
#guard (reifyBySyntax "<color>" "rgb(1, 2, 3)").startsWith "[{\"t\":\"style\""
#guard (reifyBySyntax "*" "if(){}").startsWith "[{\"t\":\"unparsed\""
#guard (reifyBySyntax "<custom-ident>" "foo").startsWith "[{\"t\":\"kw\""
#guard (reifyFor "--x" "10px").startsWith "{\"t\":\"unparsed\""

/-- The typed values of a list-valued property's text: one for each comma-separated item. -/
def reifyAll (text : String) : String :=
  let cvs := CV.parse text
  if hasFn "var" 32 cvs then "[" ++ reify text ++ "]"
  else "[" ++ ",".intercalate ((splitCommas cvs).map fun g => reify (rawText g)) ++ "]"

/-! ### Types (§4.3.2) -/

/-- The type of a numeric value: the exponents of the base types, and the percent hint. -/
structure NumType where
  ty : Ty := {}
  hint : Option Kind := none
  deriving DecidableEq, Repr, Inhabited

def kindName : Kind → String
  | .number => "number" | .length => "length" | .percent => "percent" | .angle => "angle"
  | .time => "time" | .frequency => "frequency" | .resolution => "resolution" | .flex => "flex"

/-- "Apply the percent hint" (§4.3.2): the percent exponent moves to the hinted type. -/
def applyHint (t : NumType) (hint : Kind) : NumType :=
  let p := t.ty.pct
  let ty := { t.ty with pct := 0 }
  let ty := match hint with
    | .length => { ty with len := ty.len + p }
    | .angle => { ty with ang := ty.ang + p }
    | .time => { ty with tim := ty.tim + p }
    | .frequency => { ty with frq := ty.frq + p }
    | .resolution => { ty with res := ty.res + p }
    | .flex => { ty with flx := ty.flx + p }
    | _ => { ty with pct := p }
  { ty := ty, hint := some hint }

/-- The non-percent base types with a non-zero exponent. -/
def nonPercentKinds (t : Ty) : List Kind :=
  (if t.len != 0 then [Kind.length] else []) ++ (if t.ang != 0 then [Kind.angle] else []) ++
  (if t.tim != 0 then [Kind.time] else []) ++ (if t.frq != 0 then [Kind.frequency] else []) ++
  (if t.res != 0 then [Kind.resolution] else []) ++ (if t.flx != 0 then [Kind.flex] else [])

/-- "Add two types" (§4.3.2). -/
def addTypes (a b : NumType) : Option NumType :=
  let (a, b) := match a.hint, b.hint with
    | some h, none => (a, applyHint b h)
    | none, some h => (applyHint a h, b)
    | _, _ => (a, b)
  if a.hint != b.hint then none
  else if a.ty == b.ty then some a
  else if a.ty.pct != 0 || b.ty.pct != 0 then
    -- a percentage with one other type: the hint makes them equal
    let candidates := (nonPercentKinds a.ty ++ nonPercentKinds b.ty)
    candidates.findSome? fun k =>
      let a' := applyHint a k
      let b' := applyHint b k
      if a'.ty == b'.ty then some a' else none
  else none

/-- "Multiply two types" (§4.3.2). -/
def mulTypes (a b : NumType) : Option NumType :=
  let (a, b) := match a.hint, b.hint with
    | some h, none => (a, applyHint b h)
    | none, some h => (applyHint a h, b)
    | _, _ => (a, b)
  if a.hint != b.hint then none else some { ty := a.ty.mul b.ty, hint := a.hint }

/-- The type of a numeric value (§4.3.2 "create a type" and the types of math values).
The recursion is on the nesting. -/
def numType : Nat → Calc → Option NumType
  | 0, _ => none
  | fuel + 1, c =>
    let fold := fun (f : NumType → NumType → Option NumType) (xs : List Calc) =>
      match xs.mapM (numType fuel) with
      | some (t :: ts) => ts.foldlM f t
      | _ => none
    match c with
    | .val _ "" => some {}
    | .val _ "%" => some { ty := Ty.ofKind .percent }
    | .val _ u => (unitKind u).map fun k => { ty := Ty.ofKind k }
    | .kw _ => some {}
    | .neg x => numType fuel x
    | .inv x => (numType fuel x).map fun t => { t with ty := t.ty.inv }
    | .sum xs => fold addTypes xs
    | .prod xs => fold mulTypes xs
    | .fn _ args => fold addTypes args

def typeJson (t : NumType) : String :=
  let entry := fun (name : String) (v : Int) => if v == 0 then [] else ["\"" ++ name ++ "\":" ++ toString v]
  let fields := entry "length" t.ty.len ++ entry "angle" t.ty.ang ++ entry "time" t.ty.tim ++
    entry "frequency" t.ty.frq ++ entry "resolution" t.ty.res ++ entry "flex" t.ty.flx ++ entry "percent" t.ty.pct ++
    (match t.hint with
      | some h => ["\"percentHint\":\"" ++ kindName h ++ "\""]
      | none => [])
  "{" ++ ",".intercalate fields ++ "}"

/-! ### Serialisation (§6) -/

/-- The CSS text of a typed numeric value: a unit value is its number and unit; a math
value is a math function. -/
def numericCss (c : Calc) : String :=
  match c with
  | .val v u => fmtRat v ++ u
  | c => Calc.text c

/-! ### Arithmetic (§4.3.1) -/

/-- The values of a list when all are unit values of one unit. -/
def sameUnits (xs : List Calc) : Option (List Rat × String) := sameUnitValues xs

/-- `add`: unit values of one unit are added; otherwise a sum, when the types add. -/
def add (xs : List Calc) : Option Calc :=
  let xs := match xs with
    | .sum ys :: rest => ys ++ rest
    | xs => xs
  match sameUnits xs with
  | some (vs, u) => some (.val (vs.foldl (· + ·) 0) u)
  | none =>
    let c := Calc.sum xs
    if (numType (calcFuel c) c).isSome then some c else none

/-- `mul`: numbers are multiplied, a number scales one unit value; otherwise a product. -/
def mul (xs : List Calc) : Option Calc :=
  let xs := match xs with
    | .prod ys :: rest => ys ++ rest
    | xs => xs
  let numbers := xs.filterMap fun x => match x with
    | .val v "" => some v
    | _ => none
  let others := xs.filter fun x => match x with
    | .val _ "" => false
    | _ => true
  let n := numbers.foldl (· * ·) 1
  match others with
  | [] => some (.val n "")
  | [.val v u] => if numbers.isEmpty then some (.val v u) else some (.val (n * v) u)
  | _ =>
    let c := Calc.prod xs
    if (numType (calcFuel c) c).isSome then some c else none

def negateValue : Calc → Calc
  | .val v u => .val (-v) u
  | .neg x => x
  | x => .neg x

def invertValue : Calc → Option Calc
  | .val v "" => if v == 0 then none else some (.val (1 / v) "")
  | .inv x => some x
  | x => some (.inv x)

/-- `min` and `max`: of unit values of one unit, the least or greatest; otherwise a
`CSSMathMin` or `CSSMathMax`, when the types add. -/
def extreme (name : String) (xs : List Calc) : Option Calc :=
  match sameUnits xs with
  | some (v :: vs, u) => some (.val (vs.foldl (if name == "min" then ratMin else ratMax) v) u)
  | _ =>
    let c := Calc.fn name xs
    if (numType (calcFuel c) c).isSome then some c else none

/-- `to(unit)`: a unit value in another unit of its kind, through the canonical unit. -/
def toUnit (c : Calc) (unit : String) : Option Calc :=
  match calcUnit unit, Calc.simp none (calcFuel c) c with
  | some target, .val v u =>
    if u == target then some (.val v u)
    else
      match absFactor target, absFactor u with
      | some (ft, canon), some (_, canon') => if canon == canon' && ft != 0 then some (.val (v / ft) target) else none
      | _, _ => none
  | _, _ => none

/-- `equals`: the same structure with the same values and units. -/
def calcEq : Nat → Calc → Calc → Bool
  | 0, _, _ => false
  | fuel + 1, a, b =>
    let lists := fun (xs ys : List Calc) => xs.length == ys.length && (xs.zip ys).all fun (x, y) => calcEq fuel x y
    match a, b with
    | .val v u, .val w u' => v == w && u == u'
    | .kw k, .kw k' => k == k'
    | .sum xs, .sum ys => lists xs ys
    | .prod xs, .prod ys => lists xs ys
    | .neg x, .neg y => calcEq fuel x y
    | .inv x, .inv y => calcEq fuel x y
    | .fn n xs, .fn m ys => n == m && lists xs ys
    | _, _ => false

/-- A list-valued property (§2.2): its grammar is a comma-separated list at the top. -/
def listValued (property : String) : Bool :=
  match lookup (propertyName property) with
  | some row => (trimText row.grammar).toList.getLast? == some '#'
  | none => false

/-! ### The page's protocol -/

def calcAnswer (c : Option Calc) : String :=
  match c with
  | some c => calcJson (calcFuel c) c
  | none => ""

/-- The flow-relative axis shorthands that take one typed value for both sides, as their
longhands do (`margin-block`, `padding-inline`, `inset-block`, `border-block-width` ...). -/
def axisShorthand (p : String) : Bool :=
  ["margin-", "padding-", "inset-", "border-"].any (fun pre => p.startsWith pre) &&
    (["block", "inline"].any fun axis =>
      ["", "-width", "-style", "-color"].any fun post =>
        ["margin-", "padding-", "inset-", "border-"].any fun pre => p == pre ++ axis ++ post)

/-- A shorthand that takes no typed value in `StylePropertyMap.set()` (only a string, a
CSS-wide keyword or an unparsed value): every shorthand but the axis ones. -/
def refusesTyped (p : String) : Bool :=
  ((lookup p).map (!·.longhands.isEmpty)).getD false && !axisShorthand p

/-- The operations of the page's typed values, as text: the fields of `q` are separated by
U+0000, the first is the verb. "" is a TypeError (a SyntaxError for `parse`).

- `reify` text → the JSON of the typed value; `reifyall` text → a JSON list
- `css` wire → the CSS text of a numeric value
- `unit` name → "1" when it is a unit a `CSSUnitValue` can have
- `islist` property → "1" when the property is list-valued
- `type` wire → the JSON of its type
- `add` | `sub` | `mul` | `div` | `min` | `max`, wire, wire ... → the JSON of the result
- `to` wire unit; `equals` wire wire ... → "1" or "0"
- `parse` text → the JSON of the numeric value (`CSSNumericValue.parse`) -/
def typedOp (q : String) : String :=
  match q.splitOn "\x00" with
  | ["reify", text] => reify text
  | ["reifyall", text] => reifyAll text
  | ["reifyp", property, text] => reifyFor property text
  | ["reifys", syn, text] => reifyBySyntax syn text
  | ["matchs", syn, text] => if syntaxAccepts syn text then "1" else "0"
  | ["isshorthand", property] => if refusesTyped (propertyName property) then "1" else "0"
  | ["css", wire] => ((parseWire wire).map numericCss).getD ""
  | ["unit", name] => if (calcUnit name).isSome then "1" else "0"
  | ["islist", property] => if listValued property then "1" else "0"
  | ["type", wire] => ((parseWire wire).bind fun c => (numType (calcFuel c) c).map typeJson).getD ""
  | ["to", wire, unit] => calcAnswer ((parseWire wire).bind (toUnit · unit))
  | ["parse", text] =>
    match stripWs (CV.parse text) with
    | [.tok (.num v _)] => calcAnswer (some (.val v ""))
    | [.tok (.pct v)] => calcAnswer (some (.val v "%"))
    | [.tok (.dim v _ u)] => if (unitKind (lower u)).isSome then calcAnswer (some (.val v (lower u))) else ""
    | [.fn name args] => calcAnswer ((Calc.parse (.fn name args)).map fun c => match c with
        | .val v u => Calc.sum [.val v u]
        | c => c)
    | _ => ""
  | verb :: wires =>
    match wires.mapM parseWire with
    | none => ""
    | some xs =>
      match verb, xs with
      | "add", xs => calcAnswer (add xs)
      | "sub", x :: rest => calcAnswer (add (x :: rest.map negateValue))
      | "mul", xs => calcAnswer (mul xs)
      | "div", x :: rest => calcAnswer ((rest.mapM invertValue).bind fun inv => mul (x :: inv))
      | "min", xs => calcAnswer (extreme "min" xs)
      | "max", xs => calcAnswer (extreme "max" xs)
      | "equals", x :: rest => if rest.all (fun y => calcEq (calcFuel x) x y) then "1" else "0"
      | _, _ => ""
  | _ => ""

/-! ### Tests and theorems -/

#guard reify "auto" == "{\"t\":\"kw\",\"v\":\"auto\"}"
#guard reify "3.14px" == "{\"t\":\"u\",\"v\":3.14,\"u\":\"px\"}"
#guard reify "-3.14%" == "{\"t\":\"u\",\"v\":-3.14,\"u\":\"percent\"}"
#guard reify "0" == "{\"t\":\"u\",\"v\":0,\"u\":\"number\"}"
#guard reify "calc(0em + 0px)" == "{\"t\":\"sum\",\"a\":[{\"t\":\"u\",\"v\":0,\"u\":\"em\"},{\"t\":\"u\",\"v\":0,\"u\":\"px\"}]}"
#guard reify "calc(-3.14em)" == "{\"t\":\"sum\",\"a\":[{\"t\":\"u\",\"v\":-3.14,\"u\":\"em\"}]}"
#guard reify "1px 2px" == "{\"t\":\"style\",\"c\":\"1px 2px\"}"
#guard reify " var(--A)" == "{\"t\":\"unparsed\",\"a\":[\" \",{\"t\":\"var\",\"v\":\"--A\",\"f\":null}]}"
#guard reify "var(--A, 1px)" == "{\"t\":\"unparsed\",\"a\":[{\"t\":\"var\",\"v\":\"--A\",\"f\":{\"t\":\"unparsed\",\"a\":[\" 1px\"]}}]}"
#guard reify "url(\"a.png\")" == "{\"t\":\"image\",\"c\":\"url(\\\"a.png\\\")\"}"
#guard reifyFor "margin" "1px" == "{\"t\":\"style\",\"c\":\"1px\"}"
#guard reifyFor "margin" "inherit" == "{\"t\":\"kw\",\"v\":\"inherit\"}"
#guard reifyFor "border-top-left-radius" "0px" == "{\"t\":\"style\",\"c\":\"0px\"}"
#guard reifyFor "width" "1px" == "{\"t\":\"u\",\"v\":1,\"u\":\"px\"}"
#guard typedOp "isshorthand\x00margin" == "1"
#guard typedOp "isshorthand\x00margin-top" == "0"
#guard typedOp "isshorthand\x00margin-block" == "0" && typedOp "isshorthand\x00border-inline-color" == "0"
#guard typedOp "isshorthand\x00scroll-margin" == "1" && typedOp "isshorthand\x00margin-blocks" == "0"
#guard reifyAll "1s, 2s" == "[{\"t\":\"u\",\"v\":1,\"u\":\"s\"},{\"t\":\"u\",\"v\":2,\"u\":\"s\"}]"
#guard typedOp "css\x00u(3.14 \"px\")" == "3.14px"
#guard typedOp "css\x00u(-3.14 \"percent\")" == "-3.14%"
#guard typedOp "css\x00u(1 \"number\")" == "1"
#guard typedOp "css\x00sum(u(0 \"px\"), u(0 \"em\"))" == "calc(0px + 0em)"
#guard typedOp "css\x00sum(u(1 \"px\"), negate(u(2 \"em\")))" == "calc(1px - 2em)"
#guard typedOp "css\x00product(u(2 \"number\"), u(1 \"px\"))" == "calc(2 * 1px)"
#guard typedOp "css\x00min(u(1 \"px\"), u(2 \"em\"))" == "min(1px, 2em)"
#guard typedOp "css\x00u(1 \"bogus\")" == ""
#guard typedOp "unit\x00PX" == "1"
#guard typedOp "unit\x00bogus" == "0"
#guard typedOp "islist\x00transition-duration" == "1"
#guard typedOp "islist\x00width" == "0"
#guard typedOp "type\x00u(1 \"px\")" == "{\"length\":1}"
#guard typedOp "type\x00u(1 \"number\")" == "{}"
#guard typedOp "type\x00sum(u(1 \"px\"), u(1 \"percent\"))" == "{\"length\":1,\"percentHint\":\"length\"}"
#guard typedOp "type\x00sum(u(1 \"px\"), u(1 \"s\"))" == ""
#guard typedOp "type\x00product(u(1 \"px\"), u(1 \"px\"))" == "{\"length\":2}"
#guard typedOp "add\x00u(1 \"px\")\x00u(2 \"px\")" == "{\"t\":\"u\",\"v\":3,\"u\":\"px\"}"
#guard typedOp "add\x00u(1 \"px\")\x00u(2 \"em\")" == "{\"t\":\"sum\",\"a\":[{\"t\":\"u\",\"v\":1,\"u\":\"px\"},{\"t\":\"u\",\"v\":2,\"u\":\"em\"}]}"
#guard typedOp "add\x00u(1 \"px\")\x00u(2 \"s\")" == ""
#guard typedOp "sub\x00u(5 \"px\")\x00u(2 \"px\")" == "{\"t\":\"u\",\"v\":3,\"u\":\"px\"}"
#guard typedOp "mul\x00u(5 \"px\")\x00u(2 \"number\")" == "{\"t\":\"u\",\"v\":10,\"u\":\"px\"}"
#guard typedOp "div\x00u(5 \"px\")\x00u(2 \"number\")" == "{\"t\":\"u\",\"v\":2.5,\"u\":\"px\"}"
#guard typedOp "div\x00u(5 \"px\")\x00u(0 \"number\")" == ""
#guard typedOp "max\x00u(5 \"px\")\x00u(2 \"px\")" == "{\"t\":\"u\",\"v\":5,\"u\":\"px\"}"
#guard typedOp "to\x00u(1 \"in\")\x00px" == "{\"t\":\"u\",\"v\":96,\"u\":\"px\"}"
#guard typedOp "to\x00u(96 \"px\")\x00in" == "{\"t\":\"u\",\"v\":1,\"u\":\"in\"}"
#guard typedOp "to\x00u(1 \"px\")\x00s" == ""
#guard typedOp "equals\x00u(1 \"px\")\x00u(1 \"px\")" == "1"
#guard typedOp "equals\x00u(1 \"px\")\x00u(1 \"em\")" == "0"
#guard typedOp "parse\x001.5em" == "{\"t\":\"u\",\"v\":1.5,\"u\":\"em\"}"
#guard typedOp "parse\x00auto" == ""

/-- Kind: structure. Says: adding a type to itself gives that type: a sum of values of one
type has that type. Does not say: that every pair of types adds (a length and a time do
not). -/
theorem addTypes_self (t : NumType) : addTypes t t = some t := by
  unfold addTypes
  cases h : t.hint <;> simp [h]

/-- Kind: structure. Says: the type of a negated value is the type of the value, so
`sub` type-checks exactly when `add` does. Does not say: anything about `invert` (which
negates the exponents). -/
theorem numType_neg (fuel : Nat) (x : Calc) : numType (fuel + 1) (.neg x) = numType fuel x := by
  simp [numType]

end L4Factoidal.Rendering.CssTyped
