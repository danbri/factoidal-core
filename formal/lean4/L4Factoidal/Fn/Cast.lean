/- F&O 2007 §§17.1–17.5 value conversions, shared by host-language adapters.
   Inputs are validated XSD values. Targets are built-in atomic datatypes;
   QName/NOTATION need namespace context, and list/universal/precisionDecimal
   targets remain unsupported. Source decoding and output syntax belong to
   callers. `none` covers invalid and unsupported conversions, not false values.
   Double-to-float narrowing follows §17.1.3.1's truncation, not arithmetic's
   nearest-even rounding. Decimal conversion of finite IEEE values is exact. -/
import L4Factoidal.XSD.ValueSpace
import L4Factoidal.Fn.Arithmetic

namespace L4Factoidal.Fn.Cast
open XSD

/-- F&O §17.1.3.3: exact decimal representation of a finite binary value. -/
def floatingDecimal (f : Fval) : Option Dec :=
  match f.cls with
  | .nan | .inf => none
  | .zero => some Dec.zero
  | .finite m e =>
    let k := (-e).toNat
    let magnitude := if e ≥ 0 then m * 2 ^ e.toNat else m * 5 ^ k
    some (Dec.norm ⟨if f.neg then -(magnitude : Int) else magnitude, k⟩)

/-- Choose an odd mantissa before applying F&O's mantissa/exponent bounds;
    otherwise an exact subnormal can be mistaken for an underflow. -/
def reduceBinary : Nat → Nat → Int → Nat × Int
  | 0, m, e => (m, e)
  | fuel + 1, m, e =>
    if m != 0 && m % 2 == 0 then reduceBinary fuel (m / 2) (e + 1) else (m, e)

/-- F&O §17.1.3.1, including overflow/underflow after mantissa truncation.
    Re-encoding an exactly representable result uses the shared IEEE kernel. -/
def narrowDouble (f : Fval) : Fval :=
  match f.cls with
  | .nan | .zero | .inf => f
  | .finite m e =>
    let (m, e) := reduceBinary (bitlen m) m e
    let shift := bitlen m - 24
    let m := m / 2 ^ shift
    let e := e + shift
    -- A reduced mantissa may be shifted left up to 24 bits without losing
    -- information; test overflow at that equivalent normalized exponent.
    if e + (bitlen m : Int) - 24 > 104 then ⟨f.neg, .inf⟩
    else if e < -149 then ⟨f.neg, .zero⟩
    else Arithmetic.rounded false f.neg
      (if e ≥ 0 then m * 2 ^ e.toNat else m)
      (if e ≥ 0 then 1 else 2 ^ (-e).toNat)

/-- F&O §17.1.3: numeric/Boolean sources for decimal and integer casts. -/
def decimalValue : Val → Option Dec
  | .dec d => some d
  | .flt f | .dbl f => floatingDecimal f
  | .bool b => some (Dec.ofInt (if b then 1 else 0))
  | _ => none

/-- F&O §17.1.2: E-form strings prohibit redundant trailing mantissa zeros. -/
def scientificString (f : Fval) : String :=
  let s := canonicalFval f
  match s.splitOn "E" with
  | [mantissa, exponent] =>
    match parseDecimalLex mantissa with
    | some d =>
      let m := d.canonical
      (if m.contains '.' then m else m ++ ".0") ++ "E" ++ exponent
    | none => s
  | _ => s

/-- F&O §17.1.2: floating string syntax differs from XSD's E-form formatter. -/
def floatingString (f : Fval) : String :=
  match f.cls with
  | .zero => if f.neg then "-0" else "0"
  | .finite .. =>
    match floatingDecimal { f with neg := false }, floatingDecimal f with
    | some magnitude, some d =>
      if Dec.cmp magnitude ⟨1, 6⟩ != .lt && Dec.cmp magnitude (Dec.ofInt 1000000) == .lt
      then d.canonical else scientificString f
    | _, _ => canonicalFval f
  | _ => canonicalFval f

/-- Edition-aware serialization, including astronomical internal calendar years.
    Duration zero needs the target subtype to choose P0M versus PT0S. -/
def lexical (edition : Edition) (target : Builtin) (v : Val) : String :=
  match v with
  | .dt k d => canonicalDateTime k { d with year := yearForEdition edition d }
  | .dur d =>
    if target == .yearMonthDuration && d.months == 0 then "P0M" else canonicalDuration d
  | _ => canonicalMap target v

/-- F&O §17.1.2: string values, with no lexical re-interpretation of numbers. -/
def stringValue (edition : Edition) : Val → Option String
  | .str _ s => some s
  | .bool b => some (if b then "true" else "false")
  | .dec d => some d.canonical
  | .flt f | .dbl f => some (floatingString f)
  | .dt k d => some (lexical edition .string (.dt k d))
  | .dur d => some (canonicalDuration d)
  | .bin h bytes => some (if h then hexOfBytes bytes else base64OfBytes bytes)
  | _ => none

/-- F&O §17.1.5: local calendar projection, retaining the timezone. No implicit
    current date is guessed for time-to-dateTime (requires dynamic context). -/
def calendar (target source : DTKind) (v : DTValue) : Option DTValue :=
  if target == source then some v
  else if source == .dateTime || source == .date then
    match target with
    | .dateTime => if source == .date then
        some { v with hour := some 0, minute := some 0, second := some Dec.zero } else none
    | .date => some { year := v.year, month := v.month, day := v.day, tz := v.tz }
    | .time => if source == .dateTime then
        some { hour := v.hour, minute := v.minute, second := v.second, tz := v.tz } else none
    | .gYearMonth => some { year := v.year, month := v.month, tz := v.tz }
    | .gYear => some { year := v.year, tz := v.tz }
    | .gMonthDay => some { month := v.month, day := v.day, tz := v.tz }
    | .gDay => some { day := v.day, tz := v.tz }
    | .gMonth => some { month := v.month, tz := v.tz }
  else none

/-- F&O §17.1: conversions before target facets are checked. -/
def convert (edition : Edition) (target : Builtin) (v : Val) : Option Val := do
  match v with
  | .str .string s =>
    checkedLexicalValue edition target (applyWhiteSpace target.whiteSpace s)
  | _ =>
    if target.primitive == some .string then
      let s ← stringValue edition v
      checkedLexicalValue edition target (applyWhiteSpace target.whiteSpace s)
    else if (intBounds target).isSome then
      let d ← decimalValue v
      some (.dec (Dec.ofInt (Int.tdiv d.mantissa (10 ^ d.scale))))
    else match target, v with
    | .decimal, _ => (decimalValue v).map Val.dec
    | .boolean, .bool b => some (.bool b)
    | .boolean, _ => (Numeric.booleanValue? v).map Val.bool
    | .float, .dbl f => some (.flt (narrowDouble f))
    | .float, .flt f => some (.flt f)
    | .double, .dbl f => some (.dbl f)
    | .double, .flt f =>
      let (num, den) := Arithmetic.magnitude f
      some (.dbl (match f.cls with
        | .finite .. => Arithmetic.rounded true f.neg num den
        | _ => f))
    | .float, _ => (decimalValue v).map (fun d => .flt (canonFloat (Numeric.decimalParsed d)))
    | .double, _ => (decimalValue v).map (fun d => .dbl (canonDouble (Numeric.decimalParsed d)))
    | .hexBinary, .bin _ bytes => some (.bin true bytes)
    | .base64Binary, .bin _ bytes => some (.bin false bytes)
    | .duration, .dur d => some (.dur d)
    | .yearMonthDuration, .dur d => some (.dur { months := d.months, seconds := Dec.zero })
    | .dayTimeDuration, .dur d => some (.dur { months := 0, seconds := d.seconds })
    | .anyURI, .str .anyURI s => some (.str .anyURI s)
    | _, .dt k d => do
      let targetKind ← dtKindOf? target
      (calendar targetKind k d).map (Val.dt targetKind)
    | _, _ => none

/-- Target validation is mandatory after conversion (F&O §17.2), including
    integer-derived bounds, lexical restrictions and dateTimeStamp timezone. -/
def cast (edition : Edition) (target : Builtin) (v : Val) : Option Val := do
  if !valueMembershipSupported target then none else do
    let result ← convert edition target v
    if (valueInBuiltin target result).getD false then some result else none

end L4Factoidal.Fn.Cast
