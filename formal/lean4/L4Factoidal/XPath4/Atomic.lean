/-
L4Factoidal.XPath4.Atomic — XDM 4.0 ATOMIC VALUES: their types, their
string values, casting between them, and the comparison and arithmetic
operators of F&O 4.0 that work on them.

Specs read (qtspecs commit b4723ff52fd9d4fabf2b4cd33bd44f21939c512c,
2026-10-22): XDM 4.0 §2.7 (atomic values), F&O 4.0 §4 (op:numeric-*),
§22 (casting), XSD 1.1 Part 2 §3 (the value spaces, reused from
`L4Factoidal.XSD.Datatypes`).

## What a value is

An atomic value is a TYPE ANNOTATION and a VALUE. The annotation is a
built-in XSD type (`XSD.Builtin`) or `xs:untypedAtomic`. The value is:

* `str`  — every type derived from `xs:string`, and `xs:anyURI` and
  `xs:untypedAtomic`;
* `int`  — every type derived from `xs:integer` (the annotation keeps
  `xs:short`, `xs:byte`, ... apart);
* `dec`  — `xs:decimal`, exact (`XSD.Dec`);
* `dbl`  — `xs:double`, and also `xs:float`, whose value is held as the
  binary64 value of a binary32 number;
* `qn`   — `xs:QName` and `xs:NOTATION`;
* `x`    — durations, dates and times, and binary values, held as the
  XSD value (`XSD.Val`) so the date/time arithmetic of
  `L4Factoidal.Fn.DateTime` applies unchanged.

## Not implemented here

User-defined (schema) types; `xs:NMTOKENS`/`xs:IDREFS`/`xs:ENTITIES`
as cast targets give FORG0001 for a value of more than one token
being a sequence (list types are not atomic); `xs:precisionDecimal`.
-/
import L4Factoidal.XSD.Datatypes
import L4Factoidal.XSD.IEEE754
import L4Factoidal.Fn.DateTime
import L4Factoidal.Fn.Numeric

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-! ## Errors -/

/-- A dynamic or static error, with its `err:` code (local name only,
    for example `"XPTY0004"`). -/
structure Err where
  code : String
  msg  : String := ""
  /-- The namespace of the error code; empty for `err:` (the
      `http://www.w3.org/2005/xqt-errors` namespace). Set by `fn:error`
      with a QName in another namespace (XQuery 4.0 `catch`). -/
  uri  : String := ""
deriving Repr, Inhabited

abbrev M := Except Err

def err {α} (code : String) (msg : String := "") : M α := .error { code, msg }

/-! ## Names -/

/-- An expanded QName. Equality ignores the prefix. -/
structure QN where
  uri : String
  loc : String
  pfx : String := ""
deriving Repr, Inhabited

instance : BEq QN := ⟨fun a b => a.uri == b.uri && a.loc == b.loc⟩

def QN.show (q : QN) : String := if q.pfx == "" then q.loc else q.pfx ++ ":" ++ q.loc
def QN.eqn (q : QN) : String := "Q{" ++ q.uri ++ "}" ++ q.loc

def nsXS   : String := "http://www.w3.org/2001/XMLSchema"
def nsFN   : String := "http://www.w3.org/2005/xpath-functions"
def nsMATH : String := "http://www.w3.org/2005/xpath-functions/math"
def nsMAP  : String := "http://www.w3.org/2005/xpath-functions/map"
def nsARR  : String := "http://www.w3.org/2005/xpath-functions/array"
def nsERR  : String := "http://www.w3.org/2005/xqt-errors"
def nsXML  : String := "http://www.w3.org/XML/1998/namespace"
def nsOP   : String := "http://www.w3.org/2002/08/xquery-operators"

/-! ## Types -/

/-- An atomic type annotation. -/
inductive AType where
  | b (x : Builtin)
  | untyped
deriving DecidableEq, Repr, Inhabited

def AType.name : AType → String
  | .b x => x.localName
  | .untyped => "untypedAtomic"

def atypeOfName? (s : String) : Option AType :=
  if s == "untypedAtomic" then some .untyped
  else match builtinOfName? s with
    | some .anySimpleType => none
    | some x => some (.b x)
    | none => none

/-- `t` is `s` or derived from it. `xs:untypedAtomic` derives from
    `xs:anyAtomicType` only. -/
def AType.derives (t s : AType) : Bool :=
  match t, s with
  | .untyped, .untyped => true
  | .untyped, .b .anyAtomicType => true
  | .untyped, _ => false
  | .b _, .untyped => false
  | .b x, .b y => derivedFrom x y

/-! ## Values -/

inductive AV where
  | str (s : String)
  | bool (b : Bool)
  | int (i : Int)
  | dec (d : Dec)
  | dbl (f : Float)
  | qn (q : QN)
  | x (v : Val)
deriving Repr, Inhabited

structure Atomic where
  ty : AType
  v  : AV
deriving Repr, Inhabited

def Atomic.ofStr (s : String) : Atomic := ⟨.b .string, .str s⟩
def Atomic.ofBool (b : Bool) : Atomic := ⟨.b .boolean, .bool b⟩
def Atomic.ofInt (i : Int) : Atomic := ⟨.b .integer, .int i⟩
def Atomic.ofDec (d : Dec) : Atomic := ⟨.b .decimal, .dec (Dec.norm d)⟩
def Atomic.ofDbl (f : Float) : Atomic := ⟨.b .double, .dbl f⟩
def Atomic.ofFlt (f : Float) : Atomic := ⟨.b .float, .dbl f.toFloat32.toFloat⟩
def Atomic.untypedOf (s : String) : Atomic := ⟨.untyped, .str s⟩
def Atomic.ofQN (q : QN) : Atomic := ⟨.b .qname, .qn q⟩
def Atomic.ofUri (s : String) : Atomic := ⟨.b .anyURI, .str s⟩

def Atomic.is (a : Atomic) (b : Builtin) : Bool := a.ty.derives (.b b)

def Atomic.isNumeric (a : Atomic) : Bool :=
  a.is .decimal || a.is .double || a.is .float

def Atomic.isStringLike (a : Atomic) : Bool :=
  a.is .string || a.is .anyURI || a.ty == .untyped

/-! ## IEEE 754 binary64 ↔ exact values -/

/-- The exact value of a finite double as `(negative, num, den)` with
    `den` a power of two. -/
def floatParts (f : Float) : Bool × Nat × Nat :=
  let bits := f.toBits
  let neg := (bits >>> 63) == 1
  let e := ((bits >>> 52) &&& 0x7FF).toNat
  let frac := (bits &&& 0xFFFFFFFFFFFFF).toNat
  if e == 0 then (neg, frac, 2 ^ 1074)
  else
    let m := frac + 2 ^ 52
    let be : Int := (e : Int) - 1075
    if be ≥ 0 then (neg, m * 2 ^ be.toNat, 1) else (neg, m, 2 ^ (-be).toNat)

def fvalToFloat (v : Fval) : Float := Float.ofBits (fvalToBits64 v)

/-- Correctly rounded decimal-to-binary64 (through `XSD.IEEE754`). -/
def floatOfParsed (p : Parsed) : Float :=
  match p with
  | .num neg m e =>
    -- a decimal exponent far outside the binary64 range is ±INF or ±0
    -- without building 10^e
    let digits : Int := (toString m).length
    if m != 0 && e + digits > 400 then (if neg then -(1.0 / 0.0) else 1.0 / 0.0)
    else if m == 0 || e + digits < -400 then (if neg then -0.0 else 0.0)
    else fvalToFloat (canonDouble p)
  | _ => fvalToFloat (canonDouble p)

def floatOfLex? (s : String) : Option Float := (parseLexical s).map floatOfParsed

def float32OfLex? (s : String) : Option Float :=
  (parseLexical s).map (fun p => (Float32.ofBits (fvalToBits32 (canonFloat p))).toFloat)

def floatOfInt (i : Int) : Float := floatOfParsed (.num (i < 0) i.natAbs 0)

def floatOfDec (d : Dec) : Float :=
  floatOfParsed (.num (d.mantissa < 0) d.mantissa.natAbs (-(d.scale : Int)))

def natDigits (n : Nat) : Nat := (toString n).length

/-- Round `num/den` to the nearest integer, ties to even. -/
def roundHalfEven (num den : Nat) : Nat :=
  let q := num / den
  let r := num % den
  if 2 * r > den then q + 1
  else if 2 * r < den then q
  else if q % 2 == 0 then q else q + 1

/-- The SHORTEST decimal digits `(D, q)` with `D` having `p` digits,
    value ≈ `D × 10^(q - p + 1)`, that read back as the same binary
    value. `isF32` selects binary32. -/
def shortestDigits (isF32 : Bool) (f : Float) : Nat × Int :=
  let (_, num, den) := floatParts f
  -- decimal exponent q with 10^q ≤ num/den < 10^(q+1)
  let ip := num / den
  let q0 : Int :=
    if ip > 0 then (natDigits ip : Int) - 1
    else
      -- smallest k with num * 10^k ≥ den
      let rec findK (k : Nat) (fuel : Nat) : Nat :=
        match fuel with
        | 0 => k
        | fuel + 1 => if num * 10 ^ k ≥ den then k else findK (k + 1) fuel
      Int.neg ((findK 1 400 : Nat) : Int)
  let target := if isF32 then (f.toFloat32.toBits.toNat) else f.toBits.toNat
  let digitsFor (p : Nat) : Nat × Int :=
    let sh : Int := (p : Int) - 1 - q0
    let (n2, d2) := if sh ≥ 0 then (num * 10 ^ sh.toNat, den) else (num, den * 10 ^ (-sh).toNat)
    let dd := roundHalfEven n2 d2
    if dd ≥ 10 ^ p then (dd / 10, q0 + 1) else (dd, q0)
  let back (dq : Nat × Int) (p : Nat) : Nat :=
    let e : Int := dq.2 - (p : Int) + 1
    let parsed : Parsed := .num false dq.1 e
    if isF32 then (fvalToBits32 (canonFloat parsed)).toNat
    else (fvalToBits64 (canonDouble parsed)).toNat
  let absTarget := if isF32 then target % 2 ^ 31 else target % 2 ^ 63
  let rec go (p : Nat) (fuel : Nat) : Nat × Int :=
    match fuel with
    | 0 => digitsFor 17
    | fuel + 1 =>
      let dq := digitsFor p
      if back dq p == absTarget then dq else go (p + 1) fuel
  go 1 17

def stripTrailingZeros (s : List Char) : List Char :=
  (s.reverse.dropWhile (· == '0')).reverse

/-- The XPath `xs:double`/`xs:float` → `xs:string` cast (F&O 4.0
    §22.1.2.2): decimal notation for `1e-6 ≤ |v| < 1e6`, otherwise
    `d.dddEn`, with the fewest digits that read back as `v`. -/
def fmtFloating (isF32 : Bool) (f : Float) : String :=
  if f.isNaN then "NaN"
  else if f.isInf then (if f < 0 then "-INF" else "INF")
  else if f == 0 then (if (f.toBits >>> 63) == 1 then "-0" else "0")
  else
    let neg := f < 0
    let (d, q) := shortestDigits isF32 f
    let ds := (toString d).toList
    let ds := let t := stripTrailingZeros ds; if t.isEmpty then ['0'] else t
    let a := f.abs
    let body :=
      if a ≥ 1e-6 && a < 1e6 then
        -- decimal notation
        if q ≥ 0 then
          let qn := q.toNat
          let ip := (ds.take (qn + 1)) ++ List.replicate (qn + 1 - min (qn + 1) ds.length) '0'
          let fp := ds.drop (qn + 1)
          String.ofList ip ++ (if fp.isEmpty then "" else "." ++ String.ofList fp)
        else
          "0." ++ String.ofList (List.replicate ((-q).toNat - 1) '0') ++ String.ofList ds
      else
        let fp := ds.drop 1
        String.ofList (ds.take 1) ++ "." ++ (if fp.isEmpty then "0" else String.ofList fp)
          ++ "E" ++ toString q
    (if neg then "-" else "") ++ body

def fmtDouble (f : Float) : String := fmtFloating false f
def fmtFloat (f : Float) : String := fmtFloating true f

/-- The exact decimal value of a finite double. -/
def decOfFloat (f : Float) : Dec :=
  let (neg, num, den) := floatParts f
  -- den = 2^k; num/2^k = num*5^k/10^k
  let k := Nat.log2 den
  let m : Int := (num * 5 ^ k : Nat)
  Dec.norm ⟨if neg then -m else m, k⟩

/-! ## The string value of an atomic value -/

def isZeroDur (d : DurValue) : Bool := d.months == 0 && Dec.cmp d.seconds Dec.zero == .eq

def Atomic.str (a : Atomic) : String :=
  match a.v with
  | .str s => s
  | .bool b => if b then "true" else "false"
  | .int i => toString i
  | .dec d => Dec.canonical d
  | .dbl f => if a.is .float then fmtFloat f else fmtDouble f
  | .qn q => q.show
  | .x v =>
    match v with
    | .dur d =>
        if isZeroDur d then
          (if a.is .yearMonthDuration then "P0M" else "PT0S")
        else canonicalDuration d
    | .dt k w => canonicalDateTime k w
    | .bin true bs => hexOfBytes bs
    | .bin false bs => base64OfBytes bs
    | other => canonicalMap (match a.ty with | .b b => b | .untyped => .string) other

/-! ## Numeric values -/

/-- A numeric value, after type promotion. -/
inductive Num where
  | i (v : Int)
  | d (v : Dec)
  | f (v : Float)   -- xs:float
  | g (v : Float)   -- xs:double
deriving Inhabited

def Atomic.num? (a : Atomic) : Option Num :=
  match a.v with
  | .int i => some (.i i)
  | .dec d => some (.d d)
  | .dbl f => if a.is .float then some (.f f) else some (.g f)
  | _ => none

def Num.rank : Num → Nat
  | .i _ => 0 | .d _ => 1 | .f _ => 2 | .g _ => 3

def Num.toDec : Num → Dec
  | .i v => Dec.ofInt v | .d v => v | .f v => decOfFloat v | .g v => decOfFloat v

def Num.toFloat : Num → Float
  | .i v => floatOfInt v | .d v => floatOfDec v | .f v => v | .g v => v

def Num.atomic : Num → Atomic
  | .i v => Atomic.ofInt v
  | .d v => Atomic.ofDec v
  | .f v => Atomic.ofFlt v
  | .g v => Atomic.ofDbl v

/-- Promote to the common rank. -/
def Num.promote (r : Nat) (n : Num) : Num :=
  if n.rank ≥ r then n
  else match r with
    | 1 => .d n.toDec
    | 2 => .f n.toFloat.toFloat32.toFloat
    | _ => .g n.toFloat

def decIsZero (d : Dec) : Bool := d.mantissa == 0

def Float.truncI (f : Float) : Int :=
  -- exact truncation toward zero of a finite double
  let (neg, num, den) := floatParts f
  let q : Int := (num / den : Nat)
  if neg then -q else q

inductive ArOp where
  | add | sub | mul | div | idiv | mod
deriving DecidableEq, Repr, Inhabited

def maxDecDigits : Nat := 40

/-- op:numeric-add, subtract, multiply, divide, integer-divide, mod. -/
def numArith (op : ArOp) (a b : Num) : M Num :=
  let r := max a.rank b.rank
  let a := a.promote r
  let b := b.promote r
  match a, b with
  | .i x, .i y =>
    match op with
    | .add => pure (.i (x + y))
    | .sub => pure (.i (x - y))
    | .mul => pure (.i (x * y))
    | .div => if y == 0 then err "FOAR0001" "division by zero"
              else match Fn.Numeric.decDiv? 18 (Dec.ofInt x) (Dec.ofInt y) with
                | some d => pure (.d d) | none => err "FOAR0001"
    | .idiv => if y == 0 then err "FOAR0001" "division by zero" else pure (.i (Int.tdiv x y))
    | .mod => if y == 0 then err "FOAR0001" "division by zero" else pure (.i (Int.tmod x y))
  | .d x, .d y =>
    match op with
    | .add => pure (.d (Dec.norm (Dec.add x y)))
    | .sub => pure (.d (Dec.norm (Dec.sub x y)))
    | .mul => pure (.d (Fn.Numeric.decMul x y))
    | .div => match Fn.Numeric.decDiv? (max 18 (x.scale + 18)) x y with
              | some d => pure (.d d) | none => err "FOAR0001" "division by zero"
    | .idiv => match Fn.Numeric.decIntDiv? x y with
               | some q => pure (.i q) | none => err "FOAR0001" "division by zero"
    | .mod => match Fn.Numeric.decMod? x y with
              | some q => pure (.d (Dec.norm q)) | none => err "FOAR0001" "division by zero"
  | _, _ =>
    let x := a.toFloat
    let y := b.toFloat
    let wrap (z : Float) : Num := if r == 2 then .f z.toFloat32.toFloat else .g z
    match op with
    | .add => pure (wrap (x + y))
    | .sub => pure (wrap (x - y))
    | .mul => pure (wrap (x * y))
    | .div => pure (wrap (x / y))
    | .mod =>
        if x.isNaN || y.isNaN || x.isInf || y == 0 then pure (wrap (0.0 / 0.0))
        else if y.isInf then pure (wrap x)
        else
          -- exact remainder: x - trunc(x/y)*y computed exactly
          let dx := decOfFloat x
          let dy := decOfFloat y
          match Fn.Numeric.decMod? dx dy with
          | some m => pure (wrap (let z := floatOfDec m; if z == 0 && x < 0 then -0.0 else z))
          | none => pure (wrap (0.0 / 0.0))
    | .idiv =>
        if y == 0 then err "FOAR0001" "integer division by zero"
        else if x.isNaN || y.isNaN || x.isInf then err "FOAR0002" "numeric operation overflow/underflow"
        else if y.isInf then pure (.i 0)
        else match Fn.Numeric.decIntDiv? (decOfFloat x) (decOfFloat y) with
          | some q => pure (.i q) | none => err "FOAR0001"

def numNeg : Num → Num
  | .i v => .i (-v) | .d v => .d (Dec.neg v) | .f v => .f (-v) | .g v => .g (-v)

/-- Numeric comparison; `none` when a NaN is involved. -/
def numCmp (a b : Num) : Option Ordering :=
  match a, b with
  | .i x, .i y => some (compare x y)
  | .d x, .d y => some (Dec.cmp x y)
  | _, _ =>
    let fx := a.toFloat
    let fy := b.toFloat
    let fl (n : Num) : Bool := n.rank ≥ 2
    if (fl a && fx.isNaN) || (fl b && fy.isNaN) then none
    else if (fl a && fx.isInf) || (fl b && fy.isInf) then
      let gx := if fl a then fx else 0
      let gy := if fl b then fy else 0
      if gx < gy then some .lt else if gx > gy then some .gt else some .eq
    else
      -- XPath 4.0 (PR 2218): numeric comparison is exact, on the decimal values
      some (Dec.cmp a.toDec b.toDec)

/-! ## Casting (F&O 4.0 §22) -/

def castErr {α} (a : Atomic) (t : AType) : M α :=
  err "FORG0001" ("cannot cast " ++ a.str ++ " to xs:" ++ t.name)

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def trimWs (s : String) : String :=
  String.ofList ((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse

/-- Parse an XPath numeric lexical for `xs:double`. -/
def parseDoubleLex? (s : String) : Option Float :=
  let t := trimWs s
  if t == "INF" || t == "+INF" then some (1.0 / 0.0)
  else if t == "-INF" then some (-(1.0 / 0.0))
  else if t == "NaN" then some (0.0 / 0.0)
  else
    let cs := t.toList
    let ok := !cs.isEmpty && cs.all (fun c => c.isDigit || c == '.' || c == 'e' || c == 'E' || c == '+' || c == '-')
    if !ok then none else floatOfLex? t

/-- Cast from a string to an atomic type (the lexical rules of §22.2). -/
def castFromString (s : String) (t : AType) (nsResolve : String → Option String := fun _ => none) : M Atomic :=
  let bad : M Atomic := err "FORG0001" ("invalid lexical form '" ++ s ++ "' for xs:" ++ t.name)
  match t with
  | .untyped => pure (Atomic.untypedOf s)
  | .b b =>
    let w := applyWhiteSpace b.whiteSpace s
    match b with
    | .string | .anyAtomicType => pure ⟨.b .string, .str s⟩
    | .normalizedString | .token | .language | .nmtoken | .name | .ncname | .id
    | .idref | .entity =>
        match lexicalMap b w with
        | some _ => pure ⟨t, .str w⟩
        | none => bad
    | .anyURI => pure ⟨t, .str w⟩
    | .boolean =>
        match w with
        | "true" | "1" => pure (Atomic.ofBool true)
        | "false" | "0" => pure (Atomic.ofBool false)
        | _ => bad
    | .decimal =>
        match parseDecimalLex w with
        | some d => pure (Atomic.ofDec d)
        | none => bad
    | .double =>
        match parseDoubleLex? w with
        | some f => pure (Atomic.ofDbl f)
        | none => bad
    | .float =>
        if w == "INF" || w == "+INF" || w == "-INF" || w == "NaN" then
          match parseDoubleLex? w with
          | some f => pure (Atomic.ofFlt f) | none => bad
        else match parseDoubleLex? w with
          | some _ => match float32OfLex? w with
              | some f => pure ⟨.b .float, .dbl f⟩ | none => bad
          | none => bad
    | .integer | .nonPositiveInteger | .negativeInteger | .long | .int
    | .short | .byte | .nonNegativeInteger | .unsignedLong | .unsignedInt
    | .unsignedShort | .unsignedByte | .positiveInteger =>
        match parseIntegerLex w with
        | some i => if inIntBounds b i then pure ⟨t, .int i⟩ else bad
        | none => bad
    | .qname | .notation =>
        match parseQNameLex w with
        | some (p, l) =>
            match nsResolve p with
            | some u => pure ⟨t, .qn { uri := u, loc := l, pfx := p }⟩
            | none => if p == "" then pure ⟨t, .qn { uri := "", loc := l }⟩
                      else err "FONS0004" ("no namespace binding for prefix " ++ p)
        | none => bad
    | _ =>
        match lexicalMap b w with
        | some v => pure ⟨t, .x v⟩
        | none => bad

def intRangeCheck (b : Builtin) (i : Int) : M Atomic :=
  if inIntBounds b i then pure ⟨.b b, .int i⟩
  else err "FORG0001" ("value " ++ toString i ++ " out of range for xs:" ++ b.localName)

def dtProject (k : DTKind) (w : DTValue) : DTValue :=
  match k with
  | .dateTime => w
  | .date => { year := w.year, month := w.month, day := w.day, tz := w.tz }
  | .time => { hour := w.hour, minute := w.minute, second := w.second, tz := w.tz }
  | .gYearMonth => { year := w.year, month := w.month, tz := w.tz }
  | .gYear => { year := w.year, tz := w.tz }
  | .gMonthDay => { month := w.month, day := w.day, tz := w.tz }
  | .gDay => { day := w.day, tz := w.tz }
  | .gMonth => { month := w.month, tz := w.tz }

def isIntegerTy (b : Builtin) : Bool := derivedFrom b .integer

/-- `cast as` between atomic types (§22.1). The source is never
    `xs:untypedAtomic`/`xs:string` here unless the caller wants the
    lexical route; both go through `castFromString`. -/
def castAtomic (a : Atomic) (t : AType) (nsResolve : String → Option String := fun _ => none) : M Atomic :=
  if a.ty == t then pure a
  else
  match t with
  | .untyped => pure (Atomic.untypedOf a.str)
  | .b tb =>
  if tb == .anyAtomicType then pure a else
  if a.is .anyURI && !(derivedFrom tb .string || tb == .anyURI) then
    err "XPTY0004" ("cannot cast xs:anyURI to xs:" ++ t.name)
  else if a.isStringLike then
    if tb == .qname || tb == .notation then
      if a.is .anyURI then err "XPTY0004" "cannot cast xs:anyURI to xs:QName"
      else castFromString a.str t nsResolve
    else castFromString a.str t nsResolve
  else if derivedFrom tb .string || tb == .anyURI then
    let s := a.str
    if tb == .anyURI then
      if a.is .string then pure ⟨t, .str s⟩ else err "XPTY0004" ("cannot cast to xs:anyURI from xs:" ++ a.ty.name)
    else castFromString s t
  else
  match a.v with
  | .bool b =>
      if tb == .boolean then pure ⟨t, .bool b⟩
      else if tb == .decimal then pure (Atomic.ofDec (Dec.ofInt (if b then 1 else 0)))
      else if isIntegerTy tb then intRangeCheck tb (if b then 1 else 0)
      else if tb == .double then pure (Atomic.ofDbl (if b then 1 else 0))
      else if tb == .float then pure (Atomic.ofFlt (if b then 1 else 0))
      else err "XPTY0004" ("cannot cast xs:boolean to xs:" ++ t.name)
  | .int i =>
      if tb == .boolean then pure (Atomic.ofBool (i != 0))
      else if tb == .decimal then pure (Atomic.ofDec (Dec.ofInt i))
      else if isIntegerTy tb then intRangeCheck tb i
      else if tb == .double then pure (Atomic.ofDbl (floatOfInt i))
      else if tb == .float then pure (Atomic.ofFlt (floatOfInt i))
      else err "XPTY0004" ("cannot cast xs:integer to xs:" ++ t.name)
  | .dec d =>
      if tb == .boolean then pure (Atomic.ofBool (d.mantissa != 0))
      else if tb == .decimal then pure (Atomic.ofDec d)
      else if isIntegerTy tb then intRangeCheck tb (Int.tdiv d.mantissa ((10 : Int) ^ d.scale))
      else if tb == .double then pure (Atomic.ofDbl (floatOfDec d))
      else if tb == .float then pure (Atomic.ofFlt (floatOfDec d))
      else err "XPTY0004" ("cannot cast xs:decimal to xs:" ++ t.name)
  | .dbl f =>
      if tb == .boolean then pure (Atomic.ofBool (!(f == 0) && !f.isNaN))
      else if tb == .double then pure (Atomic.ofDbl f)
      else if tb == .float then pure (Atomic.ofFlt f)
      else if tb == .decimal || isIntegerTy tb then
        if f.isNaN || f.isInf then err "FOCA0002" "cannot cast NaN or INF to a decimal"
        else if tb == .decimal then pure (Atomic.ofDec (decOfFloat f))
        else intRangeCheck tb (Float.truncI f)
      else err "XPTY0004" ("cannot cast xs:" ++ a.ty.name ++ " to xs:" ++ t.name)
  | .qn q =>
      if tb == .qname || tb == .notation then pure ⟨t, .qn q⟩
      else err "XPTY0004" ("cannot cast xs:QName to xs:" ++ t.name)
  | .str _ => castFromString a.str t
  | .x v =>
    match v, tb with
    | .dur d, .duration => pure ⟨t, .x (.dur d)⟩
    | .dur d, .yearMonthDuration => pure ⟨t, .x (.dur { months := d.months, seconds := Dec.zero })⟩
    | .dur d, .dayTimeDuration => pure ⟨t, .x (.dur { months := 0, seconds := d.seconds })⟩
    | .dt k w, _ =>
        match dtKindOf? tb with
        | some k2 =>
            if k == k2 then pure ⟨t, .x (.dt k w)⟩
            else if k == .dateTime then pure ⟨t, .x (.dt k2 (dtProject k2 w))⟩
            else if k == .date && k2 == .dateTime then
              pure ⟨t, .x (.dt .dateTime { w with hour := some 0, minute := some 0, second := some Dec.zero })⟩
            else if k == .date && (k2 == .gYearMonth || k2 == .gYear || k2 == .gMonthDay || k2 == .gDay || k2 == .gMonth) then
              pure ⟨t, .x (.dt k2 (dtProject k2 w))⟩
            else err "XPTY0004" ("cannot cast xs:" ++ a.ty.name ++ " to xs:" ++ t.name)
        | none => err "XPTY0004" ("cannot cast xs:" ++ a.ty.name ++ " to xs:" ++ t.name)
    | .bin _ bs, .hexBinary => pure ⟨t, .x (.bin true bs)⟩
    | .bin _ bs, .base64Binary => pure ⟨t, .x (.bin false bs)⟩
    | _, _ => err "XPTY0004" ("cannot cast xs:" ++ a.ty.name ++ " to xs:" ++ t.name)

/-! ## Equality and ordering of atomic values -/

/-- The primitive type, for comparability. -/
def AType.prim : AType → String
  | .untyped => "untypedAtomic"
  | .b bt =>
    if derivedFrom bt .decimal || bt == .float || bt == .double then "numeric"
    else if derivedFrom bt .string then "string"
    else if bt == .anyURI then "string"
    else if derivedFrom bt .duration then "duration"
    else if bt == .hexBinary || bt == .base64Binary then "binary"
    else match (bt.primitive) with
      | some p => p.localName
      | none => bt.localName

/-- Value comparison `eq`/`lt` (op:*-equal, op:*-less-than). `ok`
    false means the types are not comparable (XPTY0004); `none` in the
    result means unordered (NaN). Strings compare by codepoint. -/
def atomicCmp (a b : Atomic) (implicitTz : Int := 0) : M (Option Ordering) :=
  let pa := a.ty.prim
  let pb := b.ty.prim
  let pa := if pa == "untypedAtomic" then "string" else pa
  let pb := if pb == "untypedAtomic" then "string" else pb
  if pa == "numeric" && pb == "numeric" then
    match a.num?, b.num? with
    | some x, some y => pure (numCmp x y)
    | _, _ => err "XPTY0004"
  else if pa == "string" && pb == "string" then
    let x := a.str
    let y := b.str
    pure (some (if x < y then .lt else if x == y then .eq else .gt))
  else if pa == "boolean" && pb == "boolean" then
    match a.v, b.v with
    | .bool x, .bool y => pure (some (if x == y then .eq else if !x then .lt else .gt))
    | _, _ => err "XPTY0004"
  else if pa == "duration" && pb == "duration" then
    match a.v, b.v with
    | .x (.dur x), .x (.dur y) =>
        -- XPath 4.0: durations are ordered by months, then by seconds
        if x.months != y.months then pure (some (compare x.months y.months))
        else pure (some (Dec.cmp x.seconds y.seconds))
    | _, _ => err "XPTY0004"
  else if pa == pb then
    match a.v, b.v with
    | .x (.dt _ x), .x (.dt _ y) => pure (Fn.DateTime.compare implicitTz x y)
    | .x (.bin _ x), .x (.bin _ y) => pure (some (compare x y))
    | .qn x, .qn y =>
        -- XPath 4.0: QNames are ordered by namespace URI, then local name
        if x.uri != y.uri then pure (some (compare x.uri y.uri))
        else pure (some (compare x.loc y.loc))
    | _, _ => pure (some (if a.str == b.str then .eq else if a.str < b.str then .lt else .gt))
  else err "XPTY0004" ("cannot compare xs:" ++ a.ty.name ++ " with xs:" ++ b.ty.name)

/-- Types whose values have an order (`lt` is defined). -/
def AType.ordered (t : AType) : Bool :=
  match t.prim with
  | "boolean" | "numeric" | "string" | "untypedAtomic" | "date" | "time" | "dateTime"
  | "binary" => true
  -- XPath 4.0 (PR 2256): the Gregorian types and QNames are ordered too
  | "gYear" | "gYearMonth" | "gMonth" | "gMonthDay" | "gDay" | "QName" | "NOTATION" => true
  | "duration" => true
  | _ => false

/-- `op:same-key` / `fn:atomic-equal` (F&O 4.0 §14.2.1 and §17): equality
    that never raises, where NaN equals NaN and incomparable values are
    unequal. -/
def atomicEqual (a b : Atomic) : Bool :=
  match a.num?, b.num? with
  | some x, some y =>
      let fx := x.toFloat
      let fy := y.toFloat
      if (x.rank ≥ 2 && fx.isNaN) || (y.rank ≥ 2 && fy.isNaN) then
        (x.rank ≥ 2 && fx.isNaN) && (y.rank ≥ 2 && fy.isNaN)
      else if (x.rank ≥ 2 && fx.isInf) || (y.rank ≥ 2 && fy.isInf) then fx == fy
      else Dec.cmp x.toDec y.toDec == .eq
  | _, _ =>
    match a.v, b.v with
    | .x (.dt k1 x), .x (.dt k2 y) =>
        k1 == k2 && x.tz.isSome == y.tz.isSome && Fn.DateTime.compare 0 x y == some .eq
    | _, _ =>
      match atomicCmp a b with
      | .ok (some .eq) => true
      | _ => false

#guard fmtDouble 1.5 == "1.5"
#guard fmtDouble 100 == "100"
#guard fmtDouble 1e7 == "1.0E7"
#guard fmtDouble 0.1 == "0.1"
#guard fmtDouble 1.0e-7 == "1.0E-7"
#guard fmtDouble 6.283185307179586 == "6.283185307179586"
#guard fmtDouble 1234567 == "1.234567E6"
#guard fmtFloat (Float.toFloat32 0.1).toFloat == "0.1"
#guard (Atomic.ofDec ⟨10, 1⟩).str == "1"

end L4Factoidal.XPath4
