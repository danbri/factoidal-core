/-
L4Factoidal.XPath4.Fn4 — F&O 4.0 functions added after Stage 2:
`fn:hash` (§5.3.18), `fn:random-number-generator` (§5.13.2),
`fn:parts-of-dateTime` and `fn:build-dateTime` (§9.5).

Spec: F&O 4.0 editor's draft (read 2026-10-28).
-/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.Crypto.MD5
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.Blake3
import L4Factoidal.Codec.Crc32

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-! ## `fn:hash` (§5.3.18) -/

def hexBinaryOf (b : ByteArray) : Atomic := ⟨.b .hexBinary, .x (.bin true (b.toList.map (·.toNat)))⟩

def be32 (x : UInt32) : ByteArray :=
  ByteArray.mk #[(x >>> 24).toUInt8, (x >>> 16).toUInt8, (x >>> 8).toUInt8, x.toUInt8]

/-- The algorithms of §5.3.18, by their effective name
    (`upper-case(normalize-space($algorithm))`). -/
def hashBytes (alg : String) (b : ByteArray) : Option ByteArray :=
  match alg with
  | "MD5" => some (Crypto.md5 b)
  | "SHA-1" => some (Crypto.sha1 b)
  | "SHA-256" => some (Crypto.sha256 b)
  | "BLAKE3" => some (Crypto.Blake3.hash b)
  | "CRC-32" => some (be32 (Codec.crc32 b))
  | _ => none

def hashFn : LibFn := fun _ _ a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    let bytes := match bytesOfAtomic v with
      | some b => b
      | none => v.str.toUTF8
    let alg := if (argN a 1).isEmpty then "MD5" else (normSpace (strOf (argN a 1))).toUpper
    match hashBytes alg bytes with
    | some h => pure [.atom (hexBinaryOf h)]
    | none => err "FOHA0001" ("unsupported hash algorithm " ++ alg)

/-! ## `fn:random-number-generator` (§5.13.2)

The generator is SplitMix64 (Steele, Lea, Flood, "Fast splittable
pseudorandom number generators", OOPSLA 2014) over a 64-bit state. The
state of a seeded generator is the FNV-1a 64-bit hash of the seed's type
name and string value; with no seed it is a fixed constant, so that two
calls in one evaluation give the same sequence (the spec allows it: the
seed is then implementation-dependent, and fixed within an execution
scope). `number` is the top 53 bits of the output over 2^53; `next`
advances the state; `permute` is Fisher-Yates driven by successive
numbers; `take(n)` is the first n numbers. The three functions are
inline function items (so they have the record's function types) over
the internal entries `rng-record#`, `rng-permute#`, `rng-take#` of the
catalog. -/

def golden : UInt64 := 0x9E3779B97F4A7C15

def splitmix (s : UInt64) : UInt64 :=
  let z := s + golden
  let z := (z ^^^ (z >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

def fnv1a (s : String) : UInt64 :=
  s.toUTF8.foldl (fun h b => (h ^^^ b.toUInt64) * 0x100000001B3) 0xCBF29CE484222325

def rngNumber (s : UInt64) : Float := (splitmix s >>> 11).toFloat / 9007199254740992.0

def rngNext (s : UInt64) : UInt64 := s + golden

def rngQ (l : String) : QN := { uri := nsFN, loc := l }

def rngRecord (s : UInt64) : Item :=
  let st : Expr := .lit (Atomic.ofInt s.toNat)
  let vIn : QN := { uri := "", loc := "input" }
  let vN : QN := { uri := "", loc := "count" }
  .map [
    (Atomic.ofStr "number", [.atom (Atomic.ofDbl (rngNumber s))]),
    (Atomic.ofStr "next", [.fn (.inline [] (parseTy "fn:random-number-generator-record")
      (.call (rngQ "rng-record#") [some (.lit (Atomic.ofInt (rngNext s).toNat))] []) false [])]),
    (Atomic.ofStr "permute", [.fn (.inline [(vIn, parseTy "item()*")] (parseTy "item()*")
      (.call (rngQ "rng-permute#") [some st, some (.var vIn)] []) false [])]),
    (Atomic.ofStr "take", [.fn (.inline [(vN, parseTy "xs:nonNegativeInteger")] (parseTy "xs:double*")
      (.call (rngQ "rng-take#") [some st, some (.var vN)] []) false [])])]

def rngFn : LibFn := fun _ _ a =>
  match optAtom (argN a 0) with
  | none => pure [rngRecord 0x2545F4914F6CDD1D]
  | some v => pure [rngRecord (fnv1a (v.ty.name ++ ":" ++ v.str))]

def stateOf (s : Seq) : UInt64 := (intOf s).toNat.toUInt64

def rngRecordFn : LibFn := fun _ _ a => pure [rngRecord (stateOf (argN a 0))]

def rngPermuteFn : LibFn := fun _ _ a => do
  let xs := (argN a 1).toArray
  let mut arr := xs
  let mut s := stateOf (argN a 0)
  let n := arr.size
  for k in [0:n] do
    let i := n - 1 - k
    if i == 0 then break
    let j := ((splitmix s >>> 11).toNat * (i + 1)) / 9007199254740992
    s := rngNext s
    let xi := arr[i]!
    arr := (arr.set! i arr[j]!).set! j xi
  pure arr.toList

def rngTakeFn : LibFn := fun _ _ a => do
  let n := (intOf (argN a 1)).toNat
  let mut s := stateOf (argN a 0)
  let mut out : Array Item := #[]
  for _ in [0:n] do
    out := out.push (.atom (Atomic.ofDbl (rngNumber s)))
    s := rngNext s
  pure out.toList

/-! ## `fn:parts-of-dateTime` and `fn:build-dateTime` (§9.5)

A value of one of the eight date/time types has the seven components of
XSD 1.1 §3.3.7 (`XSD.DTValue`); `fn:dateTime-record` names them
`year`, `month`, `day`, `hours`, `minutes`, `seconds`, `timezone`.
`build-dateTime` takes the components that are present, which must be
one of the eight combinations of the types (else `FODT0005`), checks
each range (else `FORG0001`; a day must exist in its month, February 29
needs a leap year when the year is given), and makes the value; a
dateTime with a timezone is an `xs:dateTimeStamp`. -/

def tzDuration (m : Int) : Atomic :=
  ⟨.b .dayTimeDuration, .x (.dur { months := 0, seconds := Dec.ofInt (m * 60) })⟩

def partsOfDateTimeFn : LibFn := fun _ _ a =>
  match optAtom (argN a 0) with
  | none => pure []
  | some ⟨_, .x (.dt _ v)⟩ =>
    let ent (k : String) (x : Option Atomic) : List (Atomic × Seq) :=
      match x with
      | some y => [(Atomic.ofStr k, [.atom y])]
      | none => [(Atomic.ofStr k, [])]
    pure [.map (ent "year" (v.year.map Atomic.ofInt) ++ ent "month" (v.month.map (Atomic.ofInt ·)) ++
      ent "day" (v.day.map (Atomic.ofInt ·)) ++ ent "hours" (v.hour.map (Atomic.ofInt ·)) ++
      ent "minutes" (v.minute.map (Atomic.ofInt ·)) ++ ent "seconds" (v.second.map Atomic.ofDec) ++
      ent "timezone" (v.tz.map tzDuration))]
  | some _ => err "XPTY0004" "parts-of-dateTime needs a date, time or dateTime value"

def isLeap (y : Int) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysIn (y : Option Int) (m : Nat) : Nat :=
  if m == 2 then (match y with | some y => if isLeap y then 29 else 28 | none => 29)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- A component that must be an integer: an xs:integer, an integral
    xs:decimal, or an untyped value cast to xs:integer. -/
def bdInt (e : Env) (name : String) (v : Seq) : M (Option Int) := do
  match ← e.atomize v with
  | [] => pure none
  | [x] =>
    let x ← if x.ty == .untyped then castAtomic x (.b .integer) else pure x
    match x.num? with
    | some (.i i) => pure (some i)
    | some (.d d) =>
      if d.isInt then pure (some ((Dec.norm d).mantissa)) else err "XPTY0004" (name ++ " must be an integer")
    | _ => err "XPTY0004" (name ++ " must be an integer")
  | _ => err "XPTY0004" (name ++ " must be a single value")

def bdDec (e : Env) (name : String) (v : Seq) : M (Option Dec) := do
  match ← e.atomize v with
  | [] => pure none
  | [x] =>
    let x ← if x.ty == .untyped then castAtomic x (.b .decimal) else pure x
    match x.num? with
    | some (.i i) => pure (some (Dec.ofInt i))
    | some (.d d) => pure (some d)
    | some (.f f) | some (.g f) =>
      if f.isNaN || f.isInf then err "XPTY0004" (name ++ " must be finite") else pure (some (decOfFloat f))
    | none => err "XPTY0004" (name ++ " must be a number")
  | _ => err "XPTY0004" (name ++ " must be a single value")

def bdTz (e : Env) (v : Seq) : M (Option Int) := do
  match ← e.atomize v with
  | [] => pure none
  | [⟨_, .x (.dur d)⟩] =>
    let secs := Dec.norm d.seconds
    if d.months != 0 || !secs.isInt || secs.mantissa % 60 != 0 then
      err "FODT0003" "the timezone must be a whole number of minutes"
    let m := secs.mantissa / 60
    if m < -840 || m > 840 then err "FODT0003" "the timezone is out of range"
    pure (some m)
  | _ => err "XPTY0004" "timezone must be an xs:dayTimeDuration"

def buildDateTimeFn : LibFn := fun _ e a => do
  match argN a 0 with
  | [] => pure []
  | [.map kvs] =>
    let get (k : String) : Seq := (mapGet kvs (Atomic.ofStr k)).getD []
    let y ← bdInt e "year" (get "year")
    let mo ← bdInt e "month" (get "month")
    let d ← bdInt e "day" (get "day")
    let h ← bdInt e "hours" (get "hours")
    let mi ← bdInt e "minutes" (get "minutes")
    let sec ← bdDec e "seconds" (get "seconds")
    let tz ← bdTz e (get "timezone")
    let rng {α} (msg : String) : M α := err "FORG0001" msg
    if let some m := mo then
      if m < 1 || m > 12 then rng "month out of range"
    if let some dd := d then
      if dd < 1 || dd > ((daysIn y (mo.getD 1).toNat : Nat) : Int) || (mo.isNone && dd > 31) then rng "day out of range"
    if let some hh := h then
      if hh < 0 || hh > 23 then rng "hours out of range"
    if let some mm := mi then
      if mm < 0 || mm > 59 then rng "minutes out of range"
    if let some ss := sec then
      if Dec.cmp ss Dec.zero == .lt || Dec.cmp ss (Dec.ofInt 60) != .lt then rng "seconds out of range"
    let pres := (y.isSome, mo.isSome, d.isSome, h.isSome, mi.isSome, sec.isSome)
    let kt : Option (DTKind × Builtin) := match pres with
      | (true, true, true, true, true, true) => some (.dateTime, if tz.isSome then .dateTimeStamp else .dateTime)
      | (true, true, true, false, false, false) => some (.date, .date)
      | (false, false, false, true, true, true) => some (.time, .time)
      | (true, true, false, false, false, false) => some (.gYearMonth, .gYearMonth)
      | (true, false, false, false, false, false) => some (.gYear, .gYear)
      | (false, true, true, false, false, false) => some (.gMonthDay, .gMonthDay)
      | (false, true, false, false, false, false) => some (.gMonth, .gMonth)
      | (false, false, true, false, false, false) => some (.gDay, .gDay)
      | _ => none
    let some (k, ty) := kt | err "FODT0005" "the components present do not make a date/time type"
    let secV : Option Dec := sec.map (fun s => if Dec.cmp s Dec.zero == .eq then Dec.zero else Dec.norm s)
    let v : DTValue := DTValue.mk y (mo.map Int.toNat) (d.map Int.toNat) (h.map Int.toNat)
      (mi.map Int.toNat) secV tz
    pure [.atom ⟨.b ty, .x (.dt k v)⟩]
  | _ => err "XPTY0004" "build-dateTime needs a single map"

/-! ## `fn:round` with a rounding mode (§4.4.5)

The nine modes of the F&O 4.0 signature. The value is scaled by
10^precision; `q` is the floor of the scaled value and `r` the remainder
(0 ≤ r < den); the mode picks `q` or `q + 1`. -/

def roundDecMode (d : Dec) (prec : Int) (mode : String) : Dec :=
  let d := Dec.norm d
  let intDigits : Int := (natDigits d.mantissa.natAbs : Int) - (d.scale : Int)
  if d.mantissa == 0 || (prec ≥ 0 && d.scale ≤ prec.toNat) then d
  else if prec < 0 && -prec > intDigits + 1 && mode.startsWith "half-" then Dec.zero
  else
    let num : Int := if prec ≥ 0 then d.mantissa * (10 : Int) ^ prec.toNat else d.mantissa
    let den : Int := if prec ≥ 0 then (10 : Int) ^ d.scale else (10 : Int) ^ d.scale * (10 : Int) ^ (-prec).toNat
    let q := Int.fdiv num den
    let r := num - q * den
    let pos := num ≥ 0
    let up := q + 1
    let rounded :=
      if r == 0 then q
      else match mode with
      | "floor" => q
      | "ceiling" => up
      | "toward-zero" => if pos then q else up
      | "away-from-zero" => if pos then up else q
      | _ =>
        if 2 * r > den then up
        else if 2 * r < den then q
        else match mode with
          | "half-to-floor" => q
          | "half-toward-zero" => if pos then q else up
          | "half-away-from-zero" => if pos then up else q
          | "half-to-even" => if q % 2 == 0 then q else up
          | _ => up
    if prec ≥ 0 then Dec.norm ⟨rounded, prec.toNat⟩ else Dec.ofInt (rounded * (10 : Int) ^ (-prec).toNat)

def roundModeFn : LibFn := fun _ _ a => do
  let mode := if (argN a 2).isEmpty then "half-to-ceiling" else strOf (argN a 2)
  let prec := if (argN a 1).isEmpty then 0 else intOf (argN a 1)
  match optAtom (argN a 0) with
  | none => pure []
  | some x =>
    match x.num? with
    | some (.i i) =>
      if prec ≥ 0 then pure [.atom x]
      else match (roundDecMode (Dec.ofInt i) prec mode).toInt? with
        | some v => pure [.atom (Atomic.ofInt v)]
        | none => pure [.atom x]
    | some (.d d) => pure [.atom (Atomic.ofDec (roundDecMode d prec mode))]
    | some (.f f) | some (.g f) =>
      let mk := fun (y : Float) => if x.is .float then Atomic.ofFlt y else Atomic.ofDbl y
      if f.isNaN || f.isInf || f == 0 then pure [.atom x]
      else
        let r := floatOfDec (roundDecMode (decOfFloat f) prec mode)
        pure [.atom (mk (if r == 0 && f < 0 then -0.0 else r))]
    | none => pure [.atom x]

/-! ## `fn:unix-dateTime`, `fn:pad-string`, `fn:trim-space`, `fn:system-properties` -/

/-- The civil date of a day count from 1970-01-01 (the proleptic
    Gregorian calendar; H. Hinnant's `civil_from_days`). -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := Int.fdiv z 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  ((if m ≤ 2 then y + 1 else y), m.toNat, d.toNat)

def unixDateTimeFn : LibFn := fun _ _ a => do
  let ms := if (argN a 0).isEmpty then 0 else intOf (argN a 0)
  let days := Int.fdiv ms 86400000
  let rest := ms - days * 86400000
  let (y, m, d) := civilFromDays days
  let secMs := rest % 60000
  let v : DTValue := DTValue.mk (some y) (some m) (some d) (some (rest / 3600000).toNat)
    (some ((rest % 3600000) / 60000).toNat) (some (Dec.norm ⟨secMs, 3⟩)) (some 0)
  pure [.atom ⟨.b .dateTimeStamp, .x (.dt .dateTime v)⟩]

def enumOpt (e : Env) (opts : Seq) (key dflt : String) (allowed : List String) : M String := do
  match optLookup opts key with
  | none | some [] => pure dflt
  | some v =>
    match ← e.coerce (parseTy "xs:string") v key with
    | [.atom x] => if allowed.contains x.str then pure x.str else err "XPTY0004" (key ++ ": not an allowed value: " ++ x.str)
    | _ => err "XPTY0004" (key ++ " must be xs:string")

def padRun (pad : List Char) (n : Nat) : String :=
  String.ofList ((List.range n).map (fun i => pad.getD (i % pad.length) ' '))

def padStringFn : LibFn := fun _ e a => do
  let s := match optAtom (argN a 0) with
    | some x => x.str
    | none => ""
  let len := intOf (argN a 1)
  let opts := argN a 2
  let pad ← match optLookup opts "padding" with
    | none | some [] => pure " "
    | some v => match ← e.coerce (parseTy "xs:string") v "padding" with
      | [.atom x] => pure x.str
      | _ => err "XPTY0004" "padding must be xs:string"
  if pad == "" then err "FORG0001" "padding must not be a zero-length string"
  let side ← enumOpt e opts "side" "end" ["start", "end", "both"]
  let n : Nat := s.length
  if len ≤ Int.ofNat n then return sStr s
  let k : Nat := len.toNat - n
  let pc := pad.toList
  match side with
  | "start" => pure (sStr (padRun pc k ++ s))
  | "both" => pure (sStr (padRun pc (k / 2) ++ s ++ padRun pc (k - k / 2)))
  | _ => pure (sStr (s ++ padRun pc k))

def trimSpaceFn : LibFn := fun _ e a => do
  let s := match optAtom (argN a 0) with
    | some x => x.str
    | none => ""
  let side ← enumOpt e (argN a 1) "side" "both" ["start", "end", "both"]
  let cs := s.toList
  let cs := if side != "end" then cs.dropWhile isWs else cs
  let cs := if side != "start" then (cs.reverse.dropWhile isWs).reverse else cs
  pure (sStr (String.ofList cs))

def systemPropertiesFn : LibFn := fun _ _ _ =>
  let q (l : String) : Atomic := Atomic.ofQN { uri := "", loc := l }
  pure [.map [
    (q "xpath-version", [.atom (Atomic.ofDec ⟨40, 1⟩)]),
    (q "xsd-version", [.atom (Atomic.ofDec ⟨11, 1⟩)]),
    (q "product-name", [.atom (Atomic.ofStr "Factoidal")]),
    (q "product-version", [.atom (Atomic.ofStr "0.21")]),
    (q "schema-aware", [.atom (Atomic.ofBool false)]),
    (q "accepts-typed-data", [.atom (Atomic.ofBool false)]),
    (q "supports-xinclude", [.atom (Atomic.ofBool false)]),
    (q "supports-dtd-validation", [.atom (Atomic.ofBool false)]),
    (q "supports-dtd-attribute-typing", [.atom (Atomic.ofBool false)]),
    (q "supports-invisible-xml", [.atom (Atomic.ofBool false)]),
    (q "supports-dynamic-xquery", [.atom (Atomic.ofBool false)]),
    (q "supports-dynamic-xslt", [.atom (Atomic.ofBool false)]),
    (q "supports-binary-library", [.atom (Atomic.ofBool false)]),
    (q "supports-file-library", [.atom (Atomic.ofBool false)])]]

/-! ## `fn:slice` (§14.1.x) and `fn:scan` -/

/-- The rules of `fn:slice`, on a list; `rev` is the fuel for the one
    reversal a negative step makes. -/
def sliceList {α} : Nat → List α → Int → Int → Int → List α
  | 0, _, _, _, _ => []
  | rev + 1, xs, start, stop, step =>
    let n : Int := xs.length
    let s := if start == 0 && step < 0 then n else if start == 0 then 1 else if start < 0 then n + start + 1 else start
    let e := if stop == 0 && step < 0 then 1 else if stop == 0 then n else if stop < 0 then n + stop + 1 else stop
    let st := if step == 0 then (if e ≥ s then 1 else -1) else step
    if st < 0 then sliceList rev xs.reverse (-s) (-e) (-st)
    else
      (xs.zipIdx 1).filterMap (fun (x, p) =>
        let p : Int := p
        if p ≥ s && p ≤ e && (p - s) % st == 0 then some x else none)

def optInt (s : Seq) : Int := if s.isEmpty then 0 else intOf s

def sliceFn : LibFn := fun _ _ a =>
  pure (sliceList 2 (argN a 0) (optInt (argN a 1)) (optInt (argN a 2)) (optInt (argN a 3)))

def scanFn : LibFn := fun h _ a => do
  let mut acc := argN a 1
  let mut out : Array Item := #[.arr [acc]]
  let mut pos : Int := 1
  for x in argN a 0 do
    acc ← h.callN (argN a 2 |>.headD (.atom default)) [acc, [x], sInt pos]
    out := out.push (.arr [acc])
    pos := pos + 1
  pure out.toList

def fn4Table : List (String × LibFn) :=
  [("hash", hashFn), ("random-number-generator", rngFn), ("rng-record#", rngRecordFn),
   ("rng-permute#", rngPermuteFn), ("rng-take#", rngTakeFn),
   ("parts-of-dateTime", partsOfDateTimeFn), ("build-dateTime", buildDateTimeFn),
   ("round", roundModeFn), ("unix-dateTime", unixDateTimeFn), ("pad-string", padStringFn),
   ("trim-space", trimSpaceFn), ("system-properties", systemPropertiesFn),
   ("slice", sliceFn), ("scan", scanFn)]

end L4Factoidal.XPath4
