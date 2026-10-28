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

def fn4Table : List (String × LibFn) :=
  [("hash", hashFn), ("random-number-generator", rngFn), ("rng-record#", rngRecordFn),
   ("rng-permute#", rngPermuteFn), ("rng-take#", rngTakeFn),
   ("parts-of-dateTime", partsOfDateTimeFn), ("build-dateTime", buildDateTimeFn)]

end L4Factoidal.XPath4
