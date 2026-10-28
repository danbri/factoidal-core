/-
L4Factoidal.XPath4.Fn4 — F&O 4.0 functions added after Stage 2:
`fn:hash` (§5.3.18), `fn:random-number-generator` (§5.13.2),
`fn:parts-of-dateTime` and `fn:build-dateTime` (§9.5).

Spec: F&O 4.0 editor's draft (read 2026-10-28).
-/
import L4Factoidal.XPath4.Serialize
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

/-! ## `fn:xsd-validator` (F&O 4.0 §21, schema validation)

The validator is a function item that calls `xsd-validate#` with the
options; the validation itself is the host's schema hook
(`SchemaHook.validateWith`, supplied by `L4Factoidal.XSD11`). -/

def xsdQ (l : String) : QN := { uri := nsFN, loc := l }

def xsdValidatorFn : LibFn := fun _ _ a => do
  let opts : Item := match argN a 0 with
    | [m@(.map _)] => m
    | _ => .map []
  let vOpt : QN := { uri := "#xsd", loc := "options" }
  let vNode : QN := { uri := "#xsd", loc := "node" }
  pure [.fn (.inline [(vNode, parseTy "item()*")] (parseTy "item()*")
    (.call (xsdQ "xsd-validate#") [some (.var vOpt), some (.var vNode)] []) false [(vOpt, [opts])])]

def optEntry (opts : Seq) (k : String) : Option Seq :=
  match opts with
  | [.map kvs] => (kvs.find? (fun (key, _) => key.isStringLike && key.str == k)).map (·.2)
  | _ => none

def xsdValidateFn : LibFn := fun _ e a => do
  let opts := argN a 0
  let mode := match optEntry opts "validation-mode" with
    | some [.atom m] => m.str
    | _ => "strict"
  let mode ← if mode == "by-type" then
      match optEntry opts "type" with
      | some [.atom t] => match t.v with
        | .qn q => pure ("type Q{" ++ q.uri ++ "}" ++ q.loc)
        | _ => err "XPTY0004" "the type option must be an xs:QName"
      | _ => err "XPTY0004" "validation-mode by-type needs the type option"
    else if mode == "strict" || mode == "lax" then pure mode
    else err "XPTY0004" ("unknown validation-mode " ++ mode)
  let retNode := match optEntry opts "return-typed-node" with
    | some [.atom b] => b.str != "false"
    | _ => true
  let retErrs := match optEntry opts "return-error-details" with
    | some [.atom b] => b.str == "true"
    | _ => false
  let schemaNodes : List (Doc × Nat) := match optEntry opts "schema" with
    | some s => s.filterMap (fun i => match i with
      | .node n => some (e.doc n, n.idx)
      | _ => none)
    | none => []
  match argN a 1 with
  | [] => pure []
  | [.node n] =>
    let r := e.nrec n
    if r.kind != .document && r.kind != .element then err "XPTY0004" "xsd-validator needs a document or element node"
    if r.kind == .document &&
       (r.children.toList.filter (fun c => (e.nrec (n.at c)).kind == .element)).length != 1 then
      err "XPTY0004" "the document node must have exactly one element child"
    match e.schema.validateWith with
    | none => err "FODC0009" "no schema processor is available"
    | some f =>
      let d := e.doc n
      match f mode schemaNodes d n.idx d.uri with
      | .error x => throw x
      | .ok (res, errs) =>
        let id := n.doc + (2 : Nat) ^ 42
        let typed : List Item := match res with
          | some nd => if r.kind == .document then [.node { doc := id, idx := 0, rt := some nd }]
                       else [.node { doc := id, idx := 1, rt := some nd }]
          | none => []
        let entries : List (Atomic × Seq) :=
          [(Atomic.ofStr "is-valid", [.atom (Atomic.ofBool res.isSome)])] ++
          (if retNode && res.isSome then [(Atomic.ofStr "typed-node", typed)] else []) ++
          (if retErrs && res.isNone then
             [(Atomic.ofStr "error-details", errs.map (fun m => Item.map [(Atomic.ofStr "message", [.atom (Atomic.ofStr m)])]))]
           else [])
        pure [.map entries]
  | _ => err "XPTY0004" "xsd-validator needs one document or element node"

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
    (q "schema-aware", [.atom (Atomic.ofBool true)]),
    (q "accepts-typed-data", [.atom (Atomic.ofBool true)]),
    (q "supports-xinclude", [.atom (Atomic.ofBool false)]),
    (q "supports-dtd-validation", [.atom (Atomic.ofBool false)]),
    (q "supports-dtd-attribute-typing", [.atom (Atomic.ofBool false)]),
    (q "supports-invisible-xml", [.atom (Atomic.ofBool false)]),
    (q "supports-dynamic-xquery", [.atom (Atomic.ofBool false)]),
    (q "supports-dynamic-xslt", [.atom (Atomic.ofBool false)]),
    (q "supports-binary-library", [.atom (Atomic.ofBool true)]),
    (q "supports-file-library", [.atom (Atomic.ofBool true)])]]

/-! ## `fn:scan` -/

def optInt (s : Seq) : Int := if s.isEmpty then 0 else intOf s

def scanFn : LibFn := fun h _ a => do
  let mut acc := argN a 1
  let mut out : Array Item := #[.arr [acc]]
  let mut pos : Int := 1
  for x in argN a 0 do
    acc ← h.callN (argN a 2 |>.headD (.atom default)) [acc, [x], sInt pos]
    out := out.push (.arr [acc])
    pos := pos + 1
  pure out.toList

/-! ## `fn:path` with options (§14.1.x): `origin`, `lexical`, `namespaces`, `indexes` -/

structure PathOpts where
  origin : Option NodeRef := none
  lexical : Bool := false
  nsMap : Option (List (String × String)) := none
  indexes : Bool := true

def PathOpts.prefixFor (o : PathOpts) (u : String) : Option String :=
  o.nsMap.bind (fun m => (m.find? (fun (p, v) => p != "" && v == u)).map (·.1))

def PathOpts.elemName (o : PathOpts) (q : QN) : String :=
  if o.lexical then q.show
  else match o.nsMap with
    | some m =>
      if q.uri != "" then
        match o.prefixFor q.uri with
        | some p => p ++ ":" ++ q.loc
        | none => if m.any (fun (p, v) => p == "" && v == q.uri) then q.loc else q.eqn
      else if m.all (fun (p, v) => p != "" || v == "") then q.loc else q.eqn
    | none => q.eqn

def PathOpts.attrName (o : PathOpts) (q : QN) : String :=
  if o.lexical then q.show
  else if q.uri == "" then q.loc
  else match o.prefixFor q.uri with
    | some p => p ++ ":" ++ q.loc
    | none => q.eqn

def Env.pathStep (e : Env) (o : PathOpts) (m : NodeRef) : String :=
  let r := e.nrec m
  let sameKind (c : Nat) : Bool :=
    let rc := e.nrec (m.at c)
    rc.kind == r.kind && (r.kind != .element || rc.name == r.name) && (r.kind != .pi || rc.name.loc == r.name.loc)
  let pos : Nat := match r.parent with
    | some p => (((e.doc m).get p).children.toList.filter (fun c => c ≤ m.idx && sameKind c)).length
    | none => 1
  let ix := if o.indexes then "[" ++ toString pos ++ "]" else ""
  match r.kind with
  | .document => ""
  | .element => o.elemName r.name ++ ix
  | .attribute => "@" ++ o.attrName r.name
  | .text => "text()" ++ ix
  | .comment => "comment()" ++ ix
  | .pi => "processing-instruction(" ++ r.name.loc ++ ")" ++ ix
  | .namespace => "namespace::" ++ (if r.name.loc == "" then "*[Q{http://www.w3.org/2005/xpath-functions}local-name()=\"\"]" else r.name.loc)

def pathOptsOf (e : Env) (opts : Seq) : M PathOpts := do
  let origin ← match optLookup opts "origin" with
    | none | some [] => pure none
    | some [.node n] => pure (some n)
    | some _ => err "XPTY0004" "the origin option must be a single node"
  let lexical ← optBool opts "lexical" false
  let indexes ← optBool opts "indexes" true
  let nsMap ← match optLookup opts "namespaces" with
    | none | some [] => pure none
    | some [.map kvs] => pure (some (kvs.map (fun (k, v) => (k.str, strOf v))))
    | some _ => err "XPTY0004" "the namespaces option must be a map"
  pure { origin, lexical, nsMap, indexes }

def pathFn : LibFn := fun h e a => do
  match argN a 0 with
  | [.jnode ..] =>
    match libLookup { uri := nsFN, loc := "path" } with
    | some f => f h e a
    | none => pure []
  | [] => pure []
  | [.node n] =>
    let o ← pathOptsOf e (argN a 1)
    let chain := (n :: e.ancestors n).reverse
    match o.origin with
    | some r =>
      match (chain.dropLast).findIdx? (fun m => m == r) with
      | none => err "FOPA0001" "the origin is not an ancestor of the node"
      | some i =>
        let steps := (chain.drop (i + 1)).map (e.pathStep o)
        pure (sStr (String.intercalate "/" steps))
    | none =>
      match chain with
      | [] => pure []
      | top :: rest =>
        let topR := e.nrec top
        if topR.kind == .document && rest.isEmpty then return sStr "/"
        let pre :=
          if topR.kind == .document then ""
          else if o.lexical then "fn:root()"
          else match o.nsMap with
            | some m =>
              match m.find? (fun (p, v) => p != "" && v == nsFN) with
              | some (p, _) => p ++ ":root()"
              | none => if m.any (fun (p, v) => p == "" && v == nsFN) then "root()" else "Q{" ++ nsFN ++ "}root()"
            | none => "Q{" ++ nsFN ++ "}root()"
        pure (sStr (pre ++ String.join (rest.map (fun m => "/" ++ e.pathStep o m))))
  | _ => err "XPTY0004" "fn:path needs a node"

/-- `fn:in-scope-namespaces` (§10.2.x): the in-scope namespace bindings
    of an element, as a map from prefix to URI (the `xml` binding
    included). -/
def inScopeNamespacesFn : LibFn := fun _ e a => do
  match argN a 0 with
  | [.node n] =>
    let r := e.nrec n
    if r.kind != .element then err "XPTY0004" "in-scope-namespaces needs an element"
    let sc := (effectiveScope r.inscope).filter (fun (_, u) => u != "")
    let sc := if sc.any (·.1 == "xml") then sc else sc ++ [("xml", nsXML)]
    let sc := if r.name.uri != "" && !sc.any (·.1 == r.name.pfx) then sc ++ [(r.name.pfx, r.name.uri)] else sc
    pure [.map (sc.map (fun (p, u) => (Atomic.ofStr p, [.atom (Atomic.ofUri u)])))]
  | _ => err "XPTY0004" "in-scope-namespaces needs an element"

/-! ## The F&O 4.0 total order of atomic items: `fn:compare`, `fn:min`, `fn:max`

F&O 4.0 §5.3.6 `fn:compare` orders strings by the collation, numerics by
their exact mathematical value (NaN first, then -INF, ..., INF; a double
is compared exactly, as the rational number it denotes), booleans,
binary values by their octets, the eight date/time types after the
missing components are taken from 1972-01-01T00:00:00 and a missing
timezone from the implicit timezone, durations by months then seconds,
QNames by namespace URI then local name; any other pair raises
XPTY0004. `fn:min` and `fn:max` (§14.4) use that order and return an
item of the input (after untypedAtomic is cast to xs:double). -/

/-- The days from 1970-01-01 of a civil date (H. Hinnant's
    `days_from_civil`, the inverse of `civilFromDays`). -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := Int.fdiv y 400
  let yoe := y - era * 400
  let mp : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy := (153 * mp + 2) / 5 + (d : Int) - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- An exact rational `(num, den)`, den > 0, of a finite numeric value. -/
def exactRat : Num → Int × Nat
  | .i i => (i, 1)
  | .d d => (d.mantissa, 10 ^ d.scale)
  | .f f | .g f =>
    let (neg, n, dn) := floatParts f
    ((if neg then -(n : Int) else n), dn)

def numKind (n : Num) : Nat :=
  -- 0 NaN, 1 -INF, 2 finite, 3 +INF
  match n with
  | .f f | .g f => if f.isNaN then 0 else if f.isInf then (if f < 0 then 1 else 3) else 2
  | _ => 2

def cmpNat (a b : Nat) : Ordering := if a < b then .lt else if a == b then .eq else .gt
def cmpInt (a b : Int) : Ordering := if a < b then .lt else if a == b then .eq else .gt

def cmpNum (a b : Num) : Ordering :=
  let ka := numKind a
  let kb := numKind b
  if ka != 2 || kb != 2 then cmpNat ka kb
  else
    let (p, q) := exactRat a
    let (r, s) := exactRat b
    cmpInt (p * s) (r * q)

def lexCmp : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs => if a < b then .lt else if a > b then .gt else lexCmp as bs

/-- The instant of a date/time value in seconds, its missing components
    taken from 1972-01-01T00:00:00 and the implicit timezone. -/
def dtInstant (tz : Int) (v : DTValue) : Dec :=
  let y := v.year.getD 1972
  let m := v.month.getD 1
  let d := v.day.getD 1
  let days := daysFromCivil y m d
  let secs : Int := days * 86400 + (v.hour.getD 0 : Int) * 3600 + (v.minute.getD 0 : Int) * 60 - (v.tz.getD tz) * 60
  let s := v.second.getD Dec.zero
  Dec.norm ⟨secs * 10 ^ s.scale + s.mantissa, s.scale⟩

def dtPrim : DTKind → Nat
  | .dateTime => 0 | .date => 1 | .time => 2 | .gYearMonth => 3 | .gYear => 4
  | .gMonthDay => 5 | .gDay => 6 | .gMonth => 7

def strLike (a : Atomic) : Bool := a.ty == .untyped || a.is .string || a.is .anyURI

def compareAtoms (c : Coll) (tz : Int) (x y : Atomic) : M Ordering := do
  if strLike x && strLike y then return c.compare x.str y.str
  match x.num?, y.num? with
  | some a, some b => return cmpNum a b
  | _, _ => pure ()
  match x.v, y.v with
  | .bool a, .bool b => pure (cmpNat (if a then 1 else 0) (if b then 1 else 0))
  | .x (.bin _ p), .x (.bin _ q) => pure (lexCmp p q)
  | .x (.dt k1 v1), .x (.dt k2 v2) =>
    if dtPrim k1 != dtPrim k2 then err "XPTY0004" "date/time values of different types are not comparable"
    else pure (Dec.cmp (dtInstant tz v1) (dtInstant tz v2))
  | .x (.dur d1), .x (.dur d2) =>
    match cmpInt d1.months d2.months with
    | .eq => pure (Dec.cmp d1.seconds d2.seconds)
    | o => pure o
  | .qn p, .qn q =>
    if (x.is .notation) != (y.is .notation) then err "XPTY0004" "a QName and a NOTATION are not comparable"
    else match compare p.uri q.uri with
      | .eq => pure (compare p.loc q.loc)
      | o => pure o
  | _, _ => err "XPTY0004" ("values of types xs:" ++ x.ty.name ++ " and xs:" ++ y.ty.name ++ " are not comparable")

def ordInt : Ordering → Int | .lt => -1 | .eq => 0 | .gt => 1

def compareFn : LibFn := fun _ e a => do
  let c ← e.collation (argN a 2)
  match optAtom (argN a 0), optAtom (argN a 1) with
  | some x, some y => pure (sInt (ordInt (← compareAtoms c e.tz x y)))
  | _, _ => pure []

def isNaNAtom (a : Atomic) : Bool :=
  match a.num? with
  | some (.f f) | some (.g f) => f.isNaN
  | _ => false

/-- The items are taken in order: a NaN met before any type error is the
    result (the qt4tests cases K-SeqMINFunc-21a and -22 fix this order). -/
def minMax4 (isMax : Bool) : LibFn := fun _ e a => do
  let c ← e.collation (argN a 1)
  let xs ← e.atomize (argN a 0)
  let mut best : Option Atomic := none
  for x0 in xs do
    let x ← if x0.ty == .untyped then castAtomic x0 (.b .double) else pure x0
    if isNaNAtom x then return [.atom x]
    match best with
    | none => best := some x
    | some b =>
      match compareAtoms c e.tz x b with
      | .error _ => err "FORG0006" "the values are not mutually comparable"
      | .ok o => if (isMax && o == .gt) || (!isMax && o == .lt) then best := some x
  pure (match best with | some b => [.atom b] | none => [])

/-! ## `fn:decode-from-uri` and `fn:unparsed-binary` -/

/-- UTF-8 decoding where an invalid or incomplete sequence becomes one
    U+FFFD for the octets read so far (F&O 4.0 `fn:decode-from-uri`: the
    octets x41 xF0 x9F x92 x41 decode as "A\uFFFDA"). -/
def utf8Maximal (bs : List Nat) : String := Id.run do
  let arr := bs.toArray
  let n := arr.size
  let mut out : String := ""
  let mut i := 0
  for _ in [0:n] do
    if i ≥ n then break
    let b0 := arr[i]!
    if b0 < 0x80 then out := out.push (Char.ofNat b0); i := i + 1; continue
    let (len, lo, hi, init) :=
      if 0xC2 ≤ b0 && b0 ≤ 0xDF then (2, 0x80, 0xBF, b0 &&& 0x1F)
      else if b0 == 0xE0 then (3, 0xA0, 0xBF, b0 &&& 0x0F)
      else if 0xE1 ≤ b0 && b0 ≤ 0xEC then (3, 0x80, 0xBF, b0 &&& 0x0F)
      else if b0 == 0xED then (3, 0x80, 0x9F, b0 &&& 0x0F)
      else if 0xEE ≤ b0 && b0 ≤ 0xEF then (3, 0x80, 0xBF, b0 &&& 0x0F)
      else if b0 == 0xF0 then (4, 0x90, 0xBF, b0 &&& 0x07)
      else if 0xF1 ≤ b0 && b0 ≤ 0xF3 then (4, 0x80, 0xBF, b0 &&& 0x07)
      else if b0 == 0xF4 then (4, 0x80, 0x8F, b0 &&& 0x07)
      else (0, 0, 0, 0)
    if len == 0 then out := out.push '\uFFFD'; i := i + 1; continue
    let mut cp := init
    let mut j := 1
    let mut ok := true
    for k in [1:len] do
      let b := arr.getD (i + k) 256
      let (l, h) := if k == 1 then (lo, hi) else (0x80, 0xBF)
      if l ≤ b && b ≤ h then cp := cp * 64 + (b &&& 0x3F); j := j + 1
      else ok := false; break
    if ok then out := out.push (Char.ofNat cp) else out := out.push '\uFFFD'
    i := i + j
  return out

def hexDigitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- The percent decoding works on the UTF-8 octets of the value: `%`
    and two hexadecimal digits give one octet; `%` followed by octets that
    are not two hexadecimal digits gives U+FFFD for `%` and up to two of
    them. A decoded character that XML does not allow becomes U+FFFD. -/
def decodeFromUriFn : LibFn := fun _ _ a => do
  let src := (strOf (argN a 0)).toUTF8.toList.map (·.toNat) |>.toArray
  let hexv (b : Nat) : Option Nat :=
    if 0x30 ≤ b && b ≤ 0x39 then some (b - 0x30)
    else if 0x61 ≤ b && b ≤ 0x66 then some (b - 0x57)
    else if 0x41 ≤ b && b ≤ 0x46 then some (b - 0x37)
    else none
  let mut octs : Array Nat := #[]
  let mut i := 0
  for _ in [0:src.size] do
    if i ≥ src.size then break
    let b := src[i]!
    if b == 0x25 then
      match (src[i + 1]?).bind hexv, (src[i + 2]?).bind hexv with
      | some h, some l => octs := octs.push (h * 16 + l); i := i + 3
      | _, _ =>
        octs := octs ++ #[0xEF, 0xBF, 0xBD]
        i := i + 1 + min 2 (src.size - (i + 1))
    else
      octs := octs.push b; i := i + 1
  let t := utf8Maximal octs.toList
  pure (sStr (String.ofList (t.toList.map (fun c => if isXmlCp c.toNat then c else '\uFFFD'))))

def unparsedBinaryFn : LibFn := fun _ e a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some h =>
    match e.resourceBin h.str with
    | some bs => pure [.atom ⟨.b .base64Binary, .x (.bin false (bs.toList.map (·.toNat)))⟩]
    | none => err "FOUT1170" ("resource not available: " ++ h.str)

/-! ## `fn:id`, `fn:element-with-id`, `fn:idref` (§14.6.x)

The is-id property of an attribute: `xml:id`, or an attribute the DTD of
its document declares `ID`; is-idrefs: one the DTD declares `IDREF` or
`IDREFS`; or a node whose schema type annotation (`NRec.tann`) is derived
from `xs:ID` (an element of that type is itself an ID), `xs:IDREF` or
`xs:IDREFS`. -/

def qnameAsWritten (q : QN) : String := if q.pfx == "" then q.loc else q.pfx ++ ":" ++ q.loc

def idTokens (vs : Seq) : List String :=
  vs.flatMap (fun v => match v with
    | .atom a => (normSpace a.str).splitOn " " |>.filter (· != "")
    | _ => [])

def Env.idTarget (e : Env) (a : List Seq) : M NodeRef := do
  match argN a 1 with
  | [.node n] =>
    let root := (e.ancestors n).getLast?.getD n
    if (e.nrec root).kind != .document then err "FODC0001" "the node is not in a document"
    pure root
  | _ => err "XPTY0004" "the second argument must be a node"

def idFn : LibFn := fun _ e a => do
  let root ← e.idTarget a
  let cands := idTokens (argN a 0)
  let d := e.doc root
  let mut out : Array Item := #[]
  for i in [0:d.nodes.size] do
    let r := d.get i
    if r.kind != .element then continue
    let hit := r.attrs.toList.any (fun ai =>
      let ar := d.get ai
      let isId := (ar.name.uri == nsXML && ar.name.loc == "id") ||
        d.idAttrs.contains (qnameAsWritten r.name, qnameAsWritten ar.name) ||
        -- an attribute with a schema type derived from xs:ID
        ar.tann.any (fun t => e.schema.derives t { uri := nsXS, loc := "ID" })
      isId && cands.contains (normSpace ar.value))
    -- an element whose schema type is derived from xs:ID is itself an ID
    let selfId := r.tann.any (fun t => e.schema.derives t { uri := nsXS, loc := "ID" }) &&
      cands.contains (normSpace (d.stringValue i))
    if hit || selfId then out := out.push (.node (root.at i))
  pure out.toList

def idrefFn : LibFn := fun _ e a => do
  let root ← e.idTarget a
  let cands := idTokens (argN a 0)
  let d := e.doc root
  let mut out : Array Item := #[]
  for i in [0:d.nodes.size] do
    let r := d.get i
    if r.kind != .attribute then continue
    let some p := r.parent | continue
    let pr := d.get p
    let typed := r.tann.any (fun t => e.schema.derives t { uri := nsXS, loc := "IDREF" } ||
      e.schema.derives t { uri := nsXS, loc := "IDREFS" })
    if !typed && !d.idrefAttrs.contains (qnameAsWritten pr.name, qnameAsWritten r.name) then continue
    let toks := (normSpace r.value).splitOn " "
    if toks.any (fun t => cands.contains t) then out := out.push (.node (root.at i))
  pure out.toList

def fn4Table : List (String × LibFn) :=
  [("hash", hashFn), ("random-number-generator", rngFn), ("rng-record#", rngRecordFn),
   ("xsd-validator", xsdValidatorFn), ("xsd-validate#", xsdValidateFn),
   ("rng-permute#", rngPermuteFn), ("rng-take#", rngTakeFn),
   ("parts-of-dateTime", partsOfDateTimeFn), ("build-dateTime", buildDateTimeFn),
   ("round", roundModeFn), ("unix-dateTime", unixDateTimeFn), ("pad-string", padStringFn),
   ("trim-space", trimSpaceFn), ("system-properties", systemPropertiesFn),
   ("scan", scanFn), ("path", pathFn),
   ("in-scope-namespaces", inScopeNamespacesFn), ("compare", compareFn),
   ("decode-from-uri", decodeFromUriFn), ("unparsed-binary", unparsedBinaryFn),
   ("min", minMax4 false), ("max", minMax4 true),
   ("id", idFn), ("element-with-id", idFn), ("idref", idrefFn)]

end L4Factoidal.XPath4
