/-
L4Factoidal.HTML.InputValue — the value of an `input` element as its type reads it: the
microsyntaxes of dates and times, the conversion between a value and a number, the value
sanitization algorithm, stepping, and the constraints that depend on the value.

Specification: HTML Living Standard §2.3.5 "Dates and times" (valid date, month, week,
time and local date and time strings), §2.3.4.3 (valid floating-point numbers), §4.10.5.1
(the states of the type attribute: value sanitization, "convert a string to a number",
"convert a number to a string"), §4.10.5.3 (min, max, step), §4.10.5.4 (`stepUp`,
`stepDown`, `valueAsNumber`, `valueAsDate`), §4.10.21.2 (constraints).

Numbers are IEEE doubles (`Float`), as `valueAsNumber` is: milliseconds since 1970-01-01
for date, week, time and local date and time; months since January 1970 for month. The
calendar is computed on integers and converted.
-/
import L4Factoidal.JS.Number

namespace L4Factoidal.HTML.InputValue

/-- The states of the type attribute whose value converts to a number. -/
inductive Ty where
  | date | month | week | time | datetimeLocal | number | range
  deriving Repr, DecidableEq, Inhabited

def Ty.ofString (s : String) : Option Ty :=
  match s with
  | "date" => some .date | "month" => some .month | "week" => some .week | "time" => some .time
  | "datetime-local" => some .datetimeLocal | "number" => some .number | "range" => some .range
  | _ => none

/-! ## Calendar arithmetic on integers (proleptic Gregorian) -/

def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The number a list of ASCII digits writes; `none` for an empty list or another character. -/
def digits? (cs : List Char) : Option Nat :=
  if cs.isEmpty || !cs.all isDigit then none else some (cs.foldl (fun n c => n * 10 + (c.toNat - 48)) 0)

def isLeap (y : Nat) : Bool := (y % 4 == 0 && y % 100 != 0) || y % 400 == 0

def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeap y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- Days from 1970-01-01 to the first day of year `y` (`y ≥ 1`). -/
def daysToYear (y : Nat) : Int :=
  let p := y - 1
  (365 * p + p / 4 - p / 100 + p / 400 : Nat) - 719162

/-- Days from 1970-01-01 to `y`-`m`-`d`. -/
def daysFromCivil (y m d : Nat) : Int :=
  daysToYear y + ((List.range (m - 1)).foldl (fun n i => n + daysInMonth y (i + 1)) 0 : Nat) + (d - 1 : Nat)

/-- The year, month and day of a day count from 1970-01-01, for years 1 to 275760 (the range
of a Date object); `none` outside. The year is found from an estimate and at most two
corrections. -/
def civilFromDays (z : Int) : Option (Nat × Nat × Nat) :=
  let n := z + 719162
  if n < 0 then none else
  let est := n.toNat * 400 / 146097 + 1
  let y := if daysToYear est > z then est - 1 else if daysToYear (est + 1) ≤ z then est + 1 else est
  if y == 0 || y > 275760 then none else
  let rem := (z - daysToYear y).toNat
  let rec go : Nat → Nat → Nat → Nat × Nat
    | 0, m, r => (m, r)
    | fuel + 1, m, r => if r < daysInMonth y m || m == 12 then (m, r) else go fuel (m + 1) (r - daysInMonth y m)
  let (m, r) := go 12 1 rem
  some (y, m, r + 1)

/-- ISO weekday of a day count: 1 Monday to 7 Sunday (1970-01-01 was a Thursday). -/
def weekday (z : Int) : Nat := ((z + 3) % 7).toNat + 1

/-- Weeks in ISO week-year `y`: 53 when January 1 is a Thursday, or a Wednesday in a leap
year; else 52 (HTML §2.3.5.8). -/
def weeksInYear (y : Nat) : Nat :=
  let wd := weekday (daysToYear y)
  if wd == 4 || (wd == 3 && isLeap y) then 53 else 52

/-- Days from 1970-01-01 to the Monday of week `w` of week-year `y`. -/
def weekStart (y w : Nat) : Int :=
  let jan4 := daysToYear y + 3
  jan4 - ((weekday jan4 : Nat) - 1 : Nat) + (7 * (w - 1) : Nat)

/-! ## Parsing the microsyntaxes -/

/-- A valid date string: the year (four or more digits, greater than 0), month and day. -/
def parseDate (s : String) : Option (Nat × Nat × Nat) :=
  match s.splitOn "-" with
  | [y, m, d] =>
    if y.length < 4 || m.length != 2 || d.length != 2 then none else
    match digits? y.toList, digits? m.toList, digits? d.toList with
    | some y, some m, some d =>
      if y == 0 || m == 0 || m > 12 || d == 0 || d > daysInMonth y m then none else some (y, m, d)
    | _, _, _ => none
  | _ => none

def parseMonth (s : String) : Option (Nat × Nat) :=
  match s.splitOn "-" with
  | [y, m] =>
    if y.length < 4 || m.length != 2 then none else
    match digits? y.toList, digits? m.toList with
    | some y, some m => if y == 0 || m == 0 || m > 12 then none else some (y, m)
    | _, _ => none
  | _ => none

def parseWeek (s : String) : Option (Nat × Nat) :=
  match s.splitOn "-W" with
  | [y, w] =>
    if y.length < 4 || w.length != 2 then none else
    match digits? y.toList, digits? w.toList with
    | some y, some w => if y == 0 || w == 0 || w > weeksInYear y then none else some (y, w)
    | _, _ => none
  | _ => none

/-- A valid time string, as milliseconds after midnight: "HH:MM", "HH:MM:SS" or
"HH:MM:SS.f" with one to three fraction digits. -/
def parseTime (s : String) : Option Nat :=
  let hm := fun (h m : String) =>
    if h.length != 2 || m.length != 2 then none else
    match digits? h.toList, digits? m.toList with
    | some h, some m => if h > 23 || m > 59 then none else some (h * 3600000 + m * 60000)
    | _, _ => none
  match s.splitOn ":" with
  | [h, m] => hm h m
  | [h, m, sec] =>
    match sec.splitOn "." with
    | [ss] =>
      if ss.length != 2 then none else
      match hm h m, digits? ss.toList with
      | some t, some ss => if ss > 59 then none else some (t + ss * 1000)
      | _, _ => none
    | [ss, f] =>
      if ss.length != 2 || f.length == 0 || f.length > 3 then none else
      match hm h m, digits? ss.toList, digits? f.toList with
      | some t, some ss, some fv =>
        if ss > 59 then none else some (t + ss * 1000 + fv * (if f.length == 1 then 100 else if f.length == 2 then 10 else 1))
      | _, _, _ => none
    | _ => none
  | _ => none

/-- A valid local date and time string: a date, "T" or a space, and a time; as milliseconds
since 1970-01-01T00:00. -/
def parseLocal (s : String) : Option Int :=
  let parts := if s.contains 'T' then s.splitOn "T" else s.splitOn " "
  match parts with
  | [d, t] =>
    match parseDate d, parseTime t with
    | some (y, m, dd), some ms => some (daysFromCivil y m dd * 86400000 + ms)
    | _, _ => none
  | _ => none

/-- A valid floating-point number (HTML §2.3.4.3): an optional "-", digits and/or a "." with
digits, an optional exponent. -/
def validFloat (s : String) : Bool :=
  let cs := s.toList
  let cs := match cs with | '-' :: r => r | r => r
  let int := cs.takeWhile isDigit
  let rest := cs.dropWhile isDigit
  let (frac, rest, fracOk) := match rest with
    | '.' :: r => let f := r.takeWhile isDigit; (f, r.dropWhile isDigit, !f.isEmpty)
    | r => ([], r, true)
  let expOk := match rest with
    | [] => true
    | c :: r =>
      if c == 'e' || c == 'E' then
        let r := match r with | '-' :: q => q | '+' :: q => q | q => q
        !r.isEmpty && r.all isDigit
      else false
  fracOk && (!int.isEmpty || !frac.isEmpty) && expOk

/-! ## A value as a number, and back -/

def pad (n width : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (width - s.length) '0') ++ s

/-- "Convert a string to a number" for each state; `none` when the string is not valid. -/
def toNumber (t : Ty) (s : String) : Option Float :=
  match t with
  | .date => (parseDate s).map fun (y, m, d) => Float.ofInt (daysFromCivil y m d * 86400000)
  | .month => (parseMonth s).map fun (y, m) => Float.ofInt (((y : Int) - 1970) * 12 + ((m : Int) - 1))
  | .week => (parseWeek s).map fun (y, w) => Float.ofInt (weekStart y w * 86400000)
  | .time => (parseTime s).map fun ms => Float.ofNat ms
  | .datetimeLocal => (parseLocal s).map Float.ofInt
  | .number | .range => if validFloat s then some (L4Factoidal.JS.strToNumber s) else none

def dateString (y m d : Nat) : String := pad y 4 ++ "-" ++ pad m 2 ++ "-" ++ pad d 2

/-- A time of day in milliseconds as the shortest valid time string. -/
def timeString (ms : Nat) : String :=
  let h := ms / 3600000; let m := ms / 60000 % 60; let s := ms / 1000 % 60; let f := ms % 1000
  let base := pad h 2 ++ ":" ++ pad m 2
  if s == 0 && f == 0 then base
  else if f == 0 then base ++ ":" ++ pad s 2
  else
    let fs := pad f 3
    let fs := if f % 100 == 0 then (fs.take 1).toString else if f % 10 == 0 then (fs.take 2).toString else fs
    base ++ ":" ++ pad s 2 ++ "." ++ fs

/-- The integer a finite Float holds, when it is integral. -/
def intOf (x : Float) : Option Int :=
  if !x.isFinite || x.floor != x then none
  else some (if x < 0 then -((-x).toUInt64.toNat : Int) else (x.toUInt64.toNat : Int))

/-- "Convert a number to a string" for each state; `none` when the number has no string (not
an integer where one is needed, or outside the calendar's range). -/
def ofNumber (t : Ty) (x : Float) : Option String :=
  match t with
  | .number | .range => if x.isFinite then some (L4Factoidal.JS.numToString x) else none
  | .month => (intOf x).bind fun k =>
      let y := 1970 + k.fdiv 12
      if y < 1 || y > 275760 then none else some (pad y.toNat 4 ++ "-" ++ pad ((k.fmod 12).toNat + 1) 2)
  | .time => (intOf x).bind fun k => if k < 0 then none else some (timeString (k.toNat % 86400000))
  | .date => (intOf x).bind fun k => (civilFromDays (k.fdiv 86400000)).map fun (y, m, d) => dateString y m d
  | .datetimeLocal => (intOf x).bind fun k =>
      (civilFromDays (k.fdiv 86400000)).map fun (y, m, d) => dateString y m d ++ "T" ++ timeString (k.fmod 86400000).toNat
  | .week => (intOf x).bind fun k =>
      let day := k.fdiv 86400000
      -- the week-year is the year of the week's Thursday
      let thursday := day - ((weekday day : Nat) - 1 : Nat) + 3
      (civilFromDays thursday).map fun (y, _, _) =>
        pad y 4 ++ "-W" ++ pad (((thursday - (weekStart y 1 + 3)) / 7).toNat + 1) 2

/-! ## min, max and step (HTML §4.10.5.3.7 and §4.10.5.3.8) -/

/-- The default step and the step scale factor, in the state's number. -/
def defaultStep : Ty → Float
  | .date => 1 | .month => 1 | .week => 1 | .time => 60 | .datetimeLocal => 60 | .number => 1 | .range => 1

def stepScale : Ty → Float
  | .date => 86400000 | .month => 1 | .week => 604800000 | .time => 1000 | .datetimeLocal => 1000
  | .number => 1 | .range => 1

def defaultStepBase : Ty → Float
  | .week => -259200000
  | _ => 0

/-- The allowed value step: `none` for "any"; else the `step` attribute when a valid number
greater than zero, times the scale; else the default step times the scale. -/
def allowedStep (t : Ty) (step : Option String) : Option Float :=
  match step with
  | none => some (defaultStep t * stepScale t)
  | some s =>
    if s.toLower == "any" then none
    else if validFloat s && L4Factoidal.JS.strToNumber s > 0 then some (L4Factoidal.JS.strToNumber s * stepScale t)
    else some (defaultStep t * stepScale t)

/-- The step base: the `min` attribute's number, else the `value` attribute's, else the
default. -/
def stepBase (t : Ty) (min dflt : Option String) : Float :=
  match min.bind (toNumber t) with
  | some m => m
  | none => match dflt.bind (toNumber t) with
    | some v => v
    | none => defaultStepBase t

/-- The context of an `input` that the constraints read: its attributes. -/
structure Attrs where
  min : Option String := none
  max : Option String := none
  step : Option String := none
  /-- The `value` content attribute (the default value). -/
  dflt : Option String := none
  deriving Inhabited

/-- The minimum and maximum; a `range` has the defaults 0 and 100. -/
def minOf (t : Ty) (a : Attrs) : Option Float :=
  match a.min.bind (toNumber t) with
  | some m => some m
  | none => if t == .range then some 0 else none

def maxOf (t : Ty) (a : Attrs) : Option Float :=
  match a.max.bind (toNumber t) with
  | some m => some m
  | none => if t == .range then some 100 else none

/-- `x` is on the step grid: a whole number of steps from the base (to within the rounding
of doubles: a billionth of a step). -/
def onStep (x base step : Float) : Bool :=
  let r := (x - base) / step
  (r - r.round).abs ≤ 1e-9 * (if r.abs > 1 then r.abs else 1)

def stepMismatch (t : Ty) (a : Attrs) (x : Float) : Bool :=
  match allowedStep t a.step with
  | none => false
  | some step => !onStep x (stepBase t a.min a.dflt) step

/-- Underflow and overflow. A `time` whose maximum is less than its minimum has a reversed
range: the value is out of range when it is between them. -/
def rangeUnderflow (t : Ty) (a : Attrs) (x : Float) : Bool :=
  match minOf t a, maxOf t a with
  | some mn, some mx => if t == .time && mx < mn then x > mx && x < mn else x < mn
  | some mn, none => x < mn
  | none, _ => false

def rangeOverflow (t : Ty) (a : Attrs) (x : Float) : Bool :=
  match minOf t a, maxOf t a with
  | some mn, some mx => if t == .time && mx < mn then x > mx && x < mn else x > mx
  | none, some mx => x > mx
  | _, none => false

/-- The value of `stepUp(n)` (`up`) or `stepDown(n)` (HTML §4.10.5.4): `none` to leave the
value; `error` when there is no allowed value step. -/
inductive Stepped where
  | invalidState
  | unchanged
  | value (s : String)
  deriving Repr, DecidableEq, Inhabited

def stepBy (t : Ty) (a : Attrs) (value : String) (n : Int) (up : Bool) : Stepped :=
  match allowedStep t a.step with
  | none => .invalidState
  | some step =>
    let mn := minOf t a
    let mx := maxOf t a
    let base := stepBase t a.min a.dflt
    let floorTo := fun (v : Float) => base + ((v - base) / step).floor * step
    let ceilTo := fun (v : Float) => base + ((v - base) / step).ceil * step
    -- no value in the range that is on the grid: nothing to do
    let empty := match mn, mx with
      | some mn, some mx => mn > mx || ceilTo mn > mx
      | _, _ => false
    if empty then .unchanged else
    let v0 := (toNumber t value).getD 0
    let v := if !onStep v0 base step then (if up then ceilTo v0 else floorTo v0)
      else v0 + step * Float.ofInt (if up then n else -n)
    let v := match mn with | some mn => if v < mn then ceilTo mn else v | none => v
    let v := match mx with | some mx => if v > mx then floorTo mx else v | none => v
    if (up && v < v0) || (!up && v > v0) then .unchanged
    else match ofNumber t v with
      | some s => .value s
      | none => .unchanged

/-! ## Value sanitization (HTML §4.10.5.1) -/

def isWs (c : Char) : Bool := c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

def stripNewlines (s : String) : String := String.ofList (s.toList.filter fun c => c != '\n' && c != '\r')

def stripWs (s : String) : String := String.ofList ((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse

def isHex (c : Char) : Bool := isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def lowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The default value of a `range`: the midpoint, or the minimum when the maximum is less. -/
def rangeDefault (a : Attrs) : Float :=
  let mn := (minOf .range a).getD 0
  let mx := (maxOf .range a).getD 100
  if mx < mn then mn else mn + (mx - mn) / 2

/-- The value sanitization algorithm of the state `type` (its name, any `input` type). -/
def sanitize (type : String) (multiple : Bool) (a : Attrs) (v : String) : String :=
  match type with
  | "text" | "search" | "tel" | "password" => stripNewlines v
  | "url" => stripWs (stripNewlines v)
  | "email" =>
    if multiple then ",".intercalate ((v.splitOn ",").map stripWs) else stripWs (stripNewlines v)
  | "date" => if (parseDate v).isSome then v else ""
  | "month" => if (parseMonth v).isSome then v else ""
  | "week" => if (parseWeek v).isSome then v else ""
  | "time" => if (parseTime v).isSome then v else ""
  | "datetime-local" => match (parseLocal v).bind fun k => ofNumber .datetimeLocal (Float.ofInt k) with
    | some s => s
    | none => ""
  | "number" => if validFloat v then v else ""
  | "range" =>
    let x := match toNumber .range v with | some x => x | none => rangeDefault a
    let mn := (minOf .range a).getD 0
    let mx := (maxOf .range a).getD 100
    let x := if x < mn then mn else x
    let x := if mx ≥ mn && x > mx then mx else x
    let x := match allowedStep .range a.step with
      | none => x
      | some step =>
        let base := stepBase .range a.min a.dflt
        if onStep x base step then x else
          let lo := base + ((x - base) / step).floor * step
          let hi := lo + step
          -- the nearest on the grid, the greater at a tie, kept inside the range
          let pick := if x - lo < hi - x then lo else hi
          if pick > mx then lo else if pick < mn then hi else pick
    (ofNumber .range x).getD ""
  | "color" =>
    let cs := v.toList
    if cs.length == 7 && cs.head? == some '#' && (cs.drop 1).all isHex then String.ofList (cs.map lowerChar) else "#000000"
  | _ => v

/-! ## What is proved -/

/-- Says: stripping newlines leaves no newline, so the value of a text field is one line
(HTML §4.10.5.1.2), whatever a script sets. -/
theorem stripNewlines_none (s : String) (c : Char) (h : c ∈ (stripNewlines s).toList) : c ≠ '\n' ∧ c ≠ '\r' := by
  unfold stripNewlines at h
  simp only [String.toList_ofList, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact h.2

/-- Idempotence. Says: sanitizing a text value twice is sanitizing it once. -/
theorem stripNewlines_idem (s : String) : stripNewlines (stripNewlines s) = stripNewlines s := by
  unfold stripNewlines
  simp [List.filter_filter]

/-- Says: the value of a colour well is always a valid simple colour of seven characters,
whatever a script sets. Does not say: which colour an invalid value becomes beyond the
definition (black). -/
theorem sanitize_color_length (multiple : Bool) (a : Attrs) (v : String) :
    (sanitize "color" multiple a v).length = 7 := by
  unfold sanitize
  simp only
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    simp [h.1.1]
  · decide

/-- Says: the default allowed value step of every state is greater than zero, so stepping
with no `step` attribute always moves the value. Does not say: the round trip
`toNumber t (ofNumber t x) = x`, which the `#guard`s below check on sample values only. -/
theorem defaultStep_positive (t : Ty) : defaultStep t * stepScale t > 0 := by
  cases t <;> simp [defaultStep, stepScale] <;> decide

/-! ## Tests (WPT html/semantics/forms/the-input-element) -/

#guard toNumber .date "2019-12-10" == some 1575936000000
#guard toNumber .date "2016-02-29" == some 1456704000000
#guard toNumber .date "2019-02-29" == none && toNumber .date "0000-12-10" == none && toNumber .date "2019-13-10" == none
#guard ofNumber .date 0 == some "1970-01-01" && ofNumber .date 1575936000000 == some "2019-12-10" && ofNumber .date 1456704000000 == some "2016-02-29"
#guard ofNumber .date (-86400000) == some "1969-12-31" && ofNumber .date 951782400000 == some "2000-02-29"
#guard toNumber .month "2019-12" == some 599 && ofNumber .month 599 == some "2019-12" && ofNumber .month 0 == some "1970-01" && ofNumber .month (-1) == some "1969-12"
#guard toNumber .week "2019-W50" == some 1575849600000 && ofNumber .week 1575849600000 == some "2019-W50"
#guard toNumber .week "1970-W01" == some (-259200000) && ofNumber .week (-259200000) == some "1970-W01"
#guard toNumber .week "2019-W53" == none && toNumber .week "2020-W53" == some 1609113600000 && ofNumber .week 1609113600000 == some "2020-W53"
#guard toNumber .time "12:00" == some 43200000 && toNumber .time "23:59:59.999" == some 86399999 && toNumber .time "24:00" == none
#guard toNumber .time "00:00:00.5" == some 500 && toNumber .time "00:00:00.05" == some 50
#guard ofNumber .time 43200000 == some "12:00" && ofNumber .time 43260000 == some "12:01" && ofNumber .time 1000 == some "00:00:01"
#guard ofNumber .time 1 == some "00:00:00.001" && ofNumber .time 500 == some "00:00:00.5" && ofNumber .time 86399999 == some "23:59:59.999"
#guard toNumber .datetimeLocal "2019-12-10T12:00" == some 1575979200000 && toNumber .datetimeLocal "2019-12-10 12:00" == some 1575979200000
#guard ofNumber .datetimeLocal 1575979200000 == some "2019-12-10T12:00" && ofNumber .datetimeLocal 0 == some "1970-01-01T00:00"
#guard toNumber .number "123" == some 123 && toNumber .number "-1.5e3" == some (-1500) && toNumber .number ".5" == some 0.5
#guard toNumber .number "1." == none && toNumber .number "+1" == none && toNumber .number "1e" == none && toNumber .number "" == none
#guard ofNumber .number 123.456 == some "123.456" && ofNumber .number 1e21 == some "1e+21"
#guard validFloat "1e+5" && validFloat "-0.0" && !validFloat "e5" && !validFloat "1.5.2" && !validFloat " 1"
#guard sanitize "text" false {} "a\r\nb" == "ab" && sanitize "url" false {} "  http://a/\n " == "http://a/"
#guard sanitize "email" true {} " a@b , c@d " == "a@b,c@d" && sanitize "number" false {} "abc" == "" && sanitize "date" false {} "2019-02-30" == ""
#guard sanitize "color" false {} "#AbCdEf" == "#abcdef" && sanitize "color" false {} "red" == "#000000"
#guard sanitize "range" false {} "" == "50" && sanitize "range" false {} "200" == "100" && sanitize "range" false {} "-5" == "0" && sanitize "range" false {} "3.4" == "3"
#guard sanitize "range" false { min := some "0", max := some "10", step := some "4" } "7" == "8"
#guard sanitize "datetime-local" false {} "2019-12-10 12:00:00" == "2019-12-10T12:00"
#guard stepBy .number {} "" 1 true == .value "1" && stepBy .number {} "5" 2 false == .value "3"
#guard stepBy .number { step := some "any" } "5" 1 true == .invalidState
#guard stepBy .number { min := some "0", max := some "10", step := some "3" } "5" 1 true == .value "6"
#guard stepBy .number { max := some "10" } "10" 1 true == .unchanged || stepBy .number { max := some "10" } "10" 1 true == .value "10"
#guard stepBy .date {} "2019-12-10" 1 true == .value "2019-12-11" && stepBy .month {} "2019-12" 1 true == .value "2020-01"
#guard stepBy .time {} "12:00" 1 true == .value "12:01" && stepBy .week {} "2019-W50" 1 false == .value "2019-W49"
#guard stepMismatch .number { step := some "0.1" } 0.3 == false && stepMismatch .number {} 1.5 == true && stepMismatch .number { step := some "any" } 1.5 == false
#guard rangeUnderflow .number { min := some "5" } 4 && !rangeUnderflow .number { min := some "5" } 5 && rangeOverflow .date { max := some "2019-12-10" } 1576022400000
#guard rangeUnderflow .time { min := some "23:00", max := some "01:00" } 43200000 && !rangeUnderflow .time { min := some "23:00", max := some "01:00" } 84600000

end L4Factoidal.HTML.InputValue
