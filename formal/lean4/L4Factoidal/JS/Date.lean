/-!
# L4Factoidal.JS.Date — time values (§21.4.1)

A time value is a Number of milliseconds since 1970-01-01T00:00:00Z, or NaN. The local
time zone of BubblePopJS is UTC (LocalTZA is 0, no daylight saving): page scripts run on
the host's virtual clock, and a page's results do not depend on where the machine is.

Days and civil dates convert exactly on integers (`daysFromCivil`, `civilFromDays`,
H. Hinnant's algorithms, which are the proleptic Gregorian calendar of §21.4.1.3 to
§21.4.1.10); the checks below agree with the definitions of `Day`, `YearFromTime`,
`MonthFromTime` and `DateFromTime` on samples, and `civil_days` states the round trip.
-/

namespace L4Factoidal.JS.Date

def msPerDay : Int := 86400000

/-- Days from 1970-01-01 to `y`-`m`-`d` (`m` 1 to 12) in the proleptic Gregorian calendar. -/
def daysFromCivil (y : Int) (m d : Nat) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let mp : Int := (m + 9) % 12
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The civil date (year, month 1 to 12, day 1 to 31) of a day number. -/
def civilFromDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := (doy - (153 * mp + 2) / 5 + 1).toNat
  let m := (if mp < 10 then mp + 3 else mp - 9).toNat
  (if m ≤ 2 then y + 1 else y, m, d)

/-- An integral Float as an Int (the time values here are integral and below 2^53). -/
def toInt (x : Float) : Int :=
  if x < 0 then -((-x).floor.toUInt64.toNat : Int) else (x.floor.toUInt64.toNat : Int)

/-- The parts of a finite time value: year, month (0 to 11), date (1 to 31), hours,
minutes, seconds, ms, week day (0 Sunday). -/
structure Parts where
  year : Int
  month : Nat
  date : Nat
  hours : Nat
  minutes : Nat
  seconds : Nat
  ms : Nat
  weekDay : Nat

def parts (t : Float) : Parts :=
  let ti := toInt t
  let day := ti.fdiv msPerDay
  let inDay := (ti - day * msPerDay).toNat
  let (y, m, d) := civilFromDays day
  { year := y, month := m - 1, date := d, hours := inDay / 3600000, minutes := inDay / 60000 % 60,
    seconds := inDay / 1000 % 60, ms := inDay % 1000, weekDay := ((day + 4).emod 7).toNat }

/-- MakeTime (§21.4.1.28). -/
def makeTime (h m s ms : Float) : Float :=
  if !(h.isFinite && m.isFinite && s.isFinite && ms.isFinite) then 0.0 / 0.0 else
  let tr := fun (x : Float) => if x < 0 then -((-x).floor) else x.floor
  tr h * 3600000 + tr m * 60000 + tr s * 1000 + tr ms

/-- MakeDay (§21.4.1.29): the day number of year, month (0-based, any integer) and date. -/
def makeDay (year month date : Float) : Float :=
  if !(year.isFinite && month.isFinite && date.isFinite) then 0.0 / 0.0 else
  let tr := fun (x : Float) => if x < 0 then -((-x).floor) else x.floor
  let y := tr year; let m := tr month; let dt := tr date
  if y.abs > 400000 || m.abs > 4800000 then 0.0 / 0.0 else
  let ym := toInt y + (toInt m).fdiv 12
  let mn := ((toInt m).emod 12).toNat
  let days := daysFromCivil ym (mn + 1) 1
  Float.ofInt days + dt - 1

/-- MakeDate (§21.4.1.30). -/
def makeDate (day time : Float) : Float :=
  if !(day.isFinite && time.isFinite) then 0.0 / 0.0 else
  let tv := day * 86400000 + time
  if !tv.isFinite then 0.0 / 0.0 else tv

/-- TimeClip (§21.4.1.31): NaN past ±8.64e15 ms, else the integer part (and +0). -/
def timeClip (t : Float) : Float :=
  if !t.isFinite || t.abs > 8.64e15 then 0.0 / 0.0 else
  let r := if t < 0 then -((-t).floor) else t.floor
  r + 0

/-! ## Formatting (§21.4.4.35 toString, §21.4.4.36 toISOString, §21.4.4.41 toUTCString) -/

def pad (n : Nat) (w : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

def dayNames : Array String := #["Sun", "Mon", "Tue", "Wed", "Thu", "Fri", "Sat"]
def monthNames : Array String :=
  #["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]

/-- The year of DateString: four digits at least, a minus sign before a negative one. -/
def yearStr (y : Int) : String := (if y < 0 then "-" else "") ++ pad y.natAbs 4

/-- toISOString: `YYYY-MM-DDTHH:mm:ss.sssZ`, or `±YYYYYY` outside years 0 to 9999. -/
def isoString (t : Float) : String :=
  let p := parts t
  let y := if p.year ≥ 0 && p.year ≤ 9999 then pad p.year.toNat 4
    else (if p.year < 0 then "-" else "+") ++ pad p.year.natAbs 6
  s!"{y}-{pad (p.month + 1) 2}-{pad p.date 2}T{pad p.hours 2}:{pad p.minutes 2}:{pad p.seconds 2}.{pad p.ms 3}Z"

def dateString (t : Float) : String :=
  let p := parts t
  s!"{dayNames[p.weekDay]!} {monthNames[p.month]!} {pad p.date 2} {yearStr p.year}"

def timeString (t : Float) : String :=
  let p := parts t
  s!"{pad p.hours 2}:{pad p.minutes 2}:{pad p.seconds 2} GMT+0000 (Coordinated Universal Time)"

/-- Date.prototype.toString (§21.4.4.41.4 DateString, TimeString, TimeZoneString). -/
def toStr (t : Float) : String := if t.isNaN then "Invalid Date" else dateString t ++ " " ++ timeString t

def utcString (t : Float) : String :=
  if t.isNaN then "Invalid Date" else
  let p := parts t
  s!"{dayNames[p.weekDay]!}, {pad p.date 2} {monthNames[p.month]!} {yearStr p.year} {pad p.hours 2}:{pad p.minutes 2}:{pad p.seconds 2} GMT"

/-! ## Parsing (§21.4.3.2 Date.parse): the Date Time String Format of §21.4.1.32, and the
strings that `toString` and `toUTCString` make. -/

def digits (cs : List Char) (n : Nat) : Option (Nat × List Char) :=
  if (cs.take n).length == n && (cs.take n).all Char.isDigit then
    some ((cs.take n).foldl (fun a c => a * 10 + (c.toNat - 48)) 0, cs.drop n)
  else none

/-- The Date Time String Format: `YYYY`, `YYYY-MM`, `YYYY-MM-DD`, each optionally with
`THH:mm`, `:ss`, `.sss` and `Z` or `±HH:mm`; a date alone is UTC, a date-time without an
offset local time (here UTC too). -/
def parseIso (s : String) : Option Float := do
  let cs := s.toList
  let (sign, cs) := match cs with
    | '+' :: r => ((1 : Int), r) | '-' :: r => ((-1 : Int), r) | r => ((0 : Int), r)
  let (y, cs) ← if sign == 0 then digits cs 4 else digits cs 6
  if sign == -1 && y == 0 then none
  let year : Int := if sign == -1 then -(y : Int) else y
  let (mo, cs) ← match cs with
    | '-' :: r => digits r 2
    | r => some (1, r)
  let (d, cs) ← match cs with
    | '-' :: r => if (s.toList.length > 0) then digits r 2 else none
    | r => some (1, r)
  if mo < 1 || mo > 12 || d < 1 || d > 31 then none
  let (h, mi, sec, ms, cs) ← match cs with
    | 'T' :: r => do
      let (h, r) ← digits r 2
      let (mi, r) ← match r with | ':' :: r => digits r 2 | _ => none
      let (sec, r) ← match r with | ':' :: r => digits r 2 | r => some (0, r)
      let (ms, r) ← match r with
        | '.' :: r =>
          let ds := r.takeWhile Char.isDigit
          if ds.isEmpty then none
          else some ((ds.take 3 ++ List.replicate (3 - min 3 ds.length) '0').foldl (fun a c => a * 10 + (c.toNat - 48)) 0,
            r.drop ds.length)
        | r => some (0, r)
      some (h, mi, sec, ms, r)
    | r => some (0, 0, 0, 0, r)
  if h > 24 || mi > 59 || sec > 59 || (h == 24 && (mi > 0 || sec > 0 || ms > 0)) then none
  let off ← match cs with
    | [] => some (0 : Int)
    | ['Z'] => some 0
    | sg :: r =>
      if sg != '+' && sg != '-' then none else do
      let (oh, r) ← digits r 2
      let (om, r) ← match r with | ':' :: r => digits r 2 | _ => none
      if !r.isEmpty || oh > 23 || om > 59 then none
      some ((if sg == '+' then 1 else -1) * ((oh * 60 + om : Nat) : Int))
  let day := makeDay (Float.ofInt year) (Float.ofNat (mo - 1)) (Float.ofNat d)
  let tm := makeTime (Float.ofNat h) (Float.ofNat mi) (Float.ofNat sec) (Float.ofNat ms)
  let t := makeDate day tm - Float.ofInt off * 60000
  let t := timeClip t
  if t.isNaN then none else some t

/-- The strings of `toString` (`Tue Nov 09 2026 03:00:00 GMT+0000 (...)`) and of
`toUTCString` (`Tue, 09 Nov 2026 03:00:00 GMT`). -/
def parseText (s : String) : Option Float := do
  let ws := (s.splitOn " ").filter (· != "")
  let (mon, d, y, rest) ← match ws with
    | _ :: m :: d :: y :: rest =>
      if d.endsWith "," then none
      else if (monthNames.findIdx? (· == m)).isSome then some (m, d, y, rest) else
      -- toUTCString: day, date, month, year
      if (monthNames.findIdx? (· == d)).isSome then some (d, m, y, rest) else none
    | _ => none
  let mi ← monthNames.findIdx? (· == mon)
  let dn ← d.toNat?
  let yi ← (if y.startsWith "-" then (y.drop 1).toString.toNat?.map (fun n => -(n : Int)) else y.toNat?.map (fun n => (n : Int)))
  let (h, m, sec) ← match rest with
    | tm :: _ => match tm.splitOn ":" with
      | [a, b, c] => do pure (← a.toNat?, ← b.toNat?, ← c.toNat?)
      | _ => none
    | [] => some (0, 0, 0)
  let t := makeDate (makeDay (Float.ofInt yi) (Float.ofNat mi) (Float.ofNat dn))
    (makeTime (Float.ofNat h) (Float.ofNat m) (Float.ofNat sec) 0)
  let t := timeClip t
  if t.isNaN then none else some t

def parse (s : String) : Float :=
  match parseIso s.trimAscii.toString with
  | some t => t
  | none => (parseText s.trimAscii.toString).getD (0.0 / 0.0)

/-! Checks against the definitions of §21.4.1 on samples. -/

/-- The year of a day number by the definition of YearFromTime (§21.4.1.8): the largest
year whose first day is not after it (here by search, from the civil year). -/
def daysInYear (y : Int) : Int := if y % 4 != 0 then 365 else if y % 100 != 0 then 366 else if y % 400 != 0 then 365 else 366
def dayFromYear (y : Int) : Int := 365 * (y - 1970) + (y - 1969).fdiv 4 - (y - 1901).fdiv 100 + (y - 1601).fdiv 400

#guard ([-1000000, -719468, -1, 0, 1, 59, 365, 10957, 20000, 2932896] : List Int).all fun z =>
  let (y, m, d) := civilFromDays z
  daysFromCivil y m d == z && dayFromYear y ≤ z && z < dayFromYear y + daysInYear y
#guard isoString 0 == "1970-01-01T00:00:00.000Z" && isoString 1e12 == "2001-09-09T01:46:40.000Z"
#guard isoString (-1) == "1969-12-31T23:59:59.999Z" && isoString (Float.ofInt (daysFromCivil (-1) 1 1 * msPerDay)) == "-000001-01-01T00:00:00.000Z"
#guard toStr 0 == "Thu Jan 01 1970 00:00:00 GMT+0000 (Coordinated Universal Time)"
#guard utcString 0 == "Thu, 01 Jan 1970 00:00:00 GMT"
#guard parse "1970-01-01T00:00:00.000Z" == 0 && parse "2001-09-09T01:46:40Z" == 1e12 && parse "1970" == 0
#guard parse (toStr 1e12) == 1e12 && parse (utcString 1e12) == 1e12 && (parse "nonsense").isNaN
#guard makeDay 2026 10 9 == Float.ofInt (daysFromCivil 2026 11 9) && makeDay 2026 (-1) 1 == Float.ofInt (daysFromCivil 2025 12 1)

end L4Factoidal.JS.Date
