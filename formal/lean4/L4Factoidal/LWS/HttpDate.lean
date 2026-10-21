/-
L4Factoidal.LWS.HttpDate — civil dates and the RFC 9110 HTTP-date, both
directions, for the date validators of conditional requests.

RFC 9110 §5.6.7, verbatim:

  "HTTP-date    = IMF-fixdate / obs-date"
  "An example of the preferred format is
     Sun, 06 Nov 1994 08:49:37 GMT    ; IMF-fixdate
   Examples of the two obsolete formats are
     Sunday, 06-Nov-94 08:49:37 GMT   ; obsolete RFC 850 format
     Sun Nov  6 08:49:37 1994         ; ANSI C's asctime() format"
  "A recipient that parses a timestamp value in an HTTP field MUST accept all
  three HTTP-date formats."
  "Recipients of a timestamp value in rfc850-date format, which uses a
  two-digit year, MUST interpret a timestamp that appears to be more than 50
  years in the future as representing the most recent year in the past that
  had the same last two digits."

`parseHttpDate` accepts the three formats and answers seconds since the
Unix epoch, or `none` when the value is not an HTTP-date (wrong syntax, a
month day the month does not have, an hour above 23). RFC 9110 §13.1.3 and
§13.1.4 tell a recipient to IGNORE an If-Modified-Since or
If-Unmodified-Since whose value is not a valid HTTP-date, which is what
`none` lets `Binding.preconditionFailure` do.

The day and month names are case-sensitive (§5.6.7: "HTTP-date is
case sensitive"). The day name is checked against the list of names, not
against the date: §5.6.7 asks a recipient to be robust in parsing.

`civilOfDays` is the era algorithm (H. Hinnant, "chrono-Compatible Low-Level
Date Algorithms"), and `daysFromCivil` is its inverse. Theorem
`daysFromCivil_civilOfDays` proves the inverse for every day count, and
`unixOfCivil_civilOfUnix` lifts it to seconds: the seconds a parsed date
names are exactly the seconds whose `Last-Modified` the server formatted, so
comparing a validator a client echoes with a resource's modification time is
an exact comparison of instants.
-/

namespace L4Factoidal.LWS

/-! ## Civil dates -/

/-- Days since 1970-01-01 to a civil (proleptic Gregorian) year, month and
day. The era algorithm: eras of 400 years (146097 days) counted from
0000-03-01, so that the leap day is the last day of a year of the era. -/
def civilOfDays (days : Nat) : Nat × Nat × Nat :=
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  (if m ≤ 2 then y + 1 else y, m, d)

/-- Days from 0000-03-01 to a civil year, month and day: the inverse of
`civilOfDays`, shifted by the 719468 days from 0000-03-01 to 1970-01-01. -/
def daysFromCivil (y m d : Nat) : Nat :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  era * 146097 + (yoe * 365 + yoe / 4 - yoe / 100 + doy)

/-- Inside one era, the year of era the algorithm computes is below 400,
the days before it do not exceed the day of era, and the day of year is
below 366. -/
theorem civil_doe_bounds (doe : Nat) (h : doe < 146097) :
    let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
    yoe < 400 ∧ 365 * yoe + yoe / 4 - yoe / 100 ≤ doe ∧
      doe - (365 * yoe + yoe / 4 - yoe / 100) < 366 := by
  intro yoe
  have h1 : yoe < 400 := by omega
  have hc : doe / 36524 = 0 ∨ doe / 36524 = 1 ∨ doe / 36524 = 2 ∨ doe / 36524 = 3 ∨
      doe / 36524 = 4 := by omega
  have hy : yoe / 100 = 0 ∨ yoe / 100 = 1 ∨ yoe / 100 = 2 ∨ yoe / 100 = 3 := by omega
  refine ⟨h1, ?_⟩
  rcases hc with hc | hc | hc | hc | hc <;> rcases hy with hy | hy | hy | hy <;> omega

/-- `daysFromCivil` inverts `civilOfDays`: every day count since 1970-01-01
comes back, shifted to 0000-03-01. -/
theorem daysFromCivil_civilOfDays (n : Nat) :
    daysFromCivil (civilOfDays n).1 (civilOfDays n).2.1 (civilOfDays n).2.2 = n + 719468 := by
  unfold civilOfDays daysFromCivil
  simp only
  generalize hz : n + 719468 = z
  generalize hera : z / 146097 = era
  generalize hdoe : z - era * 146097 = doe
  have hdoe_lt : doe < 146097 := by omega
  have hz' : z = era * 146097 + doe := by omega
  have hb := civil_doe_bounds doe hdoe_lt
  simp only at hb
  generalize hyoe : (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365 = yoe at hb ⊢
  obtain ⟨hy400, hle, hlt⟩ := hb
  generalize hdoy : doe - (365 * yoe + yoe / 4 - yoe / 100) = doy
  have hdoyEq : doe = 365 * yoe + yoe / 4 - yoe / 100 + doy := by omega
  have hdoy366 : doy < 366 := by omega
  have hera' : (yoe + era * 400) / 400 = era := by omega
  have hyoe' : yoe + era * 400 - era * 400 = yoe := by omega
  generalize hmp : (5 * doy + 2) / 153 = mp
  have hmp11 : mp ≤ 11 := by omega
  have hmpd : (153 * mp + 2) / 5 ≤ doy := by omega
  by_cases h10 : mp < 10
  · simp only [h10, if_true]
    have : ¬ (mp + 3 ≤ 2) := by omega
    simp only [this, if_false]
    have : mp + 3 > 2 := by omega
    simp only [this, if_true, Nat.add_sub_cancel, hera', hyoe']
    omega
  · simp only [h10, if_false]
    have : mp - 9 ≤ 2 := by omega
    simp only [this, if_true]
    have : ¬ (mp - 9 > 2) := by omega
    have h9 : mp - 9 + 9 = mp := by omega
    simp only [this, if_false, Nat.add_sub_cancel, hera', hyoe', h9]
    omega

/-- Seconds since the Unix epoch of a civil date and a time of day. A date
before 1970 gives a negative number. -/
def unixOfCivil (y m d secOfDay : Nat) : Int :=
  ((daysFromCivil y m d : Int) - 719468) * 86400 + (secOfDay : Int)

/-- The civil date and the time of day of an instant: what `Last-Modified`
formats. -/
def civilOfUnix (t : Nat) : Nat × Nat × Nat × Nat :=
  let (y, m, d) := civilOfDays (t / 86400)
  (y, m, d, t % 86400)

/-- Parsing what the server formats gives back the instant: the civil date
and time of day of `t` name exactly `t` seconds. -/
theorem unixOfCivil_civilOfUnix (t : Nat) :
    unixOfCivil (civilOfUnix t).1 (civilOfUnix t).2.1 (civilOfUnix t).2.2.1
      (civilOfUnix t).2.2.2 = t := by
  have h := daysFromCivil_civilOfDays (t / 86400)
  unfold civilOfUnix unixOfCivil
  simp only
  rw [h]
  omega

/-! ## HTTP-date (RFC 9110 §5.6.7) -/

/-- The value of a field of exactly `len` decimal digits. -/
def httpDigits? (s : String) (len : Nat) : Option Nat :=
  if s.length == len && s.all Char.isDigit then s.toNat? else none

/-- `month = %s"Jan" / %s"Feb" / ...` -/
def monthOfName? : String → Option Nat
  | "Jan" => some 1 | "Feb" => some 2 | "Mar" => some 3 | "Apr" => some 4
  | "May" => some 5 | "Jun" => some 6 | "Jul" => some 7 | "Aug" => some 8
  | "Sep" => some 9 | "Oct" => some 10 | "Nov" => some 11 | "Dec" => some 12
  | _ => none

/-- `day-name`, the IMF-fixdate and asctime form. -/
def shortDayNames : List String := ["Mon", "Tue", "Wed", "Thu", "Fri", "Sat", "Sun"]

/-- `day-name-l`, the rfc850-date form. -/
def longDayNames : List String :=
  ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]

def httpLeapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- The number of days of month `m` of year `y`. -/
def httpMonthLength (y m : Nat) : Nat :=
  if m == 2 then (if httpLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30
  else 31

/-- `time-of-day = hour ":" minute ":" second`, as seconds of the day.
`second` may be 60, a leap second (RFC 5322 §3.3, which §5.6.7 follows). -/
def httpTimeOfDay? (s : String) : Option Nat :=
  match s.splitOn ":" with
  | [h, mi, sec] => do
      let h ← httpDigits? h 2
      let mi ← httpDigits? mi 2
      let sec ← httpDigits? sec 2
      if h ≤ 23 && mi ≤ 59 && sec ≤ 60 then some (h * 3600 + mi * 60 + sec) else none
  | _ => none

/-- A civil date that exists, and a time of day, as seconds since the epoch. -/
def httpDateValue? (y m d secOfDay : Nat) : Option Int :=
  if 1 ≤ y && 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ httpMonthLength y m then
    some (unixOfCivil y m d secOfDay)
  else none

/-- The year of an rfc850-date two-digit year `yy`, read at the instant `now`:
the year in the century of `now` with those digits, or the one a century
earlier when that is more than 50 years after the year of `now`. -/
def rfc850Year (now yy : Nat) : Nat :=
  let cur := (civilOfDays (now / 86400)).1
  let cand := cur / 100 * 100 + yy
  if cand > cur + 50 then cand - 100 else cand

/-- An HTTP-date in any of its three formats, as seconds since the Unix
epoch; `none` when the value is not an HTTP-date. `now` (seconds since the
epoch) is the instant against which a two-digit rfc850 year is read. -/
def parseHttpDate (now : Nat) (v : String) : Option Int :=
  let toks := (v.trimAscii.toString.splitOn " ").filter (· != "")
  match toks with
  -- IMF-fixdate: day-name "," SP date1 SP time-of-day SP GMT
  | [dn, dd, mon, yyyy, time, "GMT"] =>
      if dn.endsWith "," && shortDayNames.contains (dn.dropEnd 1).toString then do
        let d ← httpDigits? dd 2
        let m ← monthOfName? mon
        let y ← httpDigits? yyyy 4
        let t ← httpTimeOfDay? time
        httpDateValue? y m d t
      else none
  -- rfc850-date: day-name-l "," SP date2 SP time-of-day SP GMT
  | [dn, dmy, time, "GMT"] =>
      if dn.endsWith "," && longDayNames.contains (dn.dropEnd 1).toString then
        match dmy.splitOn "-" with
        | [dd, mon, yy] => do
            let d ← httpDigits? dd 2
            let m ← monthOfName? mon
            let yy ← httpDigits? yy 2
            let t ← httpTimeOfDay? time
            httpDateValue? (rfc850Year now yy) m d t
        | _ => none
      else none
  -- asctime-date: day-name SP date3 SP time-of-day SP year,
  -- date3 = month SP ( 2DIGIT / ( SP DIGIT ) )
  | [dn, mon, dd, time, yyyy] =>
      if shortDayNames.contains dn then do
        let d ← (if dd.length == 1 then httpDigits? dd 1 else httpDigits? dd 2)
        let m ← monthOfName? mon
        let y ← httpDigits? yyyy 4
        let t ← httpTimeOfDay? time
        httpDateValue? y m d t
      else none
  | _ => none

-- The three examples of RFC 9110 §5.6.7 name the same instant.
#guard parseHttpDate 0 "Sun, 06 Nov 1994 08:49:37 GMT" == some 784111777
#guard parseHttpDate 1792595514 "Sunday, 06-Nov-94 08:49:37 GMT" == some 784111777
#guard parseHttpDate 0 "Sun Nov  6 08:49:37 1994" == some 784111777
#guard parseHttpDate 0 "Thu, 01 Jan 1970 00:00:00 GMT" == some 0
#guard parseHttpDate 0 "Wed, 21 Oct 2026 15:11:53 GMT" == some 1792595513
-- A date before the epoch is a valid HTTP-date and is negative.
#guard parseHttpDate 0 "Wed, 31 Dec 1969 23:59:59 GMT" == some (-1)
-- A leap day exists in 2024 and not in 2023 or 2100.
#guard (parseHttpDate 0 "Thu, 29 Feb 2024 00:00:00 GMT").isSome
#guard parseHttpDate 0 "Wed, 29 Feb 2023 00:00:00 GMT" == none
#guard parseHttpDate 0 "Mon, 29 Feb 2100 00:00:00 GMT" == none
-- The two-digit year: in 2026, "26" is 2026, "77" is 2077 (51 years on
-- would be 2077 > 2076, so 1977), "76" is 2076.
#guard rfc850Year 1792595514 26 == 2026
#guard rfc850Year 1792595514 76 == 2076
#guard rfc850Year 1792595514 77 == 1977
-- Not HTTP-dates: another zone, an hour of 24, a missing comma, lower-case
-- names, ISO 8601, a list of two dates, a 31st of November.
#guard parseHttpDate 0 "Sun, 06 Nov 1994 08:49:37 UTC" == none
#guard parseHttpDate 0 "Sun, 06 Nov 1994 24:00:00 GMT" == none
#guard parseHttpDate 0 "Sun 06 Nov 1994 08:49:37 GMT" == none
#guard parseHttpDate 0 "sun, 06 nov 1994 08:49:37 GMT" == none
#guard parseHttpDate 0 "1994-11-06T08:49:37Z" == none
#guard parseHttpDate 0 "Sun, 06 Nov 1994 08:49:37 GMT, Mon, 07 Nov 1994 08:49:37 GMT" == none
#guard parseHttpDate 0 "Thu, 31 Nov 1994 08:49:37 GMT" == none
#guard parseHttpDate 0 "" == none

end L4Factoidal.LWS
