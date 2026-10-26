/-
L4Factoidal.SPARQL.Now — the lexical form of the value `NOW()` returns.

SPARQL 1.1 §17.4.5.1 (`NOW`): "Returns an XSD dateTime value for the
current query execution. All calls to this function in any one query
execution must return the same value." The evaluator is a function of
its arguments: the value is `EvalEnv.now` (`SPARQL/Expr.lean`), an
`xsd:dateTime` lexical form that the caller supplies. A caller that
runs in `IO` reads the system clock ONCE per query or update execution,
turns the reading into this lexical form with `dateTimeOfUnixMillis`,
and passes it as `now`. The clock read itself is in
`Wasm/Ops/Clock.lean`, at the executable edge; nothing in this file
reads a clock.

The lexical form follows XML Schema 1.1 Part 2 §3.3.7 (dateTime), with
the time zone `Z` (UTC): `yyyy-mm-ddThh:mm:ss[.fff]Z`. It is written
by `XSD.canonicalDateTime` (§3.3.7.2), so a fraction of second has no
trailing zeros and no fraction is written for a whole second. The same
function as XQuery and XPath Functions and Operators §15.3
`fn:current-dateTime` would use for its value: the dynamic context
supplies the instant, and the lexical form is a pure function of it.

A caller that supplies `now` itself (the pure dispatch entries, which read no
clock, take it as an optional last argument,
https://github.com/danbri/factoidal/issues/748) is checked with
`isDateTimeLexical`: the strict XSD parser must read the text as a dateTime
lexical form. A text it does not read is an error for the caller to report; it
is never replaced by "no clock".

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Fn.DateTime

namespace L4Factoidal.SPARQL

open L4Factoidal.XSD

/-- Milliseconds in one UTC day. POSIX time counts every day as exactly
this long (no leap seconds), which is the clock model the system clock
and the Unix epoch use. -/
def millisPerUnixDay : Int := 86400000

/-- The `xsd:dateTime` lexical form (XML Schema 1.1 Part 2 §3.3.7), in
UTC, of the instant `ms` milliseconds after 1970-01-01T00:00:00Z. A
negative `ms` is an instant before the epoch. Total: the day is the
floor of the quotient, so the time of day is always in `[0, 86400000)`. -/
def dateTimeOfUnixMillis (ms : Int) : String :=
  let days : Int := Int.fdiv ms millisPerUnixDay
  let msOfDay : Nat := (ms - days * millisPerUnixDay).toNat
  let (y, mo, d) := Fn.DateTime.civilFromDays days
  XSD.canonicalDateTime .dateTime
    { year := some y, month := some mo, day := some d,
      hour := some (msOfDay / 3600000),
      minute := some (msOfDay % 3600000 / 60000),
      -- The seconds of the minute with a millisecond fraction:
      -- `msOfMinute × 10^-3`. `canonicalSeconds` normalises the scale.
      second := some ⟨((msOfDay % 60000 : Nat) : Int), 3⟩,
      tz := some 0 }

/-- `s` is a lexical form of `xsd:dateTime` (XML Schema 1.1 Part 2 §3.3.7),
as the strict parser `XSD.parseDateTimeLex` reads it: the digits are fixed
width, the month and day are in range for the year, the hour, minute and
second are in range (24:00:00 is the end of the day), and a time zone, when
present, is `Z` or an offset of at most 14:00. No leading or trailing
character is skipped. The empty text is not a lexical form. -/
def isDateTimeLexical (s : String) : Bool :=
  (parseDateTimeLex .dateTime s).isSome

/-! ## Checks

Instants whose dateTime is known independently of this function: the
epoch; 2000-02-29 (2000 is divisible by 400, so it is a leap year);
2024-02-29 with a millisecond fraction; the instants 2^31 and 2^32
seconds, past the 32-bit signed and unsigned `time_t` limits;
2100-01-01 and the days either side of 2100-02-28 (2100 is divisible by
100 and not by 400, so it has no 29 February); the milliseconds around
the epoch. -/

-- Positive: the lexical forms.
#guard dateTimeOfUnixMillis 0 == "1970-01-01T00:00:00Z"
#guard dateTimeOfUnixMillis 951782400000 == "2000-02-29T00:00:00Z"
#guard dateTimeOfUnixMillis 1709210096789 == "2024-02-29T12:34:56.789Z"
#guard dateTimeOfUnixMillis 946684799000 == "1999-12-31T23:59:59Z"
#guard dateTimeOfUnixMillis 946684800000 == "2000-01-01T00:00:00Z"
#guard dateTimeOfUnixMillis 2147483648000 == "2038-01-19T03:14:08Z"
#guard dateTimeOfUnixMillis 4102444800000 == "2100-01-01T00:00:00Z"
#guard dateTimeOfUnixMillis 4107456000000 == "2100-02-28T00:00:00Z"
#guard dateTimeOfUnixMillis 4107542400000 == "2100-03-01T00:00:00Z"
#guard dateTimeOfUnixMillis 4294967296000 == "2106-02-07T06:28:16Z"
-- Positive: the fraction of second has no trailing zero (§3.3.7.2).
#guard dateTimeOfUnixMillis 1 == "1970-01-01T00:00:00.001Z"
#guard dateTimeOfUnixMillis 10 == "1970-01-01T00:00:00.01Z"
#guard dateTimeOfUnixMillis 1500 == "1970-01-01T00:00:01.5Z"
#guard dateTimeOfUnixMillis 61000 == "1970-01-01T00:01:01Z"
-- Positive: an instant before the epoch rolls the day back.
#guard dateTimeOfUnixMillis (-1) == "1969-12-31T23:59:59.999Z"
#guard dateTimeOfUnixMillis (-86400000) == "1969-12-31T00:00:00Z"

-- Negative: a function that ignores its argument, or reads the date
-- from a fixed day, fails these.
#guard dateTimeOfUnixMillis 1000 != dateTimeOfUnixMillis 0
#guard dateTimeOfUnixMillis 86400000 != dateTimeOfUnixMillis 0
#guard dateTimeOfUnixMillis 1 != dateTimeOfUnixMillis 0
-- Negative: 2100 has no 29 February. One day after 2100-02-28 is 2100-03-01.
#guard dateTimeOfUnixMillis 4107542400000 != "2100-02-29T00:00:00Z"
-- Negative: 2000 does have one, so the day after 2000-02-28 is the 29th.
#guard dateTimeOfUnixMillis 951696000000 == "2000-02-28T00:00:00Z"
#guard dateTimeOfUnixMillis 951696000000 != dateTimeOfUnixMillis 951782400000

/-- The instant a dateTime value names, in whole seconds since the epoch,
from the fields `XSD.parseDateTimeLex` reads back out of the lexical form;
read through `XSD.daysFromCivil`, a day-number function this module does
not use. -/
private def secondsOfValue (v : DTValue) : Option Int :=
  match v.year, v.month, v.day, v.hour, v.minute, v.second with
  | some y, some mo, some d, some h, some mi, some s =>
      some (daysFromCivil y mo d * 86400 + (h : Int) * 3600 + (mi : Int) * 60
              + Fn.Numeric.decFloorInt s)
  | _, _, _, _, _, _ => none

/-- Parsing the lexical form back gives the instant, to the second, with
the time zone `Z`. -/
private def readsBack (ms : Int) : Bool :=
  match parseDateTimeLex .dateTime (dateTimeOfUnixMillis ms) with
  | some v => secondsOfValue v == some (Int.fdiv ms 1000) && v.tz == some 0
  | none => false

#guard [0, 1, 999, 1000, 59999, 60000, 3599999, 3600000, 86399999, 86400000,
        951782400000, 951782400001, 1709210096789, 2147483647999, 2147483648000,
        4107456000000, 4107542400000, 4294967296000, 253402300799999,
        (-1), (-1000), (-86400000), (-86400001), (-2208988800000),
        (-62135596800000)].all readsBack
-- Negative: the check detects a wrong day. 2000-02-29 is not 2000-03-01.
#guard secondsOfValue ((parseDateTimeLex .dateTime "2000-02-29T00:00:00Z").getD default) !=
  secondsOfValue ((parseDateTimeLex .dateTime "2000-03-01T00:00:00Z").getD default)

/-! ### The lexical check on a caller's `now`

Positive: forms of §3.3.7, with and without a fraction and a time zone. -/
#guard isDateTimeLexical "2026-10-10T12:34:56Z"
#guard isDateTimeLexical "2026-10-10T12:34:56.789Z"
#guard isDateTimeLexical "2026-10-10T12:34:56+01:00"
#guard isDateTimeLexical "2026-10-10T12:34:56-14:00"
#guard isDateTimeLexical "2026-10-10T12:34:56"
#guard isDateTimeLexical "2024-02-29T00:00:00Z"
#guard isDateTimeLexical "2026-10-10T24:00:00Z"
-- Positive: every instant `dateTimeOfUnixMillis` writes is a lexical form.
#guard [0, 1, 999, 1000, 86400000, 951782400000, 1709210096789, 2147483648000,
        4107542400000, 253402300799999, (-1), (-86400001), (-2208988800000),
        (-62135596800000)].all (fun ms => isDateTimeLexical (dateTimeOfUnixMillis ms))
-- Negative: not a dateTime at all, or a different datatype's lexical form.
#guard !isDateTimeLexical ""
#guard !isDateTimeLexical "now"
#guard !isDateTimeLexical "yesterday"
#guard !isDateTimeLexical "2026-10-10"
#guard !isDateTimeLexical "12:34:56Z"
#guard !isDateTimeLexical "1760099696789"
-- Negative: a field out of range.
#guard !isDateTimeLexical "2026-13-10T00:00:00Z"
#guard !isDateTimeLexical "2026-00-10T00:00:00Z"
#guard !isDateTimeLexical "2026-02-30T00:00:00Z"
#guard !isDateTimeLexical "2026-02-29T00:00:00Z"
#guard !isDateTimeLexical "2100-02-29T00:00:00Z"
#guard !isDateTimeLexical "2026-10-10T25:00:00Z"
#guard !isDateTimeLexical "2026-10-10T12:60:00Z"
#guard !isDateTimeLexical "2026-10-10T12:34:60Z"
#guard !isDateTimeLexical "2026-10-10T12:34:56+14:01"
-- Negative: the right characters in the wrong shape.
#guard !isDateTimeLexical "2026-10-10 12:34:56Z"
#guard !isDateTimeLexical " 2026-10-10T12:34:56Z"
#guard !isDateTimeLexical "2026-10-10T12:34:56Z "
#guard !isDateTimeLexical "2026-10-10T12:34:56Zjunk"
#guard !isDateTimeLexical "26-10-10T12:34:56Z"
#guard !isDateTimeLexical "2026-1-1T1:2:3Z"
-- Negative: 2000 is a leap year, so 29 February is valid there and the day
-- after it is 1 March; a check that rejects every 29 February fails this pair.
#guard isDateTimeLexical "2000-02-29T00:00:00Z"
#guard !isDateTimeLexical "2000-02-30T00:00:00Z"

end L4Factoidal.SPARQL
