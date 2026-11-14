import L4Factoidal.Temporal.Iso

/-!
# Temporal: reading and writing ISO 8601 / RFC 9557 strings

`parseDateTime` reads the Temporal grammar's date-time strings (TemporalDateTimeString and its
relatives): a date (`YYYY-MM-DD`, `YYYYMMDD`, or a sign and six year digits), an optional time
after `T`, `t` or a space (`HH`, `HH:MM`, `HH:MM:SS`, a fraction of up to nine digits after `.`
or `,`, also without colons), an optional UTC offset (`Z` or `±HH[:MM[:SS[.fff]]]`), and
bracketed annotations: a time zone first, then `key=value` ones (`u-ca` names the calendar; an
unknown critical `!` key and two critical calendars are refused). `parseDuration` reads ISO 8601
durations (`P1Y2M3W4DT5H6M7.5S`, a fraction only on the last time unit). `formatDate`,
`formatTime` write the forms Temporal's toString methods answer.

Every reader is a single pass over the characters: each loop is a `for` over a range bounded by
the input's length (or by the digit count it may read), so its work is linear in the input.
-/

namespace L4Factoidal.Temporal

/-- A date-time string's parts. -/
structure DateTimeParts where
  year : Int := 0
  month : Nat := 0
  day : Nat := 0
  hasDate : Bool := true
  hasTime : Bool := false
  hour : Nat := 0
  minute : Nat := 0
  second : Nat := 0
  /-- The fraction of the second, in nanoseconds. -/
  fracNs : Nat := 0
  /-- 0: no offset, 1: `Z`, 2: a numeric offset (`offsetNs`). -/
  offsetKind : Nat := 0
  offsetNs : Int := 0
  /-- The bracketed time zone, or "". -/
  timeZone : String := ""
  /-- The `u-ca` value, or "". -/
  calendar : String := ""
  deriving Repr, Inhabited, BEq

def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- The digits at `i`, at most `max` of them: their value and count. -/
def scanDigits (cs : Array Char) (i max : Nat) : Nat × Nat := Id.run do
  let mut v := 0
  let mut n := 0
  for k in [0:max] do
    match cs[i + k]? with
    | some c => if isDigitC c then v := v * 10 + (c.toNat - 48); n := n + 1 else break
    | none => break
  return (v, n)

/-- Exactly `n` digits at `i`, or none. -/
def digitsExactly (cs : Array Char) (i n : Nat) : Option Nat :=
  let (v, k) := scanDigits cs i n
  if k == n then some v else none

/-- A fraction of a second after `.` or `,`: 1 to 9 digits, as nanoseconds; and the next index. -/
def scanFraction (cs : Array Char) (i : Nat) : Option (Nat × Nat) :=
  match cs[i]? with
  | some c =>
    if c == '.' || c == ',' then
      let (v, k) := scanDigits cs (i + 1) 9
      if k == 0 then none
      else if (cs[i + 1 + k]?.map isDigitC).getD false then none  -- more than nine digits
      else some (v * 10 ^ (9 - k), i + 1 + k)
    else some (0, i)
  | none => some (0, i)

/-- A time at `i` (`HH`, `HH:MM`, `HH:MM:SS[.f]`, or without colons): hour, minute, second
(60 read as 59), fraction, next index. -/
def scanTime (cs : Array Char) (i : Nat) : Option (Nat × Nat × Nat × Nat × Nat) := do
  let h ← digitsExactly cs i 2
  if h > 23 then none
  let ext := cs[i + 2]? == some ':'
  let j := if ext then i + 3 else i + 2
  match digitsExactly cs j 2 with
  | none => if ext then none else pure (h, 0, 0, 0, i + 2)
  | some mi =>
    if mi > 59 then none
    let colon2 := cs[j + 2]? == some ':'
    if colon2 && !ext then none
    let k := if colon2 then j + 3 else j + 2
    match digitsExactly cs k 2 with
    | none => if colon2 then none else pure (h, mi, 0, 0, j + 2)
    | some s =>
      if s > 60 then none
      let (f, e) ← scanFraction cs (k + 2)
      pure (h, mi, if s == 60 then 59 else s, f, e)

/-- A UTC offset at `i`: `Z`/`z` (kind 1) or `±HH[:MM[:SS[.f]]]` (kind 2, nanoseconds). -/
def scanOffset (cs : Array Char) (i : Nat) : Option (Nat × Int × Nat) :=
  match cs[i]? with
  | some 'Z' | some 'z' => some (1, 0, i + 1)
  | some c =>
    if c == '+' || c == '-' then do
      let sign : Int := if c == '-' then -1 else 1
      let (h, mi, s, f, e) ← scanTime cs (i + 1)
      if h > 23 then none
      pure (2, sign * timeToNs h mi s 0 0 f, e)
    else some (0, 0, i)
  | none => some (0, 0, i)

/-- One bracketed annotation at `i`: critical, key ("" for a time zone), value, next index. -/
def scanAnnotation (cs : Array Char) (i : Nat) : Option (Bool × String × String × Nat) := do
  if cs[i]? != some '[' then none
  let crit := cs[i + 1]? == some '!'
  let st := if crit then i + 2 else i + 1
  -- up to `]`
  let mut j := st
  let mut found := false
  for _ in [0:cs.size] do
    match cs[j]? with
    | some ']' => found := true; break
    | some _ => j := j + 1
    | none => break
  if !found || j == st then none
  let body := String.ofList (cs.extract st j).toList
  match body.splitOn "=" with
  | [tz] => pure (crit, "", tz, j + 1)
  | [k, v] =>
    if k.isEmpty || v.isEmpty then none
    if !(k.all fun c => ('a' ≤ c && c ≤ 'z') || isDigitC c || c == '-' || c == '_') then none
    pure (crit, k, v, j + 1)
  | _ => none

/-- The date at `i`: year, month, day, next index. -/
def scanDate (cs : Array Char) (i : Nat) : Option (Int × Nat × Nat × Nat) := do
  let (y, j) ← match cs[i]? with
    | some '+' | some '-' =>
      let neg := cs[i]? == some '-'
      match digitsExactly cs (i + 1) 6 with
      | some v => if neg && v == 0 then none else some ((if neg then -(v : Int) else v), i + 7)
      | none => none
    | _ => (digitsExactly cs i 4).map fun v => ((v : Int), i + 4)
  let ext := cs[j]? == some '-'
  let j := if ext then j + 1 else j
  let m ← digitsExactly cs j 2
  let ext2 := cs[j + 2]? == some '-'
  if ext != ext2 then none
  let k := if ext2 then j + 3 else j + 2
  let d ← digitsExactly cs k 2
  if m < 1 || m > 12 || d < 1 || d > 31 then none
  pure (y, m, d, k + 2)

/-- The annotations from `i` to the end: the time zone (if first) and the calendar. -/
def scanAnnotations (cs : Array Char) (i : Nat) : Option (String × String) := Id.run do
  let mut j := i
  let mut tz := ""
  let mut cal := ""
  let mut calCrit := false
  let mut calCount := 0
  let mut first := true
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    match scanAnnotation cs j with
    | none => return none
    | some (crit, k, v, e) =>
      if k == "" then
        if !first then return none
        tz := v
      else if k == "u-ca" then
        calCount := calCount + 1
        if calCount == 1 then cal := v
        if crit then calCrit := true
      else if crit then return none
      else if k.any (fun c => 'A' ≤ c && c ≤ 'Z') then return none
      first := false
      j := e
  if calCount > 1 && calCrit then return none
  return some (tz, cal)

/-- A Temporal date-time string (date, optional time and offset, annotations). -/
def parseDateTime (s : String) : Option DateTimeParts := do
  let cs := s.toList.toArray
  let (y, m, d, i) ← scanDate cs 0
  let (hasTime, h, mi, sec, f, i) ← match cs[i]? with
    | some 'T' | some 't' | some ' ' =>
      (scanTime cs (i + 1)).map fun (h, mi, sec, f, e) => (true, h, mi, sec, f, e)
    | _ => some (false, 0, 0, 0, 0, i)
  let (ok, on, i) ← if hasTime then scanOffset cs i else some (0, 0, i)
  let (tz, cal) ← scanAnnotations cs i
  pure { year := y, month := m, day := d, hasTime, hour := h, minute := mi, second := sec,
         fracNs := f, offsetKind := ok, offsetNs := on, timeZone := tz, calendar := cal }

/-- A time-only string (PlainTime): `T`-prefixed or bare time, with offset and annotations;
a full date-time string is read for its time. -/
def parseTimeString (s : String) : Option DateTimeParts :=
  match parseDateTime s with
  | some p => if p.hasTime then some p else none
  | none => do
    let cs := s.toList.toArray
    let st := if cs[0]? == some 'T' || cs[0]? == some 't' then 1 else 0
    let (h, mi, sec, f, i) ← scanTime cs st
    let (ok, on, i) ← scanOffset cs i
    if ok == 1 then none
    let (tz, cal) ← scanAnnotations cs i
    pure { hasDate := false, hasTime := true, hour := h, minute := mi, second := sec, fracNs := f,
           offsetKind := ok, offsetNs := on, timeZone := tz, calendar := cal }

/-! ## Durations -/

/-- An ISO 8601 duration: the ten fields (years … nanoseconds), sign applied. A fraction is
allowed on the last of hours, minutes or seconds and is carried down to nanoseconds. -/
def parseDuration (s : String) : Option (Array Int) := do
  let cs := s.toList.toArray
  let (sign, i) : Int × Nat := match cs[0]? with
    | some '-' => (-1, 1)
    | some '+' => (1, 1)
    | _ => (1, 0)
  if !(cs[i]? == some 'P' || cs[i]? == some 'p') then none
  let mut j := i + 1
  let mut out : Array Int := Array.replicate 10 0
  let mut inTime := false
  let mut last := 0  -- the order of the last unit read (to refuse out-of-order units)
  let mut any := false
  let mut fracSeen := false
  for _ in [0:cs.size + 1] do
    if j ≥ cs.size then break
    let c := cs[j]!
    if c == 'T' || c == 't' then
      if inTime then none
      inTime := true; j := j + 1
      if j ≥ cs.size then none
      continue
    if fracSeen then none
    let (v, k) := scanDigits cs j 30
    if k == 0 then none
    let (f, fd, e) : Nat × Nat × Nat :=
      match cs[j + k]? with
      | some '.' | some ',' =>
        let (fv, fk) := scanDigits cs (j + k + 1) 9
        (fv, fk, j + k + 1 + fk)
      | _ => (0, 0, j + k)
    if (cs[j + k]? == some '.' || cs[j + k]? == some ',') && fd == 0 then none
    let u ← cs[e]?
    let uu := u.toUpper
    let idx : Nat ← if !inTime then
        (match uu with | 'Y' => some 1 | 'M' => some 2 | 'W' => some 3 | 'D' => some 4 | _ => none)
      else (match uu with | 'H' => some 5 | 'M' => some 6 | 'S' => some 7 | _ => none)
    if idx ≤ last then none
    if fd > 0 && idx < 5 then none
    last := idx
    any := true
    out := out.set! (idx - 1) (v : Int)
    if fd > 0 then
      fracSeen := true
      -- the fraction of an hour, minute or second, in nanoseconds
      let unitNs : Nat := if idx == 5 then 3600000000000 else if idx == 6 then 60000000000 else 1000000000
      let fracNs := f * unitNs / 10 ^ fd
      if idx == 7 then
        out := out.set! 7 ((fracNs / 1000000 : Nat) : Int)
        out := out.set! 8 ((fracNs / 1000 % 1000 : Nat) : Int)
        out := out.set! 9 ((fracNs % 1000 : Nat) : Int)
      else
        -- carried into the smaller units below (minutes … nanoseconds)
        let rest := fracNs
        out := out.set! (idx) ((rest / (if idx == 5 then 60000000000 else 1000000000) : Nat) : Int)
        let r2 := rest % (if idx == 5 then 60000000000 else 1000000000)
        if idx == 5 then
          out := out.set! 6 ((r2 / 1000000000 : Nat) : Int)
          let r3 := r2 % 1000000000
          out := out.set! 7 ((r3 / 1000000 : Nat) : Int)
          out := out.set! 8 ((r3 / 1000 % 1000 : Nat) : Int)
          out := out.set! 9 ((r3 % 1000 : Nat) : Int)
        else
          out := out.set! 7 ((r2 / 1000000 : Nat) : Int)
          out := out.set! 8 ((r2 / 1000 % 1000 : Nat) : Int)
          out := out.set! 9 ((r2 % 1000 : Nat) : Int)
    j := e + 1
  if !any then none
  if inTime && last < 5 then none
  pure (out.map (· * sign))

/-! ## Writing -/

def pad (n : Nat) (w : Nat) : String :=
  let s := toString n
  String.ofList (List.replicate (w - s.length) '0') ++ s

/-- An ISO year: four digits for 0 to 9999, else a sign and six digits. -/
def formatYear (y : Int) : String :=
  if 0 ≤ y && y ≤ 9999 then pad y.toNat 4
  else (if y < 0 then "-" else "+") ++ pad y.natAbs 6

def formatDate (y : Int) (m d : Nat) : String := formatYear y ++ "-" ++ pad m 2 ++ "-" ++ pad d 2

/-- The fraction digits of `ns` nanoseconds: `digits` none for "auto" (trailing zeros dropped,
nothing when zero), else that many digits (0 to 9). -/
def formatFraction (ns : Nat) (digits : Option Nat) : String :=
  let full := pad ns 9
  match digits with
  | none =>
    if ns == 0 then "" else
    "." ++ String.ofList ((full.toList.reverse.dropWhile (· == '0')).reverse)
  | some 0 => ""
  | some k => "." ++ String.ofList (full.toList.take k)

/-- HH:MM, or HH:MM:SS[.fraction] (`precision` -1 for minutes, else as `formatFraction`). -/
def formatTime (h mi s ns : Nat) (precision : Option Int) : String :=
  match precision with
  | some (-1) => pad h 2 ++ ":" ++ pad mi 2
  | some p => pad h 2 ++ ":" ++ pad mi 2 ++ ":" ++ pad s 2 ++ formatFraction ns (some p.toNat)
  | none => pad h 2 ++ ":" ++ pad mi 2 ++ ":" ++ pad s 2 ++ formatFraction ns none

/-! ## Time zones (UTC and fixed offsets) -/

/-- The identifiers that name UTC (case-insensitive), canonicalized to "UTC". -/
def utcAliases : List String :=
  ["utc", "etc/utc", "etc/gmt", "gmt", "etc/universal", "universal", "etc/zulu", "zulu", "etc/uct", "uct",
   "etc/greenwich", "greenwich", "etc/gmt0", "gmt0", "etc/gmt+0", "etc/gmt-0", "gmt+0", "gmt-0"]

/-- A time zone identifier: UTC (kind 0) or a fixed offset of whole minutes (kind 1, in
nanoseconds), or none for anything else (named zones are not supported). -/
def parseTimeZoneId (s : String) : Option (Nat × Int) :=
  if utcAliases.contains s.toLower then some (0, 0) else
  let cs := s.toList.toArray
  match cs[0]? with
  | some '+' | some '-' =>
    match scanOffset cs 0 with
    | some (2, ns, e) => if e == cs.size && ns % 60000000000 == 0 then some (1, ns) else none
    | _ => none
  | _ => none

/-- An offset as `±HH:MM`, with `:SS` and a fraction when they are not zero (`full`), else
rounded to minutes (halfExpand). -/
def formatOffset (ns : Int) (full : Bool) : String :=
  let sign := if ns < 0 then "-" else "+"
  let a := ns.natAbs
  if full then
    let h := a / 3600000000000; let mi := a / 60000000000 % 60; let sec := a / 1000000000 % 60; let f := a % 1000000000
    sign ++ pad h 2 ++ ":" ++ pad mi 2 ++ (if sec == 0 && f == 0 then "" else ":" ++ pad sec 2 ++ formatFraction f none)
  else
    let mins := (a + 30000000000) / 60000000000
    sign ++ pad (mins / 60) 2 ++ ":" ++ pad (mins % 60) 2

#guard parseTimeZoneId "UTC" == some (0, 0) && parseTimeZoneId "etc/gmt" == some (0, 0) && parseTimeZoneId "+01:00" == some (1, 3600000000000)
#guard parseTimeZoneId "-0530" == some (1, -19800000000000) && parseTimeZoneId "+01:00:01" == none && parseTimeZoneId "Europe/Paris" == none
#guard formatOffset 3600000000000 false == "+01:00" && formatOffset (-19800000000000) true == "-05:30" && formatOffset 1 true == "+00:00:00.000000001"

/-! ## Checks -/

#guard (parseDateTime "1976-11-18").map (fun p => (p.year, p.month, p.day, p.hasTime)) == some (1976, 11, 18, false)
#guard (parseDateTime "19761118").map (·.day) == some 18
#guard (parseDateTime "+002019-01-31T12:30:45.5Z[UTC][u-ca=iso8601]").map
  (fun p => (p.year, p.hour, p.minute, p.second, p.fracNs, p.offsetKind, p.timeZone, p.calendar)) ==
  some (2019, 12, 30, 45, 500000000, 1, "UTC", "iso8601")
#guard parseDateTime "-000000-01-01" == none && parseDateTime "2020-13-01" == none && parseDateTime "2020-0101" == none
#guard parseDateTime "2020-01-01[!foo=bar]" == none && (parseDateTime "2020-01-01[foo=bar]").isSome
#guard parseDateTime "2020-01-01[u-ca=iso8601][!u-ca=gregory]" == none
#guard (parseDateTime "2020-01-01T00:00+01:00").map (·.offsetNs) == some 3600000000000
#guard (parseTimeString "T12:34").map (fun p => (p.hour, p.minute)) == some (12, 34)
#guard (parseTimeString "12:34:56,123").map (·.fracNs) == some 123000000
#guard parseDuration "P1Y2M3W4DT5H6M7.5S" == some #[1, 2, 3, 4, 5, 6, 7, 500, 0, 0]
#guard parseDuration "-PT1.5H" == some #[0, 0, 0, 0, -1, -30, 0, 0, 0, 0]
#guard parseDuration "P" == none && parseDuration "PT" == none && parseDuration "P1D2Y" == none && parseDuration "PT1.5H2M" == none
#guard formatDate 2019 2 8 == "2019-02-08" && formatDate (-1) 1 1 == "-000001-01-01" && formatDate 10000 1 1 == "+010000-01-01"
#guard formatTime 1 2 3 500000000 none == "01:02:03.5" && formatTime 1 2 3 0 none == "01:02:03" && formatTime 1 2 3 0 (some (-1)) == "01:02"

end L4Factoidal.Temporal
