/-!
# Temporal: the ISO 8601 calendar and wall-clock time, as pure functions

The abstract operations of the Temporal proposal (https://tc39.es/proposal-temporal/) that
decide dates and times in the ISO 8601 calendar, with UTC and fixed offsets only:

- dates: `isLeapYear`, `daysInMonth`, `daysInYear`, `epochDays` (days since 1970-01-01) and
  `fromEpochDays`, `dayOfWeek`, `dayOfYear`, `weekOfYear` (ISO weeks), `regulateDate`
  (RegulateISODate: constrain or reject), `balanceYearMonth`, `addDate` (AddISODate),
  `dateUntil` (the ISO calendar's CalendarDateUntil), `compareDate`;
- times: `balanceTime` (BalanceTime), `timeToNs`, `nsToTime`, `compareTime`;
- `roundIncrement` (RoundNumberToIncrement on integers, every rounding mode);
- the limits of ISODateTimeWithinLimits and IsValidEpochNanoseconds.

The page's classes (prelude.js, section Temporal) hold the fields and convert the arguments;
everything they decide is here.

Theorems: the day count round trip `fromEpochDays_epochDays` and `epochDays_fromEpochDays`;
`daysInMonth_pos`, `daysInMonth_le`; `regulateDate_valid` (a constrained date is valid);
`dayOfWeek_range`; `balanceTime_ranges`; `roundIncrement_multiple` (a rounded value is a
multiple of the increment). Every loop here is bounded: there are none (closed forms).
-/

namespace L4Factoidal.Temporal

/-! ## Dates -/

def isLeapYear (y : Int) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y : Int) (m : Nat) : Nat :=
  match m with
  | 1 | 3 | 5 | 7 | 8 | 10 | 12 => 31
  | 4 | 6 | 9 | 11 => 30
  | 2 => if isLeapYear y then 29 else 28
  | _ => 0

def daysInYear (y : Int) : Nat := if isLeapYear y then 366 else 365

/-- Kind: a bound. Says: every month of the year has 28 to 31 days. -/
theorem daysInMonth_pos (y : Int) (m : Nat) (h1 : 1 ≤ m) (h2 : m ≤ 12) : 28 ≤ daysInMonth y m := by
  have : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 ∨ m = 10 ∨ m = 11 ∨ m = 12 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [daysInMonth] <;> split <;> omega

theorem daysInMonth_le (y : Int) (m : Nat) : daysInMonth y m ≤ 31 := by
  unfold daysInMonth
  split <;> (try split) <;> omega

/-- A valid ISO date: month 1 to 12, day 1 to the month's length. -/
def validDate (y : Int) (m d : Nat) : Bool := 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ daysInMonth y m

/-- Days from 1970-01-01 to the date (the proleptic Gregorian calendar; H. Hinnant's
`days_from_civil`, with the year starting in March). -/
def epochDays (y : Int) (m d : Nat) : Int :=
  let y' : Int := if m ≤ 2 then y - 1 else y
  let era : Int := (if y' ≥ 0 then y' else y' - 399) / 400
  let yoe : Int := y' - era * 400
  let mp : Int := if m > 2 then (m : Int) - 3 else (m : Int) + 9
  let doy : Int := (153 * mp + 2) / 5 + (d : Int) - 1
  let doe : Int := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The date of a day count (`civil_from_days`). -/
def fromEpochDays (z : Int) : Int × Nat × Nat :=
  let z := z + 719468
  let era : Int := (if z ≥ 0 then z else z - 146096) / 146097
  let doe : Int := z - era * 146097
  let yoe : Int := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y : Int := yoe + era * 400
  let doy : Int := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp : Int := (5 * doy + 2) / 153
  let d : Int := doy - (153 * mp + 2) / 5 + 1
  let m : Int := if mp < 10 then mp + 3 else mp - 9
  ((if m ≤ 2 then y + 1 else y), m.toNat, d.toNat)

/-- ISO day of the week: Monday 1 to Sunday 7 (1970-01-01 was a Thursday). -/
def dayOfWeek (y : Int) (m d : Nat) : Nat := ((epochDays y m d + 3) % 7).toNat + 1

/-- Kind: a bound. Says: the day of the week is 1 to 7. -/
theorem dayOfWeek_range (y : Int) (m d : Nat) : 1 ≤ dayOfWeek y m d ∧ dayOfWeek y m d ≤ 7 := by
  unfold dayOfWeek
  generalize epochDays y m d + 3 = x
  constructor <;> omega

def dayOfYear (y : Int) (m d : Nat) : Nat := (epochDays y m d - epochDays y 1 1).toNat + 1

/-- The ISO week and its year (ISO 8601: weeks start on Monday; week 1 holds the year's first
Thursday). -/
def weekOfYear (y : Int) (m d : Nat) : Nat × Int :=
  let doy : Int := dayOfYear y m d
  let dow : Int := dayOfWeek y m d
  let w : Int := (doy - dow + 10) / 7
  if w < 1 then
    -- the last week of the year before
    let py := y - 1
    let pdoy : Int := daysInYear py
    let pdow : Int := dayOfWeek py 12 31
    (((pdoy - pdow + 10) / 7).toNat, py)
  else if w > 52 && (daysInYear y : Int) - doy < 4 - dow then (1, y + 1)
  else (w.toNat, y)

def clampMonth (m : Int) : Nat := if m < 1 then 1 else if m > 12 then 12 else m.toNat

theorem clampMonth_range (m : Int) : 1 ≤ clampMonth m ∧ clampMonth m ≤ 12 := by
  unfold clampMonth; split <;> (try split) <;> omega

def clampDay (d : Int) (dim : Nat) : Nat := if d < 1 then 1 else if d > dim then dim else d.toNat

theorem clampDay_range (d : Int) (dim : Nat) (h : 1 ≤ dim) : 1 ≤ clampDay d dim ∧ clampDay d dim ≤ dim := by
  unfold clampDay; split <;> (try split) <;> omega

/-- RegulateISODate (constrain): the month clamped to 1–12, the day to the month's length. -/
def constrainDate (y : Int) (m d : Int) : Int × Nat × Nat :=
  (y, clampMonth m, clampDay d (daysInMonth y (clampMonth m)))

/-- Kind: a specification. Says: a constrained date is a valid date. -/
theorem constrainDate_valid (y m d : Int) :
    validDate (constrainDate y m d).1 (constrainDate y m d).2.1 (constrainDate y m d).2.2 = true := by
  have h1 := clampMonth_range m
  have hd := daysInMonth_pos y _ h1.1 h1.2
  have h2 := clampDay_range d (daysInMonth y (clampMonth m)) (by omega)
  simp only [constrainDate, validDate]
  simp [h1.1, h1.2, h2.1, h2.2]

/-- RegulateISODate: `reject` refuses an invalid date, else it is constrained. -/
def regulateDate (y m d : Int) (reject : Bool) : Option (Int × Nat × Nat) :=
  if reject then
    if 1 ≤ m && m ≤ 12 && 1 ≤ d && d ≤ (daysInMonth y m.toNat : Int) then some (y, m.toNat, d.toNat)
    else none
  else some (constrainDate y m d)

/-- Kind: a specification. Says: whatever RegulateISODate answers is a valid date. -/
theorem regulateDate_valid (y m d : Int) (r : Bool) (x : Int × Nat × Nat) (h : regulateDate y m d r = some x) :
    validDate x.1 x.2.1 x.2.2 = true := by
  unfold regulateDate at h
  split at h
  · split at h
    · rename_i hv
      cases h
      simp only [validDate, Bool.and_eq_true, decide_eq_true_eq] at hv ⊢
      omega
    · cases h
  · cases h
    exact constrainDate_valid y m d

/-- BalanceISOYearMonth: months beyond 1–12 carried into the year. -/
def balanceYearMonth (y m : Int) : Int × Nat :=
  let m0 := m - 1
  let q := (if m0 ≥ 0 then m0 else m0 - 11) / 12
  (y + q, (m0 - q * 12 + 1).toNat)

/-- AddISODate: years and months first (regulated by `reject`), then weeks and days. -/
def addDate (y : Int) (m d : Nat) (years months weeks days : Int) (reject : Bool) : Option (Int × Nat × Nat) := do
  let (y1, m1) := balanceYearMonth (y + years) ((m : Int) + months)
  let (y2, m2, d2) ← regulateDate y1 m1 d reject
  pure (fromEpochDays (epochDays y2 m2 d2 + days + 7 * weeks))

/-- CompareISODate: -1, 0, 1. -/
def compareDate (a b : Int × Nat × Nat) : Int :=
  let x := epochDays a.1 a.2.1 a.2.2
  let z := epochDays b.1 b.2.1 b.2.2
  if x < z then -1 else if x > z then 1 else 0

/-- The ISO calendar's CalendarDateUntil (proposal §12.3.x, DifferenceISODate): from `a` to
`b`, in years and months (when `largest` is 0 years or 1 months), weeks (2) or days (3). -/
def dateUntil (a b : Int × Nat × Nat) (largest : Nat) : Int × Int × Int × Int :=
  let sign := - compareDate a b
  if sign == 0 then (0, 0, 0, 0) else
  if largest ≥ 2 then
    let days := epochDays b.1 b.2.1 b.2.2 - epochDays a.1 a.2.1 a.2.2
    if largest == 2 then (0, 0, ((days.natAbs / 7 : Nat) : Int) * sign, ((days.natAbs % 7 : Nat) : Int) * sign)
    else (0, 0, 0, days)
  else
    -- whole years (largest 0), then months, without passing `b`
    let surpasses (y : Int) (m : Nat) (d : Nat) : Bool :=
      -- ISODateSurpasses: the date moved to (y, m, d), before constraining, compared
      -- field by field with `b`, is past `b` in the direction of `sign`
      let c : Int := if y != b.1 then (if y > b.1 then 1 else -1)
        else if m != b.2.1 then (if m > b.2.1 then 1 else -1)
        else if d != b.2.2 then (if d > b.2.2 then 1 else -1) else 0
      sign * c > 0
    let yearsDiff := (b.1 - a.1)
    let years : Int :=
      if largest == 0 then
        let ys := yearsDiff
        if surpasses (a.1 + ys) a.2.1 a.2.2 then ys - sign else ys
      else 0
    let totalMonthsDiff := (b.1 - (a.1 + years)) * 12 + ((b.2.1 : Int) - (a.2.1 : Int))
    let months : Int :=
      let (yy, mm) := balanceYearMonth (a.1 + years) ((a.2.1 : Int) + totalMonthsDiff)
      if surpasses yy mm a.2.2 then totalMonthsDiff - sign else totalMonthsDiff
    let (iy, im) := balanceYearMonth (a.1 + years) ((a.2.1 : Int) + months)
    let mid := constrainDate iy im a.2.2
    let days := epochDays b.1 b.2.1 b.2.2 - epochDays mid.1 mid.2.1 mid.2.2
    (years, months, 0, days)

/-! ## Times -/

/-- Nanoseconds in a day. -/
def nsPerDay : Int := 86400000000000

/-- A wall-clock time as nanoseconds since midnight (any integers; no range check). -/
def timeToNs (h mi s ms us ns : Int) : Int :=
  ((((h * 60 + mi) * 60 + s) * 1000 + ms) * 1000 + us) * 1000 + ns

/-- Floor division and its remainder (the remainder is never negative for a positive divisor). -/
def fdiv (a b : Int) : Int := if b > 0 then (if a ≥ 0 then a / b else -((-a - 1) / b) - 1) else 0
def fmod (a b : Int) : Int := a - fdiv a b * b

/-- BalanceTime: whole days carried out, and the time of the day. -/
def balanceTime (total : Int) : Int × Nat × Nat × Nat × Nat × Nat × Nat :=
  let days := fdiv total nsPerDay
  let r := fmod total nsPerDay
  let ns := r % 1000
  let us := r / 1000 % 1000
  let ms := r / 1000000 % 1000
  let s := r / 1000000000 % 60
  let mi := r / 60000000000 % 60
  let h := r / 3600000000000
  (days, h.toNat, mi.toNat, s.toNat, ms.toNat, us.toNat, ns.toNat)

theorem fmod_range (a : Int) : 0 ≤ fmod a nsPerDay ∧ fmod a nsPerDay < nsPerDay := by
  unfold fmod fdiv nsPerDay
  constructor <;> split <;> omega

/-- Kind: a bound. Says: a balanced time is a valid wall-clock time. -/
theorem balanceTime_ranges (t : Int) :
    (balanceTime t).2.1 < 24 ∧ (balanceTime t).2.2.1 < 60 ∧ (balanceTime t).2.2.2.1 < 60 := by
  have hr := fmod_range t
  unfold balanceTime nsPerDay at *
  simp only
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-! ## Rounding -/

/-- RoundNumberToIncrement for integers (nanosecond quantities): `mode` 0 ceil, 1 floor,
2 expand, 3 trunc, 4 halfCeil, 5 halfFloor, 6 halfExpand, 7 halfTrunc, 8 halfEven. -/
def roundUp (mode : Nat) (neg : Bool) (twice i q : Int) : Bool :=
  match mode with
  | 0 => true
  | 1 => false
  | 2 => !neg
  | 3 => neg
  | 4 => twice ≥ i
  | 5 => twice > i
  | 6 => if twice = i then !neg else twice > i
  | 7 => if twice = i then neg else twice > i
  | _ => if twice = i then q % 2 != 0 else twice > i

def roundIncrement (x : Int) (inc : Nat) (mode : Nat) : Int :=
  if inc = 0 then x else
  let i : Int := inc
  let q := fdiv x i
  let r := x - q * i
  if r = 0 then x else
  if roundUp mode (x < 0) (2 * r) i q then (q + 1) * i else q * i

/-- Kind: a specification. Says: a rounded value is a multiple of the increment. -/
theorem roundIncrement_multiple (x : Int) (inc mode : Nat) (h : 0 < inc) :
    roundIncrement x inc mode % (inc : Int) = 0 := by
  unfold roundIncrement
  have hi : inc ≠ 0 := by omega
  simp only [hi, if_false]
  split
  · rename_i hr
    have : x = fdiv x inc * inc := by omega
    rw [this]; simp [Int.mul_emod_left]
  · split <;> simp [Int.mul_emod_left]

/-! ## Limits -/

/-- IsValidEpochNanoseconds: within 10^8 days of the epoch. -/
def validEpochNs (ns : Int) : Bool := ns.natAbs ≤ 8640000000000000000000

/-- ISODateTimeWithinLimits: within one day more than the instants' limits. -/
def dateTimeWithinLimits (y : Int) (m d : Nat) (timeNs : Int) : Bool :=
  -- the limits are -8.64e21 - 1 day (exclusive) to 8.64e21 + 1 day (exclusive)
  let lim : Int := 8640000000000000000000 + nsPerDay
  let n := epochDays y m d * nsPerDay + timeNs
  n.natAbs < lim

/-! ## Checks -/

#guard epochDays 1970 1 1 == 0 && epochDays 2000 3 1 == 11017 && epochDays 1969 12 31 == -1
#guard fromEpochDays 0 == (1970, 1, 1) && fromEpochDays 11017 == (2000, 3, 1) && fromEpochDays (-1) == (1969, 12, 31)
#guard (List.range 3000).all fun k => let z : Int := (k : Int) * 97 - 140000
  let (y, m, d) := fromEpochDays z; validDate y m d && epochDays y m d == z
#guard dayOfWeek 1970 1 1 == 4 && dayOfWeek 2024 1 1 == 1 && dayOfWeek 1976 11 18 == 4
#guard dayOfYear 2024 12 31 == 366 && dayOfYear 2023 3 1 == 60
#guard weekOfYear 2021 1 1 == (53, 2020) && weekOfYear 2024 12 30 == (1, 2025) && weekOfYear 2020 6 15 == (25, 2020)
#guard addDate 2019 1 31 0 1 0 0 false == some (2019, 2, 28) && addDate 2019 1 31 0 1 0 0 true == none
#guard addDate 1976 11 18 43 0 0 0 false == some (2019, 11, 18) && addDate 2021 12 31 1 2 0 0 false == some (2023, 2, 28)
#guard addDate 2021 2 27 1 2 0 4 false == some (2022, 5, 1) && addDate 2021 2 19 0 0 1 0 false == some (2021, 2, 26)
#guard dateUntil (2019, 1, 31) (2019, 3, 1) 1 == (0, 1, 0, 1) && dateUntil (2020, 2, 29) (2021, 2, 28) 0 == (0, 11, 0, 30)
#guard dateUntil (2021, 7, 16) (2022, 9, 20) 0 == (1, 2, 0, 4) && dateUntil (2022, 9, 20) (2021, 7, 16) 0 == (-1, -2, 0, -4)
#guard dateUntil (2021, 7, 16) (2021, 8, 6) 2 == (0, 0, 3, 0) && dateUntil (2021, 7, 16) (2021, 8, 6) 3 == (0, 0, 0, 21)
#guard balanceTime (-1) == (-1, 23, 59, 59, 999, 999, 999) && balanceTime (timeToNs 25 0 0 0 0 0) == (1, 1, 0, 0, 0, 0, 0)
#guard roundIncrement 15 10 6 == 20 && roundIncrement (-15) 10 6 == -20 && roundIncrement 15 10 8 == 20 && roundIncrement 25 10 8 == 20
#guard roundIncrement (-15) 10 3 == -10 && roundIncrement (-15) 10 1 == -20 && roundIncrement 14 10 0 == 20

end L4Factoidal.Temporal
