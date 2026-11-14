/-! Letter case for `text-transform` (CSS Text 3 §2.1), on code points. This module has no
import from the engine.

`upperPoint` and `lowerPoint` map one code point to one code point, for the basic Latin,
Latin-1, Greek and Cyrillic letters. A mapping that changes the number of characters
(`ß` to `SS`) and the letters of other blocks are left as they are, so a transformed text
has the same length and the same clusters as its source: positions in the text of the page
stay valid.

Proved: both are idempotent; lowering then raising is raising (`upper_lower`); a code point
outside the four blocks is unchanged (`upperPoint_other`). -/
namespace L4Factoidal.Rendering.TextCase

/-- The upper-case form of a code point, when it is one code point. -/
def upperPoint (n : Nat) : Nat :=
  if 0x61 ≤ n ∧ n ≤ 0x7A then n - 0x20                         -- a..z
  else if 0xE0 ≤ n ∧ n ≤ 0xFE ∧ n ≠ 0xF7 then n - 0x20         -- à..þ, not the division sign
  else if n = 0xFF then 0x178                                   -- ÿ
  else if n = 0x3C2 then 0x3A3                                  -- final sigma
  else if 0x3B1 ≤ n ∧ n ≤ 0x3C9 then n - 0x20                  -- α..ω
  else if 0x430 ≤ n ∧ n ≤ 0x44F then n - 0x20                  -- а..я
  else if 0x450 ≤ n ∧ n ≤ 0x45F then n - 0x50                  -- ѐ..џ
  else n

/-- The lower-case form of a code point, when it is one code point. -/
def lowerPoint (n : Nat) : Nat :=
  if 0x41 ≤ n ∧ n ≤ 0x5A then n + 0x20                         -- A..Z
  else if 0xC0 ≤ n ∧ n ≤ 0xDE ∧ n ≠ 0xD7 then n + 0x20         -- À..Þ, not the multiplication sign
  else if n = 0x178 then 0xFF                                   -- Ÿ
  else if 0x391 ≤ n ∧ n ≤ 0x3A9 ∧ n ≠ 0x3A2 then n + 0x20      -- Α..Ω
  else if 0x410 ≤ n ∧ n ≤ 0x42F then n + 0x20                  -- А..Я
  else if 0x400 ≤ n ∧ n ≤ 0x40F then n + 0x50                  -- Ѐ..Џ
  else n

/-- A code point that `upperPoint` changes: a lower-case letter of the four blocks. -/
def isLowerPoint (m : Nat) : Prop :=
  (0x61 ≤ m ∧ m ≤ 0x7A) ∨ (0xE0 ≤ m ∧ m ≤ 0xFF ∧ m ≠ 0xF7) ∨ (0x3B1 ≤ m ∧ m ≤ 0x3C9) ∨ (0x430 ≤ m ∧ m ≤ 0x45F)

/-- A code point that `lowerPoint` changes: an upper-case letter of the four blocks. -/
def isUpperPoint (m : Nat) : Prop :=
  (0x41 ≤ m ∧ m ≤ 0x5A) ∨ (0xC0 ≤ m ∧ m ≤ 0xDE ∧ m ≠ 0xD7) ∨ m = 0x178 ∨ (0x391 ≤ m ∧ m ≤ 0x3A9 ∧ m ≠ 0x3A2) ∨
    (0x400 ≤ m ∧ m ≤ 0x42F)

theorem upperPoint_of_not_lower (m : Nat) (h : ¬ isLowerPoint m) : upperPoint m = m := by
  unfold isLowerPoint at h
  unfold upperPoint
  repeat' split
  all_goals omega

theorem lowerPoint_of_not_upper (m : Nat) (h : ¬ isUpperPoint m) : lowerPoint m = m := by
  unfold isUpperPoint at h
  unfold lowerPoint
  repeat' split
  all_goals omega

/-- Says: an upper-case form is not a lower-case letter. -/
theorem upperPoint_not_lower (n : Nat) : ¬ isLowerPoint (upperPoint n) := by
  unfold upperPoint
  repeat' split
  all_goals (unfold isLowerPoint; omega)

theorem lowerPoint_not_upper (n : Nat) : ¬ isUpperPoint (lowerPoint n) := by
  unfold lowerPoint
  repeat' split
  all_goals (unfold isUpperPoint; omega)

theorem upperPoint_idem (n : Nat) : upperPoint (upperPoint n) = upperPoint n :=
  upperPoint_of_not_lower _ (upperPoint_not_lower n)

theorem lowerPoint_idem (n : Nat) : lowerPoint (lowerPoint n) = lowerPoint n :=
  lowerPoint_of_not_upper _ (lowerPoint_not_upper n)

/-- Says: the lower-case form of a letter has the same upper-case form as the letter. -/
theorem upper_lower (n : Nat) : upperPoint (lowerPoint n) = upperPoint n := by
  by_cases h : isUpperPoint n
  · -- an upper-case letter is its own upper-case form, and its lower-case form's
    have fixed : upperPoint n = n :=
      upperPoint_of_not_lower n (by unfold isUpperPoint at h; unfold isLowerPoint; omega)
    rw [fixed]
    unfold isUpperPoint at h
    unfold lowerPoint
    repeat' split
    all_goals (unfold upperPoint; repeat' split)
    all_goals omega
  · rw [lowerPoint_of_not_upper n h]

/-- Says: a code point outside the letters of the four blocks is unchanged. -/
theorem upperPoint_other (n : Nat) (h : n < 0x61 ∨ (0x7A < n ∧ n < 0xE0) ∨ (0xFF < n ∧ n < 0x3B1) ∨ 0x45F < n) :
    upperPoint n = n := by
  unfold upperPoint
  repeat' split
  all_goals omega

/-- Says: a transformed code point is in the Basic Multilingual Plane when its source is,
and never a surrogate: it is a character. -/
theorem upperPoint_valid (n : Nat) (h : n < 0xD800) : upperPoint n < 0xD800 := by
  unfold upperPoint
  repeat' split
  all_goals omega

theorem lowerPoint_valid (n : Nat) (h : n < 0xD800) : lowerPoint n < 0xD800 := by
  unfold lowerPoint
  repeat' split
  all_goals omega

/-- The character in upper case; a character past the letters this module knows is itself. -/
def upper (c : Char) : Char := if c.toNat < 0x460 then Char.ofNat (upperPoint c.toNat) else c

/-- The character in lower case. -/
def lower (c : Char) : Char := if c.toNat < 0x460 then Char.ofNat (lowerPoint c.toNat) else c

#guard upper 'a' == 'A'
#guard upper 'Z' == 'Z'
#guard upper 'é' == 'É'
#guard upper '÷' == '÷'
#guard upper 'ÿ' == 'Ÿ'
#guard upper 'ß' == 'ß'
#guard upper 'ω' == 'Ω'
#guard upper 'ς' == 'Σ'
#guard upper 'я' == 'Я'
#guard upper 'ё' == 'Ё'
#guard upper '1' == '1'
#guard upper '漢' == '漢'
#guard lower 'A' == 'a'
#guard lower 'É' == 'é'
#guard lower '×' == '×'
#guard lower 'Σ' == 'σ'
#guard lower 'Ё' == 'ё'
#guard lower 'Ÿ' == 'ÿ'
#guard "Straße".map upper == "STRAßE"

end L4Factoidal.Rendering.TextCase
