/-
L4Factoidal.WebDriver.Keys: the keys of WebDriver (W3C WebDriver §15.4.2, "Keyboard
actions") as UI Events key data.

A key action carries one "raw key": a code point. The code points U+E000 to U+E05D name
the keys with no character (Enter, the arrows, the modifiers, the keypad); any other is the
character a key of a US keyboard makes. This module decides, for a raw key and the
modifiers held, the `key`, `code`, `location` and legacy `keyCode` of its keyboard events.
The test driver of the WPT runner, the WebDriver server and any other source of key input
read this one table.

Proved: `special_bounded` (every table row is in U+E000 to U+E05D, so no character of
text is read as a named key), `ofRaw_printable` (a character outside the table keeps its
character as `key`), `ofRaw_special` (a table row gives its `key`, `code` and `location`),
`modifier_iff` (the four modifier keys, and no other key value).
Tested: `#guard` rows from the WPT data (`webdriver/tests/support/keys.py`).
-/

namespace L4Factoidal.WebDriver.Keys

/-- WebDriver §15.4.2, the keys named by private-use code points: the code point, the
normalised key value, the `code` and the `location` (0 standard, 1 left, 2 right,
3 numpad) as `webdriver/tests/support/keys.py` records them. -/
def special : List (Nat × String × String × Nat) := [
  (0xE000, "Unidentified", "", 0),
  (0xE001, "Cancel", "", 0),
  (0xE002, "Help", "Help", 0),
  (0xE003, "Backspace", "Backspace", 0),
  (0xE004, "Tab", "Tab", 0),
  (0xE005, "Clear", "", 0),
  (0xE006, "Enter", "Enter", 0),
  (0xE007, "Enter", "NumpadEnter", 1),
  (0xE008, "Shift", "ShiftLeft", 1),
  (0xE009, "Control", "ControlLeft", 1),
  (0xE00A, "Alt", "AltLeft", 1),
  (0xE00B, "Pause", "Pause", 0),
  (0xE00C, "Escape", "Escape", 0),
  (0xE00D, " ", "Space", 0),
  (0xE00E, "PageUp", "PageUp", 0),
  (0xE00F, "PageDown", "PageDown", 0),
  (0xE010, "End", "End", 0),
  (0xE011, "Home", "Home", 0),
  (0xE012, "ArrowLeft", "ArrowLeft", 0),
  (0xE013, "ArrowUp", "ArrowUp", 0),
  (0xE014, "ArrowRight", "ArrowRight", 0),
  (0xE015, "ArrowDown", "ArrowDown", 0),
  (0xE016, "Insert", "Insert", 0),
  (0xE017, "Delete", "Delete", 0),
  (0xE018, ";", "", 0),
  (0xE019, "=", "NumpadEqual", 3),
  (0xE01A, "0", "Numpad0", 3),
  (0xE01B, "1", "Numpad1", 3),
  (0xE01C, "2", "Numpad2", 3),
  (0xE01D, "3", "Numpad3", 3),
  (0xE01E, "4", "Numpad4", 3),
  (0xE01F, "5", "Numpad5", 3),
  (0xE020, "6", "Numpad6", 3),
  (0xE021, "7", "Numpad7", 3),
  (0xE022, "8", "Numpad8", 3),
  (0xE023, "9", "Numpad9", 3),
  (0xE024, "*", "NumpadMultiply", 3),
  (0xE025, "+", "NumpadAdd", 3),
  (0xE026, ",", "NumpadComma", 3),
  (0xE027, "-", "NumpadSubtract", 3),
  (0xE028, ".", "NumpadDecimal", 3),
  (0xE029, "/", "NumpadDivide", 3),
  (0xE031, "F1", "F1", 0),
  (0xE032, "F2", "F2", 0),
  (0xE033, "F3", "F3", 0),
  (0xE034, "F4", "F4", 0),
  (0xE035, "F5", "F5", 0),
  (0xE036, "F6", "F6", 0),
  (0xE037, "F7", "F7", 0),
  (0xE038, "F8", "F8", 0),
  (0xE039, "F9", "F9", 0),
  (0xE03A, "F10", "F10", 0),
  (0xE03B, "F11", "F11", 0),
  (0xE03C, "F12", "F12", 0),
  (0xE03D, "Meta", "MetaLeft", 1),
  (0xE040, "ZenkakuHankaku", "", 0),
  (0xE050, "Shift", "ShiftRight", 2),
  (0xE051, "Control", "ControlRight", 2),
  (0xE052, "Alt", "AltRight", 2),
  (0xE053, "Meta", "MetaRight", 2),
  (0xE054, "PageUp", "Numpad9", 3),
  (0xE055, "PageDown", "Numpad3", 3),
  (0xE056, "End", "Numpad1", 3),
  (0xE057, "Home", "Numpad7", 3),
  (0xE058, "ArrowLeft", "Numpad4", 3),
  (0xE059, "ArrowUp", "Numpad8", 3),
  (0xE05A, "ArrowRight", "Numpad6", 3),
  (0xE05B, "ArrowDown", "Numpad2", 3),
  (0xE05C, "Insert", "Numpad0", 3),
  (0xE05D, "Delete", "NumpadDecimal", 3)]

/-- The row of a raw key in `special`. -/
def specialOf (c : Char) : Option (String × String × Nat) :=
  (special.find? (·.1 == c.toNat)).map (·.2)

/-- The keys of a US keyboard that make a character other than a letter: the character,
the character with Shift, the `code`, and the legacy `keyCode` (WebDriver §15.4.2, the
table of "code for key"; UI Events, fixed virtual key codes). -/
def printable : List (Char × Char × String × Nat) := [
  ('`', '~', "Backquote", 192), ('\\', '|', "Backslash", 220), ('[', '{', "BracketLeft", 219),
  (']', '}', "BracketRight", 221), (',', '<', "Comma", 188), ('0', ')', "Digit0", 48),
  ('1', '!', "Digit1", 49), ('2', '@', "Digit2", 50), ('3', '#', "Digit3", 51),
  ('4', '$', "Digit4", 52), ('5', '%', "Digit5", 53), ('6', '^', "Digit6", 54),
  ('7', '&', "Digit7", 55), ('8', '*', "Digit8", 56), ('9', '(', "Digit9", 57),
  ('=', '+', "Equal", 187), ('-', '_', "Minus", 189), ('.', '>', "Period", 190),
  ('\'', '"', "Quote", 222), (';', ':', "Semicolon", 186), ('/', '?', "Slash", 191),
  (' ', ' ', "Space", 32)]

def isLower (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'
def isUpper (c : Char) : Bool := 'A' ≤ c && c ≤ 'Z'

/-- The `code` of the key that makes a character on a US keyboard; "" when no key does. -/
def codeOfChar (c : Char) : String :=
  if isLower c then "Key" ++ String.singleton c.toUpper
  else if isUpper c then "Key" ++ String.singleton c
  else match printable.find? (fun r => r.1 == c || r.2.1 == c) with
    | some r => r.2.2.1
    | none => ""

/-- The character needs Shift on a US keyboard ("shifted character", WebDriver §15.4.2). -/
def isShifted (c : Char) : Bool :=
  isUpper c || printable.any (fun r => r.2.1 == c && r.1 != c)

/-- The legacy `keyCode` of a key value (UI Events, legacy key attributes): the fixed
codes of the named keys, the upper-case letter or digit of a character key, else 0. -/
def keyCodeOf (key : String) : Nat :=
  match key with
  | "Backspace" => 8 | "Tab" => 9 | "Enter" => 13 | "Shift" => 16 | "Control" => 17
  | "Alt" => 18 | "Pause" => 19 | "Escape" => 27 | "PageUp" => 33 | "PageDown" => 34
  | "End" => 35 | "Home" => 36 | "ArrowLeft" => 37 | "ArrowUp" => 38 | "ArrowRight" => 39
  | "ArrowDown" => 40 | "Insert" => 45 | "Delete" => 46 | "Meta" => 91 | "Help" => 47
  | "Cancel" => 3 | "Clear" => 12
  | "F1" => 112 | "F2" => 113 | "F3" => 114 | "F4" => 115 | "F5" => 116 | "F6" => 117
  | "F7" => 118 | "F8" => 119 | "F9" => 120 | "F10" => 121 | "F11" => 122 | "F12" => 123
  | _ =>
    match key.toList with
    | [c] =>
      if isLower c then c.toUpper.toNat
      else if isUpper c then c.toNat
      else match printable.find? (fun r => r.1 == c || r.2.1 == c) with
        | some r => r.2.2.2
        | none => 0
    | _ => 0

/-- The data of a key for its keyboard events. -/
structure KeyData where
  key : String
  code : String
  location : Nat := 0
  keyCode : Nat := 0
  deriving Repr, DecidableEq, Inhabited

/-- The key data of a raw key (WebDriver §15.4.2 "normalised key value", "code for key",
"key location"): a row of `special`, else the character itself with the `code` of the key
that makes it. -/
def ofRaw (c : Char) : KeyData :=
  match specialOf c with
  | some (key, code, location) => { key, code, location, keyCode := keyCodeOf key }
  | none =>
    let key := String.singleton c
    { key, code := codeOfChar c, location := 0, keyCode := keyCodeOf key }

/-- The modifier a key value is, if any: "Shift", "Control", "Alt" or "Meta". -/
def isModifier (key : String) : Bool := key == "Shift" || key == "Control" || key == "Alt" || key == "Meta"

/-- The keyboard of a raw key is the numeric keypad's or a right-hand modifier: Element
Send Keys does not treat such a key as typeable text (WebDriver §12.5.3). -/
def isSpecial (c : Char) : Bool := (specialOf c).isSome

/-! ## Theorems -/

/-- Table bound. Says: every row of `special` is a private-use code point from U+E000 to
U+E05D, so no letter, digit or punctuation of a text is read as a named key. Does not
say: that every code point in that range has a row (U+E02A to U+E030 have none). -/
theorem special_bounded : special.all (fun r => 0xE000 ≤ r.1 && r.1 ≤ 0xE05D) = true := by decide

/-- Printable. Says: a raw key with no row in `special` has itself as its `key` and
location 0: typing a character gives that character. Does not say: which `code` it has
(a character no key of a US keyboard makes has ""). -/
theorem ofRaw_printable (c : Char) (h : specialOf c = none) :
    (ofRaw c).key = String.singleton c ∧ (ofRaw c).location = 0 := by
  simp [ofRaw, h]

/-- Named keys. Says: a raw key with a row in `special` gets that row's key value, `code`
and location. Does not say: that browsers agree on the `code` of keys the table leaves "". -/
theorem ofRaw_special (c : Char) (key code : String) (location : Nat)
    (h : specialOf c = some (key, code, location)) :
    (ofRaw c).key = key ∧ (ofRaw c).code = code ∧ (ofRaw c).location = location := by
  simp [ofRaw, h]

/-- Modifiers. Says: `isModifier` holds of exactly the four modifier key values. Does not
say: which raw keys give them (U+E008 to U+E00A, U+E03D and U+E050 to U+E053, by `special`). -/
theorem modifier_iff (key : String) :
    isModifier key = true ↔ key = "Shift" ∨ key = "Control" ∨ key = "Alt" ∨ key = "Meta" := by
  simp [isModifier, or_assoc]

/-! ## Tests (rows of `webdriver/tests/support/keys.py` and the "code for key" table) -/

#guard ofRaw (Char.ofNat 0xE003) == { key := "Backspace", code := "Backspace", location := 0, keyCode := 8 }
#guard ofRaw (Char.ofNat 0xE006) == { key := "Enter", code := "Enter", location := 0, keyCode := 13 }
#guard ofRaw (Char.ofNat 0xE008) == { key := "Shift", code := "ShiftLeft", location := 1, keyCode := 16 }
#guard ofRaw (Char.ofNat 0xE050) == { key := "Shift", code := "ShiftRight", location := 2, keyCode := 16 }
#guard ofRaw (Char.ofNat 0xE03D) == { key := "Meta", code := "MetaLeft", location := 1, keyCode := 91 }
#guard ofRaw (Char.ofNat 0xE025) == { key := "+", code := "NumpadAdd", location := 3, keyCode := 187 }
#guard ofRaw (Char.ofNat 0xE05B) == { key := "ArrowDown", code := "Numpad2", location := 3, keyCode := 40 }
#guard ofRaw 'a' == { key := "a", code := "KeyA", location := 0, keyCode := 65 }
#guard ofRaw 'Q' == { key := "Q", code := "KeyQ", location := 0, keyCode := 81 }
#guard ofRaw '!' == { key := "!", code := "Digit1", location := 0, keyCode := 49 }
#guard ofRaw ' ' == { key := " ", code := "Space", location := 0, keyCode := 32 }
#guard ofRaw 'é' == { key := "é", code := "", location := 0, keyCode := 0 }
#guard isShifted 'A' && isShifted '!' && isShifted '"' && !isShifted 'a' && !isShifted '1' && !isShifted ' '
#guard special.length == 70
#guard (special.map (·.1)).eraseDups.length == 70

end L4Factoidal.WebDriver.Keys
