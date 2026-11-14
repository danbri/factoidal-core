/-
L4Factoidal.WebDriver.HostKeys: the keys a person presses in a host (the window, the Hub,
a terminal) as WebDriver key actions, so that every host's keys and the test driver's keys
take one path into the page: `Actions.perform` with the trusted input state, then
`Hosts.PageEvents.dispatchLow` (key events, `keypress`, editing, caret moves).

A host gives one of three things:

- `text`: committed text (the window's `insertText`, after the keyboard layout and dead
  keys): typed as WebDriver's Element Send Keys types a string (`Actions.typeable`), so a
  person's typing and `test_driver.send_keys` are the same actions;
- `mac`: a macOS virtual key code with the modifier bits of the window (1 Shift, 2
  Command, 4 Option, 8 Control): a key with no character (Return, Tab, Delete, the arrows,
  Home, End, Page Up/Down, Escape, F1 to F12) or Space, or a character key held with Command or
  Control (no text is committed then); any other key is `none`, since its text follows;
- `dom`: a DOM `KeyboardEvent.key` value with the same modifier bits (the Hub, where the
  host browser already decided the key).

A key is pressed: the modifiers held go down, the key goes down and up, the modifiers go
up, the last pressed first (`press`). The window reports no key releases, so a press is
whole.

Proved: `mac_named_special` (every named row of `mac` is a WebDriver named key),
`modifiers_are_modifiers` (the modifier bits give only the four modifier keys),
`press_balanced` (the keys released are the keys pressed, last first, so no key stays
held), `text_is_send_keys` (a host's text is Element Send Keys' typing).
Tested: `#guard`s below.
-/
import L4Factoidal.WebDriver.Actions

namespace L4Factoidal.WebDriver.HostKeys
open Actions

/-- macOS virtual key codes (Carbon `kVK_*`) of the keys with no character, and Space,
and the WebDriver raw key of each (§15.4.2). Space is here because it also scrolls a page:
its keydown decides that (the window does not send Space's committed text again). -/
def macNamed : List (Nat × Nat) := [
  (49, 0xE00D), (36, 0xE006), (76, 0xE007), (48, 0xE004), (51, 0xE003), (117, 0xE017), (53, 0xE00C),
  (123, 0xE012), (124, 0xE014), (125, 0xE015), (126, 0xE013),
  (115, 0xE011), (119, 0xE010), (116, 0xE00E), (121, 0xE00F), (114, 0xE002),
  (122, 0xE031), (120, 0xE032), (99, 0xE033), (118, 0xE034), (96, 0xE035), (97, 0xE036),
  (98, 0xE037), (100, 0xE038), (101, 0xE039), (109, 0xE03A), (103, 0xE03B), (111, 0xE03C)]

/-- macOS virtual key codes (`kVK_ANSI_*`, US layout) of the character keys and their
character without Shift: what a key held with Command or Control types. -/
def macChars : List (Nat × Char) := [
  (0, 'a'), (1, 's'), (2, 'd'), (3, 'f'), (4, 'h'), (5, 'g'), (6, 'z'), (7, 'x'), (8, 'c'),
  (9, 'v'), (11, 'b'), (12, 'q'), (13, 'w'), (14, 'e'), (15, 'r'), (16, 'y'), (17, 't'),
  (18, '1'), (19, '2'), (20, '3'), (21, '4'), (22, '6'), (23, '5'), (24, '='), (25, '9'),
  (26, '7'), (27, '-'), (28, '8'), (29, '0'), (30, ']'), (31, 'o'), (32, 'u'), (33, '['),
  (34, 'i'), (35, 'p'), (37, 'l'), (38, 'j'), (39, '\''), (40, 'k'), (41, ';'), (42, '\\'),
  (43, ','), (44, '/'), (45, 'n'), (46, 'm'), (47, '.'), (50, '`')]

/-- The modifier bits of the hosts and the WebDriver raw key of each: Shift, Command
(Meta), Option (Alt), Control. -/
def modifierBits : List (Nat × Nat) := [(1, 0xE008), (2, 0xE03D), (4, 0xE00A), (8, 0xE009)]

/-- The modifier keys held, as raw keys, in the order of `modifierBits`. -/
def modifiers (bits : Nat) : List Char :=
  (modifierBits.filter fun r => bits &&& r.1 != 0).map fun r => Char.ofNat r.2

/-- The character a key makes with Shift held (US layout). -/
def shifted (c : Char) : Char :=
  if Keys.isLower c then c.toUpper
  else match Keys.printable.find? (·.1 == c) with
    | some r => r.2.1
    | none => c

/-- The raw key of a macOS key code with the modifier bits: a named key, or a character
key when Command or Control is held (the character with Shift when Shift is held); `none`
when the key's committed text follows instead. -/
def ofMac (code bits : Nat) : Option Char :=
  match macNamed.find? (·.1 == code) with
  | some r => some (Char.ofNat r.2)
  | none =>
    if bits &&& 10 == 0 then none
    else (macChars.find? (·.1 == code)).map fun r => if bits &&& 1 != 0 then shifted r.2 else r.2

/-- The raw key of a DOM `KeyboardEvent.key` value: a single character is itself; a
named key is its first row in WebDriver's table (the standard keyboard's, before the
right-hand and keypad rows); "Unidentified" and unknown names are `none`. -/
def ofDomKey (key : String) : Option Char :=
  match key.toList with
  | [c] => some c
  | _ =>
    if key == "Unidentified" then none
    else (Keys.special.find? (·.2.1 == key)).map fun r => Char.ofNat r.1

/-- A key pressed with the modifiers held: they go down, the key goes down and up, they
go up, the last first. A modifier key itself is pressed alone. -/
def press (raw : Char) (bits : Nat) : List Action :=
  let v := String.singleton raw
  let held := if Keys.isModifier (Keys.ofRaw raw).key then [] else (modifiers bits).map String.singleton
  held.map Action.keyDown ++ [Action.keyDown v, Action.keyUp v] ++ held.reverse.map Action.keyUp

/-- What a host gives for a key. -/
inductive HostKey where
  | text (s : String)
  | mac (code bits : Nat)
  | dom (key : String) (bits : Nat)
  deriving Repr, DecidableEq

/-- The key actions of a host's key. -/
def actionsOf : HostKey → List Action
  | .text s => typeable s
  | .mac code bits => match ofMac code bits with
    | some raw => press raw bits
    | none => []
  | .dom key bits => match ofDomKey key with
    | some raw => press raw bits
    | none => []

/-- The input source of a host's key: one key source, as a test driver's would be. -/
def sourceOf (k : HostKey) : Source := { id := "host keyboard", kind := .key, actions := actionsOf k }

/-- The key values that go down, in order. -/
def downs (as : List Action) : List String := as.filterMap fun | .keyDown v => some v | _ => none

/-- The key values that go up, in order. -/
def ups (as : List Action) : List String := as.filterMap fun | .keyUp v => some v | _ => none

/-! ## Theorems -/

/-- Named keys. Says: every row of `macNamed` is a key of WebDriver's table, so the window's
Return, Tab, arrows and the rest reach the page with that table's `key` and `code`. Does
not say: that the codes are those of every Apple keyboard (they are the ANSI layout's). -/
theorem mac_named_special :
    macNamed.all (fun r => Keys.special.any (·.1 == r.2)) = true := by decide

/-- Modifier bits. Says: whatever the bits, the keys held for them are among Shift,
Meta, Alt and Control, and only the four bits count. Does not say: which of the left or
right key was held (the left one is reported). -/
theorem modifiers_are_modifiers (bits : Nat) :
    ∀ c ∈ modifiers bits, c.toNat ∈ [0xE008, 0xE03D, 0xE00A, 0xE009] := by
  intro c hc
  simp only [modifiers, List.mem_map, List.mem_filter] at hc
  obtain ⟨r, ⟨hr, _⟩, rfl⟩ := hc
  simp only [modifierBits, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> decide

/-- Balanced press. Says: the keys a press releases are exactly the keys it pressed, in
the reverse order, so after a host's key no key and no modifier is held (`Actions.step`
releases a key value that is held). Does not say: that a page sees the release (a page
may move the focus between the two). -/
theorem press_balanced (raw : Char) (bits : Nat) :
    ups (press raw bits) = (downs (press raw bits)).reverse := by
  simp only [press, ups, downs, List.filterMap_append, List.filterMap_map, List.filterMap_cons,
    List.filterMap_nil, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append]
  split <;> simp [Function.comp_def, List.filterMap_reverse]

/-- One path for text. Says: the text a host commits is typed as WebDriver's Element Send
Keys types a string, so a person's typing and `test_driver.send_keys` give the page the
same events. -/
theorem text_is_send_keys (s : String) : actionsOf (.text s) = typeable s := rfl

/-! ## Tests -/

#guard ofMac 36 0 == some (Char.ofNat 0xE006)
#guard ofMac 123 1 == some (Char.ofNat 0xE012)
#guard ofMac 0 0 == none
#guard ofMac 49 0 == some (Char.ofNat 0xE00D) && (Keys.ofRaw (Char.ofNat 0xE00D)).key == " "
#guard ofMac 0 8 == some 'a'
#guard ofMac 11 2 == some 'b'
#guard ofMac 0 9 == some 'A'
#guard ofMac 18 9 == some '!'
#guard ofDomKey "Enter" == some (Char.ofNat 0xE006)
#guard ofDomKey "Shift" == some (Char.ofNat 0xE008)
#guard ofDomKey "ArrowDown" == some (Char.ofNat 0xE015)
#guard ofDomKey "a" == some 'a'
#guard ofDomKey "Unidentified" == none
#guard ofDomKey "NoSuchKey" == none
#guard press 'a' 8 == [.keyDown "", .keyDown "a", .keyUp "a", .keyUp ""]
#guard press 'A' 9 == [.keyDown "", .keyDown "", .keyDown "A", .keyUp "A", .keyUp "", .keyUp ""]
#guard press (Char.ofNat 0xE008) 1 == [.keyDown "", .keyUp ""]
#guard actionsOf (.mac 51 0) == [.keyDown "", .keyUp ""]
#guard actionsOf (.mac 0 0) == []
#guard actionsOf (.text "x") == [.keyDown "x", .keyUp "x"]
#guard actionsOf (.dom "Tab" 1) == [.keyDown "", .keyDown "", .keyUp "", .keyUp ""]
-- every named macOS key is read by `Keys.ofRaw` as a named key, never as its character
#guard macNamed.all fun r => (Keys.specialOf (Char.ofNat r.2)).isSome
-- the DOM names of the named keys come back from their raw keys
#guard ["Enter", "Tab", "Backspace", "Delete", "Escape", "ArrowLeft", "ArrowUp", "ArrowRight", "ArrowDown",
  "Home", "End", "PageUp", "PageDown", "Shift", "Control", "Alt", "Meta", "F1", "F12", "Insert"].all fun k =>
  (ofDomKey k).map (fun c => (Keys.ofRaw c).key) == some k

end L4Factoidal.WebDriver.HostKeys
