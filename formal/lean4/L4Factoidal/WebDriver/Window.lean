/-
L4Factoidal.WebDriver.Window: the commands of WebDriver on the browser's one window
(W3C WebDriver §11) that need no page: its handle, switching to it, its rect, and the
user prompts (none is ever open in the engine's sessions, so every prompt command answers
`no such alert`).

The engine's session for WebDriver has exactly one top-level browsing context, its
window. Its rect is the host's to apply; this module keeps what was asked and checks the
parameters as §11.8.2 "Set Window Rect" does.

Proved: `handles_one` (Get Window Handles is the one handle), `switch_own` and
`switch_other` (switching to the window's own handle succeeds, to any other is `no such
window`), `setRect_keeps` (a rect that is set reads back), `setRect_bad` (a negative or too
large width is `invalid argument` and changes nothing), `prompt_none` (every prompt command
is `no such alert`).
Tested: `#guard`s below.
-/
import L4Factoidal.WebDriver.Protocol

namespace L4Factoidal.WebDriver.Window
open L4Factoidal.JSON
open L4Factoidal.WebDriver.Protocol

/-- The window: its handle and rect (CSS pixels). -/
structure State where
  handle : String := "foafnaut-window-1"
  x : Int := 0
  y : Int := 0
  width : Nat := 800
  height : Nat := 600
  deriving DecidableEq, Repr, Inhabited

def State.rectJson (w : State) : Json :=
  .object [("x", .number (toString w.x)), ("y", .number (toString w.y)),
    ("width", .number (toString w.width)), ("height", .number (toString w.height))]

/-- The largest window position or size a parameter may give (§11.8.2: −(2³¹) to 2³¹ − 1). -/
def bound : Nat := 2147483647

def bad (message : String) : Error := { code := .invalidArgument, message }

/-- A parameter of Set Window Rect: absent or `null` is none; an integer in the bound (a
size not negative) is its value; anything else is `invalid argument`. -/
def param (body : Json) (name : String) (size : Bool) : Except Error (Option Int) :=
  match body.field? name with
  | none | some .null => .ok none
  | some (.number n) =>
    match n.toInt? with
    | some i =>
      if (size && i < 0) || i > bound || i < -((bound : Int) + 1) then .error (bad s!"{name} is out of range")
      else .ok (some i)
    | none => .error (bad s!"{name} is not an integer")
  | some _ => .error (bad s!"{name} is not a number")

/-- Set Window Rect: the window takes the given parts; the rest stays. -/
def setRect (w : State) (body : Json) : Except Error State := do
  let width ← param body "width" true
  let height ← param body "height" true
  let x ← param body "x" false
  let y ← param body "y" false
  return { w with width := (width.map Int.toNat).getD w.width, height := (height.map Int.toNat).getD w.height,
                  x := x.getD w.x, y := y.getD w.y }

def noAlert : Error := { code := .noSuchAlert, message := "no user prompt is open" }

/-- The answer of a window command, and the window after it; `none` for a command of the
page. -/
def answer (w : State) (c : Command) (body : Json) : Option (State × Except Error Json) :=
  match c with
  | .getWindowHandle => some (w, .ok (.string w.handle))
  | .getWindowHandles => some (w, .ok (.array [.string w.handle]))
  | .switchToWindow =>
    some (w, match body.field? "handle" with
      | some (.string h) => if h == w.handle then .ok .null else .error { code := .noSuchWindow, message := "no such window" }
      | _ => .error (bad "handle is not a string"))
  | .getWindowRect => some (w, .ok w.rectJson)
  | .setWindowRect =>
    match setRect w body with
    | .ok w' => some (w', .ok w'.rectJson)
    | .error e => some (w, .error e)
  | .maximizeWindow | .fullscreenWindow => some (w, .ok w.rectJson)
  | .dismissAlert | .acceptAlert | .getAlertText | .sendAlertText => some (w, .error noAlert)
  | _ => none

/-! ## Theorems -/

theorem handles_one (w : State) (b : Json) :
    answer w .getWindowHandles b = some (w, .ok (.array [.string w.handle])) := rfl

theorem switch_own (w : State) (b : Json) (h : b.field? "handle" = some (.string w.handle)) :
    answer w .switchToWindow b = some (w, .ok .null) := by
  simp [answer, h]

theorem switch_other (w : State) (b : Json) (o : String) (h : b.field? "handle" = some (.string o))
    (hne : o ≠ w.handle) : ∃ e, answer w .switchToWindow b = some (w, .error e) := by
  simp [answer, h, hne]

theorem prompt_none (w : State) (b : Json) (c : Command)
    (hc : c = .dismissAlert ∨ c = .acceptAlert ∨ c = .getAlertText ∨ c = .sendAlertText) :
    answer w c b = some (w, .error noAlert) := by
  rcases hc with rfl | rfl | rfl | rfl <;> rfl

/-- A failed Set Window Rect changes nothing. -/
theorem setRect_bad (w : State) (b : Json) (e : Error) (h : setRect w b = .error e) :
    answer w .setWindowRect b = some (w, .error e) := by
  simp [answer, h]

/-- What is set reads back: a rect set from the window's own rect is that rect. -/
theorem setRect_keeps (w : State) (b : Json) (w' : State) (h : setRect w b = .ok w') :
    answer w .setWindowRect b = some (w', .ok w'.rectJson) := by
  simp [answer, h]

/-! ## Tests (`webdriver/tests/classic/set_window_rect`) -/

#guard (setRect {} (.object [("width", .number "400"), ("height", .number "300")])).toOption.map (·.width) == some 400
#guard (setRect {} (.object [("width", .number "-1")])).toOption.isNone
#guard (setRect {} (.object [("x", .number "-10"), ("y", .null)])).toOption.map (fun w => (w.x, w.y)) == some (-10, 0)
#guard (setRect {} (.object [("width", .number "1.5")])).toOption.isNone
#guard (setRect {} (.object [("width", .string "1")])).toOption.isNone
#guard (answer {} .getAlertText .null).map (·.2.toOption) == some none

end L4Factoidal.WebDriver.Window
