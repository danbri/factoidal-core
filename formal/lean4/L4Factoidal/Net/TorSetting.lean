/-
L4Factoidal.Net.TorSetting — the confirmation text of the Tor switch in Foafnaut's Settings
(https://github.com/danbri/factoidal-core/issues/1060).

Owner, 2026-11-26, verbatim, on whether Settings may offer Tor before expert review: "Make them
type lol-yolo-i-will-regret-this-folly capitalized in a text field as confirmation". So the
switch turns Tor mode on (`Net.PageFetch.Page.tor`) only when the text field holds exactly
`confirmText`: capital letters, the hyphens, no other character, no space before or after.
The host gives the field's text to `accepts` and uses its answer; it does not compare the text
itself.
-/

namespace L4Factoidal.Net.TorSetting

/-- The text a person types to turn Tor mode on. -/
def confirmText : String := "LOL-YOLO-I-WILL-REGRET-THIS-FOLLY"

/-- The text field's content turns Tor mode on. -/
def accepts (s : String) : Bool := s == confirmText

/-- Kind: security theorem (the Settings confirmation). Says: `accepts` is true of exactly one
text, `confirmText`; every other text (another case, an added space, a missing hyphen, the empty
field) leaves Tor mode off. Does not say: that Tor mode is safe to use, or that the host asks for
the text before it turns Tor on (the host is tested, not proved). -/
theorem accepts_iff (s : String) : accepts s = true ↔ s = confirmText := by
  simp [accepts]

#print axioms accepts_iff

#guard accepts "LOL-YOLO-I-WILL-REGRET-THIS-FOLLY"
#guard !accepts "lol-yolo-i-will-regret-this-folly"
#guard !accepts "Lol-Yolo-I-Will-Regret-This-Folly"
#guard !accepts "LOL-YOLO-I-WILL-REGRET-THIS-FOLLY "
#guard !accepts " LOL-YOLO-I-WILL-REGRET-THIS-FOLLY"
#guard !accepts "LOL-YOLO-I-WILL-REGRET-THIS FOLLY"
#guard !accepts "LOLYOLO-I-WILL-REGRET-THIS-FOLLY"
#guard !accepts ""

end L4Factoidal.Net.TorSetting
