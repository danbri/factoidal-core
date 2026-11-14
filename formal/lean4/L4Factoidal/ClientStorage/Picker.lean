/-
L4Factoidal.ClientStorage.Picker — the file pickers of the File System Access API
(WICG file-system-access: `showOpenFilePicker`, `showSaveFilePicker`, `showDirectoryPicker`):
the checks of their options, and the answer.

## Decisions

* **No host picker.** The engine never shows a host file dialog and never hands a page a
  handle to a host file or directory: every call is refused (`answer_refuses`,
  `answer_never_ok`). Host files are outside the persistence policy, which is not decided.
* **The order of the refusals is the standard's.** The options are checked first, so a
  malformed call is a `TypeError` whatever else holds: "process accept types" (each MIME type
  parses, by `WHATWG.MimeType.parse`, and has no parameters; each suffix is a valid suffix),
  an `excludeAcceptAllOption` with no accepted type, a `startIn` that is not a well-known
  directory or a handle, an `id` that is not a valid path id. A well-formed call is then
  refused with `SecurityError`: the engine records no transient activation, and showing a
  picker requires it (`valid_security`).

Commands (`web_api` op 201, command `picker`): the fields after the command are the
picker's kind (`open`, `save`, `directory`), `1` when `excludeAcceptAllOption` is true,
`startIn` (empty: absent; `h`: a handle; `w:` and the string given), `id` (empty: absent;
`i:` and the id), then the accepted types in order: `t` starts a type, `m:` and a MIME type
string, `e:` and a suffix. The answer is `!` and the exception's name.
-/
import L4Factoidal.WHATWG.MimeType

namespace L4Factoidal.ClientStorage.Picker

/-- The text after a two-character prefix such as `m:`, when the string has that prefix. -/
def after (pre : String) (s : String) : Option String :=
  if s.toList.take 2 == pre.toList then some (String.ofList (s.toList.drop 2)) else none

/-- A valid suffix code point: ASCII alphanumeric, `+` or `.`. -/
def isSuffixChar (c : Char) : Bool := c.toNat < 128 && (c.isAlphanum || c == '+' || c == '.')

/-- A valid suffix: starts with `.`, does not end with `.`, at most 16 code points, every one a
valid suffix code point. -/
def validSuffix (s : String) : Bool :=
  s.toList.head? == some '.' && s.toList.getLast? != some '.' && s.length ≤ 16 && s.toList.all isSuffixChar

/-- An accepted MIME type: it parses and has no parameters. -/
def validMime (s : String) : Bool :=
  match L4Factoidal.WHATWG.MimeType.parse s with
  | some m => m.params.isEmpty
  | none => false

/-- The well-known directories (`WellKnownDirectory`). -/
def wellKnown : List String := ["desktop", "documents", "downloads", "music", "pictures", "videos"]

/-- A valid path id: at most 32 code points, each ASCII alphanumeric, `_` or `-`. -/
def validId (s : String) : Bool :=
  s.length ≤ 32 && s.toList.all fun c => c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-')

/-- One field of the accepted types. -/
def itemOk (x : String) : Bool :=
  if x == "t" then true
  else match after "m:" x with
    | some m => validMime m
    | none => match after "e:" x with
      | some e => validSuffix e
      | none => false

def startInOk (x : String) : Bool :=
  x == "" || x == "h" || match after "w:" x with
    | some w => wellKnown.contains w
    | none => false

def idOk (x : String) : Bool :=
  x == "" || match after "i:" x with
    | some i => validId i
    | none => false

/-- Whether the options are well formed: the checks that answer `TypeError`. -/
def optionsOk (f : List String) : Bool :=
  let kind := f.getD 0 ""
  let items := f.drop 4
  let typesOk := kind == "directory" ||
    (items.all itemOk && !(f.getD 1 "" == "1" && !items.contains "t"))
  typesOk && startInOk (f.getD 2 "") && idOk (f.getD 3 "")

/-- The exception a picker call is refused with. -/
def check (f : List String) : String := if optionsOk f then "SecurityError" else "TypeError"

/-- The answer to the fields after `picker`: always `!` and an exception's name. -/
def answer (f : List String) : String := "!" ++ check f

/-! ## Theorems -/

/-- Kind: privacy policy. Says: a picker call is refused with `TypeError` or `SecurityError`,
whatever its fields. Does not say: which one (`valid_security`, `invalid_type`). -/
theorem answer_refuses (f : List String) :
    answer f = "!TypeError" ∨ answer f = "!SecurityError" := by
  unfold answer check; split <;> simp

/-- Kind: privacy policy. Says: no picker call answers `ok`: a page is never handed a host
file or directory. -/
theorem answer_never_ok (f : List String) : answer f ≠ "ok" := by
  rcases answer_refuses f with h | h <;> rw [h] <;> decide

/-- Kind: order of checks. Says: well-formed options are refused with `SecurityError` (no
transient activation is recorded). -/
theorem valid_security (f : List String) (h : optionsOk f = true) : check f = "SecurityError" := by
  simp [check, h]

/-- Kind: order of checks. Says: an open or save picker with a malformed accepted type is a
`TypeError`, whatever its `startIn` and `id`. -/
theorem invalid_type (f : List String) (hk : f.getD 0 "" ≠ "directory") (x : String)
    (hx : x ∈ f.drop 4) (hb : itemOk x = false) : check f = "TypeError" := by
  have hall : (f.drop 4).all itemOk = false := by
    rw [List.all_eq_false]; exact ⟨x, hx, by simp [hb]⟩
  have hk' : (f.getD 0 "" == "directory") = false := beq_eq_false_iff_ne.mpr hk
  have : optionsOk f = false := by
    simp only [optionsOk, hk', hall, Bool.false_or, Bool.false_and]
  simp [check, this]

/-- Kind: validity rule. Says: a valid suffix starts with `.` and has at most 16 code points. -/
theorem validSuffix_spec (s : String) (h : validSuffix s = true) :
    s.toList.head? = some '.' ∧ s.length ≤ 16 := by
  simp [validSuffix] at h
  exact ⟨h.1.1.1, h.1.2⟩

/-- Kind: validity rule. Says: a valid path id has at most 32 code points. -/
theorem validId_length (s : String) (h : validId s = true) : s.length ≤ 32 := by
  simp [validId] at h; exact h.1

/-! ## Checks (WPT file-system-access/showPicker-errors) -/

#guard check ["open", "0", "", ""] == "SecurityError"
#guard check ["save", "0", "", ""] == "SecurityError"
#guard check ["directory", "0", "", ""] == "SecurityError"
#guard check ["open", "1", "", ""] == "TypeError"
#guard check ["open", "0", "", "", "t", "m:text/plain", "e:.txt"] == "SecurityError"
#guard check ["open", "1", "", "", "t", "m:text/plain", "e:.txt", "e:.text"] == "SecurityError"
#guard ["", "  ", "image", "  /plain", "image/  ", "text/plain;charset=utf8", "text>foo/plain", "text / plain",
  "text/plain>foo"].all fun m => check ["save", "0", "", "", "t", "m:" ++ m, "e:.foo"] == "TypeError"
#guard check ["open", "0", "w:secrets", ""] == "TypeError"
#guard check ["open", "0", "w:", ""] == "TypeError"
#guard check ["open", "0", "w:null", ""] == "TypeError"
#guard check ["open", "0", "w:downloads", ""] == "SecurityError"
#guard check ["directory", "0", "h", "i:my_dir-2"] == "SecurityError"
#guard check ["open", "0", "", "i:inv*l:d\\ chara<ters"] == "TypeError"
#guard check ["open", "0", "", "i:id-length-cannot-exceed-32-characters"] == "TypeError"
#guard [".extensiontoolong", ".txt.", "txt", ".$txt", ".t<xt", ".t/xt", ".\txt", ".txt\\", ".txt?", ".txt*", ".{txt", ".}txt",
  " .txt", ". txt", ".txt ", ".‮txt‮", ".tæxt", ".קום", ".txt🙂", ".{txt}"].all fun e =>
  check ["open", "0", "", "", "t", "m:text/plain", "e:.txt", "e:" ++ e] == "TypeError"
#guard validSuffix ".tar.gz" && validSuffix ".c++" && validSuffix ".a"

end L4Factoidal.ClientStorage.Picker
