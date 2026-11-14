import L4Factoidal.JS.Str
import L4Factoidal.JSON.Parser

/-!
# L4Factoidal.JS.JsonText — the text that `JSON.parse` reads (ECMA-262 §25.5.1)

ECMAScript reads a JSON text as UTF-16 code units, so `"\uD800"` is a string of one lone
surrogate; RFC 8259's strict parser (`L4Factoidal.JSON.parseJsonText`) refuses a lone
surrogate escape. `jsonParseText` is the strict parse, and only when that fails the strict
parse of the text with its lone surrogate escapes written as BubblePopJS's characters for
those units (`Str.jsonLoneEscapes`). The second reading can only add texts: it never changes
the value of a text that the strict parser takes (`jsonParseText_strict`).
-/

namespace L4Factoidal.JS

/-- The value and end position of a JSON text as `JSON.parse` reads it, or the strict
parser's error (its position is the one a script sees). -/
def jsonParseText (s : String) : Except L4Factoidal.JSON.JsonError (L4Factoidal.JSON.Json × Nat) :=
  match L4Factoidal.JSON.parseJsonText s with
  | .ok r => .ok r
  | .error e =>
    match L4Factoidal.JSON.parseJsonText (Str.jsonLoneEscapes s) with
    | .ok r => .ok r
    | .error _ => .error e

/-- Kind: agreement with the specification parser. Says: on every text that RFC 8259's strict
parser accepts, `JSON.parse`'s reading is that parser's value, unchanged: the lone-surrogate
reading is consulted only for a text the strict parser refuses. Does not say: that
`Str.jsonLoneEscapes` leaves a strictly valid text unchanged (not needed: it is not run on
one), nor anything of the reviver or of `jsonToValue`. -/
theorem jsonParseText_strict (s : String) (r : L4Factoidal.JSON.Json × Nat)
    (h : L4Factoidal.JSON.parseJsonText s = .ok r) : jsonParseText s = .ok r := by
  simp [jsonParseText, h]

/-- Kind: agreement with the specification parser. Says: when `JSON.parse` refuses a text, the
strict parser refuses it too, with the same error, so the position in the `SyntaxError` is
the strict parser's. Does not say: that the escaped reading failed for the same reason. -/
theorem jsonParseText_error (s : String) (e : L4Factoidal.JSON.JsonError)
    (h : jsonParseText s = .error e) : L4Factoidal.JSON.parseJsonText s = .error e := by
  unfold jsonParseText at h
  split at h
  · simp at h
  · rename_i e' he
    split at h
    · simp at h
    · simp only [Except.error.injEq] at h
      rw [he, h]

end L4Factoidal.JS
