/-
L4Factoidal.WebDriver.Errors: the error codes of WebDriver (W3C WebDriver §6.6, "Errors")
and the body of an error response.

Every command of the protocol that fails answers with one of these codes: its JSON error
code is the `error` member of the response body and its HTTP status is the response's
status. The table is the specification's.

Proved: `status_is_error` (every code answers with status 400, 404, 405 or 500: never a
success status), `name_injective` (two codes with one JSON error code are one code),
`ofName_name` (reading a JSON error code gives the code back), `body_error` (the body of
an error names its code).
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.WebDriver
open L4Factoidal.JSON

/-- The error codes of WebDriver §6.6. -/
inductive Code where
  | elementClickIntercepted | elementNotInteractable | insecureCertificate | invalidArgument
  | invalidCookieDomain | invalidElementState | invalidSelector | invalidSessionId
  | javascriptError | moveTargetOutOfBounds | noSuchAlert | noSuchCookie | noSuchElement
  | noSuchFrame | noSuchWindow | noSuchShadowRoot | scriptTimeout | sessionNotCreated
  | staleElementReference | detachedShadowRoot | timeout | unableToSetCookie
  | unableToCaptureScreen | unexpectedAlertOpen | unknownCommand | unknownError
  | unknownMethod | unsupportedOperation
  deriving DecidableEq, Repr, Inhabited

namespace Code

def all : List Code := [
  elementClickIntercepted, elementNotInteractable, insecureCertificate, invalidArgument,
  invalidCookieDomain, invalidElementState, invalidSelector, invalidSessionId,
  javascriptError, moveTargetOutOfBounds, noSuchAlert, noSuchCookie, noSuchElement,
  noSuchFrame, noSuchWindow, noSuchShadowRoot, scriptTimeout, sessionNotCreated,
  staleElementReference, detachedShadowRoot, timeout, unableToSetCookie,
  unableToCaptureScreen, unexpectedAlertOpen, unknownCommand, unknownError,
  unknownMethod, unsupportedOperation]

/-- The JSON error code. -/
def name : Code → String
  | elementClickIntercepted => "element click intercepted"
  | elementNotInteractable => "element not interactable"
  | insecureCertificate => "insecure certificate"
  | invalidArgument => "invalid argument"
  | invalidCookieDomain => "invalid cookie domain"
  | invalidElementState => "invalid element state"
  | invalidSelector => "invalid selector"
  | invalidSessionId => "invalid session id"
  | javascriptError => "javascript error"
  | moveTargetOutOfBounds => "move target out of bounds"
  | noSuchAlert => "no such alert"
  | noSuchCookie => "no such cookie"
  | noSuchElement => "no such element"
  | noSuchFrame => "no such frame"
  | noSuchWindow => "no such window"
  | noSuchShadowRoot => "no such shadow root"
  | scriptTimeout => "script timeout"
  | sessionNotCreated => "session not created"
  | staleElementReference => "stale element reference"
  | detachedShadowRoot => "detached shadow root"
  | timeout => "timeout"
  | unableToSetCookie => "unable to set cookie"
  | unableToCaptureScreen => "unable to capture screen"
  | unexpectedAlertOpen => "unexpected alert open"
  | unknownCommand => "unknown command"
  | unknownError => "unknown error"
  | unknownMethod => "unknown method"
  | unsupportedOperation => "unsupported operation"

/-- The HTTP status of a response with this error. -/
def status : Code → Nat
  | elementClickIntercepted | elementNotInteractable | insecureCertificate | invalidArgument
  | invalidCookieDomain | invalidElementState | invalidSelector => 400
  | invalidSessionId | noSuchAlert | noSuchCookie | noSuchElement | noSuchFrame | noSuchWindow
  | noSuchShadowRoot | staleElementReference | detachedShadowRoot | unknownCommand => 404
  | unknownMethod => 405
  | javascriptError | moveTargetOutOfBounds | scriptTimeout | sessionNotCreated | timeout
  | unableToSetCookie | unableToCaptureScreen | unexpectedAlertOpen | unknownError
  | unsupportedOperation => 500

/-- The code of a JSON error code. -/
def ofName (s : String) : Option Code := all.find? (·.name == s)

end Code

/-- An error of a command: its code, a message for a person, and optional data. -/
structure Error where
  code : Code
  message : String := ""
  data : Option Json := none
  deriving Repr, Inhabited

/-- The body of an error response (WebDriver §6.6 "send an error"): `value` with `error`,
`message`, `stacktrace` and, when there is some, `data`. -/
def Error.body (e : Error) : Json :=
  .object [("value", .object ([("error", .string e.code.name), ("message", .string e.message),
    ("stacktrace", .string "")] ++ (match e.data with | some d => [("data", d)] | none => [])))]

/-- The body of a successful response (§6.3 "send a response"): `value` with the data. -/
def successBody (value : Json) : Json := .object [("value", value)]

/-! ## Theorems -/

/-- Error statuses. Says: every error code answers with HTTP status 400, 404, 405 or 500,
so no error is sent with a success status. Does not say: that a command picks the right
code. -/
theorem Code.status_is_error (c : Code) :
    c.status = 400 ∨ c.status = 404 ∨ c.status = 405 ∨ c.status = 500 := by
  cases c <;> simp [Code.status]

/-- Complete list. Says: `Code.all` holds every code. Does not say: anything about order. -/
theorem Code.mem_all (c : Code) : c ∈ Code.all := by
  cases c <;> simp [Code.all]

/-- Distinct names. Says: the JSON error codes of `Code.all` are pairwise different, so a
client can tell every error from every other by its `error` string. Does not say: that
the strings match another implementation's (they are the specification's table). -/
theorem Code.names_nodup : (Code.all.map Code.name).Nodup := by decide

/-- Reading back. Says: the JSON error code of a code reads back as that code. Does not
say: what an unknown string reads as (`none`). -/
theorem Code.ofName_name (c : Code) : Code.ofName c.name = some c := by
  cases c <;> decide

/-- Injective names. Says: two codes with the same JSON error code are the same code.
Does not say: more than `names_nodup`; it is the form a caller uses. -/
theorem Code.name_injective (a b : Code) (h : a.name = b.name) : a = b := by
  have ha := Code.ofName_name a
  have hb := Code.ofName_name b
  rw [h] at ha
  rw [ha] at hb
  exact Option.some.inj hb

/-- Error body. Says: the body of an error response has `value.error` equal to the
code's JSON error code. Does not say: anything about the message text. -/
theorem Error.body_error (e : Error) :
    ((e.body.field? "value").bind (·.field? "error")) = some (.string e.code.name) := by
  simp [Error.body, Json.field?]

#guard Code.all.length == 28
#guard (Error.body { code := .noSuchElement, message := "x" }).toString ==
  "{\"value\":{\"error\":\"no such element\",\"message\":\"x\",\"stacktrace\":\"\"}}"
#guard Code.ofName "move target out of bounds" == some .moveTargetOutOfBounds
#guard Code.ofName "nope" == none

end L4Factoidal.WebDriver
