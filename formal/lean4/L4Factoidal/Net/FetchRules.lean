/-
L4Factoidal.Net.FetchRules — the rules of the Fetch API's objects that are decisions, not
conversions (Fetch Standard, https://fetch.spec.whatwg.org/): what a `Headers` object keeps
(§5.1 "validate" after "normalize"), the method a `Request` may have (§5.4 step 25), and the
MIME type of a body (§5.3 "consume body" for `blob()`; `WHATWG.MimeType`). `web_api` ops 86
to 89. The prelude's `Headers`, `Request` and `Response` hold the JavaScript objects and ask
here; what is sent on the wire is decided again, in `Net.PageFetch` (`Transfer.mainWire`
drops forbidden fields whatever an object holds).

## Decisions

* A `Headers` object with the "request" guard never holds a forbidden request-header
  (`validate_request_keep`): a page cannot put `Cookie`, `Host`, `Origin`, `Referer`, a
  `Sec-` or `Proxy-` field, or a method override that names `CONNECT`, `TRACE` or `TRACK`
  on a `Request`. One with the "response" guard never holds `Set-Cookie`
  (`validate_response_keep`). An "immutable" one takes nothing (`validate_immutable`).
* A `Request` never has a forbidden method (`method_ok`).
-/
import L4Factoidal.Net.Xhr
import L4Factoidal.WHATWG.MimeType

namespace L4Factoidal.Net.FetchRules
open L4Factoidal.Net.PageFetch L4Factoidal.WHATWG

/-- A header name (Fetch §2.2.2): a non-empty token. -/
def validName (n : String) : Bool := !n.isEmpty && n.toList.all MimeType.isTokenChar

/-- "Normalize" a header value: without leading and trailing HTTP whitespace. -/
def normalize (v : String) : String := String.ofList (MimeType.trim v.toList)

/-- A header value (after `normalize`): bytes, with no NUL, line feed or carriage return. -/
def validValue (v : String) : Bool :=
  v.toList.all fun c => c.toNat ≤ 0xFF && c != '\x00' && c != '\n' && c != '\r'

/-- What `append` or `set` does with a field. -/
inductive Verdict where
  /-- `TypeError`: not a header name or value, or the object is immutable. -/
  | invalid
  /-- Dropped without an error (a forbidden field for this guard). -/
  | ignored
  /-- Kept, with the normalized value. -/
  | keep (value : String)
  deriving DecidableEq, Repr

/-- A no-CORS-safelisted request-header name (Fetch §2.2.2). -/
def noCorsName (n : String) : Bool :=
  ["accept", "accept-language", "content-language", "content-type"].contains (lower n)

/-- Fetch §5.1 "validate a header" after "normalize", for a `Headers` object whose guard is
`guard` ("none", "request", "request-no-cors", "response", "immutable"). With
"request-no-cors" the field must also be a no-CORS-safelisted request-header (the caller
gives the value combined with the one the object holds, as `append` requires);
"request-no-cors-name" is that guard's rule for `delete`, which reads the name only, and
"request-no-cors-combined" its rule for the value `append` would make of the one held and
the new one (`held, new`, not normalized: §5.1 "append" step 4). -/
def validate (guard name value : String) : Verdict :=
  if !validName name || !validValue (normalize value) then .invalid
  else if guard == "immutable" then .invalid
  else if guard == "request-no-cors-combined" then
    if noCorsName name && safeHeader name value then .keep value else .ignored
  else if (guard == "request" || guard == "request-no-cors" || guard == "request-no-cors-name") &&
      (forbiddenRequestHeader name || forbiddenOverride name (normalize value)) then .ignored
  else if guard == "request-no-cors" && !(noCorsName name && safeHeader name (normalize value)) then .ignored
  else if guard == "request-no-cors-name" && !(noCorsName name || lower name == "range") then .ignored
  else if guard == "response" && forbiddenResponseHeader name then .ignored
  else .keep (normalize value)

/-- The method of a `Request` (Fetch §5.4 step 25): a token that is not forbidden,
normalized; `none` is `TypeError`. -/
def method (m : String) : Option String :=
  if !L4Factoidal.Net.Xhr.isToken m || forbiddenMethod m then none
  else some (L4Factoidal.Net.Xhr.normalizeMethod m)

/-! ## The ops -/

/-- One field of a `web_api` call as a string. -/
def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

/-- `web_api` ops 86 to 89 (no state): 86 the MIME type of a combined `Content-Type` value,
serialized (`MimeType.extract`; -1 for failure); 87 `validate guard name value`: `"1"` and the normalized value, `"0"` for a field
dropped, -20 for `TypeError`; 88 a header name (-20 when it is not one); 89 a method,
normalized (-20 when it is not a token or is forbidden). -/
def op (code : Nat) (fs : Array ByteArray) : Except Int ByteArray :=
  match code with
  | 86 =>
    match MimeType.extractCanonical (strAt fs 0) with
    | some t => .ok t.toUTF8
    | none => .error (-1)
  | 87 =>
    match validate (strAt fs 0) (strAt fs 1) (strAt fs 2) with
    | .invalid => .error (-20)
    | .ignored => .ok "0".toUTF8
    | .keep v => .ok ("1" ++ v).toUTF8
  | 88 => if validName (strAt fs 0) then .ok ByteArray.empty else .error (-20)
  | 89 =>
    match method (strAt fs 0) with
    | some m => .ok m.toUTF8
    | none => .error (-20)
  | _ => .error (-2)

/-! ## Theorems -/

/-- Kind: security invariant (forbidden request-headers, Fetch §2.2.2). Says: a field that a
`Headers` object with the "request" guard keeps has a valid name, is not a forbidden
request-header name, and is not a method override that names a forbidden method. Does not
say: what the request sends (`Net.PageFetch.plan_wire_forbidden` says that of the wire). -/
theorem validate_request_keep (name value v : String) (h : validate "request" name value = .keep v) :
    validName name = true ∧ forbiddenRequestHeader name = false ∧ forbiddenOverride name v = false := by
  unfold validate at h
  by_cases h1 : (!validName name || !validValue (normalize value)) = true
  · simp [h1] at h
  · by_cases h2 : (forbiddenRequestHeader name || forbiddenOverride name (normalize value)) = true
    · simp [h1, h2] at h
    · simp [h1, h2] at h
      subst h
      simp at h1 h2
      exact ⟨h1.1, h2.1, h2.2⟩

/-- Kind: security invariant (forbidden response-header names). Says: a `Headers` object with
the "response" guard never keeps `Set-Cookie` or `Set-Cookie2`. -/
theorem validate_response_keep (name value v : String) (h : validate "response" name value = .keep v) :
    forbiddenResponseHeader name = false := by
  unfold validate at h
  by_cases h1 : (!validName name || !validValue (normalize value)) = true
  · simp [h1] at h
  · by_cases h2 : forbiddenResponseHeader name = true
    · simp [h1, h2] at h
    · simpa using h2

/-- Kind: invariant. Says: an immutable `Headers` object (a `fetch` response's) keeps
nothing new: every `append` and `set` is a `TypeError`. -/
theorem validate_immutable (name value : String) : validate "immutable" name value = .invalid := by
  unfold validate
  by_cases h1 : (!validName name || !validValue (normalize value)) = true
  · simp [h1]
  · simp [h1]

/-- Kind: security invariant (forbidden methods). Says: the method a `Request` gets is never
`CONNECT`, `TRACE` or `TRACK` in any case of letters, and is a token. -/
theorem method_ok (m r : String) (h : method m = some r) :
    forbiddenMethod m = false ∧ L4Factoidal.Net.Xhr.isToken m = true := by
  unfold method at h
  split at h
  · simp at h
  · rename_i hm
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hm
    exact ⟨hm.2, by simpa using hm.1⟩

/-! ## Checks (WPT fetch/api/headers and fetch/api/request cases) -/

#guard validate "none" "Content-Type" " text/html \t" == .keep "text/html"
#guard validate "none" "X-A" "a\nb" == .invalid
#guard validate "none" "X-A" "Ā" == .invalid
#guard validate "none" "invalid name" "v" == .invalid
#guard validate "none" "" "v" == .invalid
#guard validate "none" "Cookie" "a=b" == .keep "a=b"
#guard validate "request" "Cookie" "a=b" == .ignored
#guard validate "request" "sec-x" "1" == .ignored
#guard validate "request" "Proxy-Authorization" "1" == .ignored
#guard validate "request" "X-HTTP-Method-Override" "GET, trace" == .ignored
#guard validate "request" "X-HTTP-Method-Override" "GET" == .keep "GET"
#guard validate "request" "Set-Cookie" "a" == .ignored
#guard validate "response" "Set-Cookie" "a" == .ignored
#guard validate "response" "Cookie" "a" == .keep "a"
#guard validate "immutable" "X-A" "a" == .invalid
#guard validate "request-no-cors" "Accept" "text/html" == .keep "text/html"
#guard validate "request-no-cors" "Content-Type" "text/plain;charset=UTF-8" == .keep "text/plain;charset=UTF-8"
#guard validate "request-no-cors" "Content-Type" "text/html" == .ignored
#guard validate "request-no-cors" "X-Custom" "a" == .ignored
#guard validate "request-no-cors" "Cookie" "a" == .ignored
#guard validate "request-no-cors-name" "Content-Type" "" == .keep ""
#guard validate "request-no-cors-name" "Range" "" == .keep ""
#guard validate "request-no-cors-name" "X-Custom" "" == .ignored
#guard validate "request-no-cors-combined" "Accept" (String.ofList (List.replicate 127 's') ++ ", ") == .ignored
#guard validate "request-no-cors-combined" "Accept" "a, b" == .keep "a, b"
#guard method "get" == some "GET" && method "patch" == some "patch" && method "PATCH" == some "PATCH"
#guard method "TRACE" == none && method "connect" == none && method "a b" == none && method "" == none

end L4Factoidal.Net.FetchRules
