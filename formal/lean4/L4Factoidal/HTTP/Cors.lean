/-
L4Factoidal.HTTP.Cors — the server side of the CORS protocol of the Fetch
Standard, as a policy (which origins a server answers) and two total
functions over a request: `preflight?` (the answer to a CORS-preflight
request) and `decorate` (the CORS fields of every other answer).

A server instantiates it with a `Profile`: its methods, the request header
fields a preflight is answered for, and the response header fields a page may
read. LWS (`L4Factoidal.LWS.Cors`, https://github.com/danbri/factoidal/issues/923)
and the authorization server (`L4Factoidal.Authz.Server`) use it.

Source: Fetch Standard (https://fetch.spec.whatwg.org/), §3.2 "CORS protocol".

§3.2.2 "HTTP requests": "A CORS-preflight request is a CORS request that
checks to see if the CORS protocol is understood. It uses `OPTIONS` as method
and includes the following header: `Access-Control-Request-Method` [...]
`Access-Control-Request-Headers` [...]"

§3.2.3 "HTTP responses": "An HTTP response to a CORS request can include the
following headers: `Access-Control-Allow-Origin` [...]
`Access-Control-Allow-Credentials` [...]". "An HTTP response to a
CORS-preflight request can include the following headers:
`Access-Control-Allow-Methods` [...] `Access-Control-Allow-Headers` [...]
`Access-Control-Max-Age` [...]". "An HTTP response to a CORS request that is
not a CORS-preflight request can also include the following header:
`Access-Control-Expose-Headers` [...]"

§3.2.5 "CORS protocol and credentials": "When request's credentials mode is
"include" [...]". This server profile sends no
`Access-Control-Allow-Credentials` unless `Profile.credentials` says so: the
LWS and OAuth tokens travel in `Authorization`, which a page sends in mode
"same-origin" or "omit" once the preflight lists `Authorization`.

§3.2.6 "CORS protocol and HTTP caches": "if `Access-Control-Allow-Origin` is
set to * or a static origin for a particular resource, then configure the
server to always send `Access-Control-Allow-Origin` in responses for the
resource [...]. In all other cases, configure the server to [...] always
send `Vary: Origin`". So with CORS on, every answer carries `Vary: Origin`,
also one to a request with no `Origin`.

§4.8 "CORS-preflight fetch" step 7: "If a CORS check for request and
response returns success and response's status is an ok status, then"
[the preflight succeeds]. So a preflight answer is a 2xx: it is answered
before any authorization decision (a preflight carries no credentials,
§3.2.2 "includes no credentials"), and a server that asked a preflight to
authenticate would make every authenticated cross-origin request fail.

Origins: RFC 6454 §7.1 `origin = "Origin:" OWS origin-list-or-null OWS`,
§6.2 the ASCII serialization `scheme "://" host [ ":" port ]`, lowercase,
default port omitted. `validOrigin` checks that form. The value `null` (an
opaque origin, for example a sandboxed frame or a `file:` page) is answered
only when a configured list names it: echoing it would answer every opaque
origin at once.
-/
import L4Factoidal.HTTP.Server
import L4Factoidal.JSON.Value

namespace L4Factoidal.HTTP.Cors

open L4Factoidal.HTTP (Request Response)
open L4Factoidal.JSON

/-! ## Policy and profile -/

/-- Which origins a server answers with CORS fields. -/
inductive Policy where
  /-- No CORS fields at all; every request is answered as before. -/
  | off
  /-- Echo the request's `Origin` when it is a valid serialized origin (not
  `null`). Solid Protocol §8.1: "The server MUST set the
  Access-Control-Allow-Origin header field value to the valid Origin header
  field value from the request and list Origin in the Vary header field
  value." -/
  | echo
  /-- Echo the request's `Origin` only when it is one of these. -/
  | allow (origins : List String)
deriving Repr, BEq, Inhabited

/-- What a server says in its CORS fields. -/
structure Profile where
  /-- `Access-Control-Allow-Methods` of a preflight answer. -/
  methods : List String
  /-- `Access-Control-Allow-Headers` of a preflight answer. -/
  requestHeaders : List String
  /-- `Access-Control-Expose-Headers` of every other answer. -/
  exposedHeaders : List String
  /-- `Access-Control-Max-Age` of a preflight answer, in seconds. Chromium
  uses at most 7200. -/
  maxAge : Nat := 7200
  /-- Send `Access-Control-Allow-Credentials: true`. -/
  credentials : Bool := false
deriving Repr, Inhabited

/-! ## Origins -/

private def schemeChar (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '-' || c == '.'

/-- Characters of a host: a registered name (unreserved and percent), an
IPv4 literal, or an IPv6 literal in brackets (RFC 3986 §3.2.2). -/
private def hostChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '.' || c == '_' || c == '~' || c == '%'

private def ipv6Char (c : Char) : Bool :=
  c.isAlphanum || c == ':' || c == '.'

private def portOk (cs : List Char) : Bool :=
  !cs.isEmpty && cs.all Char.isDigit

/-- The authority part of a serialized origin: `host [ ":" port ]`. -/
private def authorityOk : List Char → Bool
  | '[' :: rest =>
      match rest.splitOn ']' with
      | [inner, after] =>
          !inner.isEmpty && inner.all ipv6Char &&
            (match after with
             | [] => true
             | ':' :: p => portOk p
             | _ => false)
      | _ => false
  | cs =>
      match cs.splitOn ':' with
      | [h] => !h.isEmpty && h.all hostChar
      | [h, p] => !h.isEmpty && h.all hostChar && portOk p
      | _ => false

/-- Is `s` the ASCII serialization of a tuple origin (RFC 6454 §6.2):
`scheme "://" host [ ":" port ]`, lowercase, with no path, query or
fragment? -/
def validOrigin (s : String) : Bool :=
  let cs := s.toList
  cs.all (fun c => !c.isUpper) &&
  (match s.splitOn "://" with
   | [scheme, auth] =>
       (match scheme.toList with
        | c :: rest => c.isAlpha && rest.all schemeChar
        | [] => false) &&
       authorityOk auth.toList
   | _ => false)

#guard validOrigin "https://danbri.github.io"
#guard validOrigin "http://localhost:3000"
#guard validOrigin "http://127.0.0.1:8080"
#guard validOrigin "http://[::1]:8080"
#guard validOrigin "http://[::1]"
#guard !validOrigin "null"
#guard !validOrigin "https://danbri.github.io/"
#guard !validOrigin "https://a.example/path"
#guard !validOrigin "https://A.example"
#guard !validOrigin "https://a.example:"
#guard !validOrigin "https://a.example:80x"
#guard !validOrigin "https://user@a.example"
#guard !validOrigin "https://"
#guard !validOrigin "a.example"
#guard !validOrigin "*"
#guard !validOrigin "https://a.example, https://b.example"

/-- Is a configured origin acceptable in a `Policy.allow` list: a valid
serialized origin, or `null`? -/
def configOrigin (s : String) : Bool := s == "null" || validOrigin s

/-- Does the policy answer this `Origin` value? -/
def originAllowed : Policy → String → Bool
  | .off, _ => false
  | .echo, o => validOrigin o
  | .allow os, o => os.contains o

#guard originAllowed .echo "https://danbri.github.io"
#guard !originAllowed .echo "null"
#guard !originAllowed .echo "https://evil.example/x"
#guard !originAllowed .off "https://danbri.github.io"
#guard originAllowed (.allow ["https://danbri.github.io"]) "https://danbri.github.io"
#guard !originAllowed (.allow ["https://danbri.github.io"]) "https://evil.example"
#guard originAllowed (.allow ["null"]) "null"

/-- The configuration member `cors`: absent or `true` echoes, `false` turns
CORS off, a non-empty list of serialized origins (or `null`) echoes those. -/
def policyOfJson : Option Json → Except String Policy
  | none | some (.bool true) => .ok .echo
  | some (.bool false) => .ok .off
  | some (.array xs) => do
      let os ← xs.mapM (fun x => match x with
        | .string o =>
            if configOrigin o then .ok o
            else .error s!"config: \"cors\": {o} is not a serialized origin (scheme://host[:port], lowercase, no path)"
        | _ => .error "config: \"cors\" lists strings")
      if os.isEmpty then .error "config: \"cors\" lists no origin; use false to turn CORS off"
      else .ok (.allow os)
  | some _ => .error "config: \"cors\" is true, false or a list of origins"

/-! ## Requests -/

/-- A CORS-preflight request (Fetch §3.2.2): `OPTIONS` with
`Access-Control-Request-Method` and `Origin`. An `OPTIONS` without them is an
ordinary request. -/
def isPreflight (r : Request) : Bool :=
  r.method == "OPTIONS" &&
    (r.header? "access-control-request-method").isSome &&
    (r.header? "origin").isSome

/-! ## Header fields -/

/-- Join every `Vary` field into one, with each listed field name once
(compared without case), in the order first seen, at the end of the list.
RFC 9110 §12.5.5 gives `Vary` a list value. -/
def mergeVary (hs : List (String × String)) : List (String × String) :=
  let names := (hs.filter (fun (k, _) => k == "vary")).flatMap (fun (_, v) =>
    (v.splitOn ",").map (fun x => x.trimAscii.toString) |>.filter (· != ""))
  let uniq := names.foldl (fun acc n =>
    if acc.any (fun m => m.toLower == n.toLower) then acc else acc ++ [n]) []
  match uniq with
  | [] => hs
  | _ => (hs.filter (fun (k, _) => k != "vary")) ++ [("vary", String.intercalate ", " uniq)]

#guard mergeVary [("vary", "accept"), ("etag", "x"), ("vary", "Origin")] ==
  [("etag", "x"), ("vary", "accept, Origin")]
#guard mergeVary [("vary", "accept, authorization"), ("vary", "Accept, Origin")] ==
  [("vary", "accept, authorization, Origin")]
#guard mergeVary [("etag", "x")] == [("etag", "x")]

private def credentialsField (pf : Profile) : List (String × String) :=
  if pf.credentials then [("access-control-allow-credentials", "true")] else []

/-- The CORS fields of an answer to a request from origin `o` that the
policy answers. -/
def originFields (pf : Profile) (o : String) : List (String × String) :=
  [ ("access-control-allow-origin", o)
  , ("access-control-expose-headers", String.intercalate ", " pf.exposedHeaders) ] ++
  credentialsField pf

/-- The answer to a CORS-preflight request from origin `o` that the policy
answers: 204 with the allowed methods, request header fields and lifetime. -/
def preflightAnswer (pf : Profile) (o : String) : Response :=
  ⟨204,
   [ ("access-control-allow-origin", o)
   , ("access-control-allow-methods", String.intercalate ", " pf.methods)
   , ("access-control-allow-headers", String.intercalate ", " pf.requestHeaders)
   , ("access-control-max-age", toString pf.maxAge) ] ++
   credentialsField pf ++
   [("vary", "Origin")],
   "", none⟩

/-- The answer to a CORS-preflight request from an origin the policy does
not answer: 204 with no CORS field, which the browser reads as a refusal
(Fetch §4.8: the CORS check fails without `Access-Control-Allow-Origin`). -/
def preflightRefused : Response := ⟨204, [("vary", "Origin")], "", none⟩

/-! ## The two functions -/

/-- The answer to a CORS-preflight request, before any other decision of the
server, or `none` when the request is not one (then the server steps it as
usual). With `Policy.off`, `none`: the server answers an `OPTIONS` as it
always did. -/
def preflight? (pf : Profile) (p : Policy) (r : Request) : Option Response :=
  match p with
  | .off => none
  | _ =>
      if isPreflight r then
        match r.header? "origin" with
        | some o => some (if originAllowed p o then preflightAnswer pf o else preflightRefused)
        | none => none
      else none

/-- Add the CORS fields to an answer: `Access-Control-Allow-Origin` and
`Access-Control-Expose-Headers` when the request's `Origin` is one the policy
answers, and `Vary: Origin` whenever the policy is on. Status and content are
unchanged. -/
def decorate (pf : Profile) (p : Policy) (r : Request) (resp : Response) : Response :=
  match p with
  | .off => resp
  | _ =>
      let extra := match r.header? "origin" with
        | some o => if originAllowed p o then originFields pf o else []
        | none => []
      { resp with headers := mergeVary (resp.headers ++ extra ++ [("vary", "Origin")]) }

/-- One request through a server step `f`: a CORS-preflight request is
answered by `preflight?` and `f` is not called; any other answer of `f` is
decorated. -/
def around {σ : Type} (pf : Profile) (p : Policy) (r : Request)
    (f : Request → σ → Response × σ) (st : σ) : Response × σ :=
  match preflight? pf p r with
  | some resp => (resp, st)
  | none => let (resp, st') := f r st; (decorate pf p r resp, st')

/-! ## Theorems -/

/-- `Policy.off` changes nothing. -/
theorem decorate_off (pf : Profile) (r : Request) (resp : Response) :
    decorate pf .off r resp = resp := rfl

theorem preflight?_off (pf : Profile) (r : Request) : preflight? pf .off r = none := rfl

/-- A request that is not a CORS-preflight request (for example an `OPTIONS`
with no `Access-Control-Request-Method`) is never answered by `preflight?`. -/
theorem preflight?_not_preflight (pf : Profile) (p : Policy) (r : Request)
    (h : isPreflight r = false) : preflight? pf p r = none := by
  cases p <;> simp [preflight?, h]

/-- Every preflight answer is 204, an ok status (Fetch §4.8 step 7). -/
theorem preflight?_status (pf : Profile) (p : Policy) (r : Request) (resp : Response)
    (h : preflight? pf p r = some resp) : resp.status = 204 := by
  unfold preflight? at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h
        subst h
        split <;> rfl
      · simp at h
    · simp at h

/-- A preflight from an origin the policy answers gets that origin in
`Access-Control-Allow-Origin`. -/
theorem preflight?_allowed (pf : Profile) (p : Policy) (r : Request) (o : String)
    (hp : isPreflight r = true) (ho : r.header? "origin" = some o)
    (ha : originAllowed p o = true) :
    preflight? pf p r = some (preflightAnswer pf o) := by
  cases p <;> simp_all [preflight?, originAllowed]

/-- `decorate` keeps status and content. -/
theorem decorate_status (pf : Profile) (p : Policy) (r : Request) (resp : Response) :
    (decorate pf p r resp).status = resp.status ∧
    (decorate pf p r resp).body = resp.body ∧
    (decorate pf p r resp).bytes = resp.bytes := by
  cases p <;> simp [decorate]

/-- A CORS-preflight request does not reach the server step: `around` gives
the same answer and the same state for every step function, so no
authorization decision inside a step is made for it. -/
theorem around_preflight {σ : Type} (pf : Profile) (p : Policy) (r : Request)
    (f g : Request → σ → Response × σ) (st : σ) (resp : Response)
    (h : preflight? pf p r = some resp) :
    around pf p r f st = (resp, st) ∧ around pf p r g st = (resp, st) := by
  simp [around, h]

/-- Any other request is the server step, decorated. -/
theorem around_step {σ : Type} (pf : Profile) (p : Policy) (r : Request)
    (f : Request → σ → Response × σ) (st : σ)
    (h : preflight? pf p r = none) :
    around pf p r f st = (decorate pf p r (f r st).1, (f r st).2) := by
  simp [around, h]

end L4Factoidal.HTTP.Cors
