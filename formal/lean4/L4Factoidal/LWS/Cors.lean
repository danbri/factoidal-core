/-
L4Factoidal.LWS.Cors — CORS in the LWS HTTP binding, so a page on another
origin (for example GitHub Pages) can call a storage directly
(https://github.com/danbri/factoidal/issues/923).

The LWS 1.0 core editor's draft says nothing about CORS. The Solid Protocol
§8.1 "CORS Server", the protocol LWS grew from, says:

  "A server MUST implement the CORS protocol [FETCH] such that browsers
  allow Solid apps to send any request and combination of request headers to
  the server, and allow the app to read any response and response headers
  received from the server."

  "The server MUST set the Access-Control-Allow-Origin header field value to
  the valid Origin header field value from the request and list Origin in
  the Vary header field value."

  "Servers SHOULD explicitly enumerate all used response header fields under
  Access-Control-Expose-Headers rather than resorting to *."

So the default policy echoes a valid request `Origin` (`Policy.echo`), and
the exposed fields are every field this binding writes that is not a
CORS-safelisted response-header name. Server choices, each a configuration
member of the wasm handle (`openConfigOfJson`):

* `"cors"` absent or `true`: echo. `false`: no CORS fields
  (`lws-serve --no-cors`). A list of serialized origins (`lws-serve
  --cors-origin ORIGIN`, repeatable): echo only those. Anything else stops
  the start (`policyOfJson`).
* No `Access-Control-Allow-Credentials`: the access token travels in
  `Authorization` (RFC 6750 §2.1), which the preflight lists, so a page sends
  it without credentials mode "include".
* A CORS-preflight request (`OPTIONS` with `Access-Control-Request-Method`
  and `Origin`) is answered first, with 204, before the body files are read,
  before the redirect table, before authentication and before Web Access
  Control: it carries no token (Fetch §3.2.2), and Fetch §4.8 needs an ok
  status. An `OPTIONS` without `Access-Control-Request-Method` is answered by
  `Operations.step` as before.

The functions are `L4Factoidal.HTTP.Cors` with the profile below; the wasm
layer (`Wasm/Ops/Lws.lean`, `lwsStepWith`) calls `preflight?` before any
other decision and `decorate` on every answer.
-/
import L4Factoidal.HTTP.Cors
import L4Factoidal.LWS.Operations
import L4Factoidal.LWS.Authorization

namespace L4Factoidal.LWS.Cors

open L4Factoidal.JSON
open L4Factoidal.HTTP (Request Response)
open L4Factoidal.HTTP.Cors (Policy Profile)

/-- The methods of the binding: the LWS operations, RFC 10008 `QUERY` (type
search), `PATCH` (JSON Patch, linksets). -/
def methods : List String :=
  ["GET", "HEAD", "OPTIONS", "POST", "PUT", "PATCH", "DELETE", "QUERY"]

/-- Request header fields a preflight is answered for: every field this
binding reads. `Accept` is listed, as Solid §8.1 says a server SHOULD do. -/
def requestHeaders : List String :=
  [ "Accept", "Authorization", "Content-Type", "DPoP", "If-Match"
  , "If-Modified-Since", "If-None-Match", "If-Unmodified-Since", "Link"
  , "Prefer", "Range", "Slug" ]

/-- Response header fields a page may read: every field the binding writes
that is not a CORS-safelisted response-header name (Fetch §2.2.6:
`Cache-Control`, `Content-Language`, `Content-Length`, `Content-Type`,
`Expires`, `Last-Modified`, `Pragma`). `Last-Modified` is listed too. -/
def exposedHeaders : List String :=
  [ "Accept-Patch", "Accept-Post", "Accept-Put", "Accept-Query", "Accept-Ranges"
  , "Allow", "Content-Location", "Content-Range", "ETag", "Factoidal-Merkle-Root"
  , "Last-Modified", "Link", "Location", "Preference-Applied", "Repr-Digest"
  , "WWW-Authenticate" ]

def profile : Profile :=
  { methods, requestHeaders, exposedHeaders, maxAge := 7200, credentials := false }

/-- The configuration member `cors` (`HTTP.Cors.policyOfJson`). -/
def policyOfJson : Option Json → Except String Policy := HTTP.Cors.policyOfJson

#guard (policyOfJson none).toOption == some .echo
#guard (policyOfJson (some (.bool true))).toOption == some .echo
#guard (policyOfJson (some (.bool false))).toOption == some .off
#guard (policyOfJson (some (.array [.string "https://danbri.github.io"]))).toOption ==
  some (.allow ["https://danbri.github.io"])
#guard (policyOfJson (some (.array [.string "https://danbri.github.io/"]))).toOption.isNone
#guard (policyOfJson (some (.array [.string "*"]))).toOption.isNone
#guard (policyOfJson (some (.array []))).toOption.isNone
#guard (policyOfJson (some (.string "https://danbri.github.io"))).toOption.isNone

/-- The answer to a CORS-preflight request under this storage's policy. -/
def preflight? (cfg : Config) (r : Request) : Option Response :=
  HTTP.Cors.preflight? profile cfg.cors r

/-- The CORS fields of any other answer. -/
def decorate (cfg : Config) (r : Request) (resp : Response) : Response :=
  HTTP.Cors.decorate profile cfg.cors r resp

/-! ## No credentials (invariant I7, https://github.com/danbri/factoidal/issues/1124)

The profile sends no `Access-Control-Allow-Credentials`, so an echoed or
listed origin never makes a browser send cookies or cached HTTP credentials
in a way that lets the page read the answer (Fetch §3.2.5). Before issue 1124
only the `#guard` below checked this. -/

theorem profile_no_credentials : profile.credentials = false := rfl

/-- `decorate` adds no `Access-Control-Allow-Credentials` field, under any
policy: such a field of the answer was in the step's own answer. -/
theorem decorate_no_credentials (cfg : Config) (r : Request) (resp : Response)
    (x : String × String) (hx : x ∈ (decorate cfg r resp).headers)
    (hk : x.1 = "access-control-allow-credentials") : x ∈ resp.headers :=
  HTTP.Cors.decorate_no_credentials profile rfl cfg.cors r resp x hx hk

/-- A preflight answer never carries `Access-Control-Allow-Credentials`. -/
theorem preflight_no_credentials (cfg : Config) (r : Request) (resp : Response)
    (h : preflight? cfg r = some resp) :
    ∀ x ∈ resp.headers, x.1 ≠ "access-control-allow-credentials" :=
  HTTP.Cors.preflight?_no_credentials profile rfl cfg.cors r resp h

/-! ## No echo without authorization (invariant I7)

With `insecureNoAuth` every request is served with no authorization, so an
echoed `Origin` would let any web page read and write the storage. The
configuration member `cors` is then read by `policyFor`: absent means no
CORS fields, a list names the origins, and `true` (echo) stops the start. -/

/-- The message when `cors: true` meets `insecureNoAuth`. -/
def insecureEchoRefusal : String :=
  "config: \"cors\": true (echo every Origin) is refused with \"insecureNoAuth\": " ++
  "any web page could read and write the storage; list the origins " ++
  "(--cors-origin ORIGIN) instead (https://github.com/danbri/factoidal/issues/1124)"

/-- The CORS policy of a storage: `policyOfJson` with authorization on; with
`insecureNoAuth`, absent is `.off` and echo is refused. -/
def policyFor (insecureNoAuth : Bool) (j : Option Json) : Except String Policy :=
  if insecureNoAuth then
    match j with
    | none => .ok .off
    | some _ =>
        match policyOfJson j with
        | .ok .echo => .error insecureEchoRefusal
        | .ok p => .ok p
        | .error e => .error e
  else policyOfJson j

/-- With `insecureNoAuth`, the policy is never echo. -/
theorem insecure_no_echo (j : Option Json) (p : Policy) (h : policyFor true j = .ok p) :
    p ≠ .echo := by
  intro hp
  subst hp
  unfold policyFor at h
  cases j with
  | none => simp at h
  | some v =>
      simp only [if_true] at h
      split at h <;> simp_all

#guard (policyFor true none).toOption == some .off
#guard (policyFor true (some (.bool true))).toOption.isNone
#guard (policyFor true (some (.bool false))).toOption == some .off
#guard (policyFor true (some (.array [.string "https://danbri.github.io"]))).toOption ==
  some (.allow ["https://danbri.github.io"])
#guard (policyFor false none).toOption == some .echo

/-! ## Checks through the authorized step

The storage is under authorization with no trusted issuer key, so every
request without a token is anonymous; the root has no ACL, so an anonymous
request is refused with 401. -/

section Checks

open L4Factoidal.LWS.Authorization

private def stubV : JOSE.Verifiers :=
  { es256 := fun _ _ _ => false, rs256 := fun _ _ _ _ => false, eddsa := fun _ _ _ => false }

private def st0 : MemState :=
  { entries := [{ path := "/", kind := .storageRoot, contentType := "text/turtle",
                  body := .empty, mtime := 1000 }], clock := 1001 }

private def page : String := "https://danbri.github.io"

private def cfgWith (p : Policy) : Config := { baseIri := "http://localhost/", cors := p }

/-- One request as the wasm layer runs it: the preflight first, then the
authorized step, then the CORS fields. -/
private def run (p : Policy) (r : Request) : Response :=
  let cfg := cfgWith p
  (HTTP.Cors.around profile cfg.cors r (fun r st =>
      match authorizedStep stubV MemStore cfg {} 1100 r st with
      | .inr x => x
      | .inl _ => (⟨599, [], "", none⟩, st)) st0).1

private def req (m : String) (hs : List (String × String)) : Request :=
  { method := m, path := "/", queryStr := "", headers := hs }

private def hdr (resp : Response) (k : String) : Option String := resp.headers.lookup k

private def preflightReq (o : String) : Request :=
  req "OPTIONS" [ ("origin", o), ("access-control-request-method", "PUT")
                , ("access-control-request-headers", "authorization, content-type, if-match") ]

-- A preflight with no token is 204, with every field, under authorization.
#guard (run .echo (preflightReq page)).status == 204
#guard hdr (run .echo (preflightReq page)) "access-control-allow-origin" == some page
#guard hdr (run .echo (preflightReq page)) "access-control-allow-methods" ==
  some "GET, HEAD, OPTIONS, POST, PUT, PATCH, DELETE, QUERY"
#guard ((hdr (run .echo (preflightReq page)) "access-control-allow-headers").getD "").splitOn ", " ==
  requestHeaders
#guard hdr (run .echo (preflightReq page)) "access-control-max-age" == some "7200"
#guard hdr (run .echo (preflightReq page)) "access-control-allow-credentials" == none
#guard hdr (run .echo (preflightReq page)) "vary" == some "Origin"
#guard hdr (run .echo (preflightReq page)) "www-authenticate" == none
-- The same with a configured list that names the page.
#guard hdr (run (.allow [page]) (preflightReq page)) "access-control-allow-origin" == some page
-- An origin not on the list: 204 with no CORS field, which the browser refuses.
#guard (run (.allow [page]) (preflightReq "https://evil.example")).status == 204
#guard hdr (run (.allow [page]) (preflightReq "https://evil.example")) "access-control-allow-origin" == none
-- `null` is not echoed.
#guard hdr (run .echo (preflightReq "null")) "access-control-allow-origin" == none
-- CORS off: the preflight is an ordinary OPTIONS, refused for want of a token.
#guard (run .off (preflightReq page)).status == 401
#guard hdr (run .off (preflightReq page)) "access-control-allow-origin" == none
#guard hdr (run .off (preflightReq page)) "vary" == none
-- An OPTIONS without Access-Control-Request-Method keeps today's behaviour
-- (here 401: no token), with the CORS fields added.
#guard (run .echo (req "OPTIONS" [("origin", page)])).status == 401
#guard hdr (run .echo (req "OPTIONS" [("origin", page)])) "access-control-allow-origin" == some page
-- A GET with no token: 401, the page may read WWW-Authenticate.
#guard (run .echo (req "GET" [("origin", page)])).status == 401
#guard (hdr (run .echo (req "GET" [("origin", page)])) "www-authenticate").isSome
#guard ((hdr (run .echo (req "GET" [("origin", page)])) "access-control-expose-headers").getD "").splitOn ", " ==
  exposedHeaders
#guard exposedHeaders.contains "WWW-Authenticate" && exposedHeaders.contains "ETag"
-- A request with no Origin gets Vary: Origin and no other CORS field.
#guard hdr (run .echo (req "GET" [])) "vary" == some "Origin"
#guard hdr (run .echo (req "GET" [])) "access-control-allow-origin" == none
-- CORS off changes nothing.
#guard hdr (run .off (req "GET" [("origin", page)])) "access-control-allow-origin" == none
#guard (run .off (req "GET" [("origin", page)])).headers ==
  (match authorizedStep stubV MemStore (cfgWith .off) {} 1100 (req "GET" [("origin", page)]) st0 with
   | .inr x => x.1.headers
   | .inl _ => [])

end Checks

/-! ## Checks through the open step

`insecureNoAuth`: a page reads and writes; `Vary` of a negotiated listing and
`Vary: Origin` are one field. -/

section OpenChecks

private def cfg : Config := { baseIri := "http://localhost/", cors := .echo }

private def stepC (r : Request) (st : MemState) : Response × MemState :=
  HTTP.Cors.around profile cfg.cors r (fun r st => step MemStore cfg r st) st

private def putR : Request :=
  { method := "PUT", path := "/a.txt", queryStr := "",
    headers := [("origin", page), ("content-type", "text/plain")], body := "hello" }

#guard (stepC putR st0).1.status == 201
#guard ((stepC putR st0).1.headers.lookup "access-control-allow-origin") == some page
-- The listing varies on Accept and on Origin, in one field.
#guard ((stepC { method := "GET", path := "/", queryStr := "", headers := [("origin", page)] }
          (stepC putR st0).2).1.headers.filter (·.1 == "vary")) ==
  [("vary", "accept, Origin")]
-- A write with If-Match of the current tag succeeds; the page reads ETag.
#guard
  let (r1, s1) := stepC putR st0
  let tag := (r1.headers.lookup "etag").getD ""
  let (r2, _) := stepC { putR with headers := putR.headers ++ [("if-match", tag)], body := "again" } s1
  tag != "" && r2.status == 204 && (r2.headers.lookup "access-control-allow-origin") == some page

end OpenChecks

end L4Factoidal.LWS.Cors
