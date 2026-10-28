/-
L4Factoidal.HTTP.LocalGuard — the `Host` and `Origin` check of a listener
that has no authentication (https://github.com/danbri/factoidal/issues/1124;
row C7 and invariant I7 of
`docs/designissues/2026-10-28-feature-combination-safety.md`).

A listener with no authentication (`lws-serve --insecure-no-auth`,
`solid-serve --insecure-no-auth`, `webdav-serve` without `--users`,
`factoidal serve`) gives full access to every request that reaches it. A web
page that the user opens can send such requests in two ways:

1. DNS rebinding. A name of the attacker resolves first to the attacker's
   server and then to 127.0.0.1. The page is then same-origin with the
   listener, but its requests carry `Host: NAME:PORT` with the attacker's
   name. RFC 9110 §7.2: "The "Host" header field in a request provides the
   host and port information from the target URI". RFC 9110 §15.5.20: "The
   421 (Misdirected Request) status code indicates that the request was
   directed at a server that is unable or unwilling to produce an
   authoritative response for the target URI."  So a request whose `Host`
   names no name or address of this listener gets 421.
2. A cross-site request that changes state. A form POST or a `fetch` with
   mode "no-cors" is a CORS simple request (Fetch §3.2): the browser sends
   it with no preflight, and the page does not need to read the answer.
   Fetch §3.1 "`Origin` header": the browser sends `Origin` on every request
   whose method is neither GET nor HEAD. So a request with an unsafe method
   (RFC 9110 §9.2.1: GET, HEAD, OPTIONS and TRACE are safe; this guard
   counts only GET, HEAD and OPTIONS as safe) and an `Origin` that is not the
   listener's own origin and not on the configured list gets 403.

A request with no `Host` field does not come from a browser (every browser
sends one); the guard admits it, so that hosts which step requests with no
socket keep working. A request with no `Origin` (curl, a script, a
same-origin GET) is admitted by the origin check.

The names a listener answers: `localhost`, `127.0.0.1`, `[::1]`, the
address or name it was bound to, the addresses of its interfaces when bound
to every interface, the host of its base IRI, and the names the operator
gives (`--allow-host NAME`: a reverse proxy or Tailscale changes `Host`).
The check is on the name only. A rebinding attack needs a name of the
attacker, and the port of a `Host` field is the port the browser connected
to, so a name check is enough for (1).

The origins that may change state: the listener's own origin (an `Origin`
whose `host[:port]` equals the request's `Host`, with scheme http or https),
and the origins the operator gives (`--allow-origin ORIGIN`, and for
`lws-serve` every `--cors-origin ORIGIN`).
-/
import L4Factoidal.HTTP.Server
import L4Factoidal.HTTP.Cors
import L4Factoidal.JSON.Value

namespace L4Factoidal.HTTP.LocalGuard

open L4Factoidal.HTTP (Request Response)
open L4Factoidal.JSON

/-! ## Names -/

/-- A host name or address in the form a `Host` field carries it, without
the port: lowercase, an IPv6 address in brackets. -/
def normalizeName (s : String) : String :=
  let t := s.trimAscii.toString.toLower
  if t.startsWith "[" then t
  else if (t.toList.filter (· == ':')).length ≥ 2 then "[" ++ t ++ "]"
  else t

/-- The host part of a `Host` field value (RFC 9110 §7.2:
`uri-host [ ":" port ]`), normalized. -/
def hostName (v : String) : String :=
  let t := v.trimAscii.toString.toLower
  if t.startsWith "[" then
    match t.splitOn "]" with
    | inner :: _ => inner ++ "]"
    | [] => t
  else
    match t.splitOn ":" with
    | h :: _ => h
    | [] => t

#guard hostName "127.0.0.1:3000" == "127.0.0.1"
#guard hostName "LocalHost:8080" == "localhost"
#guard hostName "[::1]:3000" == "[::1]"
#guard hostName "[::1]" == "[::1]"
#guard hostName "evil.example" == "evil.example"
#guard normalizeName "::1" == "[::1]"
#guard normalizeName "[::1]" == "[::1]"
#guard normalizeName "Box.Tail1234.ts.net" == "box.tail1234.ts.net"

/-- The names every local listener answers. -/
def loopbackNames : List String := ["localhost", "127.0.0.1", "[::1]"]

/-! ## The guard -/

/-- The names and origins of one listener. -/
structure LocalGuard where
  /-- Normalized host names and addresses (`normalizeName`), no port. -/
  names : List String := loopbackNames
  /-- Serialized origins (RFC 6454 §6.2) that may send a request that
  changes state, besides the listener's own origin. -/
  origins : List String := []
deriving Repr, BEq, Inhabited

/-- Does the `Host` field value `v` name this listener? -/
def LocalGuard.hostAllowed (g : LocalGuard) (v : String) : Bool :=
  g.names.contains (hostName v)

/-- Safe methods for this guard: GET, HEAD and OPTIONS (RFC 9110 §9.2.1).
Every other method, also an extension method, is counted as unsafe. -/
def isSafe (method : String) : Bool :=
  method == "GET" || method == "HEAD" || method == "OPTIONS"

/-- Is the serialized origin `o` the listener's own origin, as the request's
`Host` field names it: scheme http or https, and `host[:port]` equal to the
`Host` value? -/
def sameOrigin (o : String) (host? : Option String) : Bool :=
  match host? with
  | none => false
  | some h =>
      match o.splitOn "://" with
      | [scheme, auth] =>
          (scheme == "http" || scheme == "https") && auth == h.trimAscii.toString.toLower
      | _ => false

#guard sameOrigin "http://127.0.0.1:3000" (some "127.0.0.1:3000")
#guard sameOrigin "http://localhost:3000" (some "LocalHost:3000")
#guard !sameOrigin "http://localhost:3000" (some "127.0.0.1:3000")
#guard !sameOrigin "https://evil.example" (some "127.0.0.1:3000")
#guard !sameOrigin "null" (some "127.0.0.1:3000")
#guard !sameOrigin "http://127.0.0.1:3000" none

/-- What the guard decides about one request. -/
inductive Verdict where
  | admit
  /-- The `Host` field names no name of this listener. -/
  | foreignHost (host : String)
  /-- An unsafe method from an origin that may not change state. -/
  | crossOrigin (origin : String)
deriving Repr, BEq, Inhabited

/-- The origin part of the decision, after the `Host` check. -/
def originVerdict (g : LocalGuard) (method : String) (host? origin? : Option String) : Verdict :=
  if isSafe method then .admit
  else match origin? with
    | none => .admit
    | some o => if sameOrigin o host? || g.origins.contains o then .admit else .crossOrigin o

/-- The decision for a request with this method and these `Host` and
`Origin` field values. -/
def verdict (g : LocalGuard) (method : String) (host? origin? : Option String) : Verdict :=
  match host? with
  | some h => if g.hostAllowed h then originVerdict g method host? origin? else .foreignHost h
  | none => originVerdict g method host? origin?

/-- 421 Misdirected Request (RFC 9110 §15.5.20). -/
def misdirected (host : String) : Response :=
  { status := 421, headers := [("content-type", "text/plain; charset=utf-8")],
    body := s!"Misdirected Request: Host \"{host}\" is not a name of this listener. " ++
      "A listener without authentication answers only its own names " ++
      "(https://github.com/danbri/factoidal/issues/1124); start it with " ++
      "--allow-host NAME to add a name.\n" }

/-- 403 Forbidden (RFC 9110 §15.5.4). -/
def forbidden (origin : String) : Response :=
  { status := 403, headers := [("content-type", "text/plain; charset=utf-8")],
    body := s!"Forbidden: a request that changes state from origin \"{origin}\" " ++
      "is refused on a listener without authentication " ++
      "(https://github.com/danbri/factoidal/issues/1124); start it with " ++
      "--allow-origin ORIGIN to accept that origin.\n" }

/-- The answer of the guard to a request it refuses, or `none` when the
listener may step the request. -/
def admit (g : LocalGuard) (r : Request) : Option Response :=
  match verdict g r.method (r.header? "host") (r.header? "origin") with
  | .admit => none
  | .foreignHost h => some (misdirected h)
  | .crossOrigin o => some (forbidden o)

/-- One request through a server step `f` behind an optional guard: a
refused request is answered by the guard and `f` is not called. -/
def guarded {σ : Type} (g : Option LocalGuard) (r : Request)
    (f : Request → σ → Response × σ) (st : σ) : Response × σ :=
  match g.bind (fun g => admit g r) with
  | some resp => (resp, st)
  | none => f r st

/-! ## Configuration -/

private def stringsOf (key : String) : Option Json → Except String (List String)
  | none | some .null => .ok []
  | some (.array xs) => xs.mapM (fun x => match x with
      | .string s => .ok s
      | _ => .error s!"config: \"{key}\" lists strings")
  | some _ => .error s!"config: \"{key}\" lists strings"

/-- Is `s` acceptable as an operator name (`--allow-host NAME`): not empty,
no space, slash, comma or `@`, and no port (one colon outside brackets)? -/
def configName (s : String) : Bool :=
  let t := s.trimAscii.toString
  !t.isEmpty &&
    t.toList.all (fun c => c != ' ' && c != '/' && c != ',' && c != '@') &&
    (t.startsWith "[" || (t.toList.filter (· == ':')).length != 1)

#guard configName "box.tail1234.ts.net"
#guard configName "::1"
#guard !configName "proxy.example:8080"
#guard !configName "http://proxy.example"
#guard !configName ""

/-- The guard of a listener from the configuration member `localGuard`:
`{host, addresses, allowHosts, allowOrigins}`, each optional. `host` is the
address or name given to bind (`--host`), `addresses` the addresses the
socket answers on (the interfaces when bound to every interface),
`allowHosts` and `allowOrigins` the operator's names and origins. `extra`
holds names the listener knows itself (the host of its base IRI) and
`extraOrigins` origins it accepts already (an LWS CORS list). A name or an
origin of the wrong form stops the start. -/
def ofJson (j : Json) (extra : List String := []) (extraOrigins : List String := []) :
    Except String LocalGuard := do
  let bind := match j.getString? "host" with
    | some h => [h]
    | none => []
  let addresses ← stringsOf "localGuard.addresses" (j.field? "addresses")
  let hosts ← stringsOf "allowHosts" (j.field? "allowHosts")
  match hosts.find? (fun h => !configName h) with
  | some h => throw s!"config: \"allowHosts\": {h} is not a host name or address (give it with no scheme, path or port)"
  | none => pure ()
  let origins ← stringsOf "allowOrigins" (j.field? "allowOrigins")
  match origins.find? (fun o => !Cors.configOrigin o) with
  | some o => throw s!"config: \"allowOrigins\": {o} is not a serialized origin (scheme://host[:port], lowercase, no path)"
  | none => pure ()
  let names := (loopbackNames ++ bind ++ addresses ++ extra ++ hosts).map normalizeName
    |>.filter (· != "")
  pure { names := names.eraseDups, origins := (origins ++ extraOrigins).eraseDups }

/-- The host part of an absolute http(s) IRI, normalized, when it has one. -/
def iriHost? (iri : String) : Option String :=
  match iri.splitOn "://" with
  | [_, rest] =>
      let auth := (rest.splitOn "/").headD ""
      let auth := (auth.splitOn "@").getLast?.getD auth
      if auth.isEmpty then none else some (hostName auth)
  | _ => none

#guard iriHost? "https://proxy.example/storage/" == some "proxy.example"
#guard iriHost? "http://127.0.0.1:3000/" == some "127.0.0.1"
#guard iriHost? "http://[::1]:3000/" == some "[::1]"
#guard iriHost? "urn:x" == none

/-! ## Theorems -/

/-- A request whose `Host` names no name of the listener gets 421, whatever
its method and `Origin`. -/
theorem localGuard_foreign_host (g : LocalGuard) (r : Request) (v : String)
    (hv : r.header? "host" = some v) (hn : g.hostAllowed v = false) :
    admit g r = some (misdirected v) := by
  simp [admit, verdict, hv, hn]

/-- A request with an unsafe method and an `Origin` that is neither the
listener's own origin nor on the list gets 403, when its `Host` (if any)
names the listener. -/
theorem localGuard_cross_origin_write (g : LocalGuard) (r : Request) (o : String)
    (hh : (r.header? "host").all g.hostAllowed = true)
    (hw : isSafe r.method = false) (ho : r.header? "origin" = some o)
    (hs : sameOrigin o (r.header? "host") = false) (hn : g.origins.contains o = false) :
    admit g r = some (forbidden o) := by
  have hn' : o ∉ g.origins := by simpa using hn
  unfold admit verdict
  cases hhost : r.header? "host" with
  | none =>
      rw [hhost] at hs
      simp [originVerdict, hw, ho, hs, hn']
  | some h =>
      rw [hhost] at hh hs
      simp at hh
      simp [hh, originVerdict, hw, ho, hs, hn']

/-- A request with a safe method whose `Host` names the listener (or that
has no `Host`) is admitted. -/
theorem localGuard_admits_safe (g : LocalGuard) (r : Request)
    (hh : (r.header? "host").all g.hostAllowed = true) (hs : isSafe r.method = true) :
    admit g r = none := by
  unfold admit verdict
  cases hhost : r.header? "host" with
  | none => simp [originVerdict, hs]
  | some h =>
      rw [hhost] at hh
      simp at hh
      simp [hh, originVerdict, hs]

/-- A request with no `Origin` whose `Host` names the listener (or that has
no `Host`) is admitted: curl and other clients that are not browsers keep
working. -/
theorem localGuard_admits_no_origin (g : LocalGuard) (r : Request)
    (hh : (r.header? "host").all g.hostAllowed = true) (ho : r.header? "origin" = none) :
    admit g r = none := by
  unfold admit verdict
  cases hhost : r.header? "host" with
  | none => simp [originVerdict, ho]
  | some h =>
      rw [hhost] at hh
      simp at hh
      simp [hh, originVerdict, ho]

/-- A request the guard refuses does not reach the server step: the state
is unchanged. -/
theorem guarded_refused_keeps_state {σ : Type} (g : LocalGuard) (r : Request)
    (f : Request → σ → Response × σ) (st : σ) (resp : Response)
    (h : admit g r = some resp) :
    guarded (some g) r f st = (resp, st) := by
  simp [guarded, h]

/-- With no guard, or a request the guard admits, the server step runs. -/
theorem guarded_admitted {σ : Type} (g : Option LocalGuard) (r : Request)
    (f : Request → σ → Response × σ) (st : σ)
    (h : g.bind (fun g => admit g r) = none) :
    guarded g r f st = f r st := by
  simp [guarded, h]

/-! ## Checks -/

private def g0 : LocalGuard :=
  match ofJson (.object [("host", .string "127.0.0.1")]) with
  | .ok g => g
  | .error _ => default

private def rq (m : String) (hs : List (String × String)) : Request :=
  { method := m, path := "/", queryStr := "", headers := hs }

#guard (admit g0 (rq "GET" [("host", "127.0.0.1:3000")])).isNone
#guard (admit g0 (rq "GET" [("host", "localhost:3000")])).isNone
#guard (admit g0 (rq "GET" [("host", "[::1]:3000")])).isNone
#guard ((admit g0 (rq "GET" [("host", "evil.example:3000")])).map (·.status)) == some 421
#guard ((admit g0 (rq "PUT" [("host", "evil.example:3000")])).map (·.status)) == some 421
-- A form POST from another site.
#guard ((admit g0 (rq "POST" [("host", "127.0.0.1:3030"), ("origin", "https://evil.example")])).map (·.status)) == some 403
-- The opaque origin of a sandboxed frame or a file: page.
#guard ((admit g0 (rq "DELETE" [("host", "127.0.0.1:3030"), ("origin", "null")])).map (·.status)) == some 403
-- Same origin, and curl with no Origin.
#guard (admit g0 (rq "POST" [("host", "127.0.0.1:3030"), ("origin", "http://127.0.0.1:3030")])).isNone
#guard (admit g0 (rq "POST" [("host", "127.0.0.1:3030")])).isNone
-- A cross-origin GET is admitted (a browser cannot read the answer without CORS).
#guard (admit g0 (rq "GET" [("host", "127.0.0.1:3030"), ("origin", "https://evil.example")])).isNone
-- No Host: no browser; admitted.
#guard (admit g0 (rq "PUT" [])).isNone
-- Operator names and origins.
#guard match ofJson (.object [("allowHosts", .array [.string "Box.ts.net"]),
                               ("allowOrigins", .array [.string "https://app.example"])]) with
  | .ok g => (admit g (rq "PUT" [("host", "box.ts.net"), ("origin", "https://app.example")])).isNone
  | .error _ => false
#guard (ofJson (.object [("allowHosts", .array [.string "proxy.example:8080"])])).toOption.isNone
#guard (ofJson (.object [("allowOrigins", .array [.string "https://app.example/"])])).toOption.isNone
-- The interfaces of a listener bound to every interface.
#guard match ofJson (.object [("host", .string "0.0.0.0"),
                               ("addresses", .array [.string "192.168.1.7", .string "fe80::1"])]) with
  | .ok g => (admit g (rq "GET" [("host", "192.168.1.7:3000")])).isNone &&
             (admit g (rq "GET" [("host", "[fe80::1]:3000")])).isNone &&
             (admit g (rq "GET" [("host", "evil.example")])).isSome
  | .error _ => false

end L4Factoidal.HTTP.LocalGuard
