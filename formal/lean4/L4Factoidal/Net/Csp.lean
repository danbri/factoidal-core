/-
L4Factoidal.Net.Csp — Content Security Policy source lists (CSP Level 3,
https://w3c.github.io/webappsec-csp/): §2.3 source expressions, §6.7.2 "does url match
source list in origin" with its scheme, host, port and path rules, and the directive that
governs a kind of request with its fallback to `default-src` (§6.8).

## Status

This is the decision function. The engine does not yet enforce a page's policy (no request,
script or style is blocked by it): `allows` is not called by any host, and the design record
lists CSP enforcement as open. What a policy means is proved here first.

## What is proved

A source list is a set of permissions: adding a source expression never blocks a URL that
was allowed (`allows_mono_append`, `allows_mono_cons`); the empty list and `'none'` allow
nothing (`allows_nil`, `allows_none`); `'self'` allows the page's own origin (`self_allows_own`).
A wildcard host `*.example.com` does not match `example.com` itself (tested).
-/

namespace L4Factoidal.Net.Csp

/-- The parts of a URL that a source expression reads. -/
structure Url where
  scheme : String
  host : String
  port : Option Nat := none
  path : String := "/"
  deriving DecidableEq, Repr, Inhabited

/-- The port part of a host-source. -/
inductive PortPart where
  | absent
  | any
  | num (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A source expression (§2.3.1), as far as it names where a resource may come from. -/
inductive Source where
  /-- `'none'`: matches nothing. -/
  | none_
  /-- `'self'`. -/
  | self
  /-- `*`. -/
  | star
  /-- A scheme-source, without its colon: `https:`. -/
  | scheme (s : String)
  /-- A host-source: `[scheme://]host[:port][/path]`; `wild` for a host that starts `*.`
  (then `host` is the rest, with its leading dot). -/
  | host (scheme : Option String) (host : String) (wild : Bool) (port : PortPart) (path : Option String)
  deriving DecidableEq, Repr, Inhabited

/-- ASCII lower case. -/
def lower (s : String) : String :=
  s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The default port of a scheme. -/
def defaultPort (scheme : String) : Option Nat :=
  match scheme with
  | "http" | "ws" => some 80
  | "https" | "wss" => some 443
  | _ => none

/-- The port a URL connects to. -/
def Url.effectivePort (u : Url) : Option Nat := u.port.orElse fun _ => defaultPort u.scheme

/-- §6.7.2.9 "scheme-part matches": the same scheme, or the secure upgrade of it (`http`
allows `https`; `ws` allows `wss`, `http` and `https`; `wss` allows `https`). -/
def schemeMatches (expr scheme : String) : Bool :=
  let a := lower expr
  let b := lower scheme
  a == b || (a == "http" && b == "https") || (a == "ws" && (b == "wss" || b == "http" || b == "https")) ||
    (a == "wss" && b == "https")

/-- §6.7.2.10 "host-part matches": a wildcard matches only a proper subdomain; else the
hosts are equal, ASCII case-insensitively. -/
def hostMatches (pattern : String) (wild : Bool) (host : String) : Bool :=
  if wild then (lower host).endsWith (lower pattern) && (lower host).length > (lower pattern).length
  else lower pattern == lower host

/-- §6.7.2.11 "port-part matches". -/
def portMatches (p : PortPart) (u : Url) : Bool :=
  match p with
  | .any => true
  | .absent => u.port.isNone || u.port == defaultPort u.scheme
  | .num n => u.effectivePort == some n || (n == 80 && u.effectivePort == some 443 && (lower u.scheme == "https" || lower u.scheme == "wss"))

/-- §6.7.2.12 "path-part matches" (not asked after a redirect): no path matches every path; a
path that ends in `/` matches what it is a prefix of; another matches itself only. -/
def pathMatches (pattern : Option String) (path : String) : Bool :=
  match pattern with
  | none => true
  | some p => if p.isEmpty then true else if p.endsWith "/" then path.startsWith p else path == p

/-- §6.7.2.8 "does url match expression in origin": `origin` is the URL of the page the
policy protects; `redirected` when the request was redirected (the path is then not read). -/
def matchesSource (e : Source) (origin u : Url) (redirected : Bool := false) : Bool :=
  match e with
  | .none_ => false
  | .star => ["http", "https", "ws", "wss"].contains (lower u.scheme) || lower u.scheme == lower origin.scheme
  | .scheme s => schemeMatches s u.scheme
  | .self =>
    hostMatches origin.host false u.host &&
      (u.effectivePort == origin.effectivePort ||
        (origin.effectivePort == defaultPort origin.scheme && u.effectivePort == defaultPort u.scheme)) &&
      schemeMatches origin.scheme u.scheme
  | .host scheme host wild port path =>
    !u.host.isEmpty &&
      (match scheme with
       | some s => schemeMatches s u.scheme
       | none => schemeMatches origin.scheme u.scheme) &&
      hostMatches host wild u.host && portMatches port u && (redirected || pathMatches path u.path)

/-- §6.7.2.7 "does url match source list in origin": some expression matches. -/
def allows (list : List Source) (origin u : Url) (redirected : Bool := false) : Bool :=
  list.any fun e => matchesSource e origin u redirected

/-- The source list of the directive that governs `kind` (a directive name: `script-src`,
`img-src`, ...) in a policy of directives: its own, else `default-src`'s (§6.8); `none` when
the policy has neither (then the policy does not restrict that kind). -/
def governing (policy : List (String × List Source)) (kind : String) : Option (List Source) :=
  ((policy.find? fun d => d.1 == kind).orElse fun _ => policy.find? fun d => d.1 == "default-src").map (·.2)

/-- A request of `kind` to `u` passes a policy: no governing directive, or its list allows it. -/
def passes (policy : List (String × List Source)) (kind : String) (origin u : Url) (redirected : Bool := false) : Bool :=
  match governing policy kind with
  | none => true
  | some list => allows list origin u redirected

/-! ## Theorems -/

/-- Kind: policy theorem (monotone source lists). Says: adding source expressions after a
list never blocks a URL the list allowed. Does not say: anything of adding a directive or a
second policy, which can only restrict (CSP §4: every policy must pass). -/
theorem allows_mono_append (l m : List Source) (origin u : Url) (r : Bool)
    (h : allows l origin u r = true) : allows (l ++ m) origin u r = true := by
  unfold allows at *
  rw [List.any_append, h]
  rfl

/-- Kind: policy theorem (monotone source lists). Says: adding one source expression before
a list never blocks a URL the list allowed. -/
theorem allows_mono_cons (e : Source) (l : List Source) (origin u : Url) (r : Bool)
    (h : allows l origin u r = true) : allows (e :: l) origin u r = true := by
  unfold allows at *
  rw [List.any_cons, h]
  simp

/-- Kind: policy theorem. Says: the empty source list allows nothing. -/
theorem allows_nil (origin u : Url) (r : Bool) : allows [] origin u r = false := rfl

/-- Kind: policy theorem. Says: `'none'` allows nothing. -/
theorem allows_none (origin u : Url) (r : Bool) : allows [.none_] origin u r = false := by
  simp [allows, matchesSource]

/-- Kind: lemma. Says: every scheme matches itself. -/
theorem schemeMatches_refl (s : String) : schemeMatches s s = true := by
  simp [schemeMatches]

/-- Kind: policy theorem. Says: `'self'` allows every URL of the page's own scheme, host and
port, whatever its path. -/
theorem self_allows_own (origin u : Url) (r : Bool) (hs : u.scheme = origin.scheme)
    (hh : u.host = origin.host) (hp : u.port = origin.port) : allows [.self] origin u r = true := by
  simp [allows, matchesSource, hostMatches, Url.effectivePort, hs, hh, hp, schemeMatches_refl]

/-! ## Checks (CSP §6.7.2 and WPT content-security-policy/generic cases) -/

private def origin : Url := { scheme := "https", host := "example.com" }
private def u (s h : String) (port : Option Nat := none) (path : String := "/") : Url := { scheme := s, host := h, port, path }

#guard allows [.self] origin (u "https" "example.com" none "/a/b")
#guard !allows [.self] origin (u "https" "other.example")
#guard !allows [.self] origin (u "http" "example.com")
-- an http page's 'self' takes the https upgrade of itself
#guard allows [.self] { scheme := "http", host := "example.com" } (u "https" "example.com")
#guard allows [.star] origin (u "http" "x.test") && !allows [.star] origin (u "data" "")
#guard allows [.scheme "https"] origin (u "https" "x.test") && !allows [.scheme "https"] origin (u "http" "x.test")
#guard allows [.scheme "http"] origin (u "https" "x.test")
-- a wildcard host matches a proper subdomain only
#guard allows [.host none ".example.com" true .absent none] origin (u "https" "a.example.com")
#guard !allows [.host none ".example.com" true .absent none] origin (u "https" "example.com")
#guard !allows [.host none ".example.com" true .absent none] origin (u "https" "badexample.com")
-- host case, ports, paths
#guard allows [.host none "CDN.example" false .absent none] origin (u "https" "cdn.example")
#guard !allows [.host none "cdn.example" false .absent none] origin (u "https" "cdn.example" (some 8443))
#guard allows [.host none "cdn.example" false .any none] origin (u "https" "cdn.example" (some 8443))
#guard allows [.host (some "https") "cdn.example" false (.num 8443) (some "/js/")] origin (u "https" "cdn.example" (some 8443) "/js/a.js")
#guard !allows [.host (some "https") "cdn.example" false (.num 8443) (some "/js/")] origin (u "https" "cdn.example" (some 8443) "/css/a.css")
#guard allows [.host (some "https") "cdn.example" false (.num 8443) (some "/js/")] origin (u "https" "cdn.example" (some 8443) "/css/a.css") true
#guard !allows [.host none "cdn.example" false .absent (some "/a.js")] origin (u "https" "cdn.example" none "/a.js.map")
-- 'none' with another source: the other source still allows
#guard allows [.none_, .self] origin (u "https" "example.com")
-- the governing directive and its fallback
#guard passes [("default-src", [.self])] "script-src" origin (u "https" "example.com")
#guard !passes [("default-src", [.self])] "script-src" origin (u "https" "evil.test")
#guard passes [("default-src", [.none_]), ("img-src", [.star])] "img-src" origin (u "https" "evil.test")
#guard passes [("img-src", [.none_])] "script-src" origin (u "https" "evil.test")
#guard !passes [("style-src", [.none_])] "style-src" origin (u "https" "example.com")

end L4Factoidal.Net.Csp
