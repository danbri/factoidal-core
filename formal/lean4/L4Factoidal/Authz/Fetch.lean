/-
L4Factoidal.Authz.Fetch — which documents the authorization server may
fetch, from which address, and what it remembers of them
(https://github.com/danbri/factoidal/issues/916).

Validating a subject token needs documents the server does not hold:
lws10-authn-ssi-cid "Authentication Credential Validation": "the verifier
MUST dereference the sub (subject) claim"; lws10-authn-openid
"Authentication Credential Validation": the same, then "The verifier MUST
perform OpenID Connect Discovery to locate the public portion of the JSON
Web Key (JWK) used to sign the authentication credential". The subject
chooses those URLs. So a request to the token endpoint can make this server
send a GET to an address of the requester's choice. The guard below is
this server's choice (coordinator decision, 2026-10-22): no draft defines
one.

## The rules

* A URL is `https`, or `http` only when `allowHttp` is set (off by default).
* Before any fetch the engine knows every address of the host. An IP
  literal is its own address; a name is resolved BY THE HOST (the engine
  answers `resolve`, the host passes back every address); a `localhost`
  name (RFC 6761 §6.3) is loopback whatever the resolution says.
* Unless `allowPrivateFetch` is set, a fetch is refused when ANY address is
  loopback (127.0.0.0/8, ::1), unspecified or "this network" (0.0.0.0/8,
  ::), link-local (169.254.0.0/16, fe80::/10), private (RFC 1918:
  10.0.0.0/8, 172.16.0.0/12, 192.168.0.0/16; RFC 4193: fc00::/7).
* The fetch answer names the address the host connects to, so the host
  does not resolve the name again (no second answer from a name server can
  move the request). The host does not follow redirects.
* Answers are kept for `docTtl` seconds, a failure too. At most
  `cacheMax` entries.

Address parsing is `L4Factoidal.LWS.InboxGuard` (`addr?`, `authority?`,
`localhostName`).
-/
import L4Factoidal.LWS.InboxGuard
import L4Factoidal.Crypto.CipherCall

namespace L4Factoidal.Authz

open L4Factoidal.LWS.InboxGuard (Addr addr? authority? localhostName)

/-! ## Addresses -/

/-- An address the guard refuses: loopback, unspecified or this network,
link-local, RFC 1918 private, RFC 4193 unique local. -/
def privateAddr : Addr → Bool
  | .v4 (a :: b :: _) =>
      a == 0 || a == 10 || a == 127 || (a == 169 && b == 254) ||
      (a == 172 && 16 ≤ b && b ≤ 31) || (a == 192 && b == 168)
  | .v4 _ => true
  | .v6 gs =>
      let g0 := gs.headD 0
      gs == [0, 0, 0, 0, 0, 0, 0, 1] || gs == [0, 0, 0, 0, 0, 0, 0, 0] ||
      (g0 / 64 == 0xfe80 / 64) || (g0 / 512 == 0xfc00 / 512)

/-- The fetch policy. -/
structure FetchPolicy where
  allowHttp : Bool := false
  allowPrivateFetch : Bool := false
  docTtl : Nat := 60
  cacheMax : Nat := 256

/-! ## What the engine asks the host -/

/-- A request to the host. -/
inductive Need where
  /-- Resolve this host name; pass every address back. -/
  | resolve (host : String)
  /-- GET this URL with this `Accept`, connecting to this address. -/
  | fetch (url accept address : String)
  /-- Run this one AES operation (WebCrypto on the host) and pass the bytes,
  or a refusal with no reason, back: an encrypted SAML assertion
  (https://github.com/danbri/factoidal/issues/1073,
  `L4Factoidal/Crypto/CipherCall.lean`). -/
  | cipher (req : L4Factoidal.Crypto.CipherCall.Req)
  deriving Repr, BEq, DecidableEq

/-- What is known of a document. -/
inductive DocResult where
  | body (text : String)
  | failed (why : String)
  deriving Repr, BEq, DecidableEq

structure DocEntry where
  url : String
  at_ : Nat
  result : DocResult

structure HostEntry where
  host : String
  at_ : Nat
  addresses : List String

/-- The cache of fetched documents and resolved names, newest first. -/
structure FetchState where
  docs : List DocEntry := []
  hosts : List HostEntry := []

/-- What a lookup gave. -/
inductive Got where
  | doc (text : String)
  | refused (why : String)
  | need (n : Need)
  deriving Repr, BEq, DecidableEq

def fresh (p : FetchPolicy) (now at_ : Nat) : Bool := decide (now < at_ + p.docTtl)

/-- The URL without its fragment: what is fetched. -/
def withoutFragment (u : String) : String := (u.splitOn "#").headD u

def schemeOf (u : String) : String := ((u.splitOn "://").headD "").toLower

/-- May the server connect to these addresses? -/
def addressesAllowed (p : FetchPolicy) (as : List Addr) : Bool :=
  p.allowPrivateFetch || !(as.any privateAddr)

/-- The decision for the addresses of a host: the address to connect to,
or the refusal. -/
def chooseAddress (p : FetchPolicy) (host : String) (texts : List String) :
    Except String String :=
  let parsed := texts.filterMap addr?
  if localhostName host && !p.allowPrivateFetch then
    .error s!"{host} is a localhost name; fetching it is refused (--allow-private-fetch)"
  else if parsed.isEmpty then .error s!"{host} did not resolve to an address"
  else if !addressesAllowed p parsed then
    .error s!"{host} resolves to a loopback, link-local or private address; fetching it is refused (--allow-private-fetch)"
  else match texts.find? (fun t => (addr? t).isSome) with
    | some a => .ok a
    | none => .error s!"{host} did not resolve to an address"

/-- The address texts of a host, when known: a literal, a localhost name,
or a fresh resolution. -/
def knownAddresses (p : FetchPolicy) (fs : FetchState) (now : Nat) (host : String) :
    Option (List String) :=
  match addr? host with
  | some _ =>
      some [if host.startsWith "[" then ((host.drop 1).dropEnd 1).toString else host]
  | none =>
      if localhostName host then some ["127.0.0.1"]
      else (fs.hosts.find? (fun e => e.host == host && fresh p now e.at_)).map (·.addresses)

/-- Look up a document; name what the host must do first when it is not
known. `refetchIfOlder` forces a new fetch of an entry at least that many
seconds old (a JWK Set that lacks the token's `kid`). -/
def lookup (p : FetchPolicy) (fs : FetchState) (now : Nat) (url0 accept : String)
    (refetchIfOlder : Option Nat := none) : Got :=
  let url := withoutFragment url0
  let sch := schemeOf url
  if !(sch == "https" || (sch == "http" && p.allowHttp)) then
    .refused s!"{url} is not an https URL{if sch == "http" then " (http needs --allow-http)" else ""}"
  else
    let cached := fs.docs.find? (fun e => e.url == url && fresh p now e.at_)
    let cached := match cached, refetchIfOlder with
      | some e, some age => if e.at_ + age ≤ now then none else some e
      | c, _ => c
    match cached with
    | some e => match e.result with
      | .body t => .doc t
      | .failed w => .refused w
    | none =>
        match authority? url with
        | none => .refused s!"{url} has no host"
        | some (host, _) =>
            match knownAddresses p fs now host with
            | none => .need (.resolve host)
            | some texts =>
                match chooseAddress p host texts with
                | .error w => .refused w
                | .ok a => .need (.fetch url accept a)

/-- Keep at most `n` entries. -/
def capList {α : Type} (n : Nat) (l : List α) : List α := l.take n

/-- Record a fetched document: a 200 answer is the body; any other status
is a failure. -/
def recordDoc (p : FetchPolicy) (fs : FetchState) (url : String) (status : Nat) (body : String)
    (now : Nat) : FetchState :=
  let url := withoutFragment url
  let r := if status == 200 then DocResult.body body
    else .failed s!"GET {url} answered {if status == 0 then "nothing" else toString status}"
  { fs with docs := capList p.cacheMax ({ url, at_ := now, result := r } ::
      fs.docs.filter (fun e => e.url != url)) }

/-- Record a resolution. -/
def recordHost (p : FetchPolicy) (fs : FetchState) (host : String) (addresses : List String)
    (now : Nat) : FetchState :=
  { fs with hosts := capList p.cacheMax ({ host, at_ := now, addresses } ::
      fs.hosts.filter (fun e => e.host != host)) }

/-! ## Theorems -/

/-- **The guard.** Without `allowPrivateFetch`, a host with a private
address among its addresses is never connected to. -/
theorem chooseAddress_refuses_private {p : FetchPolicy} {host : String} {texts : List String}
    {a : Addr} (hp : p.allowPrivateFetch = false) (ha : a ∈ texts.filterMap addr?)
    (hpriv : privateAddr a = true) (x : String) : chooseAddress p host texts ≠ .ok x := by
  unfold chooseAddress
  have hany : (texts.filterMap addr?).any privateAddr = true := List.any_eq_true.mpr ⟨a, ha, hpriv⟩
  simp only [hp]
  split
  · simp
  · split
    · simp
    · simp [addressesAllowed, hp, hany]

/-- Without `allowHttp`, an `http` URL is never fetched. -/
theorem lookup_http_refused {p : FetchPolicy} {fs : FetchState} {now : Nat} {url accept : String}
    {r : Option Nat} (hp : p.allowHttp = false) (hs : schemeOf (withoutFragment url) = "http")
    (u a ac : String) : lookup p fs now url accept r ≠ .need (.fetch u a ac) := by
  unfold lookup
  simp [hs, hp]

end L4Factoidal.Authz
