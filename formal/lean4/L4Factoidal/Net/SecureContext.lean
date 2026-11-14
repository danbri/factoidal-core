/-
Copyright (c) 2026 Dan Brickley. All rights reserved.
-/
import L4Factoidal.WHATWG.URL.Parser

/-!
# Secure contexts

Secure Contexts §3.1 "Is origin potentially trustworthy?" and §3.2 "Is url potentially
trustworthy?", and HTML's "secure context" for an environment whose top-level creation URL is
given. The engine asks this once per realm, when `crypto` is first used, to decide whether the
`[SecureContext]` members (`crypto.subtle`, `SubtleCrypto`, `CryptoKey`, `randomUUID`) exist.

Not modelled: the ancestor check of nested browsing contexts (a frame is judged by its own
URL), and user-agent configured trustworthy origins (there are none).
-/

namespace L4Factoidal.Net.SecureContext

open L4Factoidal.WHATWG.URL

/-- "localhost" or a name under ".localhost" (§3.1 step 4, the user agent follows
let-localhost-be-localhost), ASCII case-insensitive. -/
def localhostName (d : String) : Bool :=
  let t := d.toLower
  t == "localhost" || t.endsWith ".localhost"

/-- A loopback host: 127.0.0.0/8, ::1, or a localhost name (§3.1 steps 3 and 4). -/
def loopbackHost : Option Host → Bool
  | some (.ipv4 n) => n / 16777216 == 127
  | some (.ipv6 p) => p == #[0, 0, 0, 0, 0, 0, 0, 1]
  | some (.domain d) => localhostName d
  | _ => false

/-- §3.1 for the origin of a URL: `https`, `wss` and `file` are trustworthy; `http`, `ws` and
`ftp` only on a loopback host; any other scheme has an opaque origin and is not. -/
def originTrustworthy (u : Url) : Bool :=
  if u.scheme == "https" || u.scheme == "wss" || u.scheme == "file" then true
  else if u.scheme == "http" || u.scheme == "ws" || u.scheme == "ftp" then loopbackHost u.host
  else false

/-- The URL whose origin a `blob:` URL has (URL §4.7: the path, parsed, when its scheme is
`http`, `https` or `file`; otherwise the origin is opaque). -/
def blobInner (u : Url) : Option Url :=
  match u.path with
  | .opaque s =>
    match parseUrl s with
    | some v => if v.scheme == "http" || v.scheme == "https" || v.scheme == "file" then some v else none
    | none => none
  | .segments _ => none

/-- §3.2 "Is url potentially trustworthy?": `about:blank`, `about:srcdoc` and `data:` URLs are;
a `blob:` URL is when the origin it carries is; any other URL is when its origin is. -/
def urlTrustworthy (u : Url) : Bool :=
  if u.scheme == "about" then u.path == .opaque "blank" || u.path == .opaque "srcdoc"
  else if u.scheme == "data" then true
  else if u.scheme == "blob" then
    match blobInner u with
    | some v => originTrustworthy v
    | none => false
  else originTrustworthy u

/-- HTML "secure context" for an environment with this top-level creation URL (a string the
URL parser reads). A string that is not a URL is not a secure context. -/
def secureContext (input : String) : Bool :=
  match parseUrl input with
  | some u => urlTrustworthy u
  | none => false

/-- Kind: policy. Says: every `https` URL is potentially trustworthy, whatever its host,
port and path. Does not say: anything of the ancestors of a frame (not modelled). -/
theorem urlTrustworthy_https (u : Url) (h : u.scheme = "https") : urlTrustworthy u = true := by
  unfold urlTrustworthy originTrustworthy
  simp [h]

/-- Kind: policy (refusal). Says: an `http` URL whose host is not a loopback host is not
potentially trustworthy, so a page served from it gets no `[SecureContext]` member. Does not
say: which hosts are loopback (see `loopbackHost`). -/
theorem urlTrustworthy_http_remote (u : Url) (h : u.scheme = "http") (hl : loopbackHost u.host = false) :
    urlTrustworthy u = false := by
  unfold urlTrustworthy originTrustworthy
  simp [h, hl]

/-- Kind: totality of the refusal. Says: an input the URL parser rejects is never a secure
context. Does not say: anything of inputs it accepts. -/
theorem secureContext_unparsed (s : String) (h : parseUrl s = none) : secureContext s = false := by
  unfold secureContext; rw [h]

#guard secureContext "https://web-platform.test:8443/WebCryptoAPI/x.https.any.html"
#guard !secureContext "http://web-platform.test:8000/WebCryptoAPI/historical.any.html"
#guard secureContext "http://localhost:8000/"
#guard secureContext "http://foo.LOCALHOST/"
#guard secureContext "http://127.0.0.1/"
#guard secureContext "http://127.1.2.3/"
#guard !secureContext "http://128.0.0.1/"
#guard secureContext "http://[::1]/"
#guard secureContext "wss://example.org/"
#guard !secureContext "ws://example.org/"
#guard secureContext "file:///tmp/a.html"
#guard secureContext "about:blank"
#guard secureContext "about:srcdoc"
#guard !secureContext "about:foafnaut"
#guard secureContext "data:text/html,x"
#guard secureContext "blob:https://a.test/0e3f"
#guard !secureContext "blob:http://a.test/0e3f"
#guard !secureContext "javascript:void(0)"
#guard !secureContext "not a url"

end L4Factoidal.Net.SecureContext
