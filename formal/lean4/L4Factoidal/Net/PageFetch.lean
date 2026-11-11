/-
L4Factoidal.Net.PageFetch — the network core of page scripts: what a page may ask for, the
requests the host is told to make, and what of an answer the page may see
(https://github.com/danbri/factoidal-core/issues/374; XMLHttpRequest is `Net.Xhr`).

The host moves bytes (Deno `fetch` natively, the browser's `fetch` on the Hub); every
decision is here, on values, so the same rules serve QuickJS-NG and BubblePopJS. Off unless
the embedder turns it on (`network:true` in `scriptSession start`). Source: Fetch Standard
(https://fetch.spec.whatwg.org/): §3.2 CORS protocol, §4.3 HTTP fetch, §4.4 HTTP-redirect
fetch, §4.8 CORS-preflight fetch, §4.9 CORS check; §2.2.2 header name lists.

## Decisions

* Schemes: `http` and `https` go to the host; a `data:` URL is answered here (Fetch §4.2,
  `dataResponse`), never by the host, and only as the first URL of a request (a redirect to
  it is a network error, Fetch §4.4 step 5; mode "same-origin" refuses it). A page never
  reads `file:`, `about:` or a host's other schemes (`mayConnect`).
* Local addresses: a target that is `localhost`, a `.localhost` name or a special-purpose
  IP literal (`Egress.specialPurpose`) is reached only by a page whose own origin is local.
  A page from the network or from `file:` gets no path to the machine it runs on. A page
  is local when its URL names a local address or when the host says it loaded the page
  from one (`Page.ofUrl`, `address`).
* DNS rebinding: for a page that is not local, on a native host, a request to a name goes
  to an address chosen here. The host first resolves the name (a `Wire` with `resolve`; no
  byte goes to the server) and answers every address it got; `Egress.choose` refuses the
  name when ANY of them is special-purpose, else names one; the request then carries that
  address (`Wire.address`) and the host connects to it without resolving again. The pin
  holds for every request of the transfer to that host (preflight, request, a redirect back
  to it); a redirect to another name resolves that name. `wireReach` is checked on every
  request just before it goes out (`emit`).
* Mixed content: an `https` page reads `https` only.
* Cross-origin: refused unless CORS allows it. A request outside the CORS-safelist has a
  preflight first (every hop); the response of a cross-origin request is withheld unless the
  CORS check passes; only the safelisted and exposed header fields reach the page.
* No credentials: no cookies, no HTTP authentication, no client certificates are ever sent
  (`Cookie`, `Authorization` set by the host never exist here). `withCredentials` changes
  only the CORS check, not what is sent. A URL's user and password are removed. An
  `Authorization` field the page set is removed on a redirect to another origin (Fetch
  §4.4 step 13), and a cross-origin redirect to a URL with credentials is a network error
  (step 11).
* A host cannot tell a page what a redirect does: redirects are the engine's (the host gets
  redirect "manual" natively, `Step.send` for each hop with the policy checked again).
* On the Hub (`hostCors`), the browser that runs the Hub enforces its own CORS for its
  own origin: the host follows redirects and preflights. The private-host and scheme rules
  still apply, to the first URL and to the final URL the host reports (a response whose
  final URL is outside the policy is withheld; the request was made by then). DNS is the
  Hub browser's: no pin there.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Net.Egress
import L4Factoidal.WHATWG.Base64

namespace L4Factoidal.Net.PageFetch
open L4Factoidal.WHATWG

/-- ASCII lower case (header names compare case-insensitively). -/
def lower (s : String) : String :=
  s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Trim ASCII whitespace (HTTP whitespace: tab, CR, LF, space). -/
def trimWs (s : String) : String :=
  s.trimAscii.toString

/-- The origin of a page or URL, serialized; `"null"` for an opaque origin. -/
abbrev Origin := String

/-- A special address by URL: `localhost`, `*.localhost`, or a special-purpose IP literal. -/
def privateHost (u : URL.Url) : Bool :=
  let h := lower u.hostname
  let h := if h.endsWith "." then (h.dropEnd 1).toString else h
  h == "localhost" || h.endsWith ".localhost" ||
    match addr? h with
    | some a => specialPurpose a
    | none => false

/-- What the engine knows of the page that asks (never what the page says of itself). -/
structure Page where
  /-- The page's origin (`"null"` for a `file:` or `about:` page). -/
  origin : Origin
  /-- The page was itself loaded from a local address. -/
  isLocal : Bool
  /-- The page was loaded over `https`. -/
  secure : Bool
  /-- The Hub: the browser that runs the Hub enforces CORS itself (this file's preflight and
  CORS check are off, the scheme and local rules are not). -/
  hostCors : Bool := false
  deriving Inhabited, Repr, DecidableEq

/-- The page from its URL. `address`: the address the host loaded an `http` or `https` page
from, when it knows it (`""` otherwise); a special-purpose one makes the page local. -/
def Page.ofUrl (url : String) (hostCors : Bool := false) (address : String := "") : Page :=
  let fromLocal := match addr? address with
    | some a => specialPurpose a
    | none => false
  match URL.parseUrl url with
  | some u => { origin := u.origin, secure := u.scheme == "https", hostCors,
                isLocal := privateHost u || (fromLocal && (u.scheme == "http" || u.scheme == "https")) }
  | none => { origin := "null", isLocal := false, secure := false, hostCors }

/-- May a page ask the host to connect to `u` at all. -/
def mayConnect (p : Page) (u : URL.Url) : Bool :=
  (u.scheme == "http" || u.scheme == "https") &&
    (!privateHost u || p.isLocal) &&
      (!p.secure || u.scheme == "https")

/-- The URL is same-origin with the page. -/
def sameOrigin (p : Page) (u : URL.Url) : Bool :=
  p.origin != "null" && u.origin == p.origin

/-! ## Header name lists (Fetch §2.2.2) -/

/-- A forbidden request-header name (lowercase): the page may not set it. -/
def forbiddenRequestHeader (name : String) : Bool :=
  let n := lower name
  n.startsWith "proxy-" || n.startsWith "sec-" ||
    ["accept-charset", "accept-encoding", "access-control-request-headers",
     "access-control-request-method", "access-control-request-private-network", "connection",
     "content-length", "cookie", "cookie2", "date", "dnt", "expect", "host", "keep-alive", "origin",
     "referer", "set-cookie", "te", "trailer", "transfer-encoding", "upgrade", "via"].contains n

/-- A forbidden method. -/
def forbiddenMethod (m : String) : Bool :=
  ["CONNECT", "TRACE", "TRACK"].contains m.toUpper

/-- A method-override field whose value names a forbidden method (Fetch §2.2.2, "forbidden
request-header": `X-HTTP-Method`, `X-HTTP-Method-Override`, `X-Method-Override`). -/
def forbiddenOverride (name value : String) : Bool :=
  ["x-http-method", "x-http-method-override", "x-method-override"].contains (lower name) &&
    (value.splitOn ",").any fun m => forbiddenMethod (trimWs m)

/-- A CORS-safelisted method. -/
def safeMethod (m : String) : Bool := m == "GET" || m == "HEAD" || m == "POST"

/-- A byte of a CORS-unsafe request-header value (Fetch §3.2.1). -/
def unsafeByte (c : Char) : Bool :=
  (c.toNat < 0x20 && c != '\t') || c.toNat == 0x7f || c == '"' || c == '(' || c == ')' || c == ':' ||
    c == '<' || c == '>' || c == '?' || c == '@' || c == '[' || c == '\\' || c == ']' || c == '{' || c == '}'

/-- `Content-Type` value's essence is one of the three the CORS-safelist allows. -/
def safeContentType (v : String) : Bool :=
  let essence := lower (trimWs ((v.splitOn ";").headD ""))
  ["application/x-www-form-urlencoded", "multipart/form-data", "text/plain"].contains essence

/-- A simple `bytes=` range value. -/
def safeRange (v : String) : Bool :=
  let v := lower v
  v.startsWith "bytes=" &&
    let rest := (v.drop 6).toString
    match rest.splitOn "-" with
    | [a, b] => !a.isEmpty && a.all Char.isDigit && b.all Char.isDigit && !b.contains ',' 
    | _ => false

/-- Is one header in the CORS-safelist (Fetch §3.2.1, "CORS-safelisted request-header"). -/
def safeHeader (name value : String) : Bool :=
  value.length ≤ 128 &&
  match lower name with
  | "accept" => value.all (!unsafeByte ·)
  | "accept-language" | "content-language" =>
    value.all fun c => c.isAlphanum || c == ' ' || c == '*' || c == ',' || c == '-' || c == '.' || c == ';' || c == '='
  | "content-type" => value.all (!unsafeByte ·) && safeContentType value
  | "range" => safeRange value
  | _ => false

/-- The author's unsafe header names, lowercased and sorted, each once (Fetch §4.8 step 6). -/
def unsafeHeaderNames (hs : List (String × String)) : List String :=
  let names := (hs.filter fun (n, v) => !safeHeader n v).map (lower ·.1)
  (names.eraseDups.toArray.qsort (· < ·)).toList

/-! ## Requests and answers -/

/-- One request the host is told to make: it moves these bytes and hides nothing else. The
response body comes back as the answer. -/
structure Wire where
  id : Nat
  method : String
  url : String
  headers : List (String × String)
  body : Option ByteArray
  /-- Resolve only: the host resolves the URL's host name and answers `Answer.addresses`;
  nothing is sent to the server. -/
  resolve : Bool := false
  /-- The address to connect to for the URL's host, with `port`; the host does not resolve
  the name again. `""`: the host connects as it does (an IP literal, a local page, the Hub). -/
  address : String := ""
  port : Nat := 0
  deriving Inhabited

/-- The host's answer to a `Wire`: `status` 0 is a network failure. -/
structure Answer where
  status : Nat := 0
  statusText : String := ""
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
  /-- The final URL when the host followed redirects itself (the Hub). -/
  url : String := ""
  /-- The answer to a resolve-only `Wire`: every address the host's resolver gave. -/
  addresses : List String := []
  deriving Inhabited

/-- A response the page may read. -/
structure Response where
  status : Nat
  statusText : String
  url : String
  headers : List (String × String)
  body : ByteArray
  deriving Inhabited

/-! ## `data:` URLs (Fetch §4.2 scheme fetch, "data: URL processor") -/

/-- A token character (RFC 9110 §5.6.2). -/
def tchar (c : Char) : Bool := c.isAlphanum || "!#$%&'*+-.^_`|~".contains c

/-- The MIME type of a `data:` URL, serialized: type and subtype lowercased, each parameter
`name=value` with a token name (lowercased); `text/plain;charset=US-ASCII` when the type is
not `token/token` (MIME Sniffing §4.4, reduced: quoted values are kept as written). -/
def dataMime (m : String) : String :=
  let dflt := "text/plain;charset=US-ASCII"
  match m.splitOn ";" with
  | [] => dflt
  | e :: ps =>
    match (trimWs e).splitOn "/" with
    | [ty, sub] =>
      let sub := trimWs sub
      if ty.isEmpty || sub.isEmpty || !ty.all tchar || !sub.all tchar then dflt else
      let params := ps.filterMap fun p =>
        match (trimWs p).splitOn "=" with
        | n :: v :: more =>
          let n := lower n
          let v := "=".intercalate (v :: more)
          if n.isEmpty || !n.all tchar || v.isEmpty then none else some (n ++ "=" ++ v)
        | _ => none
      ";".intercalate ((lower ty ++ "/" ++ lower sub) :: params)
    | _ => dflt

/-- Bytes as a string of the code points 0 to 255 (isomorphic decode). -/
def isoString (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

/-- ASCII whitespace removed from the end. -/
def trimEnd (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0c')).reverse

/-- The response of a `data:` URL (Fetch §4.2: status 200 "OK", `Content-Type` the URL's
MIME type), `none` when the URL is not one or its base64 body does not decode. -/
def dataResponse (url : String) : Option (String × ByteArray) :=
  if !url.startsWith "data:" then none else
  let input := ((url.drop 5).toString.splitOn "#").headD ""
  match input.splitOn "," with
  | [] | [_] => none
  | m :: rest =>
    let mime := trimWs m
    let body := URL.percentDecode (",".intercalate rest).toUTF8
    let cut := trimEnd (mime.dropEnd 6).toString
    let b64 := (lower mime).endsWith "base64" && cut.endsWith ";"
    let mime := if b64 then trimEnd (cut.dropEnd 1).toString else mime
    let bytes := if b64 then WHATWG.Base64.decode (isoString body) else some body
    bytes.map fun b => (dataMime (if mime.startsWith ";" then "text/plain" ++ mime else mime), b)

inductive Phase where
  | preflight
  | main
  /-- The host resolves the current URL's name; the request is planned again with the pin. -/
  | resolve
  deriving DecidableEq, Repr, Inhabited

/-- One request in progress: it follows one page request over its redirects. -/
structure Transfer where
  id : Nat
  page : Page
  method : String
  /-- The current URL, serialized: what `Wire.url` carries, so the policy reads the same
  string the host fetches. -/
  url : String
  headers : List (String × String)
  body : Option ByteArray
  credentials : Bool := false
  redirects : Nat := 0
  /-- Tainted: the request crossed origins on a redirect, so its origin is `null` (Fetch §4.4). -/
  crossed : Bool := false
  phase : Phase := .main
  /-- Fetch mode "same-origin": a request that leaves the page's origin is refused. -/
  sameOriginOnly : Bool := false
  /-- The host name (lowercase) and the address chosen for it (`Egress.choose`). -/
  pin : Option (String × String) := none
  deriving Inhabited

/-- The header `name` of a field list (`none` when absent). -/
def headerGet (hs : List (String × String)) (name : String) : Option String :=
  (hs.find? fun (n, _) => lower n == name).map (·.2)

/-- The `Origin` this request carries. -/
def Transfer.originValue (t : Transfer) : Origin :=
  if t.crossed then "null" else t.page.origin

/-- Is the current URL same-origin with the page (a request that crossed origins never is). -/
def Transfer.same (t : Transfer) : Bool :=
  !t.crossed && match URL.parseUrl t.url with
    | some u => sameOrigin t.page u
    | none => false

/-- Is the current URL inside the policy. -/
def Transfer.allowed (t : Transfer) : Bool :=
  match URL.parseUrl t.url with
  | some u => mayConnect t.page u
  | none => false

/-- A preflight is needed: Fetch §4.1 main fetch step 12. -/
def Transfer.needsPreflight (t : Transfer) : Bool :=
  !safeMethod t.method || (t.headers.any fun (n, v) => !safeHeader n v) ||
    (t.headers.foldl (fun s (_, v) => s + v.length) 0) > 1024

/-- The CORS check (Fetch §4.9). -/
def corsOk (t : Transfer) (a : Answer) : Bool :=
  match headerGet a.headers "access-control-allow-origin" with
  | none => false
  | some v =>
    let v := trimWs v
    if t.credentials then
      v == t.originValue && (headerGet a.headers "access-control-allow-credentials").map trimWs == some "true"
    else v == "*" || v == t.originValue

/-- The names of a list header value (split on commas, trimmed). -/
def listValue (v : Option String) : List String :=
  match v with
  | none => []
  | some s => (s.splitOn ",").map trimWs

/-- A preflight answer allows this request (Fetch §4.8 steps 7.3 to 7.8). -/
def preflightOk (t : Transfer) (a : Answer) : Bool :=
  corsOk t a && (200 ≤ a.status && a.status < 300) &&
    let methods := listValue (headerGet a.headers "access-control-allow-methods")
    let names := (listValue (headerGet a.headers "access-control-allow-headers")).map lower
    let methodOk := safeMethod t.method || methods.contains t.method || (methods.contains "*" && !t.credentials)
    let star := names.contains "*" && !t.credentials
    let unsafeNames := unsafeHeaderNames t.headers
    methodOk && unsafeNames.all fun n => names.contains n || (star && n != "authorization")

/-- The wire form of the request, with `Origin` (Fetch §4.3 "append a request `Origin`
header"): every cross-origin request and every same-origin one that is not `GET` or `HEAD`. -/
def Transfer.mainWire (t : Transfer) : Wire :=
  let h := t.headers.filter fun (n, _) => !forbiddenRequestHeader n
  let h := if !t.same || !(t.method == "GET" || t.method == "HEAD") then h ++ [("Origin", t.originValue)] else h
  { id := t.id, method := t.method, url := t.url, headers := h, body := t.body }

/-- The CORS-preflight request (Fetch §4.8: `OPTIONS`, `Origin`, the method and the unsafe
names; no body, no author headers). -/
def Transfer.preflightWire (t : Transfer) : Wire :=
  let names := unsafeHeaderNames t.headers
  let h : List (String × String) :=
    [("Accept", "*/*"), ("Origin", t.originValue), ("Access-Control-Request-Method", t.method)] ++
      (if names.isEmpty then [] else [("Access-Control-Request-Headers", ",".intercalate names)])
  { id := t.id, method := "OPTIONS", url := t.url, headers := h, body := none }

/-- The name the host must resolve before a request to the current URL: its host when that is
a name (not an IP literal), for a page that is not local, on a native host. -/
def Transfer.toResolve (t : Transfer) : Option String :=
  if t.page.hostCors || t.page.isLocal then none else
  match URL.parseUrl t.url with
  | some u =>
    let h := lower u.hostname
    if (addr? h).isSome then none else some h
  | none => none

/-- The address chosen for `host` in this transfer. -/
def Transfer.pinned (t : Transfer) (host : String) : Option String :=
  match t.pin with
  | some (h, a) => if h == host then some a else none
  | none => none

/-- The port of the current URL (its scheme's default when it has none). -/
def Transfer.portOf (t : Transfer) : Nat :=
  match URL.parseUrl t.url with
  | some u => u.port.getD ((URL.defaultPort u.scheme).getD 0)
  | none => 0

/-- The address rule of a request the host makes. A resolve-only wire sends nothing to a
server. Otherwise, for a page that is not local on a native host, the URL's host is an IP
literal that is not special-purpose, or the wire names the address the host connects to, and
that address is not special-purpose. -/
def wireReach (p : Page) (w : Wire) : Bool :=
  w.resolve || p.isLocal || p.hostCors ||
    match URL.parseUrl w.url with
    | none => false
    | some u =>
      match addr? (lower u.hostname) with
      | some a => !specialPurpose a
      | none =>
        match addr? w.address with
        | some a => !specialPurpose a
        | none => false

/-- What a step asks for. -/
inductive Step where
  /-- Tell the host to make this request. -/
  | send (t : Transfer) (w : Wire)
  /-- The page may read this. -/
  | deliver (t : Transfer) (r : Response)
  /-- A network error: the page learns nothing else. -/
  | fail (why : String)
  deriving Inhabited

/-- The resolve-only request for the current URL's name. -/
def Transfer.resolveWire (t : Transfer) : Wire :=
  { id := t.id, method := "", url := t.url, headers := [], body := none, resolve := true }

/-- Send `w` for `t` on the address rule: a name that must be resolved and has no pin yet is
resolved first; a pinned name's request carries its address; `wireReach` is checked last. -/
def emit (t : Transfer) (w : Wire) : Step :=
  match t.toResolve with
  | none => if wireReach t.page w then .send t w else .fail "refused: address"
  | some host =>
    match t.pinned host with
    | none => .send { t with phase := .resolve } t.resolveWire
    | some a =>
      if wireReach t.page { w with address := a, port := t.portOf } then .send t { w with address := a, port := t.portOf }
      else .fail "refused: address"

/-- Plan the current `http` or `https` URL: refuse it outside the policy, or send the
preflight when one is needed, or send the request (each through `emit`). -/
def planNet (t : Transfer) : Step :=
  if !t.allowed then .fail "refused by policy"
  else if t.sameOriginOnly && !t.same then .fail "refused by mode same-origin"
  else if !t.page.hostCors && !t.same && t.needsPreflight then
    let t' := { t with phase := .preflight }
    emit t' t'.preflightWire
  else
    let t' := { t with phase := .main }
    emit t' t'.mainWire

/-- A `data:` URL, answered here: only as the first URL, and not in mode "same-origin". -/
def dataStep (t : Transfer) : Step :=
  if t.redirects != 0 || t.sameOriginOnly then .fail "data: URL refused" else
  match dataResponse t.url with
  | some (mime, b) =>
    .deliver t { status := 200, statusText := "OK", url := t.url, headers := [("Content-Type", mime)], body := b }
  | none => .fail "bad data: URL"

/-- Plan the current URL: a `data:` URL is answered here, every other goes to `planNet`. -/
def plan (t : Transfer) : Step :=
  if t.url.startsWith "data:" then dataStep t else planNet t

/-- A field a page never reads (Fetch §2.2.2 "forbidden response-header name"). -/
def forbiddenResponseHeader (name : String) : Bool :=
  lower name == "set-cookie" || lower name == "set-cookie2"

/-- A CORS-safelisted response-header name. -/
def safeResponseHeader (name : String) : Bool :=
  ["cache-control", "content-language", "content-length", "content-type", "expires",
   "last-modified", "pragma"].contains (lower name)

/-- The response the page sees: without forbidden fields, and across origins only the
safelisted and exposed ones (Fetch §4.1 "CORS filtered response"). -/
def responseOf (t : Transfer) (a : Answer) : Response :=
  let allowed := a.headers.filter fun (n, _) => !forbiddenResponseHeader n
  let exposed := (listValue (headerGet a.headers "access-control-expose-headers")).map lower
  let star := exposed.contains "*" && !t.credentials
  let hs := if t.same || t.page.hostCors then allowed
    else allowed.filter fun (n, _) => safeResponseHeader n || exposed.contains (lower n) || star
  { status := a.status, statusText := a.statusText, url := if a.url.isEmpty then t.url else a.url,
    headers := hs, body := a.body }

/-- `301`, `302`, `303`, `307` or `308`. -/
def isRedirect (s : Nat) : Bool := s == 301 || s == 302 || s == 303 || s == 307 || s == 308

/-- The redirect limit (Fetch §4.4 step 7). -/
def maxRedirects : Nat := 20

/-- The headers that describe a body (dropped with it on a redirect to `GET`, Fetch §4.4). -/
def bodyHeader (name : String) : Bool :=
  ["content-encoding", "content-language", "content-location", "content-type"].contains (lower name)

/-- Follow a redirect to `next` (Fetch §4.4). -/
def afterRedirect (t : Transfer) (status : Nat) (next : URL.Url) : Transfer :=
  let toGet := ((status == 301 || status == 302) && t.method == "POST") ||
    (status == 303 && !(t.method == "GET" || t.method == "HEAD"))
  let nextUrl : URL.Url := { next with username := "", password := "" }
  let cur := URL.parseUrl t.url
  let crossed := t.crossed ||
    (match cur with
     | some cur => cur.origin != next.origin && !sameOrigin t.page cur
     | none => true)
  let leaves := match cur with
    | some cur => cur.origin != next.origin
    | none => true
  let hs := if toGet then t.headers.filter (!bodyHeader ·.1) else t.headers
  { t with url := nextUrl.serialize true, redirects := t.redirects + 1, crossed,
           method := if toGet then "GET" else t.method,
           body := if toGet then none else t.body,
           headers := if leaves then hs.filter (lower ·.1 != "authorization") else hs }

/-- The final URL the host reports (the Hub follows redirects itself) is inside the policy. -/
def finalAllowed (t : Transfer) (a : Answer) : Bool :=
  a.url.isEmpty || match URL.parseUrl a.url with
    | some u => mayConnect t.page u
    | none => false

/-- The host's answer: refuse it, deliver it, or send the next hop. -/
def onAnswer (t : Transfer) (a : Answer) : Step :=
  match t.phase with
  | .resolve =>
    match t.toResolve with
    | none => plan { t with phase := .main }
    | some host =>
      match L4Factoidal.Net.choose {} host a.addresses with
      | .ok addr => plan { t with pin := some (host, addr), phase := .main }
      | .error _ => .fail "refused: the name resolves to a special-purpose address"
  | .preflight =>
    if a.status == 0 then .fail "network error" else
    if preflightOk t a then
      let t' := { t with phase := .main }
      emit t' t'.mainWire
    else .fail "CORS preflight refused"
  | .main =>
    if a.status == 0 then .fail "network error" else
    if !finalAllowed t a then .fail "refused by policy" else
    if !t.page.hostCors && !t.same && !corsOk t a then .fail "CORS refused" else
    if isRedirect a.status && !t.page.hostCors then
      match headerGet a.headers "location" with
      | none => .deliver t (responseOf t a)
      | some loc =>
        if t.redirects ≥ maxRedirects then .fail "too many redirects" else
        match URL.parseUrl loc (some t.url) with
        | none => .fail "bad redirect"
        | some next =>
          if next.includesCredentials && next.origin != t.page.origin then .fail "redirect with credentials" else
          plan (afterRedirect t a.status next)
    else .deliver t (responseOf t a)

/-! ## Theorems -/

/-- Kind: policy lemma. Says: a page whose origin is not local cannot make a target that the
URL names as local pass `mayConnect`. Does not say: anything about a name that resolves to a
local address (the DNS answer is the host's). -/
theorem mayConnect_local_needs_local_page (p : Page) (u : URL.Url)
    (h : mayConnect p u = true) (hp : privateHost u = true) : p.isLocal = true := by
  simp [mayConnect, hp] at h
  exact h.1.2

/-- Kind: policy lemma. Says: no scheme outside `http` and `https` passes `mayConnect` (so a
page reads no `file:` URL through this core). Does not say: anything of other paths, such as
the host loading `file:` pages for its own document. -/
theorem mayConnect_scheme (p : Page) (u : URL.Url) (h : mayConnect p u = true) :
    u.scheme = "http" ∨ u.scheme = "https" := by
  simp [mayConnect] at h
  exact h.1.1

/-- Kind: lemma on `emit`. Says: `emit` sends either the resolve-only request of the
transfer's URL (and waits in phase `resolve`), or the request it was given, with the same
URL, method, fields and body, for the same transfer, and then `wireReach` held. Does not say:
which of the two (that is `toResolve` and the pin). -/
theorem emit_cases {t t' : Transfer} {w w' : Wire} (h : emit t w = .send t' w') :
    (t' = { t with phase := .resolve } ∧ w' = t.resolveWire) ∨
    (t' = t ∧ w'.url = w.url ∧ w'.method = w.method ∧ w'.headers = w.headers ∧ w'.body = w.body ∧
      wireReach t.page w' = true) := by
  unfold emit at h
  split at h
  · split at h
    · simp only [Step.send.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, by assumption⟩
    · simp at h
  · split at h
    · simp only [Step.send.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
    · split at h
      · simp only [Step.send.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl, rfl, rfl, rfl, by assumption⟩
      · simp at h

/-- Kind: policy lemma. Says: every request `emit` tells the host to make passes `wireReach`
for the page: a resolve-only request, or one whose address is not special-purpose (or a local
page, or the Hub). Does not say: that the host connects to that address. -/
theorem emit_reach {t t' : Transfer} {w w' : Wire} (h : emit t w = .send t' w') :
    wireReach t.page w' = true ∧ t'.page = t.page := by
  rcases emit_cases h with ⟨rfl, rfl⟩ | ⟨rfl, -, -, -, -, hr⟩
  · simp [wireReach, Transfer.resolveWire]
  · exact ⟨hr, rfl⟩

/-- Kind: lemma. Says: a `data:` URL never makes `plan` send anything: every request `plan`
sends is `planNet`'s. -/
theorem plan_send_net {t t' : Transfer} {w : Wire} (h : plan t = .send t' w) : planNet t = .send t' w := by
  unfold plan at h
  split at h
  · unfold dataStep at h
    split at h
    · simp at h
    · split at h <;> simp at h
  · exact h

/-- Kind: policy theorem. Says: `plan` tells the host to make a request only when the current
URL passes `mayConnect` for the page, on the same string the host gets (`Wire.url = t.url`),
and the request passes `wireReach`. Does not say: that the host obeys. -/
theorem plan_send_allowed (t t' : Transfer) (w : Wire) (h : plan t = .send t' w) :
    t.allowed = true ∧ w.url = t.url ∧ wireReach t.page w = true ∧ t'.page = t.page := by
  replace h := plan_send_net h
  unfold planNet at h
  by_cases ha : t.allowed = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, if_false] at h
    split at h
    · simp at h
    · split at h
      · have ⟨hr, hp⟩ := emit_reach h
        rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, hu, -⟩
        · exact ⟨ha, rfl, hr, hp⟩
        · exact ⟨ha, by simp [hu, Transfer.preflightWire], hr, hp⟩
      · have ⟨hr, hp⟩ := emit_reach h
        rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, hu, -⟩
        · exact ⟨ha, rfl, hr, hp⟩
        · exact ⟨ha, by simp [hu, Transfer.mainWire], hr, hp⟩
  · simp [ha] at h

theorem afterRedirect_page (t : Transfer) (s : Nat) (n : URL.Url) : (afterRedirect t s n).page = t.page := rfl

/-- Kind: policy theorem (DNS rebinding). Says: every request that `onAnswer` tells the host
to make passes `wireReach` for the page: on a native host, for a page that is not local, a
request to a name carries an address that is not special-purpose, and any other request is
a resolve-only one or goes to an IP literal that is not special-purpose. Does not say: that the
host connects to that address and to no other (the host glue is tested, not proved). -/
theorem onAnswer_reach (t t' : Transfer) (a : Answer) (w : Wire) (h : onAnswer t a = .send t' w) :
    wireReach t.page w = true := by
  unfold onAnswer at h
  split at h
  · split at h
    · exact (plan_send_allowed _ _ _ h).2.2.1
    · split at h
      · exact (plan_send_allowed _ _ _ h).2.2.1
      · simp at h
  · split at h
    · simp at h
    · split at h
      · exact (emit_reach h).1
      · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · split at h
                · simp at h
                · split at h
                  · simp at h
                  · exact (plan_send_allowed _ _ _ h).2.2.1
          · simp at h

/-- Kind: policy theorem (DNS rebinding). Says: when the host's answer for a name lists any
special-purpose address, `onAnswer` sends no request for it: the transfer fails. Does not say:
anything of a name that the host resolves differently later (the pin is not re-read). -/
theorem onAnswer_resolve_special (t : Transfer) (a : Answer) (host : String) (x : Addr)
    (hp : t.phase = .resolve) (hr : t.toResolve = some host)
    (hx : x ∈ a.addresses.filterMap addr?) (hs : specialPurpose x = true) :
    ∀ t' w, onAnswer t a ≠ .send t' w := by
  intro t' w h
  unfold onAnswer at h
  simp only [hp, hr] at h
  split at h
  · rename_i addr hc
    exact egress_refuses_special (p := {}) rfl hx hs addr hc
  · simp at h

/-- Kind: policy theorem. Says: on a native host, `onAnswer` gives a page the response to a
cross-origin request only when the CORS check of that exact answer passed. Does not say:
what the Hub's browser does (`hostCors`), which enforces CORS for its own origin. -/
theorem deliver_cross_origin_needs_cors (t t' : Transfer) (a : Answer) (r : Response)
    (hn : t.page.hostCors = false) (hp : t.phase = .main) (hc : t.same = false)
    (h : onAnswer t a = .deliver t' r) : corsOk t a = true := by
  unfold onAnswer at h
  simp only [hp] at h
  by_cases hok : corsOk t a = true
  · exact hok
  · exfalso
    have hc' : (!t.page.hostCors && !t.same && !corsOk t a) = true := by simp [hn, hc, hok]
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp at h

/-- Kind: policy theorem. Says: on a native host, for a cross-origin request outside the
CORS-safelist, `plan` sends only the preflight (or first the resolve-only request of the
name), not the request. Does not say: that the preflight answer is what the server meant
(the server is trusted for its own CORS). -/
theorem plan_cross_unsafe_is_preflight (t t' : Transfer) (w : Wire)
    (hn : t.page.hostCors = false) (hc : t.same = false) (hu : t.needsPreflight = true)
    (h : plan t = .send t' w) :
    (w.resolve = true ∧ w.body = none) ∨ (t'.phase = .preflight ∧ w.method = "OPTIONS" ∧ w.body = none) := by
  replace h := plan_send_net h
  unfold planNet at h
  by_cases ha : t.allowed = true
  · have hs : (t.sameOriginOnly && !t.same) = t.sameOriginOnly := by simp [hc]
    simp only [ha, Bool.not_true, Bool.false_eq_true, if_false, hs] at h
    split at h
    · simp at h
    · simp only [hn, hc, hu, Bool.not_false, Bool.and_self, if_true] at h
      rcases emit_cases h with ⟨-, rfl⟩ | ⟨rfl, -, hm, -, hb, -⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact Or.inr ⟨rfl, by simp [hm, Transfer.preflightWire], by simp [hb, Transfer.preflightWire]⟩
  · simp [ha] at h

/-- Kind: policy theorem. Says: a preflight turns into the real request only after its answer
passed `preflightOk`. Does not say: anything of the `hostCors` case, where no preflight is
made here. -/
theorem onAnswer_preflight_needs_ok (t t' : Transfer) (w : Wire) (a : Answer)
    (hp : t.phase = .preflight) (h : onAnswer t a = .send t' w) : preflightOk t a = true := by
  unfold onAnswer at h
  simp only [hp] at h
  split at h
  · simp at h
  · split at h
    · assumption
    · simp at h

/-- Kind: policy theorem. Says: every request `plan` tells the host to make carries no
page-set forbidden header: only `Origin`, which the engine adds, can be a forbidden name.
Does not say: what the host adds on its own (a real fetch adds `Host` and so on). -/
theorem plan_wire_forbidden (t : Transfer) (t' : Transfer) (w : Wire) (h : plan t = .send t' w)
    (n : String × String) (hn : n ∈ w.headers) (hf : forbiddenRequestHeader n.1 = true) :
    n.1 = "Origin" ∨ w.method = "OPTIONS" := by
  replace h := plan_send_net h
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, hm, -⟩
        · simp [Transfer.resolveWire] at hn
        · exact Or.inr (by simp [hm, Transfer.preflightWire])
      · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, -, hh, -⟩
        · simp [Transfer.resolveWire] at hn
        · left
          rw [hh] at hn
          simp only [Transfer.mainWire] at hn
          split at hn
          · rcases List.mem_append.mp hn with hl | hr
            · have := (List.mem_filter.mp hl).2
              simp [hf] at this
            · simp at hr; rw [hr]
          · have := (List.mem_filter.mp hn).2
            simp [hf] at this

/-- Kind: invariant of the response filter. Says: no response the page reads has a
`Set-Cookie` or `Set-Cookie2` field. Does not say: anything of the host's own cookie jar
(no host here has one: no cookie is sent or stored). -/
theorem responseOf_no_set_cookie (t : Transfer) (a : Answer) (n : String × String)
    (hn : n ∈ (responseOf t a).headers) : forbiddenResponseHeader n.1 = false := by
  simp only [responseOf] at hn
  split at hn
  · have := (List.mem_filter.mp hn).2
    simpa using this
  · have := (List.mem_filter.mp (List.mem_filter.mp hn).1).2
    simpa using this

/-! ## Checks (`#guard` is a test) -/

private def pg : Page := Page.ofUrl "https://a.example/x"

#guard pg.origin == "https://a.example" && !pg.isLocal && pg.secure
#guard (Page.ofUrl "file:///tmp/x.html").origin == "null"
#guard (URL.parseUrl "http://LOCALHOST/").any privateHost
#guard (URL.parseUrl "http://127.0.0.1:8000/").any privateHost
#guard (URL.parseUrl "http://[::1]/").any privateHost
#guard (URL.parseUrl "http://foo.localhost./").any privateHost
#guard !(URL.parseUrl "http://web-platform.test/").any privateHost
#guard !(URL.parseUrl "http://127.0.0.1/").any (mayConnect pg)
#guard !(URL.parseUrl "file:///etc/passwd").any (mayConnect (Page.ofUrl "file:///tmp/x.html"))
#guard (URL.parseUrl "https://b.example/").any (mayConnect pg)
#guard !(URL.parseUrl "http://b.example/").any (mayConnect pg)
#guard forbiddenRequestHeader "Cookie" && forbiddenRequestHeader "Sec-Foo" && !forbiddenRequestHeader "X-Foo"
#guard forbiddenOverride "X-HTTP-Method-Override" "get, trace" && !forbiddenOverride "X-HTTP-Method-Override" "PUT"
#guard safeHeader "Content-Type" "text/plain;charset=UTF-8" && !safeHeader "Content-Type" "application/json"
#guard unsafeHeaderNames [("X-B", "1"), ("x-a", "2"), ("Accept", "*/*")] == ["x-a", "x-b"]

private def base : Transfer :=
  { id := 1, page := pg, method := "GET", url := "https://b.example/d", headers := [], body := none,
    pin := some ("b.example", "93.184.215.14") }

private def planWire (t : Transfer) : Option Wire :=
  match plan t with | .send _ w => some w | _ => none

#guard (planWire base).any fun w => w.method == "GET" && w.headers == [("Origin", "https://a.example")]
#guard (planWire { base with headers := [("X-A", "1")] }).any fun w => w.method == "OPTIONS"
#guard (planWire { base with url := "http://127.0.0.1/" }).isNone

private def corsAns (v : String) : Answer := { status := 200, headers := [("Access-Control-Allow-Origin", v), ("X-S", "1"), ("Set-Cookie", "a")] }

#guard match onAnswer base (corsAns "https://a.example") with | .deliver _ r => r.headers.isEmpty | _ => false
#guard match onAnswer base (corsAns "https://c.example") with | .fail _ => true | _ => false
#guard match onAnswer base { status := 200 } with | .fail _ => true | _ => false
#guard match onAnswer { base with url := "https://a.example/y" } ({ status := 200, headers := [("X-S", "1"), ("Set-Cookie", "a")] } : Answer) with
  | .deliver _ r => r.headers == [("X-S", "1")] | _ => false
-- DNS rebinding: a name is resolved first; any special-purpose address refuses it; a public
-- one is pinned, and the preflight and the request carry it
private def stepOf (t : Transfer) (a : Answer) : Option (Transfer × Wire) :=
  match onAnswer t a with | .send t' w => some (t', w) | _ => none
private def named : Transfer := { base with page := { pg with secure := false }, url := "http://b.example/d", headers := [("X-A", "1")], pin := none }
#guard match plan named with | .send t w => w.resolve && t.phase == .resolve && w.headers.isEmpty | _ => false
#guard match plan named with
  | .send t _ => (stepOf t { addresses := ["93.184.215.14", "127.0.0.1"] }).isNone | _ => false
#guard match plan named with
  | .send t _ => (stepOf t { addresses := ["93.184.215.14"] }).any fun (t', w) =>
      w.method == "OPTIONS" && w.address == "93.184.215.14" && w.port == 80 && t'.phase == .preflight | _ => false
#guard match plan named with
  | .send t _ => (stepOf t { addresses := ["10.0.0.1"] }).isNone | _ => false
-- a local page (the host loaded it from 127.0.0.1) resolves nothing
#guard (Page.ofUrl "http://web-platform.test:8000/x" false "127.0.0.1").isLocal
#guard !(Page.ofUrl "http://web-platform.test:8000/x" false "93.184.215.14").isLocal
#guard match plan { named with page := Page.ofUrl "http://web-platform.test/" false "127.0.0.1" } with
  | .send _ w => !w.resolve && w.method == "OPTIONS" | _ => false
-- an IP literal is not resolved
#guard match plan { base with url := "https://93.184.215.14/" } with | .send _ w => !w.resolve && w.address.isEmpty | _ => false
-- Authorization is dropped on a redirect to another origin, kept on the same origin
#guard (afterRedirect { base with headers := [("Authorization", "x")] } 302 ((URL.parseUrl "https://c.example/").getD default)).headers.isEmpty
#guard (afterRedirect { base with headers := [("Authorization", "x")] } 302 ((URL.parseUrl "https://b.example/z").getD default)).headers.length == 1
-- a cross-origin redirect to a URL with credentials is a network error
#guard match onAnswer { base with url := "https://a.example/y", pin := some ("a.example", "93.184.215.14") }
    ({ status := 302, headers := [("Location", "https://u:p@c.example/")] } : Answer) with
  | .fail _ => true | _ => false
-- the Hub: a final URL outside the policy is withheld
#guard match onAnswer { base with page := { pg with hostCors := true } } ({ status := 200, url := "http://127.0.0.1/" } : Answer) with
  | .fail _ => true | _ => false
-- data: URLs, answered here
#guard (dataResponse "data:,Hello%2C%20World!").map (fun (m, b) => (m, b.toList)) == some ("text/plain;charset=US-ASCII", "Hello, World!".toUTF8.toList)
#guard (dataResponse "data:text/html;base64,PGI+eDwvYj4=").map (fun (m, b) => (m, b.toList)) == some ("text/html", "<b>x</b>".toUTF8.toList)
#guard (dataResponse "data:TEXT/Plain ; charset=utf-8,x#frag").map (fun (m, b) => (m, b.toList)) == some ("text/plain;charset=utf-8", "x".toUTF8.toList)
#guard (dataResponse "data:;base64,%%%").isNone
#guard (dataResponse "data:nocomma").isNone
#guard match plan { base with url := "data:,x" } with | .deliver _ r => r.status == 200 && r.body.toList == "x".toUTF8.toList | _ => false
#guard match plan { base with url := "data:,x", redirects := 1 } with | .fail _ => true | _ => false
#guard match plan { base with url := "data:,x", sameOriginOnly := true } with | .fail _ => true | _ => false
-- a redirect is checked again: same-origin to a local address is refused
#guard match onAnswer { base with url := "https://a.example/y" } ({ status := 302, headers := [("Location", "http://127.0.0.1/")] } : Answer) with
  | .fail _ => true | _ => false

end L4Factoidal.Net.PageFetch
