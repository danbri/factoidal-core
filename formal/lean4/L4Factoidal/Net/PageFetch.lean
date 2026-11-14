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
* Mode "no-cors" (`fetch`, and the requests elements make): a cross-origin request goes out
  only when it is simple (a safelisted method and safelisted fields: `plan` refuses any
  other, `plan_noCors_simple`), with no preflight and no CORS check, and its answer is
  opaque: the page gets no status, no field, no byte and no URL of it (`responseOf_opaque`).
* Fetch metadata: a request to a potentially trustworthy URL says where it comes from
  (`Sec-Fetch-Site`: `same-origin` only when every URL of the request so far is of the
  page's origin, `site_same_origin`), its mode and its destination. There is no public
  suffix list in the engine, so `same-site` is said only of the page's own scheme and host
  on another port; a subdomain is `cross-site`, which claims less.
* Cross-origin: refused unless CORS allows it. A request outside the CORS-safelist has a
  preflight first (every hop); the response of a cross-origin request is withheld unless the
  CORS check passes; only the safelisted and exposed header fields reach the page.
* Referrer: a request carries a `Referer` only as `referrerOf` allows: the request's
  referrer (its document's or worker's URL unless the page named a same-origin one, or
  none) cut down by its referrer policy for the URL of each hop (`Net.ReferrerPolicy.decide`;
  Fetch §4.1 main fetch step 8). Only an `http` or `https` URL is ever a referrer; a
  redirect's `Referrer-Policy` replaces the policy for the hops after it (Fetch §4.4 step
  19), and the source of each later hop is the referrer the hop before carried, so a chain
  never regains what one hop removed (`ReferrerPolicy.determine_chain`). Not on the Hub
  (`hostCors`): the browser that runs the Hub makes that field itself.
* Credentials: cookies only, from the page session's own jar (`Net.Cookies`: in memory, each
  cookie its host's). A request carries the cookies of its URL's host when it is made with
  credentials (`Transfer.sendsCredentials`: to the page's own origin unless the page said
  "omit"; to another origin only with `credentials: "include"` or `withCredentials`), and
  then only those `SameSite` lets a request of its site carry (`plan_wire_cookie`). A
  preflight never carries any (`preflight_no_cookie`). No HTTP authentication and no client
  certificate is ever sent (`Authorization` set by the host never exists here). A URL's user and password are removed. An
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
import L4Factoidal.Net.ReferrerPolicy
import L4Factoidal.Net.Cookies

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

/-- The policy of a dedicated worker's requests (HTML §10.2.4 "run a worker": the worker's
settings object takes its origin and policy container from its owner). A worker's script URL
is same-origin with its owner (or `blob:`, whose origin is the owner's), so its requests have
the owner's origin; a `data:` worker has an opaque origin (`"null"`: nothing is same-origin
to it). Local, secure and `hostCors` are always the owner's: a worker never reaches what its
owner may not. -/
def Page.forWorker (owner : Page) (workerUrl : String) : Page :=
  if workerUrl.startsWith "data:" then { owner with origin := "null" } else owner

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
  names.eraseDups.mergeSort fun a b => decide (a ≤ b)

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
  /-- Fetch §2.2.6 response tainting, as `Response.type` shows it: `basic`, `cors`, `opaque`. -/
  tainting : String := "basic"
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
  /-- Fetch redirect mode "error" (`fetch`): a redirect is a network error (Fetch §4.3 step 6). -/
  redirectError : Bool := false
  /-- Fetch redirect mode "manual" (`fetch`): a redirect is not followed; the page gets an
  opaque-redirect response (Fetch §4.3 step 6: no status, no field, no body). -/
  redirectManual : Bool := false
  /-- The host name (lowercase) and the address chosen for it (`Egress.choose`). -/
  pin : Option (String × String) := none
  /-- For a `blob:` URL: the type and bytes of the entry that the page's own origin made
  for it (`Net.BlobUrls.resolve`, given by `Net.Xhr`); `none` when there is none. -/
  blob : Option (String × ByteArray) := none
  /-- The request's referrer (Fetch §2.2.5), a URL serialized, or `""` for none: the source
  that `referrerOf` cuts down for each hop. After a redirect it is the referrer the hop
  before carried. -/
  referrer : String := ""
  /-- The request's referrer policy (the document's or the default when the request names
  none: resolved by `Net.Xhr.beginFetch`). -/
  referrerPolicy : ReferrerPolicy.Policy := .default
  /-- Fetch mode "no-cors": no preflight and no CORS check; a cross-origin answer is opaque. -/
  noCors : Bool := false
  /-- The request's destination (Fetch §2.2.5): `empty` for `fetch` and `XMLHttpRequest`. -/
  destination : String := "empty"
  /-- The farthest any earlier URL of this request was from the page (`siteRank`): 0 while
  every one was of the page's origin. -/
  farthest : Nat := 0
  /-- Fetch credentials mode "omit" (`fetch`): no cookie is sent and none is stored. -/
  omitCredentials : Bool := false
  /-- The page session's cookies as they are when this hop is planned (`Net.Xhr` gives the
  jar before each plan and after each answer), and the time in seconds. -/
  jar : Cookies.Jar := {}
  now : Nat := 0
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

/-! ## The referrer (Fetch §4.1 main fetch step 8; Referrer Policy §8.3, §8.4) -/

/-- A loopback host: `localhost`, a `.localhost` name, `127.0.0.0/8` or `[::1]`. -/
def loopbackHost (h : String) : Bool :=
  localhostName h || h == "[::1]" ||
    match ipv4? h with
    | some (127 :: _) => true
    | _ => false

/-- A potentially trustworthy URL, as far as its scheme and host say (Secure Contexts §3.1):
`https`, `wss`, or a loopback host. -/
def trustworthyUrl (u : URL.Url) : Bool :=
  u.scheme == "https" || u.scheme == "wss" || loopbackHost (lower u.hostname)

/-- A URL for use as a referrer: without credentials and without fragment (§8.4). -/
def referrerFull (u : URL.Url) : String :=
  ({ u with username := "", password := "" } : URL.Url).serialize true

/-- The origin-only form of a referrer (§8.4 with the origin-only flag): no path, no query. -/
def referrerOrigin (u : URL.Url) : String := u.origin ++ "/"

/-- The referrer a request from `source` (a URL, serialized; `""` for none) to `target`
carries under `policy`; `""` is no referrer. Only an `http` or `https` source is ever a
referrer (§8.4 names the local schemes; a `file:` path is not sent either). A stripped
source longer than 4096 characters is cut to its origin (§8.3 step 6). -/
def referrerOf (policy : ReferrerPolicy.Policy) (source : String) (target : URL.Url) : String :=
  match URL.parseUrl source with
  | none => ""
  | some s =>
    if !(s.scheme == "http" || s.scheme == "https") then "" else
    match ReferrerPolicy.decide policy (s.origin == target.origin) (trustworthyUrl s && !trustworthyUrl target) with
    | .nothing => ""
    | .origin => referrerOrigin s
    | .full => if (referrerFull s).length > 4096 then referrerOrigin s else referrerFull s

/-- The `Referer` of a request to the transfer's current URL (`""`: none is sent). The Hub's
browser makes its own. -/
def Transfer.referer (t : Transfer) : String :=
  if t.page.hostCors then "" else
  match URL.parseUrl t.url with
  | some u => referrerOf t.referrerPolicy t.referrer u
  | none => ""

/-- The `Referer` field of a wire, when there is one. -/
def Transfer.refererField (t : Transfer) : List (String × String) :=
  if t.referer.isEmpty then [] else [("Referer", t.referer)]

/-- All values of the header `name` of a field list, joined with commas (HTTP: several
fields of one name are one list). -/
def headerAll (hs : List (String × String)) (name : String) : String :=
  ",".intercalate ((hs.filter fun (n, _) => lower n == name).map (·.2))

/-- A redirect was answered (Fetch §4.4): the next hop's source is the referrer this hop
carried, and a `Referrer-Policy` of the redirect response that names a policy replaces the
request's (step 19, "set request's referrer policy on redirect"). -/
def Transfer.hopReferrer (t : Transfer) (a : Answer) : Transfer :=
  { t with referrer := t.referer,
           referrerPolicy := (ReferrerPolicy.Policy.ofHeader (headerAll a.headers "referrer-policy")).getD t.referrerPolicy }

/-! ## Fetch metadata (https://w3c.github.io/webappsec-fetch-metadata/ §2, §3) -/

/-- How far a URL is from the page: 0 the same origin, 1 the same site, 2 another site. The
engine has no public suffix list, so the same site is only the page's own scheme and host
(another port): a subdomain counts as another site, which claims less than a browser with
the list does. -/
def siteRank (p : Page) (u : URL.Url) : Nat :=
  if sameOrigin p u then 0 else
  match URL.parseUrl p.origin with
  | some o => if p.origin != "null" && o.scheme == u.scheme && o.hostname == u.hostname then 1 else 2
  | none => 2

/-- The farthest any URL of the request, the current one too, is from the page. -/
def Transfer.site (t : Transfer) : Nat :=
  max t.farthest (match URL.parseUrl t.url with
    | some u => siteRank t.page u
    | none => 2)

/-- The `Sec-Fetch-Site` token of a rank. -/
def siteToken : Nat → String
  | 0 => "same-origin"
  | 1 => "same-site"
  | _ => "cross-site"

/-- The request's mode, as Fetch names it. -/
def Transfer.mode (t : Transfer) : String :=
  if t.sameOriginOnly then "same-origin" else if t.noCors then "no-cors" else "cors"

/-- The `Sec-Fetch-*` fields of a request in `mode` to the current URL: only to a
potentially trustworthy URL (§3 "set the ... header": step 2), and not on the Hub. -/
def Transfer.metadataFields (t : Transfer) (mode : String) : List (String × String) :=
  if t.page.hostCors then [] else
  match URL.parseUrl t.url with
  | some u =>
    if trustworthyUrl u then
      [("Sec-Fetch-Dest", t.destination), ("Sec-Fetch-Mode", mode), ("Sec-Fetch-Site", siteToken t.site)]
    else []
  | none => []

/-- The fields the engine adds after the page's own and the CORS fields: the `Referer` and
the fetch metadata. -/
def Transfer.engineFields (t : Transfer) (mode : String) : List (String × String) :=
  t.refererField ++ t.metadataFields mode

/-- The `Origin` field (Fetch §4.3 "append a request `Origin` header"): on every request whose
answer goes through the CORS check; else on a request that is not `GET` or `HEAD`, where
the referrer policy may turn it into `null` (`no-referrer`; a downgrade under the strict
policies; another origin under `same-origin`). -/
def Transfer.originField (t : Transfer) : List (String × String) :=
  if !t.same && !t.noCors then [("Origin", t.originValue)]
  else if t.method == "GET" || t.method == "HEAD" then []
  else
    let hidden := match t.referrerPolicy with
      | .noReferrer => true
      | .noReferrerWhenDowngrade | .strictOrigin | .strictOriginWhenCrossOrigin =>
        t.page.secure && !t.url.startsWith "https:"
      | .sameOrigin => !t.same
      | _ => false
    [("Origin", if hidden then "null" else t.originValue)]

/-- Is this hop made with credentials (Fetch §4.5 step 8.5): the page did not say "omit", and
the mode is "include" or the request has stayed in the page's origin. Never on the Hub
from here (its browser has its own jar). -/
def Transfer.sendsCredentials (t : Transfer) : Bool :=
  !t.omitCredentials && !t.page.hostCors && (t.credentials || t.same)

/-- The cookies' site of a URL: its host, path and whether it is secure. -/
def cookieSite (u : URL.Url) : Option Cookies.Site :=
  Cookies.siteOf u.origin (u.scheme == "https") u.pathname

/-- The value of the `Cookie` field of the request to the current URL ("" for none): the
jar's cookies for that host, path and scheme; only `SameSite=None` ones when the request is
not same-site with the page (`Transfer.site`). -/
def Transfer.cookieValue (t : Transfer) : String :=
  if !t.sendsCredentials then "" else
  match (URL.parseUrl t.url).bind cookieSite with
  | some site => Cookies.forRequest t.jar site t.now (t.site ≤ 1)
  | none => ""

/-- The jar after the `Set-Cookie` fields of the answer to this hop (Fetch §4.6 "HTTP-network
fetch": cookies are received only when credentials are included; RFC 6265bis §5.7): each
field for the host, path and scheme of the URL it answers; the answer to a request that is
not same-site with the page sets only `SameSite=None` cookies. -/
def Transfer.storeCookies (t : Transfer) (jar : Cookies.Jar) (a : Answer) : Cookies.Jar :=
  if !t.sendsCredentials then jar else
  match (URL.parseUrl t.url).bind cookieSite with
  | none => jar
  | some site =>
    a.headers.foldl (fun j (f : String × String) =>
      if lower f.1 == "set-cookie" then Cookies.setFromHeaderIn j site t.now (t.site ≤ 1) f.2 else j) jar

/-- The `Cookie` field of the main request, when there is one. -/
def Transfer.cookieField (t : Transfer) : List (String × String) :=
  if t.cookieValue.isEmpty then [] else [("Cookie", t.cookieValue)]

/-- The wire form of the request: the page's fields that are not forbidden, `Origin`,
`Cookie`, then the engine's other fields (`Referer`, fetch metadata). -/
def Transfer.mainWire (t : Transfer) : Wire :=
  let h := t.headers.filter fun (n, v) => !forbiddenRequestHeader n && !forbiddenOverride n v
  { id := t.id, method := t.method, url := t.url, headers := h ++ t.originField ++ t.cookieField ++ t.engineFields t.mode, body := t.body }

/-- The CORS-preflight request (Fetch §4.8: `OPTIONS`, `Origin`, the method and the unsafe
names; no body, no author headers). -/
def Transfer.preflightWire (t : Transfer) : Wire :=
  let names := unsafeHeaderNames t.headers
  let h : List (String × String) :=
    [("Accept", "*/*"), ("Origin", t.originValue), ("Access-Control-Request-Method", t.method)] ++
      (if names.isEmpty then [] else [("Access-Control-Request-Headers", ",".intercalate names)])
  { id := t.id, method := "OPTIONS", url := t.url, headers := h ++ t.engineFields "cors", body := none }

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
  else if t.noCors && !t.same && t.needsPreflight then .fail "refused: a no-cors request that is not simple"
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

/-- Fetch §2.2.3 "parse a single range header value", with whitespace allowed: the first and
last byte positions of `bytes=first-last`, either of which may be absent (not both). -/
def singleRange (v : String) : Option (Option Nat × Option Nat) :=
  if !v.startsWith "bytes" then none else
  let space := fun (c : Char) => c == '\t' || c == ' '
  match ((v.drop 5).toString.toList).dropWhile space with
  | '=' :: cs =>
    let cs := cs.dropWhile space
    let first := cs.takeWhile Char.isDigit
    match (cs.dropWhile Char.isDigit).dropWhile space with
    | '-' :: cs =>
      let cs := cs.dropWhile space
      let last := cs.takeWhile Char.isDigit
      if !(cs.dropWhile Char.isDigit).isEmpty then none else
      match (if first.isEmpty then none else (String.ofList first).toNat?),
            (if last.isEmpty then none else (String.ofList last).toNat?) with
      | none, none => none
      | some a, some b => if a > b then none else some (some a, some b)
      | a, b => some (a, b)
    | _ => none
  | _ => none

/-- The bytes of a blob of `full` bytes that a range names (Fetch §4.2, the `blob` scheme with
a `Range` field): the first and the last position, both inside the blob; `none` is a network
error. A suffix range `-n` names the last `n` bytes. -/
def blobRange (full : Nat) (r : Option Nat × Option Nat) : Option (Nat × Nat) :=
  match r with
  | (some a, b) =>
    if a ≥ full || min (b.getD (full - 1)) (full - 1) < a then none
    else some (a, min (b.getD (full - 1)) (full - 1))
  | (none, some n) => if n == 0 || full == 0 then none else some (full - min n full, full - 1)
  | (none, none) => none

/-- A `blob:` URL (File API §8.3; Fetch §4.2 "scheme fetch"), answered here from the entry
that the page's own origin made (`Transfer.blob`): only `GET`, and only as the first URL of a
request (a redirect to it is a network error). With a `Range` field the answer is `206` with
the bytes the range names (`blobRange`). -/
def blobStep (t : Transfer) : Step :=
  if t.redirects != 0 || t.method != "GET" then .fail "blob: URL refused" else
  match t.blob with
  | some (type, b) =>
    match headerGet t.headers "range" with
    | none =>
      .deliver t { status := 200, statusText := "OK", url := t.url,
                   headers := [("Content-Type", type), ("Content-Length", toString b.size)], body := b }
    | some v =>
      match (singleRange v).bind (blobRange b.size) with
      | some (first, last) =>
        .deliver t { status := 206, statusText := "Partial Content", url := t.url,
                     headers := [("Content-Type", type), ("Content-Length", toString (last + 1 - first)),
                                 ("Content-Range", s!"bytes {first}-{last}/{b.size}")],
                     body := b.extract first (last + 1) }
      | none => .fail "blob: range not satisfiable"
  | none => .fail "blob: URL not found"

/-- Plan the current URL: a `data:` or `blob:` URL is answered here, every other goes to
`planNet`. -/
def plan (t : Transfer) : Step :=
  if t.url.startsWith "data:" then dataStep t
  else if t.url.startsWith "blob:" then blobStep t
  else planNet t

/-- A field a page never reads (Fetch §2.2.2 "forbidden response-header name"). -/
def forbiddenResponseHeader (name : String) : Bool :=
  lower name == "set-cookie" || lower name == "set-cookie2"

/-- A CORS-safelisted response-header name. -/
def safeResponseHeader (name : String) : Bool :=
  ["cache-control", "content-language", "content-length", "content-type", "expires",
   "last-modified", "pragma"].contains (lower name)

/-- The response the page sees: without forbidden fields, and across origins only the
safelisted and exposed ones (Fetch §4.1 "CORS filtered response"). In mode "no-cors" an
answer from another origin is opaque (Fetch §2.2.6 "opaque filtered response"): no status,
no reason, no field, no byte, no URL. -/
def responseOf (t : Transfer) (a : Answer) : Response :=
  if t.noCors && !t.same && !t.page.hostCors then
    { status := 0, statusText := "", url := "", headers := [], body := ByteArray.empty, tainting := "opaque" }
  else
  let allowed := a.headers.filter fun (n, _) => !forbiddenResponseHeader n
  let exposed := (listValue (headerGet a.headers "access-control-expose-headers")).map lower
  let star := exposed.contains "*" && !t.credentials
  let hs := if t.same || t.page.hostCors then allowed
    else allowed.filter fun (n, _) => safeResponseHeader n || exposed.contains (lower n) || star
  { status := a.status, statusText := a.statusText, url := if a.url.isEmpty then t.url else a.url,
    headers := hs, body := a.body, tainting := if t.same || t.page.hostCors then "basic" else "cors" }

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
  { t with url := nextUrl.serialize true, redirects := t.redirects + 1, crossed, farthest := t.site,
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
    if !t.page.hostCors && !t.same && !t.noCors && !corsOk t a then .fail "CORS refused" else
    if isRedirect a.status && !t.page.hostCors then
      match headerGet a.headers "location" with
      | none => .deliver t (responseOf t a)
      | some loc =>
        if t.redirectError then .fail "redirect refused by redirect mode error" else
        if t.redirectManual then
          .deliver t { status := 0, statusText := "", url := t.url, headers := [], body := ByteArray.empty, tainting := "opaqueredirect" } else
        if t.redirects ≥ maxRedirects then .fail "too many redirects" else
        match URL.parseUrl loc (some t.url) with
        | none => .fail "bad redirect"
        | some next =>
          if next.includesCredentials && next.origin != t.page.origin then .fail "redirect with credentials" else
          plan (afterRedirect (t.hopReferrer a) a.status next)
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

/-- Kind: lemma. Says: a `data:` or `blob:` URL never makes `plan` send anything (it is
answered in the engine, so the host is told nothing of it): every request `plan` sends is
`planNet`'s. -/
theorem plan_send_net {t t' : Transfer} {w : Wire} (h : plan t = .send t' w) : planNet t = .send t' w := by
  unfold plan at h
  split at h
  · unfold dataStep at h
    split at h
    · simp at h
    · split at h <;> simp at h
  · split at h
    · unfold blobStep at h
      split at h
      · simp at h
      · split at h
        · split at h
          · simp at h
          · split at h <;> simp at h
        · simp at h
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
                  · split at h
                    · simp at h
                    · split at h
                      · simp at h
                      · exact (plan_send_allowed _ _ _ h).2.2.1
          · simp at h

/-- Kind: policy theorem (redirect mode). Says: a transfer in redirect mode "error" whose
request has been sent follows no redirect: no answer makes `onAnswer` send another request.
Does not say: anything of the Hub (`hostCors`), where the browser that runs it follows
redirects itself, nor of the preflight and resolve steps before the request. -/
theorem onAnswer_redirect_error (t t' : Transfer) (a : Answer) (w : Wire)
    (hp : t.phase = .main) (hr : t.redirectError = true) : onAnswer t a ≠ .send t' w := by
  intro h
  unfold onAnswer at h
  simp only [hp, hr] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · split at h <;> simp at h
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

/-- Kind: security theorem (CORS). Says: on a native host, an answer to a cross-origin request
in a mode that is not "no-cors" reaches the page only after the CORS check passed. Does not
say: that the server's `Access-Control-Allow-Origin` is wise; and of mode "no-cors" it says
nothing (there the page gets an opaque response: `deliver_noCors_opaque`). -/
theorem deliver_cross_origin_needs_cors (t t' : Transfer) (a : Answer) (r : Response)
    (hn : t.page.hostCors = false) (hp : t.phase = .main) (hc : t.same = false) (hm : t.noCors = false)
    (h : onAnswer t a = .deliver t' r) : corsOk t a = true := by
  unfold onAnswer at h
  simp only [hp] at h
  by_cases hok : corsOk t a = true
  · exact hok
  · exfalso
    have hc' : (!t.page.hostCors && !t.same && !t.noCors && !corsOk t a) = true := by simp [hn, hc, hm, hok]
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp at h

/-- Kind: lemma. Says: `emit` never delivers: it sends or fails. -/
theorem emit_not_deliver (t : Transfer) (w : Wire) (t' : Transfer) (r : Response) : emit t w ≠ .deliver t' r := by
  unfold emit
  split
  · split <;> simp
  · split
    · simp
    · split <;> simp

/-- Kind: lemma. Says: `plan` answers in the engine (a `data:` or `blob:` URL) only for the
first URL of a request: after a redirect it sends or fails. -/
theorem plan_deliver_first (t t' : Transfer) (r : Response) (h : plan t = .deliver t' r) : t.redirects = 0 := by
  unfold plan at h
  split at h
  · unfold dataStep at h
    split at h
    · simp at h
    · rename_i hr
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hr
      exact hr.1
  · split at h
    · unfold blobStep at h
      split at h
      · simp at h
      · rename_i hr
        simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at hr
        exact hr.1
    · unfold planNet at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · split at h
            · exact absurd h (emit_not_deliver _ _ _ _)
            · exact absurd h (emit_not_deliver _ _ _ _)

/-- Kind: security theorem (opaque responses). Says: in mode "no-cors", on a native host, the
response the page gets for a request that is not same-origin is opaque: status 0, no reason
phrase, no field, no byte and no URL, whatever the server answered. Does not say: that the
request was not sent (it was: "no-cors" requests are the simple ones, `plan_noCors_simple`). -/
theorem responseOf_opaque (t : Transfer) (a : Answer) (hm : t.noCors = true) (hc : t.same = false)
    (hn : t.page.hostCors = false) :
    (responseOf t a).status = 0 ∧ (responseOf t a).statusText = "" ∧ (responseOf t a).url = "" ∧
      (responseOf t a).headers = [] ∧ (responseOf t a).body = ByteArray.empty ∧ (responseOf t a).tainting = "opaque" := by
  simp [responseOf, hm, hc, hn]

/-- Kind: security theorem (mode "no-cors", end to end). Says: what `onAnswer` delivers to the
page for a "no-cors" request that is not same-origin, on a native host, has status 0, no
field and no byte, and no URL but the one the request went to (an opaque response has
none; an opaque-redirect response, in redirect mode "manual", has the request's own):
nothing of the answer is readable. -/
theorem deliver_noCors_opaque (t t' : Transfer) (a : Answer) (r : Response)
    (hn : t.page.hostCors = false) (hp : t.phase = .main) (hc : t.same = false) (hm : t.noCors = true)
    (h : onAnswer t a = .deliver t' r) :
    r.status = 0 ∧ r.headers = [] ∧ r.body = ByteArray.empty ∧ (r.url = "" ∨ r.url = t.url) := by
  have ho := responseOf_opaque t a hm hc hn
  have fromResp : r = responseOf t a →
      r.status = 0 ∧ r.headers = [] ∧ r.body = ByteArray.empty ∧ (r.url = "" ∨ r.url = t.url) := by
    intro key
    rw [key]
    exact ⟨ho.1, ho.2.2.2.1, ho.2.2.2.2.1, Or.inl ho.2.2.1⟩
  unfold onAnswer at h
  simp only [hp] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · split at h
          · simp only [Step.deliver.injEq] at h
            exact fromResp h.2.symm
          · split at h
            · simp at h
            · split at h
              · simp only [Step.deliver.injEq] at h
                rw [← h.2]
                exact ⟨rfl, rfl, rfl, Or.inr rfl⟩
              · split at h
                · simp at h
                · split at h
                  · simp at h
                  · split at h
                    · simp at h
                    · have := plan_deliver_first _ _ _ h
                      simp [afterRedirect] at this
        · simp only [Step.deliver.injEq] at h
          exact fromResp h.2.symm

/-- Kind: security theorem (mode "no-cors" sends only simple requests). Says: a request that
`plan` sends in mode "no-cors" to a URL that is not same-origin has a CORS-safelisted method
and only CORS-safelisted fields of the page's (`needsPreflight` is false): the requests a
form or an image could make. Any other is refused, never sent without a preflight. -/
theorem plan_noCors_simple (t t' : Transfer) (w : Wire) (hm : t.noCors = true) (hc : t.same = false)
    (h : plan t = .send t' w) : t.needsPreflight = false := by
  replace h := plan_send_net h
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hx
        simpa [hm, hc] using hx

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
    · split at h
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

/-- Kind: lemma. Says: the `Origin` field, when there is one, is named `Origin`. -/
theorem mem_originField (t : Transfer) (n : String × String) (h : n ∈ t.originField) : n.1 = "Origin" := by
  unfold Transfer.originField at h
  split at h
  · simp at h; rw [h]
  · split at h
    · simp at h
    · simp at h; rw [h]

/-- Kind: lemma. Says: the `Cookie` field, when there is one, is named `Cookie` and has the
value `Transfer.cookieValue`, which is then not empty. -/
theorem mem_cookieField (t : Transfer) (n : String × String) (h : n ∈ t.cookieField) :
    n.1 = "Cookie" ∧ n.2 = t.cookieValue ∧ t.cookieValue ≠ "" := by
  unfold Transfer.cookieField at h
  split at h
  · simp at h
  · rename_i he
    simp only [List.mem_singleton] at h
    rw [h]
    exact ⟨rfl, rfl, fun h0 => he (by simp [h0])⟩

/-- Kind: lemma. Says: the fetch metadata fields have the three `Sec-Fetch-` names. -/
theorem mem_metadataFields (t : Transfer) (m : String) (n : String × String) (h : n ∈ t.metadataFields m) :
    n.1 = "Sec-Fetch-Dest" ∨ n.1 = "Sec-Fetch-Mode" ∨ n.1 = "Sec-Fetch-Site" := by
  unfold Transfer.metadataFields at h
  split at h
  · simp at h
  · split at h
    · split at h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> rw [h] <;> simp
      · simp at h
    · simp at h

/-- Kind: policy theorem. Says: every request `plan` tells the host to make carries no
page-set forbidden header: only `Origin`, `Cookie`, `Referer` and the three `Sec-Fetch-`
fields, which the engine adds, can be a forbidden name (on a preflight also the
`Access-Control-Request-` fields). Does not say: what the host adds on its own (a real fetch adds `Host` and so
on), nor what the `Referer` is (`plan_wire_referer`). -/
theorem plan_wire_forbidden (t : Transfer) (t' : Transfer) (w : Wire) (h : plan t = .send t' w)
    (n : String × String) (hn : n ∈ w.headers) (hf : forbiddenRequestHeader n.1 = true) :
    n.1 = "Origin" ∨ n.1 = "Cookie" ∨ n.1 = "Referer" ∨ n.1 = "Sec-Fetch-Dest" ∨ n.1 = "Sec-Fetch-Mode" ∨
      n.1 = "Sec-Fetch-Site" ∨ w.method = "OPTIONS" := by
  have eng : ∀ (x : Transfer) (m : String), n ∈ x.engineFields m →
      n.1 = "Referer" ∨ n.1 = "Sec-Fetch-Dest" ∨ n.1 = "Sec-Fetch-Mode" ∨ n.1 = "Sec-Fetch-Site" := by
    intro x m hm
    rcases List.mem_append.mp hm with hr | hr
    · left
      unfold Transfer.refererField at hr
      split at hr
      · simp at hr
      · simp at hr; rw [hr]
    · exact Or.inr (mem_metadataFields x m n hr)
  replace h := plan_send_net h
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, hm, -⟩
          · simp [Transfer.resolveWire] at hn
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by simp [hm, Transfer.preflightWire]))))))
        · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, -, hh, -⟩
          · simp [Transfer.resolveWire] at hn
          · rw [hh] at hn
            simp only [Transfer.mainWire] at hn
            rcases List.mem_append.mp hn with hn | hr
            · rcases List.mem_append.mp hn with hn | hc
              · rcases List.mem_append.mp hn with hl | ho
                · have := (List.mem_filter.mp hl).2
                  simp [hf] at this
                · exact Or.inl (mem_originField _ n ho)
              · exact Or.inr (Or.inl (mem_cookieField _ n hc).1)
            · rcases eng _ _ hr with h1 | h1 | h1 | h1
              · exact Or.inr (Or.inr (Or.inl h1))
              · exact Or.inr (Or.inr (Or.inr (Or.inl h1)))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h1)))))

/-- Kind: lemma. Says: the referer of a transfer does not depend on its phase. -/
theorem referer_phase (t : Transfer) (ph : Phase) : ({ t with phase := ph } : Transfer).referer = t.referer := rfl

/-- Kind: privacy theorem (the `Referer` on the wire). Says: a field named `Referer` of any
request `plan` tells the host to make, the preflight too, has the value `Transfer.referer`:
the request's referrer cut down by its policy for the URL the request goes to
(`referrerOf`), and never the empty string. `hf` holds for that name (a `#guard` below):
it is why no field of the page's can be the one. Does not say: that the request's referrer
and policy are the document's (that is `Net.Xhr.beginFetch` and the embedder's `client`),
nor what a host adds on its own. -/
theorem plan_wire_referer (t : Transfer) (t' : Transfer) (w : Wire) (h : plan t = .send t' w)
    (n : String × String) (hn : n ∈ w.headers) (hf : forbiddenRequestHeader n.1 = true)
    (hr : n.1 = "Referer") : n.2 = t.referer ∧ n.2 ≠ "" := by
  have last : ∀ (ph : Phase) (m : String), n ∈ ({ t with phase := ph } : Transfer).engineFields m →
      n.2 = t.referer ∧ n.2 ≠ "" := by
    intro ph m hm
    rcases List.mem_append.mp hm with hm | hm
    · unfold Transfer.refererField at hm
      rw [referer_phase] at hm
      split at hm
      · simp at hm
      · rename_i he
        simp only [List.mem_singleton] at hm
        rw [hm]
        exact ⟨rfl, fun h0 => he (by simpa using h0)⟩
    · exfalso
      rcases mem_metadataFields _ m n hm with h1 | h1 | h1 <;> rw [h1] at hr <;> simp at hr
  replace h := plan_send_net h
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, -, hh, -⟩
          · simp [Transfer.resolveWire] at hn
          · rw [hh] at hn
            simp only [Transfer.preflightWire] at hn
            rcases List.mem_append.mp hn with hn | hl
            · exfalso
              rcases List.mem_append.mp hn with hn | hn
              · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
                rcases hn with hn | hn | hn <;> rw [hn] at hr <;> simp at hr
              · split at hn
                · simp at hn
                · simp only [List.mem_singleton] at hn
                  rw [hn] at hr
                  simp at hr
            · exact last _ _ hl
        · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, -, hh, -⟩
          · simp [Transfer.resolveWire] at hn
          · rw [hh] at hn
            simp only [Transfer.mainWire] at hn
            rcases List.mem_append.mp hn with hn | hl
            · exfalso
              rcases List.mem_append.mp hn with hn | hc
              · rcases List.mem_append.mp hn with hl | ho
                · have := (List.mem_filter.mp hl).2
                  simp [hf] at this
                · have := mem_originField _ n ho
                  rw [this] at hr
                  simp at hr
              · have := (mem_cookieField _ n hc).1
                rw [this] at hr
                simp at hr
            · exact last _ _ hl

/-- Kind: privacy theorem (credentials). Says: a hop that is not made with credentials has no
cookie value: a request to another origin without `credentials: "include"` (or
`withCredentials`), any request in mode "omit", and every request on the Hub carry none. -/
theorem cookieValue_needs_credentials (t : Transfer) (h : t.sendsCredentials = false) : t.cookieValue = "" := by
  simp [Transfer.cookieValue, h]

/-- Kind: privacy theorem (credentials). Says: the answer to a hop that is not made with
credentials stores no cookie, whatever `Set-Cookie` fields it has. -/
theorem storeCookies_needs_credentials (t : Transfer) (jar : Cookies.Jar) (a : Answer)
    (h : t.sendsCredentials = false) : t.storeCookies jar a = jar := by
  simp [Transfer.storeCookies, h]

theorem foldl_setIn_keeps_host (site : Cookies.Site) (now : Nat) (ss : Bool) (hs : List (String × String))
    (jar : Cookies.Jar) (c : Cookies.Cookie)
    (h : c ∈ (hs.foldl (fun j (f : String × String) =>
      if lower f.1 == "set-cookie" then Cookies.setFromHeaderIn j site now ss f.2 else j) jar).cookies) :
    (∃ o ∈ jar.cookies, o.host = c.host) ∨ c.host = site.host := by
  induction hs generalizing jar with
  | nil => exact .inl ⟨c, h, rfl⟩
  | cons f rest ih =>
    simp only [List.foldl_cons] at h
    rcases ih _ h with ⟨o, ho, hh⟩ | hh
    · split at ho
      · rcases Cookies.setFromHeaderIn_keeps_host jar site now ss f.2 o ho with ⟨o', ho', -, -, hh', -⟩ | hh''
        · exact .inl ⟨o', ho', hh'.trans hh⟩
        · exact .inr (hh.symm.trans hh'')
      · exact .inl ⟨o, ho, hh⟩
    · exact .inr hh

/-- Kind: privacy invariant (cookies are their host's, network side). Says: after the answer
to a hop, every cookie of the jar was there before (for its host) or is for the host of the
URL that hop went to: a response never sets a cookie for another host. -/
theorem storeCookies_keeps_host (t : Transfer) (jar : Cookies.Jar) (a : Answer) (c : Cookies.Cookie)
    (h : c ∈ (t.storeCookies jar a).cookies) :
    (∃ o ∈ jar.cookies, o.host = c.host) ∨ ∃ site, (URL.parseUrl t.url).bind cookieSite = some site ∧ c.host = site.host := by
  unfold Transfer.storeCookies at h
  split at h
  · exact .inl ⟨c, h, rfl⟩
  · split at h
    · exact .inl ⟨c, h, rfl⟩
    · rename_i site hs
      rcases foldl_setIn_keeps_host site t.now (t.site ≤ 1) a.headers jar c h with h1 | h1
      · exact .inl h1
      · exact .inr ⟨site, hs, h1⟩

/-- Kind: privacy theorem (credentials across origins). Says: a hop to a URL that is not of
the page's origin (or after the request left it) is made with credentials only when the
page asked for them (`credentials`), and never in mode "omit". -/
theorem sendsCredentials_cross (t : Transfer) (hc : t.same = false) (h : t.sendsCredentials = true) :
    t.credentials = true ∧ t.omitCredentials = false := by
  simp only [Transfer.sendsCredentials, hc, Bool.or_false, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  exact ⟨h.2, h.1.1⟩

/-- Kind: privacy theorem (preflights). Says: a CORS preflight carries no `Cookie` field,
whatever the jar holds and whatever the credentials mode (Fetch §4.8: a preflight is made
without credentials). -/
theorem preflight_no_cookie (t : Transfer) (n : String × String) (hn : n ∈ t.preflightWire.headers) :
    n.1 ≠ "Cookie" := by
  intro hc
  simp only [Transfer.preflightWire] at hn
  rcases List.mem_append.mp hn with hn | hn
  · rcases List.mem_append.mp hn with hn | hn
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with hn | hn | hn <;> rw [hn] at hc <;> simp at hc
    · split at hn
      · simp at hn
      · simp only [List.mem_singleton] at hn
        rw [hn] at hc
        simp at hc
  · rcases List.mem_append.mp hn with hn | hn
    · unfold Transfer.refererField at hn
      split at hn
      · simp at hn
      · simp only [List.mem_singleton] at hn
        rw [hn] at hc
        simp at hc
    · rcases mem_metadataFields _ _ n hn with h1 | h1 | h1 <;> rw [h1] at hc <;> simp at hc

/-- Kind: privacy theorem (the `Cookie` on the wire). Says: a field named `Cookie` of a request
`plan` tells the host to make is not the page's (`hf`: the name is forbidden to it) and is
never on a preflight; its value is `Transfer.cookieValue`: the cookies the jar holds for
exactly the host the request goes to (`Cookies.sent_host`), and only when the hop is made
with credentials. Does not say: that the host sends nothing else (a host must not add its
own cookies). -/
theorem plan_wire_cookie (t : Transfer) (t' : Transfer) (w : Wire) (h : plan t = .send t' w)
    (n : String × String) (hn : n ∈ w.headers) (hf : forbiddenRequestHeader n.1 = true)
    (hc : n.1 = "Cookie") : t'.phase = .main ∧ n.2 = t.cookieValue ∧ t.sendsCredentials = true := by
  have val : ∀ (ph : Phase), n ∈ ({ t with phase := ph } : Transfer).cookieField →
      n.2 = t.cookieValue ∧ t.sendsCredentials = true := by
    intro ph hm
    have hv := mem_cookieField _ n hm
    have e : ({ t with phase := ph } : Transfer).cookieValue = t.cookieValue := rfl
    rw [e] at hv
    refine ⟨hv.2.1, ?_⟩
    cases hs : t.sendsCredentials
    · exact absurd (cookieValue_needs_credentials t hs) hv.2.2
    · rfl
  replace h := plan_send_net h
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · rcases emit_cases h with ⟨-, rfl⟩ | ⟨-, -, -, hh, -⟩
          · simp [Transfer.resolveWire] at hn
          · rw [hh] at hn
            exact absurd hc (preflight_no_cookie _ n hn)
        · rcases emit_cases h with ⟨-, rfl⟩ | ⟨ht, -, -, hh, -⟩
          · simp [Transfer.resolveWire] at hn
          · rw [hh] at hn
            simp only [Transfer.mainWire] at hn
            rcases List.mem_append.mp hn with hn | hl
            · rcases List.mem_append.mp hn with hn | hck
              · exfalso
                rcases List.mem_append.mp hn with hl | ho
                · have := (List.mem_filter.mp hl).2
                  simp [hf] at this
                · have := mem_originField _ n ho
                  rw [this] at hc
                  simp at hc
              · rw [ht]
                exact ⟨rfl, val _ hck⟩
            · exfalso
              rcases List.mem_append.mp hl with hr | hm
              · unfold Transfer.refererField at hr
                split at hr
                · simp at hr
                · simp only [List.mem_singleton] at hr
                  rw [hr] at hc
                  simp at hc
              · rcases mem_metadataFields _ _ n hm with h1 | h1 | h1 <;> rw [h1] at hc <;> simp at hc

/-- Kind: security theorem (fetch metadata). Says: a request says `Sec-Fetch-Site:
same-origin` only when no earlier URL of the request left the page's origin and the URL it
goes to is of the page's origin: a server that trusts `same-origin` is never told so of a
request that passed through another origin. Does not say: what `same-site` means beyond
this engine's narrow reading (`siteRank`). -/
theorem site_same_origin (t : Transfer) (h : siteToken t.site = "same-origin") :
    t.farthest = 0 ∧ ∀ u, URL.parseUrl t.url = some u → sameOrigin t.page u = true := by
  have h0 : t.site = 0 := by
    cases hs : t.site with
    | zero => rfl
    | succ k =>
      rw [hs] at h
      cases k with
      | zero => simp [siteToken] at h
      | succ j => simp [siteToken] at h
  unfold Transfer.site at h0
  have hf : t.farthest = 0 := by omega
  refine ⟨hf, ?_⟩
  intro u hu
  rw [hu] at h0
  simp only at h0
  have hr : siteRank t.page u = 0 := by omega
  unfold siteRank at hr
  split at hr
  · assumption
  · split at hr
    · split at hr <;> simp at hr
    · simp at hr

/-- Kind: lemma (redirects). Says: a redirect never brings a request nearer: the farthest the
request has been from the page only grows, so `cross-site` once is `cross-site` for the
rest of the chain. -/
theorem afterRedirect_farthest (t : Transfer) (s : Nat) (n : URL.Url) :
    t.farthest ≤ (afterRedirect t s n).farthest := by
  simp only [afterRedirect, Transfer.site]
  exact Nat.le_max_left _ _

/-- Kind: privacy theorem (the bound on a referrer). Says: whatever the policy, the source
and the target, a referrer is nothing, the source's origin with `/` (no path, no query), or
the source without credentials and fragment. Nothing else is ever sent. -/
theorem referrerOf_cases (p : ReferrerPolicy.Policy) (source : String) (target : URL.Url) :
    referrerOf p source target = "" ∨
      ∃ s, URL.parseUrl source = some s ∧
        (referrerOf p source target = referrerOrigin s ∨ referrerOf p source target = referrerFull s) := by
  cases hp : URL.parseUrl source with
  | none => exact Or.inl (by simp [referrerOf, hp])
  | some s =>
    unfold referrerOf
    rw [hp]
    simp only
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr ⟨s, rfl, Or.inl rfl⟩
      · split
        · exact Or.inr ⟨s, rfl, Or.inl rfl⟩
        · exact Or.inr ⟨s, rfl, Or.inr rfl⟩

/-- Kind: privacy theorem (the default policy, cross-origin). Says: under
`strict-origin-when-cross-origin` a request to another origin carries at most the source's
origin: nothing, or the origin with `/`. No path and no query of the page that asks reach
another origin. -/
theorem referrerOf_default_cross (source : String) (s target : URL.Url)
    (hs : URL.parseUrl source = some s) (hc : s.origin ≠ target.origin) :
    referrerOf .strictOriginWhenCrossOrigin source target = "" ∨
      referrerOf .strictOriginWhenCrossOrigin source target = referrerOrigin s := by
  have hne : (s.origin == target.origin) = false := by simpa using hc
  unfold referrerOf
  rw [hs]
  simp only [hne, ReferrerPolicy.decide]
  split
  · exact Or.inl rfl
  · cases (trustworthyUrl s && !trustworthyUrl target) <;> simp

/-- Kind: privacy theorem (downgrade). Says: under the default policy, `strict-origin` and
`no-referrer-when-downgrade`, a request from a trustworthy source to a target that is not
(`https` to `http`) carries no referrer at all. -/
theorem referrerOf_downgrade (p : ReferrerPolicy.Policy) (source : String) (s target : URL.Url)
    (hs : URL.parseUrl source = some s) (ht : trustworthyUrl s = true) (hu : trustworthyUrl target = false)
    (ho : s.origin ≠ target.origin)
    (hp : p = .strictOrigin ∨ p = .strictOriginWhenCrossOrigin ∨ p = .noReferrerWhenDowngrade) :
    referrerOf p source target = "" := by
  have hne : (s.origin == target.origin) = false := by simpa using ho
  unfold referrerOf
  rw [hs]
  rcases hp with hp | hp | hp <;> subst hp <;> simp [ReferrerPolicy.decide, ht, hu, hne]

/-- Kind: privacy theorem. Says: `no-referrer` sends nothing, and `same-origin` sends nothing
to another origin. -/
theorem referrerOf_none (source : String) (target : URL.Url) :
    referrerOf .noReferrer source target = "" ∧
      (∀ s, URL.parseUrl source = some s → s.origin ≠ target.origin →
        referrerOf .sameOrigin source target = "") := by
  constructor
  · unfold referrerOf
    split
    · rfl
    · split <;> simp [ReferrerPolicy.decide]
  · intro s hs ho
    have hne : (s.origin == target.origin) = false := by simpa using ho
    unfold referrerOf
    rw [hs]
    simp [ReferrerPolicy.decide, hne]

/-- Kind: privacy theorem. Says: a request with no referrer (`""`: the page asked for none,
or the client has no URL to give) never gets one, under any policy. -/
theorem referrerOf_empty (p : ReferrerPolicy.Policy) (target : URL.Url)
    (h : URL.parseUrl "" = none) : referrerOf p "" target = "" := by
  unfold referrerOf
  rw [h]

/-- Kind: lemma. Says: the Hub's requests get no `Referer` from here. -/
theorem referer_hostCors (t : Transfer) (h : t.page.hostCors = true) : t.referer = "" := by
  simp [Transfer.referer, h]

/-- Kind: invariant of the response filter. Says: no response the page reads has a
`Set-Cookie` or `Set-Cookie2` field. Does not say: anything of the host's own cookie jar
(no host here has one: no cookie is sent or stored). -/
theorem responseOf_no_set_cookie (t : Transfer) (a : Answer) (n : String × String)
    (hn : n ∈ (responseOf t a).headers) : forbiddenResponseHeader n.1 = false := by
  unfold responseOf at hn
  split at hn
  · simp at hn
  · simp only at hn
    split at hn
    · have := (List.mem_filter.mp hn).2
      simpa using this
    · have := (List.mem_filter.mp (List.mem_filter.mp hn).1).2
      simpa using this

/-- Kind: security theorem (CORS check, Fetch §4.9 steps 3 and 4). Says: for a request made
with credentials (`withCredentials`, fetch `credentials: "include"`), an answer whose
`Access-Control-Allow-Origin` is the wildcard `*` fails the check: a response is never shared
with a credentialed request on a wildcard. Does not say: that the engine sends credentials
(it sends none: no cookies, no HTTP authentication), nor anything of the preflight's method
and header lists (`preflightOk` refuses their wildcards with credentials in its own text).
The hypothesis `t.originValue ≠ "*"` holds for every origin (a serialized origin or
`"null"`). -/
theorem corsOk_credentials_wildcard (t : Transfer) (a : Answer) (hc : t.credentials = true)
    (hw : (headerGet a.headers "access-control-allow-origin").map trimWs = some "*")
    (ho : t.originValue ≠ "*") : corsOk t a = false := by
  unfold corsOk
  cases h : headerGet a.headers "access-control-allow-origin" with
  | none => rfl
  | some v =>
    rw [h] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    have hne : ("*" == t.originValue) = false := by
      simpa using Ne.symm ho
    simp [hc, hw, hne]

/-- Kind: security theorem (CORS check). Says: an answer with no `Access-Control-Allow-Origin`
field never passes the check, with or without credentials. Does not say: anything of
same-origin requests (the check is not asked for them, `onAnswer`). -/
theorem corsOk_needs_header (t : Transfer) (a : Answer)
    (h : headerGet a.headers "access-control-allow-origin" = none) : corsOk t a = false := by
  simp [corsOk, h]

/-- Kind: policy lemma (workers). Says: a dedicated worker's request policy is its owner's
in everything but the origin: the same local, secure (mixed content) and `hostCors`
settings, so `mayConnect` answers the same for a worker as for its owner. Does not say:
anything of the origin (`forWorker_origin`), or that the host gives the worker this policy
(that is `LeanJSWorkers.workerHost_net_page`). -/
theorem forWorker_policy (owner : Page) (url : String) :
    (owner.forWorker url).isLocal = owner.isLocal ∧ (owner.forWorker url).secure = owner.secure ∧
      (owner.forWorker url).hostCors = owner.hostCors := by
  unfold Page.forWorker; split <;> simp

/-- Kind: policy lemma (workers). Says: `mayConnect` of a worker's policy is its owner's,
for every URL. Does not say: that the worker's requests are the same as the owner's
(CORS depends on the origin). -/
theorem forWorker_mayConnect (owner : Page) (url : String) (u : URL.Url) :
    mayConnect (owner.forWorker url) u = mayConnect owner u := by
  unfold Page.forWorker; split <;> rfl

/-- Kind: policy lemma (workers). Says: a worker's requests carry its owner's origin, unless
the worker's script is a `data:` URL, whose origin is opaque (`"null"`). Never another
origin. Does not say: that the worker's URL is same-origin with the owner (the `Worker`
constructor checks that). -/
theorem forWorker_origin (owner : Page) (url : String) :
    (owner.forWorker url).origin = owner.origin ∨ (owner.forWorker url).origin = "null" := by
  unfold Page.forWorker; split
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- Kind: policy lemma (workers). Says: a worker whose script URL is not `data:` has exactly
its owner's policy. Does not say: anything of `blob:` URLs beyond that they are not `data:`. -/
theorem forWorker_not_data (owner : Page) (url : String) (h : url.startsWith "data:" = false) :
    owner.forWorker url = owner := by
  simp [Page.forWorker, h]

/-! ## Checks (`#guard` is a test) -/

/-- Kind: memory safety of a range read. Says: the positions that `blobRange` names are inside
the blob, first before last: a `Range` request for a blob URL never reads past the blob's
bytes. Does not say: that the header parsed (`singleRange`). -/
theorem blobRange_within (full : Nat) (r : Option Nat × Option Nat) (first last : Nat)
    (h : blobRange full r = some (first, last)) : first ≤ last ∧ last < full := by
  unfold blobRange at h
  split at h
  · split at h
    · simp at h
    · rename_i hz
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le, Nat.not_lt] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
  · split at h
    · simp at h
    · rename_i hz
      simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hz
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      omega
  · simp at h

#guard singleRange "bytes=0-9" == some (some 0, some 9)
#guard singleRange "bytes = 5 - " == some (some 5, none)
#guard singleRange "bytes=-4" == some (none, some 4)
#guard singleRange "bytes=9-0" == none && singleRange "bytes=-" == none && singleRange "bytes=1-2,3-4" == none
#guard singleRange "items=0-9" == none && singleRange "bytes0-9" == none
#guard blobRange 10 (some 2, some 5) == some (2, 5) && blobRange 10 (some 2, some 50) == some (2, 9)
#guard blobRange 10 (some 2, none) == some (2, 9) && blobRange 10 (none, some 3) == some (7, 9)
#guard blobRange 10 (none, some 30) == some (0, 9) && blobRange 10 (some 10, none) == none && blobRange 0 (none, some 1) == none

private def pg : Page := Page.ofUrl "https://a.example/x"
/-- The fields of a wire without the fetch metadata (checked on their own below). -/
private def plain (w : Wire) : List (String × String) := w.headers.filter fun (n, _) => !(lower n).startsWith "sec-fetch-"

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
-- special addresses however the URL writes them: the URL parser normalizes IPv4 forms
#guard ["http://[::1]/", "http://0.0.0.0/", "http://127.1/", "http://0x7f.0.0.1/", "http://[::ffff:127.0.0.1]/",
  "http://localhost./", "http://a.localhost/", "http://169.254.169.254/", "http://10.0.0.1/", "http://[fe80::1]/"].all
  fun s => (URL.parseUrl s).any privateHost
#guard !(URL.parseUrl "http://93.184.215.14/").any privateHost
-- a method-override field naming a forbidden method never reaches the wire
private def overridden : Transfer :=
  { id := 1, page := pg, method := "POST", url := "https://a.example/y", body := none,
    headers := [("X-HTTP-Method-Override", "TRACE"), ("X-A", "1")] }
#guard plain overridden.mainWire == [("X-A", "1"), ("Origin", "https://a.example")]
#guard safeHeader "Content-Type" "text/plain;charset=UTF-8" && !safeHeader "Content-Type" "application/json"
#guard unsafeHeaderNames [("X-B", "1"), ("x-a", "2"), ("Accept", "*/*")] == ["x-a", "x-b"]

private def base : Transfer :=
  { id := 1, page := pg, method := "GET", url := "https://b.example/d", headers := [], body := none,
    pin := some ("b.example", "93.184.215.14") }

private def planWire (t : Transfer) : Option Wire :=
  match plan t with | .send _ w => some w | _ => none

#guard (planWire base).any fun w => w.method == "GET" && plain w == [("Origin", "https://a.example")]
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
-- redirect mode "error": a redirect is a network error; followed without it
#guard match onAnswer { base with url := "https://a.example/y", redirectError := true } ({ status := 302, headers := [("Location", "/z")] } : Answer) with | .fail _ => true | _ => false
#guard match onAnswer { base with url := "https://a.example/y" } ({ status := 302, headers := [("Location", "/z")] } : Answer) with | .send _ _ => true | _ => false
-- a redirect is checked again: same-origin to a local address is refused
#guard match onAnswer { base with url := "https://a.example/y" } ({ status := 302, headers := [("Location", "http://127.0.0.1/")] } : Answer) with
  | .fail _ => true | _ => false

-- a worker's requests: the owner's origin, or "null" for a data: worker
#guard (pg.forWorker "https://a.example/w.js").origin == "https://a.example"
#guard (pg.forWorker "data:text/javascript,1").origin == "null" && (pg.forWorker "data:,").secure
-- a data: worker's cross-origin request carries Origin: null, its owner's the owner's origin
#guard (planWire { base with page := pg.forWorker "data:," }).any fun w => plain w == [("Origin", "null")]
#guard (planWire { base with page := pg.forWorker "https://a.example/w.js" }).any fun w => plain w == [("Origin", "https://a.example")]


-- The referrer (WPT fetch/api/basic/referrer.any.js, fetch/api/redirect/redirect-referrer.any.js,
-- fetch/api/cors/cors-preflight-referrer.any.js, referrer-policy/generic/test-case.sub.js)
#guard forbiddenRequestHeader "Referer"
private def src : String := "http://web-platform.test:8000/fetch/api/basic/referrer.any.html?q=1#f"
private def tgt (s : String) : URL.Url := (URL.parseUrl s).getD default
#guard referrerOf .default src (tgt "http://web-platform.test:8000/x") == "http://web-platform.test:8000/fetch/api/basic/referrer.any.html?q=1"
#guard referrerOf .default src (tgt "http://www1.web-platform.test:8000/x") == "http://web-platform.test:8000/"
#guard referrerOf .originWhenCrossOrigin src (tgt "http://web-platform.test:8000/x") == "http://web-platform.test:8000/fetch/api/basic/referrer.any.html?q=1"
#guard referrerOf .originWhenCrossOrigin src (tgt "http://www1.web-platform.test:8000/x") == "http://web-platform.test:8000/"
#guard referrerOf .noReferrer src (tgt "http://web-platform.test:8000/x") == ""
#guard referrerOf .sameOrigin src (tgt "http://www1.web-platform.test:8000/x") == ""
#guard referrerOf .unsafeUrl src (tgt "http://www1.web-platform.test:8000/x") == "http://web-platform.test:8000/fetch/api/basic/referrer.any.html?q=1"
-- "Referrer with credentials should be stripped", "Referrer with fragment ID should be stripped"
#guard referrerOf .default "http://username:password@web-platform.test:8000" (tgt "http://web-platform.test:8000/x") == "http://web-platform.test:8000/"
#guard referrerOf .default "http://web-platform.test:8000#fragmentIdentifier" (tgt "http://web-platform.test:8000/x") == "http://web-platform.test:8000/"
-- a downgrade: nothing under the default, the origin under `origin`, all under `unsafe-url`
#guard referrerOf .default "https://a.example/p?q" (tgt "http://b.example/") == ""
#guard referrerOf .strictOrigin "https://a.example/p?q" (tgt "http://b.example/") == ""
#guard referrerOf .noReferrerWhenDowngrade "https://a.example/p?q" (tgt "http://b.example/") == ""
#guard referrerOf .origin "https://a.example/p?q" (tgt "http://b.example/") == "https://a.example/"
#guard referrerOf .noReferrerWhenDowngrade "https://a.example/p?q" (tgt "https://b.example/") == "https://a.example/p?q"
-- a loopback target is trustworthy: no downgrade (a name that only starts like one is not)
#guard referrerOf .strictOrigin "https://a.example/p" (tgt "http://127.0.0.1:8000/") == "https://a.example/"
#guard referrerOf .strictOrigin "https://a.example/p" (tgt "http://127.example.com/") == ""
-- only http and https sources: no about:, blob:, data: or file: referrer, and none from ""
#guard ["about:blank", "about:srcdoc", "data:text/html,x", "blob:https://a.example/0a", "file:///home/u/secret.html", ""].all
  fun s => referrerOf .unsafeUrl s (tgt "https://b.example/") == ""
-- a referrer over 4096 characters is cut to its origin (referrer-policy/4K+1)
#guard referrerOf .unsafeUrl ("https://a.example/" ++ String.ofList (List.replicate 4096 'A')) (tgt "https://a.example/") == "https://a.example/"
#guard (referrerOf .unsafeUrl ("https://a.example/" ++ String.ofList (List.replicate 4078 'A')) (tgt "https://a.example/")).length == 4096
-- on the wire: the request and its preflight carry it; a request with no referrer has none
private def refd : Transfer := { base with referrer := "https://a.example/dir/page.html?q#f" }
#guard (planWire refd).any fun w => plain w == [("Origin", "https://a.example"), ("Referer", "https://a.example/")]
#guard (planWire { refd with url := "https://a.example/y", pin := some ("a.example", "93.184.215.14") }).any
  fun w => plain w == [("Referer", "https://a.example/dir/page.html?q")]
#guard (planWire { refd with headers := [("X-A", "1")], referrerPolicy := .unsafeUrl }).any
  fun w => w.method == "OPTIONS" && headerGet w.headers "referer" == some "https://a.example/dir/page.html?q"
#guard (planWire { refd with page := { pg with hostCors := true } }).any fun w => headerGet w.headers "referer" == none
-- a page's own Referer field never reaches the wire
#guard (planWire { base with url := "https://a.example/y", pin := some ("a.example", "93.184.215.14"), headers := [("Referer", "https://evil.example/")] }).any
  fun w => (plain w).isEmpty
-- a redirect: the policy of the redirect response is the next hop's (redirect-referrer.any.js:
-- "Same origin redirection, empty init, origin redirect header"), and a hop back to the first
-- origin after a cross-origin one gets the origin only (referrer.any.js, last case)
private def hop (t : Transfer) (a : Answer) : Option Wire :=
  match onAnswer t a with | .send _ w => some w | _ => none
private def sameT : Transfer := { refd with url := "https://a.example/redirect", pin := some ("a.example", "93.184.215.14") }
#guard (hop sameT { status := 302, headers := [("Location", "/next"), ("Referrer-Policy", "origin")] }).any
  fun w => headerGet w.headers "referer" == some "https://a.example/"
#guard (hop sameT { status := 302, headers := [("Location", "/next"), ("Referrer-Policy", "no-referrer")] }).any
  fun w => headerGet w.headers "referer" == none
#guard (hop sameT { status := 302, headers := [("Location", "/next")] }).any
  fun w => headerGet w.headers "referer" == some "https://a.example/dir/page.html?q"
#guard (hop { refd with referrerPolicy := .originWhenCrossOrigin, page := { pg with isLocal := true } }
    { status := 302, headers := [("Location", "https://a.example/back"), ("Access-Control-Allow-Origin", "*")] }).any
  fun w => headerGet w.headers "referer" == some "https://a.example/"


-- Fetch metadata (WPT fetch/metadata/fetch.https.sub.any.js, generated/fetch.https.sub.html):
-- only to a trustworthy URL; site, mode and destination
private def metaOf (t : Transfer) : List (String × String) :=
  ((planWire t).map fun w => w.headers.filter fun (n, _) => (lower n).startsWith "sec-fetch-").getD []
private def sameT' : Transfer := { base with url := "https://a.example/y", pin := some ("a.example", "93.184.215.14") }
#guard metaOf sameT' == [("Sec-Fetch-Dest", "empty"), ("Sec-Fetch-Mode", "cors"), ("Sec-Fetch-Site", "same-origin")]
#guard metaOf base == [("Sec-Fetch-Dest", "empty"), ("Sec-Fetch-Mode", "cors"), ("Sec-Fetch-Site", "cross-site")]
#guard metaOf { sameT' with url := "https://a.example:8443/y" } == [("Sec-Fetch-Dest", "empty"), ("Sec-Fetch-Mode", "cors"), ("Sec-Fetch-Site", "same-site")]
#guard metaOf { sameT' with sameOriginOnly := true } == [("Sec-Fetch-Dest", "empty"), ("Sec-Fetch-Mode", "same-origin"), ("Sec-Fetch-Site", "same-origin")]
#guard metaOf { base with noCors := true } == [("Sec-Fetch-Dest", "empty"), ("Sec-Fetch-Mode", "no-cors"), ("Sec-Fetch-Site", "cross-site")]
-- no public suffix list: a subdomain is cross-site here (a browser with the list says same-site)
#guard metaOf { sameT' with url := "https://www.a.example/y", pin := some ("www.a.example", "93.184.215.14") }
  == [("Sec-Fetch-Dest", "empty"), ("Sec-Fetch-Mode", "cors"), ("Sec-Fetch-Site", "cross-site")]
-- an http target that is not loopback gets none; the Hub's requests get none
#guard metaOf { named with pin := some ("b.example", "93.184.215.14"), headers := [] } == []
#guard metaOf { sameT' with page := { pg with hostCors := true } } == []
-- a preflight says mode cors
#guard (planWire { base with headers := [("X-A", "1")] }).any fun w => headerGet w.headers "sec-fetch-mode" == some "cors"
-- "Same-Origin -> Cross-Site -> Same-Origin redirect": cross-site at the end (the page is
-- local here so that no name is resolved)
private def lp : Page := { pg with isLocal := true }
#guard (hop { sameT' with page := lp } { status := 302, headers := [("Location", "https://b.example/r"), ("Access-Control-Allow-Origin", "*")] }).any
  fun w => headerGet w.headers "sec-fetch-site" == some "cross-site"
private def twoHops : Option Wire :=
  match onAnswer { sameT' with page := lp, noCors := true } { status := 302, headers := [("Location", "https://b.example/r")] } with
  | .send t _ => hop t { status := 302, headers := [("Location", "https://a.example/z")] }
  | _ => none
#guard twoHops.any fun w => headerGet w.headers "sec-fetch-site" == some "cross-site" && w.url == "https://a.example/z"
#guard (hop { sameT' with page := lp } { status := 302, headers := [("Location", "/z")] }).any
  fun w => headerGet w.headers "sec-fetch-site" == some "same-origin"

-- Mode "no-cors" (WPT fetch/api/basic/mode-no-cors.sub.any.js, fetch/api/cors/cors-no-preflight):
-- a simple cross-origin request goes out with no Origin and no preflight; its answer is opaque
#guard (planWire { base with noCors := true }).any fun w => w.method == "GET" && (plain w).isEmpty
#guard (planWire { base with noCors := true, headers := [("X-A", "1")] }).isNone
#guard (planWire { base with noCors := true, method := "PUT" }).isNone
#guard match onAnswer { base with noCors := true } ({ status := 200, headers := [("X-S", "1")], body := "secret".toUTF8 } : Answer) with
  | .deliver _ r => r.status == 0 && r.headers.isEmpty && r.body.size == 0 && r.url == "" && r.tainting == "opaque" | _ => false
-- same-origin in mode no-cors: a basic response, all of it
#guard match onAnswer { sameT' with noCors := true } ({ status := 200, headers := [("X-S", "1")], body := "x".toUTF8 } : Answer) with
  | .deliver _ r => r.status == 200 && r.tainting == "basic" && r.body.size == 1 | _ => false
#guard match onAnswer base (corsAns "*") with | .deliver _ r => r.tainting == "cors" | _ => false
-- Origin on a request that is not GET or HEAD outside the CORS check (WPT fetch/origin/assorted.window.js):
-- null under no-referrer, and for a no-cors request to another origin under same-origin
private def originOf' (t : Transfer) : Option String := (planWire t).bind fun w => headerGet w.headers "origin"
#guard originOf' { sameT' with method := "POST" } == some "https://a.example"
#guard originOf' { sameT' with method := "POST", referrerPolicy := .noReferrer } == some "null"
#guard originOf' { base with method := "POST", noCors := true } == some "https://a.example"
#guard originOf' { base with method := "POST", noCors := true, referrerPolicy := .sameOrigin } == some "null"
#guard originOf' { base with method := "POST", referrerPolicy := .noReferrer } == some "https://a.example"

-- redirect mode "manual" (WPT fetch/api/redirect/redirect-mode.any.js): an opaque-redirect
-- response, nothing followed
#guard match onAnswer { sameT' with redirectManual := true } ({ status := 302, headers := [("Location", "/z"), ("X-S", "1")] } : Answer) with
  | .deliver _ r => r.status == 0 && r.headers.isEmpty && r.tainting == "opaqueredirect" && r.url == "https://a.example/y" | _ => false
#guard match onAnswer { sameT' with redirectManual := true } ({ status := 200, headers := [("X-S", "1")] } : Answer) with
  | .deliver _ r => r.status == 200 && r.tainting == "basic" | _ => false

end L4Factoidal.Net.PageFetch
