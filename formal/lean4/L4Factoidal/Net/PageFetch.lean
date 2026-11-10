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

* Schemes: `http` and `https` only. A page never reads `file:`, `about:` or a host's other
  schemes (`mayConnect`).
* Local addresses: a target that is `localhost`, a `.localhost` name or a special-purpose
  IP literal (`Egress.specialPurpose`) is reached only by a page whose own origin is local.
  A page from the network or from `file:` gets no path to the machine it runs on. This is
  a decision on the name in the URL; DNS rebinding is the host's to stop (not done).
* Mixed content: an `https` page reads `https` only.
* Cross-origin: refused unless CORS allows it. A request outside the CORS-safelist has a
  preflight first (every hop); the response of a cross-origin request is withheld unless the
  CORS check passes; only the safelisted and exposed header fields reach the page.
* No credentials: no cookies, no HTTP authentication, no client certificates are ever sent
  (`Cookie`, `Authorization` set by the host never exist here). `withCredentials` changes
  only the CORS check, not what is sent. A URL's user and password are removed.
* A host cannot tell a page what a redirect does: redirects are the engine's (the host gets
  redirect "manual" natively, `Step.send` for each hop with the policy checked again).
* On the Hub (`hostCors`), the browser that runs the Hub enforces its own CORS for its
  own origin: the host follows redirects and preflights. The private-host and scheme rules
  still apply.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Net.Egress

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

/-- The page from its URL. -/
def Page.ofUrl (url : String) (hostCors : Bool := false) : Page :=
  match URL.parseUrl url with
  | some u => { origin := u.origin, isLocal := privateHost u, secure := u.scheme == "https", hostCors }
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
  deriving Inhabited

/-- The host's answer to a `Wire`: `status` 0 is a network failure. -/
structure Answer where
  status : Nat := 0
  statusText : String := ""
  headers : List (String × String) := []
  body : ByteArray := ByteArray.empty
  /-- The final URL when the host followed redirects itself (the Hub). -/
  url : String := ""
  deriving Inhabited

/-- A response the page may read. -/
structure Response where
  status : Nat
  statusText : String
  url : String
  headers : List (String × String)
  body : ByteArray
  deriving Inhabited

inductive Phase where
  | preflight
  | main
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

/-- What a step asks for. -/
inductive Step where
  /-- Tell the host to make this request. -/
  | send (t : Transfer) (w : Wire)
  /-- The page may read this. -/
  | deliver (t : Transfer) (r : Response)
  /-- A network error: the page learns nothing else. -/
  | fail (why : String)
  deriving Inhabited

/-- Plan the current URL: refuse it outside the policy, or send the preflight when one is
needed, or send the request. -/
def plan (t : Transfer) : Step :=
  if !t.allowed then .fail "refused by policy"
  else if t.sameOriginOnly && !t.same then .fail "refused by mode same-origin"
  else if !t.page.hostCors && !t.same && t.needsPreflight then
    let t' := { t with phase := .preflight }
    .send t' t'.preflightWire
  else
    let t' := { t with phase := .main }
    .send t' t'.mainWire

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
  let crossed := t.crossed ||
    (match URL.parseUrl t.url with
     | some cur => cur.origin != next.origin && !sameOrigin t.page cur
     | none => true)
  { t with url := nextUrl.serialize true, redirects := t.redirects + 1, crossed,
           method := if toGet then "GET" else t.method,
           body := if toGet then none else t.body,
           headers := if toGet then t.headers.filter (!bodyHeader ·.1) else t.headers }

/-- The host's answer: refuse it, deliver it, or send the next hop. -/
def onAnswer (t : Transfer) (a : Answer) : Step :=
  if a.status == 0 then .fail "network error" else
  match t.phase with
  | .preflight =>
    if preflightOk t a then
      let t' := { t with phase := .main }
      .send t' t'.mainWire
    else .fail "CORS preflight refused"
  | .main =>
    if !t.page.hostCors && !t.same && !corsOk t a then .fail "CORS refused" else
    if isRedirect a.status && !t.page.hostCors then
      match headerGet a.headers "location" with
      | none => .deliver t (responseOf t a)
      | some loc =>
        if t.redirects ≥ maxRedirects then .fail "too many redirects" else
        match URL.parseUrl loc (some t.url) with
        | none => .fail "bad redirect"
        | some next => plan (afterRedirect t a.status next)
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

/-- Kind: policy theorem. Says: `plan` tells the host to make a request only when the current
URL passes `mayConnect` for the page, on the same string the host gets (`Wire.url = t.url`).
Does not say: that the host obeys. -/
theorem plan_send_allowed (t t' : Transfer) (w : Wire) (h : plan t = .send t' w) :
    t.allowed = true ∧ w.url = t.url := by
  unfold plan at h
  by_cases ha : t.allowed = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, if_false] at h
    split at h
    · simp at h
    · split at h <;> simp only [Step.send.injEq] at h <;> obtain ⟨h1, h2⟩ := h <;> subst h1 <;> subst h2 <;>
        exact ⟨ha, rfl⟩
  · simp [ha] at h

/-- Kind: policy theorem. Says: on a native host, `onAnswer` gives a page the response to a
cross-origin request only when the CORS check of that exact answer passed. Does not say:
what the Hub's browser does (`hostCors`), which enforces CORS for its own origin. -/
theorem deliver_cross_origin_needs_cors (t t' : Transfer) (a : Answer) (r : Response)
    (hn : t.page.hostCors = false) (hp : t.phase = .main) (hc : t.same = false)
    (h : onAnswer t a = .deliver t' r) : corsOk t a = true := by
  unfold onAnswer at h
  simp only [hp] at h
  split at h
  · simp at h
  · by_cases hok : corsOk t a = true
    · exact hok
    · have : (!t.page.hostCors && !t.same && !corsOk t a) = true := by simp [hn, hc, hok]
      rw [if_pos this] at h
      simp at h

/-- Kind: policy theorem. Says: on a native host, for a cross-origin request outside the
CORS-safelist, `plan` sends only the preflight, not the request. Does not say: that the
preflight answer is what the server meant (the server is trusted for its own CORS). -/
theorem plan_cross_unsafe_is_preflight (t t' : Transfer) (w : Wire)
    (hn : t.page.hostCors = false) (hc : t.same = false) (hu : t.needsPreflight = true)
    (h : plan t = .send t' w) : t'.phase = .preflight ∧ w.method = "OPTIONS" ∧ w.body = none := by
  unfold plan at h
  by_cases ha : t.allowed = true
  · have hs : (t.sameOriginOnly && !t.same) = t.sameOriginOnly := by simp [hc]
    simp only [ha, Bool.not_true, Bool.false_eq_true, if_false, hs] at h
    split at h
    · simp at h
    · simp only [hn, hc, hu, Bool.not_false, Bool.and_self, if_true, Step.send.injEq] at h
      obtain ⟨h1, h2⟩ := h
      subst h1; subst h2
      exact ⟨rfl, rfl, rfl⟩
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
  unfold plan at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Step.send.injEq] at h
        obtain ⟨_, h2⟩ := h
        subst h2
        exact Or.inr rfl
      · simp only [Step.send.injEq] at h
        obtain ⟨h1, h2⟩ := h
        subst h1; subst h2
        left
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
#guard safeHeader "Content-Type" "text/plain;charset=UTF-8" && !safeHeader "Content-Type" "application/json"
#guard unsafeHeaderNames [("X-B", "1"), ("x-a", "2"), ("Accept", "*/*")] == ["x-a", "x-b"]

private def base : Transfer :=
  { id := 1, page := pg, method := "GET", url := "https://b.example/d", headers := [], body := none }

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
-- a redirect is checked again: same-origin to a local address is refused
#guard match onAnswer { base with url := "https://a.example/y" } ({ status := 302, headers := [("Location", "http://127.0.0.1/")] } : Answer) with
  | .fail _ => true | _ => false

end L4Factoidal.Net.PageFetch
