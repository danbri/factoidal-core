/-
L4Factoidal.Net.Navigation — the requests of a top-level navigation (a typed address, a link,
a form submission) with their redirects, decided by the network core of page scripts
(`Net.PageFetch`) and moved by the host.

A host that navigates asks the engine step by step, as for a subresource (`Net.Subresource`):
`start` names the navigation (URL, method, body for a form post, the initiator, Tor mode), the
engine answers the request to make (a `Wire`), a failure, or that it is done; the host makes each
request and gives the answer back (`answer`), until it is done. The host keeps the bytes and the
header fields of the last answer.

## Decisions

* Every network decision is `Net.PageFetch`'s: the scheme and local-address rules (`mayConnect`,
  `wireReach`, the DNS pin in direct mode), Tor mode (`Page.tor`: no resolve, no address, a wire
  marked `tor` with a partition), the redirect steps (`onAnswer`, `afterRedirect`, at most
  `maxRedirects`), the `Referer` under the referrer policy, and the destination `document`.
* The page of a navigation for these rules (`navPage`) is the target document's own origin: a
  top-level navigation makes its own top-level site, so the page is built from the navigation's
  first URL. That page stays the same over the redirects of one navigation. So in Tor mode every
  hop of one navigation carries the same partition, the origin of the navigation's first URL:
  one navigation keeps one circuit set over its redirects (`answer_partition`).
* A top-level navigation is not mixed content: `navPage` is never `secure`, so a redirect from
  `https` to `http` is followed.
* Method: `GET`, or `POST` with a body whose type is one of the form encodings
  (`application/x-www-form-urlencoded`, `multipart/form-data`, `text/plain`). A 303, or a 301 or
  302 after a `POST`, continues as `GET` with no body and no body fields (Fetch §4.4,
  `afterRedirect`).
* The first URL is `http` or `https`. A redirect to another scheme fails (`data:` and `blob:`
  are answered only as a first URL, `PageFetch.dataStep` and `blobStep`; every other scheme fails
  `mayConnect`).
* Mode: the transfer is made as "no-cors" so that no CORS check and no preflight applies (a
  navigation has neither); the wire says `Sec-Fetch-Mode: navigate`. `Sec-Fetch-Site` is
  computed against the initiator (`none` when there is none: the person typed or chose the
  address). The `Origin` field of a `POST` is the initiator's origin on the first hop and `null`
  after a redirect (claims less than Fetch's "serializing a request origin").
* In direct mode a `.onion` URL fails (`mayConnect`, RFC 7686 §2); in Tor mode it is reached.
* Cookies: none. The wires carry no `Cookie` field and the engine stores no `Set-Cookie`
  (`omitCredentials`). `PageFetch`'s jar decides `SameSite` against the page, and a navigation's
  rule is against its initiator (`Cookies.navCookie`), so the jar is not used here. Gap, with an
  expected failure in `labs/demos/foafnaut/tor-wasm/deno/tor.test.ts`:
  https://github.com/danbri/factoidal-core/issues/1060.

## What is proved (`NavigationTheorems`)

`start_tor`, `answer_tor`: in Tor mode every wire is not resolve-only, names no address, is
marked `tor`, and carries a partition that is not `"null"`. `answer_partition` with
`start_inv`, `answer_inv`: every hop of one navigation has the partition of its first URL's
origin. `start_direct`, `answer_direct`: in direct mode no wire is marked `tor`.
`start_onion_direct`: a direct-mode `.onion` navigation fails.
-/
import L4Factoidal.Net.PageFetch

namespace L4Factoidal.Net.Navigation
open L4Factoidal.WHATWG
open L4Factoidal.Net.PageFetch

/-- The page of a navigation to `url` for the network rules: the target document's own origin,
never secure (a top-level navigation is not mixed content), in Tor mode when `tor`. -/
def navPage (url : String) (tor : Bool) : Page :=
  { Page.ofUrl url false "" tor with secure := false }

/-- One navigation in progress. `page`: its `navPage`, fixed at `start`; `initiator`: the URL of
the document that started it (`""`: the person typed or chose the address); `farthest`: the
farthest any URL of it so far was from the initiator (`siteRank`). -/
structure Entry where
  t : Transfer
  page : Page
  initiator : String
  farthest : Nat := 0
  deriving Inhabited

/-- The navigations in progress, by id. -/
structure Table where
  live : List (Nat × Entry) := []
  next : Nat := 1
  deriving Inhabited

/-- At most this many navigations at once. -/
def maxLive : Nat := 64

/-- What the host is told. -/
inductive Out where
  /-- Make this request and give the answer back. -/
  | wire (id : Nat) (w : Wire)
  /-- Done: the last answer is the response of the navigation, of `status` and `type`, from the
  final `url`, after `redirects` redirects. -/
  | done (id : Nat) (status : Nat) (type : String) (url : String) (redirects : Nat)
  /-- The navigation failed (a network error). -/
  | fail (id : Nat) (why : String)
  deriving Inhabited

/-- The URL parses and is `http` or `https`. -/
def httpUrl (url : String) : Bool :=
  match URL.parseUrl url with
  | some u => u.scheme == "http" || u.scheme == "https"
  | none => false

/-- The transfer of a navigation's first request. A `POST` carries its body and its type. -/
def request (id : Nat) (p : Page) (method url : String) (body : Option ByteArray) (bodyType referrer : String)
    (policy : ReferrerPolicy.Policy) : Transfer :=
  let post := method == "POST"
  { id, page := p, method, url, headers := if post then [("Content-Type", bodyType)] else [],
    body := if post then some (body.getD ByteArray.empty) else none, noCors := true, omitCredentials := true,
    destination := "document", referrer, referrerPolicy := policy }

/-- How far `url` is from the initiator (`siteRank` from the initiator's page; 2 when either does
not parse). -/
def rankFrom (initiator url : String) : Nat :=
  match URL.parseUrl url with
  | some u => siteRank (Page.ofUrl initiator) u
  | none => 2

/-- The initiator's origin, `"null"` for none. -/
def initiatorOrigin (initiator : String) : String :=
  match URL.parseUrl initiator with
  | some u => u.origin
  | none => "null"

/-- The fields of a navigation's wire: `Sec-Fetch-Mode: navigate`, `Sec-Fetch-Site` against the
initiator (`none` for none), and for a `POST` the `Origin` of the initiator on the first hop,
`null` after a redirect. -/
def navHeaders (initiator : String) (site : Nat) (firstHop : Bool) (method : String)
    (hs : List (String × String)) : List (String × String) :=
  let hs := (hs.filter fun (n, _) => lower n != "origin").map fun (n, v) =>
    if lower n == "sec-fetch-mode" then (n, "navigate")
    else if lower n == "sec-fetch-site" then (n, if initiator.isEmpty then "none" else siteToken site)
    else (n, v)
  hs ++ (if method == "POST" then [("Origin", if firstHop then initiatorOrigin initiator else "null")] else [])

/-- The wire as a navigation sends it: only the header fields of a request wire change. -/
def navWire (initiator : String) (site : Nat) (firstHop : Bool) (method : String) (w : Wire) : Wire :=
  if w.resolve then w else { w with headers := navHeaders initiator site firstHop method w.headers }

/-- The table after a step of navigation `id`, and what the host is told. `last`: the answer
the step came from (none for the first plan). -/
def after (tab : Table) (id : Nat) (e : Entry) (last : Option Answer) : Step → Table × Out
  | .send t w =>
    let site := max e.farthest (rankFrom e.initiator t.url)
    ({ tab with live := (id, { e with t, farthest := site }) :: tab.live },
      .wire id (navWire e.initiator site (t.redirects == 0) t.method w))
  | .fail why => (tab, .fail id why)
  | .deliver t _ =>
    match last with
    | some a => (tab, .done id a.status ((headerGet a.headers "content-type").getD "")
        (if a.url.isEmpty then t.url else a.url) t.redirects)
    | none => (tab, .fail id "refused: a navigation's URL is http or https")

/-- Start a navigation to `url` by `method` ("GET" or "POST"), from the document at `initiator`
(`""` for none), under its referrer `policy`; for a `POST`, `body` of type `bodyType`. -/
def start (tab : Table) (url method initiator : String) (policy : ReferrerPolicy.Policy)
    (body : Option ByteArray) (bodyType : String) (tor : Bool) : Table × Out :=
  let id := tab.next
  let tab := { tab with next := id + 1 }
  let p := navPage url tor
  if !httpUrl url then (tab, .fail id "refused: a navigation's URL is http or https")
  else if !(method == "GET" || method == "POST") then (tab, .fail id "refused: a navigation's method is GET or POST")
  else if method == "POST" && !safeHeader "content-type" bodyType then
    (tab, .fail id "refused: a form's body type is a form encoding")
  else if tab.live.length ≥ maxLive then (tab, .fail id "too many navigations")
  else
    let t := request id p method url body bodyType initiator policy
    after tab id { t, page := p, initiator } none (plan t)

/-- The host's answer to the request of navigation `id`. -/
def answer (tab : Table) (id : Nat) (a : Answer) : Table × Out :=
  match tab.live.find? (·.1 == id) with
  | none => (tab, .fail id "no such navigation")
  | some (_, e) => after { tab with live := tab.live.filter (·.1 != id) } id e (some a) (onAnswer e.t a)

/-- The host stops the navigation (the person went elsewhere, the tab closed). -/
def cancel (tab : Table) (id : Nat) : Table := { tab with live := tab.live.filter (·.1 != id) }

/-! ## Examples -/

private def wireOf : Table × Out → Option Wire
  | (_, .wire _ w) => some w
  | _ => none
private def resolved : Table × Out → Table × Out
  | (tab, .wire id w) => if w.resolve then answer tab id { addresses := ["93.184.216.34"] } else (tab, .wire id w)
  | o => o

-- Tor mode: the first wire is marked tor, in the partition of the target's origin
#guard (match wireOf (start {} "https://a.example/x" "GET" "" .default none "" true) with
  | some w => w.tor && !w.resolve && w.address.isEmpty && w.partition == "https://a.example" &&
      headerGet w.headers "sec-fetch-mode" == some "navigate" && headerGet w.headers "sec-fetch-site" == some "none" &&
      headerGet w.headers "sec-fetch-dest" == some "document" && headerGet w.headers "cookie" == none
  | none => false)
-- direct mode: the name is resolved first, then the request goes to the pinned address
#guard (match wireOf (start {} "https://a.example/x" "GET" "" .default none "" false) with
  | some w => w.resolve && !w.tor
  | none => false)
#guard (match wireOf (resolved (start {} "https://a.example/x" "GET" "" .default none "" false)) with
  | some w => !w.resolve && !w.tor && w.partition.isEmpty && w.address == "93.184.216.34"
  | none => false)
-- a redirect hop in Tor mode keeps the partition of the first URL
#guard (match start {} "https://a.example/r" "GET" "" .default none "" true with
  | (tab, .wire id _) =>
    match answer tab id { status := 302, headers := [("Location", "https://b.example/y")] } with
    | (tab, .wire id' w) => w.url == "https://b.example/y" && w.tor && w.partition == "https://a.example" &&
      (match answer tab id' { status := 200, headers := [("Content-Type", "text/html")] } with
       | (tab, .done _ 200 "text/html" "https://b.example/y" 1) => tab.live.isEmpty
       | _ => false)
    | _ => false
  | _ => false)
-- a form POST, then a 303: the next hop is a GET with no body, no Content-Type and no Origin
#guard (match start {} "https://a.example/post" "POST" "https://c.example/form" .default (some "q=1".toUTF8)
    "application/x-www-form-urlencoded" true with
  | (tab, .wire id w) => w.method == "POST" && w.body.isSome &&
      headerGet w.headers "origin" == some "https://c.example" && headerGet w.headers "sec-fetch-site" == some "cross-site" &&
      headerGet w.headers "referer" == some "https://c.example/" &&
      (match answer tab id { status := 303, headers := [("Location", "/done")] } with
       | (_, .wire _ w') => w'.method == "GET" && w'.body.isNone && headerGet w'.headers "content-type" == none &&
           headerGet w'.headers "origin" == none && w'.url == "https://a.example/done" && w'.partition == "https://a.example"
       | _ => false)
  | _ => false)
-- a 307 keeps the POST; its Origin becomes null after the redirect
#guard (match start {} "https://a.example/post" "POST" "https://a.example/form" .default (some "q=1".toUTF8) "text/plain" true with
  | (tab, .wire id _) =>
    match answer tab id { status := 307, headers := [("Location", "/again")] } with
    | (_, .wire _ w') => w'.method == "POST" && w'.body.isSome && headerGet w'.headers "origin" == some "null"
    | _ => false
  | _ => false)
-- a form body of another type is refused before anything is sent
#guard (match start {} "https://a.example/post" "POST" "" .default none "application/json" true with
  | (_, .fail _ _) => true | _ => false)
-- an https page may redirect to http (no mixed content for a navigation)
#guard (match start {} "https://a.example/r" "GET" "" .default none "" true with
  | (tab, .wire id _) => (match answer tab id { status := 301, headers := [("Location", "http://b.example/")] } with
    | (_, .wire _ w) => w.url == "http://b.example/" | _ => false)
  | _ => false)
-- a redirect to another scheme fails
#guard (match start {} "https://a.example/r" "GET" "" .default none "" true with
  | (tab, .wire id _) => (match answer tab id { status := 302, headers := [("Location", "data:text/html,x")] } with
    | (_, .fail _ _) => true | _ => false) &&
    (match answer tab id { status := 302, headers := [("Location", "ftp://b.example/")] } with
    | (_, .fail _ _) => true | _ => false)
  | _ => false)
-- a first URL that is not http or https fails
#guard (match start {} "data:text/html,x" "GET" "" .default none "" false with | (_, .fail _ _) => true | _ => false)
-- .onion: reached in Tor mode, refused in direct mode
#guard (match wireOf (start {} "http://abcdefghijklmnop.onion/" "GET" "" .default none "" true) with
  | some w => w.tor && w.partition == "http://abcdefghijklmnop.onion" | none => false)
#guard (match start {} "http://abcdefghijklmnop.onion/" "GET" "" .default none "" false with
  | (_, .fail _ _) => true | _ => false)
-- the redirect limit
private def hops : Nat → Table × Out → Bool
  | 0, (_, .fail _ why) => why == "too many redirects"
  | 0, _ => false
  | n + 1, (tab, .wire id _) => hops n (answer tab id { status := 302, headers := [("Location", s!"/r{n}")] })
  | _ + 1, _ => false
#guard hops (maxRedirects + 1) (start {} "https://a.example/r" "GET" "" .default none "" true)

end L4Factoidal.Net.Navigation
