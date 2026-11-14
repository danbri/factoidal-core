/-
L4Factoidal.Net.Subresource — the bytes a document asks for with no script: the images, style
sheets, fonts and scripts that its markup and style sheets name.

A document's subresources were fetched by each host with the host's own rule (the window:
images and fonts of the page's own origin only, by a plain `fetch` that followed redirects
itself and checked no address; the Hub and the test runner: rules of their own). So every
photograph of a page whose images live on another host was left out, and what was fetched
depended on the host. Here the rule is one, in the engine, for every host: the host asks for
each step (`answer`) and moves the bytes of the request it is told to make.

Source: Fetch Standard (https://fetch.spec.whatwg.org/) §4.1 main fetch (request mode
"no-cors": the request of an `img`, a `link rel=stylesheet`, a classic `script`, made with
no CORS check), §4.4 HTTP-redirect fetch, §2.2.6 (an opaque response: scripts read nothing of
it), §4.1 step "should response to request be blocked due to nosniff"; HTML §4.6.7.2 (a
linked style sheet whose Content-Type is not `text/css` is not used); and this tree's
`Net.PageFetch` for the address rules.

## Decisions

* A subresource request is `GET`, with no body, no field of the page, no cookie and no
  credential (`transfer`, `Plain`; `planNet_plain`, `onAnswer_plain`): it changes nothing on a server that keeps
  to HTTP's safe methods, and it carries nothing of the page but its `Origin` when it
  crosses origins.
* Another origin is allowed with no CORS check (mode "no-cors"). What makes that safe is
  that the bytes go to the engine's image store, cascade or font table and never to a
  script: the host gives them to no script, and the engine has no script path to them
  (canvas read-back of such an image is not offered). This module does not prove that; it
  is a property of the callers.
* Addresses: `Net.PageFetch`'s rules hold for every hop, the first and each redirect
  (`start_reach`, `onAnswer_reach`): `http` and `https` only, an `https` page reads `https`
  only, a local address only for a page that is itself local, a name is resolved first and
  the request goes to the address the engine chose, never to a special-purpose one.
* Redirects are the engine's: the host is told each hop (`redirect: "manual"`); at most
  `PageFetch.maxRedirects`; a redirect to a URL with credentials, to `data:` or to `blob:`
  is refused.
* A `data:` URL is read by the engine where it is used, and a `blob:` URL belongs to a
  script: neither is a subresource transfer (`start`).
* What is delivered: an answer with a 2xx status (`accept_status`). A style sheet of another
  origin, or one sent with `X-Content-Type-Options: nosniff`, must be `text/css`
  (`accept_style_type`); a script sent with `nosniff` must have a JavaScript type, and a
  script is never an image, audio, video or CSV type. Images and fonts are told apart by
  their bytes, by the decoders.
* Of the answer's fields the engine keeps `Content-Type` and `X-Content-Type-Options` only
  (`onAnswer_deliver_fields`).

On the Hub (`hostCors`) the browser that runs the Hub makes the request with its own rules
and follows redirects itself; the scheme and local-address rules apply to the first URL and
to the final URL it reports.
-/
import L4Factoidal.Net.PageFetch
import L4Factoidal.JSON.Value

namespace L4Factoidal.Net.Subresource
open L4Factoidal.WHATWG L4Factoidal.Net L4Factoidal.Net.PageFetch

/-- What the bytes are for. -/
inductive Kind where
  | image
  | style
  | font
  | script
  deriving DecidableEq, Repr, Inhabited

/-- The name of a kind in a host's request. -/
def Kind.name : Kind → String
  | .image => "image"
  | .style => "style"
  | .font => "font"
  | .script => "script"

/-- The kind a host's request names. -/
def Kind.ofName (s : String) : Option Kind :=
  if s == "image" then some .image
  else if s == "style" then some .style
  else if s == "font" then some .font
  else if s == "script" then some .script
  else none

/-- Kind: round trip. Says: the name of a kind reads back as that kind. Does not say:
anything of other strings (they read as no kind). -/
theorem Kind.ofName_name (k : Kind) : Kind.ofName k.name = some k := by
  cases k <;> decide

/-- The transfer of a subresource of `page` at `url`: `GET`, no field, no body, no
credentials, in `PageFetch`'s request record so that its address rules apply as they are. -/
def transfer (page : Page) (url : String) : Transfer :=
  { id := 0, page, method := "GET", url, headers := [], body := none }

/-- A transfer that asks as a subresource does: `GET`, no field, no body. -/
def Plain (t : Transfer) : Prop := t.method = "GET" ∧ t.headers = [] ∧ t.body = none

theorem transfer_plain (page : Page) (url : String) : Plain (transfer page url) := ⟨rfl, rfl, rfl⟩

/-- The first step for `url`: a `data:` or `blob:` URL is not a transfer; every other URL
is planned by `PageFetch.planNet` (the scheme, mixed content and address rules). -/
def start (page : Page) (url : String) : Step :=
  if url.startsWith "data:" || url.startsWith "blob:" then .fail "not a network URL"
  else planNet (transfer page url)

/-- The fields of an answer that the engine reads of a subresource. -/
def keptHeader (name : String) : Bool :=
  lower name == "content-type" || lower name == "x-content-type-options"

/-- The host's answer to the request of a subresource transfer: the address chosen for a
resolved name (as `PageFetch.onAnswer`), the next hop of a redirect, or the answer itself.
No CORS check (mode "no-cors"); the policy of `PageFetch.planNet` is applied to every hop
(a redirect to a `data:` or `blob:` URL is outside it: no scheme but `http` and `https`). -/
def onAnswer (t : Transfer) (a : Answer) : Step :=
  match t.phase with
  | .resolve => PageFetch.onAnswer t a
  | .preflight => .fail "a subresource transfer has no preflight"
  | .main =>
    if a.status == 0 then .fail "network error" else
    if !finalAllowed t a then .fail "refused by policy" else
    if isRedirect a.status && !t.page.hostCors then
      if t.redirects ≥ maxRedirects then .fail "too many redirects" else
      match (headerGet a.headers "location").bind fun loc => URL.parseUrl loc (some t.url) with
      | none => .fail "bad redirect"
      | some next =>
        if next.includesCredentials then .fail "redirect with credentials" else
        planNet (afterRedirect t a.status next)
    else
      .deliver t { status := a.status, statusText := "", url := (if a.url.isEmpty then t.url else a.url),
                   headers := a.headers.filter (fun f => keptHeader f.1), body := a.body }

/-! ## What is delivered -/

/-- The essence of a `Content-Type` value: before any parameter, trimmed, lower case. -/
def essence (v : String) : String :=
  lower (trimWs ((v.splitOn ";").headD ""))

/-- A JavaScript MIME type essence (MIME Sniffing §4.6). -/
def javaScriptType (e : String) : Bool :=
  ["application/ecmascript", "application/javascript", "application/x-ecmascript",
   "application/x-javascript", "text/ecmascript", "text/javascript", "text/javascript1.0",
   "text/javascript1.1", "text/javascript1.2", "text/javascript1.3", "text/javascript1.4",
   "text/javascript1.5", "text/jscript", "text/livescript", "text/x-ecmascript",
   "text/x-javascript"].contains e

/-- Is an answer of type essence `type` usable as kind `k`. `same`: the answer is of the
page's own origin. `nosniff`: it was sent with `X-Content-Type-Options: nosniff`. -/
def typeOk (k : Kind) (same nosniff : Bool) (type : String) : Bool :=
  match k with
  | .style => type == "text/css" || (same && !nosniff)
  | .script =>
    !(type.startsWith "image/" || type.startsWith "audio/" || type.startsWith "video/" || type == "text/csv") &&
      (!nosniff || javaScriptType type)
  | .image => true
  | .font => true

/-- What the host is told of a delivered answer: where it came from at last, and its type. -/
structure Delivered where
  url : String
  status : Nat
  contentType : String
  deriving Repr, DecidableEq, Inhabited

/-- The type essence of a response (`""` with no `Content-Type`). -/
def typeOf (r : Response) : String := essence ((headerGet r.headers "content-type").getD "")

/-- The response was sent with `X-Content-Type-Options: nosniff`. -/
def nosniffOf (r : Response) : Bool :=
  (headerGet r.headers "x-content-type-options").any fun v => lower (trimWs v) == "nosniff"

/-- The delivered answer of a transfer as kind `k`, or why it is not used. -/
def accept (k : Kind) (t : Transfer) (r : Response) : Except String Delivered :=
  if r.status < 200 || r.status ≥ 300 then .error s!"HTTP {r.status}"
  else if typeOk k t.same (nosniffOf r) (typeOf r) then .ok { url := r.url, status := r.status, contentType := typeOf r }
  else .error s!"refused: Content-Type {typeOf r} is not a {k.name}"

/-! ## Theorems -/

/-- A subresource transfer needs no CORS preflight. -/
theorem needsPreflight_plain {t : Transfer} (hp : Plain t) : t.needsPreflight = false := by
  obtain ⟨hm, hh, -⟩ := hp
  simp [Transfer.needsPreflight, hm, hh, safeMethod]

/-- Kind: invariant. Says: following a redirect keeps a subresource transfer one: still
`GET`, no field, no body. Does not say: anything of the URL (that is `plan`'s to judge). -/
theorem afterRedirect_plain {t : Transfer} (hp : Plain t) (s : Nat) (n : URL.Url) :
    Plain (afterRedirect t s n) := by
  obtain ⟨hm, hh, hb⟩ := hp
  simp [Plain, afterRedirect, hm, hh, hb]

/-- `emit` sends or fails: it delivers nothing. -/
theorem emit_not_deliver {t t' : Transfer} {w : Wire} {r : Response} : emit t w ≠ .deliver t' r := by
  intro h
  unfold emit at h
  split at h
  · split at h <;> simp at h
  · split at h
    · simp at h
    · split at h <;> simp at h

/-- Kind: lemma. Says: `planNet` never delivers: what a subresource transfer delivers is an
answer of the host, never something made here. -/
theorem planNet_not_deliver {t t' : Transfer} {r : Response} : planNet t ≠ .deliver t' r := by
  intro h
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · exact emit_not_deliver h
      · exact emit_not_deliver h

/-- Kind: policy theorem. Says: `planNet` tells the host to make a request only when the
current URL passes `mayConnect` for the page, on the same string the host gets, and the
request passes `wireReach` (`PageFetch.plan_send_allowed`, for `planNet` itself). -/
theorem planNet_send_allowed (t t' : Transfer) (w : Wire) (h : planNet t = .send t' w) :
    t.allowed = true ∧ w.url = t.url ∧ wireReach t.page w = true ∧ t'.page = t.page := by
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

/-- Kind: policy theorem (safe requests only). Says: every request `planNet` tells the host to
make for a subresource transfer is a resolve-only one (nothing goes to a server) or a `GET`
with no body, and the transfer stays a subresource transfer; no preflight is sent. Does not
say: that the server treats `GET` as safe. -/
theorem planNet_plain {t t' : Transfer} {w : Wire} (hp : Plain t) (h : planNet t = .send t' w) :
    Plain t' ∧ (w.resolve = true ∨ (w.method = "GET" ∧ w.body = none)) := by
  unfold planNet at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · rename_i hc
        simp [needsPreflight_plain hp] at hc
      · rcases emit_cases h with ⟨rfl, rfl⟩ | ⟨rfl, -, hm, -, hb, -⟩
        · exact ⟨hp, Or.inl rfl⟩
        · exact ⟨hp, Or.inr ⟨by simpa [Transfer.mainWire] using hm.trans (by simp [Transfer.mainWire, hp.1]),
            by simpa [Transfer.mainWire] using hb.trans (by simp [Transfer.mainWire, hp.2.2])⟩⟩

/-- Kind: policy theorem (the first request). Says: the first request of a subresource is
sent only for a URL that passes `mayConnect` for the page (`http` or `https`, no `http` from
an `https` page, a local address only from a local page), on the string the host gets, and
it passes the address rule `wireReach`. Does not say: that the host obeys. -/
theorem start_reach (page : Page) (url : String) (t' : Transfer) (w : Wire)
    (h : start page url = .send t' w) :
    (transfer page url).allowed = true ∧ w.url = url ∧ wireReach page w = true ∧ t'.page = page := by
  unfold start at h
  split at h
  · simp at h
  · exact planNet_send_allowed _ _ _ h

/-- Kind: policy theorem (DNS rebinding and redirects). Says: every request that `onAnswer`
tells the host to make passes `wireReach` for the page, whatever the answer was: after a
resolved name, and after each redirect, a page that is not local never has a request sent to
a special-purpose address. It holds for any transfer record, so a host that changed the
record it carries between steps gains no address by it. Does not say: that the host connects
to the address it is given and to no other. -/
theorem onAnswer_reach (t t' : Transfer) (a : Answer) (w : Wire) (h : onAnswer t a = .send t' w) :
    wireReach t.page w = true := by
  unfold onAnswer at h
  split at h
  · exact PageFetch.onAnswer_reach t t' a w h
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
              · exact (planNet_send_allowed _ _ _ h).2.2.1
        · simp at h

/-- Kind: policy theorem (redirects stay safe requests). Says: a request sent after an answer
to a subresource transfer whose own request was sent (phase `main`) is again resolve-only or
a `GET` with no body. Does not say: the same of the step after a resolved name (there
`PageFetch.onAnswer` plans the same transfer again, by `PageFetch.plan`). -/
theorem onAnswer_plain {t t' : Transfer} {a : Answer} {w : Wire} (hp : Plain t) (hm : t.phase = .main)
    (h : onAnswer t a = .send t' w) :
    Plain t' ∧ (w.resolve = true ∨ (w.method = "GET" ∧ w.body = none)) := by
  unfold onAnswer at h
  simp only [hm] at h
  split at h
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
            · exact planNet_plain (afterRedirect_plain hp _ _) h
      · simp at h

/-- Kind: policy theorem (what the engine keeps of an answer). Says: the response that
`onAnswer` delivers for a transfer whose request was sent carries only the `Content-Type` and
`X-Content-Type-Options` fields of the answer: no `Set-Cookie`, no other field. Does not say:
anything of the body (it is the subresource). -/
theorem onAnswer_deliver_fields {t t' : Transfer} {a : Answer} {r : Response} (hm : t.phase = .main)
    (h : onAnswer t a = .deliver t' r) : ∀ f ∈ r.headers, keptHeader f.1 = true := by
  unfold onAnswer at h
  simp only [hm] at h
  split at h
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
            · exact absurd h planNet_not_deliver
      · simp only [Step.deliver.injEq] at h
        obtain ⟨-, rfl⟩ := h
        intro f hf
        exact (List.mem_filter.mp hf).2

/-- Kind: policy theorem. Says: `accept` uses an answer only with a 2xx status. Does not say:
that a 2xx answer is used (its type is judged too). -/
theorem accept_status {k : Kind} {t : Transfer} {r : Response} {d : Delivered}
    (h : accept k t r = .ok d) : 200 ≤ r.status ∧ r.status < 300 := by
  unfold accept at h
  split at h
  · simp at h
  · rename_i hs
    simp at hs
    omega

/-- Kind: policy theorem (a style sheet's type). Says: an answer used as a style sheet is
`text/css`, or it is of the page's own origin and was not sent with `nosniff`. So a page can
not make the cascade read another site's HTML or JSON as CSS. Does not say: that a same-origin
answer of another type is CSS (it is read as CSS, as browsers in quirks mode read it). -/
theorem accept_style_type {t : Transfer} {r : Response} {d : Delivered}
    (h : accept .style t r = .ok d) : d.contentType = "text/css" ∨ t.same = true := by
  unfold accept at h
  split at h
  · simp at h
  · split at h
    · rename_i hok
      simp only [Except.ok.injEq] at h
      subst h
      simp only [typeOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hok
      rcases hok with hc | ⟨hs, -⟩
      · exact Or.inl hc
      · exact Or.inr hs
    · simp at h

/-! ## The host's steps, as JSON

Request: `{page, pageAddress?, hostCors?, kind, url}` for the first step; with `state` (the
`state` of the last answer, unchanged) and `answer` (`{status, headers: [[name, value]],
url?, addresses?}`: the host's answer to the request it was told to make, without the body)
for each later step. Answer: `{send: {id, method, url, headers, resolve?, address?, port?},
state}` (make this request, as `native_net.ts` makes a page script's), or `{deliver: {url,
status, contentType}}` (the body of the last answer is the subresource), or `{fail: reason}`. -/

open L4Factoidal.JSON in
private def str (j : Json) (key : String) : String := (j.getString? key).getD ""

open L4Factoidal.JSON in
private def natOf (j : Json) (key : String) : Option Nat :=
  match j.field? key with
  | some (.number s) => s.toNat?
  | _ => none

open L4Factoidal.JSON in
private def num (n : Nat) : Json := .number (toString n)

open L4Factoidal.JSON in
/-- One request to the host, in the form of a page script's request (`WebScripts.wireJson`);
a subresource request has no body. -/
def wireJson (w : Wire) : Json :=
  .object ([("id", num w.id), ("method", .string w.method), ("url", .string w.url),
      ("headers", .array (w.headers.map fun (n, v) => .array [.string n, .string v]))] ++
      (if w.resolve then [("resolve", .bool true)] else []) ++
      (if w.address.isEmpty then [] else [("address", .string w.address), ("port", num w.port)]))

open L4Factoidal.JSON in
/-- What of a transfer changes between steps: the current URL, the redirects so far, whether
it crossed origins, whether it waits for a resolved name, and the address pinned for a name. -/
def stateJson (t : Transfer) : Json :=
  .object ([("url", .string t.url), ("redirects", num t.redirects), ("crossed", .bool t.crossed),
      ("resolving", .bool (t.phase == .resolve))] ++
      (match t.pin with
       | some (h, a) => [("pinHost", .string h), ("pinAddress", .string a)]
       | none => []))

open L4Factoidal.JSON in
/-- The transfer of `page` that a host's `state` describes. The page is never read from the
state: it is made again from the request, by `Page.ofUrl`. -/
def stateOf (page : Page) (j : Json) : Option Transfer := do
  let url ← j.getString? "url"
  let redirects ← natOf j "redirects"
  let crossed ← j.getBool? "crossed"
  let resolving ← j.getBool? "resolving"
  let pin := match j.getString? "pinHost", j.getString? "pinAddress" with
    | some h, some a => some (h, a)
    | _, _ => none
  some { transfer page url with redirects, crossed, phase := (if resolving then .resolve else .main), pin }

/-- Kind: invariant. Says: whatever a host's `state` holds, the transfer read from it is a
subresource transfer of the page given (`GET`, no field, no body). Does not say: that the
state is one this module wrote. -/
theorem stateOf_plain {page : Page} {j : JSON.Json} {t : Transfer} (h : stateOf page j = some t) :
    Plain t ∧ t.page = page := by
  unfold stateOf at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨_, -, _, -, _, -, _, -, rfl⟩ := h
  exact ⟨⟨rfl, rfl, rfl⟩, rfl⟩

open L4Factoidal.JSON in
/-- The host's answer to a request, without its body (`Answer.body` stays empty: the engine
decides on the status and the fields). -/
def answerOf (x : Json) : Answer :=
  let hs : List (String × String) := match x.field? "headers" with
    | some (.array xs) => xs.filterMap fun
      | .array [.string n, .string v] => some (n, v)
      | _ => none
    | _ => []
  let addresses : List String := match x.field? "addresses" with
    | some (.array xs) => xs.filterMap fun
      | .string a => some a
      | _ => none
    | _ => []
  { status := (natOf x "status").getD 0, headers := hs, url := str x "url", addresses }

open L4Factoidal.JSON in
/-- A step as the host's answer. -/
def stepJson (k : Kind) : Step → Json
  | .send t w => .object [("send", wireJson w), ("state", stateJson t)]
  | .deliver t r =>
    match accept k t r with
    | .ok d => .object [("deliver", .object [("url", .string d.url), ("status", num d.status),
        ("contentType", .string d.contentType)])]
    | .error why => .object [("fail", .string why)]
  | .fail why => .object [("fail", .string why)]

open L4Factoidal.JSON in
/-- One step of a subresource transfer for a host (the header of this section). -/
def answer (request : Json) : Json :=
  let page := Page.ofUrl (str request "page") (request.getBool? "hostCors" == some true) (str request "pageAddress")
  match Kind.ofName (str request "kind") with
  | none => .object [("fail", .string "unknown kind of subresource")]
  | some k =>
    match request.field? "state" with
    | none => stepJson k (start page (str request "url"))
    | some s =>
      match stateOf page s with
      | none => .object [("fail", .string "bad transfer state")]
      | some t => stepJson k (onAnswer t (answerOf ((request.field? "answer").getD .null)))

/-! ## Tests -/

private def publicPage : Page := Page.ofUrl "https://news.example/story"
private def localPage : Page := Page.ofUrl "http://localhost:8000/index.html"

private def sent : Step → Option (String × String × Bool)
  | .send _ w => some (w.method, w.url, w.resolve)
  | _ => none
private def failed : Step → Bool
  | .fail _ => true
  | _ => false

-- a name is resolved first: no byte goes to the server before the engine chose the address
#guard sent (start publicPage "https://images.example/a.png") == some ("", "https://images.example/a.png", true)
-- an `https` page reads no `http` image; no scheme but http(s); no local address; no data: or blob:
#guard failed (start publicPage "http://images.example/a.png")
#guard failed (start publicPage "file:///etc/passwd")
#guard failed (start publicPage "https://localhost/a.png")
#guard failed (start publicPage "https://127.0.0.1/a.png")
#guard failed (start publicPage "https://192.168.1.1/a.png")
#guard failed (start publicPage "https://[::1]/a.png")
#guard failed (start publicPage "data:image/png;base64,aGk=")
#guard failed (start publicPage "blob:https://news.example/1")
-- a local page reaches its own server with no resolve step
#guard sent (start localPage "http://localhost:8000/a.png") == some ("GET", "http://localhost:8000/a.png", false)

-- the resolved name: a special-purpose address among the answers refuses the transfer
private def resolving : Transfer := { transfer publicPage "https://images.example/a.png" with phase := .resolve }
#guard failed (onAnswer resolving { addresses := ["93.184.215.14", "10.0.0.1"] })
#guard failed (onAnswer resolving { addresses := [] })
#guard match onAnswer resolving { addresses := ["93.184.215.14"] } with
  | .send t w => w.address == "93.184.215.14" && w.port == 443 && w.method == "GET" && !w.resolve &&
      w.url == "https://images.example/a.png" && t.pin == some ("images.example", "93.184.215.14") &&
      w.headers == [("Origin", "https://news.example")]
  | _ => false

-- answers to the request itself
private def pinned : Transfer := { transfer publicPage "https://images.example/a.png" with pin := some ("images.example", "93.184.215.14") }
#guard match onAnswer pinned { status := 200, headers := [("Content-Type", "image/png"), ("Set-Cookie", "a=b")] } with
  | .deliver _ r => r.headers == [("Content-Type", "image/png")] && r.url == "https://images.example/a.png"
  | _ => false
#guard failed (onAnswer pinned { status := 0 })
-- a redirect to the same name keeps the pin and sends the next hop there
#guard match onAnswer pinned { status := 302, headers := [("Location", "/b.png")] } with
  | .send t w => w.url == "https://images.example/b.png" && w.address == "93.184.215.14" && t.redirects == 1 && w.method == "GET"
  | _ => false
-- a redirect to another name resolves that name first; to a local address, to http, to data:, with credentials: refused
#guard sent (onAnswer pinned { status := 301, headers := [("Location", "https://cdn.example/c.png")] }) == some ("", "https://cdn.example/c.png", true)
#guard failed (onAnswer pinned { status := 302, headers := [("Location", "https://127.0.0.1/secret")] })
#guard failed (onAnswer pinned { status := 302, headers := [("Location", "http://images.example/b.png")] })
#guard failed (onAnswer pinned { status := 302, headers := [("Location", "data:image/png;base64,aGk=")] })
#guard failed (onAnswer pinned { status := 302, headers := [("Location", "https://u:p@images.example/b.png")] })
#guard failed (onAnswer pinned { status := 302, headers := [] })
#guard failed (onAnswer { pinned with redirects := maxRedirects } { status := 302, headers := [("Location", "/b.png")] })

-- what is used
private def got (k : Kind) (t : Transfer) (status : Nat) (headers : List (String × String)) : Bool :=
  (accept k t { status, statusText := "", url := t.url, headers, body := ByteArray.empty }).toOption.isSome
private def sameT : Transfer := transfer publicPage "https://news.example/site.css"
#guard got .image pinned 200 [] && got .image pinned 200 [("Content-Type", "text/html")] && got .font pinned 206 []
#guard !got .image pinned 404 [("Content-Type", "image/png")] && !got .image pinned 304 [] && !got .style pinned 500 []
#guard got .style pinned 200 [("Content-Type", "text/css; charset=utf-8")] && got .style pinned 200 [("content-type", "TEXT/CSS")]
#guard !got .style pinned 200 [("Content-Type", "text/html")] && !got .style pinned 200 []
#guard got .style sameT 200 [("Content-Type", "text/plain")] && got .style sameT 200 []
#guard !got .style sameT 200 [("Content-Type", "text/plain"), ("X-Content-Type-Options", "nosniff")]
#guard got .script pinned 200 [("Content-Type", "text/javascript")] && got .script pinned 200 [("Content-Type", "text/plain")]
#guard !got .script pinned 200 [("Content-Type", "text/plain"), ("X-Content-Type-Options", " NoSniff ")]
#guard !got .script pinned 200 [("Content-Type", "image/png")] && !got .script pinned 200 [("Content-Type", "text/csv")]

-- the host's steps: first step, the state carried, the resolved name, the answer
open L4Factoidal.JSON in
private def req (fields : List (String × Json)) : Json :=
  .object ([("page", .string "https://news.example/story"), ("kind", .string "image")] ++ fields)
open L4Factoidal.JSON in
private def first : Json := answer (req [("url", .string "https://images.example/a.png")])
open L4Factoidal.JSON in
#guard (first.field? "send").bind (·.getBool? "resolve") == some true
open L4Factoidal.JSON in
private def second : Json := answer (req [("state", (first.field? "state").getD .null),
  ("answer", .object [("addresses", .array [.string "93.184.215.14"])])])
open L4Factoidal.JSON in
#guard (second.field? "send").bind (·.getString? "address") == some "93.184.215.14"
open L4Factoidal.JSON in
#guard ((second.field? "send").bind (·.getString? "method")) == some "GET"
open L4Factoidal.JSON in
private def third : Json := answer (req [("state", (second.field? "state").getD .null),
  ("answer", .object [("status", .number "200"), ("headers", .array [.array [.string "content-type", .string "image/jpeg"]])])])
open L4Factoidal.JSON in
#guard (third.field? "deliver").bind (·.getString? "contentType") == some "image/jpeg"
open L4Factoidal.JSON in
#guard (third.field? "deliver").bind (·.getString? "url") == some "https://images.example/a.png"
-- a state that names a local pin gains nothing: the request is refused at the address rule
open L4Factoidal.JSON in
#guard ((answer (req [("state", .object [("url", .string "https://images.example/a.png"), ("redirects", .number "0"),
    ("crossed", .bool false), ("resolving", .bool false), ("pinHost", .string "images.example"), ("pinAddress", .string "127.0.0.1")]),
  ("answer", .object [("status", .number "302"), ("headers", .array [.array [.string "location", .string "/b.png"]])])])).field? "fail").isSome
open L4Factoidal.JSON in
#guard ((answer (.object [("page", .string "https://news.example/story"), ("kind", .string "video"), ("url", .string "https://images.example/a.png")])).field? "fail").isSome
-- the state round trip of the fields that change
#guard (stateOf publicPage (stateJson { pinned with redirects := 3, crossed := true })).map
    (fun t => (t.url, t.redirects, t.crossed, t.pin, t.phase == .main)) ==
  some ("https://images.example/a.png", 3, true, some ("images.example", "93.184.215.14"), true)
#guard (stateOf publicPage (stateJson resolving)).map (·.phase == .resolve) == some true

end L4Factoidal.Net.Subresource
