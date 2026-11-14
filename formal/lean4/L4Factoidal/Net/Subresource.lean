/-
L4Factoidal.Net.Subresource — the requests a document's elements make for the engine itself
(images, fonts, style sheets, classic and module scripts, media), decided by the network
core of page scripts (`Net.PageFetch`) and moved by the host.

A host that loads a page asks the engine for each subresource step by step: `start` names
the request, the engine answers the request to make (a `Wire`), a failure, or that it is
done; the host makes each request (`native_net.ts` on the desktop) and gives the answer
back (`answer`), until it is done. The host keeps the bytes of the last answer; the engine
says whether they may be used and whether a script may ever read them.

## Decisions

* Every decision is `Net.PageFetch`'s: the scheme and local-address rules (`mayConnect`,
  `wireReach`, the DNS pin), mixed content (an `https` page reads `https` only), redirects
  (followed here, with the same checks at each hop, at most `maxRedirects`), CORS, the
  `Referer` under the document's referrer policy and the fetch metadata (`Sec-Fetch-Dest` is
  the element's destination).
* Mode: an element without a `crossorigin` attribute makes a "no-cors" request (Fetch §2.2.5:
  images, classic scripts, style sheets, media); `crossorigin` makes a "cors" request
  ("anonymous" or "use-credentials"), as module scripts and fonts always are. A "no-cors"
  answer from another origin is opaque: the engine may draw it, a script may never read it
  (`Out.done` with `hidden`).
* No cookies: these requests carry no jar (`Transfer.jar` is empty), so no `Cookie` is sent
  and none is stored. The page session's jar is the script session's (`Net.Xhr`).
* A response that is not ok (status outside 200 to 299) is a failure for the element, and so is
  one whose type the element may not use (`typeOk`: style sheets, scripts and nosniff).
* The engine holds each transfer in progress in a table of at most `maxLive`; a host that
  starts more gets failures.

## What is proved

`after_style_type`: a style sheet is used only when `text/css`, or of the page's own origin and
not sent with `nosniff`. `start_wire` and `answer_wire`: every request the host is told to make passes the page's
policy (`wireReach`: no special-purpose address for a page from the network) and, for the
first one, `mayConnect` (scheme, local address, mixed content) on the URL the host fetches.
`start_mixed`: an `https` document never sends a request to an `http` URL. `kind_known`: a
request of an unknown destination is refused before anything is sent.
-/
import L4Factoidal.Net.PageFetch

namespace L4Factoidal.Net.Subresource
open L4Factoidal.WHATWG
open L4Factoidal.Net.PageFetch

/-- The destinations of the requests this file makes (Fetch §2.2.5). -/
def kinds : List String := ["image", "font", "style", "script", "audio", "video", "track"]

/-- The transfers in progress, by id. -/
structure Table where
  live : List (Nat × Transfer) := []
  next : Nat := 1
  deriving Inhabited

/-- At most this many transfers at once. -/
def maxLive : Nat := 256

/-- What the host is told. -/
inductive Out where
  /-- Make this request and give the answer back. -/
  | wire (id : Nat) (w : Wire)
  /-- Done: the bytes of the last answer (or `body`, for a `data:` URL answered here) are the
  resource, of `type` and from the final `url`; `hidden`: the answer is opaque, a script may never read it. -/
  | done (id : Nat) (status : Nat) (type : String) (url : String) (hidden : Bool) (body : Option ByteArray)
  /-- The element's request failed. -/
  | fail (id : Nat) (why : String)
  deriving Inhabited

/-- The request an element makes. `cors`: `none` without `crossorigin` ("no-cors"), `some
false` for "anonymous", `some true` for "use-credentials". -/
def request (id : Nat) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) : Transfer :=
  { id, page, method := "GET", url, headers := [], body := none, noCors := cors.isNone,
    credentials := cors == some true, destination := kind, referrer, referrerPolicy := policy }

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

/-- Is an answer of type essence `type` usable for destination `kind` (Fetch §4.1 "should
response to request be blocked due to its MIME type" and "due to nosniff"; HTML §4.6.7.2 for
style sheets): a style sheet of another origin, or one sent with `nosniff`, is `text/css`; a
script is never an image, audio, video or CSV type, and with `nosniff` has a JavaScript type.
`same`: the answer is of the page's own origin. -/
def typeOk (kind : String) (same nosniff : Bool) (type : String) : Bool :=
  if kind == "style" then type == "text/css" || (same && !nosniff)
  else if kind == "script" then
    !(type.startsWith "image/" || type.startsWith "audio/" || type.startsWith "video/" || type == "text/csv") &&
      (!nosniff || javaScriptType type)
  else true

/-- The answer was sent with `X-Content-Type-Options: nosniff`. -/
def nosniffOf (hs : List (String × String)) : Bool :=
  (headerGet hs "x-content-type-options").any fun v => lower (trimWs ((v.splitOn ",").headD "")) == "nosniff"

/-- The JSON parser breakers: prefixes a server puts before data so that a `<script>` of
another site cannot run it (CORB; under ORB a body that does not parse as a script is
blocked, and none of these does). -/
def jsonParserBreakers : List String := [")]}'", "{}&&", "{} &&"]

/-- `body` begins with the bytes of `p`. Reads at most `p`'s length of `body`. -/
def bytesStartWith (body : ByteArray) (p : String) : Bool :=
  let b := p.toUTF8
  b.size ≤ body.size && (body.extract 0 b.size).toList == b.toList

/-- ORB's "opaque-blocklisted-never-sniffed MIME type": an opaque answer of one of these types
is never a script, an image or media. -/
def orbNeverSniffed (e : String) : Bool :=
  ["application/gzip", "application/msexcel", "application/mspowerpoint", "application/msword",
   "application/msword-template", "application/pdf", "application/vnd.ces-quickpoint",
   "application/vnd.ces-quicksheet", "application/vnd.ces-quickword", "application/vnd.ms-excel",
   "application/vnd.ms-excel.sheet.macroenabled.12", "application/vnd.ms-powerpoint",
   "application/vnd.ms-powerpoint.presentation.macroenabled.12", "application/vnd.ms-word",
   "application/vnd.ms-word.document.12", "application/vnd.ms-word.document.macroenabled.12",
   "application/vnd.msword", "application/vnd.openxmlformats-officedocument.presentationml.presentation",
   "application/vnd.openxmlformats-officedocument.presentationml.template",
   "application/vnd.openxmlformats-officedocument.spreadsheetml.sheet",
   "application/vnd.openxmlformats-officedocument.spreadsheetml.template",
   "application/vnd.openxmlformats-officedocument.wordprocessingml.document",
   "application/vnd.openxmlformats-officedocument.wordprocessingml.template",
   "application/vnd.presentation-openxml", "application/vnd.presentation-openxmlm",
   "application/vnd.spreadsheet-openxml", "application/vnd.wordprocessing-openxml",
   "application/x-gzip", "application/x-protobuf", "application/x-protobuffer", "application/zip",
   "audio/mpegurl", "multipart/byteranges", "multipart/signed", "text/event-stream", "text/csv",
   "text/vtt"].contains e

/-- The first at most 1024 bytes of `body`, as ORB reads to sniff. -/
def sniffBytes (body : ByteArray) : ByteArray := body.extract 0 (min body.size 1024)

/-- An answer labelled HTML whose first bytes, after white space, open an HTML document (a
doctype, or an `html`, `head` or `body` tag, in any case): CORB's HTML sniff, which no
script passes. A comment start is not counted (HTML and JavaScript polyglots begin with one).
Reads at most 1024 bytes. -/
def sniffsHtml (body : ByteArray) : Bool :=
  let s := (String.fromUTF8? (sniffBytes body)).getD ""
  let s := lower s.trimAscii.toString
  ["<!doctype html", "<html", "<head", "<body"].any fun p => s.startsWith p

/-- A classic script's answer that the element may not run (Fetch §4.1 "should response to
request be blocked due to its MIME type" and "due to nosniff"), and for an opaque answer (a
"no-cors" answer of another origin) the opaque-response blocking: a type ORB never sniffs, a
body that begins with a JSON parser breaker, or an answer labelled HTML that sniffs as HTML.
The work reads at most 1024 bytes of the body, whatever its size. -/
def scriptBlocked (isOpaque : Bool) (headers : List (String × String)) (body : ByteArray) : Bool :=
  let ty := essence ((headerGet headers "content-type").getD "")
  !typeOk "script" (!isOpaque) (nosniffOf headers) ty ||
    (isOpaque && (orbNeverSniffed ty || jsonParserBreakers.any (bytesStartWith body) ||
      (ty == "text/html" && sniffsHtml body)))

/-- Kind: security theorem (opaque-response blocking). Says: an opaque answer that begins with
a JSON parser breaker never runs as a script, whatever its type. -/
theorem scriptBlocked_breaker (hs : List (String × String)) (body : ByteArray) (p : String)
    (hp : p ∈ jsonParserBreakers) (hb : bytesStartWith body p = true) : scriptBlocked true hs body = true := by
  have hb' : jsonParserBreakers.any (bytesStartWith body) = true := List.any_eq_true.mpr ⟨p, hp, hb⟩
  simp [scriptBlocked, hb']

/-- Kind: security theorem (Fetch §4.1). Says: an answer sent as an image never runs as a
script. -/
theorem scriptBlocked_image (o : Bool) (hs : List (String × String)) (body : ByteArray)
    (h : (essence ((headerGet hs "content-type").getD "")).startsWith "image/" = true) :
    scriptBlocked o hs body = true := by
  simp [scriptBlocked, typeOk, h]

#guard scriptBlocked true [("content-type", "text/plain")] ")]}'\n{}".toUTF8
#guard scriptBlocked true [("content-type", "application/javascript")] "{} &&{}".toUTF8
#guard !scriptBlocked true [("content-type", "application/javascript")] "var x = 1".toUTF8
#guard !scriptBlocked false [("content-type", "text/plain")] ")]}'".toUTF8
#guard scriptBlocked false [("content-type", "text/plain"), ("x-content-type-options", "nosniff")] "x".toUTF8
#guard scriptBlocked true [("content-type", "text/html")] "\n <!DOCTYPE html>\n<html>".toUTF8
#guard !scriptBlocked true [("content-type", "text/html")] "<!--/*--><html><body><script>".toUTF8
#guard scriptBlocked true [("content-type", "application/pdf")] "var x".toUTF8
#guard !scriptBlocked false [("content-type", "application/pdf")] "var x".toUTF8

/-- An ok status (Fetch §2.2.6). -/
def okStatus (s : Nat) : Bool := 200 ≤ s && s ≤ 299

/-- The table after a step of transfer `id`, and what the host is told. `last`: the answer
the step came from (none for the first plan). -/
def after (tab : Table) (id : Nat) (last : Option Answer) : Step → Table × Out
  | .send t w => ({ tab with live := (id, t) :: tab.live }, .wire id w)
  | .fail why => (tab, .fail id why)
  | .deliver t r =>
    match last with
    | some a =>
      if !okStatus a.status then (tab, .fail id s!"status {a.status}") else
      if !typeOk t.destination t.same (nosniffOf a.headers) (essence ((headerGet a.headers "content-type").getD "")) then
        (tab, .fail id "refused: the type is not one this element may use") else
      (tab, .done id a.status ((headerGet a.headers "content-type").getD "")
        (if a.url.isEmpty then t.url else a.url) (r.tainting == "opaque") none)
    | none =>
      -- a `data:` URL, answered in the engine (`PageFetch.dataStep`)
      (tab, .done id r.status ((headerGet r.headers "content-type").getD "") r.url false (some r.body))

/-- Start an element's request. -/
def start (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) : Table × Out :=
  let id := tab.next
  let tab := { tab with next := id + 1 }
  if !kinds.contains kind then (tab, .fail id "unknown destination")
  else if tab.live.length ≥ maxLive then (tab, .fail id "too many requests")
  else if url.startsWith "blob:" then (tab, .fail id "blob: URLs are a script session's")
  else after tab id none (plan (request id page kind url referrer policy cors))

/-- The host's answer to the request of transfer `id`. -/
def answer (tab : Table) (id : Nat) (a : Answer) : Table × Out :=
  match tab.live.find? (·.1 == id) with
  | none => (tab, .fail id "no such request")
  | some (_, t) => after { tab with live := tab.live.filter (·.1 != id) } id (some a) (onAnswer t a)

/-- The host stops the transfer (the element went away, the page closed). -/
def cancel (tab : Table) (id : Nat) : Table := { tab with live := tab.live.filter (·.1 != id) }

/-! ## Examples -/

private def page : Page := Page.ofUrl "https://a.example/page.html"
private def wireUrl : Table × Out → String
  | (_, .wire _ w) => w.url
  | (_, .done _ _ _ u _ _) => "done " ++ u
  | (_, .fail _ why) => "fail " ++ why
-- names are resolved first (the DNS pin): the host answers the addresses, then the request goes
private def resolved : Table × Out → Table × Out
  | (tab, .wire id w) => if w.resolve then answer tab id { addresses := ["93.184.216.34"] } else (tab, .wire id w)
  | o => o

#guard wireUrl (resolved (start {} page "image" "https://b.example/x.png" "https://a.example/page.html" .default none)) == "https://b.example/x.png"
#guard wireUrl (start {} page "image" "http://b.example/x.png" "https://a.example/page.html" .default none) == "fail refused by policy"
#guard wireUrl (start {} page "image" "https://127.0.0.1/x.png" "https://a.example/page.html" .default none) == "fail refused by policy"
#guard wireUrl (start {} page "frobnicate" "https://b.example/x.png" "" .default none) == "fail unknown destination"
#guard (match start {} page "image" "data:image/gif;base64,R0lGODlhAQABAAAAACw=" "" .default none with
  | (_, .done _ 200 ty _ false (some b)) => ty == "image/gif" && b.size == 14
  | _ => false)
-- the Referer of an image request under the default policy: the origin only, across origins
#guard (match resolved (start {} page "image" "https://b.example/x.png" "https://a.example/page.html?q" .default none) with
  | (_, .wire _ w) => !w.resolve && w.address == "93.184.216.34" && headerGet w.headers "referer" == some "https://a.example/" &&
      headerGet w.headers "sec-fetch-dest" == some "image" && headerGet w.headers "sec-fetch-mode" == some "no-cors" &&
      headerGet w.headers "cookie" == none
  | _ => false)
-- the answer: a redirect is followed here; the final answer is opaque across origins
#guard (match resolved (start {} page "image" "https://a.example/r" "" .default none) with
  | (tab, .wire id _) =>
    match resolved (answer tab id { status := 302, headers := [("Location", "https://b.example/y.png")] }) with
    | (tab, .wire id' w) => w.url == "https://b.example/y.png" &&
      (match answer tab id' { status := 200, headers := [("Content-Type", "image/png")] } with
       | (tab, .done _ 200 "image/png" "https://b.example/y.png" true none) => tab.live.isEmpty
       | _ => false)
    | _ => false
  | _ => false)
#guard (match resolved (start {} page "image" "https://a.example/x.png" "" .default none) with
  | (tab, .wire id _) => match answer tab id { status := 404 } with | (_, .fail _ _) => true | _ => false
  | _ => false)
-- a style sheet of another origin that is not text/css is refused; one of the page's origin is used
#guard (match resolved (start {} page "style" "https://b.example/s.css" "" .default none) with
  | (tab, .wire id _) => match answer tab id { status := 200, headers := [("Content-Type", "text/plain")] } with | (_, .fail _ _) => true | _ => false
  | _ => false)
#guard (match resolved (start {} page "style" "https://a.example/s.css" "" .default none) with
  | (tab, .wire id _) => match answer tab id { status := 200, headers := [("Content-Type", "text/plain")] } with | (_, .done ..) => true | _ => false
  | _ => false)
#guard (match resolved (start {} page "script" "https://a.example/s.js" "" .default none) with
  | (tab, .wire id _) => match answer tab id { status := 200, headers := [("Content-Type", "text/plain"), ("X-Content-Type-Options", "nosniff")] } with
    | (_, .fail _ _) => true | _ => false
  | _ => false)
-- a name that resolves to a special-purpose address is refused
#guard (match start {} page "image" "https://intranet.example/x.png" "" .default none with
  | (tab, .wire id _) => match answer tab id { addresses := ["10.0.0.1"] } with | (_, .fail _ _) => true | _ => false
  | _ => false)

/-! ## Theorems -/

/-- Kind: lemma. Says: `after` tells the host to make exactly the request of a `send` step. -/
theorem after_wire (tab : Table) (id : Nat) (last : Option Answer) (st : Step) (tab' : Table) (id' : Nat) (w : Wire)
    (h : after tab id last st = (tab', .wire id' w)) : ∃ t, st = .send t w := by
  unfold after at h
  split at h
  · rename_i t w0
    simp only [Prod.mk.injEq, Out.wire.injEq] at h
    exact ⟨t, by rw [h.2.2]⟩
  · simp at h
  · split at h
    · split at h
      · simp at h
      · split at h <;> simp at h
    · simp at h

/-- Kind: lemma. Says: a `start` that tells the host to make a request does so for the plan of
the element's request. -/
theorem start_send (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) (tab' : Table) (id : Nat) (w : Wire)
    (h : start tab page kind url referrer policy cors = (tab', .wire id w)) :
    ∃ t, plan (request tab.next page kind url referrer policy cors) = .send t w := by
  unfold start at h
  by_cases h1 : (!kinds.contains kind) = true
  · simp only [h1, if_true] at h; simp at h
  · simp only [h1, if_false, Bool.false_eq_true] at h
    by_cases h2 : tab.live.length ≥ maxLive
    · simp only [h2, if_true] at h; simp at h
    · simp only [h2, if_false] at h
      by_cases h3 : url.startsWith "blob:" = true
      · simp only [h3, if_true] at h; simp at h
      · simp only [h3, if_false, Bool.false_eq_true] at h
        exact after_wire _ _ _ _ _ _ _ h

/-- Kind: policy theorem. Says: the first request an element's `start` tells the host to make
passes `mayConnect` for the page on the URL the host gets (scheme, local address, mixed
content) and `wireReach` (no special-purpose address for a page from the network). -/
theorem start_wire (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) (tab' : Table) (id : Nat) (w : Wire)
    (h : start tab page kind url referrer policy cors = (tab', .wire id w)) :
    ∃ u, URL.parseUrl w.url = some u ∧ mayConnect page u = true ∧ wireReach page w = true := by
  obtain ⟨t, ht⟩ := start_send _ _ _ _ _ _ _ _ _ _ h
  obtain ⟨ha, hu, hr, -⟩ := plan_send_allowed _ _ _ ht
  unfold Transfer.allowed at ha
  split at ha
  · rename_i u hp
    refine ⟨u, ?_, ha, hr⟩
    rw [hu]; exact hp
  · simp at ha

/-- Kind: policy theorem (DNS rebinding, every hop). Says: every later request of an
element's transfer passes `wireReach` for the page that started it. -/
theorem answer_wire (tab : Table) (id : Nat) (a : Answer) (tab' : Table) (id' : Nat) (w : Wire)
    (h : answer tab id a = (tab', .wire id' w)) :
    ∃ t, (id, t) ∈ tab.live ∧ wireReach t.page w = true := by
  unfold answer at h
  split at h
  · simp at h
  · rename_i i t he
    obtain ⟨t', ht⟩ := after_wire _ _ _ _ _ _ _ h
    have hm := List.mem_of_find?_eq_some he
    have hid : i = id := by simpa using List.find?_some he
    refine ⟨t, ?_, onAnswer_reach _ _ _ _ ht⟩
    rw [← hid]; exact hm

/-- Kind: policy theorem (mixed content). Says: an `https` document's element never makes
the host send a first request to an URL that is not `https`. -/
theorem start_mixed (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) (tab' : Table) (id : Nat) (w : Wire) (hs : page.secure = true)
    (h : start tab page kind url referrer policy cors = (tab', .wire id w)) :
    ∃ u, URL.parseUrl w.url = some u ∧ u.scheme = "https" := by
  obtain ⟨u, hu, hc, -⟩ := start_wire _ _ _ _ _ _ _ _ _ _ h
  refine ⟨u, hu, ?_⟩
  unfold mayConnect at hc
  simp only [hs, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at hc
  exact hc.2

/-- Kind: security theorem (HTML §4.6.7.2, Fetch §4.1). Says: a style sheet the host is told
to use is `text/css`, or of the page's own origin and not sent with `nosniff`. -/
theorem after_style_type (tab : Table) (id : Nat) (a : Answer) (t : Transfer) (r : Response) (tab' : Table)
    (id' st : Nat) (ty u : String) (hd : Bool) (b : Option ByteArray) (hk : t.destination = "style")
    (h : after tab id (some a) (.deliver t r) = (tab', .done id' st ty u hd b)) :
    essence ty = "text/css" ∨ (t.same = true ∧ nosniffOf a.headers = false) := by
  unfold after at h
  by_cases h1 : (!okStatus a.status) = true
  · simp [h1] at h
  · simp only [h1, if_false, Bool.false_eq_true] at h
    by_cases h2 : (!typeOk t.destination t.same (nosniffOf a.headers) (essence ((headerGet a.headers "content-type").getD ""))) = true
    · simp [h2] at h
    · simp only [h2, if_false, Bool.false_eq_true, Prod.mk.injEq, Out.done.injEq] at h
      obtain ⟨-, -, -, rfl, -⟩ := h
      simp only [Bool.not_eq_true', Bool.not_eq_false] at h2
      simp only [typeOk, hk, if_true, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, Bool.not_eq_true'] at h2
      exact h2

/-- Kind: policy theorem. Says: a request of a destination this file does not know is
refused before anything is sent. -/
theorem kind_known (tab : Table) (page : Page) (kind url referrer : String) (policy : ReferrerPolicy.Policy)
    (cors : Option Bool) (hk : kinds.contains kind = false) :
    ∃ tab' id why, start tab page kind url referrer policy cors = (tab', .fail id why) := by
  have : (!kinds.contains kind) = true := by rw [hk]; rfl
  unfold start
  simp only [this, if_true]
  exact ⟨_, _, _, rfl⟩

end L4Factoidal.Net.Subresource
