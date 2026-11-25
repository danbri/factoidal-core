/-
L4Factoidal.WasmVM.Hosts.LeanJSModules: the module scripts of a document and their module
graph, fetched before any script of the page runs (record:
docs/designissues/2026-11-13-module-scripts.md).

HTML §8.1.4 (fetching scripts) and §4.12.1 (the script element), decided here; the host only
makes the requests it is told to make:

* A module script is `<script type="module">`, inline or with `src` (resolved against the
  document's base URL).
* Every module is fetched in CORS mode (`Net.PageFetch.Transfer`, the same rules as a page's
  `fetch`: policy, preflight, CORS check, redirects, DNS pin). Credentials are never sent;
  `crossorigin="use-credentials"` only makes the CORS check the credentialed one.
* A response is a module only when its status is ok (200 to 299) and its MIME type is a
  JavaScript MIME type (`isJavaScriptMime`); its body is decoded as UTF-8 (BOM sniffed).
* The module map is per document: a URL is fetched once, and a module that two scripts import
  is one module. Its key is the request URL; the module's base URL is the response URL.
* A module specifier is a URL (`/`, `./`, `../` relative to the module, or absolute). A bare
  specifier is a TypeError: import maps are not supported.
* Fetching uses the sync answers of a start (`netSync`): the requests are made one at a time
  in a fixed order, and the start is made again with each answer; no script runs until the
  whole graph is there, so nothing runs twice.

What a module script then does (`outcome`): a failed fetch anywhere in its graph fires
`error` at the element; a parse error or an unresolvable specifier is reported at the
window (SyntaxError, TypeError); otherwise its graph is linked and evaluated
(`JS.runModuleGraph`), after the classic scripts, in document order.
-/
import L4Factoidal.JS.Modules
import L4Factoidal.Net.Xhr
import L4Factoidal.WHATWG.Encoding.Core
import L4Factoidal.DOM.Arena

namespace L4Factoidal.WasmVM.Hosts.LeanJSModules
open L4Factoidal
open L4Factoidal.Net.PageFetch

/-- The JavaScript MIME type essences (MIME Sniffing §4.6). -/
def javaScriptMimes : List String :=
  ["application/ecmascript", "application/javascript", "application/x-ecmascript",
   "application/x-javascript", "text/ecmascript", "text/javascript", "text/javascript1.0",
   "text/javascript1.1", "text/javascript1.2", "text/javascript1.3", "text/javascript1.4",
   "text/javascript1.5", "text/jscript", "text/livescript", "text/x-ecmascript",
   "text/x-javascript"]

/-- A `Content-Type` value names a JavaScript MIME type. -/
def isJavaScriptMime (contentType : String) : Bool :=
  javaScriptMimes.contains (Net.Xhr.mimeEssence contentType)

/-- What a response is as a module: its text, or why it is not one (HTML §8.1.4.2 "fetch a
single module script", steps on the response). -/
def moduleText (r : Response) : Except String String :=
  if r.status < 200 || r.status > 299 then .error s!"status {r.status}"
  else match headerGet r.headers "content-type" with
    | some ct => if isJavaScriptMime ct then .ok (WHATWG.Encoding.decode r.body .utf_8)
                 else .error s!"MIME type {Net.Xhr.mimeEssence ct} is not JavaScript"
    | none => .error "no MIME type"

/-- A module specifier resolved against a base URL (HTML §8.1.5.2, with no import map). -/
def resolveSpecifier (spec base : String) : Option String :=
  if spec.startsWith "/" || spec.startsWith "./" || spec.startsWith "../" then
    (WHATWG.URL.parseUrl spec (some base)).map (·.serialize)
  else (WHATWG.URL.parseUrl spec none).map (·.serialize)

/-- What a URL of the module map holds. -/
inductive Entry where
  /-- A module, at this index of the graph. -/
  | node (i : Nat)
  | failed (why : String)
  | parseError (msg : String)
  deriving Inhabited, BEq, Repr

/-- A request of a module: the module map's entry, or a specifier that is not a URL. -/
inductive Child where
  | entry (e : Entry)
  | unresolved (spec : String)
  deriving Inhabited, BEq, Repr

/-- What a module script does. -/
inductive Outcome where
  /-- Link and evaluate the graph from this module; `external`: fire `load` after. -/
  | run (root : Nat) (external : Bool)
  /-- Fire `error` at the element. -/
  | fetchError
  /-- Report this error at the window: a SyntaxError (`isSyntax`) or a TypeError. -/
  | rethrow (isSyntax : Bool) (msg : String)
  deriving Inhabited, BEq, Repr

/-- A module fetched and parsed by an earlier attempt of the same start: the request (URL,
credentials, and the number of answers used before it), the number used after it, and what it
gave: why the fetch failed, or the parse of the text (an error, or the module). The start is
made again after each answer (`WebScripts`, `syncCache`), and each attempt reads the same
answers in the same order, so the fetches before the new answer give the same results: kept
here, they are not decoded and parsed again (BBC News, 130 modules: 79 s of the engine's time
in attempts, n² in the number of modules). -/
structure Fetched where
  url : String
  credentials : Bool
  usedBefore : Nat
  usedAfter : Nat
  result : Except String (Except String JS.ModNode)
  deriving Inhabited

/-- The module graph of a document, as fetched so far. -/
structure Loader where
  page : Page
  answers : Array Answer
  used : Nat := 0
  /-- The request the host is to make next; set once, when an answer is missing. -/
  wanted : Option Wire := none
  map : Array (String × Entry) := #[]
  graph : JS.ModGraph := #[]
  /-- The requests of each module of the graph, by graph index. -/
  kids : Array (Array (String × Child)) := #[]
  /-- The modules fetched and parsed, by this attempt and the attempts before (`Fetched`). -/
  memo : Array Fetched := #[]
  deriving Inhabited

/-- Follow a transfer through the answers: the response, why it failed, or `none` when the
next answer is not there yet (`wanted` set). -/
def fetchSteps : Nat → Loader → Step → Loader × Option (Except String Response)
  | 0, l, _ => (l, some (.error "too many steps"))
  | n + 1, l, step =>
    match step with
    | .fail why => (l, some (.error why))
    | .deliver _ r => (l, some (.ok r))
    | .send t w =>
      match l.answers[l.used]? with
      | none => ({ l with wanted := some w }, none)
      | some a => fetchSteps n { l with used := l.used + 1 } (onAnswer t a)

/-- The first request of a module fetch: `GET` in CORS mode (`credentials` only for the CORS
check of `crossorigin="use-credentials"`). -/
def moduleTransfer (p : Page) (url : String) (credentials : Bool) : Transfer :=
  { id := 0, page := p, method := "GET", url, headers := [("Accept", "*/*")], body := none, credentials }

/-- Fetch `url` as a module: its response URL and text, why it failed, or `none` (waiting). -/
def fetchModule (l : Loader) (url : String) (credentials : Bool) : Loader × Option (Except String (String × String)) :=
  match fetchSteps 64 l (plan (moduleTransfer l.page url credentials)) with
  | (l, none) => (l, none)
  | (l, some (.error why)) => (l, some (.error why))
  | (l, some (.ok r)) => (l, some ((moduleText r).map fun t => (if r.url.isEmpty then url else r.url, t)))

/-- A parsed module in the graph (or its parse error), with no requests followed yet. -/
def addParsed (l : Loader) (parsed : Except String JS.ModNode) : Loader × Entry :=
  match parsed with
  | .error e => (l, .parseError e)
  | .ok node =>
    let i := l.graph.size
    ({ l with graph := l.graph.push node, kids := l.kids.push #[] }, .node i)

/-- The parse of module text `text` at `url`. -/
def parseAt (url text : String) : Except String JS.ModNode :=
  (JS.parseModule text).map (JS.ModNode.ofSyntax url)

/-- A parsed module in the graph, with no requests followed yet. -/
def addModule (l : Loader) (url text : String) : Loader × Entry :=
  addParsed l (parseAt url text)

/-- Fetch and parse `url` (`fetchModule`, `parseAt`), or take what an earlier attempt kept for the
same request at the same point of the answers (`Fetched`). -/
def fetchParsed (l : Loader) (url : String) (cred : Bool) :
    Loader × Option (Except String (Except String JS.ModNode)) :=
  match l.memo.find? (fun f => f.url == url && f.credentials == cred && f.usedBefore == l.used) with
  | some f => ({ l with used := f.usedAfter }, some f.result)
  | none =>
    let before := l.used
    match fetchModule l url cred with
    | (l, none) => (l, none)
    | (l, some r) =>
      let res := r.map fun (final, text) => parseAt final text
      ({ l with memo := l.memo.push { url, credentials := cred, usedBefore := before, usedAfter := l.used, result := res } }, some res)

/-- Kind: equivalence. Says: with nothing kept for the request, `fetchParsed` answers what
`fetchModule` and `parseAt` answer, and moves through the answers as `fetchModule` does. Does
not say that a kept entry is right: that holds when each entry was made by this function on the
same page and the same answers before `usedAfter`, which `WebScripts` keeps by holding the memo
only between the attempts of one start (it is cleared with `syncCache`); that is not proved. -/
theorem fetchParsed_miss (l : Loader) (url : String) (cred : Bool)
    (h : l.memo.find? (fun f => f.url == url && f.credentials == cred && f.usedBefore == l.used) = none) :
    (fetchParsed l url cred).2 = (fetchModule l url cred).2.map (·.map fun (final, text) => parseAt final text) ∧
    (fetchParsed l url cred).1.used = (fetchModule l url cred).1.used := by
  unfold fetchParsed
  rw [h]
  simp only []
  cases fetchModule l url cred with
  | mk l' r => cases r <;> simp

/-- Record request `spec` of module `i` as `c` (a module also becomes a dependency). -/
def addKid (l : Loader) (i : Nat) (spec : String) (c : Child) : Loader :=
  let l := { l with kids := l.kids.modify i (·.push (spec, c)) }
  match c with
  | .entry (.node j) => { l with graph := l.graph.modify i fun m => { m with deps := m.deps.push (spec, j) } }
  | _ => l

mutual
/-- Fetch the graph from `url` (HTML "fetch a module script graph", in a fixed order): the
module map's entry for it, or `none` while an answer is missing. A URL already in the map is
not fetched again (a cycle ends there). -/
def visit : Nat → Loader → String → Bool → Loader × Option Entry
  | 0, l, _, _ => (l, some (.failed "module graph too deep"))
  | n + 1, l, url, cred =>
    match l.map.find? (·.1 == url) with
    | some (_, e) => (l, some e)
    | none =>
      match fetchParsed l url cred with
      | (l, none) => (l, none)
      | (l, some (.error why)) => ({ l with map := l.map.push (url, .failed why) }, some (.failed why))
      | (l, some (.ok parsed)) =>
        let (l, e) := addParsed l parsed
        let l := { l with map := l.map.push (url, e) }
        match e with
        | .node i =>
          match visitKids n l i ((l.graph[i]?.map (·.syn.requests.toList)).getD []) cred with
          | (l, true) => (l, some e)
          | (l, false) => (l, none)
        | _ => (l, some e)

/-- Fetch the requests of module `i` in order; `false` while an answer is missing. -/
def visitKids : Nat → Loader → Nat → List String → Bool → Loader × Bool
  | 0, l, _, _, _ => (l, true)
  | _ + 1, l, _, [], _ => (l, true)
  | n + 1, l, i, spec :: rest, cred =>
    let base := (l.graph[i]?.map (·.url)).getD ""
    match resolveSpecifier spec base with
    | none => visitKids n (addKid l i spec (.unresolved spec)) i rest cred
    | some u =>
      match visit n l u cred with
      | (l, none) => (l, false)
      | (l, some e) => visitKids n (addKid l i spec (.entry e)) i rest cred
end

/-- The outcome of a module script whose graph starts at `root` (HTML "fetch a module script
graph" and "find the first parse error"): a failed fetch anywhere is the `error` event; then
the first parse error or unresolvable specifier, depth first, is reported. -/
def outcome (l : Loader) (root : Entry) (external : Bool) : Outcome :=
  match root with
  | .failed _ => .fetchError
  | .parseError m => .rethrow true m
  | .node r =>
    let reach := JS.evalOrder l.graph r
    let kids := reach.flatMap fun i => ((l.kids[i]?).getD #[]).toList.map (·.2)
    if kids.any (fun c => match c with | .entry (.failed _) => true | _ => false) then .fetchError else
    let firstErr := (reach.reverse.flatMap fun i => ((l.kids[i]?).getD #[]).toList).findSome? fun (_, c) =>
      match c with
      | .entry (.parseError m) => some (Outcome.rethrow true m)
      | .unresolved s => some (.rethrow false s!"Failed to resolve module specifier \"{s}\": import maps are not supported, and a relative specifier must start with \"/\", \"./\" or \"../\"")
      | _ => none
    firstErr.getD (.run r external)

/-- A module script element: its node, its URL (an external script) or its text (inline), and
whether its fetches use the credentialed CORS check. -/
structure Script where
  node : Nat
  src : Option String
  source : String
  credentials : Bool
  deriving Inhabited

private def attrOf (n : DOM.Node) (name : String) : Option String :=
  (n.attrs.find? (fun a => a.ns.isNone && a.lname == name)).map (·.value)

/-- The `type` of a script element names a module script. -/
def isModuleType (n : DOM.Node) : Bool :=
  ((attrOf n "type").getD "").trimAscii.toString.toLower == "module"

/-- The document's base URL: the first `base` element with `href`, resolved against the
document's URL (HTML §2.4.1, frozen base URL). -/
def baseOf (dom : DOM.Dom) (url : String) : String := Id.run do
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "base" then
      if let some h := attrOf n "href" then
        return ((WHATWG.URL.parseUrl h (some url)).map (·.serialize)).getD url
  return url

/-- The module script elements of the document, in tree order. -/
def scriptsOf (dom : DOM.Dom) : Array Script := Id.run do
  let mut out := #[]
  for id in dom.treeOrder 0 do
    let n := dom.get id
    if DOM.Dom.isHtmlElement n "script" && isModuleType n then
      let cred := ((attrOf n "crossorigin").map (·.trimAscii.toString.toLower)) == some "use-credentials"
      out := out.push { node := id, src := attrOf n "src", source := (dom.textContent id).getD "", credentials := cred }
  return out

/-- The module scripts of a document and their graph: what each does. -/
structure Loaded where
  graph : JS.ModGraph := #[]
  scripts : Array (Nat × Outcome) := #[]
  /-- The sync answers the fetches used (the ones after are a script's `XMLHttpRequest`s). -/
  used : Nat := 0
  deriving Inhabited

/-- Load already collected module scripts. A missing answer asks the host for the next
request. Retain fetched and parsed modules for a subsequent call with more answers. -/
def loadScripts (scripts : Array Script) (base : String) (page : Page) (answers : Array Answer)
    (memo : Array Fetched := #[]) : Except Wire Loaded × Array Fetched := Id.run do
  if scripts.isEmpty then return (.ok {}, memo)
  let mut l : Loader := { page, answers, memo }
  let mut out : Array (Nat × Outcome) := #[]
  for sc in scripts do
    match sc.src with
    | some src =>
      match resolveSpecifier' src base with
      | none => out := out.push (sc.node, .fetchError)
      | some url =>
        let (l', e) := visit 4096 l url sc.credentials
        l := l'
        match e with
        | none => return (.error (l.wanted.getD (moduleTransfer page url sc.credentials).mainWire), l.memo)
        | some e => out := out.push (sc.node, outcome l e true)
    | none =>
      let (l', e) := addModule l base sc.source
      l := l'
      match e with
      | .node i =>
        let (l', ok) := visitKids 4096 l i ((l.graph[i]?.map (·.syn.requests.toList)).getD []) sc.credentials
        l := l'
        if !ok then return (.error (l.wanted.getD (moduleTransfer page base sc.credentials).mainWire), l.memo)
        out := out.push (sc.node, outcome l e false)
      | e => out := out.push (sc.node, outcome l e false)
  return (.ok { graph := l.graph, scripts := out, used := l.used }, l.memo)
where
  /-- The `src` of a script element: any URL, relative to the document's base URL. -/
  resolveSpecifier' (src base : String) : Option String :=
    if src.isEmpty then none else (WHATWG.URL.parseUrl src (some base)).map (·.serialize)

/-- Collect a document's module scripts and load their graphs. -/
def load (dom : DOM.Dom) (docUrl : String) (page : Page) (answers : Array Answer)
    (memo : Array Fetched := #[]) : Except Wire Loaded × Array Fetched :=
  let scripts := scriptsOf dom
  if scripts.isEmpty then (.ok {}, memo)
  else loadScripts scripts (baseOf dom docUrl) page answers memo

/-! ## Theorems -/

/-- Kind: security property. Says: a response is never a module unless its status is ok and its
`Content-Type` names a JavaScript MIME type (HTML §8.1.4.2: a style sheet, an image or a JSON
file served cross-site is not run as script). Does not say: what the MIME type of a response
is; the server sends it. -/
theorem moduleText_ok (r : Response) (t : String) (h : moduleText r = .ok t) :
    200 ≤ r.status ∧ r.status ≤ 299 ∧ ∃ ct, headerGet r.headers "content-type" = some ct ∧ isJavaScriptMime ct = true := by
  unfold moduleText at h
  by_cases hs : r.status < 200 || r.status > 299
  · simp [hs] at h
  · simp only [hs, Bool.false_eq_true, ↓reduceIte] at h
    simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_lt] at hs
    refine ⟨hs.1, hs.2, ?_⟩
    cases hc : headerGet r.headers "content-type" with
    | none => simp [hc] at h
    | some ct =>
      by_cases hj : isJavaScriptMime ct = true
      · exact ⟨ct, rfl, hj⟩
      · simp [hc, hj] at h

/-- Kind: invariant. Says: a document with no module script asks the host for nothing and
uses no answer, and keeps the modules it was given. Does not say: anything about its classic scripts. -/
theorem load_none (dom : DOM.Dom) (url : String) (p : Page) (a : Array Answer) (m : Array Fetched) (h : scriptsOf dom = #[]) :
    load dom url p a m = (.ok {}, m) := by
  simp [load, h]

end L4Factoidal.WasmVM.Hosts.LeanJSModules
