/-
L4Factoidal.WasmVM.Hosts.LeanJSWorkers: dedicated workers (HTML §10) for pages on
BubblePopJS (record: docs/designissues/2026-11-09-dedicated-workers.md).

Each worker is a `LeanJS.Session` of its own: its own realm and heap (a copy of the page
realm with the prelude, made a `DedicatedWorkerGlobalScope` by the prelude's section
workers), its own host with an empty arena (no DOM), its own event loop, script clock,
entropy and step budget. The page and its workers are agents of the model
`L4Factoidal.EventLoop.Agents`, whose theorems say what this code keeps:

- a message is a task on the receiver (`eventHandle`, source `postedMessage`), with its
  bytes in the receiver's inbox; inbox and tasks are both first in, first out, so each
  channel (page to worker, worker to page) delivers in order;
- only bytes cross (`JS.Clone`): no heap value or DOM node of one agent reaches another;
- a terminated or closed worker runs no further task.

Scheduling is interleaved on one thread, deterministically: after each microtask
checkpoint of the page (`engine.runJobs`), `pump` hands the page's asks to the workers and
runs each worker's due tasks at the page's clock; a worker timer arms one page timer
(`wakeHandle`) at its due time, so the page's own loop (`PageEvents.advance`, `settle`)
stops there and the workers run then. A page that makes no worker pays one check of an
empty array per checkpoint.

Scripts: a worker's script and its `importScripts` come from the embedder. A run that
needs a script the embedder has not given is undone (the worker's state before the task
is kept: sessions are values) and runs again when the script arrives; `loads` lists the
URLs to fetch (a turn's `fetches`), and the action `fetched` gives them.
-/
import L4Factoidal.WasmVM.Hosts.LeanJS
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Net.Xhr

namespace L4Factoidal.WasmVM.Hosts.LeanJSWorkers
open L4Factoidal.WasmVM
open L4Factoidal.WasmVM.Hosts
open L4Factoidal.WasmVM.Hosts.LeanJS (Session WorkerOp WorkerEvent WorkerHost)

/-- The callback number of a task that dispatches the next event of the inbox (prelude.js
`WORKER_EVENT`), and of the page timer that wakes the workers. Not numbers the prelude
hands out (it counts from 1). -/
def eventHandle : Nat := 0x7FFFFFF0
def wakeHandle : Nat := 0x7FFFFFF1

/-- Budgets. A worker's run (a script, task or event) has a page run's steps, so a worker
can run any script a page can (a run stopped at the budget is lost, and a WPT test that
runs its subtests in one script at a worker's start needs a page's steps); all workers
together have one page run's steps in one pump, then wait for the page's next turn; a worker whose runs stop at the budget `maxHalts` times, or whose heap passes
`maxObjects`, is stopped with an error at its Worker object. -/
def workerBudget : Nat := LeanJS.runBudget
def pumpSteps : Nat := LeanJS.runBudget
def workerTasks : Nat := 1000
def maxWorkers : Nat := 16
def maxHalts : Nat := 3
def maxObjects : Nat := 4000000
def maxLogs : Nat := 256

inductive Phase where
  /-- Not started: waits for its script (and the scripts its start imports). -/
  | starting
  | running
  /-- A task waits for this script; it runs again when it comes. -/
  | blocked (url : String)
  /-- A task made a sync `XMLHttpRequest`: it was undone and runs again when the answer
  (`Worker.syncWait`) comes. -/
  | syncing
  | closed
  deriving BEq, Inhabited

structure Worker where
  id : Nat
  url : String
  name : String
  phase : Phase := .starting
  s : Session
  /-- Messages from the page before the worker's script ran (its port's queue, HTML
  §10.2.4: enabled after the script runs). -/
  waiting : Array ByteArray := #[]
  /-- Steps run in total, also of runs undone. -/
  steps : Nat := 0
  halts : Nat := 0
  /-- Sync requests (XHR §4.5.2 step 12, allowed in workers): the answers given so far to
  the run being redone (`Net.Xhr.State.syncAnswers`), and the page request whose answer the
  worker waits for. A worker that is starting waits with `phase` still `starting`. -/
  syncCache : Array Net.PageFetch.Answer := #[]
  syncWait : Option Nat := none
  deriving Inhabited

structure Workers where
  list : Array Worker := #[]
  /-- URLs the embedder is to fetch. -/
  loads : Array String := #[]
  /-- Every URL asked for, in order: a fetch's id is its place here plus one. -/
  asked : Array String := #[]
  /-- The URLs of workers' own scripts (kind `worker`); the rest are `script`. -/
  mains : Array String := #[]
  /-- What it fetched (`none`: the fetch failed). -/
  scripts : Array (String × Option String) := #[]
  /-- The `Referrer-Policy` response field of each script fetched, by URL, as the embedder
  gave it ("" for none): a worker's requests have its own script's policy (`workerNet`). -/
  policies : Array (String × String) := #[]
  /-- The page timer armed for the workers' next timer (`wakeHandle`). -/
  wake : Option Nat := none
  steps : Nat := 0
  /-- Workers' requests in flight at the host: the id the host knows (taken from the page's
  own numbering, so it is never a page request's), the worker, and the worker's own id of
  the transfer (`forwardNet`, `giveNet`). -/
  routes : Array (Nat × Nat × Nat) := #[]
  deriving Inhabited

/-- A page on BubblePopJS with its workers, and the realm a worker starts from (the page
realm before any page: `WebScripts.Held.leanBase`). -/
structure Agents where
  page : Session
  w : Workers := {}
  base : Option Session := none
  /-- Fresh entropy for worker `n` from the embedder's own generator (the operating
  system's), as a page's: each worker's DRBG has its own seed, not one derived from the
  page's. Empty (no generator): the worker has no `crypto.getRandomValues`. -/
  entropy : Nat → ByteArray := fun _ => ByteArray.empty

instance : Inhabited Agents := ⟨{ page := default }⟩

/-- A worker session's engine: the page engine's steps, with the event task's callback
kept (it is not a timer's). -/
def wEngine : PageEvents.Engine Session :=
  { LeanJS.engine with release := fun s cb => if cb == eventHandle then s else LeanJS.engine.release s cb }

/-- An event for a realm: its data in the inbox, and its task. -/
def deliver (s : Session) (ev : WorkerEvent) : Session :=
  let s := s.setWk (s.wk.push ev)
  wEngine.setLoop s ((wEngine.loop s).queueTask .postedMessage eventHandle)

def Workers.request (w : Workers) (url : String) : Workers :=
  if w.loads.contains url || w.scripts.any (·.1 == url) then w else
  { w with loads := w.loads.push url, asked := if w.asked.contains url then w.asked else w.asked.push url }

/-- The fetches a turn asks of the embedder: `{id, url, kind}`. -/
def Workers.fetches (w : Workers) : List JSON.Json :=
  w.loads.toList.map fun u =>
    .object [("id", .number (toString (((w.asked.findIdx? (· == u)).getD 0) + 1))), ("url", .string u),
      ("kind", .string (if w.mains.contains u then "worker" else "script"))]

/-- A JavaScript MIME type (MIME Sniffing §4.6), by its essence. -/
def jsMime (contentType : String) : Bool :=
  let essence := (((contentType.splitOn ";").headD "").trimAscii.toString).toLower
  ["application/ecmascript", "application/javascript", "application/x-ecmascript", "application/x-javascript",
   "text/ecmascript", "text/javascript", "text/javascript1.0", "text/javascript1.1", "text/javascript1.2",
   "text/javascript1.3", "text/javascript1.4", "text/javascript1.5", "text/jscript", "text/livescript",
   "text/x-ecmascript", "text/x-javascript"].contains essence

/-- `X-Content-Type-Options: nosniff` (Fetch §2.2.6 "determine nosniff"): the first value of
the field is `nosniff`, ASCII case-insensitively. -/
def nosniffHeader (v : String) : Bool :=
  (((v.splitOn ",").headD "").trimAscii.toString).toLower == "nosniff"

/-- A fetched worker script or imported script runs: the status is ok, the declared type is a
JavaScript MIME type (an embedder that tells no type is trusted to have checked it), and with
`nosniff` (`options`, the `X-Content-Type-Options` field) the declared type must be there and
be JavaScript (Fetch §2.2.6: a script-like destination). -/
def scriptAccepted (status : Nat) (contentType options : String) : Bool :=
  200 ≤ status && status < 300 && (contentType.isEmpty || jsMime contentType) &&
    !(nosniffHeader options && !jsMime contentType)

/-- Kind: security theorem (`nosniff`, worker scripts). Says: with `nosniff`, a worker script
or imported script whose declared type is not a JavaScript MIME type (or is absent) is never
accepted, whatever its status and body. Does not say: that every embedder passes the field
(the WPT runner does; the desktop host passes neither the type nor the field yet). -/
theorem scriptAccepted_nosniff (status : Nat) (contentType options : String)
    (hn : nosniffHeader options = true) (hj : jsMime contentType = false) :
    scriptAccepted status contentType options = false := by
  simp [scriptAccepted, hn, hj]

#guard nosniffHeader "nosniff" && nosniffHeader " NoSniff , x" && !nosniffHeader "" && !nosniffHeader "x, nosniff"
#guard scriptAccepted 200 "text/javascript" "nosniff" && !scriptAccepted 200 "" "nosniff" && scriptAccepted 200 "" ""
#guard !scriptAccepted 200 "text/plain" "" && !scriptAccepted 404 "text/javascript" ""

/-- The origin of a URL, serialized ("null" for none). -/
def originOfUrl (u : String) : String := ((WHATWG.URL.parseUrl u).map (·.origin)).getD "null"

/-- An embedder's answer to a fetch (`{id, status, url, contentType, source}`, and
`contentTypeOptions`, the response's `X-Content-Type-Options` field): the URL it was asked
for and the script, or `none` for a network error (status 0, a status that is not ok, or a
type that is not JavaScript: HTML's fetches of worker scripts and imported scripts are
strict about it; `scriptAccepted`). -/
def Workers.result (w : Workers) (id status : Nat) (url contentType source : String) (options : String := "") :
    Option (String × Option String) :=
  let asked := if id ≥ 1 then w.asked[id - 1]? else none
  match asked <|> (if url.isEmpty then none else some url) with
  | none => none
  | some u =>
    -- a worker's own script is fetched in mode "same-origin" (HTML §10.2.4 "fetch a classic
    -- worker script"): a redirect to another origin is a network error
    let crossed := w.mains.contains u && !url.isEmpty && originOfUrl url != originOfUrl u
    some (u, if !crossed && scriptAccepted status contentType options then some source else none)

/-- Kind: security theorem (HTML §10.2.4, a worker's script is fetched in mode
"same-origin"). Says: a worker's own script whose answer came from another origin than the URL
it was asked for (a redirect to another origin) gives no script: the worker is not started
with another origin's code. -/
theorem result_crossed (w : Workers) (id status : Nat) (url ct src opts u : String) (s : Option String)
    (h : w.result id status url ct src opts = some (u, s)) (hm : w.mains.contains u = true)
    (hu : url.isEmpty = false) (ho : (originOfUrl url != originOfUrl u) = true) : s = none := by
  unfold Workers.result at h
  dsimp only at h
  cases hq : ((if id ≥ 1 then w.asked[id - 1]? else none) <|> (if url.isEmpty then none else some url)) with
  | none => rw [hq] at h; simp at h
  | some v =>
    rw [hq] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hm' : v ∈ w.mains := by simpa using hm
    simp [hm', hu, ho]

/-- The script source fetched for `url`: `some none` when the fetch failed. -/
def Workers.script? (w : Workers) (url : String) : Option (Option String) :=
  (w.scripts.find? (·.1 == url)).map (·.2)

/-- The string literals of `importScripts("...", '...')` calls in a script, resolved
against `base`: fetched with the script, so that a start runs once rather than once for
each script it imports. A hint only: what runs is decided by `importScripts` itself. -/
def importHints (src base : String) : Array String := Id.run do
  let key := "importScripts("
  let mut out : Array String := #[]
  let parts := src.splitOn key
  let space := fun (cs : List Char) => cs.dropWhile Char.isWhitespace
  for p in parts.drop 1 do
    if out.size ≥ 32 then break
    let mut rest := space p.toList
    for _ in [0:16] do
      match rest with
      | q :: body =>
        if q != '"' && q != '\'' then break
        let lit := body.takeWhile (· != q)
        if lit.contains '\\' then break
        if let some u := WHATWG.URL.parseUrl (String.ofList lit) (some base) then out := out.push u.href
        rest := space (body.drop (lit.length + 1))
        match rest with
        | ',' :: more => rest := space more
        | _ => break
      | [] => break
  return out

/-- The referrer policy of a worker's requests (HTML §10.2.4 "run a worker": the policy
container of the worker's script response): the `Referrer-Policy` field of its script's
response when the embedder fetched it (`some`; "" is no field: the default policy), else
its owner's (a `blob:` or `data:` script, which has no response of its own). -/
def workerPolicy (owner : Net.Xhr.State) (policy : Option String) : Net.ReferrerPolicy.Policy :=
  match policy with
  | some v => Net.Xhr.policyOfHeader v
  | none => owner.policy

/-- The network state of a new worker (`Net.Xhr`): on when its owner's is, with the
owner's policy for the worker's URL (`PageFetch.Page.forWorker`: the owner's origin, or
opaque for a `data:` worker; always the owner's local, secure and `hostCors` rules); sync
requests by undo and redo of the worker's run (`syncCache`: the answers so far). A worker
whose script is a `data:` or `blob:` URL has its owner's Content Security Policy (CSP §4.1.4:
a local scheme inherits); a worker from the network has none here yet (its own response's
fields are not read: an open item of the design record). -/
def workerNet (owner : Net.Xhr.State) (url : String) (syncCache : Array Net.PageFetch.Answer)
    (policy : Option String := none) : Net.Xhr.State :=
  { enabled := owner.enabled, page := owner.page.forWorker url, syncOk := true, syncAnswers := syncCache, window := false,
    blobs := owner.blobs, client := url, policy := workerPolicy owner policy,
    csp := if url.startsWith "data:" || url.startsWith "blob:" then owner.csp else [] }

/-- The host of a new worker: an empty arena, the page's clock and clock rate, its own
fresh entropy (`Agents.entropy`), so a worker's random values and keys owe nothing to the
page's seed, its network state (`workerNet`), and what the page's canvases draw with (fonts,
the SVG path parser; `OffscreenCanvas` is exposed in workers), as the page had it then. -/
def workerHost (page : Session) (entropy : ByteArray) (url : String := "") (syncCache : Array Net.PageFetch.Answer := #[])
    (policy : Option String := none) : Page.Host :=
  let ph := page.host
  { dom := { dom := Page.emptyDocument, commandLimit := 0, logLimit := maxLogs },
    loop := { clock := ph.loop.clock },
    time := { instructionsPerMs := ph.time.instructionsPerMs },
    reads := { canvasEnv := ph.reads.canvasEnv },
    web := { entropy, docEncoding := "UTF-8", net := workerNet ph.web.net url syncCache policy } }

/-- Kind: definitional lemma (worker canvases). Says: a worker's canvases draw with the fonts
and path parser the page's had when the worker started; nothing else of the page's reads (no
layout, no viewport) reaches the worker. -/
theorem workerHost_reads (page : Session) (e : ByteArray) (url : String) (c : Array Net.PageFetch.Answer) :
    (workerHost page e url c).reads = { canvasEnv := page.host.reads.canvasEnv } := rfl

/-- Kind: definitional lemma (workers' requests). Says: a worker's requests are decided
under its owner's policy for the worker's URL (`PageFetch.Page.forWorker`): with
`forWorker_origin`, the owner's origin or opaque, never another; with `forWorker_policy`,
the owner's local, mixed-content and `hostCors` rules. Does not say: that the realm's
scripts cannot change it (no op of `Net.Xhr.op` writes `page`, by reading of the code; not
proved here). -/
theorem workerHost_net_page (page : Session) (e : ByteArray) (url : String) (c : Array Net.PageFetch.Answer) :
    (workerHost page e url c).web.net.page = page.host.web.net.page.forWorker url := rfl

/-- Kind: definitional lemma. Says: a worker has network access exactly when its owner page
has (the embedder's `network:true`). Does not say: anything of the page's frames. -/
theorem workerHost_net_enabled (page : Session) (e : ByteArray) (url : String) (c : Array Net.PageFetch.Answer) :
    (workerHost page e url c).web.net.enabled = page.host.web.net.enabled := rfl

/-- Set the answers of a worker's sync requests before a run (`Net.Xhr.syncFetch` takes
them in order). -/
def withSync (s : Session) (cache : Array Net.PageFetch.Answer) : Session :=
  let h := s.host
  if !h.web.net.enabled then s else
  s.setHost { h with web := { h.web with net := { h.web.net with syncOk := true, syncAnswers := cache, syncUsed := 0, syncWanted := none } } }

/-- The sync request a run of the worker needs (it is then undone). -/
def syncWanted (s : Session) : Option Net.PageFetch.Wire := s.host.web.net.syncWanted

/-- Start a worker whose script has come: a copy of the base realm, made a worker's global
scope, its script run, its microtask checkpoint, then the messages that waited. When the
start needs a script not yet fetched, nothing is kept and the worker still waits. -/
def start (base page : Session) (w : Worker) (src : String) (scripts : Array (String × Option String))
    (entropy : ByteArray) (policy : Option String := none) : Worker × Option String × Option Net.PageFetch.Wire :=
  let limits := { page.limits with entropy := ByteArray.empty, commands := 0, logs := maxLogs }
  let s : Session := { base with limits, steps := 0, jobs := 0, tasks := 0, errors := #[], lastFrame := none }
  -- Math.random: a seed from this worker's own entropy, not the realm snapshot's constant
  -- (`WebApi.mathRandomSeed`; cryptosec finding F2). No entropy: the snapshot's seed, and
  -- no crypto generator either (`WebApi.randomBytes` fails closed).
  let s := match Hosts.WebApi.mathRandomSeed entropy with
    | some x => { s with heap := { s.heap with rng := x } }
    | none => s
  let s := (s.setHost (workerHost page entropy w.url w.syncCache policy)).setBudget workerBudget
  let s := s.setWk { scripts }
  let s := (s.api? "worker" #[.str (JS.Str.ofHost w.url), .str (JS.Str.ofHost w.name)]).1
  let s := s.eval src
  let s := wEngine.checkpoint s
  match s.wk.missing, syncWanted s with
  | some u, _ => ({ w with steps := w.steps + s.steps }, some u, none)
  | none, some wire => ({ w with steps := w.steps + s.steps }, none, some wire)
  | none, none =>
    let s := w.waiting.foldl (fun s d => deliver s { worker := 0, kind := "message", data := d }) s
    ({ w with s, phase := .running, waiting := #[], steps := w.steps + s.steps, syncCache := #[] }, none, none)

/-! ## Module workers (HTML §10.2.4 "run a worker", type "module") -/

/-- The mark the prelude puts in a module worker's name (its `MODULE`). -/
def moduleMark : String := "\u0001module\u0001"

/-- A worker made with `{type: "module"}`. -/
def isModuleWorker (name : String) : Bool := (name.splitOn moduleMark).length > 1

/-- The module graph of a module worker (HTML "fetch a module worker script graph"), from its
script and the scripts fetched so far: `.inr (graph, root)` when every module is there,
`.inl url` for the next module to fetch, or why it fails (a fetch that failed, a parse error,
a specifier that does not resolve: `LeanJSModules.resolveSpecifier`, no import maps). A
module is fetched once; a cycle ends at a module already in the graph. -/
def moduleGraph (url src : String) (fetched : Array (String × Option String)) :
    Except String (String ⊕ (JS.ModGraph × Nat)) := Id.run do
  let some root := (JS.parseModule src).toOption | return .error s!"SyntaxError in the module script {url}"
  let mut g : JS.ModGraph := #[JS.ModNode.ofSyntax url root]
  let mut index : Array (String × Nat) := #[(url, 0)]
  let mut pending : List Nat := [0]
  for _ in [0:4096] do
    match pending with
    | [] => break
    | i :: rest =>
      pending := rest
      let node := g[i]!
      for spec in node.syn.requests do
        match LeanJSModules.resolveSpecifier spec node.url with
        | none => return .error s!"Failed to resolve module specifier \"{spec}\""
        | some u =>
          match index.find? (·.1 == u) with
          | some (_, j) => g := g.modify i fun m => { m with deps := m.deps.push (spec, j) }
          | none =>
            match fetched.find? (·.1 == u) with
            | none => return .ok (.inl u)
            | some (_, none) => return .error s!"Failed to fetch the module {u}"
            | some (_, some text) =>
              let some syn := (JS.parseModule text).toOption | return .error s!"SyntaxError in the module {u}"
              let j := g.size
              g := g.push (JS.ModNode.ofSyntax u syn)
              index := index.push (u, j)
              g := g.modify i fun m => { m with deps := m.deps.push (spec, j) }
              pending := pending ++ [j]
  return .ok (.inr (g, 0))

/-- Start a module worker: as `start`, with its module graph linked and evaluated in place of
a classic script. -/
def startModule (base page : Session) (w : Worker) (g : JS.ModGraph) (root : Nat)
    (entropy : ByteArray) (policy : Option String := none) : Worker × Option Net.PageFetch.Wire :=
  let limits := { page.limits with entropy := ByteArray.empty, commands := 0, logs := maxLogs }
  let s : Session := { base with limits, steps := 0, jobs := 0, tasks := 0, errors := #[], lastFrame := none }
  let s := match Hosts.WebApi.mathRandomSeed entropy with
    | some x => { s with heap := { s.heap with rng := x } }
    | none => s
  let s := (s.setHost (workerHost page entropy w.url w.syncCache policy)).setBudget workerBudget
  let s := (s.api? "worker" #[.str (JS.Str.ofHost w.url), .str (JS.Str.ofHost w.name)]).1
  let (s, _) := s.runModule g #[] 0 (.run root false)
  let s := wEngine.checkpoint s
  match syncWanted s with
  | some wire => ({ w with steps := w.steps + s.steps }, some wire)
  | none =>
    let s := w.waiting.foldl (fun s d => deliver s { worker := 0, kind := "message", data := d }) s
    ({ w with s, phase := .running, waiting := #[], steps := w.steps + s.steps, syncCache := #[] }, none)

def closesIn (ops : Array WorkerOp) : Bool := ops.any fun | .close => true | _ => false

/-- Run a worker's tasks that are due at `clock`, at most `workerTasks` and about `budget`
steps. A task that needs a script not yet fetched is undone (the state before it is kept)
and the worker waits for it; a task that makes a sync request the host has not answered is
undone the same way and waits for the answer (`syncing`; its wire is the second result);
`close()` ends the runs after its task. The steps used. -/
def runTo (w : Worker) (clock budget : Nat) : Worker × Nat × Option Net.PageFetch.Wire := Id.run do
  let e := wEngine
  let mut s := w.s
  let mut used := 0
  let mut halts := w.halts
  let mut cache := w.syncCache
  for _ in [0:workerTasks] do
    if used ≥ budget then break
    let (l, r) := (e.loop s).step
    match r with
    | some run =>
      let s0 := s
      let s1 := e.runTask (e.setLoop (withSync s cache) l) run
      used := used + (s1.steps - s0.steps)
      if let some u := s1.wk.missing then
        return ({ w with s := s0, phase := .blocked u, steps := w.steps + used, halts, syncCache := cache }, used, none)
      if let some wire := syncWanted s1 then
        return ({ w with s := s0, phase := .syncing, steps := w.steps + used, halts, syncCache := cache }, used, some wire)
      cache := #[]
      if s1.errors.size > s0.errors.size && ((s1.errors.back?.getD "").startsWith "halted") then halts := halts + 1
      s := s1
      if closesIn s.wk.ops then break
    | none =>
      let (l, fired) := (e.loop s).advanceTo clock
      s := e.setLoop s l
      if fired.isEmpty then break
  return ({ w with s, steps := w.steps + used, halts, syncCache := cache }, used, none)

/-- The worker's next wake on the page's clock: now when a task waits, else its first
timer. -/
def Worker.wakeAt (w : Worker) (clock : Nat) : Option Nat :=
  if w.phase != .running then none else
  let l := wEngine.loop w.s
  if (L4Factoidal.EventLoop.State.takeTask l.active l.tasks).isSome then some clock
  else l.timers.head?.map (·.due)

/-- The JSON of a worker's error for its Worker object. -/
def errorHeader (message file : String) (line col : Nat) : String :=
  (JSON.Json.object [("message", .string message), ("file", .string file),
    ("line", .number (toString line)), ("col", .number (toString col))]).toString

/-- Stop a worker: no task of it runs again; its heap is let go. -/
def Worker.stop (w : Worker) : Worker := { w with phase := .closed, s := default, waiting := #[] }

/-- The page's asks: new workers (each waits for its script), messages, terminate. -/
def pageAsks (a : Agents) : Agents := Id.run do
  let wk := a.page.wk
  if wk.ops.isEmpty then return a
  let mut page := a.page.setWk { wk with ops := #[] }
  let mut w := a.w
  for op in wk.ops do
    match op with
    | .create id url name =>
      if w.list.size ≥ maxWorkers || a.base.isNone then
        page := deliver page { worker := id, kind := "loaderror" }
      else
        w := { w with list := w.list.push { id, url, name, s := default }, mains := w.mains.push url }
        w := w.request url
    | .post id data =>
      match w.list.findIdx? (·.id == id) with
      | some i =>
        let x := w.list[i]!
        let x := match x.phase with
          | .starting => { x with waiting := x.waiting.push data }
          | .running | .blocked _ | .syncing => { x with s := deliver x.s { worker := 0, kind := "message", data } }
          | .closed => x
        w := { w with list := w.list.set! i x }
      | none => pure ()
    | .terminate id =>
      w := { w with list := w.list.map fun x => if x.id == id then x.stop else x }
    | _ => pure ()
  return { a with page, w }

/-- A worker's asks after its runs: its messages and errors become the page's events, in
order; its console lines join the page's; `close()` stops it. -/
def workerAsks (page : Session) (x : Worker) : Session × Worker := Id.run do
  let wk := x.s.wk
  let logs := x.s.host.dom.logs
  if wk.ops.isEmpty && logs.isEmpty then return (page, x)
  let mut page := page
  let mut closing := false
  for op in wk.ops do
    match op with
    | .post _ data => page := deliver page { worker := x.id, kind := "message", data }
    | .error m f l c => page := deliver page { worker := x.id, kind := "error", header := errorHeader m f l c }
    | .close => closing := true
    | _ => pure ()
  let mut s := x.s.setWk { wk with ops := #[] }
  if !logs.isEmpty then
    let ph := page.host
    let room := ph.dom.logLimit - ph.dom.logs.size
    let lines := (logs.extract 0 room).map (s!"[worker {x.id}] " ++ ·)
    page := page.setHost { ph with dom := { ph.dom with logs := ph.dom.logs ++ lines } }
    let h := s.host
    s := s.setHost { h with dom := { h.dom with logs := #[] } }
  let x := { x with s }
  return (page, if closing then x.stop else x)

/-- Arm (or move, or clear) the page timer for the workers' next wake. -/
def arm (a : Agents) : Agents := Id.run do
  let e := LeanJS.engine
  let l := e.loop a.page
  let clock := l.clock
  let next := a.w.list.foldl (fun acc x => match x.wakeAt clock, acc with
    | some t, some u => some (min t u)
    | some t, none => some t
    | none, acc => acc) none
  -- the armed timer, while it is still armed
  let armed := a.w.wake.bind fun id => (l.timers.find? (·.id == id)).map (id, ·.due)
  match next, armed with
  | none, none => return { a with w := { a.w with wake := none } }
  | none, some (id, _) => return { a with page := e.setLoop a.page (l.clearTimer id), w := { a.w with wake := none } }
  | some t, some (_, due) => if due == max t clock then return a else
    let l := match a.w.wake with | some id => l.clearTimer id | none => l
    let id := l.nextTimer
    let l := { l with active := id :: l.active, nextTimer := id + 1 }
    return { a with page := e.setLoop a.page (l.arm id wakeHandle (t - clock) false 0), w := { a.w with wake := some id } }
  | some t, none =>
    let id := l.nextTimer
    let l := { l with active := id :: l.active, nextTimer := id + 1 }
    return { a with page := e.setLoop a.page (l.arm id wakeHandle (t - clock) false 0), w := { a.w with wake := some id } }

/-! ## Workers' requests (`Net.Xhr` in a worker)

A worker's `XMLHttpRequest` and `fetch` are decided in the worker's own `Net.Xhr.State`,
under its owner's policy (`workerNet`). The host knows only the page: a worker's requests
join the page's `netRequests` with an id from the page's numbering (`routes` maps it back),
and the host's answers to them go to the worker (`giveNet`). Nothing of a request changes
on the way but its id (`routeWire_same`). -/

def netOf (s : Session) : Net.Xhr.State := s.host.web.net

def setNet (s : Session) (n : Net.Xhr.State) : Session :=
  let h := s.host
  s.setHost { h with web := { h.web with net := n } }

/-- A worker's request as the host is told it: the worker's wire with the page-wide id. -/
def routeWire (wire : Net.PageFetch.Wire) (g : Nat) : Net.PageFetch.Wire := { wire with id := g }

/-- Kind: lemma on `routeWire`. Says: forwarding a worker's request to the host changes its
id and nothing else: method, URL, header fields, body, resolve flag and pinned address are
the worker's (so `PageFetch.plan_wire_forbidden`, `onAnswer_reach` and the other theorems on
the worker's transfers hold of what the host is told). Does not say: anything of the host. -/
theorem routeWire_same (wire : Net.PageFetch.Wire) (g : Nat) :
    (routeWire wire g).method = wire.method ∧ (routeWire wire g).url = wire.url ∧
      (routeWire wire g).headers = wire.headers ∧ (routeWire wire g).body = wire.body ∧
      (routeWire wire g).resolve = wire.resolve ∧ (routeWire wire g).address = wire.address ∧
      (routeWire wire g).port = wire.port ∧ (routeWire wire g).id = g :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Hand a worker's new requests and cancels to the page (for the host), and its sync
request (`sync`, from a run that was undone), which the worker then waits for. -/
def forwardNet (page : Session) (w : Workers) (x : Worker) (sync : Option Net.PageFetch.Wire) :
    Session × Workers × Worker := Id.run do
  let xn := netOf x.s
  if xn.outbox.isEmpty && xn.cancels.isEmpty && sync.isNone then return (page, w, x)
  let mut pn := netOf page
  let mut routes := w.routes
  for wire in xn.outbox do
    match routes.find? (fun r => r.2.1 == x.id && r.2.2 == wire.id) with
    | some (g, _, _) => pn := { pn with outbox := pn.outbox.push (routeWire wire g) }
    | none =>
      let g := pn.nextTransfer
      pn := { pn with nextTransfer := g + 1, outbox := pn.outbox.push (routeWire wire g) }
      routes := routes.push (g, x.id, wire.id)
  for c in xn.cancels do
    match routes.find? (fun r => r.2.1 == x.id && r.2.2 == c) with
    | some (g, _, _) =>
      pn := { pn with cancels := pn.cancels.push g }
      routes := routes.filter (·.1 != g)
    | none => pure ()
  let mut x := if xn.outbox.isEmpty && xn.cancels.isEmpty then x else { x with s := setNet x.s { xn with outbox := #[], cancels := #[] } }
  if let some wire := sync then
    let g := pn.nextTransfer
    pn := { pn with nextTransfer := g + 1, outbox := pn.outbox.push (routeWire wire g) }
    x := { x with syncWait := some g }
  return (setNet page pn, { w with routes }, x)

/-- The host's answers to workers' requests go to them: an async one to the worker's
`Net.Xhr.give` (its callback a task on the worker's networking source), a sync one to the
worker's answers so far (the undone task then runs again). The answers that are the page's
are given back. -/
def giveNet (a : Agents) (answers : Array (Nat × Net.PageFetch.Answer)) : Agents × Array (Nat × Net.PageFetch.Answer) := Id.run do
  if a.w.routes.isEmpty && !a.w.list.any (·.syncWait.isSome) then return (a, answers)
  let mut w := a.w
  let mut rest : Array (Nat × Net.PageFetch.Answer) := #[]
  for (g, ans) in answers do
    match w.list.findIdx? (·.syncWait == some g) with
    | some i =>
      let x := w.list[i]!
      let phase := if x.phase == .syncing then .running else x.phase
      w := { w with list := w.list.set! i { x with syncCache := x.syncCache.push ans, syncWait := none, phase } }
    | none =>
    match w.routes.find? (·.1 == g) with
    | none => rest := rest.push (g, ans)
    | some (_, wid, l) =>
      match w.list.findIdx? (·.id == wid) with
      | none => w := { w with routes := w.routes.filter (·.1 != g) }
      | some i =>
        let x := w.list[i]!
        let (net, cb) := Net.Xhr.give (netOf x.s) l ans
        let s := setNet x.s net
        let s := match cb with
          | some c => wEngine.setLoop s ((wEngine.loop s).queueTask .networking c)
          | none => s
        -- a request in flight, or a WebSocket connection that is not closed, keeps its route
        let routes := if net.live.any (·.1 == l) || net.sockets.any (fun k => k.id == l && k.readyState != 3) then w.routes
          else w.routes.filter (·.1 != g)
        w := { w with list := w.list.set! i { x with s }, routes }
  return ({ a with w }, rest)

/-- Requests of workers that are gone: the host may stop them, and their answers are dropped. -/
def dropRoutes (page : Session) (w : Workers) : Session × Workers :=
  if w.routes.isEmpty then (page, w) else
  let (keep, gone) := w.routes.partition fun r => w.list.any (·.id == r.2.1)
  if gone.isEmpty then (page, w) else
  let pn := netOf page
  (setNet page { pn with cancels := pn.cancels ++ gone.map (·.1) }, { w with routes := keep })

/-- Start the workers whose scripts have come, and run each worker's due tasks at the
page's clock (`pumpSteps` for all of them), then hand their asks and requests to the page. -/
def runWorkers (a : Agents) : Agents := Id.run do
  let some base := a.base | return a
  let clock := (LeanJS.engine.loop a.page).clock
  let mut page := a.page
  let mut w := a.w
  let mut budget := pumpSteps
  for i in [0:w.list.size] do
    let mut x := w.list[i]!
    let mut sync : Option Net.PageFetch.Wire := none
    match x.phase with
    | .starting =>
      if x.syncWait.isSome then pure () else
      match w.script? x.url with
      | some (some src) =>
        let hints := (importHints src x.url).filter fun u => (w.script? u).isNone
        if isModuleWorker x.name then
          match moduleGraph x.url src w.scripts with
          | .ok (.inl u) => w := w.request u
          | .error m =>
            page := deliver page { worker := x.id, kind := "error", header := errorHeader m x.url 0 0 }
            x := x.stop
          | .ok (.inr (g, root)) =>
            let (x', wire) := startModule base page x g root (a.entropy x.id)
              ((w.policies.find? fun (e : String × String) => e.1 == x.url).map (·.2))
            x := x'
            sync := wire
        else if !hints.isEmpty then
          w := hints.foldl Workers.request w
        else
          let (x', need, wire) := start base page x src w.scripts (a.entropy x.id)
            ((w.policies.find? fun (e : String × String) => e.1 == x.url).map (·.2))
          x := x'
          sync := wire
          if let some u := need then w := w.request u
      | some none =>
        page := deliver page { worker := x.id, kind := "loaderror" }
        x := x.stop
      | none => pure ()
    | .blocked u =>
      match w.script? u with
      | some _ => x := { x with phase := .running }
      | none => pure ()
    | _ => pure ()
    if x.phase == .running && budget > 0 then
      -- the scripts fetched so far, for importScripts
      if x.s.wk.scripts.size != w.scripts.size then x := { x with s := x.s.setWk { x.s.wk with scripts := w.scripts, missing := none } }
      let (x', used, wire) := runTo x clock budget
      x := x'
      sync := wire
      budget := budget - min budget used
      if let .blocked u := x.phase then w := w.request u
    let (page', x') := workerAsks page x
    page := page'
    x := x'
    let (page', w', x') := forwardNet page w x sync
    page := page'
    w := w'
    x := x'
    if x.phase != .closed then
      if x.halts ≥ maxHalts || x.s.heap.objs.size > maxObjects then
        let header := errorHeader "the worker was stopped: over its step or memory budget" x.url 0 0
        page := deliver page { worker := x.id, kind := "error", header }
        x := x.stop
    w := { w with list := w.list.set! i x }
  -- closed workers leave the list (their events already queued at the page stay), and
  -- their requests are stopped
  let (page', w') := dropRoutes page { w with list := w.list.filter (·.phase != .closed), steps := w.steps + (pumpSteps - budget) }
  return { a with page := page', w := w' }

/-- After each microtask checkpoint of the page. A page with no worker pays one check. -/
def pump (a : Agents) : Agents :=
  if a.page.wkIdle && a.w.list.isEmpty then a else arm (runWorkers (pageAsks a))

/-- The `Referrer-Policy` fields of scripts the embedder fetched, by URL (before `give`,
which starts the workers whose scripts came). -/
def notePolicies (a : Agents) (ps : Array (String × String)) : Agents :=
  { a with w := { a.w with policies := a.w.policies ++ ps } }

/-- The embedder's scripts (action `scripts`): `none` for a fetch that failed. -/
def give (a : Agents) (got : Array (String × Option String)) : Agents :=
  let w := got.foldl (fun w (u, src) =>
    if w.scripts.any (·.1 == u) then w else { w with scripts := w.scripts.push (u, src) }) a.w
  pump { a with w := { w with loads := w.loads.filter fun u => !got.any (·.1 == u) } }

/-- The page with its workers as an engine of `Hosts.PageEvents`: the page's steps, and
the pump after each checkpoint. -/
def engine : PageEvents.Engine Agents :=
  let p := LeanJS.engine
  { host := fun a => p.host a.page,
    setHost := fun a h => { a with page := p.setHost a.page h },
    dispatchOnly := fun a t ty => let (s, b) := p.dispatchOnly a.page t ty; ({ a with page := s }, b),
    callbackOnly := fun a cb t arg => if cb == wakeHandle then a else { a with page := p.callbackOnly a.page cb t arg },
    release := fun a cb => if cb == eventHandle || cb == wakeHandle then a else { a with page := p.release a.page cb },
    runJobs := fun a => pump { a with page := p.runJobs a.page },
    lastFrame := fun a => p.lastFrame a.page,
    setLastFrame := fun a f => { a with page := p.setLastFrame a.page f } }

/-- Whether a worker waits for the embedder: `settle` stops then. -/
def Agents.waits (a : Agents) : Bool :=
  !a.w.loads.isEmpty || a.w.list.any (·.syncWait.isSome) ||
    -- a request of a worker in flight (an open WebSocket keeps its route but does not wait)
    a.w.routes.any fun (_, wid, l) =>
      match a.w.list.find? (·.id == wid) with
      | some x => (netOf x.s).live.any (·.1 == l)
      | none => false

/-- Workers that run (for a turn's answer). -/
def Agents.running (a : Agents) : Nat := a.w.list.size

end L4Factoidal.WasmVM.Hosts.LeanJSWorkers
