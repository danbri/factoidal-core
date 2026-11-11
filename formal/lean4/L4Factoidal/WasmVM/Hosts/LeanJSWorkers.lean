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
  /-- The page timer armed for the workers' next timer (`wakeHandle`). -/
  wake : Option Nat := none
  steps : Nat := 0
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

/-- An embedder's answer to a fetch (`{id, status, url, contentType, source}`): the URL it
was asked for and the script, or `none` for a network error (status 0, a status that is
not ok, or a type that is not JavaScript: HTML's fetches of worker scripts and imported
scripts are strict about it). -/
def Workers.result (w : Workers) (id status : Nat) (url contentType source : String) : Option (String × Option String) :=
  let asked := if id ≥ 1 then w.asked[id - 1]? else none
  match asked <|> (if url.isEmpty then none else some url) with
  | none => none
  | some u =>
    let ok := 200 ≤ status && status < 300 && (contentType.isEmpty || jsMime contentType)
    some (u, if ok then some source else none)

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

/-- The host of a new worker: an empty arena, the page's clock and clock rate, and its own
fresh entropy (`Agents.entropy`), so a worker's random values and keys owe nothing to the
page's seed. -/
def workerHost (page : Session) (entropy : ByteArray) : Page.Host :=
  let ph := page.host
  { dom := { dom := Page.emptyDocument, commandLimit := 0, logLimit := maxLogs },
    loop := { clock := ph.loop.clock },
    time := { instructionsPerMs := ph.time.instructionsPerMs },
    web := { entropy, docEncoding := "UTF-8" } }

/-- Start a worker whose script has come: a copy of the base realm, made a worker's global
scope, its script run, its microtask checkpoint, then the messages that waited. When the
start needs a script not yet fetched, nothing is kept and the worker still waits. -/
def start (base page : Session) (w : Worker) (src : String) (scripts : Array (String × Option String))
    (entropy : ByteArray) : Worker × Option String :=
  let limits := { page.limits with entropy := ByteArray.empty, commands := 0, logs := maxLogs }
  let s : Session := { base with limits, steps := 0, jobs := 0, tasks := 0, errors := #[], lastFrame := none }
  -- Math.random: a seed from this worker's own entropy, not the realm snapshot's constant
  -- (`WebApi.mathRandomSeed`; cryptosec finding F2). No entropy: the snapshot's seed, and
  -- no crypto generator either (`WebApi.randomBytes` fails closed).
  let s := match Hosts.WebApi.mathRandomSeed entropy with
    | some x => { s with heap := { s.heap with rng := x } }
    | none => s
  let s := (s.setHost (workerHost page entropy)).setBudget workerBudget
  let s := s.setWk { scripts }
  let s := (s.api? "worker" #[.str (JS.Str.ofHost w.url), .str (JS.Str.ofHost w.name)]).1
  let s := s.eval src
  let s := wEngine.checkpoint s
  match s.wk.missing with
  | some u => ({ w with steps := w.steps + s.steps }, some u)
  | none =>
    let s := w.waiting.foldl (fun s d => deliver s { worker := 0, kind := "message", data := d }) s
    ({ w with s, phase := .running, waiting := #[], steps := w.steps + s.steps }, none)

def closesIn (ops : Array WorkerOp) : Bool := ops.any fun | .close => true | _ => false

/-- Run a worker's tasks that are due at `clock`, at most `workerTasks` and about `budget`
steps. A task that needs a script not yet fetched is undone (the state before it is kept)
and the worker waits for it; `close()` ends the runs after its task. The steps used. -/
def runTo (w : Worker) (clock budget : Nat) : Worker × Nat := Id.run do
  let e := wEngine
  let mut s := w.s
  let mut used := 0
  let mut halts := w.halts
  for _ in [0:workerTasks] do
    if used ≥ budget then break
    let (l, r) := (e.loop s).step
    match r with
    | some run =>
      let s0 := s
      let s1 := e.runTask (e.setLoop s l) run
      used := used + (s1.steps - s0.steps)
      if let some u := s1.wk.missing then
        return ({ w with s := s0, phase := .blocked u, steps := w.steps + used, halts }, used)
      if s1.errors.size > s0.errors.size && ((s1.errors.back?.getD "").startsWith "halted") then halts := halts + 1
      s := s1
      if closesIn s.wk.ops then break
    | none =>
      let (l, fired) := (e.loop s).advanceTo clock
      s := e.setLoop s l
      if fired.isEmpty then break
  return ({ w with s, steps := w.steps + used, halts }, used)

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
          | .running | .blocked _ => { x with s := deliver x.s { worker := 0, kind := "message", data } }
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

/-- Start the workers whose scripts have come, and run each worker's due tasks at the
page's clock (`pumpSteps` for all of them), then hand their asks to the page. -/
def runWorkers (a : Agents) : Agents := Id.run do
  let some base := a.base | return a
  let clock := (LeanJS.engine.loop a.page).clock
  let mut page := a.page
  let mut w := a.w
  let mut budget := pumpSteps
  for i in [0:w.list.size] do
    let mut x := w.list[i]!
    match x.phase with
    | .starting =>
      match w.script? x.url with
      | some (some src) =>
        let hints := (importHints src x.url).filter fun u => (w.script? u).isNone
        if !hints.isEmpty then
          w := hints.foldl Workers.request w
        else
          let (x', need) := start base page x src w.scripts (a.entropy x.id)
          x := x'
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
      let (x', used) := runTo x clock budget
      x := x'
      budget := budget - min budget used
      if let .blocked u := x.phase then w := w.request u
    let (page', x') := workerAsks page x
    page := page'
    x := x'
    if x.phase != .closed then
      if x.halts ≥ maxHalts || x.s.heap.objs.size > maxObjects then
        let header := errorHeader "the worker was stopped: over its step or memory budget" x.url 0 0
        page := deliver page { worker := x.id, kind := "error", header }
        x := x.stop
    w := { w with list := w.list.set! i x }
  -- closed workers leave the list (their events already queued at the page stay)
  return { a with page, w := { w with list := w.list.filter (·.phase != .closed), steps := w.steps + (pumpSteps - budget) } }

/-- After each microtask checkpoint of the page. A page with no worker pays one check. -/
def pump (a : Agents) : Agents :=
  if a.page.wkIdle && a.w.list.isEmpty then a else arm (runWorkers (pageAsks a))

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
def Agents.waits (a : Agents) : Bool := !a.w.loads.isEmpty

/-- Workers that run (for a turn's answer). -/
def Agents.running (a : Agents) : Nat := a.w.list.size

end L4Factoidal.WasmVM.Hosts.LeanJSWorkers
