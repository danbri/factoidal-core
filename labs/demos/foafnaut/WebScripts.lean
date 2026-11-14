import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.WasmVM.Hosts.PageAot
import L4Factoidal.WasmVM.Hosts.LeanJSRealm
import L4Factoidal.WasmVM.Hosts.LeanJSWorkers
import L4Factoidal.DOM.OfXml
import L4Factoidal.WHATWG.Encoding.Sniff
import L4Factoidal.HTML.CspSource
import WebRenderScript
import WebWasm
import WebShell

/-!
# WebScripts: page scripts run by Lean in the Foafnaut engine

The `scriptSession` operation (record: docs/designissues/2026-11-08-page-scripts.md).
QuickJS-NG, compiled to WebAssembly, runs in WasmVM inside this engine, on the page's
DOM arena (`WasmVM.Hosts.Page`). The HTML event loop model (`L4Factoidal.EventLoop`)
decides every next callback: timers, animation frames, the listener order of each
event. The host only moves time and passes clicks; it runs no page script.

The guest module is not in the repository and not in the engine. A host gives its bytes
once: through the font byte call with the family `guest:quickjs`
(`web_document_font_call_bin`, so no new export), or as Base64 (`action:"load"`).

Request `{"op":"scriptSession","action":A,...}`, with the page HTML as the call's HTML
argument for `start`:

- `info`: `{"ops":[...],"module":bool,"bytes":n}`. A host asks this first; an engine
  without this op answers "unknown document operation" (issue 1274).
- `load`: `moduleBase64`, the guest module.
- `start`: `url`, `resources` (`[{nodeId, source}]` for `src` scripts, as for
  stylesheets), optional `commandLimit` and `logLimit`. Runs the classic scripts in document order,
  `DOMContentLoaded`, then the `load` event.
- `click` (`node`), `advance` (`ms`: move the virtual clock), `settle` (`budgetMs`: run
  until no task, timer or frame waits), `turn` (run what is due now), `close`.
- `pointer` (`kind` down, move, up or cancel; `node`; the coordinates of the `nodeAt`
  answer; `button`, `buttons`, `pointerType`): the pointer and mouse events of
  `Page.Session.pointer`, with a click on release; at most one move in a frame. A host
  that finds no `pointer` in `info` sends `click`.
- `actions` (BubblePopJS sessions): input of the user as WebDriver's Perform Actions
  (`L4Factoidal.WebDriver.Actions`; W3C WebDriver §15). `actions` is the request's list of
  input sources (key, pointer, wheel, none) with their actions, or `text` is a text to type
  (Element Send Keys); `release:true` then runs Release Actions. An element origin is
  `{"element-6066-11e4-a52e-4f735466cecf": "path:0/1/2"}`: the child indices from the
  document (`s` enters a shadow root). The actions run tick by tick as trusted keyboard,
  pointer, mouse and wheel events at the element the layout's hit test gives
  (`Hosts.PageEvents.dispatchLow`). A request that WebDriver refuses (`invalid argument`,
  `move target out of bounds`, `no such element`) changes nothing after the point of the
  error and the turn has `inputError` (`error`, `message`). Only this action and `key`
  change the session's trusted input state (`LeanJS.Session.trusted`).
- `key` (BubblePopJS sessions): a key a person pressed in a host, on the same path as
  `actions` (`WebDriver.HostKeys`): `text` (committed text, typed as Element Send Keys
  types it), or `mac` (a macOS virtual key code) or `key` (a DOM key value), with
  `modifiers` (1 Shift, 2 Command, 4 Option, 8 Control). The turn's `keyDefault` says
  whether the host may scroll for the key (its `keydown` was not canceled and it went to
  no text control or editing host).
- `webdriverStart` (`address`, `port`, `platform`, `dangerouslyEnable`): a WebDriver
  endpoint (`WebDriver.Gate.start`: off unless `dangerouslyEnable`, which only the test
  runner's `--dangerously-enable-webdriver-endpoint` sends; loopback only); answers its
  `secret`. `webdriver` (`method`, `path`, `host`, `origin`, `body`): one request of its
  listener, answered `{status, body}` (`WebDriver.Protocol.handle`: the gate first).
- `message` (`data`: JSON text, `origin`): a message of the embedder to the page, as a
  `message` event at the window (a test host answers a page's request this way).
- `resize` (`width`, `height`): the viewport in CSS pixels; `resize` at the window.
- `frame` (`node`, `url`, and `bytesBase64` with `contentType`, or `source`, with
  `resources`; or `failed`): the embedder's answer to a frame navigation of a turn's
  `navigations` (a host that sets `navigations:true` in `start` loads frames' URLs; without
  it a frame with a URL keeps `about:blank`). `srcdoc` frames are Lean's own. The frame's
  document joins the arena (`Command.frameDocument`), its scripts run in the page's realm
  with `document` the frame's, and its `load` event follows (`frameLoads` counts the
  `srcdoc` loads of a turn).
- `csp` and `cspReportOnly` in `start`: the `Content-Security-Policy` and
  `Content-Security-Policy-Report-Only` fields of the page's response (several fields joined
  with commas). With the page's `meta` policies they are the session's policy
  (`Net.Xhr.cspOf`): scripts it forbids do not run, requests it forbids are not made, and
  each violation is a `securitypolicyviolation` event.
- `referrerPolicy` in `start`, in `frame` and in each `fetched` result: the `Referrer-Policy`
  field of the response the document or worker script came with (several fields joined
  with commas; absent or "" for none). The requests of that document or worker carry a
  `Referer` under it (`Net.PageFetch.referrerOf`); a host that does not send it gets the
  default policy.
- `fetched` (`results`: `[{id, status, url, contentType, source}]`): BubblePopJS's
  dedicated workers (`Hosts.LeanJSWorkers`). A turn whose workers wait for scripts lists
  them in `fetches` (`[{id, url, kind}]`, kind `worker` or `script`; and `settle` stops
  there); the embedder fetches them and answers with this action (status 0, a status not
  2xx, or a type that is not JavaScript: a network error), which then runs what is due.

- `net` (`results`: `[{id, status, statusText, url, headers, bodyBase64}]`, optional
  `elapsedMs`): the host's answers to a turn's `netRequests` (a host that sets
  `network:true` in `start` makes page requests; without it `XMLHttpRequest` is not defined).
  A request with `resolve:true` asks only for the addresses of its URL's host name: its
  answer is `{id, addresses}` and nothing goes to the server. A request with `address` and
  `port` goes to that address only; the host does not resolve the name again (DNS
  rebinding, `Net.PageFetch.emit`). `pageAddress` in `start`: the address the host loaded
  the page from, when it knows it (a local one lets the page reach local addresses).
  `elapsedMs` moves the virtual clock before the answers apply (a test host's waiting time).
  On BubblePopJS a dedicated worker's requests are in `netRequests` too, as the page's (ids
  from the page's numbering), and their answers go to the worker (`LeanJSWorkers.giveNet`).
- `syncAnswer` (`answer`, the form of one `results` entry): a sync `XMLHttpRequest` was reached.
  A turn with `netSync` (one request) carries nothing else and changes nothing: the host
  makes the request and answers here, and the action runs again from its start with the
  answer (undo and redo; on a run with several, one more each time). Not on the AOT path.
  Status 0 is a network failure. Every decision is `L4Factoidal.Net.PageFetch`.

`start` also takes `width` and `height` (the viewport in CSS pixels: `innerWidth`,
`innerHeight`), `layout` (the render request whose `layoutFields` lay the page out for
the layout reads of its scripts, `WebDocument.measure`) and `instructionsPerMs` (the
rate of the script clock, `Page.ScriptClock`; 100000 by default).

Every answer but `info` and `close` is a turn: `session`, `clock`, `changed`,
`commandCount`, `commands` (the whole list, compacted: one write per attribute and per
character data, so bounded by the DOM, in the JSON form of `WebRenderScript.commandJson`,
only when `changed` or `full:true`), `changes` (all changes since the start), the new `logs` and
`errors`, `timers`, `nextTimer`, `frames`, `nextWake`, `quiet`, `instructions`, `jobs`,
`tasks`, `layouts` (layouts made for the layout reads of scripts in the turn) and `ns`.

**AOT** (docs/designissues/2026-11-08-wasmvm-aot.md). A host with a WebAssembly engine of
its own gives the guest with the family `guest:quickjs-aot`: Lean decodes, validates and
translates it (`Hosts.PageAot.prepare`), and `aotModule` answers the host module as a raw
section of `web_document_call_bin`, with the import table in the head. Then every action
runs the same session program (`Hosts.Page.Prog`) with the host as its machine: while the
program waits for the guest, the answer is `{"session","aot":ASK,"writes"}`; the host does
the ask and calls `resume` with the reply, and passes each import call of the guest to
`host`. The host decides nothing: it copies bytes and calls the functions Lean names.

**BubblePopJS** (docs/designissues/2026-11-08-lean-js-engine.md, section 11), the
JavaScript engine written in Lean. With `engine:"bubblepop"` in `start`, the page's
scripts run in it (`Hosts.LeanJS`): no guest module, the same prelude, the same imports served by
`Hosts.Page` on the same arena, the same typed commands, and the same event code
(`Hosts.PageEvents`). Every later action of that session runs on it; the answers have the
same fields, and `engine:"bubblepop"`. `info` lists the engines (`engines`).

The cost contract: `changed` is true exactly when the turn recorded a DOM change. A
host renders again only then; the render request carries the command list, which is part
of the layout key (`WebDocument.layoutFields`), so a render with the same list reuses the
kept layout (`WebDocument.lookupLayout_eq`). No DOM change: no layout.
-/

set_option compiler.extract_closed false

namespace WebScripts
open L4Factoidal
open L4Factoidal.WasmVM.Hosts

def num (n : Nat) : JSON.Json := .number (toString n)

private def str (j : JSON.Json) (key : String) (fallback : String := "") : String :=
  match j.field? key with | some (.string s) => s | _ => fallback

private def natField (j : JSON.Json) (key : String) : Option Nat :=
  match j.field? key with | some (.number n) => n.toNat? | _ => none

/-- Marks of what a host has already been given. -/
structure Marks where
  logs : Nat := 0
  errors : Nat := 0

/-- Counts of a session before a turn. Only counts: a turn that kept the whole session
alive would copy the module's memory at its first write. -/
structure Before where
  changes : Nat := 0
  steps : Nat := 0
  jobs : Nat := 0
  tasks : Nat := 0
  layouts : Nat := 0

def Before.of (s : Page.Session) : Before :=
  { changes := s.changes, steps := s.steps, jobs := s.jobs, tasks := s.tasks, layouts := s.layouts }

def Before.ofLean (s : LeanJS.Session) : Before :=
  { changes := s.changes, steps := s.steps, jobs := s.jobs, tasks := s.tasks, layouts := s.layouts }

/-- A turn on the AOT path, waiting for the host. `fresh`: the program, before the
host has made the page's instance; `paused`: stopped at an ask. -/
inductive Stage where
  | fresh (prog : Page.Prog (Except String Page.Session))
  | paused (p : PageAot.Paused (Except String Page.Session))

structure Turn where
  id : Nat
  before : Before
  marks : Marks
  full : Bool
  ns : Nat
  stage : Stage
  /-- The size of the guest's memory, as the host last said. -/
  memSize : Nat := 0
  /-- Writes Lean took at once (they fit the memory); the host makes them before the
  next ask. -/
  pending : Array (Nat × ByteArray) := #[]

/-- What the engine holds between calls: the prepared module and one session. -/
structure Held where
  module : Option Page.Module' := none
  moduleBytes : Nat := 0
  session : Option (Nat × Page.Session × Marks) := none
  nextSession : Nat := 1
  /-- The guest translated for the host's engine (`guest:quickjs-aot`). -/
  aot : Option PageAot.Prepared := none
  /-- The AOT turn that waits for the host. -/
  turn : Option Turn := none
  /-- The size of the guest's memory after the last AOT turn. -/
  memSize : Nat := 0
  /-- The Lean engine's realm with the page objects, made at its first page. -/
  leanBase : Option LeanJS.Session := none
  /-- The session on the Lean engine. -/
  leanSession : Option (Nat × LeanJS.Session × Marks) := none
  /-- The sessions of the current page's sandboxed frames (`HTML.FrameSessions`), by
  `iframe` element, on the interpreter and on the Lean engine; and the arena size up to
  which the page was searched for frames. -/
  frames : Array (Nat × Page.Session) := #[]
  leanFrames : Array (Nat × LeanJS.Session) := #[]
  frameScan : Nat := 0
  /-- The answers of the sync requests of the action being redone (`Net.Xhr`). -/
  syncCache : Array Net.PageFetch.Answer := #[]
  /-- The action that waits for the answer to a sync request (`netSync`), and its page and
  request; `syncAnswer` puts the answer in `syncCache` and does the action again. -/
  pendingSync : Option (String × String × JSON.Json) := none
  /-- The entropy of a `start` that waits for sync answers: the start is done again with the
  same, so `Math.random` and `crypto` give the rerun what they gave the run whose request
  the host has answered (a token a script drew is the token the request carried). -/
  startEntropy : Option ByteArray := none
  /-- The dedicated workers of that session's page (`Hosts.LeanJSWorkers`). -/
  leanWorkers : LeanJSWorkers.Workers := {}
  /-- The `layout` request of the session's `start`: its layout reads (`Page.Reads.measure`)
  are made anew from it before each action, with the fonts and images held then. -/
  layoutRequest : JSON.Json := .object []
  /-- The WebDriver endpoint, when the test runner started one (`webdriverStart`): the
  gate's configuration (secret, port), the protocol's state and what this browser is. -/
  webdriver : Option (WebDriver.Gate.Config × WebDriver.Protocol.Server × WebDriver.Protocol.Browser × WebDriver.Window.State × WebDriver.Page.Doc) := none

instance : Inhabited Held := ⟨{}⟩

/-! `Held` is a field of the engine's state (`WebDocument.Engine`), passed in and given back
by each operation here (issue 390). The caller takes it out of the state before the call,
so the session is not shared and its arrays change in place. -/

/-- Entropy for session `id`'s `crypto.getRandomValues` (`Hosts.WebApi`): 32 bytes of the
machine's generator (`WebWasm.Machine.randomBytes`: `IO.getRandomBytes`, the operating
system's natively and the browser's `crypto.getRandomValues` under Emscripten), then the
session number. Empty when the machine has none (`Id`): the page then has no
`getRandomValues`. -/
def entropy {M : Type → Type} [Monad M] [WebWasm.Machine M] (id : Nat) : M ByteArray := do
  let b ← WebWasm.Machine.randomBytes 32
  return if b.isEmpty then b else b ++ (toString id).toUTF8

/-- Entropy for the workers a turn of session `id` makes (`LeanJSWorkers.Agents.entropy`):
32 fresh bytes `b` of the machine's generator, drawn once for the turn (`turnBytes`), then the
worker's number `id * 65536 + w`, so no two workers share their seed material and none is the
page's. Empty when the machine has none (`Id`). -/
def workerEntropyOf (id : Nat) (b : ByteArray) : Nat → ByteArray :=
  fun w => if b.isEmpty then b else b ++ (toString (id * 65536 + w)).toUTF8

/-- The 32 fresh bytes of a turn (`WebWasm.Machine.randomBytes`), from which its workers' and
its new frames' entropy is made (`workerEntropyOf`, `frameEntropyOf`): one draw a turn. -/
def turnBytes {M : Type → Type} [Monad M] [WebWasm.Machine M] : M ByteArray :=
  WebWasm.Machine.randomBytes 32

def workerEntropy {M : Type → Type} [Monad M] [WebWasm.Machine M] (id : Nat) : M (Nat → ByteArray) :=
  return workerEntropyOf id (← turnBytes)

/-- The `layout` request of a `start` (`Held.layoutRequest`). -/
def layoutOf (request : JSON.Json) : JSON.Json := (request.field? "layout").getD (.object [])

/-- Entropy for the script sessions of the sandboxed frames that a turn of session `id`
starts (`HTML.FrameSessions`): the turn's fresh bytes `b` (`turnBytes`), then `frame:`, `id`
and the `iframe` element `el`; the suffix starts with a letter, so it is never a worker's
(`workerEntropyOf`). A frame's HMAC_DRBG (`Hosts.WebApi`) so never starts from its page's
seed or another frame's: with the page's entropy it would repeat the page's random values,
generated keys and ECDSA nonces (record docs/designissues/2026-11-09-crypto-boundary-security.md,
finding F1). `parent` is the page's entropy: a frame gets none when its page has none, nor
when the machine has none (`Id`). -/
def frameEntropyOf (id : Nat) (parent b : ByteArray) : Nat → ByteArray :=
  fun el => if parent.isEmpty || b.isEmpty then ByteArray.empty
    else b ++ ("frame:" ++ toString id ++ ":" ++ toString el).toUTF8

def actions : List String := ["info", "load", "start", "click", "pointer", "key", "actions", "message", "webdriverStart", "webdriver", "resize", "advance", "settle", "turn", "close",
  "aotModule", "resume", "host", "frame", "fetched", "net", "syncAnswer", "cookies", "gpuRead"]

/-- An answer object with `nextSession` first: the number of the next session. -/
def withNext (n : Nat) (answer : String) : String :=
  if answer.startsWith "{" then "{\"nextSession\":" ++ toString n ++ "," ++ (answer.drop 1).toString else answer

/-- Prepare the guest module: decode, validate, and run the prelude once. -/
def loadModule (held : Held) (bytes : ByteArray) : Held × Except String String :=
  if bytes.size > 8388608 then (held, .error "scriptSession: guest module exceeds 8 MiB") else
  match Page.prepare bytes with
  | .ok m => ({ held with module := some m, moduleBytes := bytes.size, session := none },
      .ok (JSON.Json.object [("module",.bool true),("bytes",num bytes.size)]).toString)
  | .error e => (held, .error s!"scriptSession: guest module: {e}")

/-- Prepare the guest for the host's engine: decode, validate, translate (no run in Lean). -/
def loadAot (held : Held) (bytes : ByteArray) : Held × Except String String :=
  if bytes.size > 8388608 then (held, .error "scriptSession: guest module exceeds 8 MiB") else
  match PageAot.prepare bytes with
  | .ok p => ({ held with aot := some p, module := none, moduleBytes := bytes.size, session := none, turn := none },
      .ok (JSON.Json.object [("module",.bool true),("aot",.bool true),("bytes",num bytes.size),
        ("hostBytes",num p.bytes.size)]).toString)
  | .error e => (held, .error s!"scriptSession: guest module for AOT: {e}")

/-- The guest module as bytes, from `fontLoadBin` with the family `guest:quickjs` (for
the interpreter) or `guest:quickjs-aot` (for the host's engine). -/
def loadModuleBytes (held : Held) (family : String) (bytes : ByteArray) : Held × Except String String :=
  let (held, r) := if family == "guest:quickjs-aot" then loadAot held bytes else loadModule { held with aot := none } bytes
  (held, r.map (withNext held.nextSession))

def commandsJson (s : Page.Session) : JSON.Json :=
  .array (s.commands.toList.map WebRenderScript.commandJson)


/-- What a turn's answer reads of a session, on either engine. -/
structure View where
  host : Page.Host
  steps : Nat
  jobs : Nat
  tasks : Nat
  errors : Array String
  nextFrame : Option Nat
  moveWake : Option Nat
  quiet : Bool

def View.ofPage (s : Page.Session) : View :=
  { host := s.host, steps := s.steps, jobs := s.jobs, tasks := s.tasks, errors := s.errors,
    nextFrame := s.nextFrame, moveWake := s.moveWake, quiet := s.quiet && !s.host.web.net.waiting }

def View.ofLean (s : LeanJS.Session) : View :=
  let e := LeanJS.engine
  { host := s.host, steps := s.steps, jobs := s.jobs, tasks := s.tasks, errors := s.errors,
    nextFrame := e.nextFrame s, moveWake := e.moveWake s, quiet := e.quiet s && !s.host.web.net.waiting }

/-- The answer of a turn. -/
def turnAnswerOf (id : Nat) (before : Before) (s : View) (marks : Marks) (full : Bool) (ns : Nat)
    (extra : List (String × JSON.Json) := []) : String × Marks :=
  let dom := s.host.dom
  let changed := dom.changes != before.changes
  let loop := s.host.loop
  let logs := dom.logs
  let fields : List (String × JSON.Json) := [
    ("session",num id),("clock",num loop.clock),("changed",.bool changed),
    ("commandCount",num dom.commands.size),("changes",num dom.changes)] ++
    (if changed || full then [("commands",.array (dom.commands.toList.map WebRenderScript.commandJson))] else []) ++ [
    ("logs",.array ((logs.extract marks.logs logs.size).toList.map .string)),
    ("errors",.array ((s.errors.extract marks.errors s.errors.size).toList.map .string)),
    ("timers",num loop.timers.length),
    ("nextTimer",match loop.timers with | t :: _ => num t.due | [] => .null),
    ("frames",num loop.frames.length),
    ("nextWake",match [loop.timers.head?.map (·.due), s.nextFrame, s.moveWake].filterMap (fun x => x) with
      | [] => .null
      | t :: ts => num (ts.foldl min t)),
    ("quiet",.bool s.quiet),
    ("instructions",num (s.steps - before.steps)),("jobs",num (s.jobs - before.jobs)),
    ("tasks",num (s.tasks - before.tasks)),("layouts",num (s.host.reads.layouts - before.layouts)),("ns",num ns)] ++ extra
  let text := (JSON.Json.object fields).toString
  -- The page's GPU commands, validated by Lean (L4Factoidal.PageGpu): the host replays them
  -- on its WebGPU device. They need no layout; the canvas rectangles come with a render.
  let gpu := dom.gpuOut
  -- Canvas 2D (PageCanvas): the pixels of each canvas drawn in the turn, as host commands
  -- of the same list (a texture, then its pixels), blitted like a WebGPU canvas.
  let canvas := dom.canvas.hostCmds
  let text := if gpu.isEmpty && canvas.isEmpty then text else
    (text.dropEnd 1).toString ++ ",\"gpuPage\":" ++ toString dom.gpu.page ++ ",\"gpu\":[" ++
      ",".intercalate (gpu.toList.map PageGpu.Wire.HostCmd.json ++ canvas.map (PageCanvas.HostCmd.json dom.gpu.page)) ++ "]}"
  (text, { logs := logs.size, errors := s.errors.size })

def turnAnswer (id : Nat) (before : Before) (s : Page.Session) (marks : Marks) (full : Bool) (ns : Nat)
    (extra : List (String × JSON.Json) := []) : String × Marks :=
  turnAnswerOf id before (View.ofPage s) marks full ns extra

/-- The page requests and cancels a turn carries away (the host keeps them from here). -/
def netDrained (w : WebApi.State) : WebApi.State :=
  { w with net := { w.net with outbox := #[], cancels := #[], syncAnswers := #[], syncUsed := 0 } }

/-- The session after a turn answer: the GPU commands it carried are the host's now. -/
def drained (s : Page.Session) : Page.Session :=
  { s with host := { s.host with dom := { s.host.dom with gpuOut := #[], canvas := s.host.dom.canvas.sent,
                                                           gpu := s.host.dom.gpu.newFrame },
                                  web := netDrained s.host.web } }

def drainedLean (s : LeanJS.Session) : LeanJS.Session :=
  let h := s.host
  let web := if h.web.net.outbox.isEmpty && h.web.net.cancels.isEmpty && h.web.net.syncAnswers.isEmpty then h.web else netDrained h.web
  if h.dom.gpuOut.isEmpty && h.dom.canvas.drawn.isEmpty && h.web.net.outbox.isEmpty && h.web.net.cancels.isEmpty && h.web.net.syncAnswers.isEmpty then s else
  s.setHost { h with dom := { h.dom with gpuOut := #[], canvas := h.dom.canvas.sent, gpu := h.dom.gpu.newFrame }, web }

/-- The host's answers to the page's GPU readbacks (`PageGpu.deliver`; record
2026-11-14-gpu-compute-and-webnn.md): `results` of `{ticket, dataBase64}` or
`{ticket, error: true}`. Each answered ticket is the page's callback (the prelude's
`mapAsync` registered it), queued as a task; an answer for no waiting readback, or of the
wrong size, is dropped (the readback then fails). -/
def gpuGive (h : Page.Host) (request : JSON.Json) : Page.Host := Id.run do
  let xs := match request.field? "results" with
    | some (.array xs) => xs
    | _ => []
  let mut gpu := h.dom.gpu
  let mut loop := h.loop
  for x in xs.take PageGpu.maxPending do
    let t := (natField x "ticket").getD 0
    if (PageGpu.pendingOf gpu t).isNone then continue
    let data := match x.field? "dataBase64" with
      | some (.string b) => Rendering.SfntProfile.decodeBase64 b
      | _ => none
    gpu := match data.bind (PageGpu.deliver gpu t) with
      | some g => g
      | none => PageGpu.fail gpu t
    loop := loop.queueTask .other t
  return { h with dom := { h.dom with gpu }, loop }

/-- What Canvas 2D draws with and the layout reads, given anew before each action: the
fonts and images the engine holds may have changed since the page started (`fontLoad`,
`imageLoad`, `imageDrop`), and a read lays the page out with those held at the read, as
the frame does. A layout already made for the DOM's version is kept (`Reads.kept`). -/
def setReads (held : Held) (env : PageCanvas.Env) (measure : Option Page.Measure) : Held :=
  let page := fun (h : Page.Host) => { h with reads := { h.reads with canvasEnv := env, measure, styleKept := none, styleWrites := none } }
  { held with
    session := held.session.map fun (id, s, m) => (id, { s with host := page s.host }, m),
    leanSession := held.leanSession.map fun (id, s, m) => (id, s.setHost (page s.host), m) }

/-- The page's arena, parsed as `WebDocument.prepareDOM` parses it, so node numbers agree
with a render's replay of the commands. -/
def parse (html url : String) : Except String DOM.Dom :=
  if html.utf8ByteSize > 1048576 then .error "document HTML exceeds 1MiB"
  else if DOM.isXmlPath url then DOM.parseXmlDocument html
  else .ok (DOM.parseHtmlDocument html)

/-- The classic scripts in document order, with the sources a host supplied for `src`
scripts. A `src` script with no source is skipped and reported. `modules`: the engine runs
module scripts (BubblePopJS, `LeanJSModules`), so they are not reported, and a classic script
with `nomodule` is not run; the third answer says whether the page has a module script. -/
def scriptSources (dom : DOM.Dom) (request : JSON.Json) (modules : Bool := false) :
    Except String (Array (Nat × String) × Array String × Bool) := do
  let resources := match request.field? "resources" with | some (.array rs) => rs | _ => []
  if resources.length > 64 then throw "scriptSession: more than 64 script resources"
  let mut out := #[]
  let mut missing := #[]
  let mut hasModule := false
  for r in WebRenderScript.scriptRecords dom do
    let kind := str r "kind"
    let some id := natField r "nodeId" | throw "scriptSession: script nodeId"
    if kind == "module" then
      hasModule := true
      if !modules then missing := missing.push s!"module script {id} is not run"
    if kind != "classic" then continue
    if modules && r.field? "nomodule" == some (.bool true) then continue
    let src := str r "src"
    if src.isEmpty then out := out.push (id, str r "source")
    else
      match resources.find? (fun x => natField x "nodeId" == some id) with
      | some x =>
        let source := str x "source"
        if source.utf8ByteSize > WebRender.maxSourceBytes then throw "scriptSession: a script exceeds 16 MiB"
        out := out.push (id, source)
      | none => missing := missing.push s!"script {src} was not supplied"
  return (out, missing, hasModule)

/-- The pointer data of a `pointer` request as the JSON init of its events: the
coordinates of the `nodeAt` answer (`clientX`, `clientY`, `pageX`, `pageY`, `offsetX`,
`offsetY`), `button`, `buttons`, `pointerId`, `pressure`, `width`, `height`, and
`pointerType` (mouse, pen or touch). Only numbers of these names pass, so the prelude
reads nothing else. -/
def pointerInit (request : JSON.Json) : String :=
  let numeric := ["clientX","clientY","pageX","pageY","offsetX","offsetY","screenX","screenY","movementX","movementY",
    "button","buttons","pointerId","pressure","width","height","tiltX","tiltY"]
  let fields := numeric.filterMap fun k => match request.field? k with
    | some (.number n) => some (k,JSON.Json.number n)
    | _ => none
  let kind := str request "pointerType" "mouse"
  let kind := if ["mouse","pen","touch"].contains kind then kind else "mouse"
  let screen := (if fields.any (·.1 == "screenX") then [] else (fields.find? (·.1 == "clientX")).map (fun f => ("screenX",f.2)) |>.toList) ++
    (if fields.any (·.1 == "screenY") then [] else (fields.find? (·.1 == "clientY")).map (fun f => ("screenY",f.2)) |>.toList)
  (JSON.Json.object (fields ++ screen ++ [("pointerType",.string kind),("isPrimary",.bool true)] ++
    (if fields.any (·.1 == "pointerId") then [] else [("pointerId",num 1)]))).toString

def boolField (request : JSON.Json) (k : String) : Bool := request.field? k == some (.bool true)

/-- The page's viewport in CSS pixels: the window's `width`, and its `height` less the
full chrome of `shell` (the rows that a render lays the page out in,
`WebDocument.layoutTop`), in device pixels, over the screen's device pixels for each CSS
pixel, `zoomUnit` (percent; 100 if absent), as `WebDocument.layOut` lays the page out. -/
def viewport (request : JSON.Json) : Option (Nat × Nat) := do
  let w ← natField request "width"
  let h ← natField request "height"
  let top := match request.field? "shell" with
    | some j => WebShell.fullHeight (WebShell.Shell.ofJson j) w
    | none => 0
  let unit := match natField request "zoomUnit" with | some u => if u == 0 then 100 else u | none => 100
  if unit == 100 then return (w, max 1 (h - top))
  return (max 1 (w*100/unit), max 1 ((h - top)*100/unit))

def pointerKind : String → Option Page.PointerKind
  | "down" => some .down | "move" => some .move | "up" => some .up | "cancel" => some .cancel | _ => none


/-! ## The AOT path: the session program with the host as its machine -/

private def b64Digit (n : Nat) : UInt8 :=
  if n < 26 then (65 + n).toUInt8 else if n < 52 then (71 + n).toUInt8
  else if n < 62 then (n - 4).toUInt8 else if n == 62 then 43 else 47

/-- Base64 of bytes. -/
def base64 (b : ByteArray) : String := Id.run do
  let mut out := ByteArray.emptyWithCapacity ((b.size + 2) / 3 * 4)
  let mut i := 0
  for _ in [0:(b.size + 2) / 3] do
    let x0 := b[i]!.toNat
    let x1 := if i + 1 < b.size then b[i+1]!.toNat else 0
    let x2 := if i + 2 < b.size then b[i+2]!.toNat else 0
    let w := x0 * 65536 + x1 * 256 + x2
    out := out.push (b64Digit (w / 262144)) |>.push (b64Digit (w / 4096 % 64))
    out := out.push (if i + 1 < b.size then b64Digit (w / 64 % 64) else 61)
    out := out.push (if i + 2 < b.size then b64Digit (w % 64) else 61)
    i := i + 3
  return String.fromUTF8! out

def writesJson (ws : Array (Nat × ByteArray)) : JSON.Json :=
  .array (ws.toList.map fun (p, b) => .array [num p, .string (base64 b)])

def typeName : WasmVM.ValType → String
  | .i32 => "i32" | .i64 => "i64" | .f32 => "f32" | .f64 => "f64" | _ => "ref"

/-- The head of `aotModule`: what the host needs to make an instance and pass calls back.
For import `k` (named `aot.i{k}`): its parameter and result types and the ranges its host
function reads (`[ptrArg, lenArg, bound]`). -/
def moduleHead (p : PageAot.Prepared) : JSON.Json :=
  .object [("bytes",num p.bytes.size),("guestBytes",num p.guestBytes),
    ("importModule",.string WasmVM.Aot.importModule),("fuel",.string WasmVM.Aot.fuelExport),
    ("memory",.string "memory"),("exports",.array (Page.exportNames.toList.map .string)),
    ("imports",.array ((p.types.zip p.reads).zipIdx.toList.map fun ((t, rs), k) => .object [
      ("name",.string (WasmVM.Aot.importName k)),
      ("params",.array (t.params.toList.map (.string ∘ typeName))),
      ("results",.array (t.results.toList.map (.string ∘ typeName))),
      ("reads",.array (rs.map fun r => .array [num r.ptr, num r.len, num r.bound]))]))]

private def intOf? : JSON.Json → Option Int
  | .number n => n.toInt?
  | .string n => n.toInt?
  | _ => none

/-- An argument of the host as a value of type `t`: i32 as a JavaScript number (signed or
not), i64 as a decimal string (a JavaScript BigInt). -/
def valueOf (t : WasmVM.ValType) (j : JSON.Json) : Option WasmVM.Value :=
  match t, intOf? j with
  | .i32, some i => some (.i32 (Int.toNat (i % 4294967296)).toUInt32)
  | .i64, some i => some (.i64 (Int.toNat (i % 18446744073709551616)).toUInt64)
  | _, _ => none

def valueJson : WasmVM.Value → JSON.Json
  | .i32 v => num v.toNat
  | .i64 v => .string (toString v.toNat)
  | _ => .null

def askJson (fuel : Nat) : Page.Ask → JSON.Json
  | .invoke fa args => .object [("do",.string "invoke"),("export",.string (Page.exportNames[fa]?.getD "")),
      ("args",.array (args.toList.map valueJson)),("fuel",num fuel)]
  | .read p n => .object [("do",.string "read"),("ptr",num p),("len",num n)]
  | .write p b => .object [("do",.string "write"),("ptr",num p),("bytes",.string (base64 b))]

abbrev Result := Except String Page.Session

/-- Go on until an ask for the host or the end. A write that fits the memory is taken at
once (the host makes it before the next ask, in order); one that does not is an error to
the program, as the interpreter's `writeMem` gives. -/
def stepTurn (t : Turn) (cur : Result ⊕ PageAot.Paused Result) : Turn × Option Result := Id.run do
  let mut t := t
  let mut cur := cur
  for _ in [0:1048576] do
    match cur with
    | .inl r => return (t, some r)
    | .inr p =>
      match p.ask with
      | .write ptr b =>
        if ptr + b.size ≤ t.memSize then
          t := { t with pending := t.pending.push (ptr, b) }
          cur := p.resume (.wrote (.ok ()))
        else cur := p.resume (.wrote (.error "out of bounds memory access"))
      | _ => return ({ t with stage := .paused p }, none)
  return (t, some (.error "scriptSession: too many writes in a row"))

/-- The answer after a step: the next ask, or the turn's answer. -/
def answerTurn (held : Held) (t : Turn) (r : Option Result) (ns : Nat) : Held × Except String String :=
  let t := { t with ns := t.ns + ns }
  let writes := ("writes", writesJson t.pending)
  match r with
  | none =>
    let ask := match t.stage with
      | .fresh _ => JSON.Json.object [("do",.string "instantiate")]
      | .paused p => askJson p.session.limits.fuel p.ask
    ({ held with turn := some { t with pending := #[] } },
     .ok (JSON.Json.object [("session",num t.id),("aot",ask),writes]).toString)
  | some (.error e) => ({ held with turn := none, session := none }, .error s!"scriptSession: {e}")
  | some (.ok s) =>
    let (answer, marks) := turnAnswer t.id t.before s t.marks t.full t.ns [writes,("memSize",num t.memSize)]
    ({ held with turn := none, session := some (t.id, drained s, marks), memSize := t.memSize }, .ok answer)

/-- Begin an AOT turn with a program. -/
def beginTurn {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (id : Nat) (before : Before) (marks : Marks) (full : Bool) (fresh : Bool)
    (prog : Page.Prog Result) : M (Held × Except String String) := do
  let t : Turn := { id, before, marks, full, ns := 0, stage := .fresh prog, memSize := held.memSize }
  if fresh then return answerTurn held t none 0
  let ((t, r), ns) ← WebWasm.timed fun _ => stepTurn t (PageAot.Prog.next prog)
  return answerTurn held t r ns

/-- The host's reply to the ask the turn waits on. -/
def resumeTurn {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (t : Turn) (reply : JSON.Json) : M (Held × Except String String) := do
  let memSize := (natField reply "memSize").getD t.memSize
  let t := { t with memSize }
  let fail := fun (e : String) => answerTurn held t (some (.error e)) 0
  match t.stage with
  | .fresh prog =>
    if let some (.string e) := reply.field? "error" then return fail s!"host instance: {e}"
    let ((t, r), ns) ← WebWasm.timed fun _ => stepTurn t (PageAot.Prog.next prog)
    return answerTurn held t r ns
  | .paused p =>
    let next : Except String (PageAot.Paused Result × Page.Reply) := match p.ask with
      | .invoke _ _ =>
        let left := ((reply.field? "fuel").bind intOf?).getD 0
        let o : WasmVM.Outcome := match reply.field? "values", reply.field? "trap", reply.field? "exit" with
          | some (.array vs), _, _ => .values (vs.toArray.filterMap (valueOf .i32))
          | _, some (.string m), _ => .trap (.host m)
          | _, _, some (.number n) => .exit (n.toNat?.getD 0)
          | _, _, _ => .trap (.host "the host gave no outcome")
        .ok (PageAot.ranReply p o left)
      | .read _ _ =>
        match reply.field? "bytes", reply.field? "error" with
        | some (.string b), _ => match Rendering.SfntProfile.decodeBase64 b with
          | some bytes => .ok (p, .bytes (.ok bytes))
          | none => .error "the host's bytes are not Base64"
        | _, some (.string e) => .ok (p, .bytes (.error e))
        | _, _ => .error "the host gave no bytes"
      | .write _ _ => .error "a write is not asked of the host"
    match next with
    | .error e => return fail e
    | .ok (p, r) =>
      let ((t, r), ns) ← WebWasm.timed fun _ => stepTurn t (p.resume r)
      return answerTurn held t r ns

/-- One import call of the guest, passed back by the host while it runs an export. -/
def hostCall {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (aot : PageAot.Prepared) (t : Turn) (request : JSON.Json) :
    M (Held × Except String String) := do
  match t.stage with
  | .fresh _ => return (held, .error "scriptSession: no run waits for a host call")
  | .paused p =>
    let id := (natField request "id").getD 0
    let memSize := (natField request "memSize").getD t.memSize
    let args := match request.field? "args" with | some (.array a) => a | _ => []
    let params := (aot.types[id]?.map (·.params)).getD #[]
    let vals := (params.toList.zip args).filterMap fun (ty, j) => valueOf ty j
    let segs := match request.field? "reads" with
      | some (.array rs) => rs.toArray.filterMap fun r => match r with
        | .array [.number q, .string b] => match q.toNat?, Rendering.SfntProfile.decodeBase64 b with
          | some q, some bytes => some (q, bytes)
          | _, _ => none
        | _ => none
      | _ => #[]
    if vals.length != params.size || args.length != params.size then
      return (held, .ok (JSON.Json.object [("trap",.string s!"aot: wrong arguments for import {id}")]).toString)
    let fuelLeft := ((request.field? "fuel").bind intOf?).getD (Int.ofNat p.session.limits.fuel)
    let ((p, r, writes), ns) ← WebWasm.timed fun _ => PageAot.serveHost p id vals.toArray memSize segs fuelLeft
    let t := { t with stage := .paused p, memSize, ns := t.ns + ns }
    let answer := match r with
      | .values vs => JSON.Json.object [("results",.array (vs.toList.map valueJson)),("writes",writesJson writes)]
      | .trap m => .object [("trap",.string m)]
      | .exit n => .object [("exit",num n)]
    return ({ held with turn := some t }, .ok answer.toString)

/-! ## BubblePopJS, the engine written in Lean -/

/-! ### Frame documents (HTML §4.8.5)

The script session gives every connected `iframe` a browsing context (`frames:true`):
`about:blank` at once, a `srcdoc` document that Lean parses and loads after the turn
(`srcdocLoads`), and a URL for the embedder when it set `navigations:true` in `start`: each
turn lists them (`navigations`), and the embedder answers each with the action `frame`. A
frame's scripts run in the page's realm with `document` the frame's
(`Page.Session.loadFrameP`, `LeanJS.loadFrame`). Not on the AOT path (the Hub). -/

/-- Rounds of `srcdoc` loads after a turn (for frames in frames). -/
def frameRounds : Nat := 4

/-- A navigation that Lean answers itself, with no request to the embedder: a `srcdoc`
document, or a `blob:` URL (File API §8.3: the entry is in the engine, and only its own
origin reads it). -/
def leanNavigation (u : String) : Bool := u == "about:srcdoc" || u.startsWith "blob:"

/-- The document of a frame's navigation to the `blob:` URL `u`: the blob's text when the
page's own origin made the URL (`Net.Xhr.State.blobOf`) and its type is `text/html`,
decoded as a document is (HTML §13.2.3, with the charset of the type). Else "", which
leaves the frame at `about:blank` (a network error for the navigation). -/
def blobDocument (h : Page.Host) (u : String) : String :=
  match h.web.net.blobOf u with
  | some (type, bytes) =>
    let mime := L4Factoidal.WHATWG.MimeType.parse type
    if mime.map (·.essence) == some "text/html" then
      (L4Factoidal.WHATWG.Encoding.Sniff.decodeDocumentFast bytes (mime.bind (·.param "charset"))).2
    else ""
  | none => ""

/-- The documents of frames that wait for Lean (`leanNavigation`: `srcdoc`, and `blob:` URLs):
Lean parses each and loads it with its inline scripts, at most `frameRounds` rounds. A page
with no waiting navigation pays one look at an empty list. -/
def srcdocLoads {σ : Type} (host : σ → Page.Host) (load : σ → Nat → String → Array (Nat × String) → σ) (s : σ) :
    σ × Nat := Id.run do
  let mut s := s
  let mut n := 0
  for _ in [0:frameRounds] do
    let navs := (host s).dom.navigations.filter (leanNavigation ·.2)
    if navs.isEmpty then break
    for (el, u) in navs do
      let src := if u == "about:srcdoc" then (Dom.attrValue? (host s).dom.dom el "srcdoc").getD "" else blobDocument (host s) u
      let scripts := ((scriptSources (DOM.parseHtmlDocument src) (.object [])).toOption.map (·.1)).getD #[]
      s := load s el src scripts
      n := n + 1
  return (s, n)

/-- The frame navigations the embedder is to answer (action `frame`): an `iframe` and a URL. -/
def hostNavigations (h : Page.Host) : JSON.Json :=
  .array ((h.dom.navigations.filter fun (_, u) => !u.isEmpty && !leanNavigation u).toList.map fun (el, u) =>
    .object [("nodeId", num el), ("url", .string u)])

/-- The frame fields of a turn answer, only when there is something to say: `navigations`
for the embedder, and `frameLoads`, the `srcdoc` documents Lean loaded in the turn. -/
def frameFields (h : Page.Host) (loads : Nat) : List (String × JSON.Json) :=
  let waiting := h.dom.navigations.any fun (_, u) => !u.isEmpty && !leanNavigation u
  (if waiting then [("navigations", hostNavigations h)] else []) ++ (if loads == 0 then [] else [("frameLoads", num loads)])

/-- The document of a `frame` action (the embedder's answer to a navigation): `bytesBase64`
with `contentType` (decoded by Lean: HTML §13.2.3 sniffing with the transport charset, then
the Encoding Standard's decoder, `WHATWG.Encoding.Sniff.decodeDocumentFast`), or `source`
as text; empty, or `failed:true`, for a load that failed (the frame keeps `about:blank`).
Parsed as XML for an `.xht`, `.xhtml` or `.svg` URL. With its classic scripts and the sources of
the `resources` the embedder read (node numbers of the document parsed on its own). -/
def frameDocument (request : JSON.Json) : Except String (String × Bool × Array (Nat × String) × String) := do
  let url := str request "url"
  -- (encoding100) the document's encoding: the decode's here, or the name the embedder sends
  -- with `source` when it decoded the bytes (`encoding`)
  let (src, enc) ← if request.field? "failed" == some (.bool true) then pure ("", "") else
    match request.field? "bytesBase64" with
    | some (.string b) =>
      match Rendering.SfntProfile.decodeBase64 b with
      | some bytes =>
        let ct := str request "contentType"
        let label := if ct.isEmpty then none
          else (L4Factoidal.WHATWG.Encoding.Sniff.extractFromMeta ct).orElse fun _ =>
            if ct.contains ';' || ct.contains '/' then none else some ct
        let (e, t) := L4Factoidal.WHATWG.Encoding.Sniff.decodeDocumentFast bytes label
        pure (t, e.name)
      | none => throw "bytesBase64 is not Base64"
    | _ => pure (str request "source", str request "encoding")
  if src.isEmpty then return ("", false, #[], enc)
  let dom ← parse src url
  let (scripts, _) ← scriptSources dom request
  return (src, DOM.isXmlPath url, scripts, enc)


/-! ### Sandboxed frames: script sessions of their own (`HTML.FrameSessions`)

A frame whose document has an opaque origin and may run scripts (`Hosts.Dom.sessionFrames`:
`sandbox` with `allow-scripts` and without `allow-same-origin`, and a `srcdoc`) gets a
session of its own: its own arena, heap and event loop, with smaller budgets
(`frameLimits`). After each turn of the page, `pumpFrames` makes the sessions of new such
frames, then hands messages between the sessions (`FrameSessions.exchange`, at most
`frameRounds` rounds), each frame's session running its due tasks at the page's clock. A
page with no `iframe` element pays one look at the nodes made in the turn. Not on the AOT
path (the Hub). -/

/-- The budgets of a frame's session: an eighth of the page's instructions for one task,
at most 32 MiB of memory, at most 4096 commands and 256 console lines, so a frame cannot
starve its page. -/
def frameLimits (lim : Page.Limits) (fEnt : Nat → ByteArray) (el : Nat) : Page.Limits :=
  { lim with entropy := fEnt el, fuel := lim.fuel / 8, pages := min lim.pages 512, commands := min lim.commands 4096, logs := 256, frames := false }

/-- Tasks a frame's session may run in one round; rounds of messages in one pump; frames
with sessions in one page. -/
def frameTasks : Nat := 1000
def maxFrameSessions : Nat := 16

/-- What the pump needs of a session type. -/
structure FrameOps (σ : Type) where
  host : σ → Page.Host
  setHost : σ → Page.Host → σ
  deliver : σ → HTML.FrameSessions.Message → σ
  advanceTo : σ → Nat → σ
  /-- A frame's session for the `iframe` element `el` (its own entropy: `frameLimits`). -/
  start : Nat → DOM.Dom → Array (Nat × String) → HTML.Frames.Origin × HTML.Frames.Origin → Option σ
  /-- A frame's navigation ends with a document: `loadFrame` of the engine. -/
  load : σ → Nat → String → Array (Nat × String) → σ

/-- One session's part of an exchange: the messages for it delivered, its due tasks run at
`clock`, and the messages it posted taken from its outbox. -/
def frameRun {σ : Type} (ops : FrameOps σ) (clock : Nat) (s : σ) (ms : Array HTML.FrameSessions.Message) :
    σ × Array HTML.FrameSessions.Message :=
  let s := ms.foldl ops.deliver s
  let s := ops.advanceTo s clock
  let h := ops.host s
  (ops.setHost s { h with outbox := #[] }, h.outbox)

/-- Whether the nodes made since the arena had `scanned` nodes hold an `iframe` element. -/
def newIframe (d : DOM.Dom) (scanned : Nat) : Bool := Id.run do
  for i in [scanned:d.size] do
    if DOM.Dom.isHtmlElement (d.get i) "iframe" then return true
  return false

/-- The entropy of the frames a turn of the interpreter's session `id` may start: fresh bytes
are drawn only when the turn made an `iframe` element, so a page with none draws nothing. -/
def frameEntropyIf {M : Type → Type} [Monad M] [WebWasm.Machine M] (id : Nat) (parent : ByteArray) (d : DOM.Dom) (scanned : Nat) :
    M (Nat → ByteArray) := do
  if newIframe d scanned then return frameEntropyOf id parent (← turnBytes) else return fun _ => ByteArray.empty

/-- After a turn of the page: sessions for its new sandboxed frames, then the messages. -/
def pumpFrames {σ : Type} (ops : FrameOps σ) (parent : σ) (frames : Array (Nat × σ)) (scanned : Nat) :
    σ × Array (Nat × σ) × Nat := Id.run do
  let h := ops.host parent
  let d := h.dom.dom
  let mut frames := frames
  if newIframe d scanned then
    for (el, src, f) in Dom.sessionFrames h.dom do
      if !frames.any (·.1 == el) && frames.size < maxFrameSessions then
        let dom := DOM.parseHtmlDocument src
        let scripts := ((scriptSources dom (.object [])).toOption.map (·.1)).getD #[]
        if let some c := ops.start el dom scripts (f.origin, Dom.pageOrigin h.dom) then
          frames := frames.push (el, c)
  if frames.isEmpty then return (parent, frames, d.size)
  let clock := h.loop.clock
  let mut m : HTML.FrameSessions.SessionMap σ := { parent, frames }
  let mut pending : Array HTML.FrameSessions.Message := #[]
  for _ in [0:frameRounds] do
    let (m', out) := HTML.FrameSessions.exchange (frameRun ops clock) m pending
    m := m'
    pending := out
    if pending.isEmpty then break
  return (m.parent, m.frames, d.size)

def pageFrameOps (m : Page.Module') (lim : Page.Limits) (fEnt : Nat → ByteArray) : FrameOps Page.Session :=
  { host := (·.host), setHost := fun s h => { s with host := h },
    deliver := fun s msg => (s.deliverP msg).runLocal,
    advanceTo := fun s c => (s.advance c frameTasks).1,
    start := fun el dom scripts o =>
      (Page.start m dom "about:srcdoc" scripts (frameLimits lim fEnt el) #[] {} {} (some o)).toOption,
    load := fun s el src scripts => s.loadFrame el src scripts }

def leanFrameOps (base : LeanJS.Session) (lim : Page.Limits) (fEnt : Nat → ByteArray) : FrameOps LeanJS.Session :=
  { host := (·.host), setHost := LeanJS.Session.setHost,
    deliver := fun s msg =>
      let e := LeanJS.engine
      e.checkpoint (e.dispatchWith s Page.windowId "message" (Page.messageInit msg)).1,
    advanceTo := fun s c => (LeanJS.engine.advance s c frameTasks).1,
    start := fun el dom scripts o => some (LeanJS.start base dom "about:srcdoc" scripts (frameLimits lim fEnt el) {} {} (some o)),
    load := fun s el src scripts => LeanJS.loadFrame s el src scripts }

/-- The frames' sessions after frame `el` took the document `src` of `url` (the embedder's
answer to a navigation): a document of another origin whose scripts may run gets a session
of its own, as a sandboxed `srcdoc` frame does, with the frame's origin and the page's
(`LeanJS.start` with `origins`). Its scripts never run in the page's realm
(`Hosts.Dom.realmScripts`, `realmScripts_needs_access`), and the two sessions share only the
messages of `HTML.FrameSessions.exchange`. The session of a former document of the frame is
dropped. A page whose frames are all of its own origin pays one comparison here. -/
def crossFrameSessions (base : Option LeanJS.Session) (page : LeanJS.Session) (fEnt : Nat → ByteArray)
    (frames : Array (Nat × LeanJS.Session)) (el : Nat) (src url : String) (scripts : Array (Nat × String)) :
    Array (Nat × LeanJS.Session) :=
  let rest := frames.filter fun (p : Nat × LeanJS.Session) => p.1 != el
  let d := page.host.dom
  let f := Dom.elementFrame d el
  match base, parse src url with
  | some base, .ok dom =>
    if src.isEmpty || Dom.frameAccessible d el || !f.scriptsMayRun || rest.size ≥ maxFrameSessions then rest
    else
      -- no requests and no frames of its own: nothing would answer them from this session
      let lim := { frameLimits page.limits fEnt el with network := false, hostLoads := false }
      rest.push (el, LeanJS.start base dom url scripts lim {} {} (some (f.origin, Dom.pageOrigin d)))
  | _, _ => rest

/-- A page whose scripts name `XMLHttpRequest`: a later action may make a sync request, so
each action keeps the session before it (`Net.Xhr.State.mayBlock`). Other pages pay nothing. -/
def mentionsXhr (scripts : Array (Nat × String)) : Bool :=
  scripts.any fun (_, src) => (src.splitOn "XMLHttpRequest").length > 1

/-- One request to the host, as JSON. -/
def wireJson (w : Net.PageFetch.Wire) : JSON.Json :=
  .object ([("id", num w.id), ("method", .string w.method), ("url", .string w.url),
      ("headers", .array (w.headers.map fun (n, v) => .array [.string n, .string v]))] ++
      (match w.body with | some b => [("bodyBase64", .string (WHATWG.Base64.encode b))] | none => []) ++
      (if w.resolve then [("resolve", .bool true)] else []) ++
      (if w.address.isEmpty then [] else [("address", .string w.address), ("port", num w.port)]))

/-- The answer that undoes this run and asks the host for one sync request. -/
def netSyncAnswer (id : Nat) (w : Net.PageFetch.Wire) : Except String String :=
  .ok (JSON.Json.object [("session", num id), ("netSync", wireJson w)]).toString

/-- A sync-answer list for a run, on the Lean engine's net state. `snap`: the action keeps the
session before it (only a page that has made an `XMLHttpRequest` pays that copy, see `run`). -/
def setSync (w : WebApi.State) (snap : Bool) (cache : Array Net.PageFetch.Answer) : WebApi.State :=
  { w with net := { w.net with syncOk := snap, syncAnswers := cache, syncUsed := 0, syncWanted := none } }

/-- The page requests of a turn: `netRequests`, and `netCancels` for the host to stop. Only
when there are some. -/
def netFields (h : Page.Host) : List (String × JSON.Json) :=
  let net := h.web.net
  (if net.outbox.isEmpty then [] else [("netRequests", .array (net.outbox.toList.map wireJson))]) ++
  (if net.cancels.isEmpty then [] else [("netCancels", .array (net.cancels.toList.map num))])

/-- One answer of action `net` (`Net.PageFetch.Answer`). -/
def netAnswer (x : JSON.Json) : Nat × Net.PageFetch.Answer :=
  let hs : List (String × String) := match x.field? "headers" with
    | some (.array xs) => xs.filterMap fun
      | .array [.string n, .string v] => some (n, v)
      | _ => none
    | _ => []
  let body := match x.field? "bodyBase64" with
    | some (.string b) => (Rendering.SfntProfile.decodeBase64 b).getD ByteArray.empty
    | _ => ByteArray.empty
  let addresses : List String := match x.field? "addresses" with
    | some (.array xs) => xs.filterMap fun | .string a => some a | _ => none
    | _ => []
  let answer : Net.PageFetch.Answer :=
    { status := (natField x "status").getD 0, statusText := str x "statusText", headers := hs, body := body, url := str x "url",
      addresses }
  ((natField x "id").getD 0, answer)

/-- The answers of action `net`. -/
def netResults (request : JSON.Json) : Array (Nat × Net.PageFetch.Answer) :=
  match request.field? "results" with
  | some (.array xs) => xs.toArray.map netAnswer
  | _ => #[]

/-- Apply the host's answers: each answered request's callback is a task on the networking
source of the event loop (`Net.Xhr.give`). -/
def netGiveAll (h : Page.Host) (answers : Array (Nat × Net.PageFetch.Answer)) : Page.Host := Id.run do
  let mut net := h.web.net
  let mut loop := h.loop
  for (id, a) in answers do
    let (net', cb) := Net.Xhr.give net id a
    net := net'
    if let some c := cb then loop := loop.queueTask .networking c
  return { h with web := { h.web with net }, loop }

def netGive (h : Page.Host) (request : JSON.Json) : Page.Host := netGiveAll h (netResults request)

/-- The error of the turn's Perform Actions (`actions`), if WebDriver refused it. -/
def inputFields (s : LeanJS.Session) : List (String × JSON.Json) :=
  (match s.trusted.error with
  | some er => [("inputError", .object [("error", .string er.code.name), ("message", .string er.message)])]
  | none => []) ++
  -- whether the host may scroll for the last key (`PointerState.keyDefault`)
  (match s.host.pointer.keyDefault with
  | some b => [("keyDefault", .bool b)]
  | none => [])

/-- The error and the key's default are reported once. -/
def inputReported (s : LeanJS.Session) : LeanJS.Session :=
  let s := if s.trusted.error.isNone then s else s.setTrusted { s.trusted with error := none }
  if s.host.pointer.keyDefault.isNone then s
  else s.setHost { s.host with pointer := { s.host.pointer with keyDefault := none } }

/-- The node of an element reference of a host's `actions`: `path:` and the child indices
from the document (`WebDriver.Input.resolvePath`). -/
def refNode (d : DOM.Dom) (ref : String) : Option Nat :=
  if ref.startsWith "path:" then
    WebDriver.Input.resolvePath (fun n => (d.get n).kids) (fun n => (d.get n).shadow) 0 (String.ofList (ref.toList.drop 5))
  else none

/-- The input sources of an `actions` request: its `text` typed at the keyboard, else its
`actions` (`WebDriver.Actions.parse`). -/
def inputSources (request : JSON.Json) : Except WebDriver.Error (List WebDriver.Actions.Source) :=
  match request.field? "text" with
  | some (.string text) => .ok [WebDriver.Actions.typeableSource text]
  | _ => WebDriver.Actions.parse request

/-- The key of a host's `key` request (`WebDriver.HostKeys.HostKey`): committed `text`, a
macOS key code `mac`, or a DOM key value `key`, with the `modifiers` bits (1 Shift, 2
Command, 4 Option, 8 Control). -/
def hostKeyOf (request : JSON.Json) : Option WebDriver.HostKeys.HostKey :=
  let bits := (natField request "modifiers").getD 0
  match request.field? "text", natField request "mac", request.field? "key" with
  | some (.string t), _, _ => some (.text t)
  | _, some code, _ => some (.mac code bits)
  | _, _, some (.string k) => some (.dom k bits)
  | _, _, _ => none

/-- Input of the user as WebDriver's Perform Actions (`Actions.perform`, then Release
Actions with `release`) over the engine (`PageEvents.inputDriver`): the one place the
trusted input state changes. An event that gives user activation records its time. -/
def performInput (sources : List WebDriver.Actions.Source) (release : Bool) (a : LeanJSWorkers.Agents) :
    LeanJSWorkers.Agents :=
  let e := LeanJSWorkers.engine
  let base := e.inputDriver refNode
  let dispatch := fun (a : LeanJSWorkers.Agents) (low : WebDriver.Actions.Low) =>
    let a := base.dispatch a low
    if WebDriver.Input.activates low then { a with page := a.page.setTrusted { a.page.trusted with activated := some (e.loop a).clock } } else a
  let d : WebDriver.Actions.Driver LeanJSWorkers.Agents := { env := base.env, dispatch := dispatch, wait := base.wait }
  let start : WebDriver.Actions.Run LeanJSWorkers.Agents := { engine := a, input := a.page.trusted.actions }
  let r := WebDriver.Actions.perform d start sources
  let r := if release then WebDriver.Actions.release d r else r
  let a := r.engine
  { a with page := a.page.setTrusted { a.page.trusted with actions := r.input, error := r.error } }

/-- The answer of a turn of the Lean engine; the session, its workers and its sandboxed
frames' sessions are kept. A page with workers adds `workers` (how many run) and `fetches`
(the scripts they wait for). `fEnt` is the entropy of frames that get a session in this turn
(`frameEntropy`). -/
def leanTurn (held : Held) (id : Nat) (before : Before) (a : LeanJSWorkers.Agents) (marks : Marks) (full : Bool) (ns : Nat)
    (fEnt : Nat → ByteArray) : Held × Except String String :=
  let (s, loads) := srcdocLoads (·.host) (fun s el src scripts => LeanJS.loadFrame s el src scripts) a.page
  let (s, frames, scan) := match held.leanBase with
    | some base => pumpFrames (leanFrameOps base s.limits fEnt) s held.leanFrames held.frameScan
    | none => (s, held.leanFrames, held.frameScan)
  let workers : List (String × JSON.Json) :=
    if a.w.list.isEmpty && a.w.loads.isEmpty then [] else
    [("workers", num a.w.list.size)] ++ (if a.w.loads.isEmpty then [] else [("fetches", .array a.w.fetches)])
  let view := View.ofLean s
  let view := if a.waits then { view with quiet := false } else view
  let (answer, marks) := turnAnswerOf id before view marks full ns
    ([("engine",.string "bubblepop")] ++ frameFields s.host loads ++ workers ++ netFields s.host ++ inputFields s)
  ({ held with leanSession := some (id, inputReported (drainedLean s), marks), leanWorkers := a.w, leanFrames := frames, frameScan := scan }, .ok answer)

/-- `start` on the Lean engine: its realm is made at the first page (the prelude runs
once), and each page starts from it with its own arena. -/
def startLean {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (html : String) (request : JSON.Json) (measure : JSON.Json → Option Page.Measure)
    (canvas : PageCanvas.Env := {}) : M (Held × Except String String) := do
  let url := str request "url"
  let commands := min 1048576 ((natField request "commandLimit").getD L4Factoidal.WasmVM.Hosts.Dom.maxCommands)
  let logs := min 1048576 ((natField request "logLimit").getD 1024)
  let id := held.nextSession
  let hostLoads := request.field? "navigations" == some (.bool true)
  let network := request.field? "network" == some (.bool true)
  let hostCors := request.field? "hostCors" == some (.bool true)
  -- a start done again after a sync request (its answers are in `syncCache`) keeps its entropy
  let ent ← match held.startEntropy with
    | some e => if held.syncCache.isEmpty then entropy id else pure e
    | none => entropy id
  let lim : Page.Limits := { commands, logs, gpuPage := id, entropy := ent, encoding := str request "encoding", frames := true, hostLoads, network, hostCors, pageAddress := str request "pageAddress", referrerPolicy := str request "referrerPolicy", syncOk := true, syncAnswers := held.syncCache }
  let made := show Except String (Array (Nat × String) × Array String × Bool × DOM.Dom) from do
    let dom ← parse html url
    let (scripts, missing, hasModule) ← scriptSources dom request (modules := true)
    return (scripts, missing, hasModule, dom)
  match made with
  | .error e => return (held, .error s!"scriptSession: {e}")
  | .ok (scripts, missing, hasModule, dom) =>
    -- Content Security Policy: the page's policy (its response's fields from the embedder, its
    -- `meta` elements) decides which of its classic scripts run; the others are violations
    let cspMeta := L4Factoidal.HTML.CspSource.metaText dom 0
    let (scripts, cspViolations) := L4Factoidal.HTML.CspSource.filterScripts (str request "csp") (str request "cspReportOnly")
      (L4Factoidal.Net.PageFetch.Page.ofUrl url hostCors (str request "pageAddress")) dom (LeanJSModules.baseOf dom url) scripts
    let lim := { lim with csp := str request "csp", cspReportOnly := str request "cspReportOnly", cspMeta, cspViolations }
    let (base, ns0) ← WebWasm.timed fun _ => match held.leanBase with
      | some b => Except.ok b
      | none => LeanJS.prepare
    match base with
    | .error e => return (held, .error s!"scriptSession: BubblePopJS: {e}")
    | .ok base =>
      -- module scripts: their graphs are fetched first (each request a `netSync` and the start
      -- made again), so no script runs before they are all there. A page with none pays nothing.
      let page := Net.PageFetch.Page.ofUrl url hostCors (str request "pageAddress")
      let loaded := if hasModule then LeanJSModules.load dom url page held.syncCache else .ok {}
      if let .error w := loaded then
        return ({ held with leanBase := some base, pendingSync := some ("start", html, request), startEntropy := some ent }, netSyncAnswer id w)
      let mods := match loaded with | .ok m => m | .error _ => {}
      let lim := { lim with syncAnswers := held.syncCache.extract mods.used held.syncCache.size }
      let (vw, vh) := (viewport request).getD (800, 600)
      let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh, canvasEnv := canvas }
      let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
      let b ← turnBytes
      let wEnt := workerEntropyOf id b
      let (a, ns) ← WebWasm.timed fun _ =>
        let s := LeanJS.start base dom url scripts { lim with mayBlock := network && mentionsXhr scripts } reads { instructionsPerMs := rate } (mods := mods)
        let s := missing.foldl LeanJS.Session.fail s
        -- workers the page's scripts made: their scripts are asked for
        LeanJSWorkers.pump { page := s, base := some base, entropy := wEnt }
      match a.page.host.web.net.syncWanted with
      | some w => return ({ held with leanBase := some base, pendingSync := some ("start", html, request), startEntropy := some ent }, netSyncAnswer id w)
      | none =>
        let held := { held with leanBase := some base, session := none, leanSession := none, nextSession := id + 1, leanWorkers := {}, layoutRequest := layoutOf request, syncCache := #[], pendingSync := none, startEntropy := none }
        return leanTurn { held with frames := #[], leanFrames := #[], frameScan := 0 }
          id {} a {} true (ns0 + ns) (frameEntropyOf id lim.entropy b)

/-- A later action on the Lean engine's session (the actions of `act`). -/
def actLean {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (action : String) (request : JSON.Json) (id : Nat) (s : LeanJS.Session) (marks : Marks) :
    M (Held × Except String String) := do
  let full := request.field? "full" == some (.bool true)
  -- the page with its workers (`Hosts.LeanJSWorkers`): the page engine's steps, and the
  -- workers' after each checkpoint
  let e := LeanJSWorkers.engine
  let before := Before.ofLean s
  -- Undo needs the session as it was. It is kept only for a page that has made an XHR before
  -- this action or whose scripts name XMLHttpRequest (`mentionsXhr`), and a start, whose undo
  -- is the base realm: holding it would copy the page's heap array at the action's first
  -- write, and other pages must not pay that. The workers are `held.leanWorkers`, kept as
  -- they were when the run is undone.
  let keepIt := s.host.web.net.xhrs.size > 0 || s.host.web.net.mayBlock
  let snap := if keepIt then some s else none
  let s0 := s.setHost { s.host with web := setSync s.host.web keepIt held.syncCache }
  -- each worker's entropy is fresh from the machine's generator, as each page's is
  let b ← turnBytes
  let a : LeanJSWorkers.Agents := { page := s0, w := held.leanWorkers, base := held.leanBase, entropy := workerEntropyOf id b }
  let fEnt := frameEntropyOf id s.limits.entropy b
  let run := fun (f : LeanJSWorkers.Agents → LeanJSWorkers.Agents) => do
    let (a', ns) ← WebWasm.timed fun _ => f a
    match a'.page.host.web.net.syncWanted, snap with
    | some w, some old => return ({ held with leanSession := some (id, old, marks), pendingSync := some (action, "", request) }, netSyncAnswer id w)
    | _, _ => return leanTurn { held with syncCache := #[], pendingSync := none } id before a' marks full ns fEnt
  let keep := fun (msg : String) => pure (f := M) ({ held with leanSession := some (id, s, marks) }, Except.error msg)
  match action with
  | "click" =>
    match natField request "node" with
    | some node => run (e.click · node)
    | none => keep "scriptSession: click needs node"
  | "pointer" =>
    match pointerKind (str request "kind"), natField request "node" with
    | some kind, some node => run (e.pointer · kind node (pointerInit request))
    | _, _ => keep "scriptSession: pointer needs kind (down, move, up, cancel) and node"
  | "key" =>
    -- a key a person pressed in a host (the window, the Hub): its WebDriver key actions
    -- (`WebDriver.HostKeys`) on the same trusted path as `actions`
    match hostKeyOf request with
    | some k => run (performInput [WebDriver.HostKeys.sourceOf k] false)
    | none => keep "scriptSession: key needs text, mac or key"
  | "actions" =>
    -- input of the user as WebDriver's Perform Actions; the one place the trusted input state changes
    match inputSources request with
    | .error er => run fun a => { a with page := a.page.setTrusted { a.page.trusted with error := some er } }
    | .ok sources => run (performInput sources (boolField request "release"))
  | "message" =>
    -- a message of the embedder to the page: a `message` event at the window
    run fun a =>
      let a := e.checkpoint (e.dispatchWith a Page.windowId "message"
        (Page.messageInit { frame := 0, toParent := false, data := str request "data", origin := str request "origin" })).1
      (e.advance a (e.loop a).clock).1
  | "resize" =>
    match viewport request with
    | some (w, h) => run fun s => let s := e.resize s w h; (e.advance s (e.loop s).clock).1
    | none => keep "scriptSession: resize needs width and height"
  | "advance" => run fun s => e.flushMove (e.advance s ((e.loop s).clock + ((natField request "ms").getD 0))).1
  | "settle" => run fun s => (e.settle (e.flushMove s) ((natField request "budgetMs").getD 30000) 100000 LeanJSWorkers.Agents.waits).1
  | "turn" => run fun s => let s := e.flushMove s; (e.advance s (e.loop s).clock).1
  | "frame" =>
    match natField request "node", frameDocument request with
    | some node, .ok (src, xml, scripts, enc) =>
      -- the URL the document came from, when the embedder followed redirects (`responseUrl`):
      -- the frame's origin is that URL's
      let named := str request "responseUrl"
      let responseUrl := if named.isEmpty then none else some named
      -- a same-origin frame's scripts run in the page's realm; workers they make are asked
      -- for at once
      let (a', ns) ← WebWasm.timed fun _ => let s := a.page
        LeanJSWorkers.pump { a with page := LeanJS.loadFrame (s.setHost { s.host with dom := (s.host.dom.noteFrameEncoding node enc).noteFramePolicy node (str request "referrerPolicy") }) node src scripts xml responseUrl }
      match a'.page.host.web.net.syncWanted, snap with
      | some w, some old => return ({ held with leanSession := some (id, old, marks), pendingSync := some (action, "", request) }, netSyncAnswer id w)
      | _, _ =>
        -- a document of another origin: a session of its own (`crossFrameSessions`)
        let frames := crossFrameSessions held.leanBase a'.page fEnt held.leanFrames node src
          (if named.isEmpty then str request "url" else named) scripts
        return leanTurn { held with syncCache := #[], pendingSync := none, leanFrames := frames } id before a' marks full ns fEnt
    | _, .error e => keep s!"scriptSession: frame: {e}"
    | none, _ => keep "scriptSession: frame needs node"
  | "fetched" =>
    let got := match request.field? "results" with
      | some (.array xs) => xs.toArray.filterMap fun x =>
        held.leanWorkers.result ((natField x "id").getD 0) ((natField x "status").getD 0) (str x "url")
          (str x "contentType") (str x "source") (str x "contentTypeOptions")
      | _ => #[]
    -- each script's `Referrer-Policy` response field (`referrerPolicy`, "" for none), by the
    -- URL it was asked for: a worker's requests have its script's policy
    let pols := match request.field? "results" with
      | some (.array xs) => xs.toArray.filterMap fun x =>
        (held.leanWorkers.result ((natField x "id").getD 0) ((natField x "status").getD 0) (str x "url")
          (str x "contentType") (str x "source") (str x "contentTypeOptions")).map fun r => (r.1, str x "referrerPolicy")
      | _ => #[]
    run fun s => let s := LeanJSWorkers.give (LeanJSWorkers.notePolicies s pols) got; (e.advance s (e.loop s).clock).1
  | "net" =>
    let ms := (natField request "elapsedMs").getD 0
    run fun a =>
      let a := if ms == 0 then a else (e.advance a ((e.loop a).clock + ms)).1
      -- the answers to workers' requests go to them (`LeanJSWorkers.giveNet`), the rest to the page
      let all := netResults request
      let (a, rest) := LeanJSWorkers.giveNet a all
      let a := if rest.size == all.size then a else LeanJSWorkers.pump a
      let a := { a with page := a.page.setHost (netGiveAll a.page.host rest) }
      (e.advance a (e.loop a).clock).1
  | "gpuRead" =>
    run fun a =>
      let a := { a with page := a.page.setHost (gpuGive a.page.host request) }
      (e.advance a (e.loop a).clock).1
  | "cookies" =>
    -- WebDriver "Delete All Cookies" (§14.5), asked by the embedder's test driver: the page
    -- session's jar is emptied. No web_api op does this: a page's scripts can not.
    run fun a =>
      let h := a.page.host
      { a with page := a.page.setHost { h with web := { h.web with net := { h.web.net with cookies := {} } } } }
  | _ => keep "scriptSession: unknown action"

/-- One action on what the engine holds. `measure` lays out an arena for the layout reads
of its scripts (`WebDocument.measure`), with the `layout` request of `start`. -/
def act {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (action html : String) (request : JSON.Json)
    (measure : JSON.Json → Option Page.Measure := fun _ => none) (canvas : PageCanvas.Env := {}) :
    M (Held × Except String String) := do
  let held := setReads held canvas (measure held.layoutRequest)
  let full := request.field? "full" == some (.bool true)
  match action with
  | "load" =>
    match Rendering.SfntProfile.decodeBase64 (str request "moduleBase64") with
    | some bytes => return loadModule held bytes
    | none => return (held, .error "scriptSession: moduleBase64 is not Base64")
  | "aotModule" => return (held, .error "scriptSession: aotModule answers bytes (web_document_call_bin)")
  | "resume" =>
    match held.turn with
    | some t =>
      if natField request "session" != some t.id then return (held, .error "scriptSession: not the current session")
      resumeTurn { held with turn := none } t ((request.field? "reply").getD .null)
    | none => return (held, .error "scriptSession: no turn waits for the host")
  | "host" =>
    match held.turn, held.aot with
    | some t, some aot => hostCall held aot t request
    | _, _ => return (held, .error "scriptSession: no turn waits for the host")
  | "webdriverStart" =>
    -- A WebDriver endpoint: remote control of the browser (`WebDriver.Gate`). Only the test
    -- runner sends `dangerouslyEnable`, and only with its `--dangerously-enable-webdriver-endpoint`;
    -- this is the one acceptance of `Risk.webdriverEndpoint` (skills/lean-risk-flags §5).
    -- `Gate.start` refuses without it, off loopback, or with no entropy.
    let enabled : Option (Risk.Accepted .webdriverEndpoint) :=
      if request.field? "dangerouslyEnable" == some (.bool true) then some (Risk.dangerouslyAccept .webdriverEndpoint) else none
    let entropy ← turnBytes
    let launch : WebDriver.Gate.Launch := { enabled, address := str request "address", entropy }
    match WebDriver.Gate.start launch, natField request "port" with
    | .ok secret, some port =>
      let browser : WebDriver.Protocol.Browser := { platform := (match str request "platform" with | "" => "linux" | p => p) }
      return ({ held with webdriver := some ({ secret, port }, {}, browser, {}, {}) },
        .ok (JSON.Json.object [("secret", .string secret)]).toString)
    | .ok _, none => return (held, .error "scriptSession: webdriverStart needs a port")
    | .error r, _ => return (held, .error s!"scriptSession: the WebDriver endpoint is refused ({repr r})")
  | "webdriver" =>
    -- one request of the endpoint's listener: the gate, then the protocol (`Protocol.handle`)
    match held.webdriver with
    | none => return (held, .error "scriptSession: no WebDriver endpoint")
    | some (cfg, srv, browser, window, doc) =>
      let origin : Option String := match request.field? "origin" with
        | some (.string o) => some o
        | _ => none
      let entropy ← turnBytes
      let r : WebDriver.Protocol.Request := { method := str request "method", path := str request "path", host := str request "host", body := str request "body", entropy, origin }
      let (srv, out) := WebDriver.Protocol.handle cfg browser srv r
      let reply := fun (status : Nat) (body : JSON.Json) =>
        (JSON.Json.object [("status", .number (toString status)), ("body", .string body.toString)]).toString
      let held := { held with webdriver := some (cfg, srv, browser, window, doc) }
      match out with
      | .reply status body => return (held, .ok (reply status body))
      | .page command params body _ =>
        let answer : Held → Except WebDriver.Error JSON.Json → Held × Except String String := fun held result =>
          match result with
          | .ok v => (held, .ok (reply 200 (WebDriver.successBody v)))
          | .error e => (held, .ok (reply e.code.status e.body))
        -- the window's own commands (`WebDriver.Window`), then the page's (`WebDriver.Page`)
        match WebDriver.Window.answer window command body with
        | some (window, result) => return answer { held with webdriver := some (cfg, srv, browser, window, doc) } result
        | none =>
          match WebDriver.Page.step doc.url command params body with
          | .reply result => return answer held result
          | .navigate url =>
            -- the host loads the URL as the session's page (`start`), then gives this answer
            let doc := doc.navigate url
            return ({ held with webdriver := some (cfg, srv, browser, window, doc) },
              .ok (JSON.Json.object [("status", .number "200"), ("body", .string (WebDriver.successBody .null).toString),
                ("navigate", .string url)]).toString)
          | .call fn args finish =>
            match WebDriver.Page.toWire doc.refPrefix 64 args, held.leanSession with
            | .error e, _ => return answer held (.error e)
            | .ok _, none => return answer held (.error { code := .noSuchWindow, message := "no page is loaded" })
            | .ok wire, some (id, s, marks) =>
              -- the page's glue runs the function (`webdriverCall`), then the microtasks it queued
              let (s, v) := s.api? "webdriverCall" #[.str fn, .str wire.toString]
              let s := s.runJobs
              let text := match v with
                | .str t => t
                | _ => "{\"error\":\"unknown error\",\"message\":\"the page gave no answer\"}"
              let result := match JSON.parseJson text with
                | .ok j => WebDriver.Page.finish doc.refPrefix window.handle finish j
                | .error _ => .error { code := .unknownError, message := "the page's answer is not JSON" }
              return answer { held with leanSession := some (id, s, marks) } result
  | "close" => return ({ held with session := none, turn := none, leanSession := none, leanWorkers := {}, frames := #[], leanFrames := #[], frameScan := 0 }, .ok "{\"closed\":true}")
  | _ =>
  if held.turn.isSome then return (held, .error "scriptSession: a turn waits for the host")
  match action with
  | "start" =>
    if str request "engine" == "bubblepop" then startLean held html request measure canvas else
    match held.module, held.aot with
    | none, some aot =>
      -- The AOT path: Lean asks the host for a fresh instance, then runs the program.
      let url := str request "url"
      let commands := min 1048576 ((natField request "commandLimit").getD L4Factoidal.WasmVM.Hosts.Dom.maxCommands)
      let logs := min 1048576 ((natField request "logLimit").getD 1024)
      let made := show Except String (Array (Nat × String) × Array String × DOM.Dom) from do
        let dom ← parse html url
        let (scripts, missing, _) ← scriptSources dom request
        return (scripts, missing, dom)
      match made with
      | .error e => return (held, .error s!"scriptSession: {e}")
      | .ok (scripts, missing, dom) =>
        let (vw, vh) := (viewport request).getD (800, 600)
        let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh, canvasEnv := canvas }
        let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
        let prog := PageAot.startProg aot dom url scripts { commands, logs, gpuPage := held.nextSession, entropy := ← entropy held.nextSession, encoding := str request "encoding", network := request.field? "network" == some (.bool true), hostCors := request.field? "hostCors" == some (.bool true), pageAddress := str request "pageAddress" } #[] missing
          reads { instructionsPerMs := rate }
        let id := held.nextSession
        beginTurn { held with session := none, leanSession := none, nextSession := id + 1, layoutRequest := layoutOf request } id {} {} true true prog
    | none, none => return (held, .error "scriptSession: no guest module; load it first")
    | some m, _ =>
      let url := str request "url"
      let commands := min 1048576 ((natField request "commandLimit").getD L4Factoidal.WasmVM.Hosts.Dom.maxCommands)
      let logs := min 1048576 ((natField request "logLimit").getD 1024)
      let ent ← entropy held.nextSession
      let started ← WebWasm.timed fun _ => show Except String Page.Session from do
        let dom ← parse html url
        let (scripts, missing, _) ← scriptSources dom request
        let (vw, vh) := (viewport request).getD (800, 600)
        let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh, canvasEnv := canvas }
        let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
        let hostLoads := request.field? "navigations" == some (.bool true)
        let s ← Page.start m dom url scripts { commands, logs, gpuPage := held.nextSession, entropy := ent, encoding := str request "encoding", network := request.field? "network" == some (.bool true), hostCors := request.field? "hostCors" == some (.bool true), pageAddress := str request "pageAddress", syncOk := true, syncAnswers := held.syncCache, frames := true, hostLoads, mayBlock := request.field? "network" == some (.bool true) && mentionsXhr scripts } #[] reads { instructionsPerMs := rate }
        return missing.foldl Page.Session.fail s
      match started with
      | (.error e, _) => return (held, .error s!"scriptSession: {e}")
      | (.ok s, ns) =>
        let id := held.nextSession
        match s.host.web.net.syncWanted with
        | some w => return ({ held with pendingSync := some ("start", html, request) }, netSyncAnswer id w)
        | none =>
        let held := { held with syncCache := #[], pendingSync := none }
        let (s, loads) := srcdocLoads (·.host) (fun s el src scripts => s.loadFrame el src scripts) s
        let fEnt ← frameEntropyIf id s.limits.entropy s.host.dom.dom 0
        let (s, frames, scan) := pumpFrames (pageFrameOps m s.limits fEnt) s #[] 0
        let (answer, marks) := turnAnswer id {} s {} true ns (frameFields s.host loads ++ netFields s.host)
        let s := drained s
        return ({ held with session := some (id, s, marks), leanSession := none, nextSession := id + 1, layoutRequest := layoutOf request, frames, leanFrames := #[], frameScan := scan }, .ok answer)
  | _ =>
    match held.leanSession with
    | some (id, s, marks) =>
      if natField request "session" == some id then actLean { held with leanSession := none } action request id s marks
      else return (held, .error "scriptSession: not the current session")
    | none =>
    match held.session with
    | none => return (held, .error "scriptSession: no session")
    | some (id, s, marks) =>
      if natField request "session" != some id then return (held, .error "scriptSession: not the current session")
      let held := { held with session := none }
      let before := Before.of s
      -- One program for both machines: the interpreter runs it here, the host's engine
      -- runs it ask by ask on the AOT path.
      let run := fun (f : Page.Session → Page.Prog Page.Session) =>
        if held.aot.isSome && held.module.isNone then
          beginTurn held id before marks full false (Except.ok <$> f s)
        else do
          let keepIt := s.host.web.net.xhrs.size > 0 || s.host.web.net.mayBlock
          let snap : Option Page.Session := if keepIt then some s else none
          let s0 : Page.Session := { s with host := { s.host with web := setSync s.host.web keepIt held.syncCache } }
          let (s', ns) ← WebWasm.timed fun _ => (f s0).runLocal
          match s'.host.web.net.syncWanted, snap with
          | some w, some old => return ({ held with session := some (id, old, marks), pendingSync := some (action, "", request) }, netSyncAnswer id w)
          | _, _ =>
          let (s', loads) := srcdocLoads (·.host) (fun s el src scripts => s.loadFrame el src scripts) s'
          let (s', frames, scan) ← match held.module with
            | some m => do
              let fEnt ← frameEntropyIf id s'.limits.entropy s'.host.dom.dom held.frameScan
              pure (pumpFrames (pageFrameOps m s'.limits fEnt) s' held.frames held.frameScan)
            | none => pure (s', held.frames, held.frameScan)
          let (answer, marks) := turnAnswer id before s' marks full ns (frameFields s'.host loads ++ netFields s'.host)
          return ({ held with session := some (id, drained s', marks), frames, frameScan := scan, syncCache := #[], pendingSync := none }, Except.ok answer)
      match action with
      | "click" =>
        match natField request "node" with
        | some node => run (·.clickP node)
        | none => return ({ held with session := some (id, s, marks) }, .error "scriptSession: click needs node")
      | "pointer" =>
        match pointerKind (str request "kind"), natField request "node" with
        | some kind, some node => run (·.pointerP kind node (pointerInit request))
        | _, _ => return ({ held with session := some (id, s, marks) }, .error "scriptSession: pointer needs kind (down, move, up, cancel) and node")
      | "resize" =>
        match viewport request with
        | some (w, h) => run fun s => do
            let s ← s.resizeP w h
            return (← s.advanceP s.loop.clock).1
        | none => return ({ held with session := some (id, s, marks) }, .error "scriptSession: resize needs width and height")
      | "advance" => run fun s => do
          let (s, _) ← s.advanceP (s.loop.clock + ((natField request "ms").getD 0))
          s.flushMoveP
      | "settle" => run fun s => do
          let s ← s.flushMoveP
          return (← s.settleP ((natField request "budgetMs").getD 30000)).1
      | "turn" => run fun s => do
          let s ← s.flushMoveP
          return (← s.advanceP s.loop.clock).1
      | "frame" =>
        match natField request "node", frameDocument request with
        | some node, .ok (src, xml, scripts, enc) =>
          run fun s => ({ s with host := { s.host with dom := s.host.dom.noteFrameEncoding node enc } } : Page.Session).loadFrameP node src scripts xml
            (if (str request "responseUrl").isEmpty then none else some (str request "responseUrl"))
        | _, .error e => return ({ held with session := some (id, s, marks) }, .error s!"scriptSession: frame: {e}")
        | none, _ => return ({ held with session := some (id, s, marks) }, .error "scriptSession: frame needs node")
      | "net" => run fun s => do
          let ms := (natField request "elapsedMs").getD 0
          let (s, _) ← if ms == 0 then pure (s, true) else s.advanceP (s.loop.clock + ms)
          let s : Page.Session := { s with host := netGive s.host request }
          return (← s.advanceP s.loop.clock).1
      | "gpuRead" => run fun s => do
          let s : Page.Session := { s with host := gpuGive s.host request }
          return (← s.advanceP s.loop.clock).1
      | _ => return ({ held with session := some (id, s, marks) }, .error "scriptSession: unknown action")

/-- The `scriptSession` operation. `html` is the page, for `start`. -/
def op {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (name html : String) (request : JSON.Json)
    (measure : JSON.Json → Option Page.Measure := fun _ => none)
    (canvas : Unit → PageCanvas.Env := fun _ => {}) : M (Held × Except String (Option String)) := do
  if name != "scriptSession" then return (held, .ok none)
  let action := str request "action"
  if !actions.contains action then return (held, .error "scriptSession: unknown action")
  if action == "info" then
    let (loaded, bytes, aot) := (held.module.isSome || held.aot.isSome, held.moduleBytes, held.aot.isSome)
    return (held, .ok <| some (JSON.Json.object [("ops",.array (actions.map .string)),("module",.bool loaded),
      ("bytes",num bytes),("engine",.string "QuickJS-NG in WasmVM"),("aot",.bool true),("aotLoaded",.bool aot),
      ("engines",.array [.string "quickjs", .string "bubblepop"])]).toString)
  let (held, action, html, request) :=
    if action == "syncAnswer" then
      match held.pendingSync with
      | some (a, h, r) =>
        let answer := (request.field? "answer").map (fun x => (netAnswer x).2)
        ({ held with syncCache := held.syncCache.push (answer.getD {}), pendingSync := none }, a, h, r)
      | none => (held, action, html, request)
    else (held, action, html, request)
  let (held, answer) ← act held action html request measure (canvas ())
  return (held, answer.map (some ∘ withNext held.nextSession))

/-- The ops that answer bytes (`web_document_call_bin`): `aotModule`, the host module of
the guest loaded with `guest:quickjs-aot`, as section 0, with `moduleHead` as the head.
Every other request is `op`'s, with no section. -/
def opSections {M : Type → Type} [Monad M] [WebWasm.Machine M] (held : Held) (name html : String) (request : JSON.Json)
    (measure : JSON.Json → Option Page.Measure := fun _ => none)
    (canvas : Unit → PageCanvas.Env := fun _ => {}) : M (Held × Except String (Option (String × Array ByteArray))) := do
  if name == "scriptSession" && str request "action" == "aotModule" then
    let answer := match held.aot with
      | some p => Except.ok ((moduleHead p).toString, #[p.bytes])
      | none => .error "scriptSession: no guest module for AOT; load it with guest:quickjs-aot"
    return (held, answer.map fun (h, b) => some (withNext held.nextSession h, b))
  let (held, answer) ← op held name html request measure canvas
  return (held, answer.map (·.map (·, #[])))

end WebScripts
