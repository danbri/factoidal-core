import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.WasmVM.Hosts.PageAot
import L4Factoidal.WasmVM.Hosts.LeanJSRealm
import L4Factoidal.DOM.OfXml
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
- `resize` (`width`, `height`): the viewport in CSS pixels; `resize` at the window.

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
  /-- Key bytes handed to `WebHacl.wipe` when sessions ended (`dropSessions`). -/
  keyBytesWiped : Nat := 0

instance : Inhabited Held := ⟨{}⟩

/-- End the held sessions: their CryptoKeys' bytes are wiped (`WebApi.wipeAll`; the
sessions are taken out of `held` first, so the stores hold the last references). -/
def dropSessions (held : Held) : Held :=
  let ps := held.session
  let ls := held.leanSession
  let held := { held with session := none, leanSession := none }
  let n := (match ps with | some (_, s, _) => Hosts.WebApi.wipeAll s.host.web | none => 0) +
    (match ls with
     | some (_, s, _) => match s.heap.host with | some h => Hosts.WebApi.wipeAll h.page.web | none => 0
     | none => 0)
  { held with keyBytesWiped := held.keyBytesWiped + n }

initialize heldRef : IO.Ref Held ← IO.mkRef {}

private unsafe def takeImpl (_ : JSON.Json) : Held :=
  unsafeBaseIO (heldRef.modifyGet fun h => (h, {}))
private unsafe def keepImpl (h : Held) (_ : JSON.Json) : Nat :=
  unsafeBaseIO (do let n := h.nextSession; heldRef.set h; return n)
private unsafe def peekImpl (_ : JSON.Json) : Bool × Nat × Bool :=
  unsafeBaseIO (do let h ← heldRef.get; return (h.module.isSome || h.aot.isSome, h.moduleBytes, h.aot.isSome))
/-- These take, keep and read what the engine holds. The request argument keeps each
call in place; `keep` answers a number that the caller puts in its answer, so the call
stays. -/
@[implemented_by takeImpl, noinline] private opaque take (request : JSON.Json) : Held
@[implemented_by keepImpl, noinline] private opaque keep (h : Held) (request : JSON.Json) : Nat
@[implemented_by peekImpl, noinline] private opaque peek (request : JSON.Json) : Bool × Nat × Bool

/-- Entropy for session `id`'s `crypto.getRandomValues` (`Hosts.WebApi`): 32 bytes of the
host's own generator, `IO.getRandomBytes` (the operating system's natively; the browser's
`crypto.getRandomValues` under Emscripten), then the session number. Empty when the host
has none: the page then has no `getRandomValues`. -/
private unsafe def entropyImpl (id : Nat) : ByteArray :=
  unsafeBaseIO (do
    match ← (IO.getRandomBytes 32).toBaseIO with
    | .ok b => return b ++ (toString id).toUTF8
    | .error _ => return ByteArray.empty)
@[implemented_by entropyImpl, noinline] private opaque entropy (id : Nat) : ByteArray

/-- Key bytes zeroed in place so far in this process (`WebHacl.wipedSoFar`, the C
counter): the close answer reports it, so a test can see that wiping happened. -/
private unsafe def zeroedImpl (_ : Nat) : Nat := unsafeBaseIO Crypto.WebHacl.wipedSoFar
@[implemented_by zeroedImpl, noinline] private opaque zeroedSoFar (n : Nat) : Nat

def actions : List String := ["info", "load", "start", "click", "pointer", "resize", "advance", "settle", "turn", "close",
  "aotModule", "resume", "host"]

/-- An answer object with `nextSession` first: the value `keep` answered, so the
compiled code keeps the call. -/
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
def loadModuleBytes (family : String) (bytes : ByteArray) (request : JSON.Json) : Except String String :=
  let held := take request
  let (held, r) := if family == "guest:quickjs-aot" then loadAot held bytes else loadModule { held with aot := none } bytes
  let n := keep held request
  r.map (withNext n)

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
    nextFrame := s.nextFrame, moveWake := s.moveWake, quiet := s.quiet }

def View.ofLean (s : LeanJS.Session) : View :=
  let e := LeanJS.engine
  { host := s.host, steps := s.steps, jobs := s.jobs, tasks := s.tasks, errors := s.errors,
    nextFrame := e.nextFrame s, moveWake := e.moveWake s, quiet := e.quiet s }

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

/-- The session after a turn answer: the GPU commands it carried are the host's now. -/
def drained (s : Page.Session) : Page.Session :=
  { s with host := { s.host with dom := { s.host.dom with gpuOut := #[], canvas := s.host.dom.canvas.sent } } }

def drainedLean (s : LeanJS.Session) : LeanJS.Session :=
  if s.host.dom.gpuOut.isEmpty && s.host.dom.canvas.drawn.isEmpty then s else
  let h := s.host
  s.setHost { h with dom := { h.dom with gpuOut := #[], canvas := h.dom.canvas.sent } }

/-- What Canvas 2D draws with, given anew before each action (fonts and images the engine
holds may have changed since the page started). -/
def setCanvas (held : Held) (env : PageCanvas.Env) : Held :=
  let page := fun (h : Page.Host) => { h with reads := { h.reads with canvasEnv := env } }
  { held with
    session := held.session.map fun (id, s, m) => (id, { s with host := page s.host }, m),
    leanSession := held.leanSession.map fun (id, s, m) => (id, s.setHost (page s.host), m) }

/-- The page's arena, parsed as `WebDocument.prepareDOM` parses it, so node numbers agree
with a render's replay of the commands. -/
def parse (html url : String) : Except String DOM.Dom :=
  if html.utf8ByteSize > 1048576 then .error "document HTML exceeds 1MiB"
  else if DOM.isXhtmlPath url then DOM.parseXmlDocument html
  else .ok (DOM.parseHtmlDocument html)

/-- The classic scripts in document order, with the sources a host supplied for `src`
scripts. A `src` script with no source is skipped and reported. -/
def scriptSources (dom : DOM.Dom) (request : JSON.Json) : Except String (Array (Nat × String) × Array String) := do
  let resources := match request.field? "resources" with | some (.array rs) => rs | _ => []
  if resources.length > 64 then throw "scriptSession: more than 64 script resources"
  let mut out := #[]
  let mut missing := #[]
  for r in WebRenderScript.scriptRecords dom do
    let kind := str r "kind"
    let some id := natField r "nodeId" | throw "scriptSession: script nodeId"
    if kind == "module" then missing := missing.push s!"module script {id} is not run"
    if kind != "classic" then continue
    let src := str r "src"
    if src.isEmpty then out := out.push (id, str r "source")
    else
      match resources.find? (fun x => natField x "nodeId" == some id) with
      | some x =>
        let source := str x "source"
        if source.utf8ByteSize > 4194304 then throw "scriptSession: a script exceeds 4 MiB"
        out := out.push (id, source)
      | none => missing := missing.push s!"script {src} was not supplied"
  return (out, missing)

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

/-- The page's viewport in CSS pixels: the window's `width`, and its `height` less the
full chrome of `shell` (the rows that a render lays the page out in,
`WebDocument.layoutTop`). -/
def viewport (request : JSON.Json) : Option (Nat × Nat) := do
  let w ← natField request "width"
  let h ← natField request "height"
  let top := match request.field? "shell" with
    | some j => WebShell.fullHeight (WebShell.Shell.ofJson j) w
    | none => 0
  return (w, max 1 (h - top))

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
def beginTurn (held : Held) (id : Nat) (before : Before) (marks : Marks) (full : Bool) (fresh : Bool)
    (prog : Page.Prog Result) : Held × Except String String :=
  let t : Turn := { id, before, marks, full, ns := 0, stage := .fresh prog, memSize := held.memSize }
  if fresh then answerTurn held t none 0 else
  let ((t, r), ns) := WebWasm.timed fun _ => stepTurn t (PageAot.Prog.next prog)
  answerTurn held t r ns

/-- The host's reply to the ask the turn waits on. -/
def resumeTurn (held : Held) (t : Turn) (reply : JSON.Json) : Held × Except String String :=
  let memSize := (natField reply "memSize").getD t.memSize
  let t := { t with memSize }
  let fail := fun (e : String) => answerTurn held t (some (.error e)) 0
  match t.stage with
  | .fresh prog =>
    if let some (.string e) := reply.field? "error" then fail s!"host instance: {e}" else
    let ((t, r), ns) := WebWasm.timed fun _ => stepTurn t (PageAot.Prog.next prog)
    answerTurn held t r ns
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
    | .error e => fail e
    | .ok (p, r) =>
      let ((t, r), ns) := WebWasm.timed fun _ => stepTurn t (p.resume r)
      answerTurn held t r ns

/-- One import call of the guest, passed back by the host while it runs an export. -/
def hostCall (held : Held) (aot : PageAot.Prepared) (t : Turn) (request : JSON.Json) : Held × Except String String :=
  match t.stage with
  | .fresh _ => (held, .error "scriptSession: no run waits for a host call")
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
      (held, .ok (JSON.Json.object [("trap",.string s!"aot: wrong arguments for import {id}")]).toString) else
    let fuelLeft := ((request.field? "fuel").bind intOf?).getD (Int.ofNat p.session.limits.fuel)
    let ((p, r, writes), ns) := WebWasm.timed fun _ => PageAot.serveHost p id vals.toArray memSize segs fuelLeft
    let t := { t with stage := .paused p, memSize, ns := t.ns + ns }
    let answer := match r with
      | .values vs => JSON.Json.object [("results",.array (vs.toList.map valueJson)),("writes",writesJson writes)]
      | .trap m => .object [("trap",.string m)]
      | .exit n => .object [("exit",num n)]
    ({ held with turn := some t }, .ok answer.toString)

/-! ## BubblePopJS, the engine written in Lean -/

/-- The answer of a turn of the Lean engine; the session is kept. -/
def leanTurn (held : Held) (id : Nat) (before : Before) (s : LeanJS.Session) (marks : Marks) (full : Bool) (ns : Nat) :
    Held × Except String String :=
  let (answer, marks) := turnAnswerOf id before (View.ofLean s) marks full ns [("engine",.string "bubblepop")]
  ({ held with leanSession := some (id, drainedLean s, marks) }, .ok answer)

/-- `start` on the Lean engine: its realm is made at the first page (the prelude runs
once), and each page starts from it with its own arena. -/
def startLean (held : Held) (html : String) (request : JSON.Json) (measure : JSON.Json → Option Page.Measure)
    (canvas : PageCanvas.Env := {}) : Held × Except String String :=
  let url := str request "url"
  let commands := min 1048576 ((natField request "commandLimit").getD 4096)
  let logs := min 1048576 ((natField request "logLimit").getD 1024)
  let id := held.nextSession
  let lim : Page.Limits := { commands, logs, gpuPage := id, entropy := entropy id, encoding := str request "encoding" }
  let made := show Except String (Array (Nat × String) × Array String × DOM.Dom) from do
    let dom ← parse html url
    let (scripts, missing) ← scriptSources dom request
    return (scripts, missing, dom)
  match made with
  | .error e => (held, .error s!"scriptSession: {e}")
  | .ok (scripts, missing, dom) =>
    let (base, ns0) := WebWasm.timed fun _ => match held.leanBase with
      | some b => Except.ok b
      | none => LeanJS.prepare
    match base with
    | .error e => (held, .error s!"scriptSession: BubblePopJS: {e}")
    | .ok base =>
      let (vw, vh) := (viewport request).getD (800, 600)
      let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh, canvasEnv := canvas }
      let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
      let (s, ns) := WebWasm.timed fun _ =>
        let s := LeanJS.start base dom url scripts lim reads { instructionsPerMs := rate }
        missing.foldl LeanJS.Session.fail s
      leanTurn { held with leanBase := some base, session := none, leanSession := none, nextSession := id + 1 }
        id {} s {} true (ns0 + ns)

/-- A later action on the Lean engine's session (the actions of `act`). -/
def actLean (held : Held) (action : String) (request : JSON.Json) (id : Nat) (s : LeanJS.Session) (marks : Marks) :
    Held × Except String String :=
  let full := request.field? "full" == some (.bool true)
  let e := LeanJS.engine
  let before := Before.ofLean s
  let run := fun (f : LeanJS.Session → LeanJS.Session) =>
    let (s', ns) := WebWasm.timed fun _ => f s
    leanTurn held id before s' marks full ns
  let keep := fun (msg : String) => ({ held with leanSession := some (id, s, marks) }, Except.error msg)
  match action with
  | "click" =>
    match natField request "node" with
    | some node => run (e.click · node)
    | none => keep "scriptSession: click needs node"
  | "pointer" =>
    match pointerKind (str request "kind"), natField request "node" with
    | some kind, some node => run (e.pointer · kind node (pointerInit request))
    | _, _ => keep "scriptSession: pointer needs kind (down, move, up, cancel) and node"
  | "resize" =>
    match viewport request with
    | some (w, h) => run fun s => let s := e.resize s w h; (e.advance s (e.loop s).clock).1
    | none => keep "scriptSession: resize needs width and height"
  | "advance" => run fun s => e.flushMove (e.advance s ((e.loop s).clock + ((natField request "ms").getD 0))).1
  | "settle" => run fun s => (e.settle (e.flushMove s) ((natField request "budgetMs").getD 30000)).1
  | "turn" => run fun s => let s := e.flushMove s; (e.advance s (e.loop s).clock).1
  | _ => keep "scriptSession: unknown action"

/-- One action on what the engine holds. `measure` lays out an arena for the layout reads
of its scripts (`WebDocument.measure`), with the `layout` request of `start`. -/
def act (held : Held) (action html : String) (request : JSON.Json)
    (measure : JSON.Json → Option Page.Measure := fun _ => none) (canvas : PageCanvas.Env := {}) :
    Held × Except String String :=
  let held := setCanvas held canvas
  let full := request.field? "full" == some (.bool true)
  match action with
  | "load" =>
    match Rendering.SfntProfile.decodeBase64 (str request "moduleBase64") with
    | some bytes => loadModule held bytes
    | none => (held, .error "scriptSession: moduleBase64 is not Base64")
  | "aotModule" => (held, .error "scriptSession: aotModule answers bytes (web_document_call_bin)")
  | "resume" =>
    match held.turn with
    | some t =>
      if natField request "session" != some t.id then (held, .error "scriptSession: not the current session") else
      resumeTurn { held with turn := none } t ((request.field? "reply").getD .null)
    | none => (held, .error "scriptSession: no turn waits for the host")
  | "host" =>
    match held.turn, held.aot with
    | some t, some aot => hostCall held aot t request
    | _, _ => (held, .error "scriptSession: no turn waits for the host")
  | "close" =>
    let held := dropSessions { held with turn := none }
    (held, .ok s!"\{\"closed\":true,\"keyBytesWiped\":{held.keyBytesWiped},\"keyBytesZeroed\":{zeroedSoFar held.keyBytesWiped}}")
  | _ =>
  if held.turn.isSome then (held, .error "scriptSession: a turn waits for the host") else
  match action with
  | "start" =>
    let held := dropSessions held
    if str request "engine" == "bubblepop" then startLean held html request measure canvas else
    match held.module, held.aot with
    | none, some aot =>
      -- The AOT path: Lean asks the host for a fresh instance, then runs the program.
      let url := str request "url"
      let commands := min 1048576 ((natField request "commandLimit").getD 4096)
      let logs := min 1048576 ((natField request "logLimit").getD 1024)
      let made := show Except String (Array (Nat × String) × Array String × DOM.Dom) from do
        let dom ← parse html url
        let (scripts, missing) ← scriptSources dom request
        return (scripts, missing, dom)
      match made with
      | .error e => (held, .error s!"scriptSession: {e}")
      | .ok (scripts, missing, dom) =>
        let (vw, vh) := (viewport request).getD (800, 600)
        let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh, canvasEnv := canvas }
        let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
        let prog := PageAot.startProg aot dom url scripts { commands, logs, gpuPage := held.nextSession, entropy := entropy held.nextSession, encoding := str request "encoding" } #[] missing
          reads { instructionsPerMs := rate }
        let id := held.nextSession
        beginTurn { held with session := none, leanSession := none, nextSession := id + 1 } id {} {} true true prog
    | none, none => (held, .error "scriptSession: no guest module; load it first")
    | some m, _ =>
      let url := str request "url"
      let commands := min 1048576 ((natField request "commandLimit").getD 4096)
      let logs := min 1048576 ((natField request "logLimit").getD 1024)
      let started := WebWasm.timed fun _ => show Except String Page.Session from do
        let dom ← parse html url
        let (scripts, missing) ← scriptSources dom request
        let (vw, vh) := (viewport request).getD (800, 600)
        let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh, canvasEnv := canvas }
        let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
        let s ← Page.start m dom url scripts { commands, logs, gpuPage := held.nextSession, entropy := entropy held.nextSession, encoding := str request "encoding" } #[] reads { instructionsPerMs := rate }
        return missing.foldl Page.Session.fail s
      match started with
      | (.error e, _) => (held, .error s!"scriptSession: {e}")
      | (.ok s, ns) =>
        let id := held.nextSession
        let (answer, marks) := turnAnswer id {} s {} true ns
        let s := drained s
        ({ held with session := some (id, s, marks), leanSession := none, nextSession := id + 1 }, .ok answer)
  | _ =>
    match held.leanSession with
    | some (id, s, marks) =>
      if natField request "session" == some id then actLean { held with leanSession := none } action request id s marks
      else (held, .error "scriptSession: not the current session")
    | none =>
    match held.session with
    | none => (held, .error "scriptSession: no session")
    | some (id, s, marks) =>
      if natField request "session" != some id then (held, .error "scriptSession: not the current session") else
      let held := { held with session := none }
      let before := Before.of s
      -- One program for both machines: the interpreter runs it here, the host's engine
      -- runs it ask by ask on the AOT path.
      let run := fun (f : Page.Session → Page.Prog Page.Session) =>
        if held.aot.isSome && held.module.isNone then
          beginTurn held id before marks full false (Except.ok <$> f s)
        else
          let (s', ns) := WebWasm.timed fun _ => (f s).runLocal
          let (answer, marks) := turnAnswer id before s' marks full ns
          ({ held with session := some (id, drained s', marks) }, Except.ok answer)
      match action with
      | "click" =>
        match natField request "node" with
        | some node => run (·.clickP node)
        | none => ({ held with session := some (id, s, marks) }, .error "scriptSession: click needs node")
      | "pointer" =>
        match pointerKind (str request "kind"), natField request "node" with
        | some kind, some node => run (·.pointerP kind node (pointerInit request))
        | _, _ => ({ held with session := some (id, s, marks) }, .error "scriptSession: pointer needs kind (down, move, up, cancel) and node")
      | "resize" =>
        match viewport request with
        | some (w, h) => run fun s => do
            let s ← s.resizeP w h
            return (← s.advanceP s.loop.clock).1
        | none => ({ held with session := some (id, s, marks) }, .error "scriptSession: resize needs width and height")
      | "advance" => run fun s => do
          let (s, _) ← s.advanceP (s.loop.clock + ((natField request "ms").getD 0))
          s.flushMoveP
      | "settle" => run fun s => do
          let s ← s.flushMoveP
          return (← s.settleP ((natField request "budgetMs").getD 30000)).1
      | "turn" => run fun s => do
          let s ← s.flushMoveP
          return (← s.advanceP s.loop.clock).1
      | _ => ({ held with session := some (id, s, marks) }, .error "scriptSession: unknown action")

/-- The `scriptSession` operation. `html` is the page, for `start`. -/
def op (name html : String) (request : JSON.Json) (measure : JSON.Json → Option Page.Measure := fun _ => none)
    (canvas : Unit → PageCanvas.Env := fun _ => {}) : Except String (Option String) := do
  if name != "scriptSession" then return none
  let action := str request "action"
  if !actions.contains action then throw "scriptSession: unknown action"
  if action == "info" then
    let (loaded, bytes, aot) := peek request
    return some (JSON.Json.object [("ops",.array (actions.map .string)),("module",.bool loaded),
      ("bytes",num bytes),("engine",.string "QuickJS-NG in WasmVM"),("aot",.bool true),("aotLoaded",.bool aot),
      ("engines",.array [.string "quickjs", .string "bubblepop"])]).toString
  let (held, answer) := act (take request) action html request measure (canvas ())
  let n := keep held request
  return some (← answer.map (withNext n))

/-- The ops that answer bytes (`web_document_call_bin`): `aotModule`, the host module of
the guest loaded with `guest:quickjs-aot`, as section 0, with `moduleHead` as the head.
Every other request is `op`'s, with no section. -/
def opSections (name html : String) (request : JSON.Json) (measure : JSON.Json → Option Page.Measure := fun _ => none)
    (canvas : Unit → PageCanvas.Env := fun _ => {}) : Except String (Option (String × Array ByteArray)) := do
  if name == "scriptSession" && str request "action" == "aotModule" then
    let held := take request
    let answer := match held.aot with
      | some p => Except.ok ((moduleHead p).toString, #[p.bytes])
      | none => .error "scriptSession: no guest module for AOT; load it with guest:quickjs-aot"
    let n := keep held request
    return some (← answer.map fun (h, b) => (withNext n h, b))
  return (← op name html request measure canvas).map (·, #[])

end WebScripts
