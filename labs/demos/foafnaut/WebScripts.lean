import L4Factoidal.WasmVM.Hosts.Page
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

/-- What the engine holds between calls: the prepared module and one session. -/
structure Held where
  module : Option Page.Module' := none
  moduleBytes : Nat := 0
  session : Option (Nat × Page.Session × Marks) := none
  nextSession : Nat := 1

instance : Inhabited Held := ⟨{}⟩

initialize heldRef : IO.Ref Held ← IO.mkRef {}

private unsafe def takeImpl (_ : JSON.Json) : Held :=
  unsafeBaseIO (heldRef.modifyGet fun h => (h, {}))
private unsafe def keepImpl (h : Held) (_ : JSON.Json) : Nat :=
  unsafeBaseIO (do let n := h.nextSession; heldRef.set h; return n)
private unsafe def peekImpl (_ : JSON.Json) : Bool × Nat :=
  unsafeBaseIO (do let h ← heldRef.get; return (h.module.isSome, h.moduleBytes))
/-- These take, keep and read what the engine holds. The request argument keeps each
call in place; `keep` answers a number that the caller puts in its answer, so the call
stays. -/
@[implemented_by takeImpl, noinline] private opaque take (request : JSON.Json) : Held
@[implemented_by keepImpl, noinline] private opaque keep (h : Held) (request : JSON.Json) : Nat
@[implemented_by peekImpl, noinline] private opaque peek (request : JSON.Json) : Bool × Nat

def actions : List String := ["info", "load", "start", "click", "pointer", "resize", "advance", "settle", "turn", "close"]

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

/-- The guest module as bytes, from `fontLoadBin` with the family `guest:quickjs`. -/
def loadModuleBytes (bytes : ByteArray) (request : JSON.Json) : Except String String :=
  let (held, r) := loadModule (take request) bytes
  let n := keep held request
  r.map (withNext n)

def commandsJson (s : Page.Session) : JSON.Json :=
  .array (s.commands.toList.map WebRenderScript.commandJson)

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

/-- The answer of a turn. -/
def turnAnswer (id : Nat) (before : Before) (s : Page.Session) (marks : Marks) (full : Bool) (ns : Nat)
    (extra : List (String × JSON.Json) := []) : String × Marks :=
  let changed := s.changes != before.changes
  let loop := s.loop
  let fields : List (String × JSON.Json) := [
    ("session",num id),("clock",num loop.clock),("changed",.bool changed),
    ("commandCount",num s.commands.size),("changes",num s.changes)] ++
    (if changed || full then [("commands",commandsJson s)] else []) ++ [
    ("logs",.array ((s.logs.extract marks.logs s.logs.size).toList.map .string)),
    ("errors",.array ((s.errors.extract marks.errors s.errors.size).toList.map .string)),
    ("timers",num loop.timers.length),
    ("nextTimer",match loop.timers with | t :: _ => num t.due | [] => .null),
    ("frames",num loop.frames.length),
    ("nextWake",match [loop.timers.head?.map (·.due), s.nextFrame, s.moveWake].filterMap (fun x => x) with
      | [] => .null
      | t :: ts => num (ts.foldl min t)),
    ("quiet",.bool s.quiet),
    ("instructions",num (s.steps - before.steps)),("jobs",num (s.jobs - before.jobs)),
    ("tasks",num (s.tasks - before.tasks)),("layouts",num (s.layouts - before.layouts)),("ns",num ns)] ++ extra
  let text := (JSON.Json.object fields).toString
  -- The page's GPU commands, validated by Lean (L4Factoidal.PageGpu): the host replays them
  -- on its WebGPU device. They need no layout; the canvas rectangles come with a render.
  let gpu := s.host.dom.gpuOut
  let text := if gpu.isEmpty then text else
    (text.dropEnd 1).toString ++ ",\"gpuPage\":" ++ toString s.host.dom.gpu.page ++ ",\"gpu\":[" ++
      ",".intercalate (gpu.toList.map PageGpu.Wire.HostCmd.json) ++ "]}"
  (text, { logs := s.logs.size, errors := s.errors.size })

/-- The session after a turn answer: the GPU commands it carried are the host's now. -/
def drained (s : Page.Session) : Page.Session :=
  { s with host := { s.host with dom := { s.host.dom with gpuOut := #[] } } }

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

/-- One action on what the engine holds. `measure` lays out an arena for the layout reads
of its scripts (`WebDocument.measure`), with the `layout` request of `start`. -/
def act (held : Held) (action html : String) (request : JSON.Json)
    (measure : JSON.Json → Option Page.Measure := fun _ => none) : Held × Except String String :=
  let full := request.field? "full" == some (.bool true)
  match action with
  | "load" =>
    match Rendering.SfntProfile.decodeBase64 (str request "moduleBase64") with
    | some bytes => loadModule held bytes
    | none => (held, .error "scriptSession: moduleBase64 is not Base64")
  | "start" =>
    match held.module with
    | none => (held, .error "scriptSession: no guest module; load it first")
    | some m =>
      let url := str request "url"
      let commands := min 1048576 ((natField request "commandLimit").getD 4096)
      let logs := min 1048576 ((natField request "logLimit").getD 1024)
      let started := WebWasm.timed fun _ => show Except String Page.Session from do
        let dom ← parse html url
        let (scripts, missing) ← scriptSources dom request
        let (vw, vh) := (viewport request).getD (800, 600)
        let reads : Page.Reads := { measure := measure ((request.field? "layout").getD (.object [])), width := vw, height := vh }
        let rate := max 1 ((natField request "instructionsPerMs").getD 100000)
        let s ← Page.start m dom url scripts { commands, logs, gpuPage := held.nextSession } #[] reads { instructionsPerMs := rate }
        return missing.foldl Page.Session.fail s
      match started with
      | (.error e, _) => (held, .error s!"scriptSession: {e}")
      | (.ok s, ns) =>
        let id := held.nextSession
        let (answer, marks) := turnAnswer id {} s {} true ns
        let s := drained s
        ({ held with session := some (id, s, marks), nextSession := id + 1 }, .ok answer)
  | "close" => ({ held with session := none }, .ok "{\"closed\":true}")
  | _ =>
    match held.session with
    | none => (held, .error "scriptSession: no session")
    | some (id, s, marks) =>
      if natField request "session" != some id then (held, .error "scriptSession: not the current session") else
      let held := { held with session := none }
      let before := Before.of s
      let run := fun (f : Page.Session → Page.Session) =>
        let (s', ns) := WebWasm.timed fun _ => f s
        let (answer, marks) := turnAnswer id before s' marks full ns
        ({ held with session := some (id, drained s', marks) }, Except.ok answer)
      match action with
      | "click" =>
        match natField request "node" with
        | some node => run (·.click node)
        | none => ({ held with session := some (id, s, marks) }, .error "scriptSession: click needs node")
      | "pointer" =>
        match pointerKind (str request "kind"), natField request "node" with
        | some kind, some node => run (·.pointer kind node (pointerInit request))
        | _, _ => ({ held with session := some (id, s, marks) }, .error "scriptSession: pointer needs kind (down, move, up, cancel) and node")
      | "resize" =>
        match viewport request with
        | some (w, h) => run fun s => ((s.resize w h).advance s.loop.clock).1
        | none => ({ held with session := some (id, s, marks) }, .error "scriptSession: resize needs width and height")
      | "advance" => run fun s => ((s.advance (s.loop.clock + ((natField request "ms").getD 0))).1).flushMove
      | "settle" => run fun s => (s.flushMove.settle ((natField request "budgetMs").getD 30000)).1
      | "turn" => run fun s => (s.flushMove.advance s.loop.clock).1
      | _ => ({ held with session := some (id, s, marks) }, .error "scriptSession: unknown action")

/-- The `scriptSession` operation. `html` is the page, for `start`. -/
def op (name html : String) (request : JSON.Json) (measure : JSON.Json → Option Page.Measure := fun _ => none) :
    Except String (Option String) := do
  if name != "scriptSession" then return none
  let action := str request "action"
  if !actions.contains action then throw "scriptSession: unknown action"
  if action == "info" then
    let (loaded, bytes) := peek request
    return some (JSON.Json.object [("ops",.array (actions.map .string)),("module",.bool loaded),
      ("bytes",num bytes),("engine",.string "QuickJS-NG in WasmVM")]).toString
  let (held, answer) := act (take request) action html request measure
  let n := keep held request
  return some (← answer.map (withNext n))

end WebScripts
