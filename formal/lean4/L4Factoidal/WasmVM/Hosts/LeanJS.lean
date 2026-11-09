/-
L4Factoidal.WasmVM.Hosts.LeanJS: the page scripts of one document, run by BubblePopJS, the
JavaScript engine written in Lean (`L4Factoidal.JS`; record docs/designissues/2026-11-08-lean-js-engine.md,
section 11).

The same page as `Hosts.Page`, with BubblePopJS in place of QuickJS-NG in WasmVM:

- The page objects are the same JavaScript, `tools/wasmvm/quickjs/prelude.js`, run by
  BubblePopJS once (`prepare`) and called with its natives object `n`.
- Each native of `n` is `JS.Native.host k`: Lean serves it with the import of
  `foafnaut_dom` that the QuickJS build calls (`qjs_wasmvm_entry.c`), through
  `Hosts.Page.serveExtra` on a `WasmVM.Aot.Window` that holds the call's strings. So each
  DOM read and change is the same Lean code on the same arena, and each change records the
  same typed `Hosts.Dom.Command`: `WebRenderScript.applyCommands` and a render's replay do
  not change.
- The event loop, the listener order, timers, frames, pointer input and resize are
  `Hosts.PageEvents` over this engine: the same steps as `Hosts.Page`.
- The microtask queue is the engine's job queue (§9.5): Promise reactions and
  `queueMicrotask` (which the prelude makes a Promise reaction) in one FIFO, run by the
  checkpoint (`JS.checkpoint`) wherever the event code runs one: after each script, task,
  event and frame callback, as in HTML.
- The script clock (`Page.ScriptClock`) counts the engine's steps (`JS.HeapOf.steps`: one
  for each call and each loop iteration) as its instructions.
-/
import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.WasmVM.Hosts.PageEvents
import L4Factoidal.WasmVM.Aot.Window
import L4Factoidal.JS.Interp
import L4Factoidal.JS.Snapshot

namespace L4Factoidal.WasmVM.Hosts.LeanJS
open L4Factoidal.WasmVM
open L4Factoidal.WasmVM.Hosts.Page (Host Reads ScriptClock Arena)

/-- The page's host as the engine holds it: the page host and the steps run in the
session before the current run. -/
structure LHost where
  page : Host
  base : Nat := 0
  /-- The page's WebAssembly instructions when the run started: those since are script time. -/
  wasm0 : Nat := 0
  deriving Inhabited

abbrev JHeap := JS.HeapOf LHost

/-- Steps for one script, task or event (the engine stops a run past it). A step is a call
or a loop iteration; 5 M of them take about as long natively as the 4 G instructions of
`Page.Limits.fuel` take QuickJS in WasmVM (half a minute to a minute, for a script that
loops until the budget ends). -/
def runBudget : Nat := 5000000

/-- The natives of `n` (prelude.js), in the order of `qjs_wasmvm_entry.c`: name and length.
Native `k` is `JS.Native.host k`. -/
def natives : Array (String × Nat) :=
  #[("byId", 1), ("info", 2), ("str", 2), ("kids", 1), ("attr", 2), ("query", 3), ("setAttr", 3),
    ("removeAttr", 2), ("setText", 2), ("create", 2), ("insert", 3), ("remove", 2), ("replace", 3),
    ("clone", 2), ("treeOp", 3), ("listen", 4), ("unlisten", 1), ("plan", 3), ("timer", 3),
    ("clearTimer", 1), ("frame", 1), ("cancelFrame", 1), ("log", 1), ("gpu", 3), ("api", 3), ("wasm", 6), ("detach", 1),
    ("wasmGlue", 0), ("gpuBytes", 3)]

/-! ## The natives: each is an import of `foafnaut_dom`, served by `Hosts.Page` -/

/-- An argument of an import: an i32, a string (pointer and length), or the output buffer
(pointer and capacity). -/
inductive Arg where
  | int (v : Int)
  | str (b : ByteArray)
  | out

/-- The capacity of an output buffer (as `read_bytes` of the QuickJS build allows). -/
def outCap : Nat := 67108864

/-- ToInt32 of an argument (`JS_ToInt32` of the QuickJS build). -/
def intOf : JS.HostArg → Int
  | .val (.num x) => JS.toInt32 x
  | .val (.bool b) => if b then 1 else 0
  | _ => 0

/-- ToString of an argument for an import, in UTF-8. -/
def bytesOf : JS.HostArg → ByteArray
  | .val (.str s) => (JS.Str.toHost s).toUTF8
  | .val (.num x) => (JS.numToString x).toUTF8
  | .val (.bool b) => (if b then "true" else "false").toUTF8
  | .val .undef => "undefined".toUTF8
  | .val .null => "null".toUTF8
  | .val (.big i) => (toString i).toUTF8
  | .val _ => "[object Object]".toUTF8
  | .bytes b => b

/-- Lay the arguments out in a window: the strings from offset 16, the output buffer after
them. The i32 arguments, the segments, the buffer's offset and the window's size. -/
def layout (args : List Arg) : Array Value × Array (Nat × ByteArray) × Nat × Nat := Id.run do
  let strTotal := args.foldl (fun n a => match a with | .str b => n + b.size + 1 | _ => n) 0
  let buf : Nat := 16 + strTotal + 8
  let mut vals : Array Value := #[]
  let mut segs : Array (Nat × ByteArray) := #[]
  let mut at_ : Nat := 16
  for a in args do
    match a with
    | .int v => vals := vals.push (Page.i32v v)
    | .str b =>
      vals := vals.push (Page.i32v at_) |>.push (Page.i32v b.size)
      segs := segs.push (at_, b)
      at_ := at_ + b.size + 1
    | .out => vals := vals.push (Page.i32v buf) |>.push (Page.i32v outCap)
  return (vals, segs, buf, buf + outCap)

/-- The signed i32 of an import's answer. -/
def signed (r : HostResult) : Except String Int :=
  match r with
  | .values #[.i32 v] => .ok (if v.toNat ≥ 2147483648 then (v.toNat : Int) - 4294967296 else v.toNat)
  | .values _ => .ok 0
  | .trap m => .error m
  | .exit _ => .error "exit"

/-- Call import `nm` of `foafnaut_dom` on the page host: the host after it, the answer,
and the bytes the import wrote in the output buffer. -/
def callImport (h : Host) (nm : String) (args : List Arg) : Host × Except String Int × ByteArray :=
  let (vals, segs, buf, size) := layout args
  let st : StoreOf Aot.Window := { mems := #[{ data := { size, segs }, max := none }] }
  let (h, st, r) := Page.serveExtra 0 Hosts.Dom.moduleName nm vals h st
  let out := match st.mems[0]? with
    | some m => ((m.data.writes.toList.reverse.find? (·.1 == buf)).map (·.2)).getD ByteArray.empty
    | none => ByteArray.empty
  (h, signed r, out)

def strAns (r : Except String Int) (out : ByteArray) (nullOnNone : Bool) : JS.HostAns :=
  match r with
  | .error m => .err m
  | .ok n =>
    if n == -1 && nullOnNone then .val .null
    else if n < 0 then .val (.num (Float.ofInt n))
    else .val (.str (JS.Str.ofHost (String.fromUTF8? (out.extract 0 n.toNat) |>.getD "")))

def intAns (r : Except String Int) : JS.HostAns :=
  match r with
  | .ok n => .val (.num (Float.ofInt n))
  | .error m => .err m

/-- A list of i32 (little-endian) written by an import. -/
def listAns (r : Except String Int) (out : ByteArray) (emptyOnError : Bool) : JS.HostAns :=
  match r with
  | .error m => .err m
  | .ok n =>
    if n < 0 then (if emptyOnError then .ints #[] else .val (.num (Float.ofInt n))) else
    .ints ((List.range n.toNat).toArray.map fun i =>
      let v := Page.u32At out (4 * i)
      if v ≥ 2147483648 then (v : Int) - 4294967296 else v)

/-- The WebAssembly API's glue (`tools/wasmvm/quickjs/webassembly.js`), which the prelude
compiles on the first read of `WebAssembly` (native `wasmGlue`). -/
def wasmGlue : String := include_str "../../../../../tools/wasmvm/quickjs/webassembly.js"

/-- Serve native `k` of `n` with its arguments (as the `n_*` functions of
`qjs_wasmvm_entry.c`), or the clock (`JS.hostClockId`). -/
def serveNative (h : Host) (k : Nat) (args : Array JS.HostArg) : Host × JS.HostAns :=
  let a := fun (i : Nat) => args.getD i (.val .undef)
  let i := fun (j : Nat) => Arg.int (intOf (a j))
  let s := fun (j : Nat) => Arg.str (bytesOf (a j))
  if k == JS.hostClockId then
    let (t, time) := h.time.read h.loop.clock
    ({ h with time }, .val (.num (Float.ofNat t)))
  else match k with
  | 0 => let (h, r, _) := callImport h "get_element_by_id" [s 0]; (h, intAns r)
  | 1 => let (h, r, _) := callImport h "node_info" [i 0, i 1]; (h, intAns r)
  | 2 => let (h, r, o) := callImport h "node_string" [i 0, i 1, .out]; (h, strAns r o false)
  | 3 => let (h, r, o) := callImport h "node_children" [i 0, .int 0, .out]; (h, listAns r o true)
  | 4 => let (h, r, o) := callImport h "get_attribute" [i 0, s 1, .out]; (h, strAns r o true)
  | 5 => let (h, r, o) := callImport h "node_query" [i 0, i 1, s 2, .out]; (h, strAns r o true)
  | 6 => let (h, r, _) := callImport h "set_attribute" [i 0, s 1, s 2]; (h, intAns r)
  | 7 => let (h, r, _) := callImport h "remove_attribute" [i 0, s 1]; (h, intAns r)
  | 8 => let (h, r, _) := callImport h "text_content_set" [i 0, s 1]; (h, intAns r)
  | 9 => let (h, r, _) := callImport h "create_node" [i 0, s 1]; (h, intAns r)
  | 10 => let (h, r, _) := callImport h "insert_before" [i 0, i 1, i 2]; (h, intAns r)
  | 11 => let (h, r, _) := callImport h "remove_child" [i 0, i 1]; (h, intAns r)
  | 12 => let (h, r, _) := callImport h "replace_child" [i 0, i 1, i 2]; (h, intAns r)
  | 13 => let (h, r, _) := callImport h "clone_node" [i 0, i 1]; (h, intAns r)
  | 14 => let (h, r, _) := callImport h "tree_op" [i 0, i 1, i 2]; (h, intAns r)
  | 15 => let (h, r, _) := callImport h "listen" [i 0, s 1, i 2, i 3]; (h, intAns r)
  | 16 => let (h, r, _) := callImport h "unlisten" [i 0]; (h, intAns r)
  | 17 => let (h, r, o) := callImport h "dispatch_plan" [i 0, s 1, i 2, .out]; (h, listAns r o false)
  | 18 =>
    let delay := intOf (a 1)
    let (h, r, _) := callImport h "set_timer" [i 0, .int (if delay < 0 then 0 else delay), .int (if intOf (a 2) != 0 then 1 else 0)]
    (h, intAns r)
  | 19 => let (h, _, _) := callImport h "clear_timer" [i 0]; (h, .val .undef)
  | 20 => let (h, r, _) := callImport h "request_frame" [i 0]; (h, intAns r)
  | 21 => let (h, _, _) := callImport h "cancel_frame" [i 0]; (h, .val .undef)
  | 22 => let (h, _, _) := callImport h "console_log" [s 0]; (h, .val .undef)
  | 23 =>
    let payload := match a 2 with
      | .val .undef | .val .null => ByteArray.empty
      | p => bytesOf p
    let msg := bytesOf (a 1) ++ "\n".toUTF8 ++ payload
    if msg.size > outCap then (h, .val (.num (-5))) else
    let (h, r, o) := callImport h "gpu_command" [i 0, .int 0, .str msg, .out]
    (h, strAns r o false)
  | 24 =>
    -- api(op, flags, bytes, ...args): the argument block of `web_api` (Hosts.WebApi).
    let rest := (args.toList.drop 3).map bytesOf
    let block := rest.foldl (fun acc b => acc ++ Hosts.WebApi.u32le b.size ++ b) (Hosts.WebApi.u32le rest.length)
    if block.size > outCap then (h, .val (.num (-5))) else
    let (h, r, o) := callImport h "web_api" [i 0, i 1, .str block, .out]
    let asBytes := match a 2 with | .val (.bool b) => b | _ => false
    (match r with
     | .ok n => if n < 0 then (h, .val (.num (Float.ofInt n)))
       else if asBytes then (h, .bytes (o.extract 0 n.toNat)) else (h, strAns r o false)
     | .error m => (h, .err m))
  | 25 =>
    -- The WebAssembly API (`n.wasm(op, handle, payload, view, text)`): the same Lean as the
    -- `wasm_call` import (`Hosts.PageWasm.core`), with the view's bytes given directly and
    -- the changed chunks written back into that ArrayBuffer (`HostAns.writes`).
    let u := fun (j : Nat) => Int.toNat (intOf (a j) % 4294967296)
    let payload := match a 2 with
      | .val .undef | .val .null => ByteArray.empty
      | p => bytesOf p
    let view := match a 3 with | .bytes b => some b | _ => none
    let viewLen := (view.map (·.size)).getD 0
    let text := match a 4 with | .val (.bool true) => true | _ => false
    let w := h.wasm
    let h := { h with wasm := {} }
    let read : Hosts.PageWasm.ReadView := fun _ => if viewLen > w.config.viewBytes then none else view
    let (w, ws, ans) := Hosts.PageWasm.core (u 0) (u 1) payload viewLen read w
    -- With an `out` ArrayBuffer (argument 5) that holds the answer, it is written there and
    -- its length answered, as the QuickJS native does.
    let outLen := match a 5 with | .bytes o => some o.size | _ => none
    let ans : JS.HostAns := match ans with
      | .error c => .val (.num (Float.ofInt c))
      | .ok b =>
        if text then .val (.str ((String.fromUTF8? b).getD ""))
        else match outLen with
          | some cap => if b.size ≤ cap then .writes 5 #[(0, b)] (.val (.num (Float.ofNat b.size))) else .bytes b
          | none => .bytes b
    ({ h with wasm := w }, if ws.isEmpty then ans else .writes 3 ws ans)
  | 26 => (h, .detach 0)
  | 27 => (h, .val (.str wasmGlue))
  -- `gpu_command` answered as bytes, an ArrayBuffer (Canvas 2D getImageData, op 202).
  | 28 =>
    let payload := match a 2 with
      | .val .undef | .val .null => ByteArray.empty
      | p => bytesOf p
    let msg := bytesOf (a 1) ++ "\n".toUTF8 ++ payload
    if msg.size > outCap then (h, .val (.num (-5))) else
    let (h, r, o) := callImport h "gpu_command" [i 0, .int 0, .str msg, .out]
    (match r with
     | .ok n => if n < 0 then (h, .val (.num (Float.ofInt n))) else (h, .bytes (o.extract 0 n.toNat))
     | .error m => (h, .err m))
  | _ => (h, .err "foafnaut_dom: no such native")

/-- The host's natives with the script clock: the instructions run so far are the steps of
the session before this run and the steps of this run (`runBudget` less the steps left),
as `Page.Session.run` counts the instructions of a run at each host call. -/
def hostCall (lh : LHost) (k : Nat) (args : Array JS.HostArg) (left : Nat) : LHost × JS.HostAns :=
  let base := lh.base
  let wasm0 := lh.wasm0
  let steps := base + (runBudget - left) + (lh.page.wasm.steps - wasm0)
  -- `lh` is not used again: the page host is then the only reference to the DOM state, and
  -- a change of the arena is in place (`Hosts.Dom.change`)
  let h := lh.page
  let h := { h with time := h.time.atRun h.loop.clock steps }
  let (h, ans) := serveNative h k args
  ({ page := h, base, wasm0 }, ans)

/-! ## The session -/

structure Session where
  heap : JHeap
  /-- The object prelude.js returned: `call`, `dispatch`, `report`, `start`, `script`,
  `url`, `release`. -/
  api : JS.Value
  limits : Page.Limits
  /-- Engine steps run in total. -/
  steps : Nat := 0
  /-- Promise jobs run in total. -/
  jobs : Nat := 0
  /-- Tasks, frame callbacks and events run in total. -/
  tasks : Nat := 0
  errors : Array String := #[]
  lastFrame : Option Nat := none
  deriving Inhabited

def Session.host (s : Session) : Host := (s.heap.host.map (·.page)).getD default

/-- Set the page host. The heap is taken apart first, so the arena is not copied. -/
def Session.setHost (s : Session) (h : Host) : Session :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame⟩ := s
  let lh := heap.host.getD default
  ⟨{ heap with host := some { lh with page := h } }, api, limits, steps, jobs, tasks, errors, lastFrame⟩

def Session.fail (s : Session) (what : String) : Session :=
  { s with errors := if s.errors.size < 256 then s.errors.push what else s.errors }

/-- One run of the engine: the budget is set, the steps it used counted, and the loop's
clock moves up to script time at the end (as `Page.Session.run`). -/
def Session.run (s : Session) (f : JHeap → (JS.Outcome × JS.Value) × JHeap) : Session × JS.Outcome × JS.Value :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame⟩ := s
  let lh := heap.host.getD default
  let page := lh.page
  let page := { page with time := page.time.atRun page.loop.clock steps }
  let wasm0 := page.wasm.steps
  let heap := { heap with steps := runBudget, host := some { lh with page, base := steps, wasm0 } }
  let ((o, v), heap) := f heap
  let lh := heap.host.getD default
  -- The page's WebAssembly ran in this run's natives: its instructions are script time too.
  let steps := steps + (runBudget - heap.steps) + (lh.page.wasm.steps - wasm0)
  let page := lh.page
  let time := page.time.atRun page.loop.clock steps
  let page := { page with time, loop := { page.loop with clock := time.sync page.loop.clock } }
  (⟨{ heap with host := some { lh with page } }, api, limits, steps, jobs, tasks, errors, lastFrame⟩, o, v)

/-- The text of an outcome that is not normal. -/
def failure : JS.Outcome → Option String
  | .ok => none
  | .threw _ m => some m
  | .syntaxError m => some m
  | .halted w => some s!"halted: {w}"

/-- A method of the prelude's object. -/
def Session.api? (s : Session) (name : String) (args : Array JS.Value) : Session × JS.Value :=
  let api := s.api
  let (s, o, v) := s.run fun h => JS.callMethod h api name args
  match failure o with
  | some m => (s.fail m, v)
  | none => (s, v)

/-- The microtask checkpoint. -/
def Session.runJobs (s : Session) : Session :=
  let (s, o, v) := s.run fun h => let ((o, n), h) := JS.checkpoint h; ((o, .num (Float.ofNat n)), h)
  let n := match v with | .num x => x.toUInt64.toNat | _ => 0
  let s := { s with jobs := s.jobs + n }
  match failure o with
  | some m => s.fail m
  | none => s

/-- Run a classic script; an exception is reported at the window (HTML "report an
exception", the prelude's `report`) and recorded. -/
def Session.eval (s : Session) (src : String) : Session :=
  let (s, o, _) := s.run fun h => let (o, h) := JS.evalScript h src; ((o, .undef), h)
  match o with
  | .ok => s
  | .threw v m => (s.api? "report" #[v]).1.fail m
  | o => s.fail ((failure o).getD "")

def Session.dispatchOnly (s : Session) (target : Nat) (type : String) : Session × Bool :=
  let (s, v) := s.api? "dispatch" #[.num (Float.ofNat target), .str type, .num (Float.ofNat (Page.flagsOf type))]
  ({ s with tasks := s.tasks + 1 }, match v with | .str "prevented" => true | _ => false)

def Session.callbackOnly (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Session :=
  let (s, _) := s.api? "call" #[.num (Float.ofNat cb), .num (Float.ofInt target), .num (Float.ofNat arg)]
  { s with tasks := s.tasks + 1 }

def Session.release (s : Session) (cb : Nat) : Session := (s.api? "release" #[.num (Float.ofNat cb)]).1

/-- The session as an engine of `Hosts.PageEvents`. -/
def engine : PageEvents.Engine Session :=
  { host := Session.host, setHost := Session.setHost, dispatchOnly := Session.dispatchOnly,
    callbackOnly := Session.callbackOnly, release := Session.release, runJobs := Session.runJobs,
    lastFrame := Session.lastFrame, setLastFrame := fun s f => { s with lastFrame := f } }

/-! ## Starting a page -/

/-- The page objects (`tools/wasmvm/quickjs/prelude.js`, the file the QuickJS build
embeds). -/
def prelude : String := include_str "../../../../../tools/wasmvm/quickjs/prelude.js"

/-- A fresh realm with the page host on an empty document (no page objects yet). -/
def freshRealm (lim : Page.Limits := {}) : JHeap :=
  let host : Host := { dom := { dom := Page.emptyDocument, commandLimit := lim.commands, logLimit := lim.logs } }
  JS.freshHeapOf (some { page := host }) hostCall

/-- The realm with the page objects, on an empty document, made by running the prelude:
each page starts from it with its own arena, so the prelude runs once (as
`Page.Module'.base`). `LeanJSRealm.prepare` gives the same realm from the heap this left,
kept as data at build time (`snapshotData`), without lexing, parsing or running the
prelude. -/
def prepareSource (lim : Page.Limits := {}) : Except String Session := do
  let heap := { freshRealm lim with steps := runBudget }
  let (nobj, heap) := JS.hostObject heap natives
  let ((o, f), heap) := JS.evalValue heap prelude
  if let some m := failure o then throw s!"prelude: {m}"
  let ((o, api), heap) := JS.callFunction heap f .undef #[nobj]
  if let some m := failure o then throw s!"prelude: {m}"
  return { heap := { heap with jobs := #[], jobHead := 0 }, api, limits := lim }

/-- The mark of the prelude a snapshot was made from (its text's hash). -/
def preludeMark : String := toString (hash prelude)

/-- The realm of `prepareSource` as data (`JS.Snapshot.encode`), with the prelude's object
and `preludeMark`. `lake exe bubblepop-realm` writes it into `LeanJSRealmData.lean` at
build time (build-web-render.sh). -/
def snapshotData : Except String String := do
  let s ← prepareSource
  JS.Snapshot.encode (freshRealm {}) s.heap #[s.api, .str preludeMark]

/-- The realm from snapshot data: the heap that `prepareSource` left, decoded on a fresh
realm; refused when it was made from another prelude or on another realm (then the data
is stale: build-web-render.sh makes it again). -/
def prepareWith (data : String) (lim : Page.Limits := {}) : Except String Session := do
  let (heap, extra) ← JS.Snapshot.decode (freshRealm lim) data
  match extra with
  | #[api, .str mark] =>
    if mark != preludeMark then throw "snapshot: made from another prelude"
    return { heap := { heap with steps := runBudget, jobs := #[], jobHead := 0 }, api, limits := lim }
  | _ => throw "snapshot: no prelude object"

/-- The deepest nesting of JavaScript calls (`Heap.maxDepth`; deeper is a `RangeError`, as in
browsers). Natively 400. In the Foafnaut Wasm build the evaluator's frames are on the browser's
WebAssembly stack, which is about 1 MB in Chrome and Node (measured: a plain recursion
overflowed it at 368 calls, a call inside `try` in a `for` loop at 202, `Array.prototype.map`
callbacks at 128 levels of two calls), and overflowing it would stop the whole build, not the
script. The worst case measured was about 5.4 KB of that stack per call, so 100 calls use
about 540 KB, some 55 % of it. Safari's worker stack was not measured (record
2026-11-08-lean-js-engine.md, section 17). -/
def callDepth : Nat := if System.Platform.numBits == 32 then 100 else 400

/-- Start a page on the prepared realm (as `Page.start` and `Page.Session.startP`): the
content event handler attributes, the URL, the classic scripts in document order (each with
the current script set and a microtask checkpoint after it), `DOMContentLoaded`, the
window's `load` event as a task, and the tasks due at time 0. -/
def start (base : Session) (dom : Arena) (url : String) (scripts : Array (Nat × String)) (lim : Page.Limits := {})
    (reads : Reads := {}) (time : ScriptClock := {}) : Session := Id.run do
  let gpu := L4Factoidal.PageGpu.State.empty lim.gpuPage
  let domHost : Page.DomHost := { dom := dom, commandLimit := lim.commands, logLimit := lim.logs, framing := lim.frames, gpu := gpu, url, hostLoads := lim.hostLoads }
  -- the page's own iframes get browsing contexts before its scripts run (as `Page.Session.startP`)
  let domHost := if domHost.framing && dom.nodes.any (L4Factoidal.DOM.Dom.isHtmlElement · "iframe") then
    let d1 := Hosts.Dom.connectFrames domHost #[0]
    { d1 with navigations := d1.navigations.filter (!·.2.isEmpty) } else domHost
  let s := { base with
    heap := { base.heap with maxDepth := callDepth },
    limits := lim, steps := 0, jobs := 0, tasks := 0, errors := #[], lastFrame := none }
  let mut s := s.setHost { dom := domHost, reads, time, web := { entropy := lim.entropy, docEncoding := lim.encoding } }
  s := (s.api? "start" #[]).1
  s := (s.api? "url" #[.str (JS.Str.ofHost url)]).1
  for (node, src) in scripts do
    s := (s.api? "script" #[.num (Float.ofNat node)]).1
    s := s.eval src
    s := engine.checkpoint s
  s := (s.api? "script" #[.num (-1)]).1
  s := (engine.dispatch s 0 "DOMContentLoaded").1
  if Hosts.Dom.framesLoading s.host.dom then
    s := s.setHost { s.host with dom := { s.host.dom with loadWaits := true } }
  else
    s := engine.setLoop s ((engine.loop s).queueTask .domManipulation 0 (some { type := "load", target := Page.windowId }))
  return (engine.advance s 0).1

/-- A frame's navigation ends with document `source` (as `Page.Session.loadFrameP`): it
joins the arena, its classic scripts run in the page's realm with the current script set
(none for a frame of another origin or a sandbox without scripts), its `load` event at the
`iframe` is a task, and the window's when it was waiting for this frame. -/
def loadFrame (s : Session) (el : Nat) (source : String) (scripts : Array (Nat × String)) (xml : Bool := false) :
    Session := Id.run do
  let run := Hosts.Dom.frameScriptsInRealm s.host.dom el
  let (dom, root) := Hosts.Dom.attachDocument s.host.dom el source xml
  let mut s := s.setHost { s.host with dom }
  if let some root := root then
    let scripts := if run then scripts else #[]
    for (node, src) in scripts do
      s := (s.api? "script" #[.num (Float.ofNat (node + root))]).1
      s := s.eval src
      s := engine.checkpoint s
    s := (s.api? "script" #[.num (-1)]).1
  s := engine.setLoop s ((engine.loop s).queueTask .networking 0 (some { type := "load", target := el }))
  if s.host.dom.loadWaits && !Hosts.Dom.framesLoading s.host.dom then
    s := s.setHost { s.host with dom := { s.host.dom with loadWaits := false } }
    s := engine.setLoop s ((engine.loop s).queueTask .domManipulation 0 (some { type := "load", target := Page.windowId }))
  return s

/-! ## What a turn did -/

def Session.commands (s : Session) : Array Hosts.Dom.Command := s.host.dom.commands
def Session.logs (s : Session) : Array String := s.host.dom.logs
def Session.changes (s : Session) : Nat := s.host.dom.changes
def Session.layouts (s : Session) : Nat := s.host.reads.layouts

end L4Factoidal.WasmVM.Hosts.LeanJS
