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
import L4Factoidal.WasmVM.Hosts.LeanJSModules

namespace L4Factoidal.WasmVM.Hosts.LeanJS
open L4Factoidal.WasmVM
open L4Factoidal.WasmVM.Hosts.Page (Host Reads ScriptClock Arena)

/-- Steps for one script, task or event (the engine stops a run past it). A step is a call
or a loop iteration; 5 M of them take about as long natively as the 4 G instructions of
`Page.Limits.fuel` take QuickJS in WasmVM (half a minute to a minute, for a script that
loops until the budget ends). -/
def runBudget : Nat := 5000000

/-! ## Dedicated workers: what a realm asks of them (`Hosts.LeanJSWorkers`) -/

/-- An ask of a realm's scripts about workers, in the order made. A page creates, posts to
and terminates its workers; a worker posts to its page (`post 0`), closes itself, and
reports an error it did not handle. -/
inductive WorkerOp where
  | create (id : Nat) (url name : String)
  | post (id : Nat) (data : ByteArray)
  | terminate (id : Nat)
  | close
  /-- An uncaught error of a worker: message, file, line, column. -/
  | error (message file : String) (line col : Nat)
  deriving Inhabited

/-- An event for a realm: from worker `worker` (or the page, 0), of kind `message`,
`messageerror`, `error` (with the error's JSON) or `loaderror`. -/
structure WorkerEvent where
  worker : Nat
  kind : String
  header : String := ""
  data : ByteArray := ByteArray.empty
  deriving Inhabited

/-- The worker part of a BubblePopJS host. Empty, and never read, on a page that makes no
worker. -/
structure WorkerHost where
  ops : Array WorkerOp := #[]
  /-- Events for this realm, first in first out: each is the data of one task that the
  loop runs (`LeanJSWorkers.eventHandle`). -/
  inbox : Array WorkerEvent := #[]
  head : Nat := 0
  /-- The event being dispatched (native `worker` 3 took it). -/
  current : WorkerEvent := default
  nextId : Nat := 1
  /-- A worker: the script sources the embedder fetched, by URL (`none`: the fetch failed). -/
  scripts : Array (String × Option String) := #[]
  /-- A worker: the URL an `importScripts` of this run needs and has not got. The run is
  undone and waits for it (`LeanJSWorkers`). -/
  missing : Option String := none
  deriving Inhabited

/-! The inbox is a queue: `push` at the end, `take` from `head` (and emptied when all of it
is taken). `push_pending`, `take_pending`: the events not yet taken are a list that `push`
appends to and `take` takes the first of, so a realm's events run in the order they came
(the model `EventLoop.Agents`, `channel_prefix`). -/

/-- The events not yet taken, in order. -/
def WorkerHost.pending (wh : WorkerHost) : List WorkerEvent := wh.inbox.toList.drop wh.head

def WorkerHost.push (wh : WorkerHost) (ev : WorkerEvent) : WorkerHost := { wh with inbox := wh.inbox.push ev }

def WorkerHost.take (wh : WorkerHost) : WorkerHost × Option WorkerEvent :=
  match wh.inbox[wh.head]? with
  | none => (wh, none)
  | some ev =>
    (if wh.head + 1 ≥ wh.inbox.size then { wh with inbox := #[], head := 0, current := ev }
     else { wh with head := wh.head + 1, current := ev }, some ev)

theorem WorkerHost.push_pending (wh : WorkerHost) (ev : WorkerEvent) (h : wh.head ≤ wh.inbox.size) :
    (wh.push ev).pending = wh.pending ++ [ev] := by
  have h' : wh.head ≤ wh.inbox.toList.length := by simpa using h
  simp [WorkerHost.pending, WorkerHost.push, List.drop_append_of_le_length h']

theorem WorkerHost.take_pending (wh : WorkerHost) :
    wh.take.2 = wh.pending.head? ∧ wh.take.1.pending = wh.pending.tail := by
  unfold WorkerHost.take WorkerHost.pending
  split
  · rename_i hn
    have : wh.inbox.size ≤ wh.head := by
      rcases Nat.lt_or_ge wh.head wh.inbox.size with h | h
      · simp [Array.getElem?_eq_getElem h] at hn
      · exact h
    have h' : wh.inbox.toList.length ≤ wh.head := by simpa using this
    simp [List.drop_eq_nil_of_le h']
  · rename_i ev hs
    have hlt : wh.head < wh.inbox.size := by
      rcases Nat.lt_or_ge wh.head wh.inbox.size with h | h
      · exact h
      · simp [Array.getElem?_eq_none h] at hs
    have hev : wh.inbox[wh.head] = ev := by simpa [Array.getElem?_eq_getElem hlt] using hs
    have hd : wh.inbox.toList.drop wh.head = ev :: wh.inbox.toList.drop (wh.head + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hlt)]; simp [hev]
    split
    · rename_i hge
      refine ⟨by simp [hd], ?_⟩
      have h' : wh.inbox.toList.length ≤ wh.head + 1 := by simpa using hge
      simp [hd, List.drop_eq_nil_of_le h']
    · exact ⟨by simp [hd], by simp [hd]⟩

/-- `push` and `take` keep `head` within the inbox (the hypothesis of `push_pending`). -/
theorem WorkerHost.push_head (wh : WorkerHost) (ev : WorkerEvent) (h : wh.head ≤ wh.inbox.size) :
    (wh.push ev).head ≤ (wh.push ev).inbox.size := by
  simp [WorkerHost.push]; omega

theorem WorkerHost.take_head (wh : WorkerHost) (h : wh.head ≤ wh.inbox.size) :
    wh.take.1.head ≤ wh.take.1.inbox.size := by
  unfold WorkerHost.take
  split
  · exact h
  · split
    · simp
    · simp; omega

/-- Native `worker` (number 29): `worker(op, a, b, c)`.

- page: 0 `create(url, name)` answers the worker's number; 1 `post(id, bytes)`;
  2 `terminate(id)`;
- both: 3 `take()` answers the next event's head (JSON: `w` worker, `k` kind, `h` header)
  or ""; 4 answers its bytes;
- worker: 1 `post(0, bytes)` to the page; 10 `close()`; 11 `error(message, file, line,
  col)`; 12 `importScript(url)` answers the source, -1 when the embedder has not fetched
  it yet (the run is undone: `missing`), -2 when the fetch failed. -/
def serveWorker (wh : WorkerHost) (args : Array JS.HostArg) : WorkerHost × JS.HostAns :=
  let a := fun (i : Nat) => args.getD i (.val .undef)
  let nat := fun (i : Nat) => match a i with | .val (.num x) => x.toUInt64.toNat | _ => 0
  let text := fun (i : Nat) => match a i with
    | .val (.str s) => JS.Str.toHost s
    | .bytes b => (String.fromUTF8? b).getD ""
    | _ => ""
  let bytes := fun (i : Nat) => match a i with | .bytes b => b | _ => ByteArray.empty
  match nat 0 with
  | 0 =>
    let id := wh.nextId
    ({ wh with nextId := id + 1, ops := wh.ops.push (.create id (text 1) (text 2)) }, .val (.num (Float.ofNat id)))
  | 1 => ({ wh with ops := wh.ops.push (.post (nat 1) (bytes 2)) }, .val .undef)
  | 2 => ({ wh with ops := wh.ops.push (.terminate (nat 1)) }, .val .undef)
  | 3 =>
    match wh.take with
    | (wh, none) => (wh, .val (.str (JS.Str.ofHost "")))
    | (wh, some ev) =>
      let j := JSON.Json.object [("w", .number (toString ev.worker)), ("k", .string ev.kind), ("h", .string ev.header)]
      (wh, .val (.str (JS.Str.ofHost j.toString)))
  | 4 => (wh, .bytes wh.current.data)
  | 10 => ({ wh with ops := wh.ops.push .close }, .val .undef)
  | 11 => ({ wh with ops := wh.ops.push (.error (text 1) (text 2) (nat 3) (nat 4)) }, .val .undef)
  | 12 =>
    let url := text 1
    match wh.scripts.find? (·.1 == url) with
    | some (_, some src) => (wh, .val (.str (JS.Str.ofHost src)))
    | some (_, none) => (wh, .val (.num (-2)))
    | none => ({ wh with missing := wh.missing <|> some url }, .val (.num (-1)))
  | _ => (wh, .err "worker: no such op")

/-- The page's host as the engine holds it: the page host and the steps run in the
session before the current run. -/
structure LHost where
  page : Host
  base : Nat := 0
  /-- The page's WebAssembly instructions when the run started: those since are script time. -/
  wasm0 : Nat := 0
  /-- Dedicated workers (`Hosts.LeanJSWorkers`). -/
  wk : WorkerHost := {}
  /-- The step budget of a run (`runBudget`; a worker's is smaller). -/
  budget : Nat := runBudget
  deriving Inhabited

abbrev JHeap := JS.HeapOf LHost


/-- The natives of `n` (prelude.js), in the order of `qjs_wasmvm_entry.c`: name and length.
Native `k` is `JS.Native.host k`. -/
def natives : Array (String × Nat) :=
  #[("byId", 1), ("info", 2), ("str", 2), ("kids", 1), ("attr", 2), ("query", 3), ("setAttr", 3),
    ("removeAttr", 2), ("setText", 2), ("create", 2), ("insert", 3), ("remove", 2), ("replace", 3),
    ("clone", 2), ("treeOp", 3), ("listen", 4), ("unlisten", 1), ("plan", 3), ("timer", 3),
    ("clearTimer", 1), ("frame", 1), ("cancelFrame", 1), ("log", 1), ("gpu", 3), ("api", 3), ("wasm", 6), ("detach", 1),
    ("wasmGlue", 0), ("gpuBytes", 3), ("worker", 4)]

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
  if k == 29 then
    let ⟨page, base, wasm0, wk, budget⟩ := lh
    let (wk, ans) := serveWorker wk args
    (⟨page, base, wasm0, wk, budget⟩, ans)
  else
  let base := lh.base
  let wasm0 := lh.wasm0
  let wk := lh.wk
  let budget := lh.budget
  let steps := base + (budget - left) + (lh.page.wasm.steps - wasm0)
  -- `lh` is not used again: the page host is then the only reference to the DOM state, and
  -- a change of the arena is in place (`Hosts.Dom.change`)
  let h := lh.page
  let h := { h with time := h.time.atRun h.loop.clock steps }
  let (h, ans) := serveNative h k args
  ({ page := h, base, wasm0, wk, budget }, ans)

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
  /-- The state of trusted input (`WebDriver.Input.Trusted`: the keys and buttons the user
  holds, the last user activation). It is a field of the session and not of the heap: a
  run of the engine is a function of the heap (`Session.run`), so no script and no import
  reads or changes it (`Session.run_trusted`). Only `setTrusted` changes it, and only the
  host's input actions call that (`WebScripts`, action `actions`). -/
  trusted : L4Factoidal.WebDriver.Input.Trusted := {}
  deriving Inhabited

def Session.setTrusted (s : Session) (t : L4Factoidal.WebDriver.Input.Trusted) : Session := { s with trusted := t }

def Session.host (s : Session) : Host := (s.heap.host.map (·.page)).getD default

/-- Set the page host. The heap is taken apart first, so the arena is not copied. -/
def Session.setHost (s : Session) (h : Host) : Session :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  let lh := heap.host.getD default
  ⟨{ heap with host := some { lh with page := h } }, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩

/-- The worker part of the host (`Hosts.LeanJSWorkers`). -/
def Session.wk (s : Session) : WorkerHost := (s.heap.host.map (·.wk)).getD {}

/-- Set the worker part of the host (the heap taken apart, as `setHost`). -/
def Session.setWk (s : Session) (wk : WorkerHost) : Session :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  let lh := heap.host.getD default
  ⟨{ heap with host := some { lh with wk } }, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩

/-- Whether the realm has made no ask of workers and holds no event from them: the case of
every page that makes no worker, checked once per microtask checkpoint. -/
def Session.wkIdle (s : Session) : Bool :=
  match s.heap.host with
  | some lh => lh.wk.ops.isEmpty && lh.wk.nextId == 1
  | none => true

/-- The step budget of each run of this session (`runBudget` for a page). -/
def Session.setBudget (s : Session) (budget : Nat) : Session :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  let lh := heap.host.getD default
  ⟨{ heap with host := some { lh with budget } }, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩

def Session.fail (s : Session) (what : String) : Session :=
  { s with errors := if s.errors.size < 256 then s.errors.push what else s.errors }

/-- One run of the engine: the budget is set, the steps it used counted, and the loop's
clock moves up to script time at the end (as `Page.Session.run`). -/
def Session.run (s : Session) (f : JHeap → (JS.Outcome × JS.Value) × JHeap) : Session × JS.Outcome × JS.Value :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  let lh := heap.host.getD default
  let page := lh.page
  let page := { page with time := page.time.atRun page.loop.clock steps }
  let wasm0 := page.wasm.steps
  let budget := lh.budget
  let heap := { heap with steps := budget.toUInt64, host := some { lh with page, base := steps, wasm0 } }
  let ((o, v), heap) := f heap
  let lh := heap.host.getD default
  -- The page's WebAssembly ran in this run's natives: its instructions are script time too.
  let steps := steps + (budget - heap.steps.toNat) + (lh.page.wasm.steps - wasm0)
  let page := lh.page
  let time := page.time.atRun page.loop.clock steps
  let page := { page with time, loop := { page.loop with clock := time.sync page.loop.clock } }
  (⟨{ heap with host := some { lh with page } }, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩, o, v)

/-- One run of the engine with any answer (as `run`). -/
def Session.runG {α : Type} (s : Session) (f : JHeap → α × JHeap) : Session × α :=
  let ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  let lh := heap.host.getD default
  let page := lh.page
  let page := { page with time := page.time.atRun page.loop.clock steps }
  let wasm0 := page.wasm.steps
  let budget := lh.budget
  let heap := { heap with steps := budget.toUInt64, host := some { lh with page, base := steps, wasm0 } }
  let (a, heap) := f heap
  let lh := heap.host.getD default
  let steps := steps + (budget - heap.steps.toNat) + (lh.page.wasm.steps - wasm0)
  let page := lh.page
  let time := page.time.atRun page.loop.clock steps
  let page := { page with time, loop := { page.loop with clock := time.sync page.loop.clock } }
  (⟨{ heap with host := some { lh with page } }, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩, a)

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

/-- How many runs' budgets a microtask checkpoint has. A checkpoint runs every job that is
queued, and the jobs that those queue, in one run (HTML's "perform a microtask checkpoint"):
a page that chains its work through promises does all of it there. The WPT `wasm/core` pages
chain 10,000 to 15,000 tests that way; the largest took 13 M steps (2026-11-13), past one run's
5 M, so the harness never finished. A job that loops for ever, or a chain that never ends,
still stops: after `checkpointRuns` budgets. -/
def checkpointRuns : Nat := 8

/-- The microtask checkpoint, with `checkpointRuns` budgets. -/
def Session.runJobs (s : Session) : Session :=
  let budget := (s.heap.host.getD default).budget
  let s := s.setBudget (checkpointRuns * budget)
  let (s, o, v) := s.run fun h => let ((o, n), h) := JS.checkpoint h; ((o, .num (Float.ofNat n)), h)
  let s := s.setBudget budget
  let n := match v with | .num x => x.toUInt64.toNat | _ => 0
  let s := { s with jobs := s.jobs + n }
  match failure o with
  | some m => s.fail m
  | none => s

/-- Report a new error at the window: a SyntaxError (`isSyntax`) or a TypeError with `msg`
(HTML "report an exception" of a module script's error to rethrow). -/
def Session.reportNew (s : Session) (isSyntax : Bool) (msg : String) : Session :=
  let msg := if msg.startsWith "SyntaxError: " then (msg.drop 13).toString else msg
  let (s, v) := s.runG fun h => JS.newError h (if isSyntax then .syntax else .type) msg
  (s.api? "report" #[v]).1.fail ((if isSyntax then "SyntaxError: " else "TypeError: ") ++ msg)

/-- Run a classic script; an exception is reported at the window (HTML "report an
exception", the prelude's `report`) and recorded. A script that does not parse has a
SyntaxError as its error to rethrow (HTML "create a classic script", step 9), reported the
same way: `window.onerror` and `error` listeners see it. -/
def Session.eval (s : Session) (src : String) : Session :=
  let (s, o, _) := s.run fun h => let (o, h) := JS.evalScript h src; ((o, .undef), h)
  match o with
  | .ok => s
  | .threw v m => (s.api? "report" #[v]).1.fail m
  | .syntaxError m => s.reportNew true m
  | o => s.fail ((failure o).getD "")

def Session.dispatchOnly (s : Session) (target : Nat) (type : String) : Session × Bool :=
  let (s, v) := s.api? "dispatch" #[.num (Float.ofNat target), .str type, .num (Float.ofNat (Page.flagsOf type))]
  ({ s with tasks := s.tasks + 1 }, match v with | .str "prevented" => true | _ => false)

def Session.callbackOnly (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Session :=
  let (s, _) := s.api? "call" #[.num (Float.ofNat cb), .num (Float.ofInt target), .num (Float.ofNat arg)]
  { s with tasks := s.tasks + 1 }

def Session.release (s : Session) (cb : Nat) : Session := (s.api? "release" #[.num (Float.ofNat cb)]).1

/-! ### Trusted input is out of reach of scripts

Everything a page's script does, and everything an import does for it, happens inside a
run of the engine: a function of the heap that `Session.run` or `Session.runG` is given.
The theorems below say that such a run leaves `Session.trusted` as it was, whatever the
function is. So the keys and buttons held and the user activation of a session change
only where `Session.setTrusted` is called: in the host's input actions. -/

/-- Isolation (run). Says: a run of the engine with any function of the heap (any script,
with any imports) leaves the trusted input state unchanged. Does not say: that the
script can not make events of its own (it can; `dispatchEvent` marks them untrusted in
the prelude, which Lean does not check). -/
theorem Session.run_trusted (s : Session) (f : JHeap → (JS.Outcome × JS.Value) × JHeap) :
    (s.run f).1.trusted = s.trusted := by
  obtain ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  rfl

/-- Isolation (run with any answer). Says: as `run_trusted`, for `runG`. Does not say:
more than that. -/
theorem Session.runG_trusted {α : Type} (s : Session) (f : JHeap → α × JHeap) :
    (s.runG f).1.trusted = s.trusted := by
  obtain ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  rfl

theorem Session.setBudget_trusted (s : Session) (budget : Nat) : (s.setBudget budget).trusted = s.trusted := by
  obtain ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  rfl

theorem Session.setHost_trusted (s : Session) (h : Host) : (s.setHost h).trusted = s.trusted := by
  obtain ⟨heap, api, limits, steps, jobs, tasks, errors, lastFrame, trusted⟩ := s
  rfl

theorem Session.fail_trusted (s : Session) (what : String) : (s.fail what).trusted = s.trusted := rfl

/-- Isolation (a call of the prelude). Says: a call of a method of the prelude's object
(a dispatch, a callback) leaves the trusted input state unchanged. Does not say: what
the method does to the page. -/
theorem Session.api?_trusted (s : Session) (name : String) (args : Array JS.Value) :
    (s.api? name args).1.trusted = s.trusted := by
  simp only [Session.api?]
  repeat' split
  all_goals simp [Session.fail_trusted, Session.run_trusted]

/-- Isolation (an event). Says: dispatching an event to the page's listeners, trusted or
not, leaves the trusted input state unchanged: a listener can not press a key, hold a
button or give the page user activation. Does not say: that listeners run (that is the
prelude's dispatch). -/
theorem Session.dispatchOnly_trusted (s : Session) (target : Nat) (type : String) :
    (s.dispatchOnly target type).1.trusted = s.trusted := by
  simp [Session.dispatchOnly, Session.api?_trusted]

/-- Isolation (a timer or frame callback). Says: running a callback of the page leaves the
trusted input state unchanged. Does not say: more than that. -/
theorem Session.callbackOnly_trusted (s : Session) (cb : Nat) (target : Int) (arg : Nat) :
    (s.callbackOnly cb target arg).trusted = s.trusted := by
  simp [Session.callbackOnly, Session.api?_trusted]

/-- Isolation (microtasks). Says: the microtask checkpoint (every promise job of the
page) leaves the trusted input state unchanged. Does not say: more than that. -/
theorem Session.runJobs_trusted (s : Session) : s.runJobs.trusted = s.trusted := by
  simp only [Session.runJobs]
  repeat' split
  all_goals simp [Session.fail_trusted, Session.setBudget_trusted, Session.run_trusted]

/-- Only the setter. Says: `setTrusted` gives exactly the state it is given, and changes
nothing a script can read: the host, and so the DOM and the event loop, stay as they
were. Does not say: who calls it (the host's input actions; read `WebScripts`). -/
theorem Session.setTrusted_spec (s : Session) (t : L4Factoidal.WebDriver.Input.Trusted) :
    (s.setTrusted t).trusted = t ∧ (s.setTrusted t).host = s.host := ⟨rfl, rfl⟩

/-- The session as an engine of `Hosts.PageEvents`. -/
def engine : PageEvents.Engine Session :=
  { host := Session.host, setHost := Session.setHost, dispatchOnly := Session.dispatchOnly,
    callbackOnly := Session.callbackOnly, release := Session.release, runJobs := Session.runJobs,
    lastFrame := Session.lastFrame, setLastFrame := fun s f => { s with lastFrame := f } }

/-! ## Module scripts (`LeanJSModules`, `JS.Modules`) -/

/-- Run one module script (HTML "execute the script element" for a module script): fire
`error` for a failed fetch, report its error to rethrow, or link and evaluate its graph and
report what it threw; a microtask checkpoint after it, then `load` for an external one. -/
def Session.runModule (s : Session) (g : JS.ModGraph) (lives : JS.ModLives) (node : Nat)
    (oc : LeanJSModules.Outcome) : Session × JS.ModLives :=
  match oc with
  | .fetchError => ((s.dispatchOnly node "error").1, lives)
  | .rethrow isSyntax msg => (s.reportNew isSyntax msg, lives)
  | .run root external =>
    let (s, (o, lv)) := s.runG fun h => JS.runModuleGraph h g root lives
    let s := match o with
      | .ok => s
      | .threw v m => (s.api? "report" #[v]).1.fail m
      | o => s.fail ((failure o).getD "")
    let s := engine.checkpoint s
    ((if external then (s.dispatchOnly node "load").1 else s), lv)

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
  let heap := { freshRealm lim with steps := runBudget.toUInt64 }
  let (nobj, heap) := JS.hostObject heap natives
  -- the structured clone and classic scripts for dedicated workers (`JS.Clone`): built-ins
  -- of the engine, not of the host, since they walk the heap
  let heap := JS.addNatives heap nobj #[("serialize", .x .cloneSerialize, 2), ("deserialize", .x .cloneDeserialize, 1),
    ("runScript", .x .classicScript, 1),
    -- the global object's slot for the page's named properties (`JS.namedGetterKey`)
    ("setNamedGetter", .x .namedGetterSet, 1),
    -- the URL Pattern Standard (`WHATWG.URLPattern`), for the prelude's URLPattern class
    ("urlPattern", .x .urlPattern, 4),
    -- the Streams Standard's queue and fill plan (`WHATWG.Streams`), for the prelude's classes
    ("streams", .x .streams, 6)]
  let ((o, f), heap) := JS.evalValue heap prelude
  if let some m := failure o then throw s!"prelude: {m}"
  let ((o, api), heap) := JS.callFunction heap f .undef #[nobj]
  if let some m := failure o then throw s!"prelude: {m}"
  return { heap := { heap with jobs := #[], jobHead := 0 }, api, limits := lim }

/-- The mark of the prelude a snapshot was made from (its text's hash). -/
def preludeMark : String := toString (hash prelude)

/-- The realm of `prepareSource` as data (`JS.Snapshot.encode`), with the prelude's object
and `preludeMark`. `lake exe bubblepop-realm` writes it into `LeanJSRealmData.lean` at
build time (build-web-render.sh). A function of `Unit`, not a constant: a constant is computed
when the module is initialized, which ran the whole prelude at the first call into every
engine, for every page (about 300 ms of the Hub's first frame), and threw the result away. -/
def snapshotData (_ : Unit) : Except String String := do
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
    return { heap := { heap with steps := runBudget.toUInt64, jobs := #[], jobHead := 0 }, api, limits := lim }
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
the current script set and a microtask checkpoint after it), the module scripts of `mods`
(`Session.runModule`), `DOMContentLoaded`, the
window's `load` event as a task, and the tasks due at time 0. `origins`: a sandboxed
frame's own session (`HTML.FrameSessions`), with its own origin and its parent's. -/
def start (base : Session) (dom : Arena) (url : String) (scripts : Array (Nat × String)) (lim : Page.Limits := {})
    (reads : Reads := {}) (time : ScriptClock := {})
    (origins : Option (L4Factoidal.HTML.Frames.Origin × L4Factoidal.HTML.Frames.Origin) := none)
    (mods : LeanJSModules.Loaded := {}) : Session := Id.run do
  let gpu := L4Factoidal.PageGpu.State.empty lim.gpuPage
  let domHost : Page.DomHost := { dom := dom, commandLimit := lim.commands, logLimit := lim.logs, framing := lim.frames, gpu := gpu, url, selfOrigin := origins.map (·.1), parentOrigin := origins.map (·.2), hostLoads := lim.hostLoads }
  -- the page's own iframes get browsing contexts before its scripts run (as `Page.Session.startP`)
  let domHost := if domHost.framing && dom.nodes.any (L4Factoidal.DOM.Dom.isHtmlElement · "iframe") then
    let d1 := Hosts.Dom.connectFrames domHost #[0]
    { d1 with navigations := d1.navigations.filter (!·.2.isEmpty) } else domHost
  let s := { base with
    heap := { base.heap with maxDepth := callDepth.toUInt32 },
    limits := lim, steps := 0, jobs := 0, tasks := 0, errors := #[], lastFrame := none }
  -- Math.random: a seed of this session's own, not the realm snapshot's constant
  -- (`WebApi.mathRandomSeed`; as `LeanJSWorkers.start` does for a worker). With the constant
  -- every page drew the same sequence, so two pages' "random" tokens were equal.
  let s := match Hosts.WebApi.mathRandomSeed lim.entropy with
    | some x => { s with heap := { s.heap with rng := x } }
    | none => s
  let mut s := s.setHost { dom := domHost, reads, time, web := { entropy := lim.entropy, docEncoding := lim.encoding, net := { enabled := lim.network, page := L4Factoidal.Net.PageFetch.Page.ofUrl url lim.hostCors lim.pageAddress, client := url, policy := L4Factoidal.Net.Xhr.policyOfHeader lim.referrerPolicy, syncOk := lim.syncOk, syncAnswers := lim.syncAnswers, mayBlock := lim.mayBlock } } }
  s := (s.api? "start" #[]).1
  s := (s.api? "url" #[.str (JS.Str.ofHost url)]).1
  for (node, src) in scripts do
    s := (s.api? "script" #[.num (Float.ofNat node)]).1
    s := s.eval src
    s := engine.checkpoint s
  s := (s.api? "script" #[.num (-1)]).1
  -- module scripts, deferred: after the classic scripts, in document order, before
  -- `DOMContentLoaded` (`document.currentScript` is null for them)
  let mut lives : JS.ModLives := #[]
  for (node, oc) in mods.scripts do
    let (s', lv) := s.runModule mods.graph lives node oc
    s := s'
    lives := lv
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
def loadFrame (s : Session) (el : Nat) (source : String) (scripts : Array (Nat × String)) (xml : Bool := false)
    (responseUrl : Option String := none) : Session := Id.run do
  let (dom, root) := Hosts.Dom.attachDocument s.host.dom el source xml responseUrl
  -- Which scripts run here is asked of the frame as it is after this navigation
  -- (`Hosts.Dom.realmScripts`, `realmScripts_needs_access`, `navigatedTo_frame`): asked
  -- before, a frame that was `about:blank` or same-origin and went to another origin had
  -- that document's scripts run in the page's realm.
  let scripts := Hosts.Dom.realmScripts dom el scripts
  let mut s := s.setHost { s.host with dom }
  if let some root := root then
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
