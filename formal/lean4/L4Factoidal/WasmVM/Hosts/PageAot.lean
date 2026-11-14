/-
L4Factoidal.WasmVM.Hosts.PageAot: page scripts with the guest translated for the host's
WebAssembly engine (record: docs/designissues/2026-11-08-wasmvm-aot.md, section 5).

The session code is `Hosts.Page`'s `Prog`. Here are the parts of the other machine:

- `prepare`: decode, validate, check the exports and imports a page needs, link the
  bindings the interpreter would make (`Wasi.link`), translate (`Aot.translate`) and
  encode. The answer holds the host module's bytes and, for each import, the ranges of
  guest memory its host function reads (`readsOf`), so the host can send them with the
  call.
- `session`: a session with no Lean store: the guest's memory and instance are the host's.
- `Paused`, `Prog.next`: a program stopped at an ask, which the engine keeps between the
  host's calls.
- `serveHost`: one import call that the host passes back, served by `Page.serve` (the
  interpreter's function for each binding) on a `Window` of the guest's memory.

A guest import with no entry in `readsOf` makes `prepare` refuse the module, so a newly
added import that reads memory can not be served with bytes missing: such a module runs on the
interpreter. `Import.reads` is an exhaustive match: a new `foafnaut_dom` import does not
compile until its reads are stated.
-/
import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.WasmVM.Aot.Translate
import L4Factoidal.WasmVM.Aot.Encode
import L4Factoidal.WasmVM.Aot.Window

namespace L4Factoidal.WasmVM.Hosts.PageAot
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Hosts.Page

/-- A range a host function may read: argument `ptr` is a pointer, argument `len` a
length; when the length is over `bound` the function reads nothing (it answers -5). -/
structure Read where
  ptr : Nat
  len : Nat
  bound : Nat
  deriving Repr, Inhabited, BEq

/-- The memory each `foafnaut_dom` import reads: every `readStr` of `Hosts.Dom`. -/
def domReads : Hosts.Dom.Import → List Read
  | .getElementById => [⟨0, 1, Hosts.Dom.maxString⟩]
  | .documentElement => []
  | .tagName => []
  | .textContentGet => []
  | .textContentSet => [⟨1, 2, Hosts.Dom.maxString⟩]
  | .getAttribute => [⟨1, 2, Hosts.Dom.maxAttrName + Hosts.Dom.maxString⟩]
  | .setAttribute => [⟨1, 2, Hosts.Dom.maxAttrName + Hosts.Dom.maxString⟩, ⟨3, 4, Hosts.Dom.maxString⟩]
  | .createElement => [⟨0, 1, Hosts.Dom.maxAttrName⟩]
  | .appendChild => []
  | .addEventListener => [⟨1, 2, Hosts.Dom.maxAttrName⟩]
  | .setTimer => []
  | .clearTimer => []
  | .consoleLog => [⟨0, 1, Hosts.Dom.maxString⟩]
  | .nodeInfo => []
  | .nodeString => []
  | .nodeChildren => []
  | .createNode => [⟨1, 2, Hosts.Dom.maxDocument⟩]
  | .insertBefore => []
  | .removeChild => []
  | .replaceChild => []
  | .removeAttribute => [⟨1, 2, Hosts.Dom.maxAttrName + Hosts.Dom.maxString⟩]
  | .cloneNode => []
  | .treeOp => []
  | .nodeQuery => [⟨2, 3, Hosts.Dom.maxString⟩]
  | .gpuCommand => [⟨2, 3, L4Factoidal.PageGpu.maxBuffer + 65536⟩]

/-- The memory each import reads, by its binding; `none` for an import whose reads are
not known here (the module then runs on the interpreter). WASI under `Page.caps` grants
only the clocks, which write; every other function answers before it reads memory
(`Wasi.fd_write_needs_sink`, `random_get_needs_source`, `denied_is_pure`). -/
def readsOf : Wasi.Binding → Option (List Read)
  | .wasi _ => some []
  | .extra mo nm =>
    if mo == "env" && nm == "emscripten_notify_memory_growth" then some []
    else if mo != Hosts.Dom.moduleName then none
    else match nm with
      | "listen" | "dispatch_plan" => some [⟨1, 2, Hosts.Dom.maxAttrName⟩]
      | "unlisten" | "set_timer" | "clear_timer" | "request_frame" | "cancel_frame" => some []
      | "web_api" => some [⟨2, 3, Hosts.WebApi.maxInput⟩]
      -- The request, and the bytes of the Memory.buffer view it copies from.
      | "wasm_call" => some [⟨2, 3, Hosts.PageWasm.maxRequest⟩, ⟨6, 7, Hosts.PageWasm.maxRequest⟩]
      | _ => (Hosts.Dom.Import.ofName? nm).map domReads

/-- A guest prepared for the host's engine. -/
structure Prepared where
  /-- The host module. -/
  bytes : ByteArray
  plan : Aot.Plan
  bindings : Array Wasi.Binding
  /-- The reads of import `k`. -/
  reads : Array (List Read)
  /-- The types of import `k`, to read the host's arguments. -/
  types : Array FuncType
  guestBytes : Nat

/-- Decode, validate, check and translate a guest for page scripts. -/
def prepare (bytes : ByteArray) (lim : Hosts.Page.Limits := {}) : Except String Prepared := do
  let md ← (Binary.decodeParallel bytes).mapError (fun e => s!"decode: {e.toString}")
  match validate md with
  | .ok _ => pure ()
  | .error e => throw s!"validate: {e.toString}"
  if md.start.isSome then throw "the module has a start function"
  -- The exports a page needs, as functions.
  for name in exportNames do
    match md.exports.find? (·.name == name) with
    | some { desc := .func _, .. } => pure ()
    | _ => throw s!"the module has no export {name}"
  if !(md.exports.any fun e => e.name == "memory" && e.desc matches .mem 0) then
    throw "the module does not export its memory as memory"
  let (_, _, bs) ← Wasi.link ({ pageLimit := lim.pages } : Store) md accepts
  let reads ← bs.mapM fun b => match readsOf b with
    | some r => Except.ok r
    | none => .error s!"aot: no read table for an import ({repr b})"
  let types ← md.imports.mapM fun i => match i.desc with
    | .func t => match md.types[t]? with
      | some ft => Except.ok ft
      | none => .error "aot: import type"
    | _ => .error "aot: a non-function import"
  let (t, plan) ← Aot.translate md lim.pages
  return { bytes := Aot.Encode.encode t, plan, bindings := bs, reads, types, guestBytes := bytes.size }

/-- A session for a guest that runs in the host's engine: no Lean store (`store` is
empty and `mem` is 0, the address of the `Window` in `serveHost`); an export's number
is its place in `exportNames`. Its fuel per run is `lim.fuel`, as on the interpreter. -/
def session (p : Prepared) (dom : Arena) (lim : Hosts.Page.Limits := {}) (framed : Array (Nat × Nat) := #[])
    (reads : Reads := {}) (time : ScriptClock := {}) : Session × Nat × Nat × Nat :=
  let idx := fun (name : String) => (exportNames.idxOf? name).getD 0
  let (fx, init, qnew, mode) := (Exports.of fun n => .ok (idx n)).toOption.getD (default, 0, 0, 0)
  let gpu := L4Factoidal.PageGpu.State.empty lim.gpuPage
  let domHost : DomHost := { dom := dom, commandLimit := lim.commands, logLimit := lim.logs, frames := framed, framing := lim.frames, hostLoads := lim.hostLoads, gpu := gpu }
  let host : Host := { dom := domHost, reads := reads, time := time, web := { entropy := lim.entropy, docEncoding := lim.encoding } }
  ({ store := {}, inst := 0, mem := 0, bindings := p.bindings, host, fx, limits := lim }, init, qnew, mode)

/-- The program of a page start on the host's engine, after the host made a fresh
instance: `_initialize`, `qjs_new` and page mode on an empty document (as
`Page.prepare` makes the interpreter's base), then the page's own host state and
`Session.startP`, as `Page.start` does from the base. -/
def startProg (p : Prepared) (dom : Arena) (url : String) (scripts : Array (Nat × String))
    (lim : Hosts.Page.Limits := {}) (framed : Array (Nat × Nat) := #[]) (missing : Array String := #[])
    (reads : Reads := {}) (time : ScriptClock := {}) : Prog (Except String Session) :=
  let (s, init, qnew, mode) := session p emptyDocument {}
  let page := (session p dom lim framed reads time).1
  do
    match ← s.initP init qnew mode with
    | .error e => return .error e
    | .ok s =>
      let s := { s with host := page.host, limits := lim, steps := 0 }
      let s ← s.startP url scripts framed
      return .ok (missing.foldl Session.fail s)

/-! ## A program stopped at an ask -/

structure Paused (α : Type) where
  ask : Ask
  session : Session
  k : Session → Reply → Prog α
  /-- Host calls served in the current run. -/
  hostCalls : Nat := 0
  /-- The page's WebAssembly instructions when the run started (`Hosts.PageWasm`): those
  run since are script time, as in `Session.run`. -/
  wasm0 : Nat := 0

/-- The script clock at the start of a run, as `Session.run` sets it. -/
def startRun (s : Session) : Session :=
  { s with host := { s.host with time := s.host.time.atRun s.host.loop.clock s.steps } }

/-- Where a program stands: finished, or stopped at an ask. -/
def Prog.next : Prog α → α ⊕ Paused α
  | .done a => .inl a
  | .ask q s k =>
    let session := match q with | .invoke _ _ => startRun s | _ => s
    .inr { ask := q, session := session, k := k, wasm0 := s.host.wasm.steps }

/-- Continue with the machine's reply. -/
def Paused.resume (p : Paused α) (r : Reply) : α ⊕ Paused α :=
  Prog.next (p.k p.session r)

/-- The outcome of a run the host made: the values (i32 results), or a trap with its
message; `fuelLeft` is the fuel global after the run. Fuel units spent are added to
`steps`. -/
def ranReply (p : Paused α) (o : Outcome) (fuelLeft : Int) : Paused α × Reply :=
  let spent := (Int.ofNat p.session.limits.fuel - fuelLeft).toNat + (p.session.host.wasm.steps - p.wasm0)
  let o := match o with
    | .trap t => if fuelLeft < 0 then Outcome.trap (.host "out of fuel") else .trap t
    | o => o
  let s := p.session
  let steps := s.steps + spent
  -- Script time passed: the loop's clock moves up to it (as at the end of `Session.run`).
  let time := s.host.time.atRun s.host.loop.clock steps
  let host := { s.host with time, loop := { s.host.loop with clock := time.sync s.host.loop.clock } }
  ({ p with session := { s with steps, host } }, .ran o)

/-- Serve one import call the host passed back while it runs an export: binding `id`,
the arguments, the memory size, the ranges the host sent and the fuel global now. The answer: the host
result and the writes for the host to copy into the guest's memory. -/
def serveHost (p : Paused α) (id : Nat) (args : Array Value) (memSize : Nat)
    (segs : Array (Nat × ByteArray)) (fuelLeft : Int) : Paused α × HostResult × Array (Nat × ByteArray) :=
  if p.hostCalls ≥ p.session.limits.hostCalls then (p, .trap "host call budget", #[]) else
  let s := p.session
  let st : StoreOf Aot.Window := { mems := #[{ data := { size := memSize, segs }, max := none }] }
  -- The script clock counts the run so far, as `Session.run` does at each host call.
  let spent := (Int.ofNat s.limits.fuel - fuelLeft).toNat + (s.host.wasm.steps - p.wasm0)
  let h := { s.host with time := s.host.time.atRun s.host.loop.clock (s.steps + spent) }
  let (h, st, r) := serve 0 s.bindings id args h st
  let writes := match st.mems[0]? with
    | some m => m.data.writes
    | none => #[]
  ({ p with session := { s with host := h }, hostCalls := p.hostCalls + 1 }, r, writes)

end L4Factoidal.WasmVM.Hosts.PageAot
